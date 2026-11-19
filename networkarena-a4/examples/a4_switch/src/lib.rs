//! Switch program for A4.
//!
//! One program runs on every switch of the AS. It does the three things the
//! starter leaves open, and it keeps the usual Gao-Rexford policy.
//!
//! Exit. The same choice as the usual nearest-exit rule: shorter AS path,
//! then anything but the Tier-1, then fewer hops inside the AS. A backup
//! route stays behind a peer or provider route for the same prefix. Among
//! backup routes, the exit nearer the block on the neighbor's side wins,
//! so a backup we sell is carried to the town where that block lives.
//!
//! Queueing. With no customer, peer, or provider, every external packet
//! shares the Tier-1 and that link is oversubscribed. Calls and trading
//! then get a short queue in front and web and video keep the rest: a
//! burst of calls is dropped instead of filling the buffer, and the video
//! that does go out still meets its target. Once a settlement gives
//! traffic another way out, that split drops web and video that a single
//! queue would have kept, so the port stays one FIFO. Hellos have their
//! own queue in front when the split is on, so a full data queue cannot
//! hide a dead link.
//!
//! Failover. Nothing announces a failure. Each switch sends a small hello
//! on its internal ports and, once a port has gone quiet, rebuilds the
//! table without that link. Own prefixes still reachable inside the AS stay
//! on the internal path. A prefix whose exit was across the failed link is
//! dropped, rather than handed to the Tier-1: that link is already full, and
//! the detour bills us for packets that miss their target. A backup route
//! still applies when its exit is up.

#[path = "../../a4_starter/src/policy.rs"]
mod policy;
#[path = "../../a4_starter/src/router.rs"]
mod router;

use std::collections::{BTreeMap, BTreeSet};
use switch_program_sdk::wire::{self, A4InfoW, A4LinkW, A4RouteW};
use switch_program_sdk::*;

const PERIOD_NS: u64 = 100_000_000;
const DEAD_NS: u64 = 450_000_000;
const Q_HELLO: u16 = 0;
const Q_CALLS: u16 = 1;
const Q_TRADING: u16 = 2;
const Q_BULK: u16 = 3;

pub struct Program {
    live: bool,
    me: u32,
    info: A4InfoW,
    caps: BTreeMap<u16, u64>,
    local_ports: Vec<u16>,
    internal: Vec<u16>,
    queue_bytes: u64,
    routes: Vec<(u64, u32, u8, u16)>,
    drops: Vec<(u64, u32, u8)>,
    next_route_id: u64,
    next_drop_id: u64,
    last_rx: BTreeMap<u16, u64>,
    down: BTreeSet<u16>,
    queues_set: bool,
    /// Split the buffer by class. Worth it only while every external
    /// packet is headed for the Tier-1.
    split_queues: bool,
}

impl Program {
    fn offline() -> Self {
        Self {
            live: false,
            me: 0,
            info: A4InfoW::default(),
            caps: BTreeMap::new(),
            local_ports: Vec::new(),
            internal: Vec::new(),
            queue_bytes: 12_500,
            routes: Vec::new(),
            drops: Vec::new(),
            next_route_id: 1000,
            next_drop_id: 500_000,
            last_rx: BTreeMap::new(),
            down: BTreeSet::new(),
            queues_set: false,
            split_queues: false,
        }
    }

    fn down_links(&self) -> BTreeSet<(u32, u16)> {
        let mut out = BTreeSet::new();
        for &port in &self.down {
            match self.internal_link(port) {
                Some(l) => {
                    out.insert((l.a, l.a_port));
                    out.insert((l.b, l.b_port));
                }
                None => {
                    out.insert((self.me, port));
                }
            }
        }
        out
    }

    fn internal_link(&self, port: u16) -> Option<&A4LinkW> {
        self.info.internal.iter().find(|l| {
            (l.a == self.me && l.a_port == port) || (l.b == self.me && l.b_port == port)
        })
    }

    fn recompute(&mut self) -> Vec<Action> {
        let down = self.down_links();
        let mut routes = forwarding(&self.info, self.me, &down);
        let mut drops = spur_drops(&self.info, self.me, &down);
        drops.extend(cut_drops(&self.info, self.me, &down));
        drops.sort_unstable();
        drops.dedup();
        routes.retain(|&(addr, len, _)| !drops.iter().any(|&(a, l)| a == addr && l == len));
        let (drop_del, drop_add) = diff_drops(&mut self.drops, &drops, &mut self.next_drop_id);
        let route_acts = router::reinstall(&mut self.routes, &routes, &mut self.next_route_id);
        let mut out = drop_del;
        out.extend(route_acts);
        out.extend(drop_add);
        out
    }

    fn mark_down(&mut self, now: u64) -> Vec<Action> {
        let mut freshly = Vec::new();
        for &port in &self.internal {
            let Some(&heard) = self.last_rx.get(&port) else { continue };
            if now.saturating_sub(heard) > DEAD_NS && self.down.insert(port) {
                freshly.push(port);
            }
        }
        if freshly.is_empty() {
            return Vec::new();
        }
        let mut out = self.recompute();
        for port in freshly {
            out.push(actions::link_down(port));
        }
        out
    }

    fn queue_actions(&self) -> Vec<Action> {
        self.local_ports
            .iter()
            .map(|&port| {
                let bps = self.caps.get(&port).copied().unwrap_or(0);
                actions::set_queues(port, Discipline::StrictPriority, port_queues(bps, self.queue_bytes))
            })
            .collect()
    }
}

impl SwitchProgram for Program {
    fn init(_: u32, _: Vec<u16>) -> (Self, ProgramSetup) {
        (Self::offline(), router::setup(&[], false))
    }

    fn init_with(input: InitInput) -> (Self, ProgramSetup) {
        let Some(info) = input.a4.clone() else {
            return Self::init(input.switch_id, input.local_ports);
        };
        let mut caps = BTreeMap::new();
        for (i, &port) in input.local_ports.iter().enumerate() {
            caps.insert(port, input.port_capacity_bps.get(i).copied().unwrap_or(0));
        }
        let no_failed_links = BTreeSet::new();
        let routes = forwarding(&info, input.switch_id, &no_failed_links);
        let split_queues = !info.routes.iter().any(|r| {
            matches!(r.rel, wire::A4_CUSTOMER | wire::A4_PEER | wire::A4_PROVIDER)
        });
        let mut setup = router::setup(&routes, false);
        if split_queues {
            arm_classes(&mut setup);
        }
        let installed: Vec<(u64, u32, u8, u16)> = routes
            .iter()
            .enumerate()
            .map(|(i, &(addr, len, port))| (1000 + i as u64, addr, len, port))
            .collect();
        let next_route_id = 1000 + routes.len() as u64;
        let program = Self {
            live: true,
            me: input.switch_id,
            internal: router::internal_ports(&info, input.switch_id),
            queue_bytes: if info.queue_bytes == 0 { 12_500 } else { info.queue_bytes },
            info,
            caps,
            local_ports: input.local_ports,
            routes: installed,
            drops: Vec::new(),
            next_route_id,
            next_drop_id: 500_000,
            last_rx: BTreeMap::new(),
            down: BTreeSet::new(),
            queues_set: false,
            split_queues,
        };
        (program, setup)
    }

    fn on_punt(&mut self, ev: PuntEvent) -> Vec<Action> {
        if !self.live || ev.ip_proto != router::PROTO_HELLO || !self.internal.contains(&ev.ingress_port) {
            return Vec::new();
        }
        let heard = if ev.arrived_ns == 0 { ev.now_ns } else { ev.arrived_ns };
        self.last_rx.insert(ev.ingress_port, heard);
        if !self.down.remove(&ev.ingress_port) {
            return Vec::new();
        }
        let mut out = self.recompute();
        out.push(actions::link_up(ev.ingress_port));
        out
    }

    fn on_timer(&mut self, ev: TimerEvent) -> Vec<Action> {
        if !self.live {
            return Vec::new();
        }
        let mut out = Vec::new();
        if !self.queues_set {
            self.queues_set = true;
            if self.split_queues {
                out.extend(self.queue_actions());
            }
            for &port in &self.internal {
                out.push(actions::link_up(port));
            }
        }
        out.extend(self.mark_down(ev.now_ns));
        for &port in &self.internal {
            out.push(actions::in_queue(
                Q_HELLO,
                actions::inject_packet(port, router::CTRL_IP, router::CTRL_IP, router::PROTO_HELLO, 64, Vec::new()),
            ));
        }
        out.push(actions::schedule_timer(PERIOD_NS));
        out
    }
}

fn arm_classes(setup: &mut ProgramSetup) {
    let mut id = 10u64;
    let mut add = |setup: &mut ProgramSetup, class: u64, queue: u16| {
        setup.add_entry(
            router::T_CLASS,
            TableEntry {
                id: wire::EntryIdW(id),
                key: class,
                prefix_len: 8,
                priority: 0,
                action: TableAction::SetQueue { queue: wire::QueueIdW(queue) },
            },
        );
        id += 1;
    };
    add(setup, wire::A4_CALLS as u64, Q_CALLS);
    add(setup, wire::A4_TRADING as u64, Q_TRADING);
    for class in [0u64, wire::A4_WEB as u64, wire::A4_VIDEO as u64] {
        add(setup, class, Q_BULK);
    }
}

/// Caps are in 1000-byte packets. Calls get enough room for a few
/// milliseconds and no more; trading gets two slots; web and video keep
/// the rest. This is the split that beat one FIFO on a full Tier-1 link.
fn port_queues(bps: u64, queue_bytes: u64) -> Vec<QueueSpec> {
    let slots = (queue_bytes / 1000).clamp(8, 64) as u32;
    let pkt_us = if bps == 0 { 1_000 } else { 8_000_000_000 / bps.max(1) };
    let calls = (3_000 / pkt_us.max(1)).clamp(1, 4) as u32;
    let trading = 2u32;
    let hello = 1u32;
    let bulk = slots.saturating_sub(hello + calls + trading).max(2);
    vec![
        QueueSpec::new(hello),
        QueueSpec::new(calls),
        QueueSpec::new(trading),
        QueueSpec::new(bulk),
    ]
}

fn forwarding(info: &A4InfoW, me: u32, down: &BTreeSet<(u32, u16)>) -> Vec<(u32, u8, u16)> {
    router::table(info, me, down, |r, hops| Some(exit_cost(r, hops)))
}

fn exit_cost(r: &A4RouteW, hops: u32) -> u64 {
    let tier1 = u64::from(r.rel == wire::A4_TIER1);
    if r.rel == wire::A4_BACKUP {
        // `med` is the neighbor's distance from this exit to the block.
        // A lower one is the town the block is in. Hop count only breaks a tie,
        // so selling backup actually crosses to the far town.
        return 5_000_000_000 + (r.med as u64) * 1_000 + u64::from(hops);
    }
    (r.as_path.len() as u64) * 1_000_000 + tier1 * 1_000 + u64::from(hops)
}

/// Own prefixes this switch can no longer reach. Drop them unless a backup
/// route covers them and the backup's exit is still up: that route is less
/// specific, so it only applies once the /24 is gone.
fn spur_drops(info: &A4InfoW, me: u32, down: &BTreeSet<(u32, u16)>) -> Vec<(u32, u8)> {
    let mut out = Vec::new();
    for p in &info.own {
        if p.switch == me || router::next_hop(info, me, p.switch, down).is_some() {
            continue;
        }
        if !backup_covers(info, me, p.addr, p.len, down) {
            out.push((p.addr, p.len));
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn backup_covers(info: &A4InfoW, me: u32, addr: u32, len: u8, down: &BTreeSet<(u32, u16)>) -> bool {
    info.routes.iter().any(|r| {
        r.rel == wire::A4_BACKUP
            && r.len < len
            && covers(r.addr, r.len, addr)
            && (r.switch == me || router::next_hop(info, me, r.switch, down).is_some())
    })
}

fn covers(prefix: u32, len: u8, addr: u32) -> bool {
    if len == 0 {
        return true;
    }
    if len >= 32 {
        return prefix == addr;
    }
    let shift = 32 - len;
    (prefix >> shift) == (addr >> shift)
}

/// Prefixes that lost their exit when a link went down and whose only
/// remaining route is the Tier-1. Drop them so the default route does not
/// pick them up.
fn cut_drops(info: &A4InfoW, me: u32, down: &BTreeSet<(u32, u16)>) -> Vec<(u32, u8)> {
    if down.is_empty() {
        return Vec::new();
    }
    let none = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for r in &info.routes {
        if r.len == 0 || !seen.insert((r.addr, r.len)) {
            continue;
        }
        let Some(want) = chosen(info, me, &none, r.addr, r.len) else { continue };
        if want.rel == wire::A4_TIER1 {
            continue;
        }
        let reachable = want.switch == me || router::next_hop(info, me, want.switch, down).is_some();
        if reachable {
            continue;
        }
        let fallback = chosen(info, me, down, r.addr, r.len);
        if fallback.is_none_or(|r| r.rel == wire::A4_TIER1) {
            out.push((r.addr, r.len));
        }
    }
    out
}

fn chosen<'a>(info: &'a A4InfoW, me: u32, down: &BTreeSet<(u32, u16)>, addr: u32, len: u8) -> Option<&'a A4RouteW> {
    let mut best: Option<(u64, u32, u16, &A4RouteW)> = None;
    for r in &info.routes {
        if r.addr != addr || r.len != len || down.contains(&(r.switch, r.port)) {
            continue;
        }
        let hops = router::inside(info, me, r.switch, down)?;
        let key = (exit_cost(r, hops), r.switch, r.port);
        if best.as_ref().is_none_or(|(c, s, p, _)| key < (*c, *s, *p)) {
            best = Some((key.0, r.switch, r.port, r));
        }
    }
    best.map(|(_, _, _, r)| r)
}

fn diff_drops(old: &mut Vec<(u64, u32, u8)>, new: &[(u32, u8)], next_id: &mut u64) -> (Vec<Action>, Vec<Action>) {
    let want: BTreeSet<(u32, u8)> = new.iter().copied().collect();
    let mut keep = Vec::new();
    let mut del = Vec::new();
    for &(id, addr, len) in old.iter() {
        if want.contains(&(addr, len)) {
            keep.push((id, addr, len));
        } else {
            del.push(actions::delete_entry(router::T_ROUTE, id));
        }
    }
    let mut add = Vec::new();
    for &(addr, len) in new {
        if keep.iter().any(|&(_, a, l)| a == addr && l == len) {
            continue;
        }
        *next_id += 1;
        add.push(actions::install_entry(router::T_ROUTE, drop_entry(*next_id, addr, len)));
        keep.push((*next_id, addr, len));
    }
    *old = keep;
    (del, add)
}

fn drop_entry(id: u64, addr: u32, len: u8) -> TableEntry {
    TableEntry {
        id: wire::EntryIdW(id),
        key: addr as u64,
        prefix_len: len,
        priority: 0,
        action: TableAction::Drop,
    }
}

switch_program!(Program);
switch_program_sdk::policy_program!(policy::rank, policy::announce);
