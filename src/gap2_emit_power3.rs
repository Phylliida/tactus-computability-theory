//! # GAP-2 G2-F Route (i) — the TRIPLE power-block window over the `assemble5` scaffold.
//!
//! The 3-digit analog of [`crate::gap2_emit_power`]: one full per-power-block PERIODIC step
//! ([`crate::tm_power_block::lemma_power_block_step_block3`]) — `copy_refresh ∘ block_loop`, the loop
//! emitting a 3-symbol run `(s0,s1,s2)` per master-unit, master stationary. It uses 34 distinct states
//! (the widest in the build), mapped to offsets `0..33` of one STRIDE=48 window. The triple power-blocks
//! `(4,1,2)ⁱ` and `(4,3,2)ⁱ` of `fam_digits` are exactly this. Both the `M ≥ 2` and `M = 1` dispatches run
//! over the SAME window (every M=1 quint maps to a `pbb3_act` slot with identical content, exactly as the
//! single-digit case in [`crate::gap2_emit_power`]).
//!
//! Same recipe + opaque generator rule (§N+11). The exit-parametric splice: the loop-exit `(q_guard, 0)`
//! targets the external `qexit` (= the next block's `entry5(pc+1)`, or `q_cmp` for the last block).
//!
//! ## State → offset map (block3)
//! ```
//!  0 q_dh0    8 q_t      16 q_turng  24 q_guard  32 q_disc
//!  1 q_dw0    9 q_a      17 q_ret    25 q_iter   33 q_exit (terminal, parametric)
//!  2 q_bk0   10 q_b      18 q_ut     26 q_surge
//!  3 q_t0    11 q_rf     19 q_ua     27 q_e1
//!  4 q_a0    12 q_rg     20 q_uf     28 q_e2
//!  5 q_rf0   13 q_rt     21 q_ur     29 q_eret
//!  6 q_rg0   14 q_dw     22 q_urg    30 q_bhome
//!  7 q_home  15 q_turn   23 q_urt    31 q_dwalk
//! ```
//! `docs/gap2-input-loader-plan.md` §N+10/§N+11. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, Quintuple, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_assemble5::{entry5, tm_mod5, lemma_tm_wf_n5, lemma_slot_index5, lemma_idx5_decomp};
use crate::tm_dstring::dpack;
use crate::tm_copy_refresh::copy_u;
use crate::gap2_relnum_dds::seq_pow;
use crate::tm_power_block::{power_block_fuel_b3, lemma_power_block_step_block3};
use crate::tm_power_block_m1::{power_block_fuel_b3_m1, lemma_power_block_step_block3_m1};

use crate::gap2_tail_lift::{tail_safe, tail_end_h};
use crate::gap2_tail_power::{lemma_power_block_step_block3_tail_safe, lemma_power_block_step_block3_m1_tail_safe};
verus! {

// ─────────────────────────────────────────────────────────────────────────────
// The triple power-block action table. Off 0..23 (copy_refresh) is IDENTICAL to pbb1_act; off 24..33
// (block_loop) carries the triple emit `(s0,s1,s2)` via the two new states q_e1 (27), q_e2 (28).
// Returns (write, next_off, dir); the absolute next state is entry5(pc) + next_off.
// ─────────────────────────────────────────────────────────────────────────────

/// The block3 power-block action table over a STRIDE=48 window, emitting the triple `(s0,s1,s2)`
/// (`1 ≤ sj ≤ 4`). For slot `(off, sym)` returns `(write, next_off, dir)` matching the quintuples of
/// [`crate::tm_power_block::lemma_power_block_step_block3`] under the state→offset map in the module docs.
/// Every unused slot is an inert self-loop.
pub open spec fn pbb3_act(off: nat, sym: nat, s0: nat, s1: nat, s2: nat) -> (nat, nat, Dir) {
    if off == 0 {            // q_dh0
        if sym == 0 { (0, 1, Dir::L) } else { (sym, 0, Dir::L) }
    } else if off == 1 {     // q_dw0
        if sym == 1 { (1, 1, Dir::L) }
        else if sym == 0 { (1, 2, Dir::R) }
        else { (sym, 1, Dir::L) }
    } else if off == 2 {     // q_bk0
        if sym == 1 { (1, 2, Dir::R) }
        else if sym == 0 { (0, 3, Dir::L) }
        else { (sym, 2, Dir::L) }
    } else if off == 3 {     // q_t0
        if sym == 1 { (1, 3, Dir::L) }
        else if sym == 0 { (0, 4, Dir::L) }
        else { (sym, 3, Dir::L) }
    } else if off == 4 {     // q_a0
        if sym == 0 { (0, 4, Dir::L) }
        else if sym == 1 { (5, 5, Dir::R) }
        else { (sym, 4, Dir::L) }
    } else if off == 5 {     // q_rf0
        if sym == 0 { (0, 6, Dir::R) }
        else { (sym, 5, Dir::L) }
    } else if off == 6 {     // q_rg0
        if sym == 0 { (0, 6, Dir::R) }
        else if sym == 1 { (1, 7, Dir::R) }
        else { (sym, 6, Dir::L) }
    } else if off == 7 {     // q_home
        if sym == 0 { (0, 8, Dir::L) }
        else if sym == 1 { (1, 7, Dir::R) }
        else { (sym, 7, Dir::L) }
    } else if off == 8 {     // q_t
        if sym == 1 { (1, 8, Dir::L) }
        else if sym == 0 { (0, 9, Dir::L) }
        else { (sym, 8, Dir::L) }
    } else if off == 9 {     // q_a
        if sym == 0 { (0, 9, Dir::L) }
        else if sym == 5 { (5, 10, Dir::L) }
        else { (sym, 9, Dir::L) }
    } else if off == 10 {    // q_b
        if sym == 5 { (5, 10, Dir::L) }
        else if sym == 1 { (5, 11, Dir::R) }
        else if sym == 0 { (0, 15, Dir::R) }
        else { (sym, 10, Dir::L) }
    } else if off == 11 {    // q_rf
        if sym == 5 { (5, 11, Dir::R) }
        else if sym == 0 { (0, 12, Dir::R) }
        else { (sym, 11, Dir::L) }
    } else if off == 12 {    // q_rg
        if sym == 0 { (0, 12, Dir::R) }
        else if sym == 1 { (1, 13, Dir::R) }
        else { (sym, 12, Dir::L) }
    } else if off == 13 {    // q_rt
        if sym == 1 { (1, 13, Dir::R) }
        else if sym == 0 { (0, 14, Dir::L) }
        else { (sym, 13, Dir::L) }
    } else if off == 14 {    // q_dw
        if sym == 1 { (1, 14, Dir::L) }
        else if sym == 0 { (1, 7, Dir::R) }
        else { (sym, 14, Dir::L) }
    } else if off == 15 {    // q_turn
        if sym == 5 { (5, 15, Dir::R) }
        else if sym == 0 { (0, 16, Dir::R) }
        else { (sym, 15, Dir::L) }
    } else if off == 16 {    // q_turng
        if sym == 0 { (0, 16, Dir::R) }
        else if sym == 1 { (1, 17, Dir::R) }
        else { (sym, 16, Dir::L) }
    } else if off == 17 {    // q_ret
        if sym == 1 { (1, 17, Dir::R) }
        else if sym == 0 { (0, 18, Dir::L) }
        else { (sym, 17, Dir::L) }
    } else if off == 18 {    // q_ut
        if sym == 1 { (1, 18, Dir::L) }
        else if sym == 0 { (0, 19, Dir::L) }
        else { (sym, 18, Dir::L) }
    } else if off == 19 {    // q_ua
        if sym == 0 { (0, 19, Dir::L) }
        else if sym == 5 { (1, 20, Dir::L) }
        else { (sym, 19, Dir::L) }
    } else if off == 20 {    // q_uf
        if sym == 5 { (1, 20, Dir::L) }
        else if sym == 0 { (0, 21, Dir::R) }
        else { (sym, 20, Dir::L) }
    } else if off == 21 {    // q_ur
        if sym == 1 { (1, 21, Dir::R) }
        else if sym == 0 { (0, 22, Dir::R) }
        else { (sym, 21, Dir::L) }
    } else if off == 22 {    // q_urg
        if sym == 0 { (0, 22, Dir::R) }
        else if sym == 1 { (1, 23, Dir::R) }
        else { (sym, 22, Dir::L) }
    } else if off == 23 {    // q_urt (= q_loop)
        if sym == 1 { (1, 23, Dir::R) }
        else if sym == 0 { (0, 24, Dir::L) }
        else { (sym, 23, Dir::L) }
    } else if off == 24 {    // q_guard
        if sym == 1 { (1, 25, Dir::R) }
        else if sym == 0 { (0, 33, Dir::R) }
        else { (sym, 24, Dir::L) }
    } else if off == 25 {    // q_iter
        if sym == 0 { (0, 26, Dir::R) }
        else { (sym, 25, Dir::L) }
    } else if off == 26 {    // q_surge
        if 1 <= sym && sym <= 4 { (sym, 26, Dir::R) }
        else if sym == 0 { (s0, 27, Dir::R) }
        else { (sym, 26, Dir::L) }
    } else if off == 27 {    // q_e1
        if sym == 0 { (s1, 28, Dir::R) }
        else { (sym, 27, Dir::L) }
    } else if off == 28 {    // q_e2
        if sym == 0 { (s2, 29, Dir::R) }
        else { (sym, 28, Dir::L) }
    } else if off == 29 {    // q_eret
        if sym == 0 { (0, 30, Dir::L) }
        else { (sym, 29, Dir::L) }
    } else if off == 30 {    // q_bhome
        if 1 <= sym && sym <= 4 { (sym, 30, Dir::L) }
        else if sym == 0 { (0, 31, Dir::L) }
        else { (sym, 30, Dir::L) }
    } else if off == 31 {    // q_dwalk
        if sym == 1 { (1, 31, Dir::L) }
        else if sym == 0 { (0, 32, Dir::R) }
        else { (sym, 31, Dir::L) }
    } else if off == 32 {    // q_disc
        if sym == 1 { (0, 23, Dir::R) }
        else { (sym, 32, Dir::L) }
    } else {                 // off 33 (q_exit, terminal) + offsets 34..47: inert
        (sym, off, Dir::L)
    }
}

/// The exit-parametric block3 generator: q-key `entry5(pc)+off`, action from [`pbb3_act`], EXCEPT the
/// loop-exit slot `(off 24, sym 0)` targets the external `qexit`. **Opaque** (§N+11 rlimit rule).
#[verifier::opaque]
pub open spec fn pbb3x_gen(s0: nat, s1: nat, s2: nat, qexit: nat, idx: nat) -> Quintuple {
    let pc = idx / 288;
    let off = (idx % 288) / 6;
    let sym = (idx % 288) % 6;
    if off == 24 && sym == 0 {
        mk_quint(entry5(pc) + 24, 0, 0, qexit, Dir::R)
    } else {
        let a = pbb3_act(off, sym, s0, s1, s2);
        mk_quint(entry5(pc) + off, sym, a.0, entry5(pc) + a.1, a.2)
    }
}

/// Every block3 action writes a real symbol (`≤ 5`) and targets an in-window offset (`< 48`).
pub proof fn lemma_pbb3_act_bounded(off: nat, sym: nat, s0: nat, s1: nat, s2: nat)
    requires
        off < 48,
        sym <= 5,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
    ensures
        pbb3_act(off, sym, s0, s1, s2).0 <= 5,
        pbb3_act(off, sym, s0, s1, s2).1 < 48,
{
}

// ─────────────────────────────────────────────────────────────────────────────
// Concrete validation machine well-formedness.
// ─────────────────────────────────────────────────────────────────────────────

/// A concrete block3 power-block TM with `len + 1` uniform windows (each runs the `(s0,s1,s2)^M` step;
/// the exit lands on the in-window terminal `entry5(pc)+33`).
pub open spec fn pbb3_tm(len: nat, s0: nat, s1: nat, s2: nat) -> Tm {
    Tm { n: 5, m: tm_mod5(len),
        quints: Seq::new(288 * (len + 1), |idx: int| pbb3x_gen(s0, s1, s2, entry5((idx as nat) / 288) + 33, idx as nat)) }
}

/// The concrete block3 machine is well-formed.
pub proof fn lemma_pbb3_tm_wf(len: nat, s0: nat, s1: nat, s2: nat)
    requires
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
    ensures
        tm_wf(pbb3_tm(len, s0, s1, s2)),
{
    reveal(pbb3x_gen);
    let tm = pbb3_tm(len, s0, s1, s2);
    assert(tm.quints.len() == 288 * (len + 1));
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 288 * (len + 1) implies
        tm.quints[idx].q == entry5((idx as nat) / 288) + ((idx as nat) % 288) / 6
        && tm.quints[idx].a == ((idx as nat) % 288) % 6 by {
        assert(tm.quints[idx] == pbb3x_gen(s0, s1, s2, entry5((idx as nat) / 288) + 33, idx as nat));
        lemma_idx5_decomp(idx as nat, len);
    }
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 288 * (len + 1) implies
        tm.quints[idx].a2 <= 5 && tm.quints[idx].q2 < tm.m by {
        assert(tm.quints[idx] == pbb3x_gen(s0, s1, s2, entry5((idx as nat) / 288) + 33, idx as nat));
        lemma_idx5_decomp(idx as nat, len);
        let pc = (idx as nat) / 288;
        let off = ((idx as nat) % 288) / 6;
        let sym = ((idx as nat) % 288) % 6;
        lemma_pbb3_act_bounded(off, sym, s0, s1, s2);
        // both the parametric exit target (entry5(pc)+33) and the in-window next (entry5(pc)+nx<48) are < m.
        assert(entry5(pc) + 33 < tm.m) by(nonlinear_arith)
            requires entry5(pc) == 6 + 48 * pc, pc <= len, tm.m == 54 + 48 * len;
        assert(entry5(pc) + pbb3_act(off, sym, s0, s1, s2).1 < tm.m) by(nonlinear_arith)
            requires entry5(pc) == 6 + 48 * pc, pc <= len, pbb3_act(off, sym, s0, s1, s2).1 < 48,
                tm.m == 54 + 48 * len;
    }
    lemma_tm_wf_n5(tm, len);
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-slot locators (heavy slot_index5 + gen-unfold work, done once).
// ─────────────────────────────────────────────────────────────────────────────

/// **Locate one NON-exit block3 quintuple** in an exit-parametric window.
proof fn locate_pbb3x(tm: Tm, len: nat, pc: nat, s0: nat, s1: nat, s2: nat, qexit: nat,
    off: nat, sym: nat, w: nat, nx: nat, d: Dir)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        off < 48,
        sym <= 5,
        !(off == 24 && sym == 0),
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        pbb3_act(off, sym, s0, s1, s2) == (w, nx, d),
    ensures
        0 <= pc * 288 + off * 6 + sym < tm.quints.len(),
        tm.quints[(pc * 288 + off * 6 + sym) as int]
            == mk_quint(entry5(pc) + off, sym, w, entry5(pc) + nx, d),
{
    reveal(pbb3x_gen);
    let idx = (pc * 288 + off * 6 + sym) as int;
    assert(off * 6 + sym < 288) by(nonlinear_arith) requires off < 48, sym <= 5;
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    assert(pc * 288 <= idx < pc * 288 + 288);
    lemma_slot_index5(pc, off, sym);
    assert(tm.quints[idx] == pbb3x_gen(s0, s1, s2, qexit, idx as nat));
    assert(pbb3x_gen(s0, s1, s2, qexit, idx as nat) == mk_quint(entry5(pc) + off, sym, w, entry5(pc) + nx, d));
}

/// **Locate the EXIT quintuple** `(q_guard, 0, 0, qexit, R)` of an exit-parametric block3 window.
proof fn locate_pbb3x_exit(tm: Tm, len: nat, pc: nat, s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
    ensures
        0 <= pc * 288 + 24 * 6 + 0 < tm.quints.len(),
        tm.quints[(pc * 288 + 24 * 6 + 0) as int]
            == mk_quint(entry5(pc) + 24, 0, 0, qexit, Dir::R),
{
    reveal(pbb3x_gen);
    let idx = (pc * 288 + 24 * 6 + 0) as int;
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    assert(pc * 288 <= idx < pc * 288 + 288);
    lemma_slot_index5(pc, 24, 0);
    assert(tm.quints[idx] == pbb3x_gen(s0, s1, s2, qexit, idx as nat));
}

// ─────────────────────────────────────────────────────────────────────────────
// The reusable triple power-block phase lemmas (M ≥ 2 and M = 1), abstract over the full machine.
// ─────────────────────────────────────────────────────────────────────────────

/// **Expose one off-0 self-loop** of a `pbb3x` window: `(q_dh0, sym, sym, q_dh0, L)` for `sym ∈ 1..4`.
/// The walk-back-compatible quints a preceding singleton consumes when `q_home := entry5(pc)` (§N+12).
pub proof fn lemma_pbb3x_walkback(tm: Tm, len: nat, pc: nat, s0: nat, s1: nat, s2: nat, qexit: nat, sym: nat)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        1 <= sym <= 4,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
    ensures
        0 <= pc * 288 + sym < tm.quints.len(),
        tm.quints[(pc * 288 + sym) as int] == mk_quint(entry5(pc), sym, sym, entry5(pc), Dir::L),
{
    locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 0, sym, sym, 0, Dir::L);
    assert(pc * 288 + 0 * 6 + sym == pc * 288 + sym);
}

/// **Triple power-block phase (one window, the `(s0,s1,s2)^M` periodic step, `M ≥ 2`).** From
/// `{u: copy_u(0,M,g), v: dpack(od), a: 0, q: entry5(pc)}` after `power_block_fuel_b3(M,g,|od|)` steps the
/// master is stationary, the output has grown by `(s0,s1,s2)^M`, and the head is on the home pivot in the
/// external `qexit`. The per-block atom the sequencer chains by state identification.
pub proof fn lemma_pbb3x_phase(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b3(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq_pow(seq![s0, s1, s2], big_m), tm.m), a: 0, q: qexit }),
{
    let e = entry5(pc);
    // ── copy_refresh j=0 deposit-first (off 0–6). ──
    let i_dpeel0 = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp0 = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins0  = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb0   = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 1, 1, 2, Dir::R);
    let i_peel0  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 0, 0, 3, Dir::L);
    let i_temp0  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 1, 1, 3, Dir::L);
    let i_t2g0   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 0, 0, 4, Dir::L);
    let i_gap0   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 0, 0, 4, Dir::L);
    let i_mark0  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 1, 5, 5, Dir::R);
    let i_rf2g0  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 5, 0, 0, 6, Dir::R);
    let i_rgap0  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 0, 0, 6, Dir::R);
    let i_rg2t0  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh home-cycle. ──
    let i_peel   = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 7, 0, 0, 8, Dir::L);
    let i_temp   = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 1, 1, 8, Dir::L);
    let i_t2g    = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 0, 0, 9, Dir::L);
    let i_gap    = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 0, 0, 9, Dir::L);
    let i_a2b    = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 5, 5, 10, Dir::L);
    let i_fives  = (pc * 288 + 10 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 5, 5, 10, Dir::L);
    let i_mark   = (pc * 288 + 10 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 1, 5, 11, Dir::R);
    let i_rfives = (pc * 288 + 11 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 11, 5, 5, 11, Dir::R);
    let i_rf2g   = (pc * 288 + 11 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 11, 0, 0, 12, Dir::R);
    let i_rgap   = (pc * 288 + 12 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 12, 0, 0, 12, Dir::R);
    let i_rg2t   = (pc * 288 + 12 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 12, 1, 1, 13, Dir::R);
    let i_rtemp  = (pc * 288 + 13 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 13, 1, 1, 13, Dir::R);
    let i_dpeel  = (pc * 288 + 13 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 13, 0, 0, 14, Dir::L);
    let i_dtemp  = (pc * 288 + 14 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 14, 1, 1, 14, Dir::L);
    let i_dins   = (pc * 288 + 14 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 14, 0, 1, 7, Dir::R);
    let i_dwb    = (pc * 288 + 7 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 7, 1, 1, 7, Dir::R);
    // ── copy_refresh terminate walk-back. ──
    let i_turn   = (pc * 288 + 10 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 0, 0, 15, Dir::R);
    let i_master = (pc * 288 + 15 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 1, 1, 17, Dir::R);
    let i_trtemp = (pc * 288 + 17 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 17, 1, 1, 17, Dir::R);
    // ── copy_refresh unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 5, 1, 20, Dir::L);
    let i_uurest = (pc * 288 + 20 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 20, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 1, 1, 23, Dir::R);
    let i_urtemp = (pc * 288 + 23 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 1, 1, 23, Dir::R);
    // ── block_loop (triple emit); exit → external qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb3x_exit(tm, len, pc, s0, s1, s2, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 4, 4, 26, Dir::R);
    let i_e0     = (pc * 288 + 26 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 0, s0, 27, Dir::R);
    let i_e1     = (pc * 288 + 27 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 27, 0, s1, 28, Dir::R);
    let i_e2     = (pc * 288 + 28 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 28, 0, s2, 29, Dir::R);
    let i_off_l  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 29, 0, 0, 30, Dir::L);
    let il1      = (pc * 288 + 30 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 1, 1, 30, Dir::L);
    let il2      = (pc * 288 + 30 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 2, 2, 30, Dir::L);
    let il3      = (pc * 288 + 30 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 3, 3, 30, Dir::L);
    let il4      = (pc * 288 + 30 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 4, 4, 30, Dir::L);
    let i_pivot  = (pc * 288 + 30 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 0, 0, 31, Dir::L);
    let i_one_l  = (pc * 288 + 31 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 1, 1, 31, Dir::L);
    let i_erase  = (pc * 288 + 31 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 0, 0, 32, Dir::R);
    let i_disc   = (pc * 288 + 32 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 32, 1, 0, 23, Dir::R);

    // ── invoke the verified triple power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block3(tm, big_m, g, od, s0, s1, s2,
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 7, e + 8, e + 9, e + 10, e + 11, e + 12, e + 13, e + 14,
        e + 15, e + 16, e + 17,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, e + 31, e + 32, qexit,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp,
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc);
}

/// **Triple power-block phase, the `M = 1` dispatch (same `pbb3x_gen` window).** As [`lemma_pbb3x_phase`]
/// but for a single master-unit, via [`lemma_power_block_step_block3_m1`] — every M=1 quint maps to a
/// `pbb3_act` slot with identical content (copy_refresh_m1 reuses off 0–10/15–23, the triple block_loop is
/// shared). The sequencer dispatches: `M = 1` → this lemma, `M ≥ 2` → [`lemma_pbb3x_phase`].
pub proof fn lemma_pbb3x_m1_phase(tm: Tm, len: nat, pc: nat, g: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        g >= 3,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b3_m1(g, od.len()))
            == (TmConfig { u: copy_u(0, 1, g, tm.m),
                v: dpack(od + seq_pow(seq![s0, s1, s2], 1), tm.m), a: 0, q: qexit }),
{
    let e = entry5(pc);
    // ── copy_refresh_m1 j=0 copy (off 0–6). ──
    let i_dpeel  = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp  = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins   = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb    = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 1, 1, 2, Dir::R);
    let i_cpeel  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 0, 0, 3, Dir::L);
    let i_ctemp  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 1, 1, 3, Dir::L);
    let i_ct2g   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 0, 0, 4, Dir::L);
    let i_cgap   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 0, 0, 4, Dir::L);
    let i_cmark  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 1, 5, 5, Dir::R);
    let i_crf2g  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 5, 0, 0, 6, Dir::R);
    let i_crgap  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 0, 0, 6, Dir::R);
    let i_crg2t  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh_m1 terminate (home == q_home == e+7). ──
    let i_tpeel  = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 7, 0, 0, 8, Dir::L);
    let i_ttemp  = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 1, 1, 8, Dir::L);
    let i_tt2g   = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 0, 0, 9, Dir::L);
    let i_tgap   = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 0, 0, 9, Dir::L);
    let i_ta2b   = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 5, 5, 10, Dir::L);
    let i_tturn  = (pc * 288 + 10 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 0, 0, 15, Dir::R);
    let i_tmaster= (pc * 288 + 15 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 1, 1, 17, Dir::R);
    // ── copy_refresh_m1 unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 1, 1, 23, Dir::R);
    // ── block_loop (triple emit, q_loop := q_urt == e+23), exit → qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb3x_exit(tm, len, pc, s0, s1, s2, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 4, 4, 26, Dir::R);
    let i_e0     = (pc * 288 + 26 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 0, s0, 27, Dir::R);
    let i_e1     = (pc * 288 + 27 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 27, 0, s1, 28, Dir::R);
    let i_e2     = (pc * 288 + 28 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 28, 0, s2, 29, Dir::R);
    let i_off_l  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 29, 0, 0, 30, Dir::L);
    let il1      = (pc * 288 + 30 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 1, 1, 30, Dir::L);
    let il2      = (pc * 288 + 30 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 2, 2, 30, Dir::L);
    let il3      = (pc * 288 + 30 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 3, 3, 30, Dir::L);
    let il4      = (pc * 288 + 30 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 4, 4, 30, Dir::L);
    let i_pivot  = (pc * 288 + 30 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 0, 0, 31, Dir::L);
    let i_one_l  = (pc * 288 + 31 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 1, 1, 31, Dir::L);
    let i_erase  = (pc * 288 + 31 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 0, 0, 32, Dir::R);
    let i_disc   = (pc * 288 + 32 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 32, 1, 0, 23, Dir::R);
    let i_one_r  = (pc * 288 + 23 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 1, 1, 23, Dir::R);

    // ── invoke the verified M=1 triple power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block3_m1(tm, g, od, s0, s1, s2,
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 8, e + 9, e + 10, e + 15, e + 16, e + 17, e + 7,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, e + 31, e + 32, qexit,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b,
        i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t,
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
}

/// Unified per-block fuel for the triple power-block: `M = 1` uses the m1 step, `M ≥ 2` the general step.
pub open spec fn pb3_fuel(big_m: nat, g: nat, odlen: nat) -> nat {
    if big_m == 1 { power_block_fuel_b3_m1(g, odlen) } else { power_block_fuel_b3(big_m, g, odlen) }
}

/// **Unified triple power-block phase (`M ≥ 1`, the sequencer's dispatch atom).** Dispatches the symbolic
/// master `M`: `M = 1` → [`lemma_pbb3x_m1_phase`], `M ≥ 2` → [`lemma_pbb3x_phase`]. Both emit
/// `seq_pow([s0,s1,s2], M)` over the SAME `pbb3x_gen` window and end on the home pivot in `qexit`.
pub proof fn lemma_pbb3x_phase_any(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb3_fuel(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq_pow(seq![s0, s1, s2], big_m), tm.m), a: 0, q: qexit }),
{
    if big_m == 1 {
        lemma_pbb3x_m1_phase(tm, len, pc, g, od, s0, s1, s2, qexit);
    } else {
        lemma_pbb3x_phase(tm, len, pc, big_m, g, od, s0, s1, s2, qexit);
    }
}

pub proof fn lemma_pbb3x_phase_tail_safe(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b3(big_m, g, od.len()), (g + big_m + 1) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b3(big_m, g, od.len()), (g + big_m + 1) as nat)
            == (g + big_m + 1) as nat,
{
    let e = entry5(pc);
    // ── copy_refresh j=0 deposit-first (off 0–6). ──
    let i_dpeel0 = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp0 = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins0  = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb0   = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 1, 1, 2, Dir::R);
    let i_peel0  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 0, 0, 3, Dir::L);
    let i_temp0  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 1, 1, 3, Dir::L);
    let i_t2g0   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 0, 0, 4, Dir::L);
    let i_gap0   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 0, 0, 4, Dir::L);
    let i_mark0  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 1, 5, 5, Dir::R);
    let i_rf2g0  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 5, 0, 0, 6, Dir::R);
    let i_rgap0  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 0, 0, 6, Dir::R);
    let i_rg2t0  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh home-cycle. ──
    let i_peel   = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 7, 0, 0, 8, Dir::L);
    let i_temp   = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 1, 1, 8, Dir::L);
    let i_t2g    = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 0, 0, 9, Dir::L);
    let i_gap    = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 0, 0, 9, Dir::L);
    let i_a2b    = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 5, 5, 10, Dir::L);
    let i_fives  = (pc * 288 + 10 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 5, 5, 10, Dir::L);
    let i_mark   = (pc * 288 + 10 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 1, 5, 11, Dir::R);
    let i_rfives = (pc * 288 + 11 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 11, 5, 5, 11, Dir::R);
    let i_rf2g   = (pc * 288 + 11 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 11, 0, 0, 12, Dir::R);
    let i_rgap   = (pc * 288 + 12 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 12, 0, 0, 12, Dir::R);
    let i_rg2t   = (pc * 288 + 12 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 12, 1, 1, 13, Dir::R);
    let i_rtemp  = (pc * 288 + 13 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 13, 1, 1, 13, Dir::R);
    let i_dpeel  = (pc * 288 + 13 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 13, 0, 0, 14, Dir::L);
    let i_dtemp  = (pc * 288 + 14 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 14, 1, 1, 14, Dir::L);
    let i_dins   = (pc * 288 + 14 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 14, 0, 1, 7, Dir::R);
    let i_dwb    = (pc * 288 + 7 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 7, 1, 1, 7, Dir::R);
    // ── copy_refresh terminate walk-back. ──
    let i_turn   = (pc * 288 + 10 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 0, 0, 15, Dir::R);
    let i_master = (pc * 288 + 15 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 1, 1, 17, Dir::R);
    let i_trtemp = (pc * 288 + 17 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 17, 1, 1, 17, Dir::R);
    // ── copy_refresh unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 5, 1, 20, Dir::L);
    let i_uurest = (pc * 288 + 20 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 20, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 1, 1, 23, Dir::R);
    let i_urtemp = (pc * 288 + 23 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 1, 1, 23, Dir::R);
    // ── block_loop (triple emit); exit → external qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb3x_exit(tm, len, pc, s0, s1, s2, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 4, 4, 26, Dir::R);
    let i_e0     = (pc * 288 + 26 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 0, s0, 27, Dir::R);
    let i_e1     = (pc * 288 + 27 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 27, 0, s1, 28, Dir::R);
    let i_e2     = (pc * 288 + 28 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 28, 0, s2, 29, Dir::R);
    let i_off_l  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 29, 0, 0, 30, Dir::L);
    let il1      = (pc * 288 + 30 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 1, 1, 30, Dir::L);
    let il2      = (pc * 288 + 30 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 2, 2, 30, Dir::L);
    let il3      = (pc * 288 + 30 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 3, 3, 30, Dir::L);
    let il4      = (pc * 288 + 30 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 4, 4, 30, Dir::L);
    let i_pivot  = (pc * 288 + 30 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 0, 0, 31, Dir::L);
    let i_one_l  = (pc * 288 + 31 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 1, 1, 31, Dir::L);
    let i_erase  = (pc * 288 + 31 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 0, 0, 32, Dir::R);
    let i_disc   = (pc * 288 + 32 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 32, 1, 0, 23, Dir::R);

    // ── invoke the verified triple power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block3_tail_safe(tm, big_m, g, od, s0, s1, s2,
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 7, e + 8, e + 9, e + 10, e + 11, e + 12, e + 13, e + 14,
        e + 15, e + 16, e + 17,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, e + 31, e + 32, qexit,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp,
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc);
}

pub proof fn lemma_pbb3x_m1_phase_tail_safe(tm: Tm, len: nat, pc: nat, g: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        g >= 3,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b3_m1(g, od.len()), (g + 2) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b3_m1(g, od.len()), (g + 2) as nat)
            == (g + 2) as nat,
{
    let e = entry5(pc);
    // ── copy_refresh_m1 j=0 copy (off 0–6). ──
    let i_dpeel  = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp  = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins   = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb    = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 1, 1, 2, Dir::R);
    let i_cpeel  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 2, 0, 0, 3, Dir::L);
    let i_ctemp  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 1, 1, 3, Dir::L);
    let i_ct2g   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 3, 0, 0, 4, Dir::L);
    let i_cgap   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 0, 0, 4, Dir::L);
    let i_cmark  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 4, 1, 5, 5, Dir::R);
    let i_crf2g  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 5, 0, 0, 6, Dir::R);
    let i_crgap  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 0, 0, 6, Dir::R);
    let i_crg2t  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh_m1 terminate (home == q_home == e+7). ──
    let i_tpeel  = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 7, 0, 0, 8, Dir::L);
    let i_ttemp  = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 1, 1, 8, Dir::L);
    let i_tt2g   = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 8, 0, 0, 9, Dir::L);
    let i_tgap   = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 0, 0, 9, Dir::L);
    let i_ta2b   = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 9, 5, 5, 10, Dir::L);
    let i_tturn  = (pc * 288 + 10 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 10, 0, 0, 15, Dir::R);
    let i_tmaster= (pc * 288 + 15 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 16, 1, 1, 17, Dir::R);
    // ── copy_refresh_m1 unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 19, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 22, 1, 1, 23, Dir::R);
    // ── block_loop (triple emit, q_loop := q_urt == e+23), exit → qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb3x_exit(tm, len, pc, s0, s1, s2, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 4, 4, 26, Dir::R);
    let i_e0     = (pc * 288 + 26 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 26, 0, s0, 27, Dir::R);
    let i_e1     = (pc * 288 + 27 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 27, 0, s1, 28, Dir::R);
    let i_e2     = (pc * 288 + 28 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 28, 0, s2, 29, Dir::R);
    let i_off_l  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 29, 0, 0, 30, Dir::L);
    let il1      = (pc * 288 + 30 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 1, 1, 30, Dir::L);
    let il2      = (pc * 288 + 30 * 6 + 2) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 2, 2, 30, Dir::L);
    let il3      = (pc * 288 + 30 * 6 + 3) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 3, 3, 30, Dir::L);
    let il4      = (pc * 288 + 30 * 6 + 4) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 4, 4, 30, Dir::L);
    let i_pivot  = (pc * 288 + 30 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 30, 0, 0, 31, Dir::L);
    let i_one_l  = (pc * 288 + 31 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 1, 1, 31, Dir::L);
    let i_erase  = (pc * 288 + 31 * 6 + 0) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 31, 0, 0, 32, Dir::R);
    let i_disc   = (pc * 288 + 32 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 32, 1, 0, 23, Dir::R);
    let i_one_r  = (pc * 288 + 23 * 6 + 1) as int; locate_pbb3x(tm, len, pc, s0, s1, s2, qexit, 23, 1, 1, 23, Dir::R);

    // ── invoke the verified M=1 triple power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block3_m1_tail_safe(tm, g, od, s0, s1, s2,
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 8, e + 9, e + 10, e + 15, e + 16, e + 17, e + 7,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, e + 31, e + 32, qexit,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b,
        i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t,
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
}

pub proof fn lemma_pbb3x_phase_any_tail_safe(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(s0, s1, s2, qexit, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb3_fuel(big_m, g, od.len()), (g + big_m + 1) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb3_fuel(big_m, g, od.len()), (g + big_m + 1) as nat)
            == (g + big_m + 1) as nat,
{
    if big_m == 1 {
        lemma_pbb3x_m1_phase_tail_safe(tm, len, pc, g, od, s0, s1, s2, qexit);
    } else {
        lemma_pbb3x_phase_tail_safe(tm, len, pc, big_m, g, od, s0, s1, s2, qexit);
    }
}

} // verus!
