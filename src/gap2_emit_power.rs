//! # GAP-2 G2-F Route (i) — the POWER-BLOCK window over the `assemble5` scaffold.
//!
//! The fattest emitter window: one full per-power-block PERIODIC step
//! ([`crate::tm_power_block::lemma_power_block_step_block1`]) — `copy_refresh ∘ block_loop`, which rebuilds
//! a fresh temp from the preserved master and consumes it emitting `(s)^M`, master stationary. It uses 32
//! distinct states (the widest in the build), here mapped to offsets `0..31` of one STRIDE=48 window, and
//! 64 quintuples. The single-digit power-blocks `(1)ⁱ` and `(3)ⁱ` of `fam_digits` are exactly this.
//!
//! Same recipe as [`crate::gap2_emit_window`] (singleton) and [`crate::gap2_psc_rp`] (read phase):
//! a window-local action table → manifest generator → `lemma_tm_wf_n5` (wf) → `lemma_slot_index5`
//! (locate the 64 quintuples) → the verified step lemma. The per-block atom the 16-block sequencer chains.
//!
//! ## State → offset map (block1)
//! ```
//!  0 q_dh0    8 q_t      16 q_turng  24 q_guard
//!  1 q_dw0    9 q_a      17 q_ret    25 q_iter
//!  2 q_bk0   10 q_b      18 q_ut     26 q_surge
//!  3 q_t0    11 q_rf     19 q_ua     27 q_eret
//!  4 q_a0    12 q_rg     20 q_uf     28 q_bhome
//!  5 q_rf0   13 q_rt     21 q_ur     29 q_dwalk
//!  6 q_rg0   14 q_dw     22 q_urg    30 q_disc
//!  7 q_home  15 q_turn   23 q_urt    31 q_exit  (terminal, no outgoing quint)
//! ```
//! (`q_urt` = the copy_refresh end = the block_loop home `q_loop`; offset 23 carries both its quints —
//! the free splice.)
//!
//! ## Z3 budget — the per-slot locator
//! 64 inline `lemma_slot_index5` + `pbb1_gen`-unfold sub-proofs in one body blow the rlimit (Z3 is
//! superlinear in proof size). [`locate_pbb1`] does that work ONCE generically; the phase lemma then makes
//! 64 cheap calls. `docs/gap2-input-loader-plan.md` §N+11. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, Quintuple, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_assemble5::{entry5, tm_mod5, lemma_tm_wf_n5, lemma_slot_index5, lemma_idx5_decomp};
use crate::tm_dstring::dpack;
use crate::tm_copy_refresh::copy_u;
use crate::gap2_relnum_dds::seq_pow;
use crate::tm_power_block::{power_block_fuel_b1, lemma_power_block_step_block1};
use crate::tm_power_block_m1::{power_block_fuel_b1_m1, lemma_power_block_step_block1_m1};

use crate::gap2_tail_lift::{tail_safe, tail_end_h};
use crate::gap2_tail_power::{lemma_power_block_step_block1_tail_safe, lemma_power_block_step_block1_m1_tail_safe};
use crate::gap2_tail_lift_v::{tail_safe_v, tail_end_h_v};
use crate::gap2_tail_power_v::{lemma_power_block_step_block1_tail_safe_v, lemma_power_block_step_block1_m1_tail_safe_v};
verus! {

// ─────────────────────────────────────────────────────────────────────────────
// The block1 power-block action table + generator (one window per power-block).
// Returns (write, next_off, dir); the absolute next state is entry5(pc) + next_off.
// ─────────────────────────────────────────────────────────────────────────────

/// The block1 power-block action table over a STRIDE=48 window, emit symbol `s` (`1 ≤ s ≤ 4`). For slot
/// `(off, sym)` returns `(write, next_off, dir)` matching the 64 quintuples of
/// [`crate::tm_power_block::lemma_power_block_step_block1`] under the state→offset map in the module docs.
/// Every unused slot is an inert self-loop (write the scanned symbol, stay, move L).
pub open spec fn pbb1_act(off: nat, sym: nat, s: nat) -> (nat, nat, Dir) {
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
        else if sym == 0 { (0, 31, Dir::R) }
        else { (sym, 24, Dir::L) }
    } else if off == 25 {    // q_iter
        if sym == 0 { (0, 26, Dir::R) }
        else { (sym, 25, Dir::L) }
    } else if off == 26 {    // q_surge
        if 1 <= sym && sym <= 4 { (sym, 26, Dir::R) }
        else if sym == 0 { (s, 27, Dir::R) }
        else { (sym, 26, Dir::L) }
    } else if off == 27 {    // q_eret
        if sym == 0 { (0, 28, Dir::L) }
        else { (sym, 27, Dir::L) }
    } else if off == 28 {    // q_bhome
        if 1 <= sym && sym <= 4 { (sym, 28, Dir::L) }
        else if sym == 0 { (0, 29, Dir::L) }
        else { (sym, 28, Dir::L) }
    } else if off == 29 {    // q_dwalk
        if sym == 1 { (1, 29, Dir::L) }
        else if sym == 0 { (0, 30, Dir::R) }
        else { (sym, 29, Dir::L) }
    } else if off == 30 {    // q_disc
        if sym == 1 { (0, 23, Dir::R) }
        else { (sym, 30, Dir::L) }
    } else {                 // off 31 (q_exit, terminal) + offsets 32..47: inert
        (sym, off, Dir::L)
    }
}

/// The block1 power-block generator: manifest-keyed quintuple for flat index `idx` — q-key
/// `entry5(pc)+off`, scanned `sym`, action from [`pbb1_act`] (next state `entry5(pc)+next_off`). Every
/// window emits `s`.
///
/// **Opaque** so the window-hypothesis `forall i. tm.quints[i] == pbb1_gen(s,i)` does NOT drag the
/// 32-branch [`pbb1_act`] if-chain into the SMT context on every instantiation (a 79%-of-cost trigger
/// storm). Revealed only in [`locate_pbb1`] / [`lemma_pbb1_tm_wf`] where the unfold is actually needed.
#[verifier::opaque]
pub open spec fn pbb1_gen(s: nat, idx: nat) -> Quintuple {
    let pc = idx / 288;
    let off = (idx % 288) / 6;
    let sym = (idx % 288) % 6;
    let a = pbb1_act(off, sym, s);
    mk_quint(entry5(pc) + off, sym, a.0, entry5(pc) + a.1, a.2)
}

/// Every block1 action writes a real symbol (`≤ 5`) and targets an in-window offset (`< 48`).
pub proof fn lemma_pbb1_act_bounded(off: nat, sym: nat, s: nat)
    requires
        off < 48,
        sym <= 5,
        1 <= s <= 4,
    ensures
        pbb1_act(off, sym, s).0 <= 5,
        pbb1_act(off, sym, s).1 < 48,
{
    // every branch: write ∈ {0,1,2,3,4,5,s,sym} ≤ 5; next_off ∈ {literals ≤ 31, off} < 48.
}

// ─────────────────────────────────────────────────────────────────────────────
// Concrete validation machine well-formedness.
// ─────────────────────────────────────────────────────────────────────────────

/// A concrete block1 power-block TM with `len + 1` uniform windows (each runs the `(s)^M` step).
pub open spec fn pbb1_tm(len: nat, s: nat) -> Tm {
    Tm { n: 5, m: tm_mod5(len), quints: Seq::new(288 * (len + 1), |idx: int| pbb1_gen(s, idx as nat)) }
}

/// The concrete block1 machine is well-formed (discharges the [`lemma_tm_wf_n5`] hypotheses for
/// [`pbb1_gen`]).
pub proof fn lemma_pbb1_tm_wf(len: nat, s: nat)
    requires
        1 <= s <= 4,
    ensures
        tm_wf(pbb1_tm(len, s)),
{
    reveal(pbb1_gen);
    let tm = pbb1_tm(len, s);
    assert(tm.quints.len() == 288 * (len + 1));
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 288 * (len + 1) implies
        tm.quints[idx].q == entry5((idx as nat) / 288) + ((idx as nat) % 288) / 6
        && tm.quints[idx].a == ((idx as nat) % 288) % 6 by {
        assert(tm.quints[idx] == pbb1_gen(s, idx as nat));
    }
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 288 * (len + 1) implies
        tm.quints[idx].a2 <= 5 && tm.quints[idx].q2 < tm.m by {
        assert(tm.quints[idx] == pbb1_gen(s, idx as nat));
        lemma_idx5_decomp(idx as nat, len);   // pc ≤ len, off < 48, sym ≤ 5
        let pc = (idx as nat) / 288;
        let off = ((idx as nat) % 288) / 6;
        let sym = ((idx as nat) % 288) % 6;
        lemma_pbb1_act_bounded(off, sym, s);
        assert(entry5(pc) + pbb1_act(off, sym, s).1 < tm.m) by(nonlinear_arith)
            requires entry5(pc) == 6 + 48 * pc, pc <= len, pbb1_act(off, sym, s).1 < 48,
                tm.m == 54 + 48 * len;
    }
    lemma_tm_wf_n5(tm, len);
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-slot locator (the heavy slot_index5 + pbb1_gen-unfold work, done once).
// ─────────────────────────────────────────────────────────────────────────────

/// **Locate one block1 quintuple.** Given the window-`pc` carries `pbb1_gen(s,·)` and the caller proves
/// `pbb1_act(off, sym, s) == (w, nx, d)` (a literal eval at the call), the slot `(pc, off, sym)` holds the
/// quintuple `mk_quint(entry5(pc)+off, sym, w, entry5(pc)+nx, d)` and is in range. Factors the heavy
/// `lemma_slot_index5` + generator-unfold out of the 64-quint phase lemma so it stays under the rlimit.
proof fn locate_pbb1(tm: Tm, len: nat, pc: nat, s: nat, off: nat, sym: nat, w: nat, nx: nat, d: Dir)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        off < 48,
        sym <= 5,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1_gen(s, i as nat),
        pbb1_act(off, sym, s) == (w, nx, d),
    ensures
        0 <= pc * 288 + off * 6 + sym < tm.quints.len(),
        tm.quints[(pc * 288 + off * 6 + sym) as int]
            == mk_quint(entry5(pc) + off, sym, w, entry5(pc) + nx, d),
{
    reveal(pbb1_gen);
    let idx = (pc * 288 + off * 6 + sym) as int;
    assert(off * 6 + sym < 288) by(nonlinear_arith) requires off < 48, sym <= 5;
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    assert(pc * 288 <= idx < pc * 288 + 288);
    lemma_slot_index5(pc, off, sym);
    assert(tm.quints[idx] == pbb1_gen(s, idx as nat));
    assert(pbb1_gen(s, idx as nat) == mk_quint(entry5(pc) + off, sym, w, entry5(pc) + nx, d));
}

// ─────────────────────────────────────────────────────────────────────────────
// The reusable power-block phase lemma (abstract over the full machine).
// ─────────────────────────────────────────────────────────────────────────────

/// **Expose one off-0 self-loop** of a `pbb1x` window: `(q_dh0, sym, sym, q_dh0, L)` for `sym ∈ 1..4`
/// (the inert read-1..4 self-loops at `entry5(pc)`). These are exactly the WALK-BACK-COMPATIBLE quints a
/// PRECEDING singleton needs when its `q_home := entry5(pc)` (the two-window splice, §N+12). The chain
/// supplies `jl1..jl4` to `lemma_seret*x_phase` by calling this on the next window for `sym = 1,2,3,4`.
pub proof fn lemma_pbb1x_walkback(tm: Tm, len: nat, pc: nat, s: nat, qexit: nat, sym: nat)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        1 <= sym <= 4,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
    ensures
        0 <= pc * 288 + sym < tm.quints.len(),
        tm.quints[(pc * 288 + sym) as int] == mk_quint(entry5(pc), sym, sym, entry5(pc), Dir::L),
{
    locate_pbb1x(tm, len, pc, s, qexit, 0, sym, sym, 0, Dir::L);
    assert(pc * 288 + 0 * 6 + sym == pc * 288 + sym);
}

/// **Power-block phase (one window, the `(s)^M` periodic step).** Any well-formed n=5 assemble5 machine
/// whose window `pc` carries the block1 action table (`tm.quints[i] == pbb1_gen(s, i)` for `i` in window
/// `pc`) runs one full `copy_refresh ∘ block_loop`: from `{u: copy_u(0,M,g), v: dpack(od), a: 0,
/// q: entry5(pc)}` (master parked at gap `g`, head on the home pivot), after `power_block_fuel_b1(M, g,
/// |od|)` steps the master is back at the same position and the output has grown by `(s)^M`:
/// `{u: copy_u(0,M,g), v: dpack(od ++ seq_pow([s], M)), a: 0, q: entry5(pc)+31}`.
///
/// Mirrors [`crate::gap2_psc_rp::lemma_rp_phase`] / [`crate::gap2_emit_window::lemma_seret1_phase`]; the
/// per-block atom the 16-block sequencer chains by state identification (`q_dh0 = entry5(pc)`,
/// `q_exit = entry5(pc)+31`).
pub proof fn lemma_pbb1_phase(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1_gen(s, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq_pow(seq![s], big_m), tm.m), a: 0, q: entry5(pc) + 31 }),
{
    let e = entry5(pc);
    // ── locate all 64 quintuples (each a cheap locate_pbb1 call; off/sym/write/next/dir per the map). ──
    // (A) copy_refresh j=0 deposit-first
    let i_dpeel0 = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 0, 0, 0, 1, Dir::L);
    let i_dtemp0 = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 1, 1, 1, 1, Dir::L);
    let i_dins0  = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 1, 0, 1, 2, Dir::R);
    let i_dwb0   = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 2, 1, 1, 2, Dir::R);
    let i_peel0  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 2, 0, 0, 3, Dir::L);
    let i_temp0  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 3, 1, 1, 3, Dir::L);
    let i_t2g0   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 3, 0, 0, 4, Dir::L);
    let i_gap0   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 4, 0, 0, 4, Dir::L);
    let i_mark0  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 4, 1, 5, 5, Dir::R);
    let i_rf2g0  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 5, 0, 0, 6, Dir::R);
    let i_rgap0  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 6, 0, 0, 6, Dir::R);
    let i_rg2t0  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 6, 1, 1, 7, Dir::R);
    // (B) copy_refresh home-cycle
    let i_peel   = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 7, 0, 0, 8, Dir::L);
    let i_temp   = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 8, 1, 1, 8, Dir::L);
    let i_t2g    = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 8, 0, 0, 9, Dir::L);
    let i_gap    = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1(tm, len, pc, s, 9, 0, 0, 9, Dir::L);
    let i_a2b    = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1(tm, len, pc, s, 9, 5, 5, 10, Dir::L);
    let i_fives  = (pc * 288 + 10 * 6 + 5) as int; locate_pbb1(tm, len, pc, s, 10, 5, 5, 10, Dir::L);
    let i_mark   = (pc * 288 + 10 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 10, 1, 5, 11, Dir::R);
    let i_rfives = (pc * 288 + 11 * 6 + 5) as int; locate_pbb1(tm, len, pc, s, 11, 5, 5, 11, Dir::R);
    let i_rf2g   = (pc * 288 + 11 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 11, 0, 0, 12, Dir::R);
    let i_rgap   = (pc * 288 + 12 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 12, 0, 0, 12, Dir::R);
    let i_rg2t   = (pc * 288 + 12 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 12, 1, 1, 13, Dir::R);
    let i_rtemp  = (pc * 288 + 13 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 13, 1, 1, 13, Dir::R);
    let i_dpeel  = (pc * 288 + 13 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 13, 0, 0, 14, Dir::L);
    let i_dtemp  = (pc * 288 + 14 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 14, 1, 1, 14, Dir::L);
    let i_dins   = (pc * 288 + 14 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 14, 0, 1, 7, Dir::R);
    let i_dwb    = (pc * 288 + 7 * 6 + 1) as int;  locate_pbb1(tm, len, pc, s, 7, 1, 1, 7, Dir::R);
    // (C) copy_refresh terminate walk-back
    let i_turn   = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 10, 0, 0, 15, Dir::R);
    let i_master = (pc * 288 + 15 * 6 + 5) as int; locate_pbb1(tm, len, pc, s, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 16, 1, 1, 17, Dir::R);
    let i_trtemp = (pc * 288 + 17 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 17, 1, 1, 17, Dir::R);
    // (D) copy_refresh unmark (home == q_ret == e+17)
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1(tm, len, pc, s, 19, 5, 1, 20, Dir::L);
    let i_uurest = (pc * 288 + 20 * 6 + 5) as int; locate_pbb1(tm, len, pc, s, 20, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 22, 1, 1, 23, Dir::R);
    let i_urtemp = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 23, 1, 1, 23, Dir::R);
    // (E) block_loop
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 24, 0, 0, 31, Dir::R);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1(tm, len, pc, s, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1(tm, len, pc, s, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1(tm, len, pc, s, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1(tm, len, pc, s, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1(tm, len, pc, s, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1(tm, len, pc, s, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1(tm, len, pc, s, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1(tm, len, pc, s, 30, 1, 0, 23, Dir::R);

    // ── invoke the verified power-block step (q_dh0 = e, q_exit = e+31). ──
    lemma_power_block_step_block1(tm, big_m, g, od, s,
        // states (off 0..31)
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 7, e + 8, e + 9, e + 10, e + 11, e + 12, e + 13, e + 14,
        e + 15, e + 16, e + 17,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, e + 31,
        // copy_refresh quint indices
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc);
}

/// **Concrete power-block validation.** The standalone machine runs the `(s)^M` step exactly as
/// [`lemma_pbb1_phase`] promises — confirming the assemble5 ↔ power-block-step composition end-to-end.
pub proof fn lemma_pbb1_emit(len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat)
    requires
        pc <= len,
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(pbb1_tm(len, s),
            TmConfig { u: copy_u(0, big_m, g, tm_mod5(len)), v: dpack(od, tm_mod5(len)), a: 0,
                q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm_mod5(len)),
                v: dpack(od + seq_pow(seq![s], big_m), tm_mod5(len)), a: 0, q: entry5(pc) + 31 }),
{
    let tm = pbb1_tm(len, s);
    lemma_pbb1_tm_wf(len, s);
    assert(tm.m == tm_mod5(len));
    assert forall|i: int| pc * 288 <= i < pc * 288 + 288 implies #[trigger] tm.quints[i] == pbb1_gen(s, i as nat) by {
        assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    }
    lemma_pbb1_phase(tm, len, pc, big_m, g, od, s);
}

// ─────────────────────────────────────────────────────────────────────────────
// EXIT-PARAMETRIC power-block window — the 16-block SEQUENCER building block (§N+11).
//
// The N+11 splice resolution: instead of the in-window terminal `q_exit = entry5(pc)+31`, the loop-exit
// transition `(q_guard, 0, 0, ·, R)` targets an ARBITRARY external state `qexit`. The sequencer sets
//   qexit := entry5(pc+1)   for a MIDDLE block  (cross-window edge → next block's q_dh0 = entry5(pc+1));
//   qexit := q_cmp          for the LAST block   (hand-off to R-cmp).
// Because the step's END config is `{a:0, q:qexit, head on home pivot}` and block k+1's lemma assumes
// `{a:0, q:entry5(pc+1), head on home pivot}`, setting `qexit = entry5(pc+1)` makes
// `Config_term(k) ≡ Config_init(k+1)` IDENTICALLY — the chain splices with NO bridge proofs.
// ─────────────────────────────────────────────────────────────────────────────

/// The exit-parametric block1 power-block generator: identical to [`pbb1_gen`] EXCEPT the loop-exit slot
/// `(off 24, sym 0)` targets the external state `qexit` (instead of the in-window terminal
/// `entry5(pc)+31`). Opaque for the same trigger-storm reason as [`pbb1_gen`] (§N+11 rlimit pitfall).
#[verifier::opaque]
pub open spec fn pbb1x_gen(s: nat, qexit: nat, idx: nat) -> Quintuple {
    let pc = idx / 288;
    let off = (idx % 288) / 6;
    let sym = (idx % 288) % 6;
    if off == 24 && sym == 0 {
        mk_quint(entry5(pc) + 24, 0, 0, qexit, Dir::R)          // the parametric exit edge
    } else {
        let a = pbb1_act(off, sym, s);
        mk_quint(entry5(pc) + off, sym, a.0, entry5(pc) + a.1, a.2)
    }
}

/// **Locate one NON-exit block1 quintuple** in an exit-parametric window. Mirror of [`locate_pbb1`]; the
/// exit slot `(24, 0)` is excluded (`!(off == 24 && sym == 0)`) so [`pbb1x_gen`] reduces to the `pbb1_act`
/// branch, identical to [`pbb1_gen`].
proof fn locate_pbb1x(tm: Tm, len: nat, pc: nat, s: nat, qexit: nat, off: nat, sym: nat, w: nat, nx: nat, d: Dir)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        off < 48,
        sym <= 5,
        !(off == 24 && sym == 0),
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        pbb1_act(off, sym, s) == (w, nx, d),
    ensures
        0 <= pc * 288 + off * 6 + sym < tm.quints.len(),
        tm.quints[(pc * 288 + off * 6 + sym) as int]
            == mk_quint(entry5(pc) + off, sym, w, entry5(pc) + nx, d),
{
    reveal(pbb1x_gen);
    let idx = (pc * 288 + off * 6 + sym) as int;
    assert(off * 6 + sym < 288) by(nonlinear_arith) requires off < 48, sym <= 5;
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    assert(pc * 288 <= idx < pc * 288 + 288);
    lemma_slot_index5(pc, off, sym);
    assert(tm.quints[idx] == pbb1x_gen(s, qexit, idx as nat));
    assert(pbb1x_gen(s, qexit, idx as nat) == mk_quint(entry5(pc) + off, sym, w, entry5(pc) + nx, d));
}

/// **Locate the EXIT quintuple** `(q_guard, 0, 0, qexit, R)` of an exit-parametric window (slot `(24, 0)`).
proof fn locate_pbb1x_exit(tm: Tm, len: nat, pc: nat, s: nat, qexit: nat)
    requires
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
    ensures
        0 <= pc * 288 + 24 * 6 + 0 < tm.quints.len(),
        tm.quints[(pc * 288 + 24 * 6 + 0) as int]
            == mk_quint(entry5(pc) + 24, 0, 0, qexit, Dir::R),
{
    reveal(pbb1x_gen);
    let idx = (pc * 288 + 24 * 6 + 0) as int;
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    assert(pc * 288 <= idx < pc * 288 + 288);
    lemma_slot_index5(pc, 24, 0);
    assert(tm.quints[idx] == pbb1x_gen(s, qexit, idx as nat));
}

/// **Exit-parametric power-block phase (one window, the `(s)^M` periodic step).** As [`lemma_pbb1_phase`]
/// but the loop-exit lands on the EXTERNAL state `qexit` rather than the in-window terminal. From
/// `{u: copy_u(0,M,g), v: dpack(od), a: 0, q: entry5(pc)}` after `power_block_fuel_b1(M,g,|od|)` steps the
/// master is back at the same position, output grown by `(s)^M`, and the head sits on the home pivot in
/// state `qexit`: `{u: copy_u(0,M,g), v: dpack(od ++ (s)^M), a: 0, q: qexit}`.
///
/// The per-block atom the 16-block sequencer chains by state identification — set `qexit = entry5(pc+1)`
/// to make `Config_term(k) ≡ Config_init(k+1)` for the next block, or `qexit = q_cmp` for the last block.
pub proof fn lemma_pbb1x_phase(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq_pow(seq![s], big_m), tm.m), a: 0, q: qexit }),
{
    let e = entry5(pc);
    // ── locate all 64 quintuples (cheap locate_pbb1x calls; the exit via locate_pbb1x_exit → qexit). ──
    // (A) copy_refresh j=0 deposit-first
    let i_dpeel0 = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp0 = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins0  = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb0   = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 1, 1, 2, Dir::R);
    let i_peel0  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 0, 0, 3, Dir::L);
    let i_temp0  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 1, 1, 3, Dir::L);
    let i_t2g0   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 0, 0, 4, Dir::L);
    let i_gap0   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 0, 0, 4, Dir::L);
    let i_mark0  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 1, 5, 5, Dir::R);
    let i_rf2g0  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 5, 0, 0, 6, Dir::R);
    let i_rgap0  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 0, 0, 6, Dir::R);
    let i_rg2t0  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 1, 1, 7, Dir::R);
    // (B) copy_refresh home-cycle
    let i_peel   = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 0, 0, 8, Dir::L);
    let i_temp   = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 1, 1, 8, Dir::L);
    let i_t2g    = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 0, 0, 9, Dir::L);
    let i_gap    = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 0, 0, 9, Dir::L);
    let i_a2b    = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 5, 5, 10, Dir::L);
    let i_fives  = (pc * 288 + 10 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 5, 5, 10, Dir::L);
    let i_mark   = (pc * 288 + 10 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 1, 5, 11, Dir::R);
    let i_rfives = (pc * 288 + 11 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 11, 5, 5, 11, Dir::R);
    let i_rf2g   = (pc * 288 + 11 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 11, 0, 0, 12, Dir::R);
    let i_rgap   = (pc * 288 + 12 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 12, 0, 0, 12, Dir::R);
    let i_rg2t   = (pc * 288 + 12 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 12, 1, 1, 13, Dir::R);
    let i_rtemp  = (pc * 288 + 13 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 13, 1, 1, 13, Dir::R);
    let i_dpeel  = (pc * 288 + 13 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 13, 0, 0, 14, Dir::L);
    let i_dtemp  = (pc * 288 + 14 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 14, 1, 1, 14, Dir::L);
    let i_dins   = (pc * 288 + 14 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 14, 0, 1, 7, Dir::R);
    let i_dwb    = (pc * 288 + 7 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 1, 1, 7, Dir::R);
    // (C) copy_refresh terminate walk-back
    let i_turn   = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 0, 0, 15, Dir::R);
    let i_master = (pc * 288 + 15 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 1, 1, 17, Dir::R);
    let i_trtemp = (pc * 288 + 17 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 1, 1, 17, Dir::R);
    // (D) copy_refresh unmark (home == q_ret == e+17)
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 5, 1, 20, Dir::L);
    let i_uurest = (pc * 288 + 20 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 1, 1, 23, Dir::R);
    let i_urtemp = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 1, 1, 23, Dir::R);
    // (E) block_loop — the exit slot targets the EXTERNAL qexit.
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1x_exit(tm, len, pc, s, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 30, 1, 0, 23, Dir::R);

    // ── invoke the verified power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block1(tm, big_m, g, od, s,
        // states (off 0..30, then the EXTERNAL exit qexit)
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 7, e + 8, e + 9, e + 10, e + 11, e + 12, e + 13, e + 14,
        e + 15, e + 16, e + 17,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, qexit,
        // copy_refresh quint indices
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc);
}

/// **Exit-parametric power-block phase, the `M = 1` dispatch (same `pbb1x_gen` window).** The M=1 step
/// ([`lemma_power_block_step_block1_m1`]) needs a SUBSET of the M≥2 quints — every M=1 quint maps to a
/// `pbb1_act` slot with byte-identical content (verified: the m1 copy lands directly on the pivot, reusing
/// the off 0–10/15–23 states and skipping off 11–14's home-cycle), so NO separate window is needed. The
/// sequencer dispatches on the symbolic master `M`: `M = 1` → this lemma, `M ≥ 2` → [`lemma_pbb1x_phase`].
/// From `{u: copy_u(0,1,g), v: dpack(od), a: 0, q: entry5(pc)}` after `power_block_fuel_b1_m1(g, |od|)`
/// steps: `{u: copy_u(0,1,g), v: dpack(od ++ [s]), a: 0, q: qexit}`.
pub proof fn lemma_pbb1x_m1_phase(tm: Tm, len: nat, pc: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        g >= 3,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1_m1(g, od.len()))
            == (TmConfig { u: copy_u(0, 1, g, tm.m),
                v: dpack(od + seq_pow(seq![s], 1), tm.m), a: 0, q: qexit }),
{
    let e = entry5(pc);
    // ── copy_refresh_m1 j=0 copy (off 0–6). ──
    let i_dpeel  = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp  = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins   = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb    = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 1, 1, 2, Dir::R);
    let i_cpeel  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 0, 0, 3, Dir::L);
    let i_ctemp  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 1, 1, 3, Dir::L);
    let i_ct2g   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 0, 0, 4, Dir::L);
    let i_cgap   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 0, 0, 4, Dir::L);
    let i_cmark  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 1, 5, 5, Dir::R);
    let i_crf2g  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 5, 0, 0, 6, Dir::R);
    let i_crgap  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 0, 0, 6, Dir::R);
    let i_crg2t  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh_m1 terminate (home == q_home == e+7). ──
    let i_tpeel  = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 0, 0, 8, Dir::L);
    let i_ttemp  = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 1, 1, 8, Dir::L);
    let i_tt2g   = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 0, 0, 9, Dir::L);
    let i_tgap   = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 0, 0, 9, Dir::L);
    let i_ta2b   = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 5, 5, 10, Dir::L);
    let i_tturn  = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 0, 0, 15, Dir::R);
    let i_tmaster= (pc * 288 + 15 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 1, 1, 17, Dir::R);
    // ── copy_refresh_m1 unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 1, 1, 23, Dir::R);
    // ── block_loop (q_loop := q_urt == e+23), exit → qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1x_exit(tm, len, pc, s, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 30, 1, 0, 23, Dir::R);
    let i_one_r  = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 1, 1, 23, Dir::R);

    // ── invoke the verified M=1 power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block1_m1(tm, g, od, s,
        // states: off 0–6, then q_t=e+8 q_a=e+9 q_b=e+10 q_turn=e+15 q_turng=e+16 q_ret=e+17 q_home=e+7,
        //         q_ut=e+18..q_urt=e+23, block_loop e+24..e+30, qexit.
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 8, e + 9, e + 10, e + 15, e + 16, e + 17, e + 7,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, qexit,
        // copy_refresh_m1 quint indices
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b,
        i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
}

/// Unified per-block fuel for the single power-block: `M = 1` uses the m1 step, `M ≥ 2` the general step.
pub open spec fn pb1_fuel(big_m: nat, g: nat, odlen: nat) -> nat {
    if big_m == 1 { power_block_fuel_b1_m1(g, odlen) } else { power_block_fuel_b1(big_m, g, odlen) }
}

/// **Unified single power-block phase (`M ≥ 1`, the sequencer's dispatch atom).** Dispatches the symbolic
/// master `M`: `M = 1` → [`lemma_pbb1x_m1_phase`], `M ≥ 2` → [`lemma_pbb1x_phase`]. Both emit
/// `seq_pow([s], M)` over the SAME `pbb1x_gen` window and end on the home pivot in `qexit`. Since the
/// loaded master is `a+1 = i ≥ 1` (never 0, §N+12), this is the only dispatch the chain needs.
pub proof fn lemma_pbb1x_phase_any(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb1_fuel(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq_pow(seq![s], big_m), tm.m), a: 0, q: qexit }),
{
    if big_m == 1 {
        lemma_pbb1x_m1_phase(tm, len, pc, g, od, s, qexit);
    } else {
        lemma_pbb1x_phase(tm, len, pc, big_m, g, od, s, qexit);
    }
}

pub proof fn lemma_pbb1x_phase_tail_safe(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()), (g + big_m + 1) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()), (g + big_m + 1) as nat)
            == (g + big_m + 1) as nat,
{
    let e = entry5(pc);
    // ── locate all 64 quintuples (cheap locate_pbb1x calls; the exit via locate_pbb1x_exit → qexit). ──
    // (A) copy_refresh j=0 deposit-first
    let i_dpeel0 = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp0 = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins0  = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb0   = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 1, 1, 2, Dir::R);
    let i_peel0  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 0, 0, 3, Dir::L);
    let i_temp0  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 1, 1, 3, Dir::L);
    let i_t2g0   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 0, 0, 4, Dir::L);
    let i_gap0   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 0, 0, 4, Dir::L);
    let i_mark0  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 1, 5, 5, Dir::R);
    let i_rf2g0  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 5, 0, 0, 6, Dir::R);
    let i_rgap0  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 0, 0, 6, Dir::R);
    let i_rg2t0  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 1, 1, 7, Dir::R);
    // (B) copy_refresh home-cycle
    let i_peel   = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 0, 0, 8, Dir::L);
    let i_temp   = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 1, 1, 8, Dir::L);
    let i_t2g    = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 0, 0, 9, Dir::L);
    let i_gap    = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 0, 0, 9, Dir::L);
    let i_a2b    = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 5, 5, 10, Dir::L);
    let i_fives  = (pc * 288 + 10 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 5, 5, 10, Dir::L);
    let i_mark   = (pc * 288 + 10 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 1, 5, 11, Dir::R);
    let i_rfives = (pc * 288 + 11 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 11, 5, 5, 11, Dir::R);
    let i_rf2g   = (pc * 288 + 11 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 11, 0, 0, 12, Dir::R);
    let i_rgap   = (pc * 288 + 12 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 12, 0, 0, 12, Dir::R);
    let i_rg2t   = (pc * 288 + 12 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 12, 1, 1, 13, Dir::R);
    let i_rtemp  = (pc * 288 + 13 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 13, 1, 1, 13, Dir::R);
    let i_dpeel  = (pc * 288 + 13 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 13, 0, 0, 14, Dir::L);
    let i_dtemp  = (pc * 288 + 14 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 14, 1, 1, 14, Dir::L);
    let i_dins   = (pc * 288 + 14 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 14, 0, 1, 7, Dir::R);
    let i_dwb    = (pc * 288 + 7 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 1, 1, 7, Dir::R);
    // (C) copy_refresh terminate walk-back
    let i_turn   = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 0, 0, 15, Dir::R);
    let i_master = (pc * 288 + 15 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 1, 1, 17, Dir::R);
    let i_trtemp = (pc * 288 + 17 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 1, 1, 17, Dir::R);
    // (D) copy_refresh unmark (home == q_ret == e+17)
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 5, 1, 20, Dir::L);
    let i_uurest = (pc * 288 + 20 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 1, 1, 23, Dir::R);
    let i_urtemp = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 1, 1, 23, Dir::R);
    // (E) block_loop — the exit slot targets the EXTERNAL qexit.
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1x_exit(tm, len, pc, s, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 30, 1, 0, 23, Dir::R);

    // ── invoke the verified power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block1_tail_safe(tm, big_m, g, od, s,
        // states (off 0..30, then the EXTERNAL exit qexit)
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 7, e + 8, e + 9, e + 10, e + 11, e + 12, e + 13, e + 14,
        e + 15, e + 16, e + 17,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, qexit,
        // copy_refresh quint indices
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc);
}

pub proof fn lemma_pbb1x_m1_phase_tail_safe(tm: Tm, len: nat, pc: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        g >= 3,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1_m1(g, od.len()), (g + 2) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1_m1(g, od.len()), (g + 2) as nat)
            == (g + 2) as nat,
{
    let e = entry5(pc);
    // ── copy_refresh_m1 j=0 copy (off 0–6). ──
    let i_dpeel  = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp  = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins   = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb    = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 1, 1, 2, Dir::R);
    let i_cpeel  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 0, 0, 3, Dir::L);
    let i_ctemp  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 1, 1, 3, Dir::L);
    let i_ct2g   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 0, 0, 4, Dir::L);
    let i_cgap   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 0, 0, 4, Dir::L);
    let i_cmark  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 1, 5, 5, Dir::R);
    let i_crf2g  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 5, 0, 0, 6, Dir::R);
    let i_crgap  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 0, 0, 6, Dir::R);
    let i_crg2t  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh_m1 terminate (home == q_home == e+7). ──
    let i_tpeel  = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 0, 0, 8, Dir::L);
    let i_ttemp  = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 1, 1, 8, Dir::L);
    let i_tt2g   = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 0, 0, 9, Dir::L);
    let i_tgap   = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 0, 0, 9, Dir::L);
    let i_ta2b   = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 5, 5, 10, Dir::L);
    let i_tturn  = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 0, 0, 15, Dir::R);
    let i_tmaster= (pc * 288 + 15 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 1, 1, 17, Dir::R);
    // ── copy_refresh_m1 unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 1, 1, 23, Dir::R);
    // ── block_loop (q_loop := q_urt == e+23), exit → qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1x_exit(tm, len, pc, s, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 30, 1, 0, 23, Dir::R);
    let i_one_r  = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 1, 1, 23, Dir::R);

    // ── invoke the verified M=1 power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block1_m1_tail_safe(tm, g, od, s,
        // states: off 0–6, then q_t=e+8 q_a=e+9 q_b=e+10 q_turn=e+15 q_turng=e+16 q_ret=e+17 q_home=e+7,
        //         q_ut=e+18..q_urt=e+23, block_loop e+24..e+30, qexit.
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 8, e + 9, e + 10, e + 15, e + 16, e + 17, e + 7,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, qexit,
        // copy_refresh_m1 quint indices
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b,
        i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
}

pub proof fn lemma_pbb1x_phase_any_tail_safe(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb1_fuel(big_m, g, od.len()), (g + big_m + 1) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb1_fuel(big_m, g, od.len()), (g + big_m + 1) as nat)
            == (g + big_m + 1) as nat,
{
    if big_m == 1 {
        lemma_pbb1x_m1_phase_tail_safe(tm, len, pc, g, od, s, qexit);
    } else {
        lemma_pbb1x_phase_tail_safe(tm, len, pc, big_m, g, od, s, qexit);
    }
}


// ─────────────────────────────────────────────────────────────────────────────
// v-side (α-tail) companions — mirror of the u-side phase tail_safe lemmas above,
// wrapping the v-side power_block_step lemmas. Surge constraint carried up.
// ─────────────────────────────────────────────────────────────────────────────

pub proof fn lemma_pbb1x_phase_tail_safe_v(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat, h: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        h >= od.len() + big_m + 1,
    ensures
        tail_safe_v(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()), h),
        tail_end_h_v(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1(big_m, g, od.len()), h)
            == h,
{
    let e = entry5(pc);
    // ── locate all 64 quintuples (cheap locate_pbb1x calls; the exit via locate_pbb1x_exit → qexit). ──
    // (A) copy_refresh j=0 deposit-first
    let i_dpeel0 = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp0 = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins0  = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb0   = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 1, 1, 2, Dir::R);
    let i_peel0  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 0, 0, 3, Dir::L);
    let i_temp0  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 1, 1, 3, Dir::L);
    let i_t2g0   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 0, 0, 4, Dir::L);
    let i_gap0   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 0, 0, 4, Dir::L);
    let i_mark0  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 1, 5, 5, Dir::R);
    let i_rf2g0  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 5, 0, 0, 6, Dir::R);
    let i_rgap0  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 0, 0, 6, Dir::R);
    let i_rg2t0  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 1, 1, 7, Dir::R);
    // (B) copy_refresh home-cycle
    let i_peel   = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 0, 0, 8, Dir::L);
    let i_temp   = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 1, 1, 8, Dir::L);
    let i_t2g    = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 0, 0, 9, Dir::L);
    let i_gap    = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 0, 0, 9, Dir::L);
    let i_a2b    = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 5, 5, 10, Dir::L);
    let i_fives  = (pc * 288 + 10 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 5, 5, 10, Dir::L);
    let i_mark   = (pc * 288 + 10 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 1, 5, 11, Dir::R);
    let i_rfives = (pc * 288 + 11 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 11, 5, 5, 11, Dir::R);
    let i_rf2g   = (pc * 288 + 11 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 11, 0, 0, 12, Dir::R);
    let i_rgap   = (pc * 288 + 12 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 12, 0, 0, 12, Dir::R);
    let i_rg2t   = (pc * 288 + 12 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 12, 1, 1, 13, Dir::R);
    let i_rtemp  = (pc * 288 + 13 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 13, 1, 1, 13, Dir::R);
    let i_dpeel  = (pc * 288 + 13 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 13, 0, 0, 14, Dir::L);
    let i_dtemp  = (pc * 288 + 14 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 14, 1, 1, 14, Dir::L);
    let i_dins   = (pc * 288 + 14 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 14, 0, 1, 7, Dir::R);
    let i_dwb    = (pc * 288 + 7 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 1, 1, 7, Dir::R);
    // (C) copy_refresh terminate walk-back
    let i_turn   = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 0, 0, 15, Dir::R);
    let i_master = (pc * 288 + 15 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 1, 1, 17, Dir::R);
    let i_trtemp = (pc * 288 + 17 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 1, 1, 17, Dir::R);
    // (D) copy_refresh unmark (home == q_ret == e+17)
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 5, 1, 20, Dir::L);
    let i_uurest = (pc * 288 + 20 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 1, 1, 23, Dir::R);
    let i_urtemp = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 1, 1, 23, Dir::R);
    // (E) block_loop — the exit slot targets the EXTERNAL qexit.
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1x_exit(tm, len, pc, s, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 30, 1, 0, 23, Dir::R);

    // ── invoke the verified power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block1_tail_safe_v(tm, big_m, g, od, s,
        // states (off 0..30, then the EXTERNAL exit qexit)
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 7, e + 8, e + 9, e + 10, e + 11, e + 12, e + 13, e + 14,
        e + 15, e + 16, e + 17,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, qexit,
        // copy_refresh quint indices
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, h);
}

pub proof fn lemma_pbb1x_m1_phase_tail_safe_v(tm: Tm, len: nat, pc: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat, h: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        g >= 3,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        h >= od.len() + 2,
    ensures
        tail_safe_v(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1_m1(g, od.len()), h),
        tail_end_h_v(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            power_block_fuel_b1_m1(g, od.len()), h)
            == h,
{
    let e = entry5(pc);
    // ── copy_refresh_m1 j=0 copy (off 0–6). ──
    let i_dpeel  = (pc * 288 + 0 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 0, 0, 0, 1, Dir::L);
    let i_dtemp  = (pc * 288 + 1 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 1, 1, 1, Dir::L);
    let i_dins   = (pc * 288 + 1 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 1, 0, 1, 2, Dir::R);
    let i_dwb    = (pc * 288 + 2 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 1, 1, 2, Dir::R);
    let i_cpeel  = (pc * 288 + 2 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 2, 0, 0, 3, Dir::L);
    let i_ctemp  = (pc * 288 + 3 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 1, 1, 3, Dir::L);
    let i_ct2g   = (pc * 288 + 3 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 3, 0, 0, 4, Dir::L);
    let i_cgap   = (pc * 288 + 4 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 0, 0, 4, Dir::L);
    let i_cmark  = (pc * 288 + 4 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 4, 1, 5, 5, Dir::R);
    let i_crf2g  = (pc * 288 + 5 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 5, 0, 0, 6, Dir::R);
    let i_crgap  = (pc * 288 + 6 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 0, 0, 6, Dir::R);
    let i_crg2t  = (pc * 288 + 6 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 6, 1, 1, 7, Dir::R);
    // ── copy_refresh_m1 terminate (home == q_home == e+7). ──
    let i_tpeel  = (pc * 288 + 7 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 7, 0, 0, 8, Dir::L);
    let i_ttemp  = (pc * 288 + 8 * 6 + 1) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 1, 1, 8, Dir::L);
    let i_tt2g   = (pc * 288 + 8 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 8, 0, 0, 9, Dir::L);
    let i_tgap   = (pc * 288 + 9 * 6 + 0) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 0, 0, 9, Dir::L);
    let i_ta2b   = (pc * 288 + 9 * 6 + 5) as int;  locate_pbb1x(tm, len, pc, s, qexit, 9, 5, 5, 10, Dir::L);
    let i_tturn  = (pc * 288 + 10 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 10, 0, 0, 15, Dir::R);
    let i_tmaster= (pc * 288 + 15 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 5, 5, 15, Dir::R);
    let i_tm2g   = (pc * 288 + 15 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 15, 0, 0, 16, Dir::R);
    let i_trgap  = (pc * 288 + 16 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 0, 0, 16, Dir::R);
    let i_tg2t   = (pc * 288 + 16 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 16, 1, 1, 17, Dir::R);
    // ── copy_refresh_m1 unmark (home == q_ret == e+17). ──
    let i_upeel  = (pc * 288 + 17 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 17, 0, 0, 18, Dir::L);
    let i_utemp  = (pc * 288 + 18 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 1, 1, 18, Dir::L);
    let i_ut2g   = (pc * 288 + 18 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 18, 0, 0, 19, Dir::L);
    let i_ugap   = (pc * 288 + 19 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 0, 0, 19, Dir::L);
    let i_uu1    = (pc * 288 + 19 * 6 + 5) as int; locate_pbb1x(tm, len, pc, s, qexit, 19, 5, 1, 20, Dir::L);
    let i_uturn  = (pc * 288 + 20 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 20, 0, 0, 21, Dir::R);
    let i_umaster= (pc * 288 + 21 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 1, 1, 21, Dir::R);
    let i_um2g   = (pc * 288 + 21 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 21, 0, 0, 22, Dir::R);
    let i_urgap  = (pc * 288 + 22 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 0, 0, 22, Dir::R);
    let i_ug2t   = (pc * 288 + 22 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 22, 1, 1, 23, Dir::R);
    // ── block_loop (q_loop := q_urt == e+23), exit → qexit. ──
    let i_peek   = (pc * 288 + 23 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 0, 0, 24, Dir::L);
    let i_cont   = (pc * 288 + 24 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 24, 1, 1, 25, Dir::R);
    let i_exit   = (pc * 288 + 24 * 6 + 0) as int; locate_pbb1x_exit(tm, len, pc, s, qexit);
    let i_pivot_r= (pc * 288 + 25 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 25, 0, 0, 26, Dir::R);
    let ir1      = (pc * 288 + 26 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 1, 1, 26, Dir::R);
    let ir2      = (pc * 288 + 26 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 2, 2, 26, Dir::R);
    let ir3      = (pc * 288 + 26 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 3, 3, 26, Dir::R);
    let ir4      = (pc * 288 + 26 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 4, 4, 26, Dir::R);
    let i_emit   = (pc * 288 + 26 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 26, 0, s, 27, Dir::R);
    let i_off_l  = (pc * 288 + 27 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 27, 0, 0, 28, Dir::L);
    let il1      = (pc * 288 + 28 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 1, 1, 28, Dir::L);
    let il2      = (pc * 288 + 28 * 6 + 2) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 2, 2, 28, Dir::L);
    let il3      = (pc * 288 + 28 * 6 + 3) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 3, 3, 28, Dir::L);
    let il4      = (pc * 288 + 28 * 6 + 4) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 4, 4, 28, Dir::L);
    let i_pivot  = (pc * 288 + 28 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 28, 0, 0, 29, Dir::L);
    let i_one_l  = (pc * 288 + 29 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 1, 1, 29, Dir::L);
    let i_erase  = (pc * 288 + 29 * 6 + 0) as int; locate_pbb1x(tm, len, pc, s, qexit, 29, 0, 0, 30, Dir::R);
    let i_disc   = (pc * 288 + 30 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 30, 1, 0, 23, Dir::R);
    let i_one_r  = (pc * 288 + 23 * 6 + 1) as int; locate_pbb1x(tm, len, pc, s, qexit, 23, 1, 1, 23, Dir::R);

    // ── invoke the verified M=1 power-block step (q_dh0 = e, q_exit = qexit external). ──
    lemma_power_block_step_block1_m1_tail_safe_v(tm, g, od, s,
        // states: off 0–6, then q_t=e+8 q_a=e+9 q_b=e+10 q_turn=e+15 q_turng=e+16 q_ret=e+17 q_home=e+7,
        //         q_ut=e+18..q_urt=e+23, block_loop e+24..e+30, qexit.
        e + 0, e + 1, e + 2, e + 3, e + 4, e + 5, e + 6,
        e + 8, e + 9, e + 10, e + 15, e + 16, e + 17, e + 7,
        e + 18, e + 19, e + 20, e + 21, e + 22, e + 23,
        e + 24, e + 25, e + 26, e + 27, e + 28, e + 29, e + 30, qexit,
        // copy_refresh_m1 quint indices
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b,
        i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t,
        // block_loop quint indices
        i_peek, i_cont, i_exit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r, h);
}

pub proof fn lemma_pbb1x_phase_any_tail_safe_v(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, s: nat, qexit: nat, h: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s, qexit, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        h >= od.len() + big_m + 1,
    ensures
        tail_safe_v(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb1_fuel(big_m, g, od.len()), h),
        tail_end_h_v(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            pb1_fuel(big_m, g, od.len()), h)
            == h,
{
    if big_m == 1 {
        lemma_pbb1x_m1_phase_tail_safe_v(tm, len, pc, g, od, s, qexit, h);
    } else {
        lemma_pbb1x_phase_tail_safe_v(tm, len, pc, big_m, g, od, s, qexit, h);
    }
}

} // verus!
