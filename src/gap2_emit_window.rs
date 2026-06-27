//! # GAP-2 G2-F Route (i) — emitter windows over the `assemble5` scaffold.
//!
//! Wires the verified emitter step-lemmas ([`crate::tm_block_iter`], [`crate::tm_power_block`]) onto the
//! concrete [`crate::tm_assemble5`] uniform-window scaffold (STRIDE=48, marker `5`). Each `fam_digits`
//! block becomes one window `[entry5(pc), entry5(pc)+48)`; its action table places that block's quintuples
//! at fixed offsets, and a phase lemma — the analog of [`crate::gap2_psc_rp::lemma_rp_phase`] — proves the
//! corresponding step about any well-formed `assemble5` machine carrying the window. These are the
//! per-block atoms the 16-block sequencer (`fam_digits = uinv_digits(b) ++ u_digits(a)`) chains by state
//! identification (N+10).
//!
//! ## This module — the SINGLETON window
//! `lemma_seret1_phase` lays the **singleton emit** ([`crate::tm_block_iter::lemma_surge_emit_return_block1`]):
//! from the home pivot it surges right over the output, writes one digit `s`, and returns home — output
//! `od ↦ od ++ [s]`, master `u` untouched. The singletons `[4]`,`[3]`,`[2]`,`[1]` appear 8× across
//! `fam_digits` (the inter-power-block separators). Four states map to offsets `0..3`:
//!   * `q_iter   = entry5(pc)+0` — move R off the pivot.
//!   * `q_surge  = entry5(pc)+1` — skip the output (`1..4`), emit `s` on the frontier blank.
//!   * `q_eret   = entry5(pc)+2` — move L back onto the emitted digit.
//!   * `q_home   = entry5(pc)+3` — walk L over the output to the home pivot (terminal).
//!
//! `docs/gap2-input-loader-plan.md` §N+11 (NEXT item 1). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, Quintuple, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_assemble5::{entry5, tm_mod5, lemma_tm_wf_n5, lemma_slot_index5, lemma_idx5_decomp};
use crate::tm_dstring::dpack;
use crate::tm_block_iter::{lemma_surge_emit_return_block1, lemma_surge_emit_return_block3};

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// The singleton-emit action table + generator (one window per block).
// ─────────────────────────────────────────────────────────────────────────────

/// The singleton-emit action table over a STRIDE=48 window: for slot `(off, sym)` returns `(write,
/// next_off, dir)` where `next_off` is the offset of the next state *within the same window* (the
/// absolute next state is `entry5(pc) + next_off`). Emit symbol `s` (`1 ≤ s ≤ 4`). See the module docs
/// for the four-state layout. Every unused `(off, sym)` is an inert self-loop (write the scanned symbol,
/// stay at the same state, move L) — present only so the manifest layout is total.
pub open spec fn seret1_act(off: nat, sym: nat, s: nat) -> (nat, nat, Dir) {
    if off == 0 {
        // q_iter: move R off the home pivot.
        if sym == 0 { (0, 1, Dir::R) }            // (q_iter, 0, 0, q_surge, R)
        else { (sym, 0, Dir::L) }
    } else if off == 1 {
        // q_surge: skip output digits 1..4 (R); on the frontier blank emit s and turn to q_eret.
        if 1 <= sym && sym <= 4 { (sym, 1, Dir::R) }   // (q_surge, s', s', q_surge, R)
        else if sym == 0 { (s, 2, Dir::R) }             // (q_surge, 0, s, q_eret, R)
        else { (sym, 1, Dir::L) }                       // sym == 5: inert
    } else if off == 2 {
        // q_eret: move L back onto the emitted digit.
        if sym == 0 { (0, 3, Dir::L) }            // (q_eret, 0, 0, q_home, L)
        else { (sym, 2, Dir::L) }
    } else if off == 3 {
        // q_home: walk L over output digits 1..4 to the home pivot (terminal on sym 0/5).
        if 1 <= sym && sym <= 4 { (sym, 3, Dir::L) }   // (q_home, s', s', q_home, L)
        else { (sym, 3, Dir::L) }                       // sym 0 (terminal) / 5: inert (stay)
    } else {
        (sym, off, Dir::L)                              // other offsets: inert self-loop
    }
}

/// The singleton-emit generator: the manifest-keyed quintuple for flat index `idx` — q-key
/// `entry5(pc)+off`, scanned `sym`, action from [`seret1_act`] (next state `entry5(pc)+next_off`, in the
/// same window). Every window emits `s`.
pub open spec fn seret1_gen(s: nat, idx: nat) -> Quintuple {
    let pc = idx / 288;
    let off = (idx % 288) / 6;
    let sym = (idx % 288) % 6;
    let a = seret1_act(off, sym, s);
    mk_quint(entry5(pc) + off, sym, a.0, entry5(pc) + a.1, a.2)
}

// ─────────────────────────────────────────────────────────────────────────────
// Boundedness of the action table (feeds lemma_tm_wf_n5).
// ─────────────────────────────────────────────────────────────────────────────

/// Every singleton-emit action writes a real symbol (`≤ 5`) and targets an in-window offset (`< 48`).
/// The per-quintuple boundedness hypothesis of [`lemma_tm_wf_n5`] (the absolute next state
/// `entry5(pc)+next_off < tm_mod5(len)` follows for `pc ≤ len`).
pub proof fn lemma_seret1_act_bounded(off: nat, sym: nat, s: nat)
    requires
        off < 48,
        sym <= 5,
        1 <= s <= 4,
    ensures
        seret1_act(off, sym, s).0 <= 5,
        seret1_act(off, sym, s).1 < 48,
{
    // every branch: write ∈ {0,1,2,3,4,5,s,sym} ≤ 5; next_off ∈ {0,1,2,3,off} < 48.
}

// ─────────────────────────────────────────────────────────────────────────────
// The reusable singleton-emit phase lemma (abstract over the full machine).
// ─────────────────────────────────────────────────────────────────────────────

/// **Singleton-emit phase (one window).** Any well-formed n=5 assemble5 machine whose window `pc` carries
/// the singleton action table (`tm.quints[i] == seret1_gen(s, i)` for `i` in window `pc`) emits one digit
/// `s`: from the home config `{u: big_u, v: dpack(od), a: 0, q: entry5(pc)}` (master `big_u` parked in
/// `u`, output `od` in `v`, head on the home pivot), after `2·|od| + 4` steps the head is back on the home
/// pivot with the output grown by `[s]` and `u` untouched:
/// `{u: big_u, v: dpack(od ++ [s]), a: 0, q: entry5(pc)+3}`.
///
/// The hypothesis matches the per-window slice a full-`psc_tm` dispatch generator delivers, so a singleton
/// is a drop-in for the eventual machine. Mirrors [`crate::gap2_psc_rp::lemma_rp_phase`].
pub proof fn lemma_seret1_phase(tm: Tm, len: nat, pc: nat, big_u: nat, od: Seq<nat>, s: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret1_gen(s, i as nat),
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            (2 * od.len() + 4) as nat)
            == (TmConfig { u: big_u, v: dpack(od + seq![s], tm.m), a: 0, q: entry5(pc) + 3 }),
{
    // The window pc occupies flat indices [pc·288, pc·288 + 288); all < tm.quints.len().
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    let base = (pc * 288) as int;

    let q_iter = entry5(pc);
    let q_surge = (entry5(pc) + 1) as nat;
    let q_eret = (entry5(pc) + 2) as nat;
    let q_home = (entry5(pc) + 3) as nat;

    // ── locate the singleton's 11 quintuples by slot, all in window pc. ──
    // q_iter: (pc, 0, 0).
    let i_pivot_r = (pc * 288 + 0 * 6 + 0) as int;
    // q_surge: (pc, 1, 1..4) and (pc, 1, 0).
    let ir1 = (pc * 288 + 1 * 6 + 1) as int;
    let ir2 = (pc * 288 + 1 * 6 + 2) as int;
    let ir3 = (pc * 288 + 1 * 6 + 3) as int;
    let ir4 = (pc * 288 + 1 * 6 + 4) as int;
    let i_emit = (pc * 288 + 1 * 6 + 0) as int;
    // q_eret: (pc, 2, 0).
    let i_off_l = (pc * 288 + 2 * 6 + 0) as int;
    // q_home: (pc, 3, 1..4).
    let il1 = (pc * 288 + 3 * 6 + 1) as int;
    let il2 = (pc * 288 + 3 * 6 + 2) as int;
    let il3 = (pc * 288 + 3 * 6 + 3) as int;
    let il4 = (pc * 288 + 3 * 6 + 4) as int;

    // ── each index lies in window pc, hence in range. ──
    assert(base <= i_pivot_r < base + 288);
    assert(base <= ir1 < base + 288);
    assert(base <= ir2 < base + 288);
    assert(base <= ir3 < base + 288);
    assert(base <= ir4 < base + 288);
    assert(base <= i_emit < base + 288);
    assert(base <= i_off_l < base + 288);
    assert(base <= il1 < base + 288);
    assert(base <= il2 < base + 288);
    assert(base <= il3 < base + 288);
    assert(base <= il4 < base + 288);

    // ── decode each slot back to (pc, off, sym), then read off seret1_gen = the gadget quintuple. ──
    assert(tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 0, 0);
        assert(tm.quints[i_pivot_r] == seret1_gen(s, i_pivot_r as nat));
    }
    assert(tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 1);
        assert(tm.quints[ir1] == seret1_gen(s, ir1 as nat));
    }
    assert(tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 2);
        assert(tm.quints[ir2] == seret1_gen(s, ir2 as nat));
    }
    assert(tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 3);
        assert(tm.quints[ir3] == seret1_gen(s, ir3 as nat));
    }
    assert(tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 4);
        assert(tm.quints[ir4] == seret1_gen(s, ir4 as nat));
    }
    assert(tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R)) by {
        lemma_slot_index5(pc, 1, 0);
        assert(tm.quints[i_emit] == seret1_gen(s, i_emit as nat));
    }
    assert(tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L)) by {
        lemma_slot_index5(pc, 2, 0);
        assert(tm.quints[i_off_l] == seret1_gen(s, i_off_l as nat));
    }
    assert(tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L)) by {
        lemma_slot_index5(pc, 3, 1);
        assert(tm.quints[il1] == seret1_gen(s, il1 as nat));
    }
    assert(tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L)) by {
        lemma_slot_index5(pc, 3, 2);
        assert(tm.quints[il2] == seret1_gen(s, il2 as nat));
    }
    assert(tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L)) by {
        lemma_slot_index5(pc, 3, 3);
        assert(tm.quints[il3] == seret1_gen(s, il3 as nat));
    }
    assert(tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L)) by {
        lemma_slot_index5(pc, 3, 4);
        assert(tm.quints[il4] == seret1_gen(s, il4 as nat));
    }

    // ── n ≥ 4 (n == 5); invoke the verified singleton step. ──
    lemma_surge_emit_return_block1(tm, big_u, od, s,
        q_iter, q_surge, q_eret, q_home,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4);
}

// ─────────────────────────────────────────────────────────────────────────────
// Concrete validation — a standalone singleton-emit machine over assemble5.
// ─────────────────────────────────────────────────────────────────────────────

/// A concrete singleton-emit TM with `len + 1` uniform windows (each emits `s`). Validates that
/// [`seret1_act`] composes with the assemble5 scaffold (non-vacuity for [`lemma_seret1_phase`]).
pub open spec fn seret1_tm(len: nat, s: nat) -> Tm {
    Tm { n: 5, m: tm_mod5(len), quints: Seq::new(288 * (len + 1), |idx: int| seret1_gen(s, idx as nat)) }
}

/// The concrete singleton machine is well-formed (discharges the [`lemma_tm_wf_n5`] hypotheses for
/// [`seret1_gen`]).
pub proof fn lemma_seret1_tm_wf(len: nat, s: nat)
    requires
        1 <= s <= 4,
    ensures
        tm_wf(seret1_tm(len, s)),
{
    let tm = seret1_tm(len, s);
    assert(tm.quints.len() == 288 * (len + 1));
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 288 * (len + 1) implies
        tm.quints[idx].q == entry5((idx as nat) / 288) + ((idx as nat) % 288) / 6
        && tm.quints[idx].a == ((idx as nat) % 288) % 6 by {
        assert(tm.quints[idx] == seret1_gen(s, idx as nat));
    }
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 288 * (len + 1) implies
        tm.quints[idx].a2 <= 5 && tm.quints[idx].q2 < tm.m by {
        assert(tm.quints[idx] == seret1_gen(s, idx as nat));
        lemma_idx5_decomp(idx as nat, len);   // pc ≤ len, off < 48, sym ≤ 5
        let pc = (idx as nat) / 288;
        let off = ((idx as nat) % 288) / 6;
        let sym = ((idx as nat) % 288) % 6;
        lemma_seret1_act_bounded(off, sym, s);   // write ≤ 5, next_off < 48
        // absolute next = entry5(pc) + next_off < tm_mod5(len) for pc ≤ len, next_off < 48.
        assert(entry5(pc) + seret1_act(off, sym, s).1 < tm.m) by(nonlinear_arith)
            requires entry5(pc) == 6 + 48 * pc, pc <= len, seret1_act(off, sym, s).1 < 48,
                tm.m == 54 + 48 * len;
    }
    lemma_tm_wf_n5(tm, len);
}

/// **Concrete singleton validation.** The standalone machine emits one digit `s` exactly as
/// [`lemma_seret1_phase`] promises — confirming the assemble5 ↔ emitter-step composition end-to-end.
pub proof fn lemma_seret1_emit(len: nat, pc: nat, big_u: nat, od: Seq<nat>, s: nat)
    requires
        pc <= len,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(seret1_tm(len, s),
            TmConfig { u: big_u, v: dpack(od, tm_mod5(len)), a: 0, q: entry5(pc) },
            (2 * od.len() + 4) as nat)
            == (TmConfig { u: big_u, v: dpack(od + seq![s], tm_mod5(len)), a: 0, q: entry5(pc) + 3 }),
{
    let tm = seret1_tm(len, s);
    lemma_seret1_tm_wf(len, s);
    assert(tm.m == tm_mod5(len));
    assert forall|i: int| pc * 288 <= i < pc * 288 + 288 implies #[trigger] tm.quints[i] == seret1_gen(s, i as nat) by {
        assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    }
    lemma_seret1_phase(tm, len, pc, big_u, od, s);
}

// ─────────────────────────────────────────────────────────────────────────────
// EXIT-PARAMETRIC singleton window — the 16-block SEQUENCER building block (§N+11).
//
// Unlike the power-block (whose `q_exit` is a pure label), the singleton's end-state `q_home` is a
// WALK-BACK state: it loops `(q_home, sym, sym, q_home, L)` for `sym ∈ 1..4` and the run terminates ON the
// pivot (reading 0) WITHOUT firing `(q_home, 0)`. KEY COINCIDENCE: that walk-back self-loop is
// BYTE-IDENTICAL to ANY next block's inert off-0 self-loop (both power-block `q_dh0` and singleton
// `q_iter` do `(sym, stay-at-off-0, L)` on reads 1..4). So setting `q_home := qexit = entry5(pc+1)` (the
// next block's start) makes the 4 walk-back quints COINCIDE with the next window's off-0 self-loops —
// zero-glue, uniform, same splice as the power-block. The walk-back quints live AT `qexit` (window pc+1),
// supplied to this phase lemma as the 4 `jl` hypotheses (discharged in the sequencer from the next window).
// For the FINAL block the target is `q_cmp`, which must be made walk-back-compatible (carry the same 4
// self-loops). (Danielle co-designed, port 8051.)
// ─────────────────────────────────────────────────────────────────────────────

/// The exit-parametric singleton-emit generator: identical to [`seret1_gen`] EXCEPT the q_eret landing slot
/// `(off 2, sym 0)` targets the EXTERNAL state `qexit` (the next block's off-0 state) rather than the
/// in-window `q_home = entry5(pc)+3`. The walk-back self-loops are NOT carried in window pc — they live at
/// `qexit` and are supplied to [`lemma_seret1x_phase`] as the 4 `jl` quints.
pub open spec fn seret1x_gen(s: nat, qexit: nat, idx: nat) -> Quintuple {
    let pc = idx / 288;
    let off = (idx % 288) / 6;
    let sym = (idx % 288) % 6;
    if off == 2 && sym == 0 {
        mk_quint(entry5(pc) + 2, 0, 0, qexit, Dir::L)      // q_eret → q_home := qexit (cross-window)
    } else {
        let a = seret1_act(off, sym, s);
        mk_quint(entry5(pc) + off, sym, a.0, entry5(pc) + a.1, a.2)
    }
}

/// **Exit-parametric singleton-emit phase (one window).** As [`lemma_seret1_phase`] but the return walk
/// lands on the EXTERNAL state `qexit` (the next block's off-0 state). The 7 surge/emit/turn quints live in
/// window `pc`; the 4 walk-back self-loops `(qexit, 1..4, qexit, L)` are supplied as `jl1..jl4` (the next
/// window's inert off-0 self-loops, which coincide). From `{u: big_u, v: dpack(od), a: 0, q: entry5(pc)}`
/// after `2·|od| + 4` steps: `{u: big_u, v: dpack(od ++ [s]), a: 0, q: qexit}`.
pub proof fn lemma_seret1x_phase(tm: Tm, len: nat, pc: nat, big_u: nat, od: Seq<nat>, s: nat,
    qexit: nat, jl1: int, jl2: int, jl3: int, jl4: int)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(s, qexit, i as nat),
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        // the 4 walk-back self-loops AT qexit (the next window's inert off-0 self-loops).
        0 <= jl1 < tm.quints.len(),
        0 <= jl2 < tm.quints.len(),
        0 <= jl3 < tm.quints.len(),
        0 <= jl4 < tm.quints.len(),
        tm.quints[jl1] == mk_quint(qexit, 1, 1, qexit, Dir::L),
        tm.quints[jl2] == mk_quint(qexit, 2, 2, qexit, Dir::L),
        tm.quints[jl3] == mk_quint(qexit, 3, 3, qexit, Dir::L),
        tm.quints[jl4] == mk_quint(qexit, 4, 4, qexit, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            (2 * od.len() + 4) as nat)
            == (TmConfig { u: big_u, v: dpack(od + seq![s], tm.m), a: 0, q: qexit }),
{
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    let base = (pc * 288) as int;

    let q_iter = entry5(pc);
    let q_surge = (entry5(pc) + 1) as nat;
    let q_eret = (entry5(pc) + 2) as nat;

    // ── locate the 7 window-pc quints (q_iter, q_surge, q_eret); off_l targets qexit. ──
    let i_pivot_r = (pc * 288 + 0 * 6 + 0) as int;
    let ir1 = (pc * 288 + 1 * 6 + 1) as int;
    let ir2 = (pc * 288 + 1 * 6 + 2) as int;
    let ir3 = (pc * 288 + 1 * 6 + 3) as int;
    let ir4 = (pc * 288 + 1 * 6 + 4) as int;
    let i_emit = (pc * 288 + 1 * 6 + 0) as int;
    let i_off_l = (pc * 288 + 2 * 6 + 0) as int;

    assert(base <= i_pivot_r < base + 288);
    assert(base <= ir1 < base + 288);
    assert(base <= ir2 < base + 288);
    assert(base <= ir3 < base + 288);
    assert(base <= ir4 < base + 288);
    assert(base <= i_emit < base + 288);
    assert(base <= i_off_l < base + 288);

    assert(tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 0, 0);
        assert(tm.quints[i_pivot_r] == seret1x_gen(s, qexit, i_pivot_r as nat));
    }
    assert(tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 1);
        assert(tm.quints[ir1] == seret1x_gen(s, qexit, ir1 as nat));
    }
    assert(tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 2);
        assert(tm.quints[ir2] == seret1x_gen(s, qexit, ir2 as nat));
    }
    assert(tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 3);
        assert(tm.quints[ir3] == seret1x_gen(s, qexit, ir3 as nat));
    }
    assert(tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 4);
        assert(tm.quints[ir4] == seret1x_gen(s, qexit, ir4 as nat));
    }
    assert(tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R)) by {
        lemma_slot_index5(pc, 1, 0);
        assert(tm.quints[i_emit] == seret1x_gen(s, qexit, i_emit as nat));
    }
    assert(tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, qexit, Dir::L)) by {
        lemma_slot_index5(pc, 2, 0);
        assert(tm.quints[i_off_l] == seret1x_gen(s, qexit, i_off_l as nat));
    }

    // ── invoke the verified singleton step with q_home = qexit, walk-back quints jl1..jl4. ──
    lemma_surge_emit_return_block1(tm, big_u, od, s,
        q_iter, q_surge, q_eret, qexit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, jl1, jl2, jl3, jl4);
}

// ─────────────────────────────────────────────────────────────────────────────
// EXIT-PARAMETRIC TRIPLE-singleton window — the `[4,1,2]` / `[4,3,2]` separators (§N+11).
//
// Same splice as the single singleton ([`lemma_seret1x_phase`]) but emitting a 3-symbol run at the
// frontier ([`crate::tm_block_iter::lemma_surge_emit_return_block3`]) via the two extra states q_e1, q_e2.
// The return walk lands on the external `qexit`; the 4 walk-back self-loops are supplied as `jl1..jl4`.
// ─────────────────────────────────────────────────────────────────────────────

/// The triple-singleton-emit action table over a STRIDE=48 window: 6 states q_iter(0)/q_surge(1)/q_e1(2)/
/// q_e2(3)/q_eret(4)/q_home(5), emitting `(s0,s1,s2)` at the frontier. Every unused slot is an inert
/// self-loop.
pub open spec fn seret3_act(off: nat, sym: nat, s0: nat, s1: nat, s2: nat) -> (nat, nat, Dir) {
    if off == 0 {            // q_iter: move R off the home pivot.
        if sym == 0 { (0, 1, Dir::R) } else { (sym, 0, Dir::L) }
    } else if off == 1 {     // q_surge: skip output 1..4 (R); on frontier 0 emit s0 → q_e1.
        if 1 <= sym && sym <= 4 { (sym, 1, Dir::R) }
        else if sym == 0 { (s0, 2, Dir::R) }
        else { (sym, 1, Dir::L) }
    } else if off == 2 {     // q_e1: emit s1 → q_e2.
        if sym == 0 { (s1, 3, Dir::R) } else { (sym, 2, Dir::L) }
    } else if off == 3 {     // q_e2: emit s2 → q_eret.
        if sym == 0 { (s2, 4, Dir::R) } else { (sym, 3, Dir::L) }
    } else if off == 4 {     // q_eret: move L back onto the last emitted digit → q_home.
        if sym == 0 { (0, 5, Dir::L) } else { (sym, 4, Dir::L) }
    } else if off == 5 {     // q_home: walk L over output 1..4 to the home pivot (terminal on 0).
        (sym, 5, Dir::L)
    } else {
        (sym, off, Dir::L)
    }
}

/// The exit-parametric triple-singleton generator: identical to a [`seret3_act`]-keyed window EXCEPT the
/// q_eret landing slot `(off 4, sym 0)` targets the EXTERNAL `qexit` (the next block's off-0 state). The
/// walk-back self-loops live at `qexit` (supplied to the phase lemma as `jl1..jl4`).
pub open spec fn seret3x_gen(s0: nat, s1: nat, s2: nat, qexit: nat, idx: nat) -> Quintuple {
    let pc = idx / 288;
    let off = (idx % 288) / 6;
    let sym = (idx % 288) % 6;
    if off == 4 && sym == 0 {
        mk_quint(entry5(pc) + 4, 0, 0, qexit, Dir::L)      // q_eret → q_home := qexit (cross-window)
    } else {
        let a = seret3_act(off, sym, s0, s1, s2);
        mk_quint(entry5(pc) + off, sym, a.0, entry5(pc) + a.1, a.2)
    }
}

/// **Exit-parametric triple-singleton-emit phase (one window).** As [`lemma_seret1x_phase`] but emitting
/// `[s0,s1,s2]`. From `{u: big_u, v: dpack(od), a: 0, q: entry5(pc)}` after `2·|od| + 8` steps:
/// `{u: big_u, v: dpack(od ++ [s0,s1,s2]), a: 0, q: qexit}`. The 4 walk-back self-loops `(qexit, 1..4,
/// qexit, L)` are `jl1..jl4` (the next window's inert off-0 self-loops).
pub proof fn lemma_seret3x_phase(tm: Tm, len: nat, pc: nat, big_u: nat, od: Seq<nat>,
    s0: nat, s1: nat, s2: nat, qexit: nat, jl1: int, jl2: int, jl3: int, jl4: int)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret3x_gen(s0, s1, s2, qexit, i as nat),
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= jl1 < tm.quints.len(),
        0 <= jl2 < tm.quints.len(),
        0 <= jl3 < tm.quints.len(),
        0 <= jl4 < tm.quints.len(),
        tm.quints[jl1] == mk_quint(qexit, 1, 1, qexit, Dir::L),
        tm.quints[jl2] == mk_quint(qexit, 2, 2, qexit, Dir::L),
        tm.quints[jl3] == mk_quint(qexit, 3, 3, qexit, Dir::L),
        tm.quints[jl4] == mk_quint(qexit, 4, 4, qexit, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            (2 * od.len() + 8) as nat)
            == (TmConfig { u: big_u, v: dpack(od + seq![s0, s1, s2], tm.m), a: 0, q: qexit }),
{
    assert(pc * 288 + 288 <= 288 * (len + 1)) by(nonlinear_arith) requires pc <= len;
    let base = (pc * 288) as int;

    let q_iter = entry5(pc);
    let q_surge = (entry5(pc) + 1) as nat;
    let q_e1 = (entry5(pc) + 2) as nat;
    let q_e2 = (entry5(pc) + 3) as nat;
    let q_eret = (entry5(pc) + 4) as nat;

    let i_pivot_r = (pc * 288 + 0 * 6 + 0) as int;
    let ir1 = (pc * 288 + 1 * 6 + 1) as int;
    let ir2 = (pc * 288 + 1 * 6 + 2) as int;
    let ir3 = (pc * 288 + 1 * 6 + 3) as int;
    let ir4 = (pc * 288 + 1 * 6 + 4) as int;
    let i_e0 = (pc * 288 + 1 * 6 + 0) as int;
    let i_e1 = (pc * 288 + 2 * 6 + 0) as int;
    let i_e2 = (pc * 288 + 3 * 6 + 0) as int;
    let i_off_l = (pc * 288 + 4 * 6 + 0) as int;

    assert(base <= i_pivot_r < base + 288);
    assert(base <= ir1 < base + 288);
    assert(base <= ir2 < base + 288);
    assert(base <= ir3 < base + 288);
    assert(base <= ir4 < base + 288);
    assert(base <= i_e0 < base + 288);
    assert(base <= i_e1 < base + 288);
    assert(base <= i_e2 < base + 288);
    assert(base <= i_off_l < base + 288);

    assert(tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 0, 0);
        assert(tm.quints[i_pivot_r] == seret3x_gen(s0, s1, s2, qexit, i_pivot_r as nat));
    }
    assert(tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 1);
        assert(tm.quints[ir1] == seret3x_gen(s0, s1, s2, qexit, ir1 as nat));
    }
    assert(tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 2);
        assert(tm.quints[ir2] == seret3x_gen(s0, s1, s2, qexit, ir2 as nat));
    }
    assert(tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 3);
        assert(tm.quints[ir3] == seret3x_gen(s0, s1, s2, qexit, ir3 as nat));
    }
    assert(tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R)) by {
        lemma_slot_index5(pc, 1, 4);
        assert(tm.quints[ir4] == seret3x_gen(s0, s1, s2, qexit, ir4 as nat));
    }
    assert(tm.quints[i_e0] == mk_quint(q_surge, 0, s0, q_e1, Dir::R)) by {
        lemma_slot_index5(pc, 1, 0);
        assert(tm.quints[i_e0] == seret3x_gen(s0, s1, s2, qexit, i_e0 as nat));
    }
    assert(tm.quints[i_e1] == mk_quint(q_e1, 0, s1, q_e2, Dir::R)) by {
        lemma_slot_index5(pc, 2, 0);
        assert(tm.quints[i_e1] == seret3x_gen(s0, s1, s2, qexit, i_e1 as nat));
    }
    assert(tm.quints[i_e2] == mk_quint(q_e2, 0, s2, q_eret, Dir::R)) by {
        lemma_slot_index5(pc, 3, 0);
        assert(tm.quints[i_e2] == seret3x_gen(s0, s1, s2, qexit, i_e2 as nat));
    }
    assert(tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, qexit, Dir::L)) by {
        lemma_slot_index5(pc, 4, 0);
        assert(tm.quints[i_off_l] == seret3x_gen(s0, s1, s2, qexit, i_off_l as nat));
    }

    // ── invoke the verified triple-singleton step with q_home = qexit, walk-back quints jl1..jl4. ──
    lemma_surge_emit_return_block3(tm, big_u, od, s0, s1, s2,
        q_iter, q_surge, q_e1, q_e2, q_eret, qexit,
        i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, jl1, jl2, jl3, jl4);
}

} // verus!
