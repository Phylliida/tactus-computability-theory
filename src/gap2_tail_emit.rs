//! # GAP-2 G2-F — tail-safety of the emit-loop (`block_loop`/`power_block`) digit walks
//!
//! The power-block emit loop (`tm_block_iter`/`tm_block_loop`) shuttles the head over the OUTPUT digits
//! (`1..4`) to append a block — RIGHT to the frontier (`dwalk_right`/surge), emit, LEFT back home
//! (`dwalk_left_prefix`/return). These walks move AWAY from the high tail (the rightward surge raises the
//! offset; the leftward return lowers it back), so they are never tight — but `tail_safe` still has to be
//! threaded step-by-step. This module discharges the two digit-walk primitives; the higher emit gadgets
//! (surge/return/block_iter/block_loop/power_block) chain them in [`crate::gap2_tail_emit2`] (forthcoming).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, tm_step, apply_quint, quint_matches};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{dpack, dpile, pow_nat, lemma_dpack_pop, lemma_pow_nat_unfold};
use crate::tm_dwalk_prefix::{drev, lemma_drev_len, lemma_drev_digit_bound, lemma_dpile_is_dpack_drev,
    lemma_dpile_concat};
use crate::tm_block_iter::{lemma_surge, lemma_return_walk, lemma_surge_emit_return_block1,
    lemma_block_iter_block1};
use crate::tm_dec_master::lemma_dec_temp;
use crate::tm_block_loop::{loop_fuel_b1, lemma_guard_continue, lemma_guard_exit,
    lemma_block_loop_block1};
use crate::tm_block_loop::{lemma_dec_u_step, lemma_dec_u_zero};
use crate::tm_shuttle::lemma_emit_block1_frontier;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_dec_master::{dec_u, lemma_walk_left_prefix, lemma_walk_back_prefix};
use crate::tm_walk::{pile_ones, lemma_pile_ones_div_mod};
use crate::tm_emit::pile_sym;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_tail_unfold, lemma_step_tail_safe,
    lemma_tail_chain};
use crate::gap2_tail_walks::{lemma_run_walk_left_tail_safe, lemma_run_walk_right_tail_safe};
use crate::gap2_tail_phase1::lemma_pile_ones_eq_pile_sym;

verus! {

/// **`dwalk_right` is tail-safe** for its `blk.len()` R-moves over the output digits — unconditional (R
/// never pops the tail); offset RISES by `blk.len()`. Mirror of [`crate::tm_dwalk::lemma_dwalk_right`]
/// (the `i_s` digit-dispatch picks the firing quint each step).
pub proof fn lemma_dwalk_right_tail_safe(
    tm: Tm, c: TmConfig, q_back: nat, blk: Seq<nat>,
    i1: int, i2: int, i3: int, i4: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        c.a == blk[0],
        c.v == dpack(blk.drop_first(), tm.m),
        c.q == q_back,
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
    ensures
        tail_safe(tm, c, blk.len(), h),
        tail_end_h(tm, c, blk.len(), h) == (h + blk.len()) as nat,
    decreases blk.len(),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let s = blk[0];
    assert(1 <= s <= 4);
    let i_s = if s == 1 { i1 } else if s == 2 { i2 } else if s == 3 { i3 } else { i4 };
    assert(tm.quints[i_s] == mk_quint(q_back, s, s, q_back, Dir::R));
    assert(quint_matches(tm.quints[i_s], c));
    let c_next = apply_quint(tm.quints[i_s], c, m);
    lemma_tail_unfold(tm, c, blk.len(), h, i_s);   // R: unfold to c_next at offset h+1
    assert(c_next.u == c.u * m + s);
    assert(c_next.v == c.v / m);
    assert(c_next.a == c.v % m);
    assert(c_next.q == q_back);
    let rest = blk.drop_first();
    if rest.len() == 0 {
        assert(blk.len() == 1);
        // tail_safe(c_next, 0, h+1) == true; tail_end_h(c_next, 0, h+1) == h+1 == h+blk.len().
    } else {
        assert(rest[0] == blk[1]);
        assert(1 <= rest[0] <= 4);
        lemma_dpack_pop(rest, m);
        assert(c_next.a == rest[0]);
        assert(c_next.v == dpack(rest.drop_first(), m));
        assert forall|k: int| 0 <= k < rest.len() implies 1 <= #[trigger] rest[k] <= 4 by {
            assert(rest[k] == blk[k + 1]);
        }
        lemma_dwalk_right_tail_safe(tm, c_next, q_back, rest, i1, i2, i3, i4, (h + 1) as nat);
        assert(((h + 1) + rest.len()) as nat == (h + blk.len()) as nat);
    }
}

/// **`dwalk_left_prefix` is tail-safe** for its `blk.len()` L-moves over the output digits with a
/// preserved high tail `w`, when the entry offset `h ≥ blk.len()`; offset DROPS by `blk.len()`. Mirror of
/// [`crate::tm_dwalk_prefix::lemma_dwalk_left_prefix`]. The return-walk's home arm; never tight on the
/// emit path (`h = H_0 + (frontier reach)` is far above `blk.len()`).
pub proof fn lemma_dwalk_left_prefix_tail_safe(
    tm: Tm, c: TmConfig, q_walk: nat, blk: Seq<nat>, w: nat,
    i1: int, i2: int, i3: int, i4: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        w % tm.m == 0,
        c.a == blk[0],
        c.u == dpack(blk.drop_first(), tm.m) + pow_nat(tm.m, (blk.len() - 1) as nat) * w,
        c.q == q_walk,
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[i3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[i4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
        h >= blk.len(),
    ensures
        tail_safe(tm, c, blk.len(), h),
        tail_end_h(tm, c, blk.len(), h) == (h - blk.len()) as nat,
    decreases blk.len(),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let s = blk[0];
    assert(1 <= s <= 4);
    let i_s = if s == 1 { i1 } else if s == 2 { i2 } else if s == 3 { i3 } else { i4 };
    assert(tm.quints[i_s] == mk_quint(q_walk, s, s, q_walk, Dir::L));
    assert(quint_matches(tm.quints[i_s], c));
    let c_next = apply_quint(tm.quints[i_s], c, m);
    lemma_tail_unfold(tm, c, blk.len(), h, i_s);   // L: needs h >= 1, unfold to c_next at h-1
    assert(c_next.u == c.u / m);
    assert(c_next.a == c.u % m);
    assert(c_next.q == q_walk);
    let rest = blk.drop_first();
    if rest.len() == 0 {
        assert(blk.len() == 1);
        // tail_safe(c_next, 0, h-1) == true; end h-1 == h-blk.len().
    } else {
        assert(rest[0] == blk[1]);
        assert(1 <= rest[0] <= 4);
        assert((blk.len() - 1) as nat == rest.len());
        let x = dpack(rest.drop_first(), m) + pow_nat(m, (rest.len() - 1) as nat) * w;
        assert(dpack(rest, m) == rest[0] + m * dpack(rest.drop_first(), m));
        lemma_pow_nat_unfold(m, rest.len());
        assert(c.u == x * m + rest[0]) by(nonlinear_arith)
            requires
                c.u == dpack(rest, m) + pow_nat(m, rest.len()) * w,
                dpack(rest, m) == rest[0] + m * dpack(rest.drop_first(), m),
                pow_nat(m, rest.len()) == m * pow_nat(m, (rest.len() - 1) as nat),
                x == dpack(rest.drop_first(), m) + pow_nat(m, (rest.len() - 1) as nat) * w;
        lemma_div_mod_step(x, m, rest[0]);
        assert(c_next.u == x);
        assert(c_next.a == rest[0]);
        assert forall|k: int| 0 <= k < rest.len() implies 1 <= #[trigger] rest[k] <= 4 by {
            assert(rest[k] == blk[k + 1]);
        }
        lemma_dwalk_left_prefix_tail_safe(tm, c_next, q_walk, rest, w, i1, i2, i3, i4, (h - 1) as nat);
        assert(((h - 1) - rest.len()) as nat == (h - blk.len()) as nat);
    }
}

/// **`surge` is tail-safe** for its `od.len() + 1` R-moves (move-R off the pivot, then `dwalk_right` over
/// the output) — unconditional; offset RISES by `od.len() + 1`. Mirror of
/// [`crate::tm_block_iter::lemma_surge`].
pub proof fn lemma_surge_tail_safe(
    tm: Tm, big_u: nat, od: Seq<nat>, q_iter: nat, q_surge: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter }, (od.len() + 1) as nat, h),
        tail_end_h(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter }, (od.len() + 1) as nat,
            h) == (h + od.len() + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };
    assert(quint_matches(tm.quints[i_pivot_r], c0));
    lemma_tm_step_picks(tm, c0, i_pivot_r);
    let c1 = apply_quint(tm.quints[i_pivot_r], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == big_u * m && c1.q == q_surge);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    lemma_step_tail_safe(tm, c0, i_pivot_r, h);   // R, end h+1
    if od.len() == 0 {
        assert((od.len() + 1) as nat == 1);
        assert((h + 1) as nat == (h + od.len() + 1) as nat);
    } else {
        assert(od[0] <= 4 && od[0] < m);
        lemma_dpack_pop(od, m);
        assert(c1.v == dpack(od.drop_first(), m));
        assert(c1.a == od[0]);
        lemma_dwalk_right_tail_safe(tm, c1, q_surge, od, ir1, ir2, ir3, ir4, (h + 1) as nat);
        assert(((h + 1) + od.len()) as nat == (h + od.len() + 1) as nat);
        lemma_tail_chain(tm, c0, 1, od.len(), h, (h + 1) as nat, (h + od.len() + 1) as nat);
    }
}

/// **`return_walk` is tail-safe** for its `combined.len() + 1` L-moves (move-L off the frontier, then
/// `dwalk_left_prefix` home over the output) when the entry offset `h ≥ combined.len() + 1`; offset DROPS
/// by `combined.len() + 1`. Mirror of [`crate::tm_block_iter::lemma_return_walk`] (the `drev` reversal
/// bridge derives the post-`off_l` config). Never tight on the emit path (the surge raised `h` first).
pub proof fn lemma_return_walk_tail_safe(
    tm: Tm, big_u: nat, combined: Seq<nat>, q_eret: nat, q_home: nat,
    i_off_l: int, il1: int, il2: int, il3: int, il4: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        combined.len() >= 1,
        forall|k: int| 0 <= k < combined.len() ==> 1 <= #[trigger] combined[k] <= 4,
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        h >= combined.len() + 1,
    ensures
        tail_safe(tm, TmConfig { u: dpile(big_u * tm.m, combined, tm.m), v: 0, a: 0, q: q_eret },
            (combined.len() + 1) as nat, h),
        tail_end_h(tm, TmConfig { u: dpile(big_u * tm.m, combined, tm.m), v: 0, a: 0, q: q_eret },
            (combined.len() + 1) as nat, h) == (h - combined.len() - 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let n = combined.len();
    let c3 = TmConfig { u: dpile(big_u * m, combined, m), v: 0, a: 0, q: q_eret };
    assert(quint_matches(tm.quints[i_off_l], c3));
    lemma_tm_step_picks(tm, c3, i_off_l);
    let c4 = apply_quint(tm.quints[i_off_l], c3, m);
    assert(tm_step(tm, c3) == Some(c4));
    assert(c4.v == 0 && c4.q == q_home);
    assert(tm_run(tm, c4, 0) == c4);
    assert(tm_run(tm, c3, 1) == c4);
    lemma_step_tail_safe(tm, c3, i_off_l, h);   // L, needs h>=1, end h-1

    // ── derive c4.u / c4.a via the drev reversal bridge (mirror of lemma_return_walk). ──
    lemma_dpile_is_dpack_drev(big_u * m, combined, m);
    let dr = drev(combined);
    lemma_drev_len(combined);
    lemma_drev_digit_bound(combined, 4);
    assert(dr.len() == n);
    assert(dr.len() >= 1 && dr[0] <= 4 && dr[0] < m);
    assert(dpack(dr, m) == dr[0] + m * dpack(dr.drop_first(), m));
    assert((big_u * m) * pow_nat(m, n) == m * (big_u * pow_nat(m, n))) by(nonlinear_arith);
    let qd = big_u * pow_nat(m, n) + dpack(dr.drop_first(), m);
    assert(c3.u == qd * m + dr[0]) by(nonlinear_arith)
        requires
            c3.u == (big_u * m) * pow_nat(m, n) + dpack(dr, m),
            dpack(dr, m) == dr[0] + m * dpack(dr.drop_first(), m),
            (big_u * m) * pow_nat(m, n) == m * (big_u * pow_nat(m, n)),
            qd == big_u * pow_nat(m, n) + dpack(dr.drop_first(), m);
    lemma_div_mod_step(qd, m, dr[0]);
    assert(c4.u == qd);
    assert(c4.a == dr[0]);
    lemma_pow_nat_unfold(m, n);
    assert(big_u * pow_nat(m, n) == pow_nat(m, (n - 1) as nat) * (m * big_u)) by(nonlinear_arith)
        requires pow_nat(m, n) == m * pow_nat(m, (n - 1) as nat);
    assert((n - 1) as nat == (dr.len() - 1) as nat);
    assert(c4.u == dpack(dr.drop_first(), m) + pow_nat(m, (dr.len() - 1) as nat) * (m * big_u));
    assert(m * big_u == big_u * m + 0) by(nonlinear_arith);
    lemma_div_mod_step(big_u, m, 0);
    assert((m * big_u) % m == 0);

    // ── dwalk_left_prefix home over dr at offset h-1 (needs h-1 >= |dr| == n). ──
    lemma_dwalk_left_prefix_tail_safe(tm, c4, q_home, dr, (m * big_u) as nat, il1, il2, il3, il4,
        (h - 1) as nat);
    assert(((h - 1) - dr.len()) as nat == (h - combined.len() - 1) as nat);
    lemma_tail_chain(tm, c3, 1, dr.len(), h, (h - 1) as nat, (h - combined.len() - 1) as nat);
    assert((1 + dr.len()) as nat == (combined.len() + 1) as nat);
}

/// **`surge_emit_return_block1` is tail-safe** for its `2·od.len() + 4` steps, net-disp-0 (offset returns
/// to `h`) for ANY entry offset `h` — the surge raises the offset BEFORE the return lowers it, so the
/// return is never tight. Mirror of [`crate::tm_block_iter::lemma_surge_emit_return_block1`]: surge ∘ emit
/// (1 R-step) ∘ return.
pub proof fn lemma_surge_emit_return_block1_tail_safe(
    tm: Tm, big_u: nat, od: Seq<nat>, s: nat,
    q_iter: nat, q_surge: nat, q_eret: nat, q_home: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_emit < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
    ensures
        tail_safe(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter },
            (2 * od.len() + 4) as nat, h),
        tail_end_h(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter },
            (2 * od.len() + 4) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };

    // ── surge: offset h → h+|od|+1. ──
    lemma_surge(tm, big_u, od, q_iter, q_surge, i_pivot_r, ir1, ir2, ir3, ir4);
    let c2 = TmConfig { u: dpile(big_u * m, od, m), v: 0, a: 0, q: q_surge };
    assert(tm_run(tm, c0, (od.len() + 1) as nat) == c2);
    lemma_surge_tail_safe(tm, big_u, od, q_iter, q_surge, i_pivot_r, ir1, ir2, ir3, ir4, h);

    // ── emit s (1 R-step): offset h+|od|+1 → h+|od|+2. ──
    lemma_emit_block1_frontier(tm, c2, q_surge, s, q_eret, i_emit);
    let combined = od + seq![s];
    let c3 = TmConfig { u: dpile(c2.u, seq![s], m), v: 0, a: 0, q: q_eret };
    assert(tm_run(tm, c2, 1) == c3);
    lemma_dpile_concat(big_u * m, od, seq![s], m);
    assert(c3.u == dpile(big_u * m, combined, m));
    assert(quint_matches(tm.quints[i_emit], c2));
    lemma_step_tail_safe(tm, c2, i_emit, (h + od.len() + 1) as nat);   // R, end h+|od|+2
    lemma_tm_run_split(tm, c0, (od.len() + 1) as nat, 1);
    assert((od.len() + 1 + 1) as nat == (od.len() + 2) as nat);
    assert(tm_run(tm, c0, (od.len() + 2) as nat) == c3);
    assert(((h + od.len() + 1) + 1) as nat == (h + od.len() + 2) as nat);
    lemma_tail_chain(tm, c0, (od.len() + 1) as nat, 1, h, (h + od.len() + 1) as nat,
        (h + od.len() + 2) as nat);

    // ── return: offset h+|od|+2 → h. ──
    assert(combined.len() == od.len() + 1);
    assert forall|k: int| 0 <= k < combined.len() implies 1 <= #[trigger] combined[k] <= 4 by {
        if k < od.len() { assert(combined[k] == od[k]); } else { assert(combined[k] == s); }
    }
    lemma_return_walk(tm, big_u, combined, q_eret, q_home, i_off_l, il1, il2, il3, il4);
    let c5 = TmConfig { u: big_u, v: dpack(combined, m), a: 0, q: q_home };
    assert(tm_run(tm, c3, (combined.len() + 1) as nat) == c5);
    // return entry offset h+|od|+2 >= |combined|+1 == |od|+2 (h >= 0).
    lemma_return_walk_tail_safe(tm, big_u, combined, q_eret, q_home, i_off_l, il1, il2, il3, il4,
        (h + od.len() + 2) as nat);
    assert(((h + od.len() + 2) - combined.len() - 1) as nat == h);
    lemma_tm_run_split(tm, c0, (od.len() + 2) as nat, (combined.len() + 1) as nat);
    assert((od.len() + 2 + (combined.len() + 1)) as nat == (2 * od.len() + 4) as nat);
    lemma_tail_chain(tm, c0, (od.len() + 2) as nat, (combined.len() + 1) as nat, h,
        (h + od.len() + 2) as nat, h);
}

/// **`dec_temp` is tail-safe** for its `2·temp + 2` steps when the tail enters at offset `h ≥ temp + 1`,
/// returning to `h` (net-disp-0). Mirror of [`crate::tm_dec_master::lemma_dec_temp`]: peel(L) ·
/// walk-left(L,temp) · erase(R) · discard(R) · walk-back(R,temp−1). The leftward reach is over the temp
/// counter (toward the master), deepest offset `h − 1 − temp ≥ 0`; never tight on the emit path
/// (`h = H_0 = g+M+1`, `temp ≤ M` ⟹ deepest `≥ g`). Reuses the s=1 general walk companions.
pub proof fn lemma_dec_temp_tail_safe(
    tm: Tm, temp: nat, w: nat, output_val: nat,
    q_home: nat, q_walk: nat, q_disc: nat, q_back: nat,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        temp >= 1,
        w % tm.m == 0,
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_walk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_walk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        h >= temp + 1,
    ensures
        tail_safe(tm, TmConfig { u: dec_u(temp, w, tm.m), v: output_val, a: 0, q: q_home },
            (2 * temp + 2) as nat, h),
        tail_end_h(tm, TmConfig { u: dec_u(temp, w, tm.m), v: output_val, a: 0, q: q_home },
            (2 * temp + 2) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = TmConfig { u: dec_u(temp, w, m), v: output_val, a: 0, q: q_home };
    let v1 = output_val * m;
    lemma_div_mod_step(output_val, m, 0);
    assert(output_val * m + 0 == v1);
    lemma_fundamental_div_mod(w as int, m as int);
    assert(w == m * (w / m)) by { assert(w % m == 0); }
    assert(m * (w / m) == (w / m) * m) by(nonlinear_arith);

    // ── S1: peel the pivot (L). offset h → h-1. ──
    let ux = repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * w;
    assert(repunit_m(temp, m) == m * repunit_m((temp - 1) as nat, m) + 1) by {
        crate::tm_two_counter::lemma_repunit_step((temp - 1) as nat, m);
        assert(((temp - 1) + 1) as nat == temp);
    }
    lemma_pow_nat_unfold(m, temp);
    assert(dec_u(temp, w, m) == ux * m + 1) by(nonlinear_arith)
        requires
            dec_u(temp, w, m) == repunit_m(temp, m) + pow_nat(m, temp) * w,
            repunit_m(temp, m) == m * repunit_m((temp - 1) as nat, m) + 1,
            pow_nat(m, temp) == m * pow_nat(m, (temp - 1) as nat),
            ux == repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * w;
    lemma_div_mod_step(ux, m, 1);
    lemma_tm_step_picks(tm, c0, i_pivot);
    let c_peel = apply_quint(tm.quints[i_pivot], c0, m);
    assert(tm_step(tm, c0) == Some(c_peel));
    assert(c_peel.u == ux && c_peel.v == v1 && c_peel.a == 1 && c_peel.q == q_walk);
    assert(tm_run(tm, c_peel, 0) == c_peel);
    assert(tm_run(tm, c0, 1) == c_peel);
    assert(quint_matches(tm.quints[i_pivot], c0));
    lemma_step_tail_safe(tm, c0, i_pivot, h);   // L, end h-1

    // ── S2: walk-left over temp (temp steps), q_walk. offset h-1 → h-1-temp. ──
    lemma_walk_left_prefix(tm, c_peel, q_walk, (temp - 1) as nat, w, i_one_l);
    let c_sep = TmConfig { u: w / m, v: pile_ones(v1, temp, m), a: w % m, q: q_walk };
    assert(((temp - 1) + 1) as nat == temp);
    assert(tm_run(tm, c_peel, temp) == c_sep);
    lemma_tm_run_split(tm, c0, 1, temp);
    assert(tm_run(tm, c0, (1 + temp) as nat) == c_sep);
    assert(c_peel.u == 1 * repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * w)
        by(nonlinear_arith)
        requires c_peel.u == ux,
            ux == repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * w;
    lemma_run_walk_left_tail_safe(tm, c_peel, q_walk, 1, (temp - 1) as nat, w, i_one_l, (h - 1) as nat);
    assert(((h - 1) - temp) as nat == (h - 1 - temp) as nat);
    lemma_tail_chain(tm, c0, 1, temp, h, (h - 1) as nat, (h - 1 - temp) as nat);

    // ── S3: erase-turnaround (R). offset h-1-temp → h-temp. ──
    assert(c_sep.a == 0);   // w % m == 0
    lemma_tm_step_picks(tm, c_sep, i_erase);
    let c_erase = apply_quint(tm.quints[i_erase], c_sep, m);
    assert(tm_step(tm, c_sep) == Some(c_erase));
    lemma_pile_ones_div_mod(v1, temp, m);
    assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == (w / m) * m, w == m * (w / m);
    assert(c_erase.u == w && c_erase.v == pile_ones(v1, (temp - 1) as nat, m) && c_erase.a == 1
        && c_erase.q == q_disc);
    assert(tm_run(tm, c_erase, 0) == c_erase);
    assert(tm_run(tm, c_sep, 1) == c_erase);
    lemma_tm_run_split(tm, c0, (1 + temp) as nat, 1);
    assert(tm_run(tm, c0, (1 + temp + 1) as nat) == c_erase);
    assert(quint_matches(tm.quints[i_erase], c_sep));
    lemma_step_tail_safe(tm, c_sep, i_erase, (h - 1 - temp) as nat);   // R, end h-temp
    assert(((h - 1 - temp) + 1) as nat == (h - temp) as nat);
    lemma_tail_chain(tm, c0, (1 + temp) as nat, 1, h, (h - 1 - temp) as nat, (h - temp) as nat);

    // ── S4: discard (R). offset h-temp → h-temp+1. ──
    lemma_tm_step_picks(tm, c_erase, i_disc);
    let c_disc = apply_quint(tm.quints[i_disc], c_erase, m);
    assert(tm_step(tm, c_erase) == Some(c_disc));
    assert(c_disc.u == w * m && c_disc.q == q_back);
    assert(tm_run(tm, c_disc, 0) == c_disc);
    assert(tm_run(tm, c_erase, 1) == c_disc);
    lemma_tm_run_split(tm, c0, (1 + temp + 1) as nat, 1);
    assert(tm_run(tm, c0, (1 + temp + 1 + 1) as nat) == c_disc);
    assert(quint_matches(tm.quints[i_disc], c_erase));
    lemma_step_tail_safe(tm, c_erase, i_disc, (h - temp) as nat);   // R, end h-temp+1
    assert(((h - temp) + 1) as nat == (h - temp + 1) as nat);
    lemma_tail_chain(tm, c0, (1 + temp + 1) as nat, 1, h, (h - temp) as nat, (h - temp + 1) as nat);

    if temp == 1 {
        // c_disc is final (no walk-back). 4 steps; offset already h-temp+1 == h.
        assert((2 * temp + 2) as nat == (1 + temp + 1 + 1) as nat);
        assert((h - temp + 1) as nat == h);   // temp == 1
    } else {
        // ── S5: walk-back (temp-1 R-steps), q_back. offset h-temp+1 → h. ──
        lemma_pile_ones_div_mod(v1, (temp - 1) as nat, m);
        assert(c_disc.v == pile_ones(v1, (temp - 2) as nat, m));
        assert(c_disc.a == 1);
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c_disc.u == repunit_m(0, m) + pow_nat(m, 0) * (w * m)) by(nonlinear_arith)
            requires c_disc.u == w * m, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_walk_back_prefix(tm, c_disc, q_back, 0, (temp - 2) as nat, v1, (w * m) as nat, i_one_r);
        let c_final = TmConfig {
            u: repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * (w * m),
            v: v1 / m, a: v1 % m, q: q_back };
        assert((0 + (temp - 2) + 1) as nat == (temp - 1) as nat);
        assert(tm_run(tm, c_disc, (temp - 1) as nat) == c_final);
        lemma_tm_run_split(tm, c0, (1 + temp + 1 + 1) as nat, (temp - 1) as nat);
        assert((1 + temp + 1 + 1 + (temp - 1)) as nat == (2 * temp + 2) as nat);
        assert(tm_run(tm, c0, (2 * temp + 2) as nat) == c_final);
        // companion (s=1): c_disc.u == 1·R(0)+m^0·(w·m), c_disc.v == pile_sym(v1, 1, temp-2).
        assert(c_disc.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * (w * m)) by(nonlinear_arith)
            requires c_disc.u == w * m, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_pile_ones_eq_pile_sym(v1, (temp - 2) as nat, m);
        assert(c_disc.v == pile_sym(v1, 1, (temp - 2) as nat, m));
        lemma_run_walk_right_tail_safe(tm, c_disc, q_back, 1, 0, (temp - 2) as nat, v1, (w * m) as nat,
            i_one_r, (h - temp + 1) as nat);
        assert(((h - temp + 1) + (temp - 2) + 1) as nat == h);
        lemma_tail_chain(tm, c0, (1 + temp + 1 + 1) as nat, (temp - 1) as nat, h, (h - temp + 1) as nat,
            h);
    }
}

/// **`block_iter_block1` is tail-safe** for its `2·od.len() + 2·temp + 6` steps when the tail enters at
/// `h ≥ temp + 1`, returning to `h` (net-disp-0). Mirror of [`crate::tm_block_iter::lemma_block_iter_block1`]:
/// [`lemma_surge_emit_return_block1_tail_safe`] (emit one digit, any offset) then
/// [`lemma_dec_temp_tail_safe`] (decrement, `h ≥ temp + 1`).
pub proof fn lemma_block_iter_block1_tail_safe(
    tm: Tm, temp: nat, w: nat, od: Seq<nat>, s: nat,
    q_iter: nat, q_surge: nat, q_eret: nat, q_home: nat, q_dwalk: nat, q_disc: nat, q_back: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        temp >= 1,
        w % tm.m == 0,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_emit < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        h >= temp + 1,
    ensures
        tail_safe(tm, TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_iter },
            (2 * od.len() + 2 * temp + 6) as nat, h),
        tail_end_h(tm, TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_iter },
            (2 * od.len() + 2 * temp + 6) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    let big_u = dec_u(temp, w, m);
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };

    // ── surge ∘ emit ∘ return: output od ↦ od ++ [s]. offset h → h. ──
    lemma_surge_emit_return_block1(tm, big_u, od, s, q_iter, q_surge, q_eret, q_home,
        i_pivot_r, ir1, ir2, ir3, ir4, i_emit, i_off_l, il1, il2, il3, il4);
    let out2 = dpack(od + seq![s], m);
    let c_mid = TmConfig { u: big_u, v: out2, a: 0, q: q_home };
    assert(tm_run(tm, c0, (2 * od.len() + 4) as nat) == c_mid);
    lemma_surge_emit_return_block1_tail_safe(tm, big_u, od, s, q_iter, q_surge, q_eret, q_home,
        i_pivot_r, ir1, ir2, ir3, ir4, i_emit, i_off_l, il1, il2, il3, il4, h);

    // ── dec_temp: temp ↦ temp − 1. offset h → h (needs h ≥ temp+1). ──
    lemma_dec_temp_tail_safe(tm, temp, w, out2, q_home, q_dwalk, q_disc, q_back,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r, h);

    // ── chain. ──
    lemma_tail_chain(tm, c0, (2 * od.len() + 4) as nat, (2 * temp + 2) as nat, h, h, h);
    assert((2 * od.len() + 4 + (2 * temp + 2)) as nat == (2 * od.len() + 2 * temp + 6) as nat);
}

/// **The continue-guard is tail-safe** (2 steps, peek-L · cont-R), net-disp-0 for `h ≥ 1`. Mirror of
/// [`crate::tm_block_loop::lemma_guard_continue`].
pub proof fn lemma_guard_continue_tail_safe(
    tm: Tm, temp: nat, w: nat, out: nat, q_loop: nat, q_guard: nat, q_iter: nat,
    i_peek: int, i_cont: int, h: nat,
)
    requires
        tm_wf(tm),
        temp >= 1,
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
        h >= 1,
    ensures
        tail_safe(tm, TmConfig { u: dec_u(temp, w, tm.m), v: out, a: 0, q: q_loop }, 2, h),
        tail_end_h(tm, TmConfig { u: dec_u(temp, w, tm.m), v: out, a: 0, q: q_loop }, 2, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    lemma_dec_u_step(temp, w, m);
    let c0 = TmConfig { u: dec_u(temp, w, m), v: out, a: 0, q: q_loop };
    assert(quint_matches(tm.quints[i_peek], c0));
    lemma_tm_step_picks(tm, c0, i_peek);
    let c1 = apply_quint(tm.quints[i_peek], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.a == 1 && c1.q == q_guard);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    lemma_step_tail_safe(tm, c0, i_peek, h);   // L, end h-1
    assert(quint_matches(tm.quints[i_cont], c1));
    lemma_step_tail_safe(tm, c1, i_cont, (h - 1) as nat);   // R, end h
    assert(((h - 1) + 1) as nat == h);
    lemma_tail_chain(tm, c0, 1, 1, h, (h - 1) as nat, h);
}

/// **The exit-guard is tail-safe** (2 steps, peek-L · exit-R), net-disp-0 for `h ≥ 1`. Mirror of
/// [`crate::tm_block_loop::lemma_guard_exit`].
pub proof fn lemma_guard_exit_tail_safe(
    tm: Tm, w: nat, out: nat, q_loop: nat, q_guard: nat, q_exit: nat,
    i_peek: int, i_exit: int, h: nat,
)
    requires
        tm_wf(tm),
        w % tm.m == 0,
        0 <= i_peek < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
        h >= 1,
    ensures
        tail_safe(tm, TmConfig { u: dec_u(0, w, tm.m), v: out, a: 0, q: q_loop }, 2, h),
        tail_end_h(tm, TmConfig { u: dec_u(0, w, tm.m), v: out, a: 0, q: q_loop }, 2, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    lemma_dec_u_zero(w, m);
    let c0 = TmConfig { u: w, v: out, a: 0, q: q_loop };
    assert(quint_matches(tm.quints[i_peek], c0));
    lemma_tm_step_picks(tm, c0, i_peek);
    let c1 = apply_quint(tm.quints[i_peek], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.a == 0 && c1.q == q_guard);   // w % m == 0
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    lemma_step_tail_safe(tm, c0, i_peek, h);   // L, end h-1
    assert(quint_matches(tm.quints[i_exit], c1));
    lemma_step_tail_safe(tm, c1, i_exit, (h - 1) as nat);   // R, end h
    assert(((h - 1) + 1) as nat == h);
    lemma_tail_chain(tm, c0, 1, 1, h, (h - 1) as nat, h);
}

/// **`block_loop_block1` is tail-safe** for its `loop_fuel_b1(od.len(), temp)` steps when the tail enters
/// at `h ≥ temp + 1`, returning to `h` (net-disp-0 every iteration). Mirror of
/// [`crate::tm_block_loop::lemma_block_loop_block1`]: induct on `temp`, chaining the continue-guard, one
/// [`lemma_block_iter_block1_tail_safe`], and the recursion (or the exit-guard at `temp == 0`). Never tight
/// — the deepest reach is over the temp counter, far below the master+tail.
pub proof fn lemma_block_loop_block1_tail_safe(
    tm: Tm, temp: nat, w: nat, od: Seq<nat>, s: nat,
    q_loop: nat, q_guard: nat, q_iter: nat, q_surge: nat, q_eret: nat, q_home: nat,
    q_dwalk: nat, q_disc: nat, q_exit: nat,
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        w % tm.m == 0,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_emit < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_loop, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_loop, 1, 1, q_loop, Dir::R),
        h >= temp + 1,
    ensures
        tail_safe(tm, TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_loop },
            loop_fuel_b1(od.len(), temp), h),
        tail_end_h(tm, TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_loop },
            loop_fuel_b1(od.len(), temp), h) == h,
    decreases temp,
{
    reveal(tm_wf);
    let m = tm.m;
    let c0 = TmConfig { u: dec_u(temp, w, m), v: dpack(od, m), a: 0, q: q_loop };
    if temp == 0 {
        lemma_guard_exit_tail_safe(tm, w, dpack(od, m), q_loop, q_guard, q_exit, i_peek, i_exit, h);
        assert(loop_fuel_b1(od.len(), 0) == 2);
        assert(dec_u(0, w, m) == w) by { lemma_dec_u_zero(w, m); }
    } else {
        // ── continue guard (2 steps) → q_iter. ──
        lemma_guard_continue(tm, temp, w, dpack(od, m), q_loop, q_guard, q_iter, i_peek, i_cont);
        let c1 = TmConfig { u: dec_u(temp, w, m), v: dpack(od, m), a: 0, q: q_iter };
        assert(tm_run(tm, c0, 2) == c1);
        lemma_guard_continue_tail_safe(tm, temp, w, dpack(od, m), q_loop, q_guard, q_iter, i_peek,
            i_cont, h);

        // ── body: one block_iter (output od ↦ od++[s], temp ↦ temp-1). ──
        lemma_block_iter_block1(tm, temp, w, od, s,
            q_iter, q_surge, q_eret, q_home, q_dwalk, q_disc, q_loop,
            i_pivot_r, ir1, ir2, ir3, ir4, i_emit, i_off_l, il1, il2, il3, il4,
            i_pivot, i_one_l, i_erase, i_disc, i_one_r);
        let od2 = od + seq![s];
        let body = (2 * od.len() + 2 * temp + 6) as nat;
        let c2 = TmConfig { u: dec_u((temp - 1) as nat, (m * w) as nat, m), v: dpack(od2, m), a: 0,
            q: q_loop };
        assert(tm_run(tm, c1, body) == c2);
        lemma_block_iter_block1_tail_safe(tm, temp, w, od, s,
            q_iter, q_surge, q_eret, q_home, q_dwalk, q_disc, q_loop,
            i_pivot_r, ir1, ir2, ir3, ir4, i_emit, i_off_l, il1, il2, il3, il4,
            i_pivot, i_one_l, i_erase, i_disc, i_one_r, h);
        // chain guard · body.
        lemma_tm_run_split(tm, c0, 2, body);
        assert(tm_run(tm, c0, (2 + body) as nat) == c2);
        lemma_tail_chain(tm, c0, 2, body, h, h, h);

        // ── recurse on (od2, temp-1, m·w). od2 digits 1..4; (m·w)%m==0. ──
        assert forall|k: int| 0 <= k < od2.len() implies 1 <= #[trigger] od2[k] <= 4 by {
            if k < od.len() { assert(od2[k] == od[k]); } else { assert(od2[k] == s); }
        }
        assert((m * w) % m == 0) by {
            assert(m * w == w * m) by(nonlinear_arith);
            lemma_div_mod_step(w, m, 0);
        }
        lemma_block_loop_block1(tm, (temp - 1) as nat, (m * w) as nat, od2, s,
            q_loop, q_guard, q_iter, q_surge, q_eret, q_home, q_dwalk, q_disc, q_exit,
            i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
            i_emit, i_off_l, il1, il2, il3, il4, i_pivot, i_one_l, i_erase, i_disc, i_one_r);
        let rec = loop_fuel_b1(od2.len(), (temp - 1) as nat);
        lemma_block_loop_block1_tail_safe(tm, (temp - 1) as nat, (m * w) as nat, od2, s,
            q_loop, q_guard, q_iter, q_surge, q_eret, q_home, q_dwalk, q_disc, q_exit,
            i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
            i_emit, i_off_l, il1, il2, il3, il4, i_pivot, i_one_l, i_erase, i_disc, i_one_r, h);
        // chain (guard·body) · recurse.
        lemma_tail_chain(tm, c0, (2 + body) as nat, rec, h, h, h);
        assert(loop_fuel_b1(od.len(), temp) == (2 + body + rec) as nat);
    }
}

} // verus!
