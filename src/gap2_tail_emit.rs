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
use crate::tm::{Tm, TmConfig, tm_wf, apply_quint, quint_matches};
use crate::tm_gadget::mk_quint;
use crate::tm_dstring::{dpack, dpile, pow_nat, lemma_dpack_pop, lemma_pow_nat_unfold};
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_tail_unfold};

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

} // verus!
