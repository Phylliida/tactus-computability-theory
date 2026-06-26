//! # GAP-2-E brick B3 (part 1) — the walk-left loop
//!
//! The inc/dec gadgets (`docs/gap2-register-to-tm-plan.md` B3/B4) walk the head out through a unary
//! block, peeling its `1`s onto the opposite stack, edit at the turnaround, then walk back. This file
//! builds the **walk-left ones-loop**: the uniform `(q_walk, 1, 1, q_walk, L)` step repeated until the
//! head falls off the block into the left blank. The peeled `1`s pile onto `v`; `pile_ones` is that
//! pile and `lemma_walk_left_inner` is the decreasing-fuel loop lemma (the analog of
//! `multi_output_primitives::lemma_copy_loop_inner`).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_two_counter::{repunit_m, lemma_repunit_div_mod, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};

verus! {

/// `pile_ones(v, k, m)` = the result of pushing `k` ones onto stack `v` (each push is `·m + 1`, the
/// low end). Closed form `v·m^k + repunit_m(k)`; defined by the push recurrence to keep `m^k` implicit.
pub open spec fn pile_ones(v: nat, k: nat, m: nat) -> nat
    decreases k
{
    if k == 0 { v } else { pile_ones(v, (k - 1) as nat, m) * m + 1 }
}

/// Pushing `k` ones onto `v·m + 1` is the same as pushing `k + 1` ones onto `v` (the closed forms both
/// equal `v·m^{k+1} + repunit_m(k+1)`). The bridge that lets the loop induction re-fold the pile.
pub proof fn lemma_pile_ones_shift(v: nat, k: nat, m: nat)
    ensures
        pile_ones(v * m + 1, k, m) == pile_ones(v, (k + 1) as nat, m),
    decreases k,
{
    if k == 0 {
        // pile_ones(v*m+1, 0) == v*m+1 == pile_ones(v, 0)*m+1 == pile_ones(v, 1).
        assert(pile_ones(v * m + 1, 0, m) == v * m + 1);
        assert(pile_ones(v, 0, m) == v);
        assert(pile_ones(v, 1, m) == pile_ones(v, 0, m) * m + 1);
    } else {
        lemma_pile_ones_shift(v, (k - 1) as nat, m);
        // pile_ones(v*m+1, k) == pile_ones(v*m+1, k-1)*m+1 == pile_ones(v, k)*m+1 == pile_ones(v, k+1).
    }
}

/// **The walk-left ones-loop.** From a config in state `q_walk` scanning a `1`, with `j0` further ones
/// in `u` (`u == repunit_m(j0)`), the loop quintuple `(q_walk, 1, 1, q_walk, L)` fires `j0 + 1` times —
/// peeling the scanned `1` and the `j0` ones in `u`, piling all `j0 + 1` onto `v` — and lands the head
/// on the left blank (`u == 0`, scanned `== 0`), still in `q_walk` (where the turnaround quintuple
/// `(q_walk, 0, …)` then fires). Induction on `j0`, mirroring `lemma_copy_loop_inner`.
pub proof fn lemma_walk_left_inner(tm: Tm, c: TmConfig, q_walk: nat, j0: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        c.u == repunit_m(j0, tm.m),
        c.a == 1,
        c.q == q_walk,
    ensures
        tm_run(tm, c, (j0 + 1) as nat)
            == (TmConfig { u: 0, v: pile_ones(c.v, (j0 + 1) as nat, tm.m), a: 0, q: q_walk }),
    decreases j0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches c (q == q_walk, a == 1) and fires.
    lemma_tm_step_picks(tm, c, i1);
    let c_next = (TmConfig { u: c.u / m, v: c.v * m + 1, a: c.u % m, q: q_walk });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint L with a2 == 1
    if j0 == 0 {
        // c.u == repunit(0) == 0 ⟹ c_next == (0, c.v*m+1, 0, q_walk) == (0, pile_ones(c.v,1), 0, q_walk).
        lemma_repunit_zero(m);
        assert(c.u == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(pile_ones(c.v, 0, m) == c.v);
        assert(pile_ones(c.v, 1, m) == pile_ones(c.v, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: 0, v: pile_ones(c.v, 1, m), a: 0, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // c.u == repunit(j0); peel one ⟹ c_next.u == repunit(j0-1), c_next.a == 1.
        lemma_repunit_div_mod((j0 - 1) as nat, m);
        assert(((j0 - 1) as nat + 1) as nat == j0);
        assert(c_next.u == repunit_m((j0 - 1) as nat, m));
        assert(c_next.a == 1);
        lemma_walk_left_inner(tm, c_next, q_walk, (j0 - 1) as nat, i1);
        // IH: tm_run(c_next, j0) == (0, pile_ones(c.v*m+1, j0), 0, q_walk).
        lemma_pile_ones_shift(c.v, j0, m);   // pile_ones(c.v*m+1, j0) == pile_ones(c.v, j0+1)
        // tm_run(c, j0+1) == tm_run(c_next, j0).
        assert(tm_run(tm, c, (j0 + 1) as nat) == tm_run(tm, c_next, j0));
    }
}

} // verus!
