//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the master-decrement foundation.
//!
//! Model B's per-block loop decrements a master counter (`iₐ` or `i_b`) at "home" each iteration. The
//! home layout is `[iₐ ones] 0 [i_b ones] 0 [output] 0 [blanks]`, head on the pivot `0` before the output.
//! Decrementing `i_b` mirrors [`crate::tm_dec::lemma_dec`] (walk out over `i_b`'s ones, erase the OUTER
//! one at the `i_b/iₐ` separator, walk back — keeping `i_b` adjacent to the pivot, no gap growth), with one
//! twist: the left tape is NOT a bare counter, it carries `iₐ`'s content beyond the `i_b/iₐ` separator. So
//! the walk-left must STOP at that separator and LEAVE the high content intact, unlike
//! [`crate::tm_walk::lemma_walk_left_inner`] (which assumes the rest of `u` is blank and lands `u == 0`).
//!
//! This file is the foundation: [`lemma_walk_left_prefix`], the generalized walk-left over a `repunit`
//! PREFIX with an arbitrary high tail `w` left in `u`. The walk-BACK reuses
//! [`crate::tm_walk::lemma_walk_back_inner`] verbatim (it is already generic in the under-pile content).
//! The full `dec_master` gadget + `home_config` build on this next.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_pile_ones_shift};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};

verus! {

/// **Generalized walk-left over a `repunit` prefix with a high tail `w`.** From a config in state
/// `q_walk` scanning a `1`, with `j0` further ones and then the tail `w` packed above them in `u`
/// (`u == repunit_m(j0) + pow_nat(m, j0)·w`), the loop quintuple `(q_walk, 1, 1, q_walk, L)` fires
/// `j0 + 1` times — peeling the scanned `1` and the `j0` ones, piling all `j0 + 1` onto `v` — and lands
/// the head on `w`'s low cell (`a == w % m`, `u == w / m`), still in `q_walk`. The `dec_master` analog of
/// [`crate::tm_walk::lemma_walk_left_inner`]: instead of assuming the rest of `u` is blank (landing
/// `u == 0`), it LEAVES the high tail `w` intact. The caller sets `w % m == 0` (the `i_b/iₐ` separator
/// blank) so the head stops on a blank, where the erase-turnaround then fires. Induction on `j0`.
pub proof fn lemma_walk_left_prefix(tm: Tm, c: TmConfig, q_walk: nat, j0: nat, w: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        c.u == repunit_m(j0, tm.m) + pow_nat(tm.m, j0) * w,
        c.a == 1,
        c.q == q_walk,
    ensures
        tm_run(tm, c, (j0 + 1) as nat)
            == (TmConfig { u: w / tm.m, v: pile_ones(c.v, (j0 + 1) as nat, tm.m),
                a: w % tm.m, q: q_walk }),
    decreases j0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches (q == q_walk, a == 1) and fires (L-move, a2 == 1).
    lemma_tm_step_picks(tm, c, i1);
    let c_next = TmConfig { u: c.u / m, v: c.v * m + 1, a: c.u % m, q: q_walk };
    assert(tm_step(tm, c) == Some(c_next));
    if j0 == 0 {
        // u == repunit(0) + pow_nat(m,0)·w == 0 + 1·w == w.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(1nat * w == w) by(nonlinear_arith);
        assert(c.u == w);
        // c_next == (w/m, pile_ones(c.v,1), w%m, q_walk).
        assert(pile_ones(c.v, 0, m) == c.v);
        assert(pile_ones(c.v, 1, m) == pile_ones(c.v, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: w / m, v: pile_ones(c.v, 1, m), a: w % m, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == repunit(j0) + m^j0·w == (repunit(j0-1) + m^(j0-1)·w)·m + 1.
        let x = repunit_m((j0 - 1) as nat, m) + pow_nat(m, (j0 - 1) as nat) * w;
        assert(repunit_m(j0, m) == m * repunit_m((j0 - 1) as nat, m) + 1);   // repunit recurrence
        lemma_pow_nat_unfold(m, j0);                                         // m^j0 == m·m^(j0-1)
        assert(c.u == x * m + 1) by(nonlinear_arith)
            requires
                c.u == repunit_m(j0, m) + pow_nat(m, j0) * w,
                repunit_m(j0, m) == m * repunit_m((j0 - 1) as nat, m) + 1,
                pow_nat(m, j0) == m * pow_nat(m, (j0 - 1) as nat),
                x == repunit_m((j0 - 1) as nat, m) + pow_nat(m, (j0 - 1) as nat) * w;
        lemma_div_mod_step(x, m, 1);   // (x·m + 1)/m == x, %m == 1
        assert(c_next.u == x);
        assert(c_next.a == 1);
        lemma_walk_left_prefix(tm, c_next, q_walk, (j0 - 1) as nat, w, i1);
        // IH: tm_run(c_next, j0) == (w/m, pile_ones(c.v·m+1, j0), w%m, q_walk).
        lemma_pile_ones_shift(c.v, j0, m);   // pile_ones(c.v·m+1, j0) == pile_ones(c.v, j0+1)
        assert(tm_run(tm, c, (j0 + 1) as nat) == tm_run(tm, c_next, j0));
    }
}

} // verus!
