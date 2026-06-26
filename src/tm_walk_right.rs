//! # GAP-2-E brick B5.1 — the right-counter walk loops (mirror of `tm_walk.rs`)
//!
//! The right counter `c2` lives in `v`; its inc/dec gadgets walk the head **right** through that
//! block via `Dir::R` moves (`v → v/m`, piling the peeled `1`s onto `u`), then walk back **left**
//! via `Dir::L`. These are the exact `u ↔ v`, `L ↔ R` mirrors of `lemma_walk_left_inner` /
//! `lemma_walk_back_inner`. The pile is symmetric, so `pile_ones` and its helpers are reused verbatim
//! (here the pile accumulates on `u` instead of `v`).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_two_counter::{repunit_m, lemma_repunit_div_mod, lemma_repunit_step, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_pile_ones_shift, lemma_pile_ones_div_mod};

verus! {

/// **The walk-right ones-loop** (mirror of `lemma_walk_left_inner`). From a config in state `q_walk`
/// scanning a `1`, with `j0` further ones in `v` (`v == repunit_m(j0)`), the loop quintuple
/// `(q_walk, 1, 1, q_walk, R)` fires `j0 + 1` times — peeling the scanned `1` and the `j0` ones in
/// `v`, piling all `j0 + 1` onto `u` — and lands the head on the right blank (`v == 0`, scanned
/// `== 0`), still in `q_walk`. Induction on `j0`.
pub proof fn lemma_walk_right_inner(tm: Tm, c: TmConfig, q_walk: nat, j0: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::R),
        c.v == repunit_m(j0, tm.m),
        c.a == 1,
        c.q == q_walk,
    ensures
        tm_run(tm, c, (j0 + 1) as nat)
            == (TmConfig { u: pile_ones(c.u, (j0 + 1) as nat, tm.m), v: 0, a: 0, q: q_walk }),
    decreases j0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_tm_step_picks(tm, c, i1);
    let c_next = (TmConfig { u: c.u * m + 1, v: c.v / m, a: c.v % m, q: q_walk });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint R with a2 == 1
    if j0 == 0 {
        lemma_repunit_zero(m);
        assert(c.v == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(pile_ones(c.u, 0, m) == c.u);
        assert(pile_ones(c.u, 1, m) == pile_ones(c.u, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: pile_ones(c.u, 1, m), v: 0, a: 0, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        lemma_repunit_div_mod((j0 - 1) as nat, m);
        assert(((j0 - 1) as nat + 1) as nat == j0);
        assert(c_next.v == repunit_m((j0 - 1) as nat, m));
        assert(c_next.a == 1);
        lemma_walk_right_inner(tm, c_next, q_walk, (j0 - 1) as nat, i1);
        // IH: tm_run(c_next, j0) == (pile_ones(c.u*m+1, j0), 0, 0, q_walk).
        lemma_pile_ones_shift(c.u, j0, m);   // pile_ones(c.u*m+1, j0) == pile_ones(c.u, j0+1)
        assert(tm_run(tm, c, (j0 + 1) as nat) == tm_run(tm, c_next, j0));
    }
}

/// **The walk-back-left ones-loop** (mirror of `lemma_walk_back_inner`). From a config in state
/// `q_back` scanning a `1`, with `k0` ones already reconstructed in `v` (`v == repunit_m(k0)`) and a
/// pile of `rem0` ones sitting above `W` in `u` (`u == pile_ones(W, rem0)`), the
/// `(q_back, 1, 1, q_back, L)` step fires `rem0 + 1` times — writing each `1` back onto `v` and
/// popping the pile — landing `v == repunit_m(k0 + rem0 + 1)` with the head on `W`'s low cell
/// (`a == W % m`, `u == W / m`). For the inc-right gadget `W = repunit(c1)·m + 2`, so the head lands
/// on the separator.
pub proof fn lemma_walk_back_left_inner(tm: Tm, c: TmConfig, q_back: nat, k0: nat, rem0: nat, w: nat, i1b: int)
    requires
        tm_wf(tm),
        0 <= i1b < tm.quints.len(),
        tm.quints[i1b] == mk_quint(q_back, 1, 1, q_back, Dir::L),
        c.v == repunit_m(k0, tm.m),
        c.u == pile_ones(w, rem0, tm.m),
        c.a == 1,
        c.q == q_back,
    ensures
        tm_run(tm, c, (rem0 + 1) as nat)
            == (TmConfig { u: w / tm.m, v: repunit_m((k0 + rem0 + 1) as nat, tm.m), a: w % tm.m, q: q_back }),
    decreases rem0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_tm_step_picks(tm, c, i1b);
    let c_next = (TmConfig { u: c.u / m, v: c.v * m + 1, a: c.u % m, q: q_back });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint L with a2 == 1
    // c_next.v == repunit(k0+1).
    lemma_repunit_step(k0, m);
    assert(repunit_m(k0, m) * m == m * repunit_m(k0, m)) by(nonlinear_arith);
    assert(c_next.v == repunit_m((k0 + 1) as nat, m));
    if rem0 == 0 {
        assert(pile_ones(w, 0, m) == w);
        assert(c_next == (TmConfig { u: w / m, v: repunit_m((k0 + 1) as nat, m), a: w % m, q: q_back }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        lemma_pile_ones_div_mod(w, rem0, m);
        assert(c_next.a == 1);
        assert(c_next.u == pile_ones(w, (rem0 - 1) as nat, m));
        lemma_walk_back_left_inner(tm, c_next, q_back, (k0 + 1) as nat, (rem0 - 1) as nat, w, i1b);
        assert(((k0 + 1) + (rem0 - 1) + 1) as nat == (k0 + rem0 + 1) as nat);
        assert(tm_run(tm, c, (rem0 + 1) as nat) == tm_run(tm, c_next, rem0));
    }
}

} // verus!
