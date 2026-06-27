//! # GAP-2 G2-F Route (i) brick R-cmp (B-cmp.0) — the skip-blank (skip-`0`) walk loops.
//!
//! The compare phase (R-cmp, M1 design — see `docs/gap2-input-loader-plan.md` §N+19) shuttles the head
//! between the output block (in `u`) and the parked `alpha` block (in `v`), crossing a GAP of blank cells
//! (`0`) that grows as matched output digits are consumed to `0`. Crossing the gap is a uniform
//! `(q, 0, 0, q, dir)` loop — the blank analog of [`crate::tm_walk::lemma_walk_left_inner`] (which loops
//! on the unary symbol `1`). This file is that primitive: peel exactly `k + 1` blanks off the near stack
//! onto the far stack and land the head on the first cell BELOW them — the next nonblank frontier digit
//! (or a sentinel `5`), whose value the caller reads as `rest % m`.
//!
//! Unlike `lemma_walk_left_inner` (whose `u == repunit_m(j0)` is *all* ones, peeled to the blank beyond),
//! the skip-blank loop runs over `k` blanks above an **arbitrary** `rest` (`u == rest·m^k`), so it is a
//! fixed-fuel `k + 1` step lemma: the caller arranges `rest % m != 0` to know the loop stopped on a
//! frontier and not deeper in the gap.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};

verus! {

/// `pile_zeros(v, k, m)` = pushing `k` blanks (`0`) onto stack `v` (each push is `·m`, i.e. `·m + 0`).
/// Closed form `v·m^k`; defined by the push recurrence so `m^k` stays implicit (mirrors
/// [`crate::tm_walk::pile_ones`]).
pub open spec fn pile_zeros(v: nat, k: nat, m: nat) -> nat
    decreases k
{
    if k == 0 { v } else { pile_zeros(v, (k - 1) as nat, m) * m }
}

/// Pushing `k` blanks onto `v·m` is the same as pushing `k + 1` blanks onto `v` (both closed forms equal
/// `v·m^{k+1}`). The bridge that lets the loop induction re-fold the pile (mirrors
/// [`crate::tm_walk::lemma_pile_ones_shift`]).
pub proof fn lemma_pile_zeros_shift(v: nat, k: nat, m: nat)
    ensures
        pile_zeros(v * m, k, m) == pile_zeros(v, (k + 1) as nat, m),
    decreases k,
{
    if k == 0 {
        // pile_zeros(v*m, 0) == v*m == pile_zeros(v, 0)*m == pile_zeros(v, 1).
        assert(pile_zeros(v * m, 0, m) == v * m);
        assert(pile_zeros(v, 0, m) == v);
        assert(pile_zeros(v, 1, m) == pile_zeros(v, 0, m) * m);
    } else {
        lemma_pile_zeros_shift(v, (k - 1) as nat, m);
        // pile_zeros(v*m, k) == pile_zeros(v*m, k-1)*m == pile_zeros(v, k)*m == pile_zeros(v, k+1).
    }
}

/// **The skip-blank-left loop.** From state `q_walk` scanning a blank (`a == 0`), with the next `k` low
/// digits of `u` also blank above an arbitrary `rest` (`u == pile_zeros(rest, k, m) == rest·m^k`), the
/// loop quintuple `(q_walk, 0, 0, q_walk, L)` fires `k + 1` times — peeling the `k + 1` blanks (the
/// scanned one + the `k` in `u`) onto `v` — and lands the head on `rest`'s low digit (`a == rest % m`),
/// `u == rest / m`, still in `q_walk`. Induction on `k`, mirroring [`crate::tm_walk::lemma_walk_left_inner`].
pub proof fn lemma_skip0_left(tm: Tm, c: TmConfig, q_walk: nat, k: nat, rest: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_walk, 0, 0, q_walk, Dir::L),
        c.a == 0,
        c.u == pile_zeros(rest, k, tm.m),
        c.q == q_walk,
    ensures
        tm_run(tm, c, (k + 1) as nat)
            == (TmConfig { u: rest / tm.m, v: pile_zeros(c.v, (k + 1) as nat, tm.m), a: rest % tm.m, q: q_walk }),
    decreases k,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches c (q == q_walk, a == 0) and fires; L-move with a2 == 0.
    lemma_tm_step_picks(tm, c, i0);
    let c_next = (TmConfig { u: c.u / m, v: c.v * m + 0, a: c.u % m, q: q_walk });
    assert(tm_step(tm, c) == Some(c_next));
    if k == 0 {
        // c.u == pile_zeros(rest, 0) == rest.
        assert(c.u == rest);
        assert(c_next.u == rest / m);
        assert(c_next.a == rest % m);
        assert(pile_zeros(c.v, 0, m) == c.v);
        assert(pile_zeros(c.v, 1, m) == pile_zeros(c.v, 0, m) * m);   // == c.v * m == c_next.v
        assert(c_next.v == c.v * m);
        assert(c_next == (TmConfig { u: rest / m, v: pile_zeros(c.v, 1, m), a: rest % m, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // c.u == pile_zeros(rest, k) == pile_zeros(rest, k-1) * m ⟹ peel one blank.
        let lower = pile_zeros(rest, (k - 1) as nat, m);
        assert(c.u == lower * m);
        assert((lower * m) % m == 0) by(nonlinear_arith) requires m > 1;
        assert((lower * m) / m == lower) by(nonlinear_arith) requires m > 1;
        assert(c_next.a == 0);
        assert(c_next.u == lower);
        assert(c_next.v == c.v * m);
        lemma_skip0_left(tm, c_next, q_walk, (k - 1) as nat, rest, i0);
        // IH: tm_run(c_next, k) == (rest/m, pile_zeros(c.v*m, k), rest%m, q_walk).
        lemma_pile_zeros_shift(c.v, k, m);   // pile_zeros(c.v*m, k) == pile_zeros(c.v, k+1)
        assert(tm_run(tm, c, (k + 1) as nat) == tm_run(tm, c_next, k));
    }
}

/// **The skip-blank-right loop** — the mirror of [`lemma_skip0_left`] (`u ↔ v`, `L ↔ R`). From state
/// `q_back` scanning a blank (`a == 0`), with the next `k` low digits of `v` also blank above an
/// arbitrary `rest` (`v == pile_zeros(rest, k, m)`), the loop quintuple `(q_back, 0, 0, q_back, R)` fires
/// `k + 1` times — peeling the `k + 1` blanks onto `u` — and lands the head on `rest`'s low digit
/// (`a == rest % m`), `v == rest / m`, still in `q_back`.
pub proof fn lemma_skip0_right(tm: Tm, c: TmConfig, q_back: nat, k: nat, rest: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_back, 0, 0, q_back, Dir::R),
        c.a == 0,
        c.v == pile_zeros(rest, k, tm.m),
        c.q == q_back,
    ensures
        tm_run(tm, c, (k + 1) as nat)
            == (TmConfig { u: pile_zeros(c.u, (k + 1) as nat, tm.m), v: rest / tm.m, a: rest % tm.m, q: q_back }),
    decreases k,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_tm_step_picks(tm, c, i0);
    let c_next = (TmConfig { u: c.u * m + 0, v: c.v / m, a: c.v % m, q: q_back });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint R with a2 == 0
    if k == 0 {
        assert(c.v == rest);
        assert(c_next.v == rest / m);
        assert(c_next.a == rest % m);
        assert(pile_zeros(c.u, 0, m) == c.u);
        assert(pile_zeros(c.u, 1, m) == pile_zeros(c.u, 0, m) * m);
        assert(c_next.u == c.u * m);
        assert(c_next == (TmConfig { u: pile_zeros(c.u, 1, m), v: rest / m, a: rest % m, q: q_back }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        let lower = pile_zeros(rest, (k - 1) as nat, m);
        assert(c.v == lower * m);
        assert((lower * m) % m == 0) by(nonlinear_arith) requires m > 1;
        assert((lower * m) / m == lower) by(nonlinear_arith) requires m > 1;
        assert(c_next.a == 0);
        assert(c_next.v == lower);
        assert(c_next.u == c.u * m);
        lemma_skip0_right(tm, c_next, q_back, (k - 1) as nat, rest, i0);
        lemma_pile_zeros_shift(c.u, k, m);
        assert(tm_run(tm, c, (k + 1) as nat) == tm_run(tm, c_next, k));
    }
}

} // verus!
