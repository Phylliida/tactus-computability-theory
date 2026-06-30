//! # GAP-2 G2-F — α-srm brick 1: the §9 walk-to-blank loops `R₀` / `L₀`.
//!
//! The body of the dovetail simulates the (unary) enumerator register machine via Shepherdson–Sturgis
//! *Computability of Recursive Functions* §8–§9 (the **single rotating string register**, `α-srm`; see
//! `docs/gap2-input-loader-plan.md` §N+52). §8's whole rationale is to replace the LRM's *middle-of-word*
//! operations by ones that "affect only the beginning and end of A", and §9 realizes the resulting SRM on
//! a literal left/right TM by **walk-to-blank** subroutines — head moves toward an end, peeling a word's
//! letters across the head, and stops on the next blank. No interior cell is ever opened or shifted.
//!
//! For the enumerator the registers are **unary**, so every word of the string register `A = A₁ 0 A₂ 0 …`
//! is a run of `1`s separated by blanks (`0`). §9's `R₀` ("proceed to next blank to the right") therefore
//! peels one run of `1`s and lands on its trailing separator. This file is that primitive, as a strict
//! generalization of [`crate::tm_walk::lemma_walk_right_inner`] / [`crate::tm_walk::lemma_walk_left_inner`]:
//! those take the ones-run to be the *whole* stack (`v == repunit_m(j0)`); here the run sits **above an
//! arbitrary tail** `rest` (the separator + the rest of `A`), so the lemma is a fixed-fuel `L + 1` step
//! statement (like [`crate::tm_skip_blank`]). The caller arranges `rest % m == 0` to know the head stopped
//! on the separator blank rather than mid-tape.
//!
//! The "`L` ones above `rest`" representation is *exactly* `pile_ones(rest, L, m)` (push `L` ones onto
//! `rest`, low-first — closed form `rest·mᴸ + repunit_m(L)`), so no new spec and no explicit `mᵏ` are
//! needed; the proofs reuse `pile_ones` and its div/mod + shift lemmas directly, mirroring the ones-loops
//! almost line-for-line.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_pile_ones_shift, lemma_pile_ones_div_mod};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **`R₀` — walk right to the next blank.** From a config in state `q` scanning a `1` (the first letter
/// of a unary word), with `L` further `1`s of that word in `v` above an arbitrary tail `rest`
/// (`v == pile_ones(rest, L, m)`), the loop quintuple `(q, 1, 1, q, R)` fires exactly `L + 1` times —
/// peeling the scanned `1` and the `L` ones in `v` across the head onto `u` — and lands the head on the
/// cell that followed the run (`a == rest % m`, `v == rest / m`), still in `q`. When `rest % m == 0`
/// (the run is immediately followed by a separator blank, as in `A₁ 0 A₂ …`) the head lands ON that
/// blank — "the next blank to the right". Fixed fuel `L + 1`; induction on `L`. Strictly generalizes
/// [`crate::tm_walk::lemma_walk_right_inner`] (the `rest == 0` case).
pub proof fn lemma_walk_right_to_blank(tm: Tm, c: TmConfig, q: nat, l: nat, rest: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q, 1, 1, q, Dir::R),
        c.v == pile_ones(rest, l, tm.m),
        c.a == 1,
        c.q == q,
    ensures
        tm_run(tm, c, (l + 1) as nat)
            == (TmConfig { u: pile_ones(c.u, (l + 1) as nat, tm.m), v: rest / tm.m, a: rest % tm.m, q }),
    decreases l,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches c (q == q, a == 1) and fires: push the scanned `1` onto u, pop v.
    lemma_tm_step_picks(tm, c, i1);
    let c_next = (TmConfig { u: c.u * m + 1, v: c.v / m, a: c.v % m, q });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint R with a2 == 1
    if l == 0 {
        // c.v == pile_ones(rest, 0) == rest ⟹ c_next == (c.u*m+1, rest/m, rest%m, q).
        assert(pile_ones(rest, 0, m) == rest);
        assert(pile_ones(c.u, 0, m) == c.u);
        assert(pile_ones(c.u, 1, m) == pile_ones(c.u, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: pile_ones(c.u, 1, m), v: rest / m, a: rest % m, q }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // c.v == pile_ones(rest, l); pop the low `1` ⟹ c_next.v == pile_ones(rest, l-1), c_next.a == 1.
        lemma_pile_ones_div_mod(rest, l, m);
        assert(c_next.v == pile_ones(rest, (l - 1) as nat, m));
        assert(c_next.a == 1);
        lemma_walk_right_to_blank(tm, c_next, q, (l - 1) as nat, rest, i1);
        // IH: tm_run(c_next, l) == (pile_ones(c.u*m+1, l), rest/m, rest%m, q).
        lemma_pile_ones_shift(c.u, l, m);   // pile_ones(c.u*m+1, l) == pile_ones(c.u, l+1)
        assert(tm_run(tm, c, (l + 1) as nat) == tm_run(tm, c_next, l));
    }
}

/// **`L₀` — walk left to the next blank** (the mirror of [`lemma_walk_right_to_blank`]). From a config in
/// state `q` scanning a `1`, with `L` further `1`s of the word in `u` above an arbitrary tail `rest`
/// (`u == pile_ones(rest, L, m)`), the loop quintuple `(q, 1, 1, q, L)` fires `L + 1` times — peeling the
/// scanned `1` and the `L` ones in `u` across the head onto `v` — and lands the head on the cell that
/// preceded the run (`a == rest % m`, `u == rest / m`), still in `q`. Used by `aₙ` (append-end) to walk
/// back left after printing. Fixed fuel `L + 1`; induction on `L`. Strictly generalizes
/// [`crate::tm_walk::lemma_walk_left_inner`] (the `rest == 0` case).
pub proof fn lemma_walk_left_to_blank(tm: Tm, c: TmConfig, q: nat, l: nat, rest: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q, 1, 1, q, Dir::L),
        c.u == pile_ones(rest, l, tm.m),
        c.a == 1,
        c.q == q,
    ensures
        tm_run(tm, c, (l + 1) as nat)
            == (TmConfig { u: rest / tm.m, v: pile_ones(c.v, (l + 1) as nat, tm.m), a: rest % tm.m, q }),
    decreases l,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_tm_step_picks(tm, c, i1);
    let c_next = (TmConfig { u: c.u / m, v: c.v * m + 1, a: c.u % m, q });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint L with a2 == 1
    if l == 0 {
        assert(pile_ones(rest, 0, m) == rest);
        assert(pile_ones(c.v, 0, m) == c.v);
        assert(pile_ones(c.v, 1, m) == pile_ones(c.v, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: rest / m, v: pile_ones(c.v, 1, m), a: rest % m, q }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        lemma_pile_ones_div_mod(rest, l, m);
        assert(c_next.u == pile_ones(rest, (l - 1) as nat, m));
        assert(c_next.a == 1);
        lemma_walk_left_to_blank(tm, c_next, q, (l - 1) as nat, rest, i1);
        lemma_pile_ones_shift(c.v, l, m);   // pile_ones(c.v*m+1, l) == pile_ones(c.v, l+1)
        assert(tm_run(tm, c, (l + 1) as nat) == tm_run(tm, c_next, l));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// R₀^N — the §9 "proceed to next blank to the right, N times" word-counter.
//
// §9's `P_N` (append to the end of the register-word `A = A₁ 0 A₂ 0 … 0 A_N 0`) is
// `L, R₀^N, P^(i), L₀^N, R`: walk right past the `N` separating blanks to the trailing blank
// beyond `A_N`, print, walk back. `R₀` ("proceed to next blank to the right" = `R, J^(1)[1]`)
// peels ONE word and lands on its trailing separator — that is exactly brick 1
// (`lemma_walk_right_to_blank`) preceded by one `R`. Doing it `N` times needs **distinct states**
// (a single state would walk right forever — §8.2/§9's "must know the number of commas" subtlety):
// states `g₀…g_N`, a **cross-separator** quint `(g_j, 0, 0, g_{j+1}, R)` per blank and a **walk**
// quint `(g_{j+1}, 1, 1, g_{j+1}, R)` per word. From the head on the leading blank in `g₀`, the
// machine lands on `A_N`'s trailing blank in `g_N`. `N` is the fixed register count, so the quint
// list is finite. (Plan §N+54 §V; faithful §9 port, layout-agnostic like brick 1.)
//
// The right half-tape `v` holding `A₁ 0 A₂ 0 … 0 A_N 0 [rest]` (low digit = head-adjacent = front of
// `A₁`) is `words_layout([l₁,…,l_N], rest, m)`: each word is a unary run `pile_ones(·)` with a `0`
// separator above it. Built directly on the existing `pile_ones`, no new tape spec.

/// The right half-tape layout of `N` unary words followed by `rest`: `[A₁][0][A₂][0]…[A_N][0][rest]`,
/// low-first (`A₁`'s front is the lowest base-`m` digit). Each `words[j]` is the length (ones-count) of
/// word `A_{j+1}`; the `* m` inserts the `0` separator above each word.
pub open spec fn words_layout(words: Seq<nat>, rest: nat, m: nat) -> nat
    decreases words.len()
{
    if words.len() == 0 {
        rest
    } else {
        pile_ones(words_layout(words.drop_first(), rest, m) * m, words.first(), m)
    }
}

/// **One `R₀` step of the counter: cross a separator, walk the next word, land on its separator.**
/// From the head ON a separator blank (`a == 0`) in state `g`, with the next word (`l` ones) sitting
/// above an arbitrary `inner` tail in `v` (`v == pile_ones(inner * m, l, m)` = `[l ones][0][inner]`),
/// the cross quint `(g, 0, 0, g2, R)` steps off the separator into the word and the walk quint
/// `(g2, 1, 1, g2, R)` peels the word's ones (brick 1); after `l + 1` steps the head lands ON the
/// word's trailing separator (`a == 0`, `v == inner`) in state `g2`, with the separator + the word
/// pushed onto `u`. Handles the empty word (`l == 0`: the cross lands directly on the next separator,
/// no walk). The inductive step of `R₀^N`.
pub proof fn lemma_r0_word_step(
    tm: Tm, c: TmConfig, g: nat, g2: nat, l: nat, inner: nat, i_cross: int, i_walk: int,
)
    requires
        tm_wf(tm),
        0 <= i_cross < tm.quints.len(),
        0 <= i_walk < tm.quints.len(),
        tm.quints[i_cross] == mk_quint(g, 0, 0, g2, Dir::R),
        tm.quints[i_walk] == mk_quint(g2, 1, 1, g2, Dir::R),
        c.a == 0,
        c.q == g,
        c.v == pile_ones(inner * tm.m, l, tm.m),
    ensures
        tm_run(tm, c, (l + 1) as nat)
            == (TmConfig { u: pile_ones(c.u * tm.m, l, tm.m), v: inner, a: 0, q: g2 }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the cross quintuple matches c (q == g, a == 0) and fires: push the separator `0` onto u, pop v.
    lemma_tm_step_picks(tm, c, i_cross);
    let c1 = (TmConfig { u: c.u * m + 0, v: c.v / m, a: c.v % m, q: g2 });
    assert(tm_step(tm, c) == Some(c1));   // apply_quint R with a2 == 0
    assert(c.u * m + 0 == c.u * m);
    if l == 0 {
        // v == pile_ones(inner*m, 0) == inner*m ⟹ c1 lands on the separator: a == 0, v == inner.
        assert(pile_ones(inner * m, 0, m) == inner * m);
        assert((inner * m) % m == 0) by(nonlinear_arith) requires m > 1;
        assert((inner * m) / m == inner) by(nonlinear_arith) requires m > 1;
        assert(pile_ones(c.u * m, 0, m) == c.u * m);
        assert(c1 == (TmConfig { u: pile_ones(c.u * m, 0, m), v: inner, a: 0, q: g2 }));
        assert(tm_run(tm, c1, 0) == c1);
        assert(tm_run(tm, c, 1) == c1);
    } else {
        // v == pile_ones(inner*m, l), l ≥ 1 ⟹ c1.a == 1, c1.v == pile_ones(inner*m, l-1).
        lemma_pile_ones_div_mod(inner * m, l, m);
        assert(c1.a == 1);
        assert(c1.v == pile_ones(inner * m, (l - 1) as nat, m));
        assert(c1.u == c.u * m);
        // brick 1 from c1 with tail `inner*m`: walk g2, `l-1` more ones, fires `l` steps, lands on the
        // separator (`(inner*m) % m == 0`, `(inner*m) / m == inner`).
        lemma_walk_right_to_blank(tm, c1, g2, (l - 1) as nat, inner * m, i_walk);
        assert((inner * m) % m == 0) by(nonlinear_arith) requires m > 1;
        assert((inner * m) / m == inner) by(nonlinear_arith) requires m > 1;
        assert(((l - 1) as nat + 1) as nat == l);
        // compose: tm_run(c, 1 + l) == tm_run(tm_run(c, 1), l) == tm_run(c1, l) == target.
        lemma_tm_run_split(tm, c, 1, l);
        assert(tm_run(tm, c1, 0) == c1);
        assert(tm_run(tm, c, 1) == c1);
        assert((1 + l) as nat == (l + 1) as nat);
    }
}

} // verus!
