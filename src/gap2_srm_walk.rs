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

/// The left half-tape accumulation after `R₀^N` has walked over `words`: each word's separator (`*m`)
/// then its `l` ones is pushed onto `u` (left-fold), low-first in walk order. Mirror of `words_layout`.
pub open spec fn u_accum(u0: nat, words: Seq<nat>, m: nat) -> nat
    decreases words.len()
{
    if words.len() == 0 {
        u0
    } else {
        u_accum(pile_ones(u0 * m, words.first(), m), words.drop_first(), m)
    }
}

/// Total `R₀^N` step count: one cross + `l` walk steps per word = `Σ (lⱼ + 1)`.
pub open spec fn r0_steps(words: Seq<nat>) -> nat
    decreases words.len()
{
    if words.len() == 0 {
        0
    } else {
        (words.first() + 1 + r0_steps(words.drop_first())) as nat
    }
}

/// The quintuples `R₀^N` needs are present in `tm`, peeling the first word and shifting the state base by
/// one (matching `lemma_r0_walk`'s recursion): word 0 needs cross `(g0,0,0,g0+1,R)` and walk
/// `(g0+1,1,1,g0+1,R)`; the remaining `n-1` words use base `g0+1`. (`g0…g0+n` are the `n+1` counter
/// states; the assembler allocates them as a consecutive block.)
pub open spec fn r0_quints_present(tm: Tm, g0: nat, n: nat) -> bool
    decreases n
{
    if n == 0 {
        true
    } else {
        &&& (exists|ic: int| 0 <= ic < tm.quints.len()
                && tm.quints[ic] == mk_quint(g0, 0, 0, (g0 + 1) as nat, Dir::R))
        &&& (exists|iw: int| 0 <= iw < tm.quints.len()
                && tm.quints[iw] == mk_quint((g0 + 1) as nat, 1, 1, (g0 + 1) as nat, Dir::R))
        &&& r0_quints_present(tm, (g0 + 1) as nat, (n - 1) as nat)
    }
}

/// **`R₀^N` — proceed to the next blank to the right, `N` times (the §9 word-counter).** From the head
/// ON the leading separator (`a == 0`) in state `g0`, with `v == words_layout(words, rest, m)` (the `N`
/// unary words `A₁ 0 A₂ 0 … 0 A_N 0` above `rest`, `N == words.len()`), the counter walks past all `N`
/// separators — crossing each blank into a fresh state `g0+1, …, g0+N` and walking each word's ones via
/// brick 1 — and lands the head ON `A_N`'s trailing separator (`a == 0`, `v == rest`) in state `g0+N`,
/// with the leading separator + all `N` words piled onto `u` (`u == u_accum(c.u, words, m)`). The `N+1`
/// distinct states ARE the comma-count (a single state walks forever — the §8.2/§9 subtlety). Induction
/// on `words.len()`, composing `lemma_r0_word_step` per word via `lemma_tm_run_split`. The §9 realization
/// of `R₀^N` inside `P_N` (append-to-end). No verifier escape hatches.
pub proof fn lemma_r0_walk(tm: Tm, c: TmConfig, g0: nat, words: Seq<nat>, rest: nat)
    requires
        tm_wf(tm),
        c.a == 0,
        c.q == g0,
        c.v == words_layout(words, rest, tm.m),
        r0_quints_present(tm, g0, words.len()),
    ensures
        tm_run(tm, c, r0_steps(words))
            == (TmConfig { u: u_accum(c.u, words, tm.m), v: rest, a: 0, q: (g0 + words.len()) as nat }),
    decreases words.len(),
{
    let m = tm.m;
    if words.len() == 0 {
        // r0_steps([]) == 0; words_layout([],rest) == rest; u_accum(c.u,[]) == c.u; g0+0 == g0.
        assert(tm_run(tm, c, 0) == c);
        assert(words_layout(words, rest, m) == rest);
        assert(u_accum(c.u, words, m) == c.u);
    } else {
        let l = words.first();
        let ws = words.drop_first();
        // unfold the presence predicate (n ≥ 1) and extract the two witness indices for word 0.
        assert(r0_quints_present(tm, g0, words.len()));
        assert(exists|ic: int| 0 <= ic < tm.quints.len()
                && tm.quints[ic] == mk_quint(g0, 0, 0, (g0 + 1) as nat, Dir::R));
        assert(exists|iw: int| 0 <= iw < tm.quints.len()
                && tm.quints[iw] == mk_quint((g0 + 1) as nat, 1, 1, (g0 + 1) as nat, Dir::R));
        let ic = choose|ic: int| 0 <= ic < tm.quints.len()
                && tm.quints[ic] == mk_quint(g0, 0, 0, (g0 + 1) as nat, Dir::R);
        let iw = choose|iw: int| 0 <= iw < tm.quints.len()
                && tm.quints[iw] == mk_quint((g0 + 1) as nat, 1, 1, (g0 + 1) as nat, Dir::R);
        // v == words_layout(words,rest) == pile_ones(words_layout(ws,rest)*m, l, m): the first word + tail.
        let inner = words_layout(ws, rest, m);
        assert(c.v == pile_ones(inner * m, l, m));
        // one R₀ step over word 0.
        lemma_r0_word_step(tm, c, g0, (g0 + 1) as nat, l, inner, ic, iw);
        let c1 = (TmConfig { u: pile_ones(c.u * m, l, m), v: inner, a: 0, q: (g0 + 1) as nat });
        assert(tm_run(tm, c, (l + 1) as nat) == c1);
        // the remaining n-1 words from c1, base g0+1.
        assert(r0_quints_present(tm, (g0 + 1) as nat, (words.len() - 1) as nat));
        assert(ws.len() == words.len() - 1);
        lemma_r0_walk(tm, c1, (g0 + 1) as nat, ws, rest);
        // compose: r0_steps(words) == (l+1) + r0_steps(ws); split the run at l+1.
        assert(r0_steps(words) == (l + 1 + r0_steps(ws)) as nat);
        lemma_tm_run_split(tm, c, (l + 1) as nat, r0_steps(ws));
        // u_accum(c.u, words) == u_accum(c1.u, ws); states: (g0+1)+ws.len() == g0+words.len().
        assert(u_accum(c.u, words, m) == u_accum(c1.u, ws, m));
        assert(((g0 + 1) + ws.len()) as nat == (g0 + words.len()) as nat);
    }
}

} // verus!
