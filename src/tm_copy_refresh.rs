//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — copy-refresh foundation (seek walks).
//!
//! After a per-block loop ([`crate::tm_block_loop`]) consumes the active `temp` counter, the left tape is
//! `u == dec_u(0, m^temp·w) == m^temp·w` — the master content `w` has floated UP by `temp` cells, leaving a
//! growing blank gap between the home pivot and the master. To emit the NEXT power-block of the same phase
//! (same exponent) the machine must rebuild a fresh `temp` counter from the PRESERVED master (a copy-refresh,
//! plan §5 / the n=5 marker decision). The first ingredient is locating the master across that blank gap.
//!
//! This file builds the **seek** walks — the blank-gap analogs of [`crate::tm_dwalk`] (which walk over
//! nonzero digit blocks and stop at a blank); here the head walks over a run of blanks and stops at the
//! first NONZERO cell (the master's low digit):
//!   - [`lemma_seek_left_blanks`]: walk-LEFT over a blank gap to the master (`(q, 0, 0, q, L)`), and
//!   - [`lemma_seek_right_blanks`]: walk-RIGHT over a blank gap back to the pivot (`(q, 0, 0, q, R)`),
//!     the un-seek mirror.
//! Both are symbol-agnostic in the piled content (`v` / `u` round-trips through the seek + un-seek).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero, lemma_repunit_step};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_walk::{pile_ones, lemma_pile_ones_div_mod};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_dec_master::{dec_u, lemma_walk_left_prefix, lemma_walk_back_prefix};
use crate::tm_block_loop::lemma_dec_u_step;
use crate::tm_emit::{pile_sym, lemma_pile_sym_shift};

verus! {

/// `m^(a+b) == m^a · m^b` (the additive place-value law; induction on `b`).
pub proof fn lemma_pow_nat_add(m: nat, a: nat, b: nat)
    ensures
        pow_nat(m, (a + b) as nat) == pow_nat(m, a) * pow_nat(m, b),
    decreases b,
{
    if b == 0 {
        assert(pow_nat(m, 0) == 1);
        assert((a + 0) as nat == a);
        assert(pow_nat(m, a) * 1 == pow_nat(m, a)) by(nonlinear_arith);
    } else {
        lemma_pow_nat_add(m, a, (b - 1) as nat);   // m^(a+b-1) == m^a·m^(b-1)
        assert((a + (b - 1)) as nat == (a + b - 1) as nat);
        lemma_pow_nat_unfold(m, (a + b) as nat);   // m^(a+b) == m·m^(a+b-1)
        lemma_pow_nat_unfold(m, b);                // m^b == m·m^(b-1)
        assert(pow_nat(m, (a + b) as nat) == pow_nat(m, a) * pow_nat(m, b)) by(nonlinear_arith)
            requires
                pow_nat(m, (a + b) as nat) == m * pow_nat(m, (a + b - 1) as nat),
                pow_nat(m, (a + b - 1) as nat) == pow_nat(m, a) * pow_nat(m, (b - 1) as nat),
                pow_nat(m, b) == m * pow_nat(m, (b - 1) as nat);
    }
}

// ============================================================================
// the marked-copy invariant (closed form, drift-free)
// ============================================================================

/// **The left-tape value during the marked unary copy (STATIONARY-MASTER design, `G ≥ M`).** After `j` of
/// the master's `big_m` ones have been copied (marked `1 → 5` low-to-high), reading `u` low→high from the
/// home pivot:
///   `[temp: j ones][G − j blanks: shrinking gap][master @ position G: j fives (low) then (big_m − j) ones]`.
/// The master sits at the FIXED absolute position `G` (factor `m^G`, independent of `j`); the temp counter
/// grows at its HIGH end INTO the gap (the gap shrinks `G → G−j`), so **no `u·m+1` shift and no `v`/output
/// corruption** — every iteration is two in-place additions (mark `+4·m^(G+j)`, deposit `+m^j`). This needs
/// `G ≥ big_m` so the gap never runs out before the copy finishes (guaranteed: at every `copy_refresh` the
/// gap `G = k·i ≥ i = big_m`, the phase's shared exponent). Closed form:
///   `copy_u(j, M, G) = repunit(j) + m^G·(5·repunit(j) + m^j·repunit(M−j))`.
/// Endpoints: `copy_u(0,M,G) = m^G·repunit(M)` (the post-[`crate::tm_block_loop`] state — master at gap `G`,
/// no counter), and `copy_u(M,M,G) = repunit(M) + m^G·5·repunit(M)` (fresh temp `M` ones built at the
/// pivot, master all fives at `G`), which the un-mark pass `5 → 1` turns into `dec_u(M, m^(G−M)·repunit(M))`
/// — a fresh `M`-counter below the preserved master (`M` ones at the stationary position `G`), ready for the
/// next `block_loop`.
pub open spec fn copy_u(j: nat, big_m: nat, g: nat, m: nat) -> nat {
    repunit_m(j, m)
        + pow_nat(m, g)
            * (5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m))
}

/// The master block content at copy-step `j`: `j` fives (copied, low) then `(M − j)` ones (high), read as a
/// base-`m` value. `master_at(j, M) = 5·repunit(j) + m^j·repunit(M − j)`. The stationary master sits at the
/// fixed position `G`, so `copy_u(j, M, G) == repunit(j) + m^G·master_at(j, M)` (see [`lemma_copy_u_master`]).
pub open spec fn master_at(j: nat, big_m: nat, m: nat) -> nat {
    5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m)
}

/// `copy_u(j, M, G) == repunit(j) + m^G · master_at(j, M)` — factor the copy invariant into the temp counter
/// (`repunit(j)`) plus the stationary master block at position `G`. A definitional regrouping.
pub proof fn lemma_copy_u_master(j: nat, big_m: nat, g: nat, m: nat)
    ensures
        copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * master_at(j, big_m, m),
{
}

/// **Marking one master one shifts the master block by `+4·m^j`:** `master_at(j+1, M) == master_at(j, M)
/// + 4·m^j` (for `j < M`). The lowest unmarked one (value `1` at master-position `j`) becomes a `5` — a
/// `+4` at that place. Proven from `R(j+1)=R(j)+m^j` and `R(M−j)=m·R(M−j−1)+1` (the `5·m^j` from the new
/// five minus `m^j` from the consumed one). This is the master-side of [`lemma_copy_u_iter_arith`]'s mark.
pub proof fn lemma_master_at_step(j: nat, big_m: nat, m: nat)
    requires
        j < big_m,
    ensures
        master_at((j + 1) as nat, big_m, m) == master_at(j, big_m, m) + 4 * pow_nat(m, j),
{
    lemma_repunit_high(j, m);                          // R(j+1) == R(j) + m^j
    lemma_pow_nat_unfold(m, (j + 1) as nat);           // m^(j+1) == m·m^j
    lemma_repunit_step((big_m - j - 1) as nat, m);     // R(M−j) == m·R(M−j−1)+1
    assert(((big_m - j - 1) + 1) as nat == (big_m - j) as nat);
    assert((big_m - (j + 1)) as nat == (big_m - j - 1) as nat);
    assert(master_at((j + 1) as nat, big_m, m) == master_at(j, big_m, m) + 4 * pow_nat(m, j))
        by(nonlinear_arith)
        requires
            master_at((j + 1) as nat, big_m, m)
                == 5 * repunit_m((j + 1) as nat, m)
                    + pow_nat(m, (j + 1) as nat) * repunit_m((big_m - j - 1) as nat, m),
            master_at(j, big_m, m)
                == 5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m),
            repunit_m((j + 1) as nat, m) == repunit_m(j, m) + pow_nat(m, j),
            pow_nat(m, (j + 1) as nat) == m * pow_nat(m, j),
            repunit_m((big_m - j) as nat, m) == m * repunit_m((big_m - j - 1) as nat, m) + 1;
}

/// **Start endpoint:** `copy_u(0, M, G) == m^G · repunit(M)` — the post-`block_loop` left tape (the master's
/// `M` ones floated up by the consumed counter to gap `G`, nothing below the pivot). The input to the copy.
pub proof fn lemma_copy_u_start(big_m: nat, g: nat, m: nat)
    ensures
        copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m),
{
    lemma_repunit_zero(m);          // repunit_m(0) == 0
    assert(pow_nat(m, 0) == 1);
    // copy_u(0,M,G) = 0 + m^G·(5·0 + m^0·repunit(M)) = m^G·repunit(M).
    assert(5 * repunit_m(0, m) == 0) by(nonlinear_arith) requires repunit_m(0, m) == 0;
    assert(pow_nat(m, 0) * repunit_m((big_m - 0) as nat, m) == repunit_m(big_m, m)) by(nonlinear_arith)
        requires pow_nat(m, 0) == 1;
    assert(copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m)) by(nonlinear_arith)
        requires
            copy_u(0, big_m, g, m)
                == repunit_m(0, m) + pow_nat(m, g) * (5 * repunit_m(0, m)
                    + pow_nat(m, 0) * repunit_m(big_m, m)),
            repunit_m(0, m) == 0,
            5 * repunit_m(0, m) == 0,
            pow_nat(m, 0) * repunit_m(big_m, m) == repunit_m(big_m, m);
}

/// **End endpoint (pre-unmark):** `copy_u(M, M, G) == repunit(M) + m^G·(5·repunit(M))` — the fresh temp
/// counter (`M` ones) is built at the pivot, and the whole master block (stationary at `G`) is now `M`
/// fives (every one copied). The subsequent un-mark pass rewrites those `M` fives back to ones, yielding
/// `dec_u(M, m^(G−M)·repunit(M))` (see [`lemma_copy_u_end_unmarked`]).
pub proof fn lemma_copy_u_end(big_m: nat, g: nat, m: nat)
    ensures
        copy_u(big_m, big_m, g, m)
            == repunit_m(big_m, m) + pow_nat(m, g) * (5 * repunit_m(big_m, m)),
{
    lemma_repunit_zero(m);
    assert(pow_nat(m, big_m) * repunit_m((big_m - big_m) as nat, m) == 0) by(nonlinear_arith)
        requires repunit_m((big_m - big_m) as nat, m) == 0, (big_m - big_m) as nat == 0;
    // copy_u(M,M,G) = repunit(M) + m^G·(5·repunit(M) + m^M·repunit(0)) = repunit(M) + m^G·5·repunit(M).
    assert(copy_u(big_m, big_m, g, m)
        == repunit_m(big_m, m) + pow_nat(m, g) * (5 * repunit_m(big_m, m)))
        by(nonlinear_arith)
        requires
            copy_u(big_m, big_m, g, m)
                == repunit_m(big_m, m) + pow_nat(m, g)
                    * (5 * repunit_m(big_m, m) + pow_nat(m, big_m) * repunit_m((big_m - big_m) as nat, m)),
            pow_nat(m, big_m) * repunit_m((big_m - big_m) as nat, m) == 0;
}

/// **The un-marked end state IS a `dec_u` home config.** After the copy builds `copy_u(M,M,G)` and the
/// un-mark pass rewrites the master's `M` fives back to ones (replacing the `5·repunit(M)` factor by
/// `repunit(M)`, giving `repunit(M) + m^G·repunit(M)`), the left tape is exactly
/// `dec_u(M, m^(G−M)·repunit(M))` — a fresh `M`-counter (`repunit(M)`) below the preserved master (`M` ones
/// at the stationary position `G`, i.e. `G−M` above the new counter). Needs `G ≥ M` (the stationary-master
/// gap invariant). This pins the post-copy-refresh home config for the next `block_loop`.
pub proof fn lemma_copy_u_end_unmarked(big_m: nat, g: nat, m: nat)
    requires
        g >= big_m,
    ensures
        repunit_m(big_m, m) + pow_nat(m, g) * repunit_m(big_m, m)
            == dec_u(big_m, (pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m)) as nat, m),
{
    lemma_pow_nat_add(m, big_m, (g - big_m) as nat);   // m^(M+(G−M)) == m^M·m^(G−M)
    assert((big_m + (g - big_m)) as nat == g);
    // dec_u(M, w) = repunit(M) + m^M·w with w = m^(G−M)·repunit(M); m^M·(m^(G−M)·repunit(M)) = m^G·repunit(M).
    assert(pow_nat(m, big_m) * (pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m))
        == pow_nat(m, g) * repunit_m(big_m, m)) by(nonlinear_arith)
        requires pow_nat(m, g) == pow_nat(m, big_m) * pow_nat(m, (g - big_m) as nat);
}

/// **High-end repunit recurrence:** `repunit(j+1) == repunit(j) + m^j` (append a `1` at the TOP, the
/// complement of [`crate::tm_two_counter::lemma_repunit_step`]'s low-end `m·repunit(j)+1`). Induction on j.
pub proof fn lemma_repunit_high(j: nat, m: nat)
    ensures
        repunit_m((j + 1) as nat, m) == repunit_m(j, m) + pow_nat(m, j),
    decreases j,
{
    lemma_repunit_step(j, m);   // R(j+1) == m·R(j)+1
    if j == 0 {
        lemma_repunit_zero(m);  // R(0)==0
        assert(pow_nat(m, 0) == 1);
    } else {
        lemma_repunit_high((j - 1) as nat, m);   // R(j) == R(j-1) + P(j-1)     (f2)
        lemma_repunit_step((j - 1) as nat, m);   // R(j) == m·R(j-1)+1          (f3)
        lemma_pow_nat_unfold(m, j);              // P(j) == m·P(j-1)            (f4)
        // distribute f2 by m:  m·R(j) == m·R(j-1) + m·P(j-1).
        assert(m * repunit_m(j, m)
            == m * repunit_m((j - 1) as nat, m) + m * pow_nat(m, (j - 1) as nat)) by(nonlinear_arith)
            requires repunit_m(j, m) == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat);
        // R(j+1) = m·R(j)+1 = (m·R(j-1)+1) + m·P(j-1) = R(j) + P(j)  — linear in the named products.
        assert(repunit_m((j + 1) as nat, m) == repunit_m(j, m) + pow_nat(m, j));
    }
}

/// **The marked-copy iteration arithmetic.** For `j < big_m`, one copy iteration takes
/// `copy_u(j) → copy_u(j+1)` by exactly two in-place additions: `+4·m^(G+j)` (mark the lowest unmarked
/// master one, `1 → 5`) and `+m^j` (deposit a fresh temp one at the high-end separator):
///   `copy_u(j+1, M, G) == copy_u(j, M, G) + 4·m^(G+j) + m^j`.
/// The mark and deposit are the two physical sub-gadgets ([`lemma_deposit`] is the `+m^j`). Proven from
/// the high-end repunit recurrence (`R(j+1)=R(j)+m^j`) and the low-end one (`R(M−j)=m·R(M−j−1)+1`), which
/// collapse the `5 + m·R(M−j−1) − R(M−j) = 4` cross-term. **This pins the iteration's correctness target.**
pub proof fn lemma_copy_u_iter_arith(j: nat, big_m: nat, g: nat, m: nat)
    requires
        j < big_m,
    ensures
        copy_u((j + 1) as nat, big_m, g, m)
            == copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat) + pow_nat(m, j),
{
    lemma_repunit_high(j, m);                          // R(j+1) == R(j) + P(j)
    lemma_pow_nat_unfold(m, (j + 1) as nat);           // P(j+1) == m·P(j)
    lemma_pow_nat_add(m, g, j);                        // P(g+j) == P(g)·P(j)
    lemma_repunit_step((big_m - j - 1) as nat, m);     // R(M−j) == m·R(M−j−1)+1
    assert(((big_m - j - 1) + 1) as nat == (big_m - j) as nat);
    assert((big_m - (j + 1)) as nat == (big_m - j - 1) as nat);
    // Both sides reduce to  R(j) + P(j) + P(g)·(5·R(j) + m·P(j)·R(M−j−1)) + 5·P(g)·P(j).
    assert(copy_u((j + 1) as nat, big_m, g, m)
        == copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat) + pow_nat(m, j))
        by(nonlinear_arith)
        requires
            copy_u((j + 1) as nat, big_m, g, m)
                == repunit_m((j + 1) as nat, m) + pow_nat(m, g)
                    * (5 * repunit_m((j + 1) as nat, m)
                        + pow_nat(m, (j + 1) as nat) * repunit_m((big_m - j - 1) as nat, m)),
            copy_u(j, big_m, g, m)
                == repunit_m(j, m) + pow_nat(m, g)
                    * (5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m)),
            repunit_m((j + 1) as nat, m) == repunit_m(j, m) + pow_nat(m, j),
            pow_nat(m, (j + 1) as nat) == m * pow_nat(m, j),
            pow_nat(m, (g + j) as nat) == pow_nat(m, g) * pow_nat(m, j),
            repunit_m((big_m - j) as nat, m) == m * repunit_m((big_m - j - 1) as nat, m) + 1;
}

/// **Seek-left over a blank gap to the master.** From `{u: m^g·r, a: 0, q: q_seek}` with `r % m != 0`
/// (the target's low digit is nonzero — the master), the loop quintuple `(q_seek, 0, 0, q_seek, L)` fires
/// `g + 1` times: it peels the initial scanned blank (the pivot) plus the `g` gap blanks of `u`, piling all
/// `g + 1` blanks onto `v` (multiplying it by `m^(g+1)`), and lands the head on the master's low digit
/// `{u: r/m, v: c.v · m^(g+1), a: r % m, q: q_seek}` — where `r % m != 0` makes the loop quintuple stop
/// firing (a different `(q_seek, s, …)` quintuple then takes over). The blank-gap analog of
/// [`crate::tm_dwalk::lemma_dwalk_left`]; induction on `g`.
pub proof fn lemma_seek_left_blanks(tm: Tm, c: TmConfig, q_seek: nat, g: nat, r: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_seek, 0, 0, q_seek, Dir::L),
        c.u == pow_nat(tm.m, g) * r,
        r % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tm_run(tm, c, (g + 1) as nat)
            == (TmConfig { u: r / tm.m, v: c.v * pow_nat(tm.m, (g + 1) as nat), a: r % tm.m, q: q_seek }),
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches (q == q_seek, a == 0) and fires (L-move, a2 == 0).
    assert(quint_matches(tm.quints[i0], c));
    lemma_tm_step_picks(tm, c, i0);
    let c_next = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // L-move, a2 == 0: u' = c.u/m, v' = c.v·m + 0, a' = c.u%m.
    assert(c_next.u == c.u / m);
    assert(c_next.v == c.v * m + 0);
    assert(c_next.a == c.u % m);
    assert(c_next.q == q_seek);
    if g == 0 {
        // u == m^0·r == r; a' == r%m ≠ 0 (master), u' == r/m. Done in one step.
        assert(pow_nat(m, 0) == 1);
        assert(1nat * r == r) by(nonlinear_arith);
        assert(c.u == r);
        assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
        assert(c.v * m + 0 == c.v * pow_nat(m, 1)) by(nonlinear_arith)
            requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: r / m, v: c.v * pow_nat(m, (g + 1) as nat), a: r % m,
            q: q_seek }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == m^g·r == m·(m^(g-1)·r); a' == 0 (still in the gap), u' == m^(g-1)·r.
        let r1 = pow_nat(m, (g - 1) as nat) * r;
        lemma_pow_nat_unfold(m, g);   // m^g == m·m^(g-1)
        assert(c.u == m * r1) by(nonlinear_arith)
            requires c.u == pow_nat(m, g) * r, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                r1 == pow_nat(m, (g - 1) as nat) * r;
        assert(m * r1 == r1 * m) by(nonlinear_arith);
        lemma_div_mod_step(r1, m, 0);   // (r1·m + 0)/m == r1, %m == 0
        assert(c_next.u == r1);
        assert(c_next.a == 0);
        // recurse on g-1.
        lemma_seek_left_blanks(tm, c_next, q_seek, (g - 1) as nat, r, i0);
        // IH: tm_run(c_next, g) == (r/m, c_next.v · m^g, r%m, q_seek); chain to g+1.
        lemma_pow_nat_unfold(m, (g + 1) as nat);   // m^(g+1) == m·m^g
        assert(c_next.v * pow_nat(m, g) == c.v * pow_nat(m, (g + 1) as nat)) by(nonlinear_arith)
            requires c_next.v == c.v * m + 0, pow_nat(m, (g + 1) as nat) == m * pow_nat(m, g);
        assert(tm_run(tm, c, (g + 1) as nat) == tm_run(tm, c_next, g));
    }
}

/// **Seek-right over a blank gap (the un-seek mirror of [`lemma_seek_left_blanks`]).** The exact `u ↔ v`,
/// `L ↔ R` swap: from `{v: m^g·rv, a: 0, q: q_seek}` with `rv % m != 0` (the target's low digit on the
/// right is nonzero), the loop quintuple `(q_seek, 0, 0, q_seek, R)` fires `g + 1` times — peeling the
/// initial scanned blank plus the `g` gap blanks of `v`, piling all `g + 1` onto `u` (multiplying it by
/// `m^(g+1)`) — and lands the head on the target's low digit `{u: c.u · m^(g+1), v: rv/m, a: rv % m,
/// q: q_seek}`. Used to walk the head back right toward home after the marked copy. Induction on `g`.
pub proof fn lemma_seek_right_blanks(tm: Tm, c: TmConfig, q_seek: nat, g: nat, rv: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_seek, 0, 0, q_seek, Dir::R),
        c.v == pow_nat(tm.m, g) * rv,
        rv % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tm_run(tm, c, (g + 1) as nat)
            == (TmConfig { u: c.u * pow_nat(tm.m, (g + 1) as nat), v: rv / tm.m, a: rv % tm.m,
                q: q_seek }),
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    assert(quint_matches(tm.quints[i0], c));
    lemma_tm_step_picks(tm, c, i0);
    let c_next = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // R-move, a2 == 0: u' = c.u·m + 0, v' = c.v/m, a' = c.v%m.
    assert(c_next.u == c.u * m + 0);
    assert(c_next.v == c.v / m);
    assert(c_next.a == c.v % m);
    assert(c_next.q == q_seek);
    if g == 0 {
        assert(pow_nat(m, 0) == 1);
        assert(1nat * rv == rv) by(nonlinear_arith);
        assert(c.v == rv);
        assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
        assert(c.u * m + 0 == c.u * pow_nat(m, 1)) by(nonlinear_arith)
            requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: c.u * pow_nat(m, (g + 1) as nat), v: rv / m, a: rv % m,
            q: q_seek }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        let rv1 = pow_nat(m, (g - 1) as nat) * rv;
        lemma_pow_nat_unfold(m, g);   // m^g == m·m^(g-1)
        assert(c.v == m * rv1) by(nonlinear_arith)
            requires c.v == pow_nat(m, g) * rv, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                rv1 == pow_nat(m, (g - 1) as nat) * rv;
        assert(m * rv1 == rv1 * m) by(nonlinear_arith);
        lemma_div_mod_step(rv1, m, 0);   // (rv1·m + 0)/m == rv1, %m == 0
        assert(c_next.v == rv1);
        assert(c_next.a == 0);
        lemma_seek_right_blanks(tm, c_next, q_seek, (g - 1) as nat, rv, i0);
        lemma_pow_nat_unfold(m, (g + 1) as nat);   // m^(g+1) == m·m^g
        assert(c_next.u * pow_nat(m, g) == c.u * pow_nat(m, (g + 1) as nat)) by(nonlinear_arith)
            requires c_next.u == c.u * m + 0, pow_nat(m, (g + 1) as nat) == m * pow_nat(m, g);
        assert(tm_run(tm, c, (g + 1) as nat) == tm_run(tm, c_next, g));
    }
}

// ============================================================================
// generic single-symbol run walks (the symbol-`s` analog of walk_left_prefix)
// ============================================================================

/// **Non-destructive walk-LEFT over a homogeneous run of symbol `s`.** The symbol-`s` generalization of
/// [`crate::tm_dec_master::lemma_walk_left_prefix`] (`s = 1`): from a config in state `q_walk` scanning an
/// `s`, with `len` further `s`s and then the tail `w` packed above them
/// (`u == s·repunit(len) + m^len·w`), the loop quintuple `(q_walk, s, s, q_walk, L)` fires `len + 1` times
/// — writing each `s` back and piling it onto `v` — and lands the head on `w`'s low cell
/// (`a == w % m`, `u == w / m`), still in `q_walk`. The caller picks `w` so `w % m != s` (the next region's
/// symbol) to stop the loop. Used by the MARK seek to cross the temp ones (`s = 1`) and the master fives
/// (`s = 5`). Induction on `len`; the pile re-folds via [`crate::tm_emit::lemma_pile_sym_shift`].
pub proof fn lemma_run_walk_left(tm: Tm, c: TmConfig, q_walk: nat, s: nat, len: nat, w: nat, i1: int)
    requires
        tm_wf(tm),
        1 <= s <= tm.n,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, s, s, q_walk, Dir::L),
        c.u == s * repunit_m(len, tm.m) + pow_nat(tm.m, len) * w,
        c.a == s,
        c.q == q_walk,
    ensures
        tm_run(tm, c, (len + 1) as nat)
            == (TmConfig { u: w / tm.m, v: pile_sym(c.v, s, (len + 1) as nat, tm.m),
                a: w % tm.m, q: q_walk }),
    decreases len,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1 && s < m);   // tm_wf ⟹ 0 < n < m, and s ≤ n < m
    lemma_tm_step_picks(tm, c, i1);
    let c_next = TmConfig { u: c.u / m, v: c.v * m + s, a: c.u % m, q: q_walk };
    assert(tm_step(tm, c) == Some(c_next));
    if len == 0 {
        // u == s·repunit(0) + m^0·w == 0 + 1·w == w.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c.u == w) by(nonlinear_arith)
            requires c.u == s * repunit_m(0, m) + pow_nat(m, 0) * w, repunit_m(0, m) == 0,
                pow_nat(m, 0) == 1;
        // c_next == (w/m, pile_sym(c.v, s, 1), w%m, q_walk).
        assert(pile_sym(c.v, s, 0, m) == c.v);
        assert(pile_sym(c.v, s, 1, m) == pile_sym(c.v, s, 0, m) * m + s);
        assert(c_next == (TmConfig { u: w / m, v: pile_sym(c.v, s, 1, m), a: w % m, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == s·repunit(len) + m^len·w == (s·repunit(len-1) + m^(len-1)·w)·m + s.
        let x = s * repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        assert(repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1);   // repunit recurrence
        lemma_pow_nat_unfold(m, len);                                          // m^len == m·m^(len-1)
        assert(c.u == x * m + s) by(nonlinear_arith)
            requires
                c.u == s * repunit_m(len, m) + pow_nat(m, len) * w,
                repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1,
                pow_nat(m, len) == m * pow_nat(m, (len - 1) as nat),
                x == s * repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        lemma_div_mod_step(x, m, s);   // (x·m + s)/m == x, %m == s
        assert(c_next.u == x);
        assert(c_next.a == s);
        lemma_run_walk_left(tm, c_next, q_walk, s, (len - 1) as nat, w, i1);
        lemma_pile_sym_shift(c.v, s, len, m);   // pile_sym(c.v·m+s, s, len) == pile_sym(c.v, s, len+1)
        assert(tm_run(tm, c, (len + 1) as nat) == tm_run(tm, c_next, len));
    }
}

/// Pop one symbol off a `pile_sym`: for `k ≥ 1` (and `s < m`), `pile_sym(w, s, k) % m == s` and
/// `/ m == pile_sym(w, s, k − 1)`. The symbol-`s` analog of [`crate::tm_walk::lemma_pile_ones_div_mod`],
/// driving the [`lemma_run_walk_right`] induction.
pub proof fn lemma_pile_sym_div_mod(w: nat, s: nat, k: nat, m: nat)
    requires
        k >= 1,
        s < m,
        m > 0,
    ensures
        pile_sym(w, s, k, m) % m == s,
        pile_sym(w, s, k, m) / m == pile_sym(w, s, (k - 1) as nat, m),
{
    assert(pile_sym(w, s, k, m) == pile_sym(w, s, (k - 1) as nat, m) * m + s);
    lemma_div_mod_step(pile_sym(w, s, (k - 1) as nat, m), m, s);
}

/// **Non-destructive walk-RIGHT over a homogeneous run of symbol `s` (the mirror of [`lemma_run_walk_left`],
/// `u ↔ v`, `L ↔ R`).** The symbol-`s` generalization of [`crate::tm_dec_master::lemma_walk_back_prefix`]:
/// from a config in state `q_back` scanning an `s`, with `k0` `s`s already reconstructed atop `w_hi` in `u`
/// (`u == s·repunit(k0) + m^k0·w_hi`) and a `pile_sym` of `rem0` more `s`s above `w_pile` in `v`
/// (`v == pile_sym(w_pile, s, rem0)`), the `(q_back, s, s, q_back, R)` step fires `rem0 + 1` times — writing
/// each `s` back onto `u`'s low end (pushing `w_hi` up) and popping the pile — landing
/// `u == s·repunit(k0 + rem0 + 1) + m^(k0+rem0+1)·w_hi` with the head on `w_pile`'s low cell
/// (`a == w_pile % m`, `v == w_pile / m`). The return leg of the MARK over the fives (`s = 5`) and temp
/// (`s = 1`). Induction on `rem0`.
pub proof fn lemma_run_walk_right(
    tm: Tm, c: TmConfig, q_back: nat, s: nat, k0: nat, rem0: nat, w_pile: nat, w_hi: nat, i1b: int,
)
    requires
        tm_wf(tm),
        1 <= s <= tm.n,
        0 <= i1b < tm.quints.len(),
        tm.quints[i1b] == mk_quint(q_back, s, s, q_back, Dir::R),
        c.u == s * repunit_m(k0, tm.m) + pow_nat(tm.m, k0) * w_hi,
        c.v == pile_sym(w_pile, s, rem0, tm.m),
        c.a == s,
        c.q == q_back,
    ensures
        tm_run(tm, c, (rem0 + 1) as nat)
            == (TmConfig {
                u: s * repunit_m((k0 + rem0 + 1) as nat, tm.m)
                    + pow_nat(tm.m, (k0 + rem0 + 1) as nat) * w_hi,
                v: w_pile / tm.m, a: w_pile % tm.m, q: q_back }),
    decreases rem0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1 && s < m);
    lemma_tm_step_picks(tm, c, i1b);
    let c_next = TmConfig { u: c.u * m + s, v: c.v / m, a: c.v % m, q: q_back };
    assert(tm_step(tm, c) == Some(c_next));
    // c_next.u == s·repunit(k0+1) + m^(k0+1)·w_hi.
    let nk = (k0 + 1) as nat;
    assert(repunit_m(nk, m) == m * repunit_m(k0, m) + 1);   // repunit recurrence
    lemma_pow_nat_unfold(m, nk);                            // m^(k0+1) == m·m^k0
    assert(c_next.u == s * repunit_m(nk, m) + pow_nat(m, nk) * w_hi) by(nonlinear_arith)
        requires
            c.u == s * repunit_m(k0, m) + pow_nat(m, k0) * w_hi,
            c_next.u == c.u * m + s,
            repunit_m(nk, m) == m * repunit_m(k0, m) + 1,
            pow_nat(m, nk) == m * pow_nat(m, k0);
    if rem0 == 0 {
        // c.v == pile_sym(w_pile, s, 0) == w_pile.
        assert(pile_sym(w_pile, s, 0, m) == w_pile);
        assert((k0 + 0 + 1) as nat == nk);
        assert(c_next == (TmConfig {
            u: s * repunit_m(nk, m) + pow_nat(m, nk) * w_hi, v: w_pile / m, a: w_pile % m, q: q_back }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // pop a pile-s: c.v % m == s, c.v / m == pile_sym(w_pile, s, rem0-1).
        lemma_pile_sym_div_mod(w_pile, s, rem0, m);
        assert(c_next.a == s);
        assert(c_next.v == pile_sym(w_pile, s, (rem0 - 1) as nat, m));
        lemma_run_walk_right(tm, c_next, q_back, s, nk, (rem0 - 1) as nat, w_pile, w_hi, i1b);
        assert(((k0 + 1) + (rem0 - 1) + 1) as nat == (k0 + rem0 + 1) as nat);
        assert(tm_run(tm, c, (rem0 + 1) as nat) == tm_run(tm, c_next, rem0));
    }
}

// ============================================================================
// the MARK gadget — seek to the lowest unmarked master one, mark 1→5, return
// ============================================================================

/// **Forward seek of the MARK (general case `2 ≤ j < M`, gap `g − j ≥ 2`).** From the home config
/// `{u: copy_u(j), v: out, a: 0, q: q_mh}`, walk left over temp (`j` ones, state `q_t`), the gap
/// (`g − j` blanks, state `q_a` — note temp and the master fives/ones are blank-separated from the gap),
/// and the master fives (`j` fives, also `q_a`), landing the head on the LOWEST unmarked master one
/// (`a == 1`, `u == repunit(M − j − 1)`) in state `q_a`, where the caller's mark quintuple
/// `(q_a, 1, 5, …)` then fires. The output `v` is piled up region-by-region into
/// `pile_sym(pile_sym(out·m, 1, j)·m^(g−j), 5, j)` (temp ones, then `g − j` gap blanks, then the fives);
/// the return leg ([`lemma_mark_ret`]) pops it back. Total `g + j + 1` steps. Five quintuples: pivot-peel,
/// temp-walk (`q_t`), temp→gap transition `(q_t, 0, 0, q_a, L)`, gap-walk + fives-walk (`q_a`).
pub proof fn lemma_mark_fwd(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_fives: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        g >= j + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_fives] == mk_quint(q_a, 5, 5, q_a, Dir::L),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (g + j + 1) as nat)
            == (TmConfig {
                u: repunit_m((big_m - j - 1) as nat, tm.m),
                v: pile_sym(
                    pile_sym(out * tm.m, 1, j, tm.m) * pow_nat(tm.m, (g - j) as nat), 5, j, tm.m),
                a: 1, q: q_a }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);   // tm_wf ⟹ 0 < n < m, n ≥ 5
    let ms = master_at(j, big_m, m);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j) + m^g·ms
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── S1: pivot-peel (q_mh, 0, 0, q_t, L). copy_u(j)%m==1, /m == R(j-1) + m^(g-1)·ms. ──
    lemma_repunit_step((j - 1) as nat, m);   // R(j) == m·R(j-1)+1
    lemma_pow_nat_unfold(m, g);              // m^g == m·m^(g-1)
    let u1 = repunit_m((j - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * ms;
    assert(copy_u(j, big_m, g, m) == u1 * m + 1) by(nonlinear_arith)
        requires
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * ms,
            repunit_m(j, m) == m * repunit_m((j - 1) as nat, m) + 1,
            pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == repunit_m((j - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * ms;
    lemma_div_mod_step(u1, m, 1);   // (u1·m+1)/m == u1, %m == 1
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_t);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);

    // ── S2: walk-left over temp (j steps), q_t. c1.u == 1·R(j-1) + m^(j-1)·(m^(g-j)·ms). ──
    let w_a = pow_nat(m, (g - j) as nat) * ms;
    lemma_pow_nat_add(m, (j - 1) as nat, (g - j) as nat);   // m^(j-1)·m^(g-j) == m^((j-1)+(g-j))
    assert(((j - 1) + (g - j)) as nat == (g - 1) as nat);
    assert(c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a) by(nonlinear_arith)
        requires
            c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * ms,
            pow_nat(m, (g - 1) as nat) == pow_nat(m, (j - 1) as nat) * pow_nat(m, (g - j) as nat),
            w_a == pow_nat(m, (g - j) as nat) * ms;
    lemma_run_walk_left(tm, c1, q_t, 1, (j - 1) as nat, w_a, i_temp);
    // w_a % m == 0 (g-j ≥ 2 ≥ 1), w_a / m == m^(g-j-1)·ms.
    lemma_pow_nat_unfold(m, (g - j) as nat);   // m^(g-j) == m·m^(g-j-1)
    assert(w_a == (pow_nat(m, (g - j - 1) as nat) * ms) * m) by(nonlinear_arith)
        requires w_a == pow_nat(m, (g - j) as nat) * ms,
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 1) as nat) * ms, m, 0);   // (X·m+0)/m==X, %m==0
    let pile_temp = pile_sym(out * m, 1, j, m);
    let c2 = TmConfig { u: pow_nat(m, (g - j - 1) as nat) * ms, v: pile_temp, a: 0, q: q_t };
    assert(((j - 1) + 1) as nat == j);
    assert(tm_run(tm, c1, j) == c2);
    lemma_tm_run_split(tm, c0, 1, j);
    assert(tm_run(tm, c0, (1 + j) as nat) == c2);

    // ── S3: temp→gap transition (q_t, 0, 0, q_a, L). c2.u%m==0 (g-j-1≥1), /m == m^(g-j-2)·ms. ──
    lemma_pow_nat_unfold(m, (g - j - 1) as nat);   // m^(g-j-1) == m·m^(g-j-2)
    assert(c2.u == (pow_nat(m, (g - j - 2) as nat) * ms) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - j - 1) as nat) * ms,
            pow_nat(m, (g - j - 1) as nat) == m * pow_nat(m, (g - j - 2) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 2) as nat) * ms, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - j - 2) as nat) * ms && c3.v == pile_temp * m && c3.a == 0
        && c3.q == q_a);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, (1 + j) as nat, 1);
    assert(tm_run(tm, c0, (1 + j + 1) as nat) == c3);

    // ── S4: seek-left over the remaining gap (g-j-1 steps), q_a. c3.u == m^(g-j-2)·ms, ms%m==5. ──
    // ms == 5·R(j) + m^j·R(M-j) == 5 + m·(5·R(j-1) + m^(j-1)·R(M-j)).
    lemma_pow_nat_unfold(m, j);   // m^j == m·m^(j-1)
    let ms_div = 5 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m);
    assert(ms == ms_div * m + 5) by(nonlinear_arith)
        requires
            ms == 5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m),
            repunit_m(j, m) == m * repunit_m((j - 1) as nat, m) + 1,
            pow_nat(m, j) == m * pow_nat(m, (j - 1) as nat),
            ms_div == 5 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m);
    lemma_div_mod_step(ms_div, m, 5);   // ms%m==5, ms/m==ms_div
    lemma_seek_left_blanks(tm, c3, q_a, (g - j - 2) as nat, ms, i_gap);
    lemma_pow_nat_unfold(m, (g - j) as nat);   // for v: pile_temp·m·m^(g-j-1) == pile_temp·m^(g-j)
    let c4 = TmConfig { u: ms_div, v: (pile_temp * m) * pow_nat(m, (g - j - 1) as nat), a: 5, q: q_a };
    assert(((g - j - 2) + 1) as nat == (g - j - 1) as nat);
    assert(tm_run(tm, c3, (g - j - 1) as nat) == c4);
    lemma_tm_run_split(tm, c0, (1 + j + 1) as nat, (g - j - 1) as nat);
    assert((1 + j + 1 + (g - j - 1)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c4);
    // c4.v == pile_temp · m^(g-j).
    assert((pile_temp * m) * pow_nat(m, (g - j - 1) as nat) == pile_temp * pow_nat(m, (g - j) as nat))
        by(nonlinear_arith)
        requires pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    let big_v = pile_temp * pow_nat(m, (g - j) as nat);
    assert(c4.v == big_v);

    // ── S5: walk-left over the master fives (j steps), q_a. c4.u == 5·R(j-1) + m^(j-1)·R(M-j). ──
    lemma_run_walk_left(tm, c4, q_a, 5, (j - 1) as nat, repunit_m((big_m - j) as nat, m), i_fives);
    // R(M-j) % m == 1, / m == R(M-j-1)  (M-j ≥ 1).
    lemma_repunit_step((big_m - j - 1) as nat, m);   // R(M-j) == m·R(M-j-1)+1
    assert(((big_m - j - 1) + 1) as nat == (big_m - j) as nat);
    assert(repunit_m((big_m - j) as nat, m) == repunit_m((big_m - j - 1) as nat, m) * m + 1)
        by(nonlinear_arith)
        requires repunit_m((big_m - j) as nat, m) == m * repunit_m((big_m - j - 1) as nat, m) + 1;
    lemma_div_mod_step(repunit_m((big_m - j - 1) as nat, m), m, 1);
    let c5 = TmConfig {
        u: repunit_m((big_m - j - 1) as nat, m), v: pile_sym(big_v, 5, j, m), a: 1, q: q_a };
    assert(((j - 1) + 1) as nat == j);
    assert(tm_run(tm, c4, j) == c5);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, j);
    assert((g + 1 + j) as nat == (g + j + 1) as nat);
    assert(tm_run(tm, c0, (g + j + 1) as nat) == c5);
}

/// **The MARK gadget (general case `2 ≤ j < M`, gap `g − j ≥ 2`).** From the home config
/// `{u: copy_u(j), v: out, a: 0, q: q_mh}`, seek to the lowest unmarked master one ([`lemma_mark_fwd`]),
/// flip it `1 → 5` (`(q_a, 1, 5, q_rf, R)`), and walk back to the home pivot reversing the forward piling
/// — fives back (`q_rf`, [`lemma_run_walk_right`]), rf→gap transition, gap back (`q_rg`,
/// [`lemma_seek_right_blanks`]), rg→temp transition, temp back (`q_rt`). Net: `u` gains exactly
/// `4·m^(g+j)` (the mark, via [`lemma_master_at_step`]), the output `v` is restored, head back on the pivot
/// (`a == 0`) in `q_rt`. Total `2·(g + j + 1)` steps. Eleven quintuples. The companion [`lemma_deposit`]
/// then adds the `+m^j` to complete one [`lemma_copy_u_iter_arith`] step.
pub proof fn lemma_mark(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_rf: nat, q_rg: nat, q_rt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        g >= j + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_fives] == mk_quint(q_a, 5, 5, q_a, Dir::L),
        tm.quints[i_mark] == mk_quint(q_a, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1)) as nat)
            == (TmConfig {
                u: (copy_u(j, big_m, g, tm.m) + 4 * pow_nat(tm.m, (g + j) as nat)) as nat,
                v: out, a: 0, q: q_rt }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let pile_temp = pile_sym(out * m, 1, j, m);
    let big_v = pile_temp * pow_nat(m, (g - j) as nat);
    let mm1 = repunit_m((big_m - j - 1) as nat, m);   // R(M−j−1)
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── FORWARD: c0 → c5 (the lowest unmarked one), g+j+1 steps. ──
    lemma_mark_fwd(tm, j, big_m, g, out, q_mh, q_t, q_a, i_peel, i_temp, i_t2g, i_gap, i_fives);
    let c5 = TmConfig { u: mm1, v: pile_sym(big_v, 5, j, m), a: 1, q: q_a };
    assert(tm_run(tm, c0, (g + j + 1) as nat) == c5);

    // ── MARK step (q_a, 1, 5, q_rf, R). v pops the top five, u gains the marked 5. ──
    lemma_pile_sym_div_mod(big_v, 5, j, m);   // pile_sym(big_v,5,j)%m==5, /m==pile_sym(big_v,5,j-1)
    lemma_tm_step_picks(tm, c5, i_mark);
    let c6 = apply_quint(tm.quints[i_mark], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == mm1 * m + 5 && c6.v == pile_sym(big_v, 5, (j - 1) as nat, m) && c6.a == 5
        && c6.q == q_rf);
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (g + j + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + j + 2) as nat) == c6);

    // ── S6: run_walk_right over the fives (j steps). c6.u == 5·R(1)+m·R(M−j−1). ──
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(c6.u == 5 * repunit_m(1, m) + pow_nat(m, 1) * mm1) by(nonlinear_arith)
        requires c6.u == mm1 * m + 5, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c6, q_rf, 5, 1, (j - 1) as nat, big_v, mm1, i_rfives);
    assert((1 + (j - 1) + 1) as nat == (j + 1) as nat);
    assert((big_m - (j + 1)) as nat == (big_m - j - 1) as nat);
    assert(ms_next == 5 * repunit_m((j + 1) as nat, m) + pow_nat(m, (j + 1) as nat) * mm1);
    // big_v % m == 0, / m == pile_temp·m^(g-j-1).
    lemma_pow_nat_unfold(m, (g - j) as nat);   // m^(g-j) == m·m^(g-j-1)
    assert(big_v == (pile_temp * pow_nat(m, (g - j - 1) as nat)) * m) by(nonlinear_arith)
        requires big_v == pile_temp * pow_nat(m, (g - j) as nat),
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - j - 1) as nat), m, 0);
    let c7 = TmConfig { u: ms_next, v: pile_temp * pow_nat(m, (g - j - 1) as nat), a: 0, q: q_rf };
    assert(tm_run(tm, c6, j) == c7);
    lemma_tm_run_split(tm, c0, (g + j + 2) as nat, j);
    assert((g + j + 2 + j) as nat == (g + 2 * j + 2) as nat);
    assert(tm_run(tm, c0, (g + 2 * j + 2) as nat) == c7);

    // ── S7: rf→gap transition (q_rf, 0, 0, q_rg, R). ──
    lemma_pow_nat_unfold(m, (g - j - 1) as nat);   // m^(g-j-1) == m·m^(g-j-2)
    assert(c7.v == (pile_temp * pow_nat(m, (g - j - 2) as nat)) * m) by(nonlinear_arith)
        requires c7.v == pile_temp * pow_nat(m, (g - j - 1) as nat),
            pow_nat(m, (g - j - 1) as nat) == m * pow_nat(m, (g - j - 2) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - j - 2) as nat), m, 0);
    lemma_tm_step_picks(tm, c7, i_rf2g);
    let c8 = apply_quint(tm.quints[i_rf2g], c7, m);
    assert(tm_step(tm, c7) == Some(c8));
    assert(c8.u == ms_next * m && c8.v == pile_temp * pow_nat(m, (g - j - 2) as nat) && c8.a == 0
        && c8.q == q_rg);
    assert(tm_run(tm, c8, 0) == c8);
    assert(tm_run(tm, c7, 1) == c8);
    lemma_tm_run_split(tm, c0, (g + 2 * j + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 2 * j + 3) as nat) == c8);

    // ── S8: seek_right_blanks over the gap (g-j-1 steps). rv = pile_temp, rv%m == 1 (j≥1). ──
    lemma_pile_sym_div_mod(out * m, 1, j, m);   // pile_temp%m==1, /m==pile_sym(out·m,1,j-1)
    assert(c8.v == pow_nat(m, (g - j - 2) as nat) * pile_temp) by(nonlinear_arith)
        requires c8.v == pile_temp * pow_nat(m, (g - j - 2) as nat);
    lemma_seek_right_blanks(tm, c8, q_rg, (g - j - 2) as nat, pile_temp, i_rgap);
    let c9 = TmConfig { u: c8.u * pow_nat(m, (g - j - 1) as nat),
        v: pile_sym(out * m, 1, (j - 1) as nat, m), a: 1, q: q_rg };
    assert(((g - j - 2) + 1) as nat == (g - j - 1) as nat);
    assert(tm_run(tm, c8, (g - j - 1) as nat) == c9);
    lemma_tm_run_split(tm, c0, (g + 2 * j + 3) as nat, (g - j - 1) as nat);
    assert((g + 2 * j + 3 + (g - j - 1)) as nat == (2 * g + j + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + j + 2) as nat) == c9);
    // c9.u == ms_next·m^(g-j).
    assert(c9.u == ms_next * pow_nat(m, (g - j) as nat)) by(nonlinear_arith)
        requires c9.u == (ms_next * m) * pow_nat(m, (g - j - 1) as nat),
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);

    // ── S9: rg→temp transition (q_rg, 1, 1, q_rt, R). j≥2 ⟹ pile_sym(out·m,1,j-1)%m==1. ──
    lemma_pile_sym_div_mod(out * m, 1, (j - 1) as nat, m);
    lemma_tm_step_picks(tm, c9, i_rg2t);
    let c10 = apply_quint(tm.quints[i_rg2t], c9, m);
    assert(tm_step(tm, c9) == Some(c10));
    assert(c10.u == c9.u * m + 1 && c10.v == pile_sym(out * m, 1, (j - 2) as nat, m) && c10.a == 1
        && c10.q == q_rt);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c9, 1) == c10);
    lemma_tm_run_split(tm, c0, (2 * g + j + 2) as nat, 1);
    assert(tm_run(tm, c0, (2 * g + j + 3) as nat) == c10);

    // ── S10: run_walk_right over temp (j-1 steps). c10.u == 1·R(1)+m·c9.u. ──
    assert(c10.u == 1 * repunit_m(1, m) + pow_nat(m, 1) * c9.u) by(nonlinear_arith)
        requires c10.u == c9.u * m + 1, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c10, q_rt, 1, 1, (j - 2) as nat, out * m, c9.u, i_rtemp);
    assert((1 + (j - 2) + 1) as nat == j);
    lemma_div_mod_step(out, m, 0);   // (out·m)/m==out, %m==0
    let c11 = TmConfig { u: repunit_m(j, m) + pow_nat(m, j) * c9.u, v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c10, (j - 1) as nat) == c11);
    lemma_tm_run_split(tm, c0, (2 * g + j + 3) as nat, (j - 1) as nat);
    assert((2 * g + j + 3 + (j - 1)) as nat == (2 * (g + j + 1)) as nat);
    assert(tm_run(tm, c0, (2 * (g + j + 1)) as nat) == c11);

    // ── c11.u == copy_u(j) + 4·m^(g+j). ──
    // c11.u = R(j) + m^j·c9.u = R(j) + m^j·(ms_next·m^(g-j)) = R(j) + m^g·ms_next.
    lemma_pow_nat_add(m, j, (g - j) as nat);   // m^g == m^j·m^(g-j)
    assert((j + (g - j)) as nat == g);
    assert(pow_nat(m, j) * c9.u == pow_nat(m, g) * ms_next) by(nonlinear_arith)
        requires c9.u == ms_next * pow_nat(m, (g - j) as nat),
            pow_nat(m, g) == pow_nat(m, j) * pow_nat(m, (g - j) as nat);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j)+m^g·master_at(j,M)
    lemma_master_at_step(j, big_m, m);     // ms_next == master_at(j,M)+4·m^j
    lemma_pow_nat_add(m, g, j);            // m^(g+j) == m^g·m^j
    assert(c11.u == (copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat)) as nat) by(nonlinear_arith)
        requires
            c11.u == repunit_m(j, m) + pow_nat(m, g) * ms_next,
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * master_at(j, big_m, m),
            ms_next == master_at(j, big_m, m) + 4 * pow_nat(m, j),
            pow_nat(m, (g + j) as nat) == pow_nat(m, g) * pow_nat(m, j);
}

// ============================================================================
// the deposit (high-end temp grow) — the dec_temp MIRROR (insert, not discard)
// ============================================================================

/// **The `deposit` gadget — grow the temp counter by ONE at its HIGH end (the temp/master separator),
/// returning to the home pivot.** The stationary-master copy-refresh deposit (plan §5 / N+5 mechanics note):
/// the home layout is `[temp: j ones][separator blank][gap…][master @ G]…` with the head on the pivot `0`
/// before the temp counter. Four quintuples — the MIRROR of [`crate::tm_dec_master::lemma_dec_temp`], with
/// the erase+discard replaced by a single INSERT-turnaround that writes a fresh `1` at the separator blank:
///   `(q_dh, 0, 0, q_dw, L)`  peel the pivot (push it onto v, expose temp's inner one),
///   `(q_dw, 1, 1, q_dw, L)`  walk left over temp's ones to the temp/master separator blank,
///   `(q_dw, 0, 1, q_bk, R)`  INSERT-turnaround: write a `1` at the separator (was `0`), grow temp,
///   `(q_bk, 1, 1, q_bk, R)`  walk back, reconstructing temp+1 (the high content `w` shifts DOWN one).
/// From `{u: dec_u(j, w), v: out, a: 0, q_dh}` (`w % m == 0`, the separator is a blank), `2·j + 2` steps
/// reach `{u: dec_u(j, w) + m^j, v: out, a: 0, q_bk}` — temp grown to `j + 1` ones at the high end (so the
/// gap above shrinks by one), the output `v` round-tripped (pushed onto the pile, restored). Composes
/// [`crate::tm_dec_master::lemma_walk_left_prefix`] + [`crate::tm_dec_master::lemma_walk_back_prefix`].
pub proof fn lemma_deposit(
    tm: Tm, j: nat, w: nat, out: nat,
    q_dh: nat, q_dw: nat, q_bk: nat,
    i_pivot: int, i_one_l: int, i_ins: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        w % tm.m == 0,
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_ins < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot] == mk_quint(q_dh, 0, 0, q_dw, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_ins] == mk_quint(q_dw, 0, 1, q_bk, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_bk, 1, 1, q_bk, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: dec_u(j, w, tm.m), v: out, a: 0, q: q_dh },
            (2 * j + 2) as nat)
            == (TmConfig { u: (dec_u(j, w, tm.m) + pow_nat(tm.m, j)) as nat, v: out, a: 0, q: q_bk }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);   // tm_wf ⟹ 0 < n < m, n ≥ 2
    let c0 = TmConfig { u: dec_u(j, w, m), v: out, a: 0, q: q_dh };
    let v1 = out * m;   // the output with the pivot 0 pushed on top
    lemma_div_mod_step(out, m, 0);   // v1/m == out, v1%m == 0
    assert(out * m + 0 == v1);

    // w == (w/m)·m  (w%m == 0).
    lemma_fundamental_div_mod(w as int, m as int);
    assert(w == m * (w / m)) by { assert(w % m == 0); }
    assert(m * (w / m) == w);

    // ── Step 1: peel the pivot (q_dh, 0, 0, q_dw, L). ──
    // dec_u(j,w) % m == 0 when j==0 (== w, w%m==0), == 1 when j>=1; we want the head on temp's low one
    // (j>=1) or directly on the separator (j==0). Compute u0/m and u0%m uniformly.
    lemma_tm_step_picks(tm, c0, i_pivot);
    let c_peel = apply_quint(tm.quints[i_pivot], c0, m);
    assert(tm_step(tm, c0) == Some(c_peel));
    assert(c_peel.v == v1);
    assert(c_peel.q == q_dw);
    assert(tm_run(tm, c_peel, 0) == c_peel);
    assert(tm_run(tm, c0, 1) == c_peel);

    if j == 0 {
        // u0 == dec_u(0,w) == w; head onto the separator (a == w%m == 0), u == w/m.
        assert(dec_u(0, w, m) == w) by { lemma_repunit_zero(m); assert(pow_nat(m, 0) == 1); }
        assert(c_peel.u == w / m);
        assert(c_peel.a == 0);   // w % m == 0
        // ── Step 2 (j==0): INSERT directly (q_dw, 0, 1, q_bk, R). ──
        lemma_tm_step_picks(tm, c_peel, i_ins);
        let c_ins = apply_quint(tm.quints[i_ins], c_peel, m);
        assert(tm_step(tm, c_peel) == Some(c_ins));
        // R-move, a2 == 1: u = (w/m)·m + 1 == w + 1, v = v1/m == out, a = v1%m == 0.
        assert(c_ins.u == (w / m) * m + 1);
        assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == w;
        assert(c_ins.u == w + 1);
        assert(c_ins.v == out);
        assert(c_ins.a == 0);
        assert(c_ins.q == q_bk);
        // dec_u(0,w) + m^0 == w + 1.
        assert(pow_nat(m, 0) == 1);
        assert((dec_u(0, w, m) + pow_nat(m, 0)) as nat == w + 1) by { assert(dec_u(0, w, m) == w); }
        assert(c_ins == (TmConfig { u: (dec_u(0, w, m) + pow_nat(m, 0)) as nat, v: out, a: 0, q: q_bk }));
        assert(tm_run(tm, c_ins, 0) == c_ins);
        assert(tm_run(tm, c_peel, 1) == c_ins);
        lemma_tm_run_split(tm, c0, 1, 1);
        assert((2 * j + 2) as nat == 2);
        assert(tm_run(tm, c0, 2) == c_ins);
    } else {
        // u0 == dec_u(j,w), j>=1: %m==1, /m==dec_u(j-1,w). Head onto temp's low one (a==1).
        lemma_dec_u_step(j, w, m);   // dec_u(j,w)%m==1, /m==dec_u(j-1,w)
        assert(c_peel.u == dec_u((j - 1) as nat, w, m));
        assert(c_peel.a == 1);

        // ── Step 2: walk-left over temp's ones (j steps) to the separator. ──
        // dec_u(j-1,w) == repunit(j-1) + m^(j-1)·w (matches lemma_walk_left_prefix's shape).
        lemma_walk_left_prefix(tm, c_peel, q_dw, (j - 1) as nat, w, i_one_l);
        let c_sep = TmConfig { u: w / m, v: pile_ones(v1, j, m), a: w % m, q: q_dw };
        assert(((j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_peel, j) == c_sep);
        lemma_tm_run_split(tm, c0, 1, j);
        assert(tm_run(tm, c0, (1 + j) as nat) == c_sep);

        // ── Step 3: INSERT-turnaround at the separator (a == w%m == 0). ──
        assert(c_sep.a == 0);   // w % m == 0
        lemma_tm_step_picks(tm, c_sep, i_ins);
        let c_ins = apply_quint(tm.quints[i_ins], c_sep, m);
        assert(tm_step(tm, c_sep) == Some(c_ins));
        lemma_pile_ones_div_mod(v1, j, m);   // pile_ones(v1,j)%m==1, /m==pile_ones(v1,j-1)
        // R-move, a2 == 1: u = (w/m)·m + 1 == w + 1, v = pile_ones(v1,j)/m, a = pile_ones(v1,j)%m == 1.
        assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == w;
        assert(c_ins.u == w + 1);
        assert(c_ins.v == pile_ones(v1, (j - 1) as nat, m));
        assert(c_ins.a == 1);
        assert(c_ins.q == q_bk);
        assert(tm_run(tm, c_ins, 0) == c_ins);
        assert(tm_run(tm, c_sep, 1) == c_ins);
        lemma_tm_run_split(tm, c0, (1 + j) as nat, 1);
        assert(tm_run(tm, c0, (1 + j + 1) as nat) == c_ins);

        // ── Step 4: walk-back (j steps): k0=0, rem0=j-1, w_hi = w+1. u == w+1 == repunit(0)+m^0·(w+1). ──
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c_ins.u == repunit_m(0, m) + pow_nat(m, 0) * (w + 1)) by(nonlinear_arith)
            requires c_ins.u == w + 1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_walk_back_prefix(tm, c_ins, q_bk, 0, (j - 1) as nat, v1, (w + 1) as nat, i_one_r);
        let c_final = TmConfig {
            u: repunit_m(j, m) + pow_nat(m, j) * (w + 1),
            v: v1 / m, a: v1 % m, q: q_bk };
        assert((0 + (j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_ins, j) == c_final);
        // c_final.u == repunit(j) + m^j·(w+1) == dec_u(j,w) + m^j.
        assert(c_final.u == (dec_u(j, w, m) + pow_nat(m, j)) as nat) by(nonlinear_arith)
            requires
                c_final.u == repunit_m(j, m) + pow_nat(m, j) * (w + 1),
                dec_u(j, w, m) == repunit_m(j, m) + pow_nat(m, j) * w;
        assert(c_final.v == out);   // v1 / m
        assert(c_final.a == 0);     // v1 % m
        assert(c_final == (TmConfig { u: (dec_u(j, w, m) + pow_nat(m, j)) as nat, v: out, a: 0,
            q: q_bk }));
        lemma_tm_run_split(tm, c0, (1 + j + 1) as nat, j);
        assert((1 + j + 1 + j) as nat == (2 * j + 2) as nat);
        assert(tm_run(tm, c0, (2 * j + 2) as nat) == c_final);
    }
}

// ============================================================================
// one marked-copy iteration: copy_u(j) → copy_u(j+1)  (mark ∘ deposit)
// ============================================================================

/// **One marked-copy iteration (general case `2 ≤ j < M`, gap `g − j ≥ 2`).** Composes the MARK
/// ([`lemma_mark`], `+4·m^(g+j)`) and the DEPOSIT ([`lemma_deposit`], `+m^j`) — wired by reusing the mark's
/// exit state `q_rt` as the deposit's home state (the deposit's pivot-peel `(q_rt, 0, 0, q_dw, L)` and the
/// mark's temp-return `(q_rt, 1, 1, q_rt, R)` are disambiguated by the scanned symbol). From
/// `{u: copy_u(j), v: out, a: 0, q: q_mh}`, after `2·(g+j+1) + (2·j+2)` steps the left tape is
/// `copy_u(j+1)` (one more master one marked `1 → 5`, one more temp one), output `v` preserved, head on the
/// pivot in `q_bk`. The arithmetic closes via [`lemma_copy_u_iter_arith`].
pub proof fn lemma_copy_iter(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat, q_bk: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        g >= j + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_fives] == mk_quint(q_a, 5, 5, q_a, Dir::L),
        tm.quints[i_mark] == mk_quint(q_a, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
        tm.quints[i_dpeel] == mk_quint(q_rt, 0, 0, q_dw, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw, 0, 1, q_bk, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk, 1, 1, q_bk, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1) + (2 * j + 2)) as nat)
            == (TmConfig { u: copy_u((j + 1) as nat, big_m, g, tm.m), v: out, a: 0, q: q_bk }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);   // tm_wf ⟹ 0 < n < m, n ≥ 5
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let w_dep = pow_nat(m, (g - j) as nat) * ms_next;

    // ── MARK: c0 → c_mid, where c_mid.u == copy_u(j)+4·m^(g+j) == dec_u(j, w_dep). ──
    lemma_mark(tm, j, big_m, g, out, q_mh, q_t, q_a, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j) + m^g·master_at(j,M)
    lemma_master_at_step(j, big_m, m);     // ms_next == master_at(j,M) + 4·m^j
    lemma_pow_nat_add(m, g, j);            // m^(g+j) == m^g·m^j
    lemma_pow_nat_add(m, j, (g - j) as nat);   // m^g == m^j·m^(g-j)
    assert((j + (g - j)) as nat == g);
    // copy_u(j)+4·m^(g+j) == R(j) + m^g·ms_next == R(j) + m^j·w_dep == dec_u(j, w_dep).
    assert(copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat) == dec_u(j, w_dep, m))
        by(nonlinear_arith)
        requires
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * master_at(j, big_m, m),
            ms_next == master_at(j, big_m, m) + 4 * pow_nat(m, j),
            pow_nat(m, (g + j) as nat) == pow_nat(m, g) * pow_nat(m, j),
            pow_nat(m, g) == pow_nat(m, j) * pow_nat(m, (g - j) as nat),
            w_dep == pow_nat(m, (g - j) as nat) * ms_next,
            dec_u(j, w_dep, m) == repunit_m(j, m) + pow_nat(m, j) * w_dep;
    let c_mid = TmConfig { u: dec_u(j, w_dep, m), v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c0, (2 * (g + j + 1)) as nat) == c_mid);

    // ── DEPOSIT (home state q_rt): c_mid → c_end, u += m^j. w_dep % m == 0 (g-j ≥ 2). ──
    lemma_pow_nat_unfold(m, (g - j) as nat);   // m^(g-j) == m·m^(g-j-1)
    assert(w_dep == (pow_nat(m, (g - j - 1) as nat) * ms_next) * m) by(nonlinear_arith)
        requires w_dep == pow_nat(m, (g - j) as nat) * ms_next,
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 1) as nat) * ms_next, m, 0);
    assert(w_dep % m == 0);
    lemma_deposit(tm, j, w_dep, out, q_rt, q_dw, q_bk, i_dpeel, i_dtemp, i_dins, i_dwb);
    let c_end = TmConfig { u: (dec_u(j, w_dep, m) + pow_nat(m, j)) as nat, v: out, a: 0, q: q_bk };
    assert(tm_run(tm, c_mid, (2 * j + 2) as nat) == c_end);

    // ── c_end.u == copy_u(j+1) via the iteration arithmetic. ──
    lemma_copy_u_iter_arith(j, big_m, g, m);   // copy_u(j+1) == copy_u(j)+4·m^(g+j)+m^j
    assert(c_end.u == copy_u((j + 1) as nat, big_m, g, m)) by(nonlinear_arith)
        requires
            c_end.u == dec_u(j, w_dep, m) + pow_nat(m, j),
            dec_u(j, w_dep, m) == copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat),
            copy_u((j + 1) as nat, big_m, g, m)
                == copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat) + pow_nat(m, j);
    assert(c_end == (TmConfig { u: copy_u((j + 1) as nat, big_m, g, m), v: out, a: 0, q: q_bk }));

    // ── chain MARK ∘ DEPOSIT. ──
    lemma_tm_run_split(tm, c0, (2 * (g + j + 1)) as nat, (2 * j + 2) as nat);
    assert((2 * (g + j + 1) + (2 * j + 2)) as nat == (2 * (g + j + 1)) as nat + (2 * j + 2) as nat);
    assert(tm_run(tm, c0, (2 * (g + j + 1) + (2 * j + 2)) as nat) == c_end);
}

// ============================================================================
// EDGE: the gap-exactly-one iteration (g − j == 1, i.e. g == j + 1, j ≥ 2)
// ============================================================================
//
// At the FIRST intra-phase copy_refresh the gap G equals the master length M (the master floated up
// by exactly one consumed counter), so the last marked-copy iteration j = M − 1 has gap g − j = 1. The
// single gap blank is consumed by the temp→gap `t2g` transition, so the forward seek lands DIRECTLY on
// the master's lowest five — there is no gap to seek across. The MARK uses the SAME eleven quintuples as
// the general [`lemma_mark`] (the `i_gap`/`i_rgap` seek quints simply never fire), so one TM/quint-set
// drives both the general and the g−j=1 iterations; the loop dispatches on `g == j + 1`. The deposit
// afterward refills the now-consumed gap cell (temp grows flush against the master).

/// **Forward seek of the MARK, gap-exactly-one case (`g == j + 1`, `2 ≤ j < M`).** Mirror of
/// [`lemma_mark_fwd`] specialized to `g = j + 1`: the temp→gap transition `(q_t, 0, 0, q_a, L)` consumes
/// the lone gap blank and lands the head directly on the master's lowest five — there is NO gap-seek
/// (S4 fires zero steps and is dropped). Lands on the lowest unmarked master one, the SAME `c5` state as
/// [`lemma_mark_fwd`] (with `g = j + 1`, so `big_v = pile_temp · m`). Total `2·j + 2` steps.
pub proof fn lemma_mark_fwd_gj1(
    tm: Tm, j: nat, big_m: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_fives: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_fives] == mk_quint(q_a, 5, 5, q_a, Dir::L),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(j, big_m, (j + 1) as nat, tm.m), v: out, a: 0, q: q_mh },
            (2 * j + 2) as nat)
            == (TmConfig {
                u: repunit_m((big_m - j - 1) as nat, tm.m),
                v: pile_sym(pile_sym(out * tm.m, 1, j, tm.m) * tm.m, 5, j, tm.m),
                a: 1, q: q_a }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let g = (j + 1) as nat;
    let ms = master_at(j, big_m, m);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j) + m^g·ms
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── S1: pivot-peel (q_mh, 0, 0, q_t, L). copy_u(j)%m==1, /m == R(j-1) + m^(g-1)·ms == R(j-1)+m^j·ms. ──
    lemma_repunit_step((j - 1) as nat, m);   // R(j) == m·R(j-1)+1
    lemma_pow_nat_unfold(m, g);              // m^g == m·m^(g-1) == m·m^j
    assert((g - 1) as nat == j);
    let u1 = repunit_m((j - 1) as nat, m) + pow_nat(m, j) * ms;
    assert(copy_u(j, big_m, g, m) == u1 * m + 1) by(nonlinear_arith)
        requires
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * ms,
            repunit_m(j, m) == m * repunit_m((j - 1) as nat, m) + 1,
            pow_nat(m, g) == m * pow_nat(m, j),
            u1 == repunit_m((j - 1) as nat, m) + pow_nat(m, j) * ms;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_t);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);

    // ── S2: walk-left over temp (j steps), q_t. c1.u == 1·R(j-1) + m^(j-1)·(m·ms). ──
    let w_a = m * ms;
    lemma_pow_nat_unfold(m, j);   // m^j == m·m^(j-1)
    assert(c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a) by(nonlinear_arith)
        requires
            c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, j) * ms,
            pow_nat(m, j) == m * pow_nat(m, (j - 1) as nat),
            w_a == m * ms;
    lemma_run_walk_left(tm, c1, q_t, 1, (j - 1) as nat, w_a, i_temp);
    // w_a % m == 0, w_a / m == ms.
    assert(m * ms == ms * m) by(nonlinear_arith);
    lemma_div_mod_step(ms, m, 0);   // (ms·m+0)/m==ms, %m==0
    let pile_temp = pile_sym(out * m, 1, j, m);
    let c2 = TmConfig { u: ms, v: pile_temp, a: 0, q: q_t };
    assert(((j - 1) + 1) as nat == j);
    assert(tm_run(tm, c1, j) == c2);
    lemma_tm_run_split(tm, c0, 1, j);
    assert(tm_run(tm, c0, (1 + j) as nat) == c2);

    // ── S3: temp→gap transition (q_t, 0, 0, q_a, L) consumes the lone gap blank; ms%m==5, lands on five. ──
    let ms_div = 5 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m);
    assert(ms == ms_div * m + 5) by(nonlinear_arith)
        requires
            ms == 5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m),
            repunit_m(j, m) == m * repunit_m((j - 1) as nat, m) + 1,
            pow_nat(m, j) == m * pow_nat(m, (j - 1) as nat),
            ms_div == 5 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m);
    lemma_div_mod_step(ms_div, m, 5);   // ms%m==5, ms/m==ms_div
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == ms_div && c3.v == pile_temp * m && c3.a == 5 && c3.q == q_a);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, (1 + j) as nat, 1);
    assert(tm_run(tm, c0, (1 + j + 1) as nat) == c3);

    // ── S5: walk-left over the master fives (j steps), q_a. c3.u == 5·R(j-1) + m^(j-1)·R(M-j). ──
    lemma_run_walk_left(tm, c3, q_a, 5, (j - 1) as nat, repunit_m((big_m - j) as nat, m), i_fives);
    lemma_repunit_step((big_m - j - 1) as nat, m);   // R(M-j) == m·R(M-j-1)+1
    assert(((big_m - j - 1) + 1) as nat == (big_m - j) as nat);
    assert(repunit_m((big_m - j) as nat, m) == repunit_m((big_m - j - 1) as nat, m) * m + 1)
        by(nonlinear_arith)
        requires repunit_m((big_m - j) as nat, m) == m * repunit_m((big_m - j - 1) as nat, m) + 1;
    lemma_div_mod_step(repunit_m((big_m - j - 1) as nat, m), m, 1);
    let c5 = TmConfig {
        u: repunit_m((big_m - j - 1) as nat, m), v: pile_sym(pile_temp * m, 5, j, m), a: 1, q: q_a };
    assert(((j - 1) + 1) as nat == j);
    assert(tm_run(tm, c3, j) == c5);
    lemma_tm_run_split(tm, c0, (1 + j + 1) as nat, j);
    assert((1 + j + 1 + j) as nat == (2 * j + 2) as nat);
    assert(tm_run(tm, c0, (2 * j + 2) as nat) == c5);
}

/// **The MARK gadget, gap-exactly-one case (`g == j + 1`, `2 ≤ j < M`).** Mirror of [`lemma_mark`]
/// specialized to `g = j + 1`: forward via [`lemma_mark_fwd_gj1`] (no gap-seek), flip the master one
/// `1 → 5`, walk back — fives back, `rf→gap` transition landing DIRECTLY on the temp's high one (no
/// gap-seek S8, the lone gap blank already consumed), `rg→temp` transition, temp back. Net `u` gains
/// `4·m^(g+j) = 4·m^(2j+1)`, output `v` restored, head on the pivot in `q_rt`. The ensures matches
/// [`lemma_mark`] with `g = j + 1`. Total `2·(g + j + 1) = 4·j + 4` steps. SAME eleven quintuples as
/// [`lemma_mark`] (`i_gap`/`i_rgap` never fire).
pub proof fn lemma_mark_gj1(
    tm: Tm, j: nat, big_m: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_rf: nat, q_rg: nat, q_rt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_fives] == mk_quint(q_a, 5, 5, q_a, Dir::L),
        tm.quints[i_mark] == mk_quint(q_a, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(j, big_m, (j + 1) as nat, tm.m), v: out, a: 0, q: q_mh },
            (2 * (2 * j + 2)) as nat)
            == (TmConfig {
                u: (copy_u(j, big_m, (j + 1) as nat, tm.m) + 4 * pow_nat(tm.m, (2 * j + 1) as nat)) as nat,
                v: out, a: 0, q: q_rt }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let g = (j + 1) as nat;
    let pile_temp = pile_sym(out * m, 1, j, m);
    let big_v = pile_temp * m;                       // big_v == pile_temp · m^(g−j) with g−j == 1
    let mm1 = repunit_m((big_m - j - 1) as nat, m);   // R(M−j−1)
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── FORWARD: c0 → c5 (the lowest unmarked one), 2j+2 steps (no gap-seek). ──
    lemma_mark_fwd_gj1(tm, j, big_m, out, q_mh, q_t, q_a, i_peel, i_temp, i_t2g, i_fives);
    let c5 = TmConfig { u: mm1, v: pile_sym(big_v, 5, j, m), a: 1, q: q_a };
    assert(tm_run(tm, c0, (2 * j + 2) as nat) == c5);

    // ── MARK step (q_a, 1, 5, q_rf, R). ──
    lemma_pile_sym_div_mod(big_v, 5, j, m);
    lemma_tm_step_picks(tm, c5, i_mark);
    let c6 = apply_quint(tm.quints[i_mark], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == mm1 * m + 5 && c6.v == pile_sym(big_v, 5, (j - 1) as nat, m) && c6.a == 5
        && c6.q == q_rf);
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (2 * j + 2) as nat, 1);
    assert(tm_run(tm, c0, (2 * j + 3) as nat) == c6);

    // ── S6: run_walk_right over the fives (j steps). c6.u == 5·R(1)+m·R(M−j−1). ──
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(c6.u == 5 * repunit_m(1, m) + pow_nat(m, 1) * mm1) by(nonlinear_arith)
        requires c6.u == mm1 * m + 5, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c6, q_rf, 5, 1, (j - 1) as nat, big_v, mm1, i_rfives);
    assert((1 + (j - 1) + 1) as nat == (j + 1) as nat);
    assert((big_m - (j + 1)) as nat == (big_m - j - 1) as nat);
    assert(ms_next == 5 * repunit_m((j + 1) as nat, m) + pow_nat(m, (j + 1) as nat) * mm1);
    // big_v % m == 0, / m == pile_temp.
    assert(big_v == pile_temp * m);
    lemma_div_mod_step(pile_temp, m, 0);
    let c7 = TmConfig { u: ms_next, v: pile_temp, a: 0, q: q_rf };
    assert(tm_run(tm, c6, j) == c7);
    lemma_tm_run_split(tm, c0, (2 * j + 3) as nat, j);
    assert((2 * j + 3 + j) as nat == (3 * j + 3) as nat);
    assert(tm_run(tm, c0, (3 * j + 3) as nat) == c7);

    // ── S7: rf→gap transition (q_rf, 0, 0, q_rg, R) lands DIRECTLY on the temp high one (no gap S8). ──
    lemma_pile_sym_div_mod(out * m, 1, j, m);   // pile_temp%m==1 (j≥1), /m==pile_sym(out·m,1,j-1)
    lemma_tm_step_picks(tm, c7, i_rf2g);
    let c8 = apply_quint(tm.quints[i_rf2g], c7, m);
    assert(tm_step(tm, c7) == Some(c8));
    assert(c8.u == ms_next * m && c8.v == pile_sym(out * m, 1, (j - 1) as nat, m) && c8.a == 1
        && c8.q == q_rg);
    assert(tm_run(tm, c8, 0) == c8);
    assert(tm_run(tm, c7, 1) == c8);
    lemma_tm_run_split(tm, c0, (3 * j + 3) as nat, 1);
    assert(tm_run(tm, c0, (3 * j + 4) as nat) == c8);

    // ── S9: rg→temp transition (q_rg, 1, 1, q_rt, R). j≥2 ⟹ pile_sym(out·m,1,j-1)%m==1. ──
    lemma_pile_sym_div_mod(out * m, 1, (j - 1) as nat, m);
    lemma_tm_step_picks(tm, c8, i_rg2t);
    let c10 = apply_quint(tm.quints[i_rg2t], c8, m);
    assert(tm_step(tm, c8) == Some(c10));
    assert(c10.u == c8.u * m + 1 && c10.v == pile_sym(out * m, 1, (j - 2) as nat, m) && c10.a == 1
        && c10.q == q_rt);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c8, 1) == c10);
    lemma_tm_run_split(tm, c0, (3 * j + 4) as nat, 1);
    assert(tm_run(tm, c0, (3 * j + 5) as nat) == c10);

    // ── S10: run_walk_right over temp (j-1 steps). c10.u == 1·R(1)+m·c8.u. ──
    assert(c10.u == 1 * repunit_m(1, m) + pow_nat(m, 1) * c8.u) by(nonlinear_arith)
        requires c10.u == c8.u * m + 1, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c10, q_rt, 1, 1, (j - 2) as nat, out * m, c8.u, i_rtemp);
    assert((1 + (j - 2) + 1) as nat == j);
    lemma_div_mod_step(out, m, 0);   // (out·m)/m==out, %m==0
    let c11 = TmConfig { u: repunit_m(j, m) + pow_nat(m, j) * c8.u, v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c10, (j - 1) as nat) == c11);
    lemma_tm_run_split(tm, c0, (3 * j + 5) as nat, (j - 1) as nat);
    assert((3 * j + 5 + (j - 1)) as nat == (2 * (2 * j + 2)) as nat);
    assert(tm_run(tm, c0, (2 * (2 * j + 2)) as nat) == c11);

    // ── c11.u == copy_u(j) + 4·m^(2j+1). ──
    // c11.u = R(j) + m^j·c8.u = R(j) + m^j·(ms_next·m) = R(j) + m^(j+1)·ms_next == R(j) + m^g·ms_next.
    assert(pow_nat(m, j) * c8.u == pow_nat(m, g) * ms_next) by(nonlinear_arith)
        requires c8.u == ms_next * m, pow_nat(m, g) == m * pow_nat(m, j);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j)+m^g·master_at(j,M)
    lemma_master_at_step(j, big_m, m);     // ms_next == master_at(j,M)+4·m^j
    lemma_pow_nat_add(m, g, j);            // m^(g+j) == m^g·m^j
    assert((g + j) as nat == (2 * j + 1) as nat);
    assert(c11.u == (copy_u(j, big_m, g, m) + 4 * pow_nat(m, (2 * j + 1) as nat)) as nat) by(nonlinear_arith)
        requires
            c11.u == repunit_m(j, m) + pow_nat(m, g) * ms_next,
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * master_at(j, big_m, m),
            ms_next == master_at(j, big_m, m) + 4 * pow_nat(m, j),
            pow_nat(m, (2 * j + 1) as nat) == pow_nat(m, g) * pow_nat(m, j);
}

/// **One marked-copy iteration, gap-exactly-one case (`g == j + 1`, `2 ≤ j < M`).** Mirror of
/// [`lemma_copy_iter`] composing [`lemma_mark_gj1`] (`+4·m^(2j+1)`) and [`lemma_deposit`] (`+m^j`). This
/// is the LAST iteration of a `G == M` copy_refresh (`j = M − 1`, so `g = j + 1 = M`); the deposit
/// refills the lone gap cell, leaving temp flush against the master (`copy_u(j+1, M, j+1)`, the
/// end state). `2·(2j+2) + (2j+2) = 6j + 6` steps. Same quint-set as [`lemma_copy_iter`].
pub proof fn lemma_copy_iter_gj1(
    tm: Tm, j: nat, big_m: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat, q_bk: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_fives] == mk_quint(q_a, 5, 5, q_a, Dir::L),
        tm.quints[i_mark] == mk_quint(q_a, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
        tm.quints[i_dpeel] == mk_quint(q_rt, 0, 0, q_dw, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw, 0, 1, q_bk, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk, 1, 1, q_bk, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(j, big_m, (j + 1) as nat, tm.m), v: out, a: 0, q: q_mh },
            (6 * j + 6) as nat)
            == (TmConfig { u: copy_u((j + 1) as nat, big_m, (j + 1) as nat, tm.m), v: out, a: 0,
                q: q_bk }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let g = (j + 1) as nat;
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let w_dep = m * ms_next;   // == m^(g−j)·ms_next with g−j == 1

    // ── MARK: c0 → c_mid, where c_mid.u == copy_u(j)+4·m^(2j+1) == dec_u(j, w_dep). ──
    lemma_mark_gj1(tm, j, big_m, out, q_mh, q_t, q_a, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j) + m^g·master_at(j,M)
    lemma_master_at_step(j, big_m, m);     // ms_next == master_at(j,M) + 4·m^j
    lemma_pow_nat_add(m, g, j);            // m^(g+j) == m^g·m^j
    lemma_pow_nat_unfold(m, g);            // m^g == m·m^j  (g == j+1)
    assert((g + j) as nat == (2 * j + 1) as nat);
    // copy_u(j)+4·m^(2j+1) == R(j) + m^g·ms_next == R(j) + m^j·w_dep == dec_u(j, w_dep).
    assert(copy_u(j, big_m, g, m) + 4 * pow_nat(m, (2 * j + 1) as nat) == dec_u(j, w_dep, m))
        by(nonlinear_arith)
        requires
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * master_at(j, big_m, m),
            ms_next == master_at(j, big_m, m) + 4 * pow_nat(m, j),
            pow_nat(m, (2 * j + 1) as nat) == pow_nat(m, g) * pow_nat(m, j),
            pow_nat(m, g) == m * pow_nat(m, j),
            w_dep == m * ms_next,
            dec_u(j, w_dep, m) == repunit_m(j, m) + pow_nat(m, j) * w_dep;
    let c_mid = TmConfig { u: dec_u(j, w_dep, m), v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c0, (2 * (2 * j + 2)) as nat) == c_mid);

    // ── DEPOSIT (home state q_rt): c_mid → c_end, u += m^j. w_dep % m == 0. ──
    assert(m * ms_next == ms_next * m) by(nonlinear_arith);
    lemma_div_mod_step(ms_next, m, 0);
    assert(w_dep % m == 0);
    lemma_deposit(tm, j, w_dep, out, q_rt, q_dw, q_bk, i_dpeel, i_dtemp, i_dins, i_dwb);
    let c_end = TmConfig { u: (dec_u(j, w_dep, m) + pow_nat(m, j)) as nat, v: out, a: 0, q: q_bk };
    assert(tm_run(tm, c_mid, (2 * j + 2) as nat) == c_end);

    // ── c_end.u == copy_u(j+1) via the iteration arithmetic. ──
    lemma_copy_u_iter_arith(j, big_m, g, m);   // copy_u(j+1) == copy_u(j)+4·m^(g+j)+m^j
    assert(c_end.u == copy_u((j + 1) as nat, big_m, g, m)) by(nonlinear_arith)
        requires
            c_end.u == dec_u(j, w_dep, m) + pow_nat(m, j),
            dec_u(j, w_dep, m) == copy_u(j, big_m, g, m) + 4 * pow_nat(m, (2 * j + 1) as nat),
            copy_u((j + 1) as nat, big_m, g, m)
                == copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat) + pow_nat(m, j),
            (g + j) as nat == (2 * j + 1) as nat;
    assert(c_end == (TmConfig { u: copy_u((j + 1) as nat, big_m, g, m), v: out, a: 0, q: q_bk }));

    // ── chain MARK ∘ DEPOSIT. ──
    lemma_tm_run_split(tm, c0, (2 * (2 * j + 2)) as nat, (2 * j + 2) as nat);
    assert((2 * (2 * j + 2) + (2 * j + 2)) as nat == (6 * j + 6) as nat);
    assert((2 * (2 * j + 2)) as nat + (2 * j + 2) as nat == (6 * j + 6) as nat);
    assert(tm_run(tm, c0, (6 * j + 6) as nat) == c_end);
}

} // verus!
