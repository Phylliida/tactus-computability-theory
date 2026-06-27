//! # GAP-2 G2-F Route (i) brick R-cmp (B-cmp.6, part 1) — the REJECT decision bricks.
//!
//! After the steady-state compare loop ([`crate::tm_cmp_loop::lemma_cmp_loop`]) the machine must DECIDE:
//! accept (output == α) or reject (mismatch, too-short, or too-long). Per the port-8051 co-design
//! (`docs/gap2-input-loader-plan.md` §N+26), the comparator is a pure predicate block: every failure path
//! transitions to a single sink state `q_reject`, and the OUTER dovetail (R-S) owns the reject cleanup
//! (clear output, rewind, increment candidate, re-dovetail). So a reject brick's only obligation is to
//! reach `q_reject`.
//!
//! This file builds the **MISMATCH** reject (the smallest first brick): the gap-cross lands the head on
//! the output frontier `d_o ∈ 1..4` in the compare state `q_cmp` (carrying the marked α value `vk`); when
//! `d_o ≠ vk` the mismatch quintuple `(q_cmp, d_o, d_o, q_reject, R)` fires and the run is in `q_reject`.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, tm_step, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::pow_nat;
use crate::tm_skip_blank::pile_zeros;
use crate::tm_cmp_traverse::lemma_cmp_gap_cross;
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **B-cmp.6 — the MISMATCH reject round.** From the loop invariant `INV(K)` (head one cell into `u`
/// scanning the top gap blank `0` in the left-walk state `q_walk` carrying the marked value `vk`, output
/// stack `pile_zeros(d_o + m·out_rest, g, m)`, α stack `c.v`), the machine crosses the gap into the
/// compare state `q_cmp` ([`lemma_cmp_gap_cross`]) and reads the output frontier `d_o`. When `d_o ≠ vk`
/// the digit does not match the marked α value, so the **mismatch** quintuple `(q_cmp, d_o, d_o,
/// q_reject, R)` fires and the run reaches the sink state `q_reject`. Fuel `g + 1`. Requires `n ≥ 4`.
///
/// (`d_o ≠ vk` is the semantic side-condition that distinguishes this from the MATCH quintuple
/// `(q_cmp, vk, 0, q_back, R)`; both cannot be present for the same scanned digit under `tm_wf`
/// determinism, so in the assembled deterministic TM exactly one fires per frontier value.)
pub proof fn lemma_cmp_mismatch_round(
    tm: Tm, c: TmConfig, q_walk: nat, q_cmp: nat, q_reject: nat,
    g: nat, d_o: nat, out_rest: nat,
    ib: int, ic: int, jm: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        1 <= d_o <= 4,
        g >= 1,
        c.a == pile_zeros(d_o + tm.m * out_rest, g, tm.m) % tm.m,
        c.u == pile_zeros(d_o + tm.m * out_rest, g, tm.m) / tm.m,
        c.q == q_walk,
        0 <= ib < tm.quints.len(),
        0 <= ic < tm.quints.len(),
        0 <= jm < tm.quints.len(),
        tm.quints[ib] == mk_quint(q_walk, 0, 0, q_cmp, Dir::L),   // boundary transition
        tm.quints[ic] == mk_quint(q_cmp, 0, 0, q_cmp, Dir::L),    // gap skip
        tm.quints[jm] == mk_quint(q_cmp, d_o, d_o, q_reject, Dir::R),   // mismatch -> reject
    ensures
        tm_run(tm, c, (g + 1) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    // ── cross the gap, land scanning d_o in q_cmp.
    lemma_cmp_gap_cross(tm, c, q_walk, q_cmp, g, d_o, out_rest, ib, ic);
    let c_cmp = TmConfig { u: out_rest, v: pile_zeros(c.v, g, m), a: d_o, q: q_cmp };
    assert(tm_run(tm, c, g) == c_cmp);

    // ── the mismatch quintuple fires (q == q_cmp, a == d_o) -> q_reject.
    assert(quint_matches(tm.quints[jm], c_cmp));
    lemma_tm_step_picks(tm, c_cmp, jm);
    let c_rej = apply_quint(tm.quints[jm], c_cmp, m);
    assert(tm_step(tm, c_cmp) == Some(c_rej));
    assert(c_rej.q == q_reject);

    // ── compose: g + 1 steps.
    lemma_tm_run_split(tm, c, g, 1);
    assert(tm_run(tm, c_rej, 0) == c_rej);
    assert(tm_run(tm, c_cmp, 1) == c_rej);
    assert(tm_run(tm, c, (g + 1) as nat) == c_rej);
}

/// **B-cmp.6 — the output-too-short reject round.** Same entry as [`lemma_cmp_mismatch_round`], but the
/// output ran out: after crossing the consumed-output gap the head reads the **output far-`5` sentinel**
/// (`d_o == 5`) instead of a digit, while α still has the marked digit `vk ∈ 1..4` pending. The
/// too-short quintuple `(q_cmp, 5, 5, q_reject, R)` fires and the run reaches `q_reject`. Fuel `g + 1`.
/// Requires `n ≥ 5` (the sentinel `5` must be a real symbol below `m`). Reuses the generalized
/// [`lemma_cmp_gap_cross`] at frontier `d_o = 5`.
pub proof fn lemma_cmp_tooshort_round(
    tm: Tm, c: TmConfig, q_walk: nat, q_cmp: nat, q_reject: nat,
    g: nat, out_rest: nat,
    ib: int, ic: int, jt: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        g >= 1,
        c.a == pile_zeros(5 + tm.m * out_rest, g, tm.m) % tm.m,
        c.u == pile_zeros(5 + tm.m * out_rest, g, tm.m) / tm.m,
        c.q == q_walk,
        0 <= ib < tm.quints.len(),
        0 <= ic < tm.quints.len(),
        0 <= jt < tm.quints.len(),
        tm.quints[ib] == mk_quint(q_walk, 0, 0, q_cmp, Dir::L),   // boundary transition
        tm.quints[ic] == mk_quint(q_cmp, 0, 0, q_cmp, Dir::L),    // gap skip
        tm.quints[jt] == mk_quint(q_cmp, 5, 5, q_reject, Dir::R),  // output sentinel -> reject (too short)
    ensures
        tm_run(tm, c, (g + 1) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    // ── cross the gap, land scanning the output sentinel 5 in q_cmp.
    lemma_cmp_gap_cross(tm, c, q_walk, q_cmp, g, 5, out_rest, ib, ic);
    let c_cmp = TmConfig { u: out_rest, v: pile_zeros(c.v, g, m), a: 5, q: q_cmp };
    assert(tm_run(tm, c, g) == c_cmp);

    // ── the too-short quintuple fires (q == q_cmp, a == 5) -> q_reject.
    assert(quint_matches(tm.quints[jt], c_cmp));
    lemma_tm_step_picks(tm, c_cmp, jt);
    let c_rej = apply_quint(tm.quints[jt], c_cmp, m);
    assert(tm_step(tm, c_cmp) == Some(c_rej));
    assert(c_rej.q == q_reject);

    // ── compose: g + 1 steps.
    lemma_tm_run_split(tm, c, g, 1);
    assert(tm_run(tm, c_rej, 0) == c_rej);
    assert(tm_run(tm, c_cmp, 1) == c_rej);
    assert(tm_run(tm, c, (g + 1) as nat) == c_rej);
}

} // verus!
