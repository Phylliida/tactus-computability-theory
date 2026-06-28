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
use crate::tm_dstring::{dpack, pow_nat};
use crate::tm_skip_blank::pile_zeros;
use crate::tm_cmp_traverse::{lemma_cmp_gap_cross, lemma_cmp_match_round_end};
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

/// **B-cmp.6 — the ACCEPT decision (reaches `q_accept`).** The α-exhaust path's success branch, composed
/// end-to-end from the loop-exit `INV` (uniform with the reject bricks: head one cell into `u` scanning the
/// top gap-`0` in the left-walk track `q_walk`, the marker on the LAST α digit `vk` with the far sentinel
/// above — `w == m·whi + 5`, `whi == 5` — and the output frontier `d_o == vk`, i.e. the last digit matches).
/// The output **exhausts** after this digit: above the last matched output digit sits the output far-`5`
/// sentinel (`out_rest == 5`). The machine: gap-cross #1 into `q_cmp` ([`lemma_cmp_gap_cross`]) reads the
/// frontier `vk`; [`lemma_cmp_match_round_end`] matches it, restores α, and switches to `q_verify_end` at
/// the boundary; a verify-end gap-cross #2 reads the next output cell — the output far-`5` sentinel — and
/// the **accept** quintuple `(q_verify_cmp, 5, 5, q_accept, R)` fires: BOTH strings exhausted together with
/// all digits matched ⟹ output `==` α ⟹ `q_accept`. Fuel `2·|blk| + 3·g + 6`. Requires `n ≥ 5`. (The
/// tape-wipe to `tm_origin` is the separate cleanup brick; this only reaches the `q_accept` marker.)
pub proof fn lemma_cmp_accept_decide(
    tm: Tm, c: TmConfig,
    q_walk: nat, q_cmp: nat, q_back: nat, q_read: nat, q_verify_end: nat, q_verify_cmp: nat, q_accept: nat,
    blk: Seq<nat>, w: nat, whi: nat, vk: nat, g: nat,
    ib: int, ic: int,
    jc: int, js: int, i1: int, i2: int, i3: int, i4: int, j: int, je: int,
    l1: int, l2: int, l3: int, l4: int,
    ibv: int, icv: int, ja: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        1 <= vk <= 4,
        g >= 1,
        w == tm.m * whi + 5,
        whi == 5,
        c.a == pile_zeros(vk + tm.m * 5, g, tm.m) % tm.m,
        c.u == pile_zeros(vk + tm.m * 5, g, tm.m) / tm.m,   // output frontier vk, then far sentinel 5
        c.v == dpack(blk, tm.m) + pow_nat(tm.m, blk.len()) * w,
        c.q == q_walk,
        0 <= ib < tm.quints.len(),
        0 <= ic < tm.quints.len(),
        0 <= jc < tm.quints.len(),
        0 <= js < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        0 <= j < tm.quints.len(),
        0 <= je < tm.quints.len(),
        0 <= l1 < tm.quints.len(),
        0 <= l2 < tm.quints.len(),
        0 <= l3 < tm.quints.len(),
        0 <= l4 < tm.quints.len(),
        0 <= ibv < tm.quints.len(),
        0 <= icv < tm.quints.len(),
        0 <= ja < tm.quints.len(),
        tm.quints[ib] == mk_quint(q_walk, 0, 0, q_cmp, Dir::L),   // gap-cross #1 boundary
        tm.quints[ic] == mk_quint(q_cmp, 0, 0, q_cmp, Dir::L),    // gap-cross #1 gap skip
        tm.quints[jc] == mk_quint(q_cmp, vk, 0, q_back, Dir::R),
        tm.quints[js] == mk_quint(q_back, 0, 0, q_back, Dir::R),
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
        tm.quints[j]  == mk_quint(q_back, 5, vk, q_read, Dir::R),
        tm.quints[je] == mk_quint(q_read, 5, 5, q_verify_end, Dir::L),
        tm.quints[l1] == mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L),
        tm.quints[l2] == mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L),
        tm.quints[l3] == mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L),
        tm.quints[l4] == mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L),
        tm.quints[ibv] == mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L),  // verify boundary
        tm.quints[icv] == mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L),  // verify gap skip
        tm.quints[ja]  == mk_quint(q_verify_cmp, 5, 5, q_accept, Dir::R),      // ACCEPT
    ensures
        tm_run(tm, c, (2 * blk.len() + 3 * g + 6) as nat).q == q_accept,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let k = blk.len();
    let alpha = dpack(blk, m) + pow_nat(m, k) * w;

    // ── gap-cross #1: cross the gap, land scanning the output frontier vk in q_cmp.
    lemma_cmp_gap_cross(tm, c, q_walk, q_cmp, g, vk, 5, ib, ic);
    let c_cmp = TmConfig { u: 5, v: pile_zeros(c.v, g, m), a: vk, q: q_cmp };
    assert(tm_run(tm, c, g) == c_cmp);
    assert(c_cmp.v == pile_zeros(alpha, g, m));

    // ── match the last digit, restore α, land at the verify-end boundary.
    lemma_cmp_match_round_end(tm, c_cmp, q_cmp, q_back, q_read, q_verify_end, blk, w, whi, vk, g, 5,
        jc, js, i1, i2, i3, i4, j, je, l1, l2, l3, l4);
    let c_end = TmConfig {
        u: pile_zeros(5, g, m),
        v: dpack(blk + seq![vk], m) + pow_nat(m, (k + 1) as nat) * 5,
        a: 0,
        q: q_verify_end,
    };
    assert(tm_run(tm, c_cmp, (2 * k + g + 4) as nat) == c_end);

    // ── verify-end gap-cross #2: full output stack == pile_zeros(5, g+1), frontier == the far sentinel 5.
    assert(m * 0 == 0) by(nonlinear_arith);
    assert(pile_zeros(5 + m * 0, (g + 1) as nat, m) == pile_zeros(5, g, m) * m);   // unfold (g+1 >= 1)
    assert((pile_zeros(5, g, m) * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((pile_zeros(5, g, m) * m) / m == pile_zeros(5, g, m)) by(nonlinear_arith) requires m > 1;
    assert(c_end.a == pile_zeros(5 + m * 0, (g + 1) as nat, m) % m);
    assert(c_end.u == pile_zeros(5 + m * 0, (g + 1) as nat, m) / m);
    lemma_cmp_gap_cross(tm, c_end, q_verify_end, q_verify_cmp, (g + 1) as nat, 5, 0, ibv, icv);
    let c_v = TmConfig { u: 0, v: pile_zeros(c_end.v, (g + 1) as nat, m), a: 5, q: q_verify_cmp };
    assert(tm_run(tm, c_end, (g + 1) as nat) == c_v);

    // ── the accept quintuple fires (q == q_verify_cmp, a == 5) -> q_accept.
    assert(quint_matches(tm.quints[ja], c_v));
    lemma_tm_step_picks(tm, c_v, ja);
    let c_acc = apply_quint(tm.quints[ja], c_v, m);
    assert(tm_step(tm, c_v) == Some(c_acc));
    assert(c_acc.q == q_accept);

    // ── compose: g + (2k+g+4) + (g+1) + 1 = 2k + 3g + 6.
    lemma_tm_run_split(tm, c, g, (2 * k + 2 * g + 6) as nat);
    lemma_tm_run_split(tm, c_cmp, (2 * k + g + 4) as nat, (g + 2) as nat);
    lemma_tm_run_split(tm, c_end, (g + 1) as nat, 1);
    assert(tm_run(tm, c_acc, 0) == c_acc);
    assert(tm_run(tm, c_v, 1) == c_acc);
    assert((2 * k + 3 * g + 6) as nat == (g + (2 * k + 2 * g + 6)) as nat);
    assert((2 * k + 2 * g + 6) as nat == ((2 * k + g + 4) + (g + 2)) as nat);
    assert(tm_run(tm, c, (2 * k + 3 * g + 6) as nat) == c_acc);
}

/// **B-cmp.6 — the too-long reject decision (reaches `q_reject`).** The α-exhaust path's failure branch
/// when the output is LONGER than α. Same `INV` entry as [`lemma_cmp_accept_decide`] (head one cell into
/// `u`, the marker on the last α digit `vk`, far sentinel above, output frontier `d_o == vk`), but the
/// output does **not** exhaust: above the just-matched last output digit sits another output digit
/// `d_o2 ∈ 1..4` (`out_rest == d_o2 + m·out_rest2`). After gap-cross #1 + [`lemma_cmp_match_round_end`]
/// lands at the verify-end boundary, the verify-end gap-cross #2 reads that surviving digit, and the
/// **too-long** quintuple `(q_verify_cmp, d_o2, d_o2, q_reject, R)` fires (α exhausted but output still has
/// digits ⟹ lengths differ ⟹ `q_reject`). Fuel `2·|blk| + 3·g + 6`. Requires `n ≥ 5`.
pub proof fn lemma_cmp_toolong_round(
    tm: Tm, c: TmConfig,
    q_walk: nat, q_cmp: nat, q_back: nat, q_read: nat, q_verify_end: nat, q_verify_cmp: nat, q_reject: nat,
    blk: Seq<nat>, w: nat, whi: nat, vk: nat, g: nat, d_o2: nat, out_rest2: nat,
    ib: int, ic: int,
    jc: int, js: int, i1: int, i2: int, i3: int, i4: int, j: int, je: int,
    l1: int, l2: int, l3: int, l4: int,
    ibv: int, icv: int, jl: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        1 <= vk <= 4,
        1 <= d_o2 <= 4,
        g >= 1,
        w == tm.m * whi + 5,
        whi == 5,
        c.a == pile_zeros(vk + tm.m * (d_o2 + tm.m * out_rest2), g, tm.m) % tm.m,
        c.u == pile_zeros(vk + tm.m * (d_o2 + tm.m * out_rest2), g, tm.m) / tm.m,
        c.v == dpack(blk, tm.m) + pow_nat(tm.m, blk.len()) * w,
        c.q == q_walk,
        0 <= ib < tm.quints.len(),
        0 <= ic < tm.quints.len(),
        0 <= jc < tm.quints.len(),
        0 <= js < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        0 <= j < tm.quints.len(),
        0 <= je < tm.quints.len(),
        0 <= l1 < tm.quints.len(),
        0 <= l2 < tm.quints.len(),
        0 <= l3 < tm.quints.len(),
        0 <= l4 < tm.quints.len(),
        0 <= ibv < tm.quints.len(),
        0 <= icv < tm.quints.len(),
        0 <= jl < tm.quints.len(),
        tm.quints[ib] == mk_quint(q_walk, 0, 0, q_cmp, Dir::L),   // gap-cross #1 boundary
        tm.quints[ic] == mk_quint(q_cmp, 0, 0, q_cmp, Dir::L),    // gap-cross #1 gap skip
        tm.quints[jc] == mk_quint(q_cmp, vk, 0, q_back, Dir::R),
        tm.quints[js] == mk_quint(q_back, 0, 0, q_back, Dir::R),
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
        tm.quints[j]  == mk_quint(q_back, 5, vk, q_read, Dir::R),
        tm.quints[je] == mk_quint(q_read, 5, 5, q_verify_end, Dir::L),
        tm.quints[l1] == mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L),
        tm.quints[l2] == mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L),
        tm.quints[l3] == mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L),
        tm.quints[l4] == mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L),
        tm.quints[ibv] == mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L),
        tm.quints[icv] == mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L),
        tm.quints[jl]  == mk_quint(q_verify_cmp, d_o2, d_o2, q_reject, Dir::R),   // too-long -> reject
    ensures
        tm_run(tm, c, (2 * blk.len() + 3 * g + 6) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let k = blk.len();
    let out_rest = d_o2 + m * out_rest2;
    let alpha = dpack(blk, m) + pow_nat(m, k) * w;

    // ── gap-cross #1: cross the gap, land scanning the output frontier vk in q_cmp.
    lemma_cmp_gap_cross(tm, c, q_walk, q_cmp, g, vk, out_rest, ib, ic);
    let c_cmp = TmConfig { u: out_rest, v: pile_zeros(c.v, g, m), a: vk, q: q_cmp };
    assert(tm_run(tm, c, g) == c_cmp);
    assert(c_cmp.v == pile_zeros(alpha, g, m));

    // ── match the last digit, restore α, land at the verify-end boundary.
    lemma_cmp_match_round_end(tm, c_cmp, q_cmp, q_back, q_read, q_verify_end, blk, w, whi, vk, g, out_rest,
        jc, js, i1, i2, i3, i4, j, je, l1, l2, l3, l4);
    let c_end = TmConfig {
        u: pile_zeros(out_rest, g, m),
        v: dpack(blk + seq![vk], m) + pow_nat(m, (k + 1) as nat) * 5,
        a: 0,
        q: q_verify_end,
    };
    assert(tm_run(tm, c_cmp, (2 * k + g + 4) as nat) == c_end);

    // ── verify-end gap-cross #2: full output stack == pile_zeros(out_rest, g+1), frontier == d_o2.
    assert(pile_zeros(out_rest, (g + 1) as nat, m) == pile_zeros(out_rest, g, m) * m);   // unfold
    assert((pile_zeros(out_rest, g, m) * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((pile_zeros(out_rest, g, m) * m) / m == pile_zeros(out_rest, g, m))
        by(nonlinear_arith) requires m > 1;
    assert(c_end.a == pile_zeros(d_o2 + m * out_rest2, (g + 1) as nat, m) % m);
    assert(c_end.u == pile_zeros(d_o2 + m * out_rest2, (g + 1) as nat, m) / m);
    lemma_cmp_gap_cross(tm, c_end, q_verify_end, q_verify_cmp, (g + 1) as nat, d_o2, out_rest2, ibv, icv);
    let c_v = TmConfig { u: out_rest2, v: pile_zeros(c_end.v, (g + 1) as nat, m), a: d_o2, q: q_verify_cmp };
    assert(tm_run(tm, c_end, (g + 1) as nat) == c_v);

    // ── the too-long quintuple fires (q == q_verify_cmp, a == d_o2) -> q_reject.
    assert(quint_matches(tm.quints[jl], c_v));
    lemma_tm_step_picks(tm, c_v, jl);
    let c_rej = apply_quint(tm.quints[jl], c_v, m);
    assert(tm_step(tm, c_v) == Some(c_rej));
    assert(c_rej.q == q_reject);

    // ── compose: g + (2k+g+4) + (g+1) + 1 = 2k + 3g + 6.
    lemma_tm_run_split(tm, c, g, (2 * k + 2 * g + 6) as nat);
    lemma_tm_run_split(tm, c_cmp, (2 * k + g + 4) as nat, (g + 2) as nat);
    lemma_tm_run_split(tm, c_end, (g + 1) as nat, 1);
    assert(tm_run(tm, c_rej, 0) == c_rej);
    assert(tm_run(tm, c_v, 1) == c_rej);
    assert((2 * k + 3 * g + 6) as nat == (g + (2 * k + 2 * g + 6)) as nat);
    assert((2 * k + 2 * g + 6) as nat == ((2 * k + g + 4) + (g + 2)) as nat);
    assert(tm_run(tm, c, (2 * k + 3 * g + 6) as nat) == c_rej);
}

} // verus!
