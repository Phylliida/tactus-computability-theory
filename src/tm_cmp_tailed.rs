//! # GAP-2 G2-F Route (i) brick R-cmp — the u-TAIL-LIFT (HALF 2): tail-safe COMPARE.
//!
//! The global R-S dovetail keeps a finite **Control-Zone backup** `T_u` parked as a high tail on `u`,
//! at digit offset `H = L+1+g+M+1` (above the working tape), which the per-stage emit→reloc→compare→branch
//! surface must carry **untouched** through to `q_accept`/`q_reject` (HALF 1 — [`crate::gap2_reloc::
//! lemma_reloc_local_tailed`] — already carries it through the relocation; this file carries it through
//! the comparator). See `docs/gap2-input-loader-plan.md` §N+31 (the design / de-risk).
//!
//! **The key observation (§N+31 DE-RISK 3).** The comparator's gadgets are already *tail-generic in their
//! above-frontier parameter*: [`crate::tm_cmp_traverse::lemma_cmp_gap_cross`] / `lemma_cmp_match_round_end`
//! take an arbitrary `out_rest`, [`crate::tm_cmp_loop::lemma_cmp_loop`] / `lemma_cmp_reach_inv_p` an
//! arbitrary `out_above`/`out_tail`. The far-`5` output sentinel rides in exactly that parameter, and the
//! decision terminals fire on reading it (frontier `5`, or the divergent digit) **without popping `u` any
//! higher** — so a tail at offset `> L` is preserved. Concretely, a u-tail absorbs into the high parameter:
//!   * the THREE **reject** rounds (mismatch / too-short / too-long) already take the above-frontier rest
//!     freely (`out_rest`/`out_rest2`), so the tail rides there with no new lemma (used by the reject
//!     reloc-assemblies in `gap2_reloc_compare.rs`);
//!   * the **accept** decision is the only terminal that pins the far-`5` exactly (`out_rest == 5`). This
//!     file builds [`lemma_cmp_accept_decide_tailed`] generalising it to `out_rest == 5 + m·tail` — the
//!     accept quintuple still fires on the frontier `5` (since `5 < m` ⟹ `(5 + m·tail) % m == 5`), the
//!     tail `tail` riding above untouched — and [`lemma_cmp_decides_accept_tailed`] assembling the tailed
//!     ACCEPT end-to-end (bootstrap + matched loop via the generic [`lemma_cmp_reach_inv_p`] + the tailed
//!     decide). With `tail == 0` both recover the originals.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, tm_step, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold, lemma_dpack_empty};
use crate::tm_skip_blank::pile_zeros;
use crate::tm_cmp_traverse::{lemma_cmp_gap_cross, lemma_cmp_match_round_end};
use crate::tm_cmp_loop::{cmp_quints_present, has_quint, cmp_inv_config, cmp_above, cmp_marker,
    cmp_out_pregap, cmp_loop_fuel, extract_quint};
use crate::tm_cmp_assemble::{cmp_accept_fuel, lemma_cmp_reach_inv_p, alpha_tail_above,
    lemma_singleton_out_pregap, lemma_dpack_singleton_local, lemma_dpack_high_peel, lemma_bridge_blk};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Brick 1 — the tailed ACCEPT decide terminal (generalize lemma_cmp_accept_decide to carry a tail).
// ─────────────────────────────────────────────────────────────────────────────

/// **u-tail-lift — the tailed ACCEPT decision (reaches `q_accept`).** Identical to
/// [`crate::tm_cmp_decide::lemma_cmp_accept_decide`] except the output stack carries an arbitrary tail
/// `tail` above the far-`5` sentinel: the entry output content above the just-loaded frontier digit `vk`
/// is `out_rest == 5 + m·tail` (was pinned `5`). The machine: gap-cross #1 reads the frontier `vk`,
/// [`lemma_cmp_match_round_end`] matches it (restoring α, both sides' last digit consumed) and switches to
/// `q_verify_end`; the verify gap-cross #2 reads the next output cell — the far-`5` sentinel (`(5 + m·tail)
/// % m == 5` since `5 < m`) with the tail `tail` riding above — and the accept quintuple `(q_verify_cmp, 5,
/// 5, q_accept, R)` fires (it matches on the scanned `5`, independent of `u`). Fuel `2·|blk| + 3·g + 6`,
/// the same as the untailed decide. With `tail == 0` this IS `lemma_cmp_accept_decide`. Requires `n ≥ 5`.
pub proof fn lemma_cmp_accept_decide_tailed(
    tm: Tm, c: TmConfig,
    q_walk: nat, q_cmp: nat, q_back: nat, q_read: nat, q_verify_end: nat, q_verify_cmp: nat, q_accept: nat,
    blk: Seq<nat>, w: nat, whi: nat, vk: nat, g: nat, tail: nat,
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
        c.a == pile_zeros(vk + tm.m * (5 + tm.m * tail), g, tm.m) % tm.m,
        c.u == pile_zeros(vk + tm.m * (5 + tm.m * tail), g, tm.m) / tm.m,   // frontier vk, far sentinel 5, tail above
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
    let out_rest = (5 + m * tail) as nat;
    let alpha = dpack(blk, m) + pow_nat(m, k) * w;

    // ── gap-cross #1: cross the gap, land scanning the output frontier vk in q_cmp.
    lemma_cmp_gap_cross(tm, c, q_walk, q_cmp, g, vk, out_rest, ib, ic);
    let c_cmp = TmConfig { u: out_rest, v: pile_zeros(c.v, g, m), a: vk, q: q_cmp };
    assert(tm_run(tm, c, g) == c_cmp);
    assert(c_cmp.v == pile_zeros(alpha, g, m));

    // ── match the last digit, restore α, land at the verify-end boundary (out_rest free here).
    lemma_cmp_match_round_end(tm, c_cmp, q_cmp, q_back, q_read, q_verify_end, blk, w, whi, vk, g, out_rest,
        jc, js, i1, i2, i3, i4, j, je, l1, l2, l3, l4);
    let c_end = TmConfig {
        u: pile_zeros(out_rest, g, m),
        v: dpack(blk + seq![vk], m) + pow_nat(m, (k + 1) as nat) * 5,
        a: 0,
        q: q_verify_end,
    };
    assert(tm_run(tm, c_cmp, (2 * k + g + 4) as nat) == c_end);

    // ── verify-end gap-cross #2: full output stack == pile_zeros(out_rest, g+1) == pile_zeros(5 + m·tail, g+1),
    //    frontier == the far sentinel 5 (since 5 < m), with the tail riding above (out_rest_gc == tail).
    assert(pile_zeros(5 + m * tail, (g + 1) as nat, m) == pile_zeros(5 + m * tail, g, m) * m);   // unfold (g+1 >= 1)
    assert((pile_zeros(5 + m * tail, g, m) * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((pile_zeros(5 + m * tail, g, m) * m) / m == pile_zeros(5 + m * tail, g, m))
        by(nonlinear_arith) requires m > 1;
    assert(c_end.a == pile_zeros(5 + m * tail, (g + 1) as nat, m) % m);
    assert(c_end.u == pile_zeros(5 + m * tail, (g + 1) as nat, m) / m);
    lemma_cmp_gap_cross(tm, c_end, q_verify_end, q_verify_cmp, (g + 1) as nat, 5, tail, ibv, icv);
    let c_v = TmConfig { u: tail, v: pile_zeros(c_end.v, (g + 1) as nat, m), a: 5, q: q_verify_cmp };
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

// ─────────────────────────────────────────────────────────────────────────────
// Brick 2 — the tailed ACCEPT assembly, end-to-end (bootstrap + matched loop via the generic
// lemma_cmp_reach_inv_p + the tailed decide).
// ─────────────────────────────────────────────────────────────────────────────

/// **u-tail-lift — the tailed ACCEPT decision, end-to-end (reaches `q_accept`).** As
/// [`crate::tm_cmp_assemble::lemma_cmp_decides_accept`] but the output stack carries an arbitrary tail
/// `tail` above the far-`5` sentinel: the parked entry is `u == dpack(α) + m^L·(5 + m·tail)` (was
/// `dpack(α) + m^L·5`), while α is parked exactly (`v == dpack(α) + m^L·5`). The comparator runs the
/// bootstrap and the `L-1` matched rounds to `INV(L-1)` (via the tail-generic [`lemma_cmp_reach_inv_p`]
/// at `p = L-1`, carrying `out_tail = vk + m·(5 + m·tail)`), then the tailed accept decision
/// [`lemma_cmp_accept_decide_tailed`] reads the far-`5` and accepts — the tail riding above untouched.
/// Fuel [`cmp_accept_fuel`]`(L)`, identical to the untailed assembly. With `tail == 0` this IS
/// `lemma_cmp_decides_accept`. Requires `n ≥ 5`, `|α| ≥ 2`, all α digits `1..4`.
pub proof fn lemma_cmp_decides_accept_tailed(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_accept: nat,
    alpha: Seq<nat>, tail: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
        has_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, 5, 5, q_accept, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * (5 + tm.m * tail),
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            cmp_accept_fuel(alpha.len())).q == q_accept,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = alpha.len();
    let p = (big_l - 1) as nat;
    let vk = alpha[p as int];
    assert(1 <= vk <= 4);
    let out_rest = (5 + m * tail) as nat;
    let out_tail = (vk + m * out_rest) as nat;
    let w = (m * 5 + 5) as nat;

    let pre_p = alpha.subrange(0, p as int);                 // α[0..L-1]  (length L-1)
    assert(pre_p.len() == big_l - 1);
    assert(pre_p.len() >= 1);
    assert forall|k: int| 0 <= k < pre_p.len() implies 1 <= #[trigger] pre_p[k] <= 4 by {
        assert(pre_p[k] == alpha[k]);
    }

    // ── parked entry; recast u into reach_inv_p's `dpack(α[0..p]) + m^p·out_tail` form.
    let c0 = TmConfig {
        u: (dpack(alpha, m) + pow_nat(m, big_l) * out_rest) as nat,
        v: (dpack(alpha, m) + pow_nat(m, big_l) * 5) as nat,
        a: 0, q: q_start };
    assert forall|i: int| 0 <= i < alpha.len() implies #[trigger] alpha[i] < m by { assert(alpha[i] <= 4); }
    lemma_dpack_high_peel(alpha, m);                          // dpack(α) == dpack(α[0..L-1]) + m^{L-1}·α[L-1]
    assert((alpha.len() - 1) as nat == p);
    assert(alpha.subrange(0, (alpha.len() - 1) as int) =~= pre_p);
    assert(alpha[(alpha.len() - 1) as int] == vk);
    assert(dpack(alpha, m) == dpack(pre_p, m) + pow_nat(m, p) * vk);
    lemma_pow_nat_unfold(m, big_l);                           // m^L == m·m^{L-1}
    assert((big_l - 1) as nat == p);
    let pu_reach = (dpack(pre_p, m) + pow_nat(m, p) * out_tail) as nat;
    assert(c0.u == pu_reach) by(nonlinear_arith)
        requires
            c0.u == dpack(alpha, m) + pow_nat(m, big_l) * out_rest,
            dpack(alpha, m) == dpack(pre_p, m) + pow_nat(m, p) * vk,
            pow_nat(m, big_l) == m * pow_nat(m, p),
            out_tail == vk + m * out_rest,
            pu_reach == dpack(pre_p, m) + pow_nat(m, p) * out_tail;

    // ── reach INV(L-1) carrying the tail in out_tail.
    let c0_reach = TmConfig { u: pu_reach, v: c0.v, a: 0, q: q_start };
    assert(c0 == c0_reach);
    lemma_cmp_reach_inv_p(tm, qw, qc, qb, qr, q_start, q_read_boot, alpha, p, out_tail);
    let inv_p = cmp_inv_config(qw, pre_p, alpha.subrange(p as int, (p + 1) as int),
        alpha_tail_above(alpha, p, m), (p + 1) as nat, out_tail, m);
    assert(tm_run(tm, c0_reach, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat) == inv_p);

    // ── recognize inv_p as lemma_cmp_accept_decide_tailed's entry (g == L, out_rest == 5 + m·tail).
    let ds1 = alpha.subrange(p as int, (p + 1) as int);       // [vk]
    assert(ds1.len() == 1);
    assert(ds1[0] == vk);
    // suf = alpha_tail_above(α, L-1) == 5.
    assert(alpha.subrange((p + 1) as int, alpha.len() as int) =~= Seq::<nat>::empty());
    lemma_dpack_empty(m);
    assert((alpha.len() - 1 - p) as nat == 0nat);
    assert(pow_nat(m, 0) == 1);
    assert(alpha_tail_above(alpha, p, m) == 5);
    // cmp_above([vk], 5) == 5 ; cmp_marker([vk], 5) == w.
    assert(ds1.drop_first() =~= Seq::<nat>::empty());
    assert((ds1.len() - 1) as nat == 0nat);
    assert(cmp_above(ds1, 5, m) == 5) by {
        assert(dpack(ds1.drop_first(), m) == 0);
        assert(pow_nat(m, (ds1.len() - 1) as nat) == 1);
    }
    assert(cmp_marker(ds1, 5, m) == w);
    // output side: cmp_out_pregap([vk], out_tail) == out_tail == vk + m·out_rest.
    lemma_singleton_out_pregap(alpha, p, out_tail, m);
    assert(cmp_out_pregap(ds1, out_tail, m) == out_tail);

    // inv_p fields.
    assert(inv_p.u == pile_zeros(out_tail, (p + 1) as nat, m) / m);
    assert(inv_p.a == pile_zeros(out_tail, (p + 1) as nat, m) % m);
    assert(inv_p.q == qw(vk));
    assert(dpack(seq![vk], m) == vk) by { lemma_dpack_singleton_local(vk, m); }
    assert(inv_p.v == dpack(pre_p, m) + pow_nat(m, pre_p.len()) * cmp_marker(ds1, 5, m));
    assert(inv_p.v == dpack(pre_p, m) + pow_nat(m, pre_p.len()) * w);
    assert(pre_p.len() == p);

    // accept_decide_tailed's entry: u == pile_zeros(vk + m·(5 + m·tail), L)/m == pile_zeros(out_tail, L)/m, g == L.
    assert((p + 1) as nat == big_l);
    let cd = TmConfig {
        u: pile_zeros(vk + m * (5 + m * tail), big_l, m) / m,
        a: pile_zeros(vk + m * (5 + m * tail), big_l, m) % m,
        v: dpack(pre_p, m) + pow_nat(m, pre_p.len()) * w,
        q: qw(vk),
    };
    assert(out_tail == vk + m * (5 + m * tail));
    assert(cd.u == inv_p.u);
    assert(cd.a == inv_p.a);
    assert(cd.v == inv_p.v);
    assert(cd == inv_p);

    // ── extract the tailed-accept-decide quint indices and fire it.
    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    let aib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let aic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let ajc = extract_quint(tm, mk_quint(qc(vk), vk, 0, qb(vk), Dir::R));
    let ajs = extract_quint(tm, mk_quint(qb(vk), 0, 0, qb(vk), Dir::R));
    let ai1 = extract_quint(tm, mk_quint(qb(vk), 1, 1, qb(vk), Dir::R));
    let ai2 = extract_quint(tm, mk_quint(qb(vk), 2, 2, qb(vk), Dir::R));
    let ai3 = extract_quint(tm, mk_quint(qb(vk), 3, 3, qb(vk), Dir::R));
    let ai4 = extract_quint(tm, mk_quint(qb(vk), 4, 4, qb(vk), Dir::R));
    let aj  = extract_quint(tm, mk_quint(qb(vk), 5, vk, qr, Dir::R));
    let aje = extract_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L));
    let al1 = extract_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L));
    let al2 = extract_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L));
    let al3 = extract_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L));
    let al4 = extract_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L));
    let aibv = extract_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L));
    let aicv = extract_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L));
    let aja = extract_quint(tm, mk_quint(q_verify_cmp, 5, 5, q_accept, Dir::R));

    lemma_cmp_accept_decide_tailed(tm, inv_p, qw(vk), qc(vk), qb(vk), qr,
        q_verify_end, q_verify_cmp, q_accept, pre_p, w, 5, vk, big_l, tail,
        aib, aic, ajc, ajs, ai1, ai2, ai3, ai4, aj, aje,
        al1, al2, al3, al4, aibv, aicv, aja);
    let f3 = (2 * pre_p.len() + 3 * big_l + 6) as nat;
    assert(tm_run(tm, inv_p, f3).q == q_accept);

    // ── compose: reach fuel (8 + loop) + decide fuel == cmp_accept_fuel(L).
    let f2 = cmp_loop_fuel(1, 2, (p - 1) as nat);
    lemma_tm_run_split(tm, c0_reach, (8 + f2) as nat, f3);
    assert(cmp_accept_fuel(big_l) == (8 + f2 + f3) as nat) by {
        assert((p - 1) as nat == (big_l - 2) as nat);
        assert(pre_p.len() == (big_l - 1) as nat);
    }
    assert(tm_run(tm, c0_reach, cmp_accept_fuel(big_l)) == tm_run(tm, inv_p, f3));
}

// ─────────────────────────────────────────────────────────────────────────────
// Brick 4a — the tailed TOO-SHORT decide (the one reject terminal that pins the far-5). The mismatch /
// mismatch0 / too-long terminals already take their above-frontier rest freely, so they carry the tail
// with no new cmp lemma; this is the lone exception.
// ─────────────────────────────────────────────────────────────────────────────

/// **u-tail-lift — the tailed TOO-SHORT decision (reaches `q_reject`).** As
/// [`crate::tm_cmp_assemble::lemma_cmp_decides_tooshort`] but the output's far-`5` sentinel carries an
/// arbitrary tail above it (`out_tail == 5 + m·tail`, was pinned `5`): the comparator reaches `INV(p)` via
/// the tail-generic [`lemma_cmp_reach_inv_p`] (carrying `out_tail`), the gap-cross reads the sentinel `5`
/// (`(5 + m·tail) % m == 5`), and the too-short quintuple fires → `q_reject`, the tail riding above. With
/// `tail == 0` this IS `lemma_cmp_decides_tooshort`. Requires `n ≥ 5`, `|α| ≥ 2`, `1 ≤ p ≤ |α|-1`.
pub proof fn lemma_cmp_decides_tooshort_tailed(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat, q_reject: nat,
    alpha: Seq<nat>, p: nat, tail: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        1 <= p <= alpha.len() - 1,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(alpha[p as int]), 5, 5, q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha.subrange(0, p as int), tm.m) + pow_nat(tm.m, p) * (5 + tm.m * tail),
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    let vk = alpha[p as int];
    let out_tail = (5 + m * tail) as nat;
    let c0 = TmConfig {
        u: dpack(alpha.subrange(0, p as int), m) + pow_nat(m, p) * out_tail,
        v: dpack(alpha, m) + pow_nat(m, alpha.len()) * 5,
        a: 0,
        q: q_start,
    };
    lemma_cmp_reach_inv_p(tm, qw, qc, qb, qr, q_start, q_read_boot, alpha, p, out_tail);
    let inv_p = cmp_inv_config(qw, alpha.subrange(0, p as int), alpha.subrange(p as int, (p + 1) as int),
        alpha_tail_above(alpha, p, m), (p + 1) as nat, out_tail, m);
    assert(tm_run(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat) == inv_p);

    lemma_singleton_out_pregap(alpha, p, out_tail, m);
    assert(inv_p.a == pile_zeros(5 + m * tail, (p + 1) as nat, m) % m);
    assert(inv_p.u == pile_zeros(5 + m * tail, (p + 1) as nat, m) / m);
    assert(inv_p.q == qw(vk));

    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    let ib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let jt = extract_quint(tm, mk_quint(qc(vk), 5, 5, q_reject, Dir::R));
    crate::tm_cmp_decide::lemma_cmp_tooshort_round(tm, inv_p, qw(vk), qc(vk), q_reject,
        (p + 1) as nat, tail, ib, ic, jt);
    assert(tm_run(tm, inv_p, (p + 2) as nat).q == q_reject);

    lemma_tm_run_split(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat, (p + 2) as nat);
}

} // verus!
