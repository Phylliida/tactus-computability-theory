//! # GAP-2 G2-F Route (i) brick R-cmp — u-TAIL-LIFT HALF 2: the tail-safe RELOCATION ∘ COMPARE.
//!
//! Composes HALF 1's tail-safe relocation ([`crate::gap2_reloc::lemma_reloc_local_tailed`]) with the
//! tail-safe comparator ([`crate::tm_cmp_tailed`]) so the whole emit-end → `q_accept`/`q_reject` surface
//! carries the global R-S dovetail's **Control-Zone backup** `T_u` (a high tail on `u`, at digit offset
//! `H = L+1+g+M+1` above the working tape) untouched. The untailed assemblies live in
//! `gap2_reloc_compare.rs` (`lemma_reloc_then_compare_{accept,reject}`); these are their `+ m^H·T_u` lifts,
//! `T_u == 0` recovering them. See `docs/gap2-input-loader-plan.md` §N+31/N+32.
//!
//! This file ships the **ACCEPT** direction (the dovetail "witness found" path → cleanup/origin). The
//! REJECT direction (route a divergence to a reject terminal, advancing the dovetail) follows as a sibling
//! brick — the reject rounds are already `out_rest`-generic, so it threads the tail in their existing
//! above-frontier parameter.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold};
use crate::tm_copy_refresh::{copy_u, lemma_pow_nat_add};
use crate::tm_dwalk_prefix::{drev, lemma_drev_len, lemma_drev_digit_bound};
use crate::gap2_reloc::lemma_reloc_local_tailed;
use crate::tm_cmp_loop::{cmp_quints_present, has_quint, cmp_loop_fuel};
use crate::tm_cmp_assemble::{cmp_accept_fuel, lemma_cmp_decides_mismatch, lemma_cmp_decides_mismatch0,
    lemma_cmp_decides_toolong};
use crate::tm_cmp_tailed::{lemma_cmp_decides_accept_tailed, lemma_cmp_decides_tooshort_tailed};
use crate::gap2_reject_classify::{lemma_reject_u_mismatch, lemma_reject_u_tooshort, lemma_reject_u_toolong,
    cpl, lemma_cpl_le, lemma_cpl_match, lemma_cpl_diff};
use crate::gap2_reloc_compare::{reloc_fuel, reloc_compare_accept_fuel, reject_quints,
    reloc_compare_reject_fuel};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **Relocation → parked entry, TAIL-SAFE (shared core).** As [`crate::gap2_reloc_compare::
/// lemma_reloc_to_parked`] but the emit-end `u` carries a high tail `T_u` above the spent master
/// (`u == copy_u(0,M,g) + m^{g+M+1}·t_u`); [`lemma_reloc_local_tailed`] wipes the master and stamps/transfers
/// the output, landing the comparator's parked entry with the tail lifted to offset `L+1+g+M+1`:
///   `u == dpack(drev(output)) + m^L·5 + m^{L+1+g+M+1}·t_u`, `v == dpack(beta) + m^{|beta|}·5`,
///   `a == 0`, state `q_xfer`. With `t_u == 0` this is `lemma_reloc_to_parked`.
pub proof fn lemma_reloc_to_parked_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        big_m >= 1,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        0 <= i_seek < tm.quints.len(),
        0 <= i_trans < tm.quints.len(),
        0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(),
        0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(),
        0 <= i_sb2 < tm.quints.len(),
        0 <= i_sb3 < tm.quints.len(),
        0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(),
        0 <= j1 < tm.quints.len(),
        0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(),
        0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm,
            TmConfig {
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            reloc_fuel(g, big_m, output.len()))
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5
                        + pow_nat(tm.m, (output.len() + 1 + g + big_m + 1) as nat) * t_u) as nat,
                    v: (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5) as nat,
                    a: 0, q: q_xfer }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let xbeta = (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat;
    assert(w == xbeta * m + 0) by(nonlinear_arith) requires w == m * xbeta;
    verus_group_theory::word_numbering::lemma_div_mod_step(xbeta, m, 0);
    assert(w % m == 0);
    assert(w / m == xbeta);
    lemma_reloc_local_tailed(tm, big_m, g, output, w, t_u, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4,
        j0, j1, j2, j3, j4);
}

/// **R-cmp — the tail-safe RELOCATION ∘ COMPARE ACCEPT assembly.** As [`crate::gap2_reloc_compare::
/// lemma_reloc_then_compare_accept`] but the emit-end `u` carries the Control-Zone backup tail
/// `t_u` (`u == copy_u(0,M,g) + m^{g+M+1}·t_u`). When the relocated output matches the parked α
/// (`drev(output) =~= beta`), the machine runs the tail-safe relocation into the comparator's parked entry
/// (now `u == dpack(beta) + m^L·5 + m^{H}·t_u`, `H = L+1+g+M+1`) and the tail-safe accept decision
/// ([`lemma_cmp_decides_accept_tailed`] with `tail == m^{g+M+1}·t_u`), reaching `q_accept` — the backup
/// `t_u` riding above the far-`5` untouched. Same fuel [`reloc_compare_accept_fuel`] as the untailed
/// assembly; `t_u == 0` recovers it. Requires `n ≥ 5`, `M ≥ 1`, `|output| ≥ 2`, all output digits `1..4`.
pub proof fn lemma_reloc_then_compare_accept_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat,
    // relocation states (q_xfer doubles as the comparator's q_start)
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    // comparator states
    q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_accept: nat,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    // q_clean quints (9)
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    // stamp+transfer quints (5)
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        big_m >= 1,
        output.len() >= 2,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        drev(output) =~= beta,
        // ── relocation quints.
        0 <= i_seek < tm.quints.len(),
        0 <= i_trans < tm.quints.len(),
        0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(),
        0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(),
        0 <= i_sb2 < tm.quints.len(),
        0 <= i_sb3 < tm.quints.len(),
        0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(),
        0 <= j1 < tm.quints.len(),
        0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(),
        0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
        // ── comparator quints (entry state q_xfer == q_start).
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)),
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
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            reloc_compare_accept_fuel(g, big_m, output.len(), beta.len())).q == q_accept,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();

    // ── beta = drev(output): same length, same digit bound 1..4.
    lemma_drev_len(output);
    assert(beta.len() == big_l);
    assert(beta.len() >= 2);
    lemma_drev_digit_bound(output, 4);
    assert forall|k: int| 0 <= k < beta.len() implies 1 <= #[trigger] beta[k] <= 4 by {
        assert(beta[k] == drev(output)[k]);
    }

    // ── tail-safe relocation: emit-end (with backup t_u) → parked entry (tail lifted to offset H).
    let c0 = TmConfig {
        u: (copy_u(0, big_m, g, m) + pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat,
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat,
        a: 0, q: q_s };
    lemma_reloc_to_parked_tailed(tm, big_m, g, output, beta, w, t_u, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let big_h = (big_l + 1 + g + big_m + 1) as nat;
    let c_mid = TmConfig {
        u: (dpack(drev(output), m) + pow_nat(m, big_l) * 5 + pow_nat(m, big_h) * t_u) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // ── recast c_mid into the tailed accept entry: u == dpack(beta) + m^L·(5 + m·tail), tail == m^{g+M+1}·t_u.
    let tail = (pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat;
    assert(dpack(drev(output), m) == dpack(beta, m));
    assert(pow_nat(m, big_l) == pow_nat(m, beta.len()));
    lemma_pow_nat_add(m, (big_l + 1) as nat, (g + big_m + 1) as nat);   // m^H == m^{L+1}·m^{g+M+1}
    assert(((big_l + 1) + (g + big_m + 1)) as nat == big_h);
    lemma_pow_nat_unfold(m, (big_l + 1) as nat);                        // m^{L+1} == m·m^L
    let cacc = TmConfig {
        u: (dpack(beta, m) + pow_nat(m, beta.len()) * (5 + m * tail)) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat,
        a: 0, q: q_xfer };
    assert(c_mid.u == cacc.u) by(nonlinear_arith)
        requires
            c_mid.u == dpack(beta, m) + pow_nat(m, big_l) * 5 + pow_nat(m, big_h) * t_u,
            cacc.u == dpack(beta, m) + pow_nat(m, beta.len()) * (5 + m * tail),
            beta.len() == big_l,
            pow_nat(m, big_h) == pow_nat(m, (big_l + 1) as nat) * pow_nat(m, (g + big_m + 1) as nat),
            pow_nat(m, (big_l + 1) as nat) == m * pow_nat(m, big_l),
            tail == pow_nat(m, (g + big_m + 1) as nat) * t_u;
    assert(c_mid.v == cacc.v);
    assert(c_mid == cacc);
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == cacc);

    // ── tail-safe compare decision: parked entry → q_accept (alpha := beta, q_start := q_xfer).
    lemma_cmp_decides_accept_tailed(tm, qw, qc, qb, qr,
        q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_accept, beta, tail);
    let cmp_fuel = cmp_accept_fuel(beta.len());
    assert(tm_run(tm, cacc, cmp_fuel).q == q_accept);

    // ── compose: reloc_fuel + cmp_fuel == reloc_compare_accept_fuel.
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), cmp_fuel);
    assert((reloc_fuel(g, big_m, big_l) + cmp_fuel) as nat
        == reloc_compare_accept_fuel(g, big_m, big_l, beta.len()));
    assert(tm_run(tm, c0, reloc_compare_accept_fuel(g, big_m, big_l, beta.len()))
        == tm_run(tm, cacc, cmp_fuel));
}

// ─────────────────────────────────────────────────────────────────────────────
// REJECT direction (tail-safe). The mismatch / mismatch0 / too-long cmp decides already take their
// above-frontier rest freely; the tail `m^H·t_u` (H = L+1+g+M+1) absorbs into that rest via a single
// pow split (`out_rest := out_rest + m^{H-offset}·t_u`). Too-short alone needs the tailed cmp lemma.
// ─────────────────────────────────────────────────────────────────────────────

/// **R-cmp — tail-safe MISMATCH terminal (interior `p`).** As [`crate::gap2_reloc_compare::
/// lemma_reloc_then_compare_mismatch`] but the emit-end `u` carries `m^{g+M+1}·t_u`; after relocation the
/// backup rides to offset `H = L+1+g+M+1`, which absorbs into the mismatch round's above-frontier rest
/// `out_rest2 + m^{H-p-1}·t_u`. The mismatch quintuple still fires on the divergent digit `x[p]`.
pub proof fn lemma_reloc_then_compare_mismatch_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat, p: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    q_read_boot: nat, q_reject: nat,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm), tm.n >= 5, big_m >= 1,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        beta.len() >= 2,
        forall|k: int| 0 <= k < beta.len() ==> 1 <= #[trigger] beta[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        1 <= p <= beta.len() - 1,
        p < output.len(),
        forall|i: int| 0 <= i < p ==> drev(output)[i] == beta[i],
        drev(output)[p as int] != beta[p as int],
        0 <= i_seek < tm.quints.len(), 0 <= i_trans < tm.quints.len(), 0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(), 0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(), 0 <= i_sb2 < tm.quints.len(), 0 <= i_sb3 < tm.quints.len(), 0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(), 0 <= j1 < tm.quints.len(), 0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(), 0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(beta[p as int]), drev(output)[p as int], drev(output)[p as int], q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            (reloc_fuel(g, big_m, output.len()) + (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2))) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    let big_l = output.len();
    let x = drev(output);
    let k = x.len();
    lemma_drev_len(output);
    lemma_drev_digit_bound(output, 4);
    let d_o = x[p as int];
    assert(1 <= d_o <= 4);
    let big_h = (big_l + 1 + g + big_m + 1) as nat;
    let out_rest2 = (dpack(x.subrange((p + 1) as int, k as int), m) + pow_nat(m, (k - p - 1) as nat) * 5) as nat;
    let out_rest2_tailed = (out_rest2 + pow_nat(m, (big_h - p - 1) as nat) * t_u) as nat;

    let c0 = TmConfig { u: (copy_u(0, big_m, g, m) + pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat,
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked_tailed(tm, big_m, g, output, beta, w, t_u, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5 + pow_nat(m, big_h) * t_u) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u into the mismatch shape; absorb the tail into out_rest2_tailed (abstract-var steps).
    let base = (dpack(x, m) + pow_nat(m, k) * 5) as nat;
    lemma_reject_u_mismatch(x, beta, p, m);                       // base == bb + pp·(d_o + m·out_rest2)
    let bb = dpack(beta.subrange(0, p as int), m);
    let pp = pow_nat(m, p);
    let pph = pow_nat(m, (big_h - p - 1) as nat);
    let du = (bb + pp * (d_o + m * out_rest2)) as nat;
    assert(base == du);
    // pp·m·pph == m^H  (m^p·m·m^{H-p-1} == m^{p+1}·m^{H-p-1} == m^H).
    lemma_pow_nat_add(m, (p + 1) as nat, (big_h - p - 1) as nat);
    assert(((p + 1) + (big_h - p - 1)) as nat == big_h);
    lemma_pow_nat_unfold(m, (p + 1) as nat);                      // m^{p+1} == m·m^p
    assert(pp * m * pph == pow_nat(m, big_h)) by(nonlinear_arith)
        requires
            pow_nat(m, (p + 1) as nat) * pph == pow_nat(m, big_h),
            pow_nat(m, (p + 1) as nat) == m * pp;
    let cmm = TmConfig {
        u: (bb + pp * (d_o + m * out_rest2_tailed)) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    // cmm.u == du + m^H·t_u  (the tail rides at offset H above the un-tailed shape).
    assert(cmm.u == du + pow_nat(m, big_h) * t_u) by(nonlinear_arith)
        requires
            cmm.u == bb + pp * (d_o + m * (out_rest2 + pph * t_u)),
            du == bb + pp * (d_o + m * out_rest2),
            pp * m * pph == pow_nat(m, big_h);
    assert(c_mid.u == cmm.u);                                     // base + m^H·t_u == du + m^H·t_u
    assert(c_mid == cmm);

    lemma_cmp_decides_mismatch(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_reject, beta, p, d_o, out_rest2_tailed);
    let f = (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat;
    assert(tm_run(tm, cmm, f).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), f);
}

/// **R-cmp — tail-safe MISMATCH0 terminal (`p == 0`).** The first relocated digit differs; the tail
/// absorbs into the low-level rest `out_rest + m^{H-1}·t_u`.
pub proof fn lemma_reloc_then_compare_mismatch0_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    q_read_boot: nat, q_reject: nat,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm), tm.n >= 5, big_m >= 1,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        beta.len() >= 1,
        forall|k: int| 0 <= k < beta.len() ==> 1 <= #[trigger] beta[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        drev(output)[0] != beta[0],
        0 <= i_seek < tm.quints.len(), 0 <= i_trans < tm.quints.len(), 0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(), 0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(), 0 <= i_sb2 < tm.quints.len(), 0 <= i_sb3 < tm.quints.len(), 0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(), 0 <= j1 < tm.quints.len(), 0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(), 0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(beta[0]), drev(output)[0], drev(output)[0], q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            (reloc_fuel(g, big_m, output.len()) + 4) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();
    let x = drev(output);
    let k = x.len();
    lemma_drev_len(output);
    lemma_drev_digit_bound(output, 4);
    let d_o = x[0];
    assert(1 <= d_o <= 4);
    let big_h = (big_l + 1 + g + big_m + 1) as nat;
    let out_rest = (dpack(x.drop_first(), m) + pow_nat(m, (k - 1) as nat) * 5) as nat;
    let out_rest_tailed = (out_rest + pow_nat(m, (big_h - 1) as nat) * t_u) as nat;

    let c0 = TmConfig { u: (copy_u(0, big_m, g, m) + pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat,
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked_tailed(tm, big_m, g, output, beta, w, t_u, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5 + pow_nat(m, big_h) * t_u) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u == d_o + m·out_rest_tailed (abstract-var steps: peel low digit, then absorb tail).
    assert(k >= 1);
    assert(dpack(x, m) == x[0] + m * dpack(x.drop_first(), m));   // dpack unfold (x nonempty)
    lemma_pow_nat_unfold(m, k);                                   // m^k == m·m^{k-1}
    lemma_pow_nat_unfold(m, big_h);                              // m^H == m·m^{H-1}
    let base = (dpack(x, m) + pow_nat(m, k) * 5) as nat;
    let alow = dpack(x.drop_first(), m);
    let p1 = pow_nat(m, (k - 1) as nat);
    let ph1 = pow_nat(m, (big_h - 1) as nat);
    let du = (d_o + m * out_rest) as nat;
    // base == du  (peel: dpack(x)+m^k·5 == x[0] + m·(alow + m^{k-1}·5)).
    assert(base == du) by(nonlinear_arith)
        requires
            base == dpack(x, m) + pow_nat(m, k) * 5,
            dpack(x, m) == x[0] + m * alow,
            pow_nat(m, k) == m * p1,
            out_rest == alow + p1 * 5,
            du == d_o + m * out_rest,
            d_o == x[0];
    let cmm = TmConfig { u: (d_o + m * out_rest_tailed) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    // cmm.u == du + m^H·t_u  (the tail rides at offset H above the un-tailed shape).
    assert(cmm.u == du + pow_nat(m, big_h) * t_u) by(nonlinear_arith)
        requires
            cmm.u == d_o + m * (out_rest + ph1 * t_u),
            du == d_o + m * out_rest,
            pow_nat(m, big_h) == m * ph1;
    assert(c_mid.u == cmm.u);                                     // base + m^H·t_u == du + m^H·t_u
    assert(c_mid == cmm);

    lemma_cmp_decides_mismatch0(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_reject, beta, d_o, out_rest_tailed);
    assert(tm_run(tm, cmm, 4).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), 4);
}

/// **R-cmp — tail-safe TOO-SHORT terminal.** The relocated output is a proper prefix of α (`p == |output|
/// < |beta|`); the output far-`5` sits at the cut, the backup `t_u` riding above it via the tailed
/// too-short cmp lemma (`tail == m^{H-p-1}·t_u`).
pub proof fn lemma_reloc_then_compare_tooshort_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat, p: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    q_read_boot: nat, q_reject: nat,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm), tm.n >= 5, big_m >= 1,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        beta.len() >= 2,
        forall|k: int| 0 <= k < beta.len() ==> 1 <= #[trigger] beta[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        1 <= p <= beta.len() - 1,
        p == output.len(),
        forall|i: int| 0 <= i < p ==> drev(output)[i] == beta[i],
        0 <= i_seek < tm.quints.len(), 0 <= i_trans < tm.quints.len(), 0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(), 0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(), 0 <= i_sb2 < tm.quints.len(), 0 <= i_sb3 < tm.quints.len(), 0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(), 0 <= j1 < tm.quints.len(), 0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(), 0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(beta[p as int]), 5, 5, q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            (reloc_fuel(g, big_m, output.len()) + (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2))) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    let big_l = output.len();
    let x = drev(output);
    let k = x.len();
    lemma_drev_len(output);
    lemma_drev_digit_bound(output, 4);
    let big_h = (big_l + 1 + g + big_m + 1) as nat;

    let c0 = TmConfig { u: (copy_u(0, big_m, g, m) + pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat,
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked_tailed(tm, big_m, g, output, beta, w, t_u, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5 + pow_nat(m, big_h) * t_u) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u into the tailed too-short shape (far-5 + tail at out-level p).
    let base = (dpack(x, m) + pow_nat(m, k) * 5) as nat;
    lemma_reject_u_tooshort(x, beta, p, m);                       // base == bb + pp·5
    let bb = dpack(beta.subrange(0, p as int), m);
    let pp = pow_nat(m, p);
    let pph = pow_nat(m, (big_h - p - 1) as nat);
    let du = (bb + pp * 5) as nat;
    assert(base == du);
    let tail_ts = (pph * t_u) as nat;
    lemma_pow_nat_add(m, (p + 1) as nat, (big_h - p - 1) as nat);
    assert(((p + 1) + (big_h - p - 1)) as nat == big_h);
    lemma_pow_nat_unfold(m, (p + 1) as nat);
    assert(pp * m * pph == pow_nat(m, big_h)) by(nonlinear_arith)
        requires
            pow_nat(m, (p + 1) as nat) * pph == pow_nat(m, big_h),
            pow_nat(m, (p + 1) as nat) == m * pp;
    let cts = TmConfig {
        u: (bb + pp * (5 + m * tail_ts)) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(cts.u == du + pow_nat(m, big_h) * t_u) by(nonlinear_arith)
        requires
            cts.u == bb + pp * (5 + m * (pph * t_u)),
            du == bb + pp * 5,
            pp * m * pph == pow_nat(m, big_h);
    assert(c_mid.u == cts.u);
    assert(c_mid == cts);

    lemma_cmp_decides_tooshort_tailed(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_reject, beta, p, tail_ts);
    let f = (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat;
    assert(tm_run(tm, cts, f).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), f);
}

/// **R-cmp — tail-safe TOO-LONG terminal.** α is a proper prefix of the relocated output; after the full
/// match the surviving output digit `x[|beta|]` fires the too-long reject, the backup riding in the
/// too-long round's above-frontier rest `out_rest2 + m^{H-L-1}·t_u`.
pub proof fn lemma_reloc_then_compare_toolong_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_reject: nat,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm), tm.n >= 5, big_m >= 1,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        beta.len() >= 2,
        forall|k: int| 0 <= k < beta.len() ==> 1 <= #[trigger] beta[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        beta.len() < output.len(),
        forall|i: int| 0 <= i < beta.len() ==> drev(output)[i] == beta[i],
        0 <= i_seek < tm.quints.len(), 0 <= i_trans < tm.quints.len(), 0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(), 0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(), 0 <= i_sb2 < tm.quints.len(), 0 <= i_sb3 < tm.quints.len(), 0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(), 0 <= j1 < tm.quints.len(), 0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(), 0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)),
        has_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, drev(output)[beta.len() as int], drev(output)[beta.len() as int], q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            (reloc_fuel(g, big_m, output.len())
                + (8 + cmp_loop_fuel(1, 2, (beta.len() - 2) as nat) + (2 * (beta.len() - 1) + 3 * beta.len() + 6))) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    let big_l = output.len();
    let x = drev(output);
    let k = x.len();
    let lb = beta.len();
    lemma_drev_len(output);
    lemma_drev_digit_bound(output, 4);
    let d_o2 = x[lb as int];
    assert(1 <= d_o2 <= 4);
    let big_h = (big_l + 1 + g + big_m + 1) as nat;
    let out_rest2 = (dpack(x.subrange((lb + 1) as int, k as int), m) + pow_nat(m, (k - lb - 1) as nat) * 5) as nat;
    let phl = pow_nat(m, (big_h - lb - 1) as nat);
    let out_rest2_tailed = (out_rest2 + phl * t_u) as nat;

    let c0 = TmConfig { u: (copy_u(0, big_m, g, m) + pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat,
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked_tailed(tm, big_m, g, output, beta, w, t_u, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5 + pow_nat(m, big_h) * t_u) as nat,
        v: (dpack(beta, m) + pow_nat(m, lb) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u into the too-long shape; absorb the tail into out_rest2_tailed (offset L+1).
    let base = (dpack(x, m) + pow_nat(m, k) * 5) as nat;
    lemma_reject_u_toolong(x, beta, m);                          // base == du (un-tailed too-long shape)
    let bb = dpack(beta.subrange(0, (lb - 1) as int), m);
    let pq = pow_nat(m, (lb - 1) as nat);
    let bl1 = beta[(lb - 1) as int];
    let inner = (d_o2 + m * out_rest2) as nat;
    let inner_t = (d_o2 + m * out_rest2_tailed) as nat;
    let du = (bb + pq * (bl1 + m * inner)) as nat;
    assert(base == du);
    // q3 == pq·m·m·phl == m^H.
    let q2 = (m * phl) as nat;
    let q3 = (pq * m * q2) as nat;
    lemma_pow_nat_unfold(m, (big_h - lb) as nat);               // m^{H-L} == m·m^{H-L-1}
    assert(q2 == pow_nat(m, (big_h - lb) as nat));
    lemma_pow_nat_unfold(m, lb);                                // m^L == m·m^{L-1}
    lemma_pow_nat_add(m, lb, (big_h - lb) as nat);              // m^L·m^{H-L} == m^H
    assert((lb + (big_h - lb)) as nat == big_h);
    assert(q3 == pow_nat(m, big_h)) by(nonlinear_arith)
        requires
            q3 == pq * m * q2,
            pow_nat(m, lb) == m * pq,
            q2 == pow_nat(m, (big_h - lb) as nat),
            pow_nat(m, lb) * pow_nat(m, (big_h - lb) as nat) == pow_nat(m, big_h);
    // inner_t == inner + q2·t_u  (level-1 absorb).
    assert(inner_t == inner + q2 * t_u) by(nonlinear_arith)
        requires
            inner_t == d_o2 + m * (out_rest2 + phl * t_u),
            inner == d_o2 + m * out_rest2,
            q2 == m * phl;
    let ctl = TmConfig {
        u: (bb + pq * (bl1 + m * inner_t)) as nat,
        v: (dpack(beta, m) + pow_nat(m, lb) * 5) as nat, a: 0, q: q_xfer };
    // ctl.u == du + m^H·t_u  (outer absorb: ctl.u - du == pq·m·(inner_t - inner) == q3·t_u).
    assert(ctl.u == du + pow_nat(m, big_h) * t_u) by(nonlinear_arith)
        requires
            ctl.u == bb + pq * (bl1 + m * inner_t),
            du == bb + pq * (bl1 + m * inner),
            inner_t == inner + q2 * t_u,
            q3 == pq * m * q2,
            q3 == pow_nat(m, big_h);
    assert(c_mid.u == ctl.u);
    assert(c_mid == ctl);

    lemma_cmp_decides_toolong(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_reject,
        beta, d_o2, out_rest2_tailed);
    let f = (8 + cmp_loop_fuel(1, 2, (lb - 2) as nat) + (2 * (lb - 1) + 3 * lb + 6)) as nat;
    assert(tm_run(tm, ctl, f).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), f);
}

/// **R-cmp — the tail-safe RELOCATION ∘ COMPARE DECIDES (reject direction).** As [`crate::gap2_reloc_compare::
/// lemma_reloc_then_compare_reject`] but the emit-end `u` carries the Control-Zone backup `t_u`. When
/// `drev(output) != beta`, the machine relocates and the comparator reaches `q_reject`, routing by
/// common-prefix length `p == cpl(drev(output), beta)` to a tailed terminal — the backup `t_u` riding
/// above the working tape untouched. Same fuel [`reloc_compare_reject_fuel`]; `t_u == 0` recovers the
/// untailed dispatch. Requires the [`reject_quints`] bundle.
pub proof fn lemma_reloc_then_compare_reject_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, t_u: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
    q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_reject: nat,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    j0: int, j1: int, j2: int, j3: int, j4: int,
)
    requires
        tm_wf(tm), tm.n >= 5, big_m >= 1,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        beta.len() >= 2,
        forall|k: int| 0 <= k < beta.len() ==> 1 <= #[trigger] beta[k] <= 4,
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        drev(output) != beta,
        // relocation quints.
        0 <= i_seek < tm.quints.len(), 0 <= i_trans < tm.quints.len(), 0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(), 0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(), 0 <= i_sb2 < tm.quints.len(), 0 <= i_sb3 < tm.quints.len(), 0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_reloc, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_reloc, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_reloc, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_reloc, Dir::L),
        0 <= j0 < tm.quints.len(), 0 <= j1 < tm.quints.len(), 0 <= j2 < tm.quints.len(),
        0 <= j3 < tm.quints.len(), 0 <= j4 < tm.quints.len(),
        tm.quints[j0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[j1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[j2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[j3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[j4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
        // comparator reject-quint bundle.
        reject_quints(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_reject),
    ensures
        tm_run(tm,
            TmConfig {
                u: (copy_u(0, big_m, g, tm.m) + pow_nat(tm.m, (g + big_m + 1) as nat) * t_u) as nat,
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            reloc_compare_reject_fuel(g, big_m, output, beta)).q == q_reject,
{
    let m = tm.m;
    let big_l = output.len();
    let x = drev(output);
    let k = x.len();
    let lb = beta.len();
    lemma_drev_len(output);                                   // k == big_l
    lemma_drev_digit_bound(output, 4);                        // x digits 1..4
    let p = cpl(x, beta);
    lemma_cpl_le(x, beta);                                    // p <= k, p <= lb
    lemma_cpl_match(x, beta);                                 // x[i]==beta[i] for i<p

    if p < k && p < lb {
        lemma_cpl_diff(x, beta);                              // x[p] != beta[p]
        if p == 0 {
            assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
            assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
            assert(has_quint(tm, mk_quint(qc(beta[0]), x[0], x[0], q_reject, Dir::R)));
            lemma_reloc_then_compare_mismatch0_tailed(tm, big_m, g, output, beta, w, t_u,
                q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_reject, qw, qc, qb, qr,
                i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
        } else {
            assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
            assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
            assert(has_quint(tm, mk_quint(qc(beta[p as int]), x[p as int], x[p as int], q_reject, Dir::R)));
            lemma_reloc_then_compare_mismatch_tailed(tm, big_m, g, output, beta, w, t_u, p,
                q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_reject, qw, qc, qb, qr,
                i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
        }
    } else if p == k {
        if p == lb {
            assert(x =~= beta) by {
                assert forall|i: int| 0 <= i < k implies x[i] == beta[i] by { }
            }
            assert(false);
        }
        assert(p < lb);
        assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
        assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
        assert(has_quint(tm, mk_quint(qc(beta[p as int]), 5, 5, q_reject, Dir::R)));
        lemma_reloc_then_compare_tooshort_tailed(tm, big_m, g, output, beta, w, t_u, p,
            q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_reject, qw, qc, qb, qr,
            i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    } else {
        assert(p == lb);
        assert(p < k);
        assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
        assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
        assert(has_quint(tm, mk_quint(q_verify_cmp, x[lb as int], x[lb as int], q_reject, Dir::R)));
        lemma_reloc_then_compare_toolong_tailed(tm, big_m, g, output, beta, w, t_u,
            q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_reject, qw, qc, qb, qr,
            i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    }
}

} // verus!
