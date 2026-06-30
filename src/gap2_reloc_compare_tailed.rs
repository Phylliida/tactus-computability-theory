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
use crate::tm_cmp_loop::{cmp_quints_present, has_quint};
use crate::tm_cmp_assemble::cmp_accept_fuel;
use crate::tm_cmp_tailed::lemma_cmp_decides_accept_tailed;
use crate::gap2_reloc_compare::{reloc_fuel, reloc_compare_accept_fuel};
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

} // verus!
