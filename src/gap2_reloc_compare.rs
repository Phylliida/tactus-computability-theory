//! # GAP-2 G2-F Route (i) — the RELOCATION ∘ COMPARE assembly (the emit→decide coupling).
//!
//! Composes the two pinned, separately-verified contracts of the R-cmp frontier:
//!   * the **relocation** ([`crate::gap2_reloc::lemma_reloc_local`]) — WIPE ∘ STAMP+TRANSFER, which from the
//!     emit-end tape (`u == copy_u(0,M,g)` spent master · `v == dpack(output) + m^L·w`, head on the boundary
//!     `a == 0`, state `q_s`) produces the comparator's **parked entry** (`u == dpack(drev(output)) + m^L·5`,
//!     `v == w/m`, `a == 0`, state `q_xfer`);
//!   * the **compare decision** ([`crate::tm_cmp_assemble::lemma_cmp_decides_accept`]) — which from that
//!     parked entry reaches `q_accept` exactly when the relocated output digit-string equals the parked α.
//!
//! The relocation's deliverable IS the comparator's `requires`, so the assembly is a clean composition glued
//! by [`crate::tm_run_lemmas::lemma_tm_run_split`]. **The splice is state identification** — the relocation
//! exits in `q_xfer` scanning `a == 0`, which is precisely the comparator's `q_start` (we pass the SAME state
//! for both). **The value bridge** is `drev`: the relocation lands the output *reversed* on `u`
//! (a rightward digit-walk reverses), and α is parked *reversed* on `v` ([`crate::tm_rp`]), so the comparator
//! compares `drev(output)` against `drev(α)` — equal iff `output == α` ([`crate::tm_dwalk_prefix::drev`] is an
//! involution, and preserves the digit bound). Here we phrase α by the digit-string `beta` that physically
//! sits reversed on `v` (so `beta == drev(α)`); the accept premise `drev(output) =~= beta` reads, in forward
//! terms, as `output =~= α`.
//!
//! This file builds the **ACCEPT** direction (the dovetail "witness found" path → halt/origin). The REJECT
//! direction (route a divergence to one of the four reject terminals) is a follow-up brick. Both are
//! layout-independent: they live in the relocation's LOCAL frame, needing none of the deferred R-S/dovetail
//! `u`-tail layout (the relocation is `tail_safe`). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold};
use crate::tm_dwalk_prefix::{drev, lemma_drev_len, lemma_drev_digit_bound};
use crate::tm_copy_refresh::copy_u;
use crate::gap2_master_mgmt::q_clean_fuel;
use crate::gap2_reloc::lemma_reloc_local;
use crate::tm_cmp_loop::{cmp_quints_present, has_quint, cmp_loop_fuel};
use crate::tm_cmp_assemble::{lemma_cmp_decides_accept, cmp_accept_fuel,
    lemma_cmp_decides_mismatch, lemma_cmp_decides_tooshort, lemma_cmp_decides_toolong,
    lemma_cmp_decides_mismatch0};
use crate::gap2_reject_classify::{lemma_reject_u_mismatch, lemma_reject_u_tooshort, lemma_reject_u_toolong,
    cpl, lemma_cpl_le, lemma_cpl_match, lemma_cpl_diff};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// The total fuel of the emit-end → `q_accept` run: the relocation (`q_clean_fuel(g,M) + 1 + |output|`) plus
/// the compare's accept chain ([`cmp_accept_fuel`]`(|beta|)`).
pub open spec fn reloc_compare_accept_fuel(g: nat, big_m: nat, big_l: nat, beta_len: nat) -> nat {
    (q_clean_fuel(g, big_m) + 1 + big_l + cmp_accept_fuel(beta_len)) as nat
}

/// **R-cmp — the RELOCATION ∘ COMPARE ACCEPT assembly.** From the emit-end tape
///   `u == copy_u(0,M,g)` (the spent emit-scratch master),
///   `v == dpack(output) + m^L·w`  with `w == m·(dpack(beta) + m^{|beta|}·5)` (output low-first, a one-cell
///        gap `0`, then the parked-reversed-α block `beta` with its far-`5` ceiling),
///   `a == 0` on the boundary, state `q_s`,
/// when the relocated output matches the parked α (`drev(output) =~= beta`), the machine runs the relocation
/// (`q_clean` wipe ∘ stamp+transfer) into the comparator's parked entry, then the compare decision, reaching
/// `q_accept`. The relocation exit state `q_xfer` IS the comparator's `q_start` (state identification, no
/// glue). Requires `n ≥ 5`, `M ≥ 1`, `|output| ≥ 2`, all output digits `1..4`.
pub proof fn lemma_reloc_then_compare_accept(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat,
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
        // the parked α-block value, packaged as the above-output v-tail (gap `0`, then `beta`).
        w == tm.m * (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5),
        // the accept premise: the relocated (reversed) output equals the parked (reversed) α.
        drev(output) =~= beta,
        // ── relocation quints (states q_s -> q_w -> q_r -> q_reloc -> q_xfer), see lemma_reloc_local.
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
        // ── comparator quints (entry state q_xfer == q_start), see lemma_cmp_decides_accept.
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
                u: copy_u(0, big_m, g, tm.m),
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            reloc_compare_accept_fuel(g, big_m, output.len(), beta.len())).q == q_accept,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();

    // ── beta = drev(output): same length, same digit bound 1..4.
    lemma_drev_len(output);                                   // |drev(output)| == |output|
    assert(beta.len() == big_l);
    assert(beta.len() >= 2);
    lemma_drev_digit_bound(output, 4);                        // drev(output) digits 1..4
    assert forall|k: int| 0 <= k < beta.len() implies 1 <= #[trigger] beta[k] <= 4 by {
        assert(beta[k] == drev(output)[k]);
    }

    // ── the parked α-block value (the comparator's u == v in the accept case).
    let xbeta = (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat;
    // w == m·xbeta == xbeta·m + 0, so w % m == 0 and w / m == xbeta.
    assert(w == xbeta * m + 0) by(nonlinear_arith) requires w == m * xbeta;
    verus_group_theory::word_numbering::lemma_div_mod_step(xbeta, m, 0);
    assert(w % m == 0);
    assert(w / m == xbeta);

    // ── relocation: emit-end → parked entry (local frame).
    let c0 = TmConfig {
        u: copy_u(0, big_m, g, m),
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat,
        a: 0, q: q_s };
    lemma_reloc_local(tm, big_m, g, output, w, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4,
        j0, j1, j2, j3, j4);
    let reloc_fuel = (q_clean_fuel(g, big_m) + 1 + big_l) as nat;
    let c_mid = TmConfig {
        u: (dpack(drev(output), m) + pow_nat(m, big_l) * 5) as nat,
        v: (w / m), a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel) == c_mid);

    // ── recognize c_mid as the comparator's accept entry (built from beta).
    let cacc = TmConfig {
        u: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat,
        a: 0, q: q_xfer };
    // u: dpack(drev(output)) == dpack(beta) (same seq); m^L == m^{|beta|}.
    assert(dpack(drev(output), m) == dpack(beta, m));
    assert(pow_nat(m, big_l) == pow_nat(m, beta.len()));
    assert(c_mid.u == cacc.u);
    // v: w/m == xbeta == cacc.v.
    assert(c_mid.v == cacc.v);
    assert(c_mid == cacc);
    assert(tm_run(tm, c0, reloc_fuel) == cacc);

    // ── compare decision: parked entry → q_accept (alpha := beta, q_start := q_xfer).
    lemma_cmp_decides_accept(tm, qw, qc, qb, qr,
        q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_accept, beta);
    let cmp_fuel = cmp_accept_fuel(beta.len());
    assert(tm_run(tm, cacc, cmp_fuel).q == q_accept);

    // ── compose: reloc_fuel + cmp_fuel.
    lemma_tm_run_split(tm, c0, reloc_fuel, cmp_fuel);
    assert((reloc_fuel + cmp_fuel) as nat == reloc_compare_accept_fuel(g, big_m, big_l, beta.len()));
    assert(tm_run(tm, c0, reloc_compare_accept_fuel(g, big_m, big_l, beta.len())) == tm_run(tm, cacc, cmp_fuel));
}

// ─────────────────────────────────────────────────────────────────────────────
// REJECT direction — the relocation produces the comparator's parked entry; each terminal then fires.
// ─────────────────────────────────────────────────────────────────────────────

/// The relocation fuel `q_clean_fuel(g,M) + 1 + |output|` (shared across the accept/reject assemblies).
pub open spec fn reloc_fuel(g: nat, big_m: nat, big_l: nat) -> nat {
    (q_clean_fuel(g, big_m) + 1 + big_l) as nat
}

/// **Relocation → parked entry (shared core).** Runs [`lemma_reloc_local`] from the emit-end tape and
/// re-packages the `v`-tail `w == m·(dpack(beta) + m^{|beta|}·5)` as the comparator's parked α-block. The
/// result `u == dpack(drev(output)) + m^L·5` (output reversed, far-`5` ceiling), `v == dpack(beta) + m^{|β|}·5`
/// (the parked-reversed α), `a == 0` (the `g=1` boundary), state `q_xfer` — exactly the comparator's entry.
pub proof fn lemma_reloc_to_parked(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat,
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
                u: copy_u(0, big_m, g, tm.m),
                v: (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
                a: 0, q: q_s },
            reloc_fuel(g, big_m, output.len()))
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5) as nat,
                    v: (dpack(beta, tm.m) + pow_nat(tm.m, beta.len()) * 5) as nat,
                    a: 0, q: q_xfer }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();
    let xbeta = (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat;
    assert(w == xbeta * m + 0) by(nonlinear_arith) requires w == m * xbeta;
    verus_group_theory::word_numbering::lemma_div_mod_step(xbeta, m, 0);
    assert(w / m == xbeta);
    lemma_reloc_local(tm, big_m, g, output, w, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4,
        j0, j1, j2, j3, j4);
}

/// **R-cmp — RELOCATION ∘ COMPARE, MISMATCH terminal.** The relocated output diverges from α at an interior
/// position `p` (`drev(output)[0..p] == beta[0..p]`, `drev(output)[p] ≠ beta[p]`, both digits `1..4`,
/// `1 ≤ p ≤ |beta|-1`, `p < |output|`): the machine relocates, then the comparator's mismatch round fires →
/// `q_reject`. (`beta` is the parked-reversed α; `drev(output)` the relocated reversed output.)
pub proof fn lemma_reloc_then_compare_mismatch(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, p: nat,
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
        // comparator quints (entry state q_xfer).
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(beta[p as int]), drev(output)[p as int], drev(output)[p as int], q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: copy_u(0, big_m, g, tm.m),
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
    lemma_drev_digit_bound(output, 4);                       // x digits 1..4
    let d_o = x[p as int];
    assert(1 <= d_o <= 4);
    let out_rest2 = (dpack(x.subrange((p + 1) as int, k as int), m) + pow_nat(m, (k - p - 1) as nat) * 5) as nat;

    // emit-end -> parked entry.
    let c0 = TmConfig { u: copy_u(0, big_m, g, m),
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked(tm, big_m, g, output, beta, w, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u into the mismatch terminal's u shape.
    lemma_reject_u_mismatch(x, beta, p, m);
    let cmm = TmConfig {
        u: (dpack(beta.subrange(0, p as int), m) + pow_nat(m, p) * (d_o + m * out_rest2)) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(c_mid.u == cmm.u);
    assert(c_mid == cmm);

    // fire the mismatch terminal.
    lemma_cmp_decides_mismatch(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_reject, beta, p, d_o, out_rest2);
    let f = (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat;
    assert(tm_run(tm, cmm, f).q == q_reject);

    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), f);
}

/// **R-cmp — RELOCATION ∘ COMPARE, MISMATCH0 terminal (`p == 0`).** The very first relocated digit differs
/// from α (`drev(output)[0] ≠ beta[0]`): relocate, then the first-digit mismatch fires → `q_reject` (fuel 4).
pub proof fn lemma_reloc_then_compare_mismatch0(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat,
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
                u: copy_u(0, big_m, g, tm.m),
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
    let out_rest = (dpack(x.drop_first(), m) + pow_nat(m, (k - 1) as nat) * 5) as nat;

    let c0 = TmConfig { u: copy_u(0, big_m, g, m),
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked(tm, big_m, g, output, beta, w, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // c_mid.u == d_o + m·out_rest  (peel the low digit; far-5 rides in out_rest).
    assert(k >= 1);
    assert(dpack(x, m) == x[0] + m * dpack(x.drop_first(), m));   // dpack unfold (x nonempty)
    lemma_pow_nat_unfold(m, k);                                   // m^k == m·m^{k-1}
    assert(c_mid.u == d_o + m * out_rest) by(nonlinear_arith)
        requires
            c_mid.u == dpack(x, m) + pow_nat(m, k) * 5,
            dpack(x, m) == x[0] + m * dpack(x.drop_first(), m),
            pow_nat(m, k) == m * pow_nat(m, (k - 1) as nat),
            out_rest == dpack(x.drop_first(), m) + pow_nat(m, (k - 1) as nat) * 5,
            d_o == x[0];
    let cmm = TmConfig { u: (d_o + m * out_rest) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(c_mid == cmm);

    lemma_cmp_decides_mismatch0(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_reject, beta, d_o, out_rest);
    assert(tm_run(tm, cmm, 4).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), 4);
}

/// **R-cmp — RELOCATION ∘ COMPARE, TOO-SHORT terminal.** The relocated output is a proper prefix of α
/// (`drev(output)[0..p] == beta[0..p]`, `|output| == p < |beta|`): relocate, then the output's far-`5`
/// sentinel is read at the gap-cross while α still has `beta[p]` → `q_reject`.
pub proof fn lemma_reloc_then_compare_tooshort(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat, p: nat,
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
                u: copy_u(0, big_m, g, tm.m),
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

    let c0 = TmConfig { u: copy_u(0, big_m, g, m),
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked(tm, big_m, g, output, beta, w, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u into the too-short terminal's u shape (p == k == |x|).
    lemma_reject_u_tooshort(x, beta, p, m);
    let cts = TmConfig {
        u: (dpack(beta.subrange(0, p as int), m) + pow_nat(m, p) * 5) as nat,
        v: (dpack(beta, m) + pow_nat(m, beta.len()) * 5) as nat, a: 0, q: q_xfer };
    assert(c_mid.u == cts.u);
    assert(c_mid == cts);

    lemma_cmp_decides_tooshort(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_reject, beta, p);
    let f = (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat;
    assert(tm_run(tm, cts, f).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), f);
}

/// **R-cmp — RELOCATION ∘ COMPARE, TOO-LONG terminal.** α is a proper prefix of the relocated output
/// (`drev(output)[0..|beta|] == beta`, then `drev(output)[|beta|] ∈ 1..4`): relocate, the comparator matches
/// all of α, then the verify gap-cross reads the surviving output digit → `q_reject`.
pub proof fn lemma_reloc_then_compare_toolong(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat,
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
                u: copy_u(0, big_m, g, tm.m),
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
    lemma_drev_digit_bound(output, 4);                       // x digits 1..4
    let d_o2 = x[lb as int];
    assert(1 <= d_o2 <= 4);
    let out_rest2 = (dpack(x.subrange((lb + 1) as int, k as int), m) + pow_nat(m, (k - lb - 1) as nat) * 5) as nat;

    let c0 = TmConfig { u: copy_u(0, big_m, g, m),
        v: (dpack(output, m) + pow_nat(m, big_l) * w) as nat, a: 0, q: q_s };
    lemma_reloc_to_parked(tm, big_m, g, output, beta, w, q_s, q_w, q_r, q_reloc, q_xfer,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    let c_mid = TmConfig {
        u: (dpack(x, m) + pow_nat(m, k) * 5) as nat,
        v: (dpack(beta, m) + pow_nat(m, lb) * 5) as nat, a: 0, q: q_xfer };
    assert(tm_run(tm, c0, reloc_fuel(g, big_m, big_l)) == c_mid);

    // recast c_mid.u into the too-long terminal's u shape.
    lemma_reject_u_toolong(x, beta, m);
    let ctl = TmConfig {
        u: (dpack(beta.subrange(0, (lb - 1) as int), m)
             + pow_nat(m, (lb - 1) as nat)
               * (beta[(lb - 1) as int] + m * (d_o2 + m * out_rest2))) as nat,
        v: (dpack(beta, m) + pow_nat(m, lb) * 5) as nat, a: 0, q: q_xfer };
    assert(c_mid.u == ctl.u);
    assert(c_mid == ctl);

    lemma_cmp_decides_toolong(tm, qw, qc, qb, qr, q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_reject,
        beta, d_o2, out_rest2);
    let f = (8 + cmp_loop_fuel(1, 2, (lb - 2) as nat) + (2 * (lb - 1) + 3 * lb + 6)) as nat;
    assert(tm_run(tm, ctl, f).q == q_reject);
    lemma_tm_run_split(tm, c0, reloc_fuel(g, big_m, big_l), f);
}

// ─────────────────────────────────────────────────────────────────────────────
// Generic REJECT dispatch — output ≠ α routes (by common-prefix length) to one terminal.
// ─────────────────────────────────────────────────────────────────────────────

/// **The comparator's reject-quint bundle.** Every quintuple the four reject terminals can consume, over the
/// whole digit alphabet `1..4`: the match machinery ([`cmp_quints_present`]), the entry handshake, the
/// per-first-digit bootstrap read, the per-`(V≠d)` mismatch reject, the per-`V` too-short reject, and the
/// verify chain with its per-digit too-long reject. A faithful over-approximation of the quint set the real
/// `psc_tm` carries; the deterministic comparator never has a state/symbol collision (the reject symbols are
/// disjoint from the match symbol `V` and the gap `0`).
pub open spec fn reject_quints(
    tm: Tm, qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_xfer: nat, q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_reject: nat,
) -> bool {
    &&& (forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V))
    &&& has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R))
    &&& (forall|V: nat| #![trigger mk_quint(q_read_boot, V, 5, qw(V), Dir::L)]
            1 <= V <= 4 ==> has_quint(tm, mk_quint(q_read_boot, V, 5, qw(V), Dir::L)))
    &&& (forall|V: nat, d: nat| #![trigger mk_quint(qc(V), d, d, q_reject, Dir::R)]
            1 <= V <= 4 && 1 <= d <= 4 && d != V ==> has_quint(tm, mk_quint(qc(V), d, d, q_reject, Dir::R)))
    &&& (forall|V: nat| #![trigger mk_quint(qc(V), 5, 5, q_reject, Dir::R)]
            1 <= V <= 4 ==> has_quint(tm, mk_quint(qc(V), 5, 5, q_reject, Dir::R)))
    &&& has_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L))
    &&& has_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L))
    &&& has_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L))
    &&& has_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L))
    &&& has_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L))
    &&& has_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L))
    &&& has_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L))
    &&& (forall|d: nat| #![trigger mk_quint(q_verify_cmp, d, d, q_reject, Dir::R)]
            1 <= d <= 4 ==> has_quint(tm, mk_quint(q_verify_cmp, d, d, q_reject, Dir::R)))
}

/// The exact reject fuel: the relocation plus the terminal selected by the common-prefix length
/// `p == cpl(drev(output), beta)`.
pub open spec fn reloc_compare_reject_fuel(g: nat, big_m: nat, output: Seq<nat>, beta: Seq<nat>) -> nat {
    let r = reloc_fuel(g, big_m, output.len());
    let x = drev(output);
    let p = cpl(x, beta);
    let c =
        if p < x.len() && p < beta.len() {
            if p == 0 { 4nat } else { (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat }
        } else if p == x.len() {
            (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat
        } else {
            (8 + cmp_loop_fuel(1, 2, (beta.len() - 2) as nat) + (2 * (beta.len() - 1) + 3 * beta.len() + 6)) as nat
        };
    (r + c) as nat
}

/// **R-cmp — the RELOCATION ∘ COMPARE DECIDES (reject direction).** When the relocated output differs from
/// the parked α (`drev(output) != beta`), the machine relocates and the comparator reaches `q_reject`. The
/// routing is by common-prefix length `p == cpl(drev(output), beta)`: interior divergence → mismatch /
/// mismatch0, output-exhausts → too-short, output-overruns → too-long. Together with
/// [`lemma_reloc_then_compare_accept`] this is the full DECIDES surface: the emit-end machine reaches
/// `q_accept` iff `output == α`, else `q_reject`. Requires the [`reject_quints`] bundle.
pub proof fn lemma_reloc_then_compare_reject(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, beta: Seq<nat>, w: nat,
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
                u: copy_u(0, big_m, g, tm.m),
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
            // first-digit mismatch.
            assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
            assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
            assert(has_quint(tm, mk_quint(qc(beta[0]), x[0], x[0], q_reject, Dir::R)));
            lemma_reloc_then_compare_mismatch0(tm, big_m, g, output, beta, w,
                q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_reject, qw, qc, qb, qr,
                i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
        } else {
            // interior mismatch at p.
            assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
            assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
            assert(has_quint(tm, mk_quint(qc(beta[p as int]), x[p as int], x[p as int], q_reject, Dir::R)));
            lemma_reloc_then_compare_mismatch(tm, big_m, g, output, beta, w, p,
                q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_reject, qw, qc, qb, qr,
                i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
        }
    } else if p == k {
        // output is a proper prefix of α (p == |x| < |beta|: rule out p == lb via X != beta).
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
        lemma_reloc_then_compare_tooshort(tm, big_m, g, output, beta, w, p,
            q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_reject, qw, qc, qb, qr,
            i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    } else {
        // p == lb < k: α is a proper prefix of the output (too-long).
        assert(p == lb);                                     // from cpl_le (p<=lb) + !(p<lb path) reasoning
        assert(p < k);                                       // p == lb, and !(p == k) with p<=k ⟹ p<k
        assert(has_quint(tm, mk_quint(q_xfer, 0, 0, q_read_boot, Dir::R)));
        assert(has_quint(tm, mk_quint(q_read_boot, beta[0], 5, qw(beta[0]), Dir::L)));
        assert(has_quint(tm, mk_quint(q_verify_cmp, x[lb as int], x[lb as int], q_reject, Dir::R)));
        lemma_reloc_then_compare_toolong(tm, big_m, g, output, beta, w,
            q_s, q_w, q_r, q_reloc, q_xfer, q_read_boot, q_verify_end, q_verify_cmp, q_reject, qw, qc, qb, qr,
            i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4, j0, j1, j2, j3, j4);
    }
}

} // verus!
