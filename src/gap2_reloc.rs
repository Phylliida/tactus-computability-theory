//! # GAP-2 G2-F Route (i) — the RELOCATION gadget (the emit-coupling proper).
//!
//! Bridges the emitter's output to the comparator's **parked-entry** interface
//! ([`crate::tm_cmp_decide::lemma_cmp_bootstrap`]'s requires). At emit-end the tape holds
//!   `u = copy_u(0,M,g)` (the spent `copy_u` master scratch) · `v = dpack(output) + m^H·(α-block)`
//! (output low-first, then a one-cell gap, then α parked reversed with a far-`5` sentinel at its top),
//! head on the output/scratch boundary `a = 0`. The compare wants (`docs/gap2-input-loader-plan.md` §N+28)
//!   `u = dpack(drev(output)) + m^L·5` (output **reversed** onto `u`, far-`5` ceiling, nothing above) ·
//!   `v = dpack(drev(α)) + m^{L'}·5` (α reversed, far-`5`), head on the `g=1` boundary `a = 0`.
//!
//! The relocation is **two head-walks** (the design pinned with Danielle, §N+28: wipe → transfer → stamp
//! → g=1):
//!   1. **WIPE** the `copy_u` master scratch off `u` (`q_clean`-erase + a seek-right return), leaving
//!      `u = 0` locally and the surviving dovetail/temp high-tail untouched above.
//!   2. **STAMP+TRANSFER** — this module's core. The far-`5` stamp MERGES into the transfer's first step:
//!      `(q_reloc, 0, 5, q_xfer, R)` writes the output far-`5` onto `u` while crossing the boundary onto
//!      `output[0]`, then the [`crate::tm_dwalk::lemma_dwalk_right`] loop `(q_xfer, d, d, q_xfer, R)`
//!      peels the output block onto `u` *above* the `5`. Net `u = dpile(5, output) = dpack(drev(output))
//!      + m^L·5` — exactly the contract's ceiling — landing the head on the gap-`0` (`a = 0`, the `g=1`
//!      boundary). The α-block rides through as a `v`-side high tail ([`crate::gap2_tail_lift_v`]).
//!
//! This file builds the STAMP+TRANSFER **local** core (no tails); the `v`-tail lift (carry α) and the
//! WIPE leg compose on top. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, apply_quint, quint_matches, tm_step};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{dpack, dpile, pow_nat, lemma_dpack_pop};
use crate::tm_dwalk::lemma_dwalk_right;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_dwalk_prefix::{drev, lemma_dpile_is_dpack_drev};
use crate::tm_cmp_traverse::lemma_dwalk_right_gen;
use crate::tm_dstring::lemma_pow_nat_unfold;
use crate::tm_two_counter::repunit_m;
use crate::tm_copy_refresh::{copy_u, lemma_pow_nat_add};
use crate::gap2_master_mgmt::{lemma_q_clean, q_clean_fuel};

verus! {

/// **STAMP+TRANSFER, local core (dpile form).** From the wiped boundary (`u == 0`, `a == 0`, head on the
/// output/scratch boundary, state `q_reloc`) with the output block packed low-first on `v`
/// (`v == dpack(output)`), the relocation runs `1 + |output|` steps:
///   * step 0 — `(q_reloc, 0, 5, q_xfer, R)`: stamp the output far-`5` onto `u` and cross onto `output[0]`;
///   * steps 1..L — `(q_xfer, d, d, q_xfer, R)` (`d ∈ 1..4`): [`lemma_dwalk_right`] peels the output block
///     onto `u`, landing on the blank `0` above the output.
/// Net `u == dpile(5, output)` (the block reversed onto the stamped `5`), `v == 0`, `a == 0`, `q == q_xfer`.
pub proof fn lemma_reloc_stamp_transfer_local(
    tm: Tm, c: TmConfig, q_reloc: nat, q_xfer: nat, output: Seq<nat>,
    i0: int, i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        c.a == 0,
        c.u == 0,
        c.v == dpack(output, tm.m),
        c.q == q_reloc,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[i1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[i2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[i3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[i4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm, c, (1 + output.len()) as nat)
            == (TmConfig { u: dpile(5, output, tm.m), v: 0, a: 0, q: q_xfer }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);

    // ── step 0: stamp the far-5, cross onto output[0].
    assert(quint_matches(tm.quints[i0], c));   // q == q_reloc, a == 0
    lemma_tm_step_picks(tm, c, i0);
    let c1 = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c1));
    // R-move with a2 = 5: u' = 0·m + 5 = 5, v' = v/m, a' = v%m.
    lemma_dpack_pop(output, m);                // dpack(output)%m == output[0], /m == dpack(output.drop_first())
    assert(c1.u == 5);
    assert(c1.a == output[0]);
    assert(c1.v == dpack(output.drop_first(), m));
    assert(c1.q == q_xfer);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c, 1) == c1);

    // ── steps 1..L: dwalk_right peels output onto u above the stamped 5.
    assert(1 <= output[0] <= 4);
    lemma_dwalk_right(tm, c1, q_xfer, output, i1, i2, i3, i4);
    let c2 = TmConfig { u: dpile(c1.u, output, m), v: 0, a: 0, q: q_xfer };
    assert(tm_run(tm, c1, output.len()) == c2);
    assert(c1.u == 5);

    // ── compose: 1 + L.
    lemma_tm_run_split(tm, c, 1, output.len());
    assert(tm_run(tm, c, (1 + output.len()) as nat) == tm_run(tm, c1, output.len()));
}

/// **STAMP+TRANSFER, local core (contract form).** Same as [`lemma_reloc_stamp_transfer_local`] but with
/// the `u`-result spelled in the comparator's parked-entry shape `dpack(drev(output)) + m^L·5` (the
/// far-`5` ceiling immediately above the reversed output), via the [`lemma_dpile_is_dpack_drev`] bridge.
pub proof fn lemma_reloc_stamp_transfer_contract(
    tm: Tm, c: TmConfig, q_reloc: nat, q_xfer: nat, output: Seq<nat>,
    i0: int, i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        c.a == 0,
        c.u == 0,
        c.v == dpack(output, tm.m),
        c.q == q_reloc,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[i1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[i2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[i3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[i4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm, c, (1 + output.len()) as nat)
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5) as nat,
                    v: 0, a: 0, q: q_xfer,
               }),
{
    let m = tm.m;
    lemma_reloc_stamp_transfer_local(tm, c, q_reloc, q_xfer, output, i0, i1, i2, i3, i4);
    lemma_dpile_is_dpack_drev(5, output, m);   // dpile(5,output) == 5·m^L + dpack(drev(output))
    assert(dpile(5, output, m) == (dpack(drev(output), m) + pow_nat(m, output.len()) * 5) as nat) by(nonlinear_arith)
        requires dpile(5, output, m) == 5 * pow_nat(m, output.len()) + dpack(drev(output), m);
}

/// **STAMP+TRANSFER, tailed (dpile form).** The general workhorse: the α-block rides through on `v` as a
/// high tail. From `(u == 0, a == 0, v == dpack(output) + m^L·w, q == q_reloc)` — output low-first, then the
/// "above-output" value `w` (the one-cell gap `0` plus the parked α-block) at offset `L = |output|` — the
/// relocation runs `1 + L` steps: the far-`5` stamp + cross (step 0), then [`lemma_dwalk_right_gen`] peels
/// the output onto `u` and stops scanning `w % m`. With `w % m == 0` (the gap cell), the head lands on the
/// `g=1` boundary `a == 0`, leaving `v == w / m` (= the α-block) and `u == dpile(5, output)` — the parked-entry
/// shape. Reuses the local step-0 derivation, then the tailed walk in one call.
pub proof fn lemma_reloc_stamp_transfer_tailed(
    tm: Tm, c: TmConfig, q_reloc: nat, q_xfer: nat, output: Seq<nat>, w: nat,
    i0: int, i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w % tm.m == 0,
        c.a == 0,
        c.u == 0,
        c.v == (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
        c.q == q_reloc,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[i1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[i2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[i3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[i4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm, c, (1 + output.len()) as nat)
            == (TmConfig { u: dpile(5, output, tm.m), v: (w / tm.m), a: 0, q: q_xfer }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();

    // ── step 0: stamp the far-5, cross onto output[0]. The above-output tail rides down to offset L-1.
    assert(quint_matches(tm.quints[i0], c));   // q == q_reloc, a == 0
    lemma_tm_step_picks(tm, c, i0);
    let c1 = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c1));
    // Factor c.v == X·m + output[0] where X == dpack(output.drop_first()) + m^{L-1}·w, then div/mod step.
    crate::tm_dstring::lemma_pow_nat_unfold(m, big_l);   // m^L == m·m^{L-1}
    let big_x = (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    assert(dpack(output, m) == output[0] + m * dpack(output.drop_first(), m));   // dpack unfold (output nonempty)
    assert(output[0] < m);
    assert(c.v == big_x * m + output[0]) by(nonlinear_arith)
        requires
            c.v == (dpack(output, m) + pow_nat(m, big_l) * w) as nat,
            dpack(output, m) == output[0] + m * dpack(output.drop_first(), m),
            pow_nat(m, big_l) == m * pow_nat(m, (big_l - 1) as nat),
            big_x == (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    verus_group_theory::word_numbering::lemma_div_mod_step(big_x, m, output[0]);   // c.v/m == X, %m == output[0]
    assert(c.v % m == output[0]);
    assert(c.v / m == big_x);
    assert(c1.u == 5);
    assert(c1.a == output[0]);
    assert(c1.v == (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat);
    assert(c1.q == q_xfer);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c, 1) == c1);

    // ── steps 1..L: the tailed digit-walk-right peels output onto u, stops scanning w%m.
    assert(1 <= output[0] <= 4);
    lemma_dwalk_right_gen(tm, c1, q_xfer, output, w, i1, i2, i3, i4);
    let c2 = TmConfig { u: dpile(c1.u, output, m), v: (w / m), a: (w % m), q: q_xfer };
    assert(tm_run(tm, c1, big_l) == c2);
    assert(c1.u == 5);
    assert(c2.a == 0);                          // w % m == 0

    // ── compose: 1 + L.
    lemma_tm_run_split(tm, c, 1, big_l);
    assert(tm_run(tm, c, (1 + big_l) as nat) == tm_run(tm, c1, big_l));
}

/// **STAMP+TRANSFER, tailed (contract form) — the relocation's TARGET shape.** As
/// [`lemma_reloc_stamp_transfer_tailed`] but with the `u`-result in the comparator's parked-entry ceiling
/// `dpack(drev(output)) + m^L·5`. This is precisely the `u` of [`crate::tm_cmp_decide::lemma_cmp_bootstrap`]'s
/// requires (the relocation's deliverable), with the α-block left as `v == w / m` ready as the compare's
/// right tape.
pub proof fn lemma_reloc_stamp_transfer_tailed_contract(
    tm: Tm, c: TmConfig, q_reloc: nat, q_xfer: nat, output: Seq<nat>, w: nat,
    i0: int, i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w % tm.m == 0,
        c.a == 0,
        c.u == 0,
        c.v == (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
        c.q == q_reloc,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[i1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[i2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[i3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[i4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm, c, (1 + output.len()) as nat)
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5) as nat,
                    v: (w / tm.m), a: 0, q: q_xfer,
               }),
{
    let m = tm.m;
    lemma_reloc_stamp_transfer_tailed(tm, c, q_reloc, q_xfer, output, w, i0, i1, i2, i3, i4);
    lemma_dpile_is_dpack_drev(5, output, m);   // dpile(5,output) == 5·m^L + dpack(drev(output))
    assert(dpile(5, output, m) == (dpack(drev(output), m) + pow_nat(m, output.len()) * 5) as nat) by(nonlinear_arith)
        requires dpile(5, output, m) == 5 * pow_nat(m, output.len()) + dpack(drev(output), m);
}

/// **The LOCAL relocation phase — WIPE ∘ STAMP+TRANSFER.** The full emit-coupling in the local frame (the
/// dovetail/temp `u`-tail rides above via a separate lift at assembly). From the emit-end tape
///   `u == copy_u(0, M, g)` (the spent `copy_u` master scratch, `= m^g·R(M)`),
///   `v == dpack(output) + m^L·w` (output low-first, then the above-output value `w` = the one-cell gap `0`
///        plus the parked α-block, `w % m == 0`), `a == 0` on the boundary, state `q_s`,
/// it runs `q_clean` to wipe the master to `0` (head back at the boundary, state `q_reloc == q_home`), then
/// the tailed stamp+transfer to deposit the reversed output with its far-`5` ceiling onto `u`. The splice is
/// **state identification**: `q_clean` lands in `q_home == q_reloc` scanning `a == 0`, and the stamp quint
/// `(q_reloc, 0, 5, q_xfer, R)` fires there — no glue step. Net the comparator's parked entry:
///   `u == dpack(drev(output)) + m^L·5`, `v == w / m` (= the α-block), `a == 0`, state `q_xfer`.
pub proof fn lemma_reloc_local(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, w: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
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
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w % tm.m == 0,
        // q_clean quints (states q_s -> q_w -> q_r -> q_reloc), see lemma_q_clean.
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
        // stamp+transfer quints (states q_reloc -> q_xfer).
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
            (q_clean_fuel(g, big_m) + 1 + output.len()) as nat)
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5) as nat,
                    v: (w / tm.m), a: 0, q: q_xfer,
               }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();
    let v0 = (dpack(output, m) + pow_nat(m, big_l) * w) as nat;

    // ── copy_u(0,M,g) == m^g·R(M) == q_clean's t=0 master form.
    assert(repunit_m(0, m) == 0) by { crate::tm_two_counter::lemma_repunit_zero(m); }
    assert(pow_nat(m, 0) == 1);
    assert(copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m)) by(nonlinear_arith)
        requires
            copy_u(0, big_m, g, m) == repunit_m(0, m)
                + pow_nat(m, g) * (5 * repunit_m(0, m) + pow_nat(m, 0) * repunit_m(big_m, m)),
            repunit_m(0, m) == 0,
            pow_nat(m, 0) == 1;
    // ... which equals q_clean's t=0 master form pow_nat(m,g)·(R(M) + m^(M+1)·0).
    assert(pow_nat(m, (big_m + 1) as nat) * 0 == 0) by(nonlinear_arith);
    assert(copy_u(0, big_m, g, m)
        == pow_nat(m, g) * (repunit_m(big_m, m) + pow_nat(m, (big_m + 1) as nat) * 0)) by(nonlinear_arith)
        requires
            copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m),
            pow_nat(m, (big_m + 1) as nat) * 0 == 0;

    // ── v0 % m == output[0] ∈ 1..4 (the q_clean precondition). v0 == big_y·m + output[0].
    lemma_dpack_pop(output, m);                // dpack(output)%m == output[0], /m == dpack(output.drop_first())
    lemma_pow_nat_unfold(m, big_l);            // m^L == m·m^{L-1}
    let big_y = (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    assert(dpack(output, m) == output[0] + m * dpack(output.drop_first(), m));
    assert(output[0] < m);
    assert(v0 == big_y * m + output[0]) by(nonlinear_arith)
        requires
            v0 == (dpack(output, m) + pow_nat(m, big_l) * w) as nat,
            dpack(output, m) == output[0] + m * dpack(output.drop_first(), m),
            pow_nat(m, big_l) == m * pow_nat(m, (big_l - 1) as nat),
            big_y == (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    verus_group_theory::word_numbering::lemma_div_mod_step(big_y, m, output[0]);
    assert(v0 % m == output[0]);
    assert(1 <= v0 % m <= 4);

    // ── WIPE leg: q_clean (t=0) erases the master, head back on the boundary in q_reloc.
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: v0, a: 0, q: q_s };
    lemma_q_clean(tm, g, big_m, 0, v0, q_s, q_w, q_r, q_reloc,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4);
    // q_clean's result u == 0·m^{g+K+1} == 0.
    let c1 = TmConfig { u: 0, v: v0, a: 0, q: q_reloc };
    assert((0 * pow_nat(m, (g + big_m + 1) as nat)) as nat == 0);
    assert(tm_run(tm, c0, q_clean_fuel(g, big_m)) == c1);

    // ── STAMP+TRANSFER leg: deposit reversed output + far-5 onto u; α-block left as v == w/m.
    lemma_reloc_stamp_transfer_tailed_contract(tm, c1, q_reloc, q_xfer, output, w, j0, j1, j2, j3, j4);
    let c2 = TmConfig {
        u: (dpack(drev(output), m) + pow_nat(m, big_l) * 5) as nat,
        v: (w / m), a: 0, q: q_xfer };
    assert(tm_run(tm, c1, (1 + big_l) as nat) == c2);

    // ── compose: q_clean_fuel + (1 + L).
    lemma_tm_run_split(tm, c0, q_clean_fuel(g, big_m), (1 + big_l) as nat);
    assert((q_clean_fuel(g, big_m) + (1 + big_l)) as nat == (q_clean_fuel(g, big_m) + 1 + big_l) as nat);
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
//  u-TAIL LIFT (R-cmp tail-safety, the first half) — carry a Control-Zone / dovetail backup `T_u`,
//  parked on `u` high above the master, through the relocation untouched. This is what lets the
//  per-stage emit→reloc→compare surface run INSIDE the global R-S dovetail frame without clobbering
//  the search state. The `q_clean` master-wipe already carries the tail (its `t` parameter); the only
//  new content is the STAMP+TRANSFER starting from a nonzero `u`-floor (the surviving backup, collapsed
//  to `u`'s low end by the wipe), which rides up to a high offset above the relocated output's far-`5`.
//  The compare-side u-precondition generalization (the second half) is a separate follow-on brick.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// **STAMP+TRANSFER, u-floor generalization (dpile form).** Identical to
/// [`lemma_reloc_stamp_transfer_tailed`] but the relocation starts from an arbitrary `u`-floor
/// `c.u == u_floor` (the surviving Control-Zone / dovetail backup, sitting at `u`'s low end after the
/// master wipe) instead of `u == 0`. The far-`5` stamp lifts the floor by one digit
/// (`c1.u == u_floor·m + 5`) and the tailed digit-walk piles the output above it: net
/// `u == dpile(u_floor·m + 5, output)`. This is the `u`-side analogue of the `v`-tail lift — it proves
/// the relocation is **tail-safe**: a backup high above the master survives the wipe+transfer untouched.
pub proof fn lemma_reloc_stamp_transfer_ufloor(
    tm: Tm, c: TmConfig, q_reloc: nat, q_xfer: nat, output: Seq<nat>, w: nat, u_floor: nat,
    i0: int, i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w % tm.m == 0,
        c.a == 0,
        c.u == u_floor,
        c.v == (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
        c.q == q_reloc,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[i1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[i2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[i3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[i4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm, c, (1 + output.len()) as nat)
            == (TmConfig {
                    u: dpile((u_floor * tm.m + 5) as nat, output, tm.m),
                    v: (w / tm.m), a: 0, q: q_xfer,
               }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();

    // ── step 0: stamp the far-5, cross onto output[0]. R-move: u: u_floor -> u_floor·m + 5.
    assert(quint_matches(tm.quints[i0], c));   // q == q_reloc, a == 0
    lemma_tm_step_picks(tm, c, i0);
    let c1 = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c1));
    // Factor c.v == X·m + output[0] where X == dpack(output.drop_first()) + m^{L-1}·w, then div/mod step.
    lemma_pow_nat_unfold(m, big_l);   // m^L == m·m^{L-1}
    let big_x = (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    assert(dpack(output, m) == output[0] + m * dpack(output.drop_first(), m));   // dpack unfold (output nonempty)
    assert(output[0] < m);
    assert(c.v == big_x * m + output[0]) by(nonlinear_arith)
        requires
            c.v == (dpack(output, m) + pow_nat(m, big_l) * w) as nat,
            dpack(output, m) == output[0] + m * dpack(output.drop_first(), m),
            pow_nat(m, big_l) == m * pow_nat(m, (big_l - 1) as nat),
            big_x == (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    verus_group_theory::word_numbering::lemma_div_mod_step(big_x, m, output[0]);   // c.v/m == X, %m == output[0]
    assert(c.v % m == output[0]);
    assert(c.v / m == big_x);
    // R-move with a2 = 5: c1.u == c.u·m + 5 == u_floor·m + 5.
    assert(c1.u == (u_floor * m + 5) as nat);
    assert(c1.a == output[0]);
    assert(c1.v == (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat);
    assert(c1.q == q_xfer);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c, 1) == c1);

    // ── steps 1..L: the tailed digit-walk-right peels output onto u, stops scanning w%m == 0.
    assert(1 <= output[0] <= 4);
    lemma_dwalk_right_gen(tm, c1, q_xfer, output, w, i1, i2, i3, i4);
    let c2 = TmConfig { u: dpile(c1.u, output, m), v: (w / m), a: (w % m), q: q_xfer };
    assert(tm_run(tm, c1, big_l) == c2);
    assert(c1.u == (u_floor * m + 5) as nat);
    assert(c2.a == 0);                          // w % m == 0

    // ── compose: 1 + L.
    lemma_tm_run_split(tm, c, 1, big_l);
    assert(tm_run(tm, c, (1 + big_l) as nat) == tm_run(tm, c1, big_l));
}

/// **STAMP+TRANSFER, u-floor (contract form).** As [`lemma_reloc_stamp_transfer_ufloor`] but with the
/// `u`-result spelled in the parked-entry ceiling shape with the floor lifted to offset `L+1`:
/// `dpack(drev(output)) + m^L·5 + m^{L+1}·u_floor` — the reversed output, the far-`5` ceiling, then the
/// surviving backup riding high above. Via the [`lemma_dpile_is_dpack_drev`] bridge.
pub proof fn lemma_reloc_stamp_transfer_ufloor_contract(
    tm: Tm, c: TmConfig, q_reloc: nat, q_xfer: nat, output: Seq<nat>, w: nat, u_floor: nat,
    i0: int, i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w % tm.m == 0,
        c.a == 0,
        c.u == u_floor,
        c.v == (dpack(output, tm.m) + pow_nat(tm.m, output.len()) * w) as nat,
        c.q == q_reloc,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_reloc, 0, 5, q_xfer, Dir::R),
        tm.quints[i1] == mk_quint(q_xfer, 1, 1, q_xfer, Dir::R),
        tm.quints[i2] == mk_quint(q_xfer, 2, 2, q_xfer, Dir::R),
        tm.quints[i3] == mk_quint(q_xfer, 3, 3, q_xfer, Dir::R),
        tm.quints[i4] == mk_quint(q_xfer, 4, 4, q_xfer, Dir::R),
    ensures
        tm_run(tm, c, (1 + output.len()) as nat)
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5
                        + pow_nat(tm.m, (output.len() + 1) as nat) * u_floor) as nat,
                    v: (w / tm.m), a: 0, q: q_xfer,
               }),
{
    let m = tm.m;
    let big_l = output.len();
    lemma_reloc_stamp_transfer_ufloor(tm, c, q_reloc, q_xfer, output, w, u_floor, i0, i1, i2, i3, i4);
    // dpile(u_floor·m+5, output) == (u_floor·m+5)·m^L + dpack(drev(output)).
    lemma_dpile_is_dpack_drev((u_floor * m + 5) as nat, output, m);
    lemma_pow_nat_unfold(m, (big_l + 1) as nat);   // m^{L+1} == m·m^L
    assert(dpile((u_floor * m + 5) as nat, output, m)
        == (dpack(drev(output), m) + pow_nat(m, big_l) * 5 + pow_nat(m, (big_l + 1) as nat) * u_floor) as nat)
        by(nonlinear_arith)
        requires
            dpile((u_floor * m + 5) as nat, output, m)
                == (u_floor * m + 5) * pow_nat(m, big_l) + dpack(drev(output), m),
            pow_nat(m, (big_l + 1) as nat) == m * pow_nat(m, big_l);
}

/// **The LOCAL relocation phase, TAIL-SAFE (carry a Control-Zone backup `T_u`).** Generalizes
/// [`lemma_reloc_local`] from `u == copy_u(0,M,g)` (bare master) to `u == copy_u(0,M,g) + m^{g+M+1}·T_u`
/// — the spent master with a surviving high tail `T_u` parked just above it (the dovetail/temp backup the
/// global R-S frame keeps off to the side). The wipe ([`lemma_q_clean`] with `t = T_u`) erases the master
/// and returns the head to the boundary leaving `u == T_u·m^{g+M+1}`; the u-floor stamp+transfer then
/// deposits the reversed output with its far-`5` ceiling and rides the backup up to offset `L+1+g+M+1`,
/// well above the far-`5` (= digit `L`). Net the comparator's parked entry **plus** the untouched backup:
///   `u == dpack(drev(output)) + m^L·5 + m^{(L+1+g+M+1)}·T_u`, `v == w/m`, `a == 0`, state `q_xfer`.
/// With `T_u == 0` this is exactly [`lemma_reloc_local`]. The relocation is tail-safe because `q_clean`'s
/// deepest left reach is the master separator (below the backup) and the transfer only writes the
/// output region — the backup is never scanned.
pub proof fn lemma_reloc_local_tailed(
    tm: Tm, big_m: nat, g: nat, output: Seq<nat>, w: nat, t_u: nat,
    q_s: nat, q_w: nat, q_r: nat, q_reloc: nat, q_xfer: nat,
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
        output.len() >= 1,
        forall|k: int| 0 <= k < output.len() ==> 1 <= #[trigger] output[k] <= 4,
        w % tm.m == 0,
        // q_clean quints (states q_s -> q_w -> q_r -> q_reloc), see lemma_q_clean.
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
        // stamp+transfer quints (states q_reloc -> q_xfer).
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
            (q_clean_fuel(g, big_m) + 1 + output.len()) as nat)
            == (TmConfig {
                    u: (dpack(drev(output), tm.m) + pow_nat(tm.m, output.len()) * 5
                        + pow_nat(tm.m, (output.len() + 1 + g + big_m + 1) as nat) * t_u) as nat,
                    v: (w / tm.m), a: 0, q: q_xfer,
               }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = output.len();
    let v0 = (dpack(output, m) + pow_nat(m, big_l) * w) as nat;

    // ── copy_u(0,M,g) == m^g·R(M); the q_clean (t = t_u) master-form entry equals copy_u + m^{g+M+1}·t_u.
    assert(repunit_m(0, m) == 0) by { crate::tm_two_counter::lemma_repunit_zero(m); }
    assert(pow_nat(m, 0) == 1);
    assert(copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m)) by(nonlinear_arith)
        requires
            copy_u(0, big_m, g, m) == repunit_m(0, m)
                + pow_nat(m, g) * (5 * repunit_m(0, m) + pow_nat(m, 0) * repunit_m(big_m, m)),
            repunit_m(0, m) == 0,
            pow_nat(m, 0) == 1;
    // m^g · m^{M+1} == m^{g+M+1}.
    lemma_pow_nat_add(m, g, (big_m + 1) as nat);
    let qc_entry = (pow_nat(m, g) * (repunit_m(big_m, m) + pow_nat(m, (big_m + 1) as nat) * t_u)) as nat;
    assert(qc_entry == (copy_u(0, big_m, g, m) + pow_nat(m, (g + big_m + 1) as nat) * t_u) as nat)
        by(nonlinear_arith)
        requires
            copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m),
            pow_nat(m, (g + big_m + 1) as nat) == pow_nat(m, g) * pow_nat(m, (big_m + 1) as nat),
            qc_entry == (pow_nat(m, g) * (repunit_m(big_m, m) + pow_nat(m, (big_m + 1) as nat) * t_u)) as nat;

    // ── v0 % m == output[0] ∈ 1..4 (the q_clean precondition). v0 == big_y·m + output[0].
    lemma_dpack_pop(output, m);
    lemma_pow_nat_unfold(m, big_l);
    let big_y = (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    assert(dpack(output, m) == output[0] + m * dpack(output.drop_first(), m));
    assert(output[0] < m);
    assert(v0 == big_y * m + output[0]) by(nonlinear_arith)
        requires
            v0 == (dpack(output, m) + pow_nat(m, big_l) * w) as nat,
            dpack(output, m) == output[0] + m * dpack(output.drop_first(), m),
            pow_nat(m, big_l) == m * pow_nat(m, (big_l - 1) as nat),
            big_y == (dpack(output.drop_first(), m) + pow_nat(m, (big_l - 1) as nat) * w) as nat;
    verus_group_theory::word_numbering::lemma_div_mod_step(big_y, m, output[0]);
    assert(v0 % m == output[0]);
    assert(1 <= v0 % m <= 4);

    // ── WIPE leg: q_clean (t = t_u) erases the master, head back on the boundary in q_reloc,
    //    leaving the backup at u == t_u·m^{g+M+1}.
    let c0 = TmConfig { u: qc_entry, v: v0, a: 0, q: q_s };
    lemma_q_clean(tm, g, big_m, t_u, v0, q_s, q_w, q_r, q_reloc,
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4);
    let u_floor = (t_u * pow_nat(m, (g + big_m + 1) as nat)) as nat;
    let c1 = TmConfig { u: u_floor, v: v0, a: 0, q: q_reloc };
    assert(tm_run(tm, c0, q_clean_fuel(g, big_m)) == c1);

    // ── STAMP+TRANSFER leg (u-floor): deposit reversed output + far-5 onto u above the backup.
    lemma_reloc_stamp_transfer_ufloor_contract(tm, c1, q_reloc, q_xfer, output, w, u_floor,
        j0, j1, j2, j3, j4);
    let c2 = TmConfig {
        u: (dpack(drev(output), m) + pow_nat(m, big_l) * 5 + pow_nat(m, (big_l + 1) as nat) * u_floor) as nat,
        v: (w / m), a: 0, q: q_xfer };
    assert(tm_run(tm, c1, (1 + big_l) as nat) == c2);

    // ── reshape the backup offset: m^{L+1} · (t_u·m^{g+M+1}) == t_u · m^{L+1+g+M+1}.
    lemma_pow_nat_add(m, (big_l + 1) as nat, (g + big_m + 1) as nat);
    assert(pow_nat(m, (big_l + 1) as nat) * u_floor
        == pow_nat(m, (big_l + 1 + g + big_m + 1) as nat) * t_u) by(nonlinear_arith)
        requires
            u_floor == (t_u * pow_nat(m, (g + big_m + 1) as nat)) as nat,
            pow_nat(m, (big_l + 1 + g + big_m + 1) as nat)
                == pow_nat(m, (big_l + 1) as nat) * pow_nat(m, (g + big_m + 1) as nat);

    // ── compose: q_clean_fuel + (1 + L).
    lemma_tm_run_split(tm, c0, q_clean_fuel(g, big_m), (1 + big_l) as nat);
    assert((q_clean_fuel(g, big_m) + (1 + big_l)) as nat == (q_clean_fuel(g, big_m) + 1 + big_l) as nat);
}

} // verus!
