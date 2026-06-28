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

} // verus!
