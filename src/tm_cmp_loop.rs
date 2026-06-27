//! # GAP-2 G2-F Route (i) brick R-cmp (B-cmp.5) — the compare LOOP (induction over the digit list).
//!
//! [`crate::tm_cmp_traverse::lemma_cmp_round`] (B-cmp.5 STEP) runs one matched round `INV(k) → INV(k+1)`
//! of the M1 generate-and-compare: cross the consumed-output gap into the compare state, match the output
//! frontier against the marked α digit (carried in state), consume it, advance the marker one cell deeper,
//! and return the head to the new output frontier. This file iterates that step into the full compare loop:
//! given a digit list `ds = [α[k0], …, α[k0+n]]` whose first `n` digits match the corresponding output
//! digits, the loop runs `n` rounds and lands at `INV(k0+n)` (the marker on the lookahead `α[k0+n]`).
//!
//! **The value-in-state encoding (see `docs/gap2-input-loader-plan.md` §N+24).** Because the per-round
//! compare/marker quintuples mention the round's marked value `vk = ds[i]`, which VARIES, the loop's states
//! are **value-indexed functions** `qw, qc, qb: spec_fn(nat) -> nat` (the left-walk / compare-mode /
//! right-walk tracks for value `V`), with `qr: nat` the shared read+remark dispatch state. The quintuple
//! availability is a single `forall|V ∈ 1..4| cmp_quints_present(…, V)` hypothesis — the spec-fn
//! applications live inside the named predicate body, so the forall trigger is just `cmp_quints_present`,
//! sidestepping the bare-forall-over-spec-fn trigger trap.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm::Quintuple;
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold};
use crate::tm_skip_blank::pile_zeros;
use crate::tm_cmp_traverse::lemma_cmp_round;
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Spec helpers — the loop invariant `INV(k)` expressed over the digit list `ds`.
// ─────────────────────────────────────────────────────────────────────────────

/// The base-`m` value of the α digits strictly ABOVE the marker. `ds[0]` is the marked (hidden) digit
/// carried in state; `ds.drop_first()` are the digits above it, followed by the α suffix value `suf`.
pub open spec fn cmp_above(ds: Seq<nat>, suf: nat, m: nat) -> nat {
    dpack(ds.drop_first(), m) + pow_nat(m, (ds.len() - 1) as nat) * suf
}

/// The marker word `w = m·(above) + 5`: low cell is the marker `5`, above it the α digits beyond the
/// marker. The cell HIDING `ds[0]` is replaced by this marker (value `ds[0]` carried in state).
pub open spec fn cmp_marker(ds: Seq<nat>, suf: nat, m: nat) -> nat {
    m * cmp_above(ds, suf, m) + 5
}

/// The output "pre-gap" value: the `n = ds.len()-1` matched output digits (which equal `ds[0..n-1]`),
/// followed by `out_above` (the output beyond the loop's matched region). The full output stack is this
/// value with `g` consumed-output blanks (`0`) piled below it.
pub open spec fn cmp_out_pregap(ds: Seq<nat>, out_above: nat, m: nat) -> nat {
    dpack(ds.subrange(0, (ds.len() - 1) as int), m) + pow_nat(m, (ds.len() - 1) as nat) * out_above
}

/// The compare-loop invariant config `INV` over `(pre, ds, suf, g, out_above)`: restored α prefix `pre`,
/// then the marker word hiding `ds[0]`, then the α tail; output stack `pile_zeros(out_pregap, g)` with the
/// head ONE cell into `u` (so `a` is the top gap blank, `u` the rest), state `qw(ds[0])` (left-walk track
/// for the marked value).
pub open spec fn cmp_inv_config(
    qw: spec_fn(nat) -> nat, pre: Seq<nat>, ds: Seq<nat>, suf: nat, g: nat, out_above: nat, m: nat,
) -> TmConfig {
    TmConfig {
        u: pile_zeros(cmp_out_pregap(ds, out_above, m), g, m) / m,
        v: dpack(pre, m) + pow_nat(m, pre.len()) * cmp_marker(ds, suf, m),
        a: pile_zeros(cmp_out_pregap(ds, out_above, m), g, m) % m,
        q: qw(ds[0]),
    }
}

/// The total fuel of `n` rounds starting at prefix length `k0`, gap `g`: each round `i` costs
/// `2·(k0+i) + 2·(g+i) + 4` (the step fuel of [`crate::tm_cmp_traverse::lemma_cmp_round`] at that point).
pub open spec fn cmp_loop_fuel(k0: nat, g: nat, n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        (2 * k0 + 2 * g + 4) + cmp_loop_fuel((k0 + 1) as nat, (g + 1) as nat, (n - 1) as nat)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Quintuple availability — value-indexed, bundled per value `V` (spec-fn apps hidden in the body).
// ─────────────────────────────────────────────────────────────────────────────

/// `tm` contains the quintuple `qt` somewhere in its list.
pub open spec fn has_quint(tm: Tm, qt: Quintuple) -> bool {
    exists|i: int| 0 <= i < tm.quints.len() && tm.quints[i] == qt
}

/// All compare quintuples for the value-track `V` are present in `tm` (the 14 quintuples one round at
/// value `V` may fire). The marker-step writes `V` and hands off to the shared `qr`; the read+remark
/// dispatches `qr` by the scanned digit `V` into `qw(V)`.
pub open spec fn cmp_quints_present(
    tm: Tm, qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat, V: nat,
) -> bool {
    &&& has_quint(tm, mk_quint(qw(V), 0, 0, qc(V), Dir::L))   // boundary transition
    &&& has_quint(tm, mk_quint(qc(V), 0, 0, qc(V), Dir::L))   // gap skip (compare mode)
    &&& has_quint(tm, mk_quint(qc(V), V, 0, qb(V), Dir::R))   // compare match
    &&& has_quint(tm, mk_quint(qb(V), 0, 0, qb(V), Dir::R))   // return skip
    &&& has_quint(tm, mk_quint(qb(V), 1, 1, qb(V), Dir::R))   // right walk
    &&& has_quint(tm, mk_quint(qb(V), 2, 2, qb(V), Dir::R))
    &&& has_quint(tm, mk_quint(qb(V), 3, 3, qb(V), Dir::R))
    &&& has_quint(tm, mk_quint(qb(V), 4, 4, qb(V), Dir::R))
    &&& has_quint(tm, mk_quint(qb(V), 5, V, qr, Dir::R))      // marker step (restore V, advance R)
    &&& has_quint(tm, mk_quint(qr, V, 5, qw(V), Dir::L))      // read+remark (record V, re-mark, L)
    &&& has_quint(tm, mk_quint(qw(V), 1, 1, qw(V), Dir::L))   // left walk
    &&& has_quint(tm, mk_quint(qw(V), 2, 2, qw(V), Dir::L))
    &&& has_quint(tm, mk_quint(qw(V), 3, 3, qw(V), Dir::L))
    &&& has_quint(tm, mk_quint(qw(V), 4, 4, qw(V), Dir::L))
}

// ─────────────────────────────────────────────────────────────────────────────
// Recursion-step identities for the invariant helpers (peel the low element of `ds`).
// ─────────────────────────────────────────────────────────────────────────────

/// **Marker tail peel.** `cmp_above(ds) == ds[1] + m·cmp_above(ds.drop_first())` for `ds.len() ≥ 2` —
/// reading the marked digit `ds[0]` off (it is hidden), the digit just above the marker is `ds[1]`.
pub proof fn lemma_cmp_above_step(ds: Seq<nat>, suf: nat, m: nat)
    requires
        ds.len() >= 2,
    ensures
        cmp_above(ds, suf, m) == ds[1] + m * cmp_above(ds.drop_first(), suf, m),
{
    let r = ds.drop_first();
    assert(r.len() == ds.len() - 1);
    assert(r[0] == ds[1]);
    assert(r.len() >= 1);
    // dpack(r) unfold (r nonempty).
    assert(dpack(r, m) == r[0] + m * dpack(r.drop_first(), m));
    let k1 = (ds.len() - 1) as nat;   // == r.len()
    let k2 = (ds.len() - 2) as nat;   // == r.len() - 1
    lemma_pow_nat_unfold(m, k1);      // pow_nat(m, k1) == m * pow_nat(m, k1-1)
    assert((k1 - 1) as nat == k2);
    assert((r.len() - 1) as nat == k2);
    assert(cmp_above(ds, suf, m) == dpack(r, m) + pow_nat(m, k1) * suf);
    assert(cmp_above(r, suf, m) == dpack(r.drop_first(), m) + pow_nat(m, k2) * suf);
    assert(cmp_above(ds, suf, m) == ds[1] + m * cmp_above(r, suf, m)) by(nonlinear_arith)
        requires
            cmp_above(ds, suf, m) == dpack(r, m) + pow_nat(m, k1) * suf,
            dpack(r, m) == ds[1] + m * dpack(r.drop_first(), m),
            pow_nat(m, k1) == m * pow_nat(m, k2),
            cmp_above(r, suf, m) == dpack(r.drop_first(), m) + pow_nat(m, k2) * suf;
}

/// **Output pre-gap peel.** `cmp_out_pregap(ds) == ds[0] + m·cmp_out_pregap(ds.drop_first())` for
/// `ds.len() ≥ 2` — the lowest matched output digit is `ds[0]` (the current frontier).
pub proof fn lemma_cmp_out_pregap_step(ds: Seq<nat>, out_above: nat, m: nat)
    requires
        ds.len() >= 2,
    ensures
        cmp_out_pregap(ds, out_above, m) == ds[0] + m * cmp_out_pregap(ds.drop_first(), out_above, m),
{
    let n = (ds.len() - 1) as int;          // == ds.drop_first().len()
    let t = ds.subrange(0, n);              // the n matched digits of ds
    assert(t.len() == n);
    assert(t[0] == ds[0]);
    assert(t.len() >= 1);
    // dpack(t) unfold (t nonempty).
    assert(dpack(t, m) == t[0] + m * dpack(t.drop_first(), m));
    // t.drop_first() == ds.drop_first().subrange(0, n-1): both are ds.subrange(1, n).
    let r = ds.drop_first();
    assert(t.drop_first() =~= r.subrange(0, (n - 1) as int)) by {
        assert(t.drop_first().len() == n - 1);
        assert(r.subrange(0, (n - 1) as int).len() == n - 1);
        assert forall|i: int| 0 <= i < n - 1 implies
            t.drop_first()[i] == r.subrange(0, (n - 1) as int)[i] by {
            assert(t.drop_first()[i] == t[i + 1]);
            assert(t[i + 1] == ds[i + 1]);
            assert(r.subrange(0, (n - 1) as int)[i] == r[i]);
            assert(r[i] == ds[i + 1]);
        }
    }
    let k1 = (ds.len() - 1) as nat;
    let k2 = (ds.len() - 2) as nat;
    lemma_pow_nat_unfold(m, k1);
    assert((k1 - 1) as nat == k2);
    assert(r.len() == ds.len() - 1);
    assert((r.len() - 1) as int == n - 1);
    assert(cmp_out_pregap(ds, out_above, m) == dpack(t, m) + pow_nat(m, k1) * out_above);
    assert(cmp_out_pregap(r, out_above, m)
        == dpack(r.subrange(0, (n - 1) as int), m) + pow_nat(m, k2) * out_above);
    assert(dpack(t.drop_first(), m) == dpack(r.subrange(0, (n - 1) as int), m));
    assert(cmp_out_pregap(ds, out_above, m) == ds[0] + m * cmp_out_pregap(r, out_above, m))
        by(nonlinear_arith)
        requires
            cmp_out_pregap(ds, out_above, m) == dpack(t, m) + pow_nat(m, k1) * out_above,
            dpack(t, m) == ds[0] + m * dpack(t.drop_first(), m),
            pow_nat(m, k1) == m * pow_nat(m, k2),
            cmp_out_pregap(r, out_above, m)
                == dpack(t.drop_first(), m) + pow_nat(m, k2) * out_above;
}

// ─────────────────────────────────────────────────────────────────────────────
// The packaged round — wrap `lemma_cmp_round` in the `cmp_inv_config` form, extracting the per-round
// quintuple indices from the value-indexed availability hypothesis.
// ─────────────────────────────────────────────────────────────────────────────

/// Pull a concrete index for a quintuple known to be present.
pub proof fn extract_quint(tm: Tm, qt: Quintuple) -> (i: int)
    requires
        has_quint(tm, qt),
    ensures
        0 <= i < tm.quints.len(),
        tm.quints[i] == qt,
{
    choose|i: int| 0 <= i < tm.quints.len() && tm.quints[i] == qt
}

/// **One packaged matched round `INV → INV'`.** Given the entry config in `cmp_inv_config` form and the
/// value-indexed quintuple availability, run one [`lemma_cmp_round`] (consuming `ds[0]`, matching it
/// against the output frontier) and land at the `cmp_inv_config` for `(pre ++ [ds[0]], ds.drop_first(),
/// g+1)`. The marked value advances `ds[0] → ds[1]`; the left-walk track switches `qw(ds[0]) → qw(ds[1])`.
/// Fuel `2·|pre| + 2·g + 4`. The induction step the compare loop chains.
pub proof fn lemma_cmp_round_packaged(
    tm: Tm, c: TmConfig,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    pre: Seq<nat>, ds: Seq<nat>, suf: nat, g: nat, out_above: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        pre.len() >= 1,
        forall|k: int| 0 <= k < pre.len() ==> 1 <= #[trigger] pre[k] <= 4,
        ds.len() >= 2,
        forall|k: int| 0 <= k < ds.len() ==> 1 <= #[trigger] ds[k] <= 4,
        g >= 1,
        c == cmp_inv_config(qw, pre, ds, suf, g, out_above, tm.m),
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
    ensures
        tm_run(tm, c, (2 * pre.len() + 2 * g + 4) as nat)
            == cmp_inv_config(qw, pre + seq![ds[0]], ds.drop_first(), suf, (g + 1) as nat, out_above, tm.m),
{
    let m = tm.m;
    reveal(tm_wf);
    assert(m > 5);
    let vk = ds[0];
    let s = ds[1];
    assert(1 <= vk <= 4);
    assert(1 <= s <= 4);
    let out_rest = cmp_out_pregap(ds.drop_first(), out_above, m);
    let whi = cmp_above(ds, suf, m);
    let suf_param = cmp_above(ds.drop_first(), suf, m);
    let w = cmp_marker(ds, suf, m);

    // ── instantiate quint availability at vk (current value) and s (next value).
    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    assert(cmp_quints_present(tm, qw, qc, qb, qr, s));

    // ── extract indices (vk-family + s-family).
    let ib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let jc = extract_quint(tm, mk_quint(qc(vk), vk, 0, qb(vk), Dir::R));
    let js = extract_quint(tm, mk_quint(qb(vk), 0, 0, qb(vk), Dir::R));
    let r1 = extract_quint(tm, mk_quint(qb(vk), 1, 1, qb(vk), Dir::R));
    let r2 = extract_quint(tm, mk_quint(qb(vk), 2, 2, qb(vk), Dir::R));
    let r3 = extract_quint(tm, mk_quint(qb(vk), 3, 3, qb(vk), Dir::R));
    let r4 = extract_quint(tm, mk_quint(qb(vk), 4, 4, qb(vk), Dir::R));
    let jm = extract_quint(tm, mk_quint(qb(vk), 5, vk, qr, Dir::R));
    let jr = extract_quint(tm, mk_quint(qr, s, 5, qw(s), Dir::L));
    let l1 = extract_quint(tm, mk_quint(qw(s), 1, 1, qw(s), Dir::L));
    let l2 = extract_quint(tm, mk_quint(qw(s), 2, 2, qw(s), Dir::L));
    let l3 = extract_quint(tm, mk_quint(qw(s), 3, 3, qw(s), Dir::L));
    let l4 = extract_quint(tm, mk_quint(qw(s), 4, 4, qw(s), Dir::L));

    // ── peel identities so the entry config matches lemma_cmp_round's spelled-out form.
    lemma_cmp_above_step(ds, suf, m);              // whi == s + m·suf_param
    lemma_cmp_out_pregap_step(ds, out_above, m);   // cmp_out_pregap(ds) == vk + m·out_rest
    assert(w == m * whi + 5);                       // cmp_marker def
    assert(whi == m * suf_param + s);               // commute the peel
    // entry config fields (from c == cmp_inv_config).
    assert(c.v == dpack(pre, m) + pow_nat(m, pre.len()) * w);
    assert(c.q == qw(vk));
    assert(cmp_out_pregap(ds, out_above, m) == vk + m * out_rest);
    assert(c.a == pile_zeros(vk + m * out_rest, g, m) % m);
    assert(c.u == pile_zeros(vk + m * out_rest, g, m) / m);

    // ── run one round.
    lemma_cmp_round(tm, c, qw(vk), qw(s), qc(vk), qb(vk), qr,
        pre, w, whi, suf_param, vk, s, g, vk, out_rest,
        ib, ic, jc, js, r1, r2, r3, r4, jm, jr, l1, l2, l3, l4);
    let c_exit = TmConfig {
        u: pile_zeros(out_rest, g, m),
        v: dpack(pre + seq![vk], m) + pow_nat(m, (pre.len() + 1) as nat) * (m * suf_param + 5),
        a: 0,
        q: qw(s),
    };
    assert(tm_run(tm, c, (2 * pre.len() + 2 * g + 4) as nat) == c_exit);

    // ── show c_exit == cmp_inv_config(recursive params).
    let dsr = ds.drop_first();
    let inv_next = cmp_inv_config(qw, pre + seq![vk], dsr, suf, (g + 1) as nat, out_above, m);
    // output side: pile_zeros(out_rest, g+1) == pile_zeros(out_rest, g)·m.
    assert(pile_zeros(out_rest, (g + 1) as nat, m) == pile_zeros(out_rest, g, m) * m);
    assert((pile_zeros(out_rest, g, m) * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((pile_zeros(out_rest, g, m) * m) / m == pile_zeros(out_rest, g, m))
        by(nonlinear_arith) requires m > 1;
    assert(cmp_out_pregap(dsr, out_above, m) == out_rest);
    assert(inv_next.u == pile_zeros(out_rest, g, m));
    assert(inv_next.a == 0);
    // marker side: cmp_marker(dsr, suf, m) == m·suf_param + 5.
    assert(cmp_marker(dsr, suf, m) == m * suf_param + 5);
    assert((pre + seq![vk]).len() == pre.len() + 1);
    assert(inv_next.v == c_exit.v);
    // state side: dsr[0] == s.
    assert(dsr[0] == s);
    assert(inv_next.q == qw(s));
    assert(c_exit == inv_next);
}

// ─────────────────────────────────────────────────────────────────────────────
// The compare loop — iterate the packaged round over the digit list `ds`.
// ─────────────────────────────────────────────────────────────────────────────

/// **B-cmp.5 — the compare LOOP.** From `INV(k0)` (config in `cmp_inv_config` form over `(pre, ds, suf,
/// g, out_above)`, `|pre| = k0`), run the `n = ds.len()-1` matched rounds and land at `INV(k0+n)`: the α
/// prefix grown by the `n` matched digits `ds[0..n-1]`, the marker now hiding the lookahead `ds[n]`, the
/// gap grown to `g+n`. Fuel `cmp_loop_fuel(k0, g, n)`. The match of round `i` requires the output frontier
/// to equal `ds[i]` — guaranteed because `cmp_out_pregap` packs those very `ds[0..n-1]` as the output's
/// low digits (the loop's caller arranges the output to agree with α on the matched prefix). Induction on
/// `ds.len()` (base `ds.len()==1` = 0 rounds, the head already on the lookahead's invariant). Requires
/// `n ≥ 5`.
pub proof fn lemma_cmp_loop(
    tm: Tm, c: TmConfig,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    pre: Seq<nat>, ds: Seq<nat>, suf: nat, g: nat, out_above: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        pre.len() >= 1,
        forall|k: int| 0 <= k < pre.len() ==> 1 <= #[trigger] pre[k] <= 4,
        ds.len() >= 1,
        forall|k: int| 0 <= k < ds.len() ==> 1 <= #[trigger] ds[k] <= 4,
        g >= 1,
        c == cmp_inv_config(qw, pre, ds, suf, g, out_above, tm.m),
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
    ensures
        tm_run(tm, c, cmp_loop_fuel(pre.len(), g, (ds.len() - 1) as nat))
            == cmp_inv_config(qw,
                pre + ds.subrange(0, (ds.len() - 1) as int),
                ds.subrange((ds.len() - 1) as int, ds.len() as int),
                suf, (g + (ds.len() - 1)) as nat, out_above, tm.m),
    decreases ds.len(),
{
    let m = tm.m;
    let n = (ds.len() - 1) as nat;
    if ds.len() == 1 {
        // ── base case: 0 rounds.
        assert(cmp_loop_fuel(pre.len(), g, 0) == 0);
        assert(tm_run(tm, c, 0) == c);
        assert(pre + ds.subrange(0, 0) =~= pre);
        assert(ds.subrange(0, 1) =~= ds);
        assert((g + 0) as nat == g);
        // both seq args of the ensures config equal those of c's config ⟹ same config.
        assert(cmp_inv_config(qw, pre + ds.subrange(0, (ds.len() - 1) as int),
                    ds.subrange((ds.len() - 1) as int, ds.len() as int),
                    suf, (g + (ds.len() - 1)) as nat, out_above, m)
            == cmp_inv_config(qw, pre, ds, suf, g, out_above, m));
    } else {
        // ── recursive case: ds.len() >= 2, run one round then recurse.
        let pre2 = pre + seq![ds[0]];
        let ds2 = ds.drop_first();
        assert(ds2.len() == ds.len() - 1);
        assert(ds2.len() >= 1);
        // digit validity of the grown prefix / shrunk list.
        assert forall|k: int| 0 <= k < pre2.len() implies 1 <= #[trigger] pre2[k] <= 4 by {
            if k < pre.len() {
                assert(pre2[k] == pre[k]);
            } else {
                assert(pre2[k] == ds[0]);
            }
        }
        assert forall|k: int| 0 <= k < ds2.len() implies 1 <= #[trigger] ds2[k] <= 4 by {
            assert(ds2[k] == ds[k + 1]);
        }

        lemma_cmp_round_packaged(tm, c, qw, qc, qb, qr, pre, ds, suf, g, out_above);
        let c_mid = cmp_inv_config(qw, pre2, ds2, suf, (g + 1) as nat, out_above, m);
        assert(tm_run(tm, c, (2 * pre.len() + 2 * g + 4) as nat) == c_mid);

        lemma_cmp_loop(tm, c_mid, qw, qc, qb, qr, pre2, ds2, suf, (g + 1) as nat, out_above);
        // recursion ensures: tm_run(c_mid, cmp_loop_fuel(pre2.len(), g+1, ds2.len()-1)) == final2.
        let nrec = (ds2.len() - 1) as nat;   // == n - 1
        assert(nrec == n - 1);
        assert(pre2.len() == pre.len() + 1);
        let final2 = cmp_inv_config(qw,
            pre2 + ds2.subrange(0, (ds2.len() - 1) as int),
            ds2.subrange((ds2.len() - 1) as int, ds2.len() as int),
            suf, ((g + 1) + (ds2.len() - 1)) as nat, out_above, m);
        assert(tm_run(tm, c_mid, cmp_loop_fuel(pre2.len(), (g + 1) as nat, nrec)) == final2);

        // ── final2 == the desired final config (seq-arg equalities + gap arithmetic).
        assert(pre2 + ds2.subrange(0, (ds2.len() - 1) as int)
            =~= pre + ds.subrange(0, (ds.len() - 1) as int));
        assert(ds2.subrange((ds2.len() - 1) as int, ds2.len() as int)
            =~= ds.subrange((ds.len() - 1) as int, ds.len() as int));
        assert(((g + 1) + (ds2.len() - 1)) as nat == (g + (ds.len() - 1)) as nat);
        assert(final2 == cmp_inv_config(qw,
            pre + ds.subrange(0, (ds.len() - 1) as int),
            ds.subrange((ds.len() - 1) as int, ds.len() as int),
            suf, (g + (ds.len() - 1)) as nat, out_above, m));

        // ── fuel composition: cmp_loop_fuel(k0, g, n) == round + cmp_loop_fuel(k0+1, g+1, n-1).
        assert(cmp_loop_fuel(pre.len(), g, n)
            == (2 * pre.len() + 2 * g + 4) + cmp_loop_fuel((pre.len() + 1) as nat, (g + 1) as nat, (n - 1) as nat));
        assert(cmp_loop_fuel(pre2.len(), (g + 1) as nat, nrec)
            == cmp_loop_fuel((pre.len() + 1) as nat, (g + 1) as nat, (n - 1) as nat));
        lemma_tm_run_split(tm, c, (2 * pre.len() + 2 * g + 4) as nat,
            cmp_loop_fuel(pre2.len(), (g + 1) as nat, nrec));
        assert(cmp_loop_fuel(pre.len(), g, n)
            == ((2 * pre.len() + 2 * g + 4) + cmp_loop_fuel(pre2.len(), (g + 1) as nat, nrec)) as nat);
    }
}

} // verus!
