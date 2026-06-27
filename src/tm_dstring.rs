//! # GAP-2 G2-F Route (i) brick R-P (foundation) — the base-m digit-string algebra.
//!
//! The copy-and-park (R-P) and ping-pong compare (R-cmp) phases manipulate `α`'s base-m digits as a
//! *string of arbitrary symbols `1..4`* — unlike the counter gadgets, whose blocks are unary (all `1`s,
//! captured by `repunit_m`/`pile_ones` in [`crate::tm_two_counter`]/[`crate::tm_walk`]). This module
//! is the symbol-agnostic analog: a digit sequence `ds : Seq<nat>` packed low-first into a base-m nat by
//! [`dpack`], with the pop/low/`digits_le`/length algebra the digit-walk loop invariants read.
//!
//! `dpack(ds, m) = ds[0] + m·ds[1] + m²·ds[2] + …` — `ds[0]` is the lowest digit (nearest the head).
//! The defining recurrence `dpack(ds) = ds[0] + m·dpack(ds[1..])` is exactly "push the low digit `ds[0]`
//! on top of the rest", the atomic edit a left/right move performs. Mirrors the `repunit_m` lemmas one
//! for one, but indexed by the actual digit values.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-P). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm_h0_bwd::{digits_le, lemma_digits_le_push};

verus! {

/// `m^k`, the place value of position `k` (low-first), defined by the standard recurrence.
pub open spec fn pow_nat(m: nat, k: nat) -> nat
    decreases k
{
    if k == 0 { 1 } else { m * pow_nat(m, (k - 1) as nat) }
}

/// `pow_nat(m, k) == m·pow_nat(m, k-1)` for `k ≥ 1` (the defining unfold, named for triggering).
pub proof fn lemma_pow_nat_unfold(m: nat, k: nat)
    requires
        k >= 1,
    ensures
        pow_nat(m, k) == m * pow_nat(m, (k - 1) as nat),
{
}

/// `dpack(ds, m)` packs the digit sequence `ds` low-first into a base-`m` value: `ds[0]` is the lowest
/// digit, `ds[ds.len()-1]` the highest. `dpack(ds) = ds[0] + m·dpack(ds.drop_first())`.
pub open spec fn dpack(ds: Seq<nat>, m: nat) -> nat
    decreases ds.len()
{
    if ds.len() == 0 {
        0
    } else {
        ds[0] + m * dpack(ds.drop_first(), m)
    }
}

/// The empty string packs to `0` (a blank tape).
pub proof fn lemma_dpack_empty(m: nat)
    ensures
        dpack(Seq::empty(), m) == 0,
{
    assert(Seq::<nat>::empty().len() == 0);
}

/// **Pop the low digit.** For a nonempty string whose low digit is a real symbol (`ds[0] < m`),
/// `dpack(ds) % m == ds[0]` and `dpack(ds) / m == dpack(ds.drop_first())`. The arithmetic a right/left
/// move reads when stepping over one cell.
pub proof fn lemma_dpack_pop(ds: Seq<nat>, m: nat)
    requires
        m > 1,
        ds.len() >= 1,
        ds[0] < m,
    ensures
        dpack(ds, m) % m == ds[0],
        dpack(ds, m) / m == dpack(ds.drop_first(), m),
{
    let x = dpack(ds.drop_first(), m);
    // dpack(ds) == ds[0] + m·x == x·m + ds[0].
    assert(dpack(ds, m) == ds[0] + m * x);
    assert(m * x == x * m) by(nonlinear_arith);
    assert(dpack(ds, m) == x * m + ds[0]);
    lemma_div_mod_step(x, m, ds[0]);   // (x·m + ds[0])/m == x, %m == ds[0]  (ds[0] < m)
}

/// **Push a low digit.** Prepending a real symbol `d < m` as the new lowest digit multiplies by `m` and
/// adds `d`: `dpack(seq![d] + ds) == d + m·dpack(ds)`. The atomic edit a copy gadget performs.
pub proof fn lemma_dpack_push(d: nat, ds: Seq<nat>, m: nat)
    ensures
        dpack(seq![d] + ds, m) == d + m * dpack(ds, m),
{
    let pushed = seq![d] + ds;
    assert(pushed.len() == ds.len() + 1);
    assert(pushed[0] == d);
    assert(pushed.drop_first() =~= ds);
    // dpack(pushed) == pushed[0] + m·dpack(pushed.drop_first()) == d + m·dpack(ds).
}

/// **Digit bound.** If every digit of `ds` is a real symbol (`≤ n < m`), the packed value satisfies the
/// tape invariant `digits_le(dpack(ds), m, n)`. By induction, pushing each `ds[0] ≤ n`.
pub proof fn lemma_dpack_digits_le(ds: Seq<nat>, m: nat, n: nat)
    requires
        m > 1,
        n < m,
        forall|i: int| 0 <= i < ds.len() ==> #[trigger] ds[i] <= n,
    ensures
        digits_le(dpack(ds, m), m, n),
    decreases ds.len(),
{
    if ds.len() == 0 {
        lemma_dpack_empty(m);
        // dpack == 0 ⟹ digits_le holds (x == 0 branch).
    } else {
        let rest = ds.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i] <= n by {
            assert(rest[i] == ds[i + 1]);
        }
        lemma_dpack_digits_le(rest, m, n);   // digits_le(dpack(rest))
        let x = dpack(rest, m);
        assert(ds[0] <= n);
        // dpack(ds) == ds[0] + m·x == x·m + ds[0]; push the digit ds[0] ≤ n.
        assert(m * x == x * m) by(nonlinear_arith);
        lemma_digits_le_push(x, m, n, ds[0]);   // digits_le(x·m + ds[0])
        assert(dpack(ds, m) == x * m + ds[0]);
    }
}

/// A string whose digits are all **nonzero** packs to a nonzero value iff nonempty — more precisely the
/// low digit `dpack(ds) % m == ds[0] > 0`, so the head never mistakes a digit cell for the blank `0`
/// that terminates the block. (The walk-until-blank loop's progress guarantee.)
pub proof fn lemma_dpack_low_nonzero(ds: Seq<nat>, m: nat)
    requires
        m > 1,
        ds.len() >= 1,
        ds[0] < m,
        ds[0] > 0,
    ensures
        dpack(ds, m) % m == ds[0],
        dpack(ds, m) > 0,
{
    lemma_dpack_pop(ds, m);
    // dpack(ds) % m == ds[0] > 0 ⟹ dpack(ds) > 0 (a multiple of m plus a nonzero residue).
    assert(dpack(ds, m) > 0) by {
        if dpack(ds, m) == 0 {
            assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        }
    }
}

/// **Append-split.** `dpack(lo + hi) == dpack(lo) + m^{lo.len()}·dpack(hi)` — the low block `lo` sits
/// below the high block `hi`. Stated via the push recurrence so `m^k` stays implicit: the low block's
/// digits are read first, then the high block continues at the same packing. Useful for the
/// `[counters | scratch | sentinel | α | sentinel]` layout where one stack holds several blocks.
pub proof fn lemma_dpack_append(lo: Seq<nat>, hi: Seq<nat>, m: nat)
    ensures
        dpack(lo + hi, m) == dpack(lo, m) + pow_nat(m, lo.len()) * dpack(hi, m),
    decreases lo.len(),
{
    if lo.len() == 0 {
        assert(lo + hi =~= hi);
        assert(pow_nat(m, 0) == 1);
    } else {
        let lo_rest = lo.drop_first();
        let k1 = (lo.len() - 1) as nat;
        assert((lo + hi).drop_first() =~= lo_rest + hi);
        assert((lo + hi)[0] == lo[0]);
        assert(lo_rest.len() == k1);
        // unfold: dpack(lo+hi) == lo[0] + m·dpack(lo_rest + hi); dpack(lo) == lo[0] + m·dpack(lo_rest).
        assert(dpack(lo + hi, m) == lo[0] + m * dpack(lo_rest + hi, m));
        assert(dpack(lo, m) == lo[0] + m * dpack(lo_rest, m));
        lemma_dpack_append(lo_rest, hi, m);   // IH
        assert(dpack(lo_rest + hi, m) == dpack(lo_rest, m) + pow_nat(m, k1) * dpack(hi, m));
        lemma_pow_nat_unfold(m, lo.len());
        assert(pow_nat(m, lo.len()) == m * pow_nat(m, k1));
        // distribute & re-associate the m·(… + …) term.
        assert(m * (dpack(lo_rest, m) + pow_nat(m, k1) * dpack(hi, m))
            == m * dpack(lo_rest, m) + m * (pow_nat(m, k1) * dpack(hi, m))) by(nonlinear_arith);
        assert(m * (pow_nat(m, k1) * dpack(hi, m)) == (m * pow_nat(m, k1)) * dpack(hi, m))
            by(nonlinear_arith);
        // chain: dpack(lo+hi) == (lo[0] + m·dpack(lo_rest)) + (m·pow_nat(m,k1))·dpack(hi).
        assert(dpack(lo + hi, m)
            == (lo[0] + m * dpack(lo_rest, m)) + (m * pow_nat(m, k1)) * dpack(hi, m));
    }
}

} // verus!
