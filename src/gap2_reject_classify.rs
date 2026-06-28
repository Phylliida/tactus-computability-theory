//! # GAP-2 G2-F Route (i) — the digit-string DIVERGENCE CLASSIFIER (reject-direction support).
//!
//! Pure digit-string arithmetic backing the REJECT half of the relocation∘compare assembly
//! ([`crate::gap2_reloc_compare`]). When the relocated output `X == drev(output)` differs from the parked
//! α-block `beta` (both reversed, digits `1..4`, end-sentinel `5`), the comparator's decision routes to one
//! of four reject terminals by the **common-prefix length** `p == cpl(X, beta)`:
//!   * `p < |X|` and `p < |beta|`  →  the two strings diverge at `p` (`X[p] ≠ beta[p]`): MISMATCH (`p ≥ 1`)
//!     or MISMATCH0 (`p == 0`);
//!   * `p == |X| < |beta|`  →  `X` a proper prefix of `beta`: TOO-SHORT (output exhausts first);
//!   * `p == |beta| < |X|`  →  `beta` a proper prefix of `X`: TOO-LONG (output overruns α).
//! The `p == |X| == |beta|` case is impossible (it would force `X == beta`).
//!
//! This file provides [`cpl`] + its three structural lemmas ([`lemma_cpl_le`], [`lemma_cpl_match`],
//! [`lemma_cpl_diff`]), the far-sentinel split [`lemma_dpack_far5_split`], and the four "u-shape" lemmas that
//! recast `dpack(X) + m^{|X|}·5` into the exact `u` each terminal reads. Kept in a separate module so the
//! recursive `cpl`/`dpack` triggers do not pollute the assembly proofs. No verifier escape hatches.

use vstd::prelude::*;
use crate::tm_dstring::{dpack, pow_nat, lemma_dpack_append, lemma_pow_nat_unfold};
use crate::tm_copy_refresh::lemma_pow_nat_add;

verus! {

/// **Common-prefix length** of two digit-strings: the largest `p` with `x[0..p] == y[0..p]`. Peels the low
/// element; stops at the first mismatch or when either string ends.
pub open spec fn cpl(x: Seq<nat>, y: Seq<nat>) -> nat
    decreases x.len()
{
    if x.len() == 0 || y.len() == 0 {
        0
    } else if x[0] != y[0] {
        0
    } else {
        (1 + cpl(x.drop_first(), y.drop_first())) as nat
    }
}

/// `cpl(x, y) ≤ |x|` and `≤ |y|`.
pub proof fn lemma_cpl_le(x: Seq<nat>, y: Seq<nat>)
    ensures
        cpl(x, y) <= x.len(),
        cpl(x, y) <= y.len(),
    decreases x.len(),
{
    if x.len() == 0 || y.len() == 0 {
    } else if x[0] != y[0] {
    } else {
        lemma_cpl_le(x.drop_first(), y.drop_first());
    }
}

/// The common prefix matches: `x[i] == y[i]` for every `i < cpl(x, y)`.
pub proof fn lemma_cpl_match(x: Seq<nat>, y: Seq<nat>)
    ensures
        forall|i: int| 0 <= i < cpl(x, y) ==> x[i] == y[i],
    decreases x.len(),
{
    if x.len() == 0 || y.len() == 0 {
    } else if x[0] != y[0] {
    } else {
        let xr = x.drop_first();
        let yr = y.drop_first();
        lemma_cpl_match(xr, yr);
        lemma_cpl_le(xr, yr);
        assert forall|i: int| 0 <= i < cpl(x, y) implies x[i] == y[i] by {
            if i == 0 {
            } else {
                assert(x[i] == xr[i - 1]);
                assert(y[i] == yr[i - 1]);
                assert((i - 1) < cpl(xr, yr));   // since i < cpl(x,y) == 1 + cpl(xr,yr)
            }
        }
    }
}

/// At the divergence point: if `cpl(x, y)` is interior to BOTH strings, the digits there differ.
pub proof fn lemma_cpl_diff(x: Seq<nat>, y: Seq<nat>)
    requires
        cpl(x, y) < x.len(),
        cpl(x, y) < y.len(),
    ensures
        x[cpl(x, y) as int] != y[cpl(x, y) as int],
    decreases x.len(),
{
    // cpl < x.len() ⟹ x.len() ≥ 1, likewise y.
    if x[0] != y[0] {
        // cpl == 0.
    } else {
        let xr = x.drop_first();
        let yr = y.drop_first();
        let p = cpl(x, y);
        assert(p == 1 + cpl(xr, yr));
        assert(cpl(xr, yr) < xr.len());
        assert(cpl(xr, yr) < yr.len());
        lemma_cpl_diff(xr, yr);
        assert(x[p as int] == xr[cpl(xr, yr) as int]);
        assert(y[p as int] == yr[cpl(xr, yr) as int]);
    }
}

/// **The subrange split.** `x == x[0..p] ++ x[p..|x|]`.
pub proof fn lemma_subrange_split(x: Seq<nat>, p: nat)
    requires
        p <= x.len(),
    ensures
        x =~= x.subrange(0, p as int) + x.subrange(p as int, x.len() as int),
{
    let lo = x.subrange(0, p as int);
    let hi = x.subrange(p as int, x.len() as int);
    assert((lo + hi).len() == x.len());
    assert forall|i: int| 0 <= i < x.len() implies x[i] == (lo + hi)[i] by {
        if i < p { assert((lo + hi)[i] == lo[i]); } else { assert((lo + hi)[i] == hi[i - p]); }
    }
}

/// **Far-sentinel split at `p`.** `dpack(x) + m^{|x|}·5 == dpack(x[0..p]) + m^p·(dpack(x[p..]) + m^{|x|-p}·5)`.
/// The output's reversed value with its `5` ceiling, factored at any cut point `p`.
pub proof fn lemma_dpack_far5_split(x: Seq<nat>, p: nat, m: nat)
    requires
        m > 1,
        p <= x.len(),
    ensures
        dpack(x, m) + pow_nat(m, x.len()) * 5
            == dpack(x.subrange(0, p as int), m)
               + pow_nat(m, p) * (dpack(x.subrange(p as int, x.len() as int), m)
                                  + pow_nat(m, (x.len() - p) as nat) * 5),
{
    let k = x.len();
    let lo = x.subrange(0, p as int);
    let hi = x.subrange(p as int, k as int);
    lemma_subrange_split(x, p);
    assert(lo.len() == p);
    assert(hi.len() == (k - p) as nat);
    lemma_dpack_append(lo, hi, m);                  // dpack(lo+hi) == dpack(lo) + m^p·dpack(hi)
    assert(dpack(x, m) == dpack(lo, m) + pow_nat(m, p) * dpack(hi, m));
    lemma_pow_nat_add(m, p, (k - p) as nat);        // m^k == m^p·m^{k-p}
    assert((p + (k - p)) as nat == k);
    assert(dpack(x, m) + pow_nat(m, k) * 5
            == dpack(lo, m) + pow_nat(m, p) * (dpack(hi, m) + pow_nat(m, (k - p) as nat) * 5))
        by(nonlinear_arith)
        requires
            dpack(x, m) == dpack(lo, m) + pow_nat(m, p) * dpack(hi, m),
            pow_nat(m, k) == pow_nat(m, p) * pow_nat(m, (k - p) as nat);
}

// ─────────────────────────────────────────────────────────────────────────────
// The four "u-shape" lemmas: recast `dpack(X) + m^{|X|}·5` into each terminal's `u`.
// ─────────────────────────────────────────────────────────────────────────────

/// **MISMATCH / MISMATCH0 u-shape.** With `x[0..p] == beta[0..p]` and `p < |x|`, the relocated `u` splits as
/// `dpack(beta[0..p]) + m^p·(x[p] + m·out_rest2)` with `out_rest2 == dpack(x[p+1..]) + m^{|x|-p-1}·5`.
pub proof fn lemma_reject_u_mismatch(x: Seq<nat>, beta: Seq<nat>, p: nat, m: nat)
    requires
        m > 1,
        p < x.len(),
        p <= beta.len(),
        forall|i: int| 0 <= i < p ==> x[i] == beta[i],
    ensures
        dpack(x, m) + pow_nat(m, x.len()) * 5
            == dpack(beta.subrange(0, p as int), m)
               + pow_nat(m, p) * (x[p as int]
                    + m * (dpack(x.subrange((p + 1) as int, x.len() as int), m)
                           + pow_nat(m, (x.len() - p - 1) as nat) * 5)),
{
    let k = x.len();
    lemma_dpack_far5_split(x, p, m);
    let hi = x.subrange(p as int, k as int);        // x[p..], nonempty
    assert(hi.len() == (k - p) as nat);
    assert(hi.len() >= 1);
    assert(hi[0] == x[p as int]);
    // dpack(hi) == x[p] + m·dpack(hi.drop_first());  hi.drop_first() == x[p+1..].
    assert(hi.drop_first() =~= x.subrange((p + 1) as int, k as int)) by {
        assert forall|i: int| 0 <= i < (k - p - 1) implies hi.drop_first()[i] == x.subrange((p + 1) as int, k as int)[i] by {
            assert(hi.drop_first()[i] == hi[i + 1]);
            assert(hi[i + 1] == x[p + 1 + i]);
        }
    }
    let tail = x.subrange((p + 1) as int, k as int);
    assert(dpack(hi, m) == x[p as int] + m * dpack(tail, m));
    lemma_pow_nat_unfold(m, (k - p) as nat);        // m^{k-p} == m·m^{k-p-1}
    // dpack(hi) + m^{k-p}·5 == x[p] + m·(dpack(tail) + m^{k-p-1}·5).
    assert(dpack(hi, m) + pow_nat(m, (k - p) as nat) * 5
            == x[p as int] + m * (dpack(tail, m) + pow_nat(m, (k - p - 1) as nat) * 5))
        by(nonlinear_arith)
        requires
            dpack(hi, m) == x[p as int] + m * dpack(tail, m),
            pow_nat(m, (k - p) as nat) == m * pow_nat(m, (k - p - 1) as nat);
    // dpack(x[0..p]) == dpack(beta[0..p]).
    assert(x.subrange(0, p as int) =~= beta.subrange(0, p as int)) by {
        assert forall|i: int| 0 <= i < p implies x.subrange(0, p as int)[i] == beta.subrange(0, p as int)[i] by {
            assert(x.subrange(0, p as int)[i] == x[i]);
            assert(beta.subrange(0, p as int)[i] == beta[i]);
        }
    }
}

/// **TOO-SHORT u-shape.** When `x` is a proper prefix of `beta` (`p == |x| ≤ |beta|`, prefix matched), the
/// relocated `u == dpack(beta[0..p]) + m^p·5` — the output's `5` sentinel sits exactly at the cut.
pub proof fn lemma_reject_u_tooshort(x: Seq<nat>, beta: Seq<nat>, p: nat, m: nat)
    requires
        m > 1,
        p == x.len(),
        p <= beta.len(),
        forall|i: int| 0 <= i < p ==> x[i] == beta[i],
    ensures
        dpack(x, m) + pow_nat(m, x.len()) * 5
            == dpack(beta.subrange(0, p as int), m) + pow_nat(m, p) * 5,
{
    let k = x.len();
    lemma_dpack_far5_split(x, p, m);
    let hi = x.subrange(p as int, k as int);        // empty (p == k)
    assert(hi =~= Seq::<nat>::empty());
    assert(dpack(hi, m) == 0) by { crate::tm_dstring::lemma_dpack_empty(m); }
    assert((k - p) as nat == 0nat);
    assert(pow_nat(m, 0) == 1);
    // dpack(hi) + m^0·5 == 5.
    assert(dpack(hi, m) + pow_nat(m, (k - p) as nat) * 5 == 5) by(nonlinear_arith)
        requires dpack(hi, m) == 0, pow_nat(m, (k - p) as nat) == 1;
    // dpack(x[0..p]) == dpack(beta[0..p]); x[0..p] == x (p == k).
    assert(x.subrange(0, p as int) =~= beta.subrange(0, p as int)) by {
        assert forall|i: int| 0 <= i < p implies x.subrange(0, p as int)[i] == beta.subrange(0, p as int)[i] by {
            assert(x.subrange(0, p as int)[i] == x[i]);
            assert(beta.subrange(0, p as int)[i] == beta[i]);
        }
    }
}

/// **TOO-LONG u-shape.** When `beta` is a proper prefix of `x` (`p == |beta| == L < |x|`, full match), the
/// relocated `u == dpack(beta[0..L-1]) + m^{L-1}·(beta[L-1] + m·(x[L] + m·out_rest2))` with
/// `out_rest2 == dpack(x[L+1..]) + m^{|x|-L-1}·5` — α matched, then output continues with digit `x[L]`.
pub proof fn lemma_reject_u_toolong(x: Seq<nat>, beta: Seq<nat>, m: nat)
    requires
        m > 1,
        beta.len() >= 1,
        beta.len() < x.len(),
        forall|i: int| 0 <= i < beta.len() ==> x[i] == beta[i],
    ensures
        dpack(x, m) + pow_nat(m, x.len()) * 5
            == dpack(beta.subrange(0, (beta.len() - 1) as int), m)
               + pow_nat(m, (beta.len() - 1) as nat)
                 * (beta[(beta.len() - 1) as int]
                    + m * (x[beta.len() as int]
                           + m * (dpack(x.subrange((beta.len() + 1) as int, x.len() as int), m)
                                  + pow_nat(m, (x.len() - beta.len() - 1) as nat) * 5))),
{
    let k = x.len();
    let big_l = beta.len();
    let q = (big_l - 1) as nat;                      // cut at L-1
    lemma_dpack_far5_split(x, q, m);
    let hi = x.subrange(q as int, k as int);         // x[L-1 ..], length k-L+1 ≥ 2
    assert(hi.len() == (k - q) as nat);
    assert(hi.len() >= 2);
    assert(hi[0] == x[q as int]);
    // peel x[L-1] then x[L].
    let hi1 = hi.drop_first();                        // x[L ..]
    assert(hi1 =~= x.subrange(big_l as int, k as int)) by {
        assert forall|i: int| 0 <= i < (k - big_l) implies hi1[i] == x.subrange(big_l as int, k as int)[i] by {
            assert(hi1[i] == hi[i + 1]);
            assert(hi[i + 1] == x[q + 1 + i]);
        }
    }
    let hi2 = hi1.drop_first();                       // x[L+1 ..]
    assert(hi2 =~= x.subrange((big_l + 1) as int, k as int)) by {
        assert forall|i: int| 0 <= i < (k - big_l - 1) implies hi2[i] == x.subrange((big_l + 1) as int, k as int)[i] by {
            assert(hi2[i] == hi1[i + 1]);
            assert(hi1[i + 1] == x[big_l + 1 + i]);
        }
    }
    assert(hi1[0] == x[big_l as int]);
    let tail = x.subrange((big_l + 1) as int, k as int);
    assert(dpack(hi, m) == x[q as int] + m * dpack(hi1, m));
    assert(dpack(hi1, m) == x[big_l as int] + m * dpack(tail, m));
    // m^{k-q} == m·m^{k-L} == m·m·m^{k-L-1}  (k-q == k-L+1, two unfolds; avoids pow_nat(m,2)).
    lemma_pow_nat_unfold(m, (k - q) as nat);        // m^{k-q} == m·m^{k-q-1}
    assert((k - q - 1) as nat == (k - big_l) as nat);
    lemma_pow_nat_unfold(m, (k - big_l) as nat);    // m^{k-L} == m·m^{k-L-1}
    // dpack(hi) + m^{k-q}·5 == x[L-1] + m·(x[L] + m·(dpack(tail) + m^{k-L-1}·5)).
    assert(dpack(hi, m) + pow_nat(m, (k - q) as nat) * 5
            == x[q as int]
               + m * (x[big_l as int]
                      + m * (dpack(tail, m) + pow_nat(m, (k - big_l - 1) as nat) * 5)))
        by(nonlinear_arith)
        requires
            dpack(hi, m) == x[q as int] + m * dpack(hi1, m),
            dpack(hi1, m) == x[big_l as int] + m * dpack(tail, m),
            pow_nat(m, (k - q) as nat) == m * pow_nat(m, (k - big_l) as nat),
            pow_nat(m, (k - big_l) as nat) == m * pow_nat(m, (k - big_l - 1) as nat);
    // x[L-1] == beta[L-1]; dpack(x[0..L-1]) == dpack(beta[0..L-1]).
    assert(x[q as int] == beta[q as int]);
    assert(x.subrange(0, q as int) =~= beta.subrange(0, q as int)) by {
        assert forall|i: int| 0 <= i < q implies x.subrange(0, q as int)[i] == beta.subrange(0, q as int)[i] by {
            assert(x.subrange(0, q as int)[i] == x[i]);
            assert(beta.subrange(0, q as int)[i] == beta[i]);
        }
    }
}

} // verus!
