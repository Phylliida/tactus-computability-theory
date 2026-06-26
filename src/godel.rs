//! # Gödel encoding for the k→2 register reduction (L1).
//!
//! `docs/gap2-register-to-tm-plan.md` §L1. The 2-counter Minsky simulation of a k-register
//! machine stores the register vector `(r₀,…,r_{k-1})` as a single Gödel number
//! `godel(regs) = ∏_j base(j)^{regs[j]}`, with the other counter as scratch. `Inc(rᵢ)` becomes
//! multiply-by-`base(i)`, and the `DecJump(rᵢ)` zero-test becomes the divisibility query
//! `base(i) | godel(regs)`. This module supplies the abstract value `godel` and the headline
//! arithmetic fact the zero-test needs:
//!
//! > **`lemma_godel_div_iff`**: for `i < regs.len()`, `base(i) | godel(regs) ⟺ regs[i] ≥ 1`.
//!
//! To dodge primality (and the unbounded prime sequence its proof would need) the base sequence
//! is **Sylvester/Euclid**: `base(0)=2`, `base(j)=1+∏_{i<j} base(i)`. Then `base(j) ≡ 1 mod base(i)`
//! for `i<j`, so the sequence is pairwise coprime by a one-line argument — exactly the property
//! the divisibility iff consumes (via `number_theory`'s coprimality lemmas). Fully verified.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use crate::number_theory::*;

verus! {

// ── The Sylvester/Euclid pairwise-coprime base sequence ──
// base(0) = 2 ; base(j) = 1 + prod_base_below(j) where prod_base_below(j) = ∏_{i<j} base(i).
// Mutually recursive: base(j) reads prod_base_below(j); prod_base_below(j) reads base(j-1).
// The (index, tag) lexicographic measure orders base above prod_base_below at equal index.

pub open spec fn base(j: nat) -> nat
    decreases j, 1nat,
{
    if j == 0 { 2 } else { 1 + prod_base_below(j) }
}

pub open spec fn prod_base_below(j: nat) -> nat
    decreases j, 0nat,
{
    if j == 0 { 1 } else { prod_base_below((j - 1) as nat) * base((j - 1) as nat) }
}

// ── base ≥ 2 and the product is positive ──

pub proof fn lemma_prod_base_below_positive(j: nat)
    ensures prod_base_below(j) >= 1,
    decreases j, 0nat,
{
    if j == 0 {
    } else {
        lemma_prod_base_below_positive((j - 1) as nat);
        lemma_base_ge_2((j - 1) as nat);
        assert(prod_base_below((j - 1) as nat) * base((j - 1) as nat) >= 1) by(nonlinear_arith)
            requires prod_base_below((j - 1) as nat) >= 1, base((j - 1) as nat) >= 2;
    }
}

pub proof fn lemma_base_ge_2(j: nat)
    ensures base(j) >= 2,
    decreases j, 1nat,
{
    if j == 0 {
    } else {
        lemma_prod_base_below_positive(j);
        assert(base(j) == 1 + prod_base_below(j));
    }
}

// ── base(i) | prod_base_below(j) for i < j ──

pub proof fn lemma_base_divides_prod_below(i: nat, j: nat)
    requires i < j,
    ensures prod_base_below(j) % base(i) == 0,
    decreases j,
{
    lemma_base_ge_2(i);   // base(i) >= 2 > 0
    // j >= 1 since i < j. prod_base_below(j) = prod_base_below(j-1) * base(j-1).
    if i == (j - 1) as nat {
        lemma_mod_self(base(i));   // base(i) % base(i) == 0
        // prod_base_below(j) = prod_base_below(j-1) * base(i).
        lemma_divides_mul(base(i), base(i), prod_base_below((j - 1) as nat));
        assert(prod_base_below(j)
            == prod_base_below((j - 1) as nat) * base((j - 1) as nat));
    } else {
        lemma_base_divides_prod_below(i, (j - 1) as nat);   // prod_base_below(j-1) % base(i) == 0
        lemma_divides_mul(base(i), prod_base_below((j - 1) as nat), base((j - 1) as nat));
        assert(prod_base_below(j)
            == prod_base_below((j - 1) as nat) * base((j - 1) as nat));
    }
}

// ── Pairwise coprimality: base(i) ≡ 1 mod base(hi) ⟹ gcd == 1 ──

pub proof fn lemma_base_coprime(i: nat, j: nat)
    requires i != j,
    ensures gcd(base(i), base(j)) == 1,
{
    lemma_base_ge_2(i);
    lemma_base_ge_2(j);
    let bi = base(i) as int;
    let bj = base(j) as int;
    if i < j {
        // base(j) = 1 + prod_base_below(j), base(i) | prod_base_below(j).
        lemma_base_divides_prod_below(i, j);
        let pbj = prod_base_below(j) as int;
        assert(pbj % bi == 0);
        lemma_fundamental_div_mod(pbj, bi);
        let quo = pbj / bi;
        assert(pbj == bi * quo) by(nonlinear_arith)
            requires pbj == bi * (pbj / bi) + pbj % bi, pbj % bi == 0, quo == pbj / bi;
        assert(base(j) == 1 + prod_base_below(j));   // j >= 1
        assert(bj == 1 + pbj);
        // (-quo)*base(i) + 1*base(j) == 1.
        assert((-quo) * bi + 1 * bj == 1) by(nonlinear_arith)
            requires bj == 1 + pbj, pbj == bi * quo;
        lemma_gcd_one_from_combo(base(i), base(j), -quo, 1);
    } else {
        // j < i: base(i) = 1 + prod_base_below(i), base(j) | prod_base_below(i).
        lemma_base_divides_prod_below(j, i);
        let pbi = prod_base_below(i) as int;
        assert(pbi % bj == 0);
        lemma_fundamental_div_mod(pbi, bj);
        let quo = pbi / bj;
        assert(pbi == bj * quo) by(nonlinear_arith)
            requires pbi == bj * (pbi / bj) + pbi % bj, pbi % bj == 0, quo == pbi / bj;
        assert(base(i) == 1 + prod_base_below(i));   // i >= 1
        assert(bi == 1 + pbi);
        // 1*base(i) + (-quo)*base(j) == 1.
        assert(1 * bi + (-quo) * bj == 1) by(nonlinear_arith)
            requires bi == 1 + pbi, pbi == bj * quo;
        lemma_gcd_one_from_combo(base(i), base(j), 1, -quo);
    }
}

// ── The Gödel encoding ──
// godel_prod(regs, upto) = ∏_{j<upto} base(j)^{regs[j]} ; godel_encode = the full product.

pub open spec fn godel_prod(regs: Seq<nat>, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 {
        1
    } else {
        godel_prod(regs, (upto - 1) as nat)
            * pow_nat(base((upto - 1) as nat), regs[(upto - 1) as int])
    }
}

pub open spec fn godel_encode(regs: Seq<nat>) -> nat {
    godel_prod(regs, regs.len())
}

// ── The i-th factor divides the product (forward divisibility) ──

pub proof fn lemma_factor_divides_prod(regs: Seq<nat>, i: nat, upto: nat)
    requires i < upto,
    ensures godel_prod(regs, upto) % pow_nat(base(i), regs[i as int]) == 0,
    decreases upto,
{
    lemma_base_ge_2(i);   // base(i) >= 2 > 0
    let pf_i = pow_nat(base(i), regs[i as int]);
    lemma_pow_positive(base(i), regs[i as int]);   // pf_i >= 1
    let pow_last = pow_nat(base((upto - 1) as nat), regs[(upto - 1) as int]);
    assert(godel_prod(regs, upto) == godel_prod(regs, (upto - 1) as nat) * pow_last);
    if i == (upto - 1) as nat {
        assert(pf_i == pow_last);
        lemma_mod_self(pf_i);
        lemma_divides_mul(pf_i, pf_i, godel_prod(regs, (upto - 1) as nat));
        // ensures (godel_prod(upto-1) * pf_i) % pf_i == 0 == godel_prod(upto) % pf_i.
    } else {
        lemma_factor_divides_prod(regs, i, (upto - 1) as nat);   // godel_prod(upto-1) % pf_i == 0
        lemma_divides_mul(pf_i, godel_prod(regs, (upto - 1) as nat), pow_last);
        // ensures (godel_prod(upto-1) * pow_last) % pf_i == 0 == godel_prod(upto) % pf_i.
    }
}

// ── base(i) coprime to the product when regs[i] = 0 (backward non-divisibility) ──

pub proof fn lemma_godel_coprime(regs: Seq<nat>, i: nat, upto: nat)
    requires i >= upto || regs[i as int] == 0,
    ensures gcd(base(i), godel_prod(regs, upto)) == 1,
    decreases upto,
{
    lemma_base_ge_2(i);   // base(i) >= 2 > 0
    if upto == 0 {
        assert(godel_prod(regs, upto) == 1);
        lemma_gcd_one(base(i));
    } else {
        let pow_last = pow_nat(base((upto - 1) as nat), regs[(upto - 1) as int]);
        assert(godel_prod(regs, upto) == godel_prod(regs, (upto - 1) as nat) * pow_last);
        // IH precondition holds: i >= upto-1 ∨ regs[i] == 0.
        lemma_godel_coprime(regs, i, (upto - 1) as nat);   // gcd(base(i), godel_prod(upto-1)) == 1
        // gcd(base(i), pow_last) == 1.
        if (upto - 1) as nat == i {
            // i < upto ⟹ the i>=upto disjunct is false ⟹ regs[i] == 0 ⟹ pow_last = base(i)^0 = 1.
            assert(regs[i as int] == 0);
            assert(pow_last == pow_nat(base(i), 0));
            assert(pow_last == 1);
            lemma_gcd_one(base(i));
        } else {
            lemma_base_coprime(i, (upto - 1) as nat);   // gcd(base(i), base(upto-1)) == 1
            lemma_coprime_pow(base(i), base((upto - 1) as nat), regs[(upto - 1) as int]);
            // gcd(base(i), pow_last) == 1.
        }
        lemma_coprime_mul(base(i), godel_prod(regs, (upto - 1) as nat), pow_last);
        // gcd(base(i), godel_prod(upto-1) * pow_last) == 1 == gcd(base(i), godel_prod(upto)).
    }
}

// ── The headline divisibility iff ──

/// **`base(i) | godel(regs) ⟺ regs[i] ≥ 1`**, for `i` within the register vector. This is the
/// arithmetic core of the 2-counter `DecJump(rᵢ)` zero-test in the Gödel k→2 simulation.
pub proof fn lemma_godel_div_iff(regs: Seq<nat>, i: nat)
    requires i < regs.len(),
    ensures godel_encode(regs) % base(i) == 0 <==> regs[i as int] >= 1,
{
    lemma_base_ge_2(i);   // base(i) >= 2
    let g = godel_encode(regs);
    let len = regs.len();
    let pf_i = pow_nat(base(i), regs[i as int]);
    assert(g == godel_prod(regs, len));

    // Forward: regs[i] >= 1 ⟹ base(i) | g.
    if regs[i as int] >= 1 {
        lemma_factor_divides_prod(regs, i, len);          // g % pf_i == 0
        lemma_base_divides_pow(base(i), regs[i as int]);  // pf_i % base(i) == 0
        lemma_pow_positive(base(i), regs[i as int]);      // pf_i >= 1
        lemma_divides_trans(base(i), pf_i, g);            // g % base(i) == 0
        assert(godel_encode(regs) % base(i) == 0);
    }

    // Backward: base(i) | g ⟹ regs[i] >= 1.  Contrapositive: regs[i] == 0 ⟹ base(i) ∤ g.
    if regs[i as int] == 0 {
        lemma_godel_coprime(regs, i, len);                // gcd(base(i), g) == 1
        lemma_coprime_not_divides(base(i), g);            // g % base(i) != 0
        assert(godel_encode(regs) % base(i) != 0);
    }
}

} // verus!
