//! # Number-theory core for the Gödel k→2 reduction (L1).
//!
//! `docs/gap2-register-to-tm-plan.md` §L1. The 2-counter (Minsky) simulation of a k-register
//! machine packs the registers into one Gödel number `∏ base(j)^{regs[j]}`; the `DecJump`
//! zero-test reduces to the divisibility fact `base(i) | godel ⟺ regs[i] ≥ 1`. The *only*
//! number theory that fact needs is that the base sequence is **pairwise coprime** (and `≥ 2`).
//!
//! This module is the reusable coprimality core: `gcd` (Euclid), `ext_gcd`/`lemma_bezout`
//! (Bézout identity), and the three derived facts the Gödel proof consumes —
//! [`lemma_coprime_mul`] (coprimality is multiplicative), [`lemma_coprime_pow`] (coprime to a
//! base ⟹ coprime to its powers), and [`lemma_coprime_not_divides`] (`a ≥ 2` coprime to `x`
//! ⟹ `a ∤ x`). The gcd/Bézout halves are ported from the verified `verus-fixed-point`
//! `number_theory.rs` (Z3); the three derived lemmas are new. Fully verified, no verifier
//! escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_small_mod};

verus! {

// ── pow ────────────────────────────────────────────────
// b^k as a spec function (used by the Gödel encoding and lemma_coprime_pow).

pub open spec fn pow_nat(b: nat, k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 } else { b * pow_nat(b, (k - 1) as nat) }
}

/// `b^k ≥ 1` when `b ≥ 1`.
pub proof fn lemma_pow_positive(b: nat, k: nat)
    requires b >= 1,
    ensures pow_nat(b, k) >= 1,
    decreases k,
{
    if k == 0 {
    } else {
        lemma_pow_positive(b, (k - 1) as nat);
        assert(b * pow_nat(b, (k - 1) as nat) >= 1) by(nonlinear_arith)
            requires b >= 1, pow_nat(b, (k - 1) as nat) >= 1;
    }
}

/// `b | b^k` when `k ≥ 1` (the i-th factor carries `base(i)` once `regs[i] ≥ 1`).
pub proof fn lemma_base_divides_pow(b: nat, k: nat)
    requires b >= 1, k >= 1,
    ensures pow_nat(b, k) % b == 0,
{
    // b^k = b * b^{k-1}, so b | b^k.
    let q = pow_nat(b, (k - 1) as nat);
    assert(pow_nat(b, k) == b * q);
    // converse wants x == q_arg*d + r, i.e. (q as int)*(b as int); commute the cast product.
    assert((b * q) as int == (q as int) * (b as int)) by(nonlinear_arith);
    lemma_fundamental_div_mod_converse((b * q) as int, b as int, q as int, 0);
    assert(pow_nat(b, k) % b == 0);
}

// ── GCD (Euclidean algorithm) ──────────────────────────

pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a } else { gcd(b, a % b) }
}

// ── Extended Euclidean — Bézout coefficients ───────────
// Returns (s, t) with gcd(a, b) = s*a + t*b.

pub open spec fn ext_gcd(a: nat, b: nat) -> (int, int)
    decreases b,
{
    if b == 0 {
        (1int, 0int)
    } else {
        let r = ext_gcd(b, a % b);
        let s1 = r.0;
        let t1 = r.1;
        let q = (a / b) as int;
        (t1, s1 - q * t1)
    }
}

// ── Helper: if d divides both b and r, it divides q*b+r ──

pub proof fn lemma_divides_linear_combination(d: int, b: int, r: int, q: int)
    requires
        d > 0,
        b % d == 0,
        r % d == 0,
    ensures
        (q * b + r) % d == 0,
{
    lemma_fundamental_div_mod(b, d);
    lemma_fundamental_div_mod(r, d);
    let kb = b / d;
    let kr = r / d;
    let total = q * b + r;
    let qtotal = q * kb + kr;
    assert(total == d * qtotal) by (nonlinear_arith)
        requires
            b == d * kb + b % d, b % d == 0,
            r == d * kr + r % d, r % d == 0,
            total == q * b + r, qtotal == q * kb + kr;
    lemma_fundamental_div_mod_converse(total, d, qtotal, 0);
}

// ── GCD divides both arguments ─────────────────────────

pub proof fn lemma_gcd_divides(a: nat, b: nat)
    requires a > 0 || b > 0,
    ensures
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases b,
{
    if b == 0 {
        assert(gcd(a, b) == a);
        assert(a > 0nat);
        lemma_fundamental_div_mod_converse(a as int, a as int, 1, 0);
        lemma_fundamental_div_mod_converse(0int, a as int, 0, 0);
    } else {
        lemma_gcd_divides(b, a % b);
        let d = gcd(a, b);
        assert(b % d == 0nat);
        assert((a % b) % d == 0nat);
        lemma_fundamental_div_mod(a as int, b as int);
        let q = (a as int) / (b as int);
        let r = (a as int) % (b as int);
        lemma_gcd_positive(b, a % b);
        lemma_divides_linear_combination(d as int, b as int, r, q);
        assert(a as int == (b as int) * q + r);
        assert((b as int) * q + r == q * (b as int) + r) by (nonlinear_arith);
        assert((a as int) % (d as int) == 0);
    }
}

// ── GCD is positive when inputs are ────────────────────

pub proof fn lemma_gcd_positive(a: nat, b: nat)
    requires a > 0 || b > 0,
    ensures gcd(a, b) > 0,
    decreases b,
{
    if b == 0 {
        assert(gcd(a, b) == a);
    } else {
        if a % b > 0 {
            lemma_gcd_positive(b, a % b);
        } else {
            assert(a % b == 0nat);
            assert(gcd(b, 0nat) == b);
        }
    }
}

// ── Bézout's Identity ──────────────────────────────────

pub proof fn lemma_bezout(a: nat, b: nat)
    ensures
        gcd(a, b) as int == ext_gcd(a, b).0 * (a as int) + ext_gcd(a, b).1 * (b as int),
    decreases b,
{
    if b == 0 {
    } else {
        lemma_bezout(b, a % b);
        let s1 = ext_gcd(b, a % b).0;
        let t1 = ext_gcd(b, a % b).1;
        let q = (a / b) as int;
        let r = (a % b) as int;
        let ai = a as int;
        let bi = b as int;
        lemma_fundamental_div_mod(ai, bi);
        assert(s1 * bi + t1 * r == t1 * ai + (s1 - q * t1) * bi)
            by (nonlinear_arith)
            requires ai == bi * q + r;
    }
}

// ── gcd(a, 1) == 1 ─────────────────────────────────────

pub proof fn lemma_gcd_one(a: nat)
    ensures gcd(a, 1) == 1,
{
    // gcd(a,1) = gcd(1, a % 1) = gcd(1, 0) = 1.
    assert(a % 1 == 0) by(nonlinear_arith);
    assert(gcd(a, 1) == gcd(1, a % 1));
    assert(gcd(1, 0nat) == 1);
}

// ── A Bézout combination of 1 forces gcd == 1 ──────────

/// If `s·a + t·n == 1` for integers `s,t`, then `gcd(a,n) == 1`.
pub proof fn lemma_gcd_one_from_combo(a: nat, n: nat, s: int, t: int)
    requires
        a > 0,
        s * (a as int) + t * (n as int) == 1,
    ensures
        gcd(a, n) == 1,
{
    let d = gcd(a, n);
    lemma_gcd_positive(a, n);
    lemma_gcd_divides(a, n);
    // d | a and d | n.
    assert(a % d == 0nat);
    assert(n % d == 0nat);
    let di = d as int;
    // (s*a) % d == 0, then (t*n + s*a) % d == 0.
    lemma_divides_linear_combination(di, a as int, 0, s);   // (s*a + 0) % d == 0
    assert((s * (a as int)) % di == 0) by {
        assert(s * (a as int) + 0 == s * (a as int));
    }
    lemma_divides_linear_combination(di, n as int, s * (a as int), t);  // (t*n + s*a) % d == 0
    assert((t * (n as int) + s * (a as int)) % di == 0);
    assert(t * (n as int) + s * (a as int) == 1) by(nonlinear_arith)
        requires s * (a as int) + t * (n as int) == 1;
    assert((1int) % di == 0);
    // 1 % d == 0 with d > 0 forces d == 1.
    if d > 1 {
        lemma_small_mod(1, d);   // 1 < d ⟹ 1 % d == 1
        assert(false);
    }
}

// ── Coprimality is multiplicative ──────────────────────

/// `gcd(a,b) == 1 ∧ gcd(a,c) == 1 ⟹ gcd(a, b*c) == 1`.
pub proof fn lemma_coprime_mul(a: nat, b: nat, c: nat)
    requires
        a > 0,
        gcd(a, b) == 1,
        gcd(a, c) == 1,
    ensures
        gcd(a, b * c) == 1,
{
    // Avoid the degree-3 Bézout-product identity: multiply gcd(a,b)'s Bézout eq by c, conclude
    // d := gcd(a, b*c) divides c, then d | a ∧ d | c ∧ gcd(a,c)=1 force d = 1.
    let d = gcd(a, b * c);
    lemma_gcd_positive(a, b * c);
    lemma_gcd_divides(a, b * c);                    // a % d == 0, (b*c) % d == 0
    let di = d as int;
    let ai = a as int;
    let bi = b as int;
    let ci = c as int;
    assert(a % d == 0nat);
    assert((b * c) % d == 0nat);
    assert((b * c) as int == bi * ci);              // cast distributes over *
    assert((bi * ci) % di == 0);                    // same Euclidean-mod term as (b*c) % d

    // From gcd(a,b)=1: 1 == s1*a + t1*b. Multiply by c: c == (s1*c)*a + t1*(b*c).
    lemma_bezout(a, b);
    let s1 = ext_gcd(a, b).0;
    let t1 = ext_gcd(a, b).1;
    assert(s1 * ai + t1 * bi == 1);
    assert(ci == (s1 * ci) * ai + t1 * (bi * ci)) by(nonlinear_arith)
        requires s1 * ai + t1 * bi == 1;
    // d | a ⟹ d | (s1*c)*a ;  d | (b*c) ⟹ d | t1*(b*c) ;  sum == c ⟹ d | c.
    lemma_divides_linear_combination(di, ai, 0, s1 * ci);                  // ((s1*c)*a)%d==0
    assert(((s1 * ci) * ai) % di == 0) by {
        assert((s1 * ci) * ai + 0 == (s1 * ci) * ai);
    }
    lemma_divides_linear_combination(di, bi * ci, (s1 * ci) * ai, t1);     // (t1*(b*c)+(s1*c)*a)%d==0
    assert(t1 * (bi * ci) + (s1 * ci) * ai == ci);
    assert(ci % di == 0);

    // From gcd(a,c)=1: 1 == s2*a + t2*c. d | a ∧ d | c ⟹ d | 1 ⟹ d == 1.
    lemma_bezout(a, c);
    let s2 = ext_gcd(a, c).0;
    let t2 = ext_gcd(a, c).1;
    assert(s2 * ai + t2 * ci == 1);
    lemma_divides_linear_combination(di, ai, 0, s2);                       // (s2*a)%d==0
    assert((s2 * ai) % di == 0) by {
        assert(s2 * ai + 0 == s2 * ai);
    }
    lemma_divides_linear_combination(di, ci, s2 * ai, t2);                 // (t2*c+s2*a)%d==0
    assert(t2 * ci + s2 * ai == 1) by(nonlinear_arith)
        requires s2 * ai + t2 * ci == 1;
    assert((1int) % di == 0);
    if d > 1 {
        lemma_small_mod(1, d);
        assert(false);
    }
}

// ── Coprime to a base ⟹ coprime to its powers ──────────

/// `gcd(a,b) == 1 ⟹ gcd(a, b^k) == 1`.
pub proof fn lemma_coprime_pow(a: nat, b: nat, k: nat)
    requires
        a > 0,
        gcd(a, b) == 1,
    ensures
        gcd(a, pow_nat(b, k)) == 1,
    decreases k,
{
    if k == 0 {
        assert(pow_nat(b, 0) == 1);
        lemma_gcd_one(a);
    } else {
        lemma_coprime_pow(a, b, (k - 1) as nat);
        // pow_nat(b,k) == b * pow_nat(b,k-1).
        lemma_coprime_mul(a, b, pow_nat(b, (k - 1) as nat));
        assert(pow_nat(b, k) == b * pow_nat(b, (k - 1) as nat));
    }
}

// ── Coprime + (a ≥ 2) ⟹ non-divisibility ───────────────

/// If `a ≥ 2` is coprime to `x`, then `a ∤ x`.
pub proof fn lemma_coprime_not_divides(a: nat, x: nat)
    requires
        a >= 2,
        gcd(a, x) == 1,
    ensures
        x % a != 0,
{
    lemma_bezout(a, x);
    let s = ext_gcd(a, x).0;
    let t = ext_gcd(a, x).1;
    let ai = a as int;
    let xi = x as int;
    assert(s * ai + t * xi == 1);
    if x % a == 0 {
        // x % a == 0 (nat) gives xi % ai == 0 (same Euclidean-mod term under the int cast).
        assert(xi % ai == 0);
        lemma_fundamental_div_mod(xi, ai);   // xi == ai*(xi/ai) + xi%ai
        let q = xi / ai;
        assert(xi == ai * q) by(nonlinear_arith)
            requires xi == ai * (xi / ai) + xi % ai, xi % ai == 0, q == xi / ai;
        // 1 == s*a + t*(a*q) == a*(s + t*q).
        assert(1 == ai * (s + t * q)) by(nonlinear_arith)
            requires s * ai + t * xi == 1, xi == ai * q;
        assert(false) by(nonlinear_arith)
            requires 1 == ai * (s + t * q), ai >= 2;
    }
}

} // verus!
