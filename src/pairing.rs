use vstd::prelude::*;

verus! {

///  Triangular number: T(n) = n * (n + 1) / 2.
pub open spec fn triangular(n: nat) -> nat {
    (n * (n + 1)) / 2
}

///  Cantor pairing function: pair(a, b) = T(a + b) + a.
pub open spec fn pair(a: nat, b: nat) -> nat {
    triangular(a + b) + a
}

///  Helper: triangular numbers are strictly monotone.
proof fn lemma_triangular_strict_mono(n: nat, m: nat)
    requires
        n < m,
    ensures
        triangular(n) < triangular(m),
    decreases m - n,
{
    if m == n + 1 {
        //  T(n+1) = (n+1)(n+2)/2 = T(n) + n + 1
        assert(triangular(n + 1) == ((n + 1) * (n + 2)) / 2);
        assert(triangular(n) == (n * (n + 1)) / 2);
        //  (n+1)(n+2) = n(n+1) + 2(n+1)
        assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
        assert(((n + 1) * (n + 2)) / 2 == (n * (n + 1)) / 2 + (n + 1)) by(nonlinear_arith);
    } else {
        lemma_triangular_strict_mono(n, (m - 1) as nat);
        lemma_triangular_strict_mono((m - 1) as nat, m);
    }
}

///  Helper: triangular(n) >= n for all n.
proof fn lemma_triangular_ge(n: nat)
    ensures
        triangular(n) >= n,
{
    assert(n * (n + 1) >= 2 * n) by(nonlinear_arith);
    assert(n * (n + 1) / 2 >= n) by(nonlinear_arith);
}

///  Pair is at least as large as each component.
pub proof fn lemma_pair_gt_components(a: nat, b: nat)
    ensures
        pair(a, b) >= a,
        pair(a, b) >= b,
{
    lemma_triangular_ge(a + b);
    //  pair(a, b) = T(a+b) + a >= a+b + a >= a and >= b
    assert(pair(a, b) == triangular(a + b) + a);
    assert(triangular(a + b) >= a + b);
}

///  pair(a, b) >= a + b.
pub proof fn lemma_pair_ge_sum(a: nat, b: nat)
    ensures
        pair(a, b) >= a + b,
{
    lemma_triangular_ge(a + b);
    assert(pair(a, b) == triangular(a + b) + a);
    assert(triangular(a + b) >= a + b);
}

///  If a >= 1, then pair(a, b) > b.
pub proof fn lemma_pair_pos_tag_gt_content(a: nat, b: nat)
    requires
        a >= 1,
    ensures
        pair(a, b) > b,
{
    lemma_triangular_ge(a + b);
    assert(triangular(a + b) >= a + b);
    assert(pair(a, b) == triangular(a + b) + a);
    assert(pair(a, b) >= a + b + a);
    assert(pair(a, b) >= b + 2 * a);
}

///  Cantor pairing is injective: pair(a1,b1) == pair(a2,b2) implies a1==a2 && b1==b2.
pub proof fn lemma_pair_injective(a1: nat, b1: nat, a2: nat, b2: nat)
    requires
        pair(a1, b1) == pair(a2, b2),
    ensures
        a1 == a2 && b1 == b2,
{
    let s1 = a1 + b1;
    let s2 = a2 + b2;

    //  First show s1 == s2. If s1 != s2, then T(s1) and T(s2) are far apart.
    if s1 < s2 {
        lemma_triangular_strict_mono(s1, s2);
        //  T(s2) > T(s1), and T(s2) + a2 = T(s1) + a1
        //  So T(s1) + a1 >= T(s2) + a2 > T(s1) + a2
        //  But also a1 <= s1 < s2, so T(s2) >= T(s1) + s1 + 1
        lemma_triangular_step(s1);
        //  T(s1+1) = T(s1) + s1 + 1, and T(s2) >= T(s1+1) >= T(s1) + s1 + 1
        //  pair(a2,b2) = T(s2) + a2 >= T(s1) + s1 + 1 + a2 >= T(s1) + s1 + 1
        //  pair(a1,b1) = T(s1) + a1 <= T(s1) + s1
        //  Contradiction
        assert(pair(a1, b1) <= triangular(s1) + s1);
        assert(pair(a2, b2) >= triangular(s2));
        if s2 > s1 + 1 {
            lemma_triangular_strict_mono(s1 + 1, s2);
        }
        assert(triangular(s2) >= triangular(s1) + s1 + 1);
        assert(false);
    } else if s2 < s1 {
        lemma_triangular_strict_mono(s2, s1);
        lemma_triangular_step(s2);
        assert(pair(a2, b2) <= triangular(s2) + s2);
        assert(pair(a1, b1) >= triangular(s1));
        if s1 > s2 + 1 {
            lemma_triangular_strict_mono(s2 + 1, s1);
        }
        assert(triangular(s1) >= triangular(s2) + s2 + 1);
        assert(false);
    }
    //  s1 == s2, so T(s1) == T(s2), so a1 == a2
    assert(s1 == s2);
    assert(triangular(s1) == triangular(s2));
    assert(a1 == a2);
    //  From a1 + b1 == a2 + b2 and a1 == a2, b1 == b2
    assert(b1 == b2);
}

///  The "anti-diagonal" of a paired value: the unique k with T(k) <= p < T(k+1).
pub open spec fn unpair_sum(p: nat) -> nat {
    choose|k: nat| #[trigger] triangular(k) <= p && p < triangular(k + 1)
}

///  First component of Cantor unpairing.
pub open spec fn unpair1(p: nat) -> nat {
    (p - triangular(unpair_sum(p))) as nat
}

///  Second component of Cantor unpairing.
pub open spec fn unpair2(p: nat) -> nat {
    (unpair_sum(p) - unpair1(p)) as nat
}

///  Helper: T(n+1) = T(n) + n + 1.
proof fn lemma_triangular_step(n: nat)
    ensures
        triangular(n + 1) == triangular(n) + n + 1,
{
    assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
    assert(((n + 1) * (n + 2)) / 2 == (n * (n + 1)) / 2 + (n + 1)) by(nonlinear_arith);
}

///  Every nat has a unique anti-diagonal.
pub proof fn lemma_unpair_sum_exists(p: nat)
    ensures
        triangular(unpair_sum(p)) <= p && p < triangular(unpair_sum(p) + 1),
{
    //  Show the witness exists: find k such that T(k) <= p < T(k+1)
    //  By induction / well-ordering, such k exists for every p.
    //  T(0) = 0 <= p. Find largest k with T(k) <= p.
    let k = unpair_sum(p);
    //  unpair_sum is defined as choose, so we need to show the predicate is satisfiable.
    //  We prove: for all p, exists k such that T(k) <= p < T(k+1).
    //  This follows because T(0) = 0 <= p, and T(n) → ∞, so there's a largest k with T(k) <= p.
    assert(triangular(0) == 0);
    //  By well-ordering, there exists k with T(k) <= p < T(k+1).
    //  Actually, unpair_sum(p) IS the chosen k, so its properties hold by definition.
    //  But we need to show the choice is valid (the predicate is satisfiable).
    //  Let's prove it by finding a concrete witness.
    lemma_unpair_sum_exists_helper(p, p);
}

proof fn lemma_unpair_sum_exists_helper(p: nat, fuel: nat)
    ensures
        exists|k: nat| triangular(k) <= p && p < triangular(k + 1),
    decreases fuel,
{
    assert(triangular(0) == 0);
    if p < triangular(1) {
        assert(triangular(0) <= p && p < triangular(1));
    } else if fuel == 0 {
        //  Won't happen for valid p, but needed for termination
        assert(triangular(0) <= p);
        lemma_triangular_step(0);
        assert(triangular(1) == 1);
        //  p >= 1, need to find k >= 1
        assert(false); //  unreachable for fuel >= p
    } else {
        //  T(fuel+1) > fuel >= p for large enough fuel
        //  Find k by searching
        if triangular(fuel + 1) <= p {
            //  fuel+1 is too small, but p <= fuel, contradiction
            lemma_triangular_ge(fuel + 1);
            assert(triangular(fuel + 1) >= fuel + 1);
            assert(false); //  fuel + 1 > fuel >= p, but T(fuel+1) <= p, contradiction
        } else {
            //  T(fuel+1) > p. Check if T(fuel) <= p.
            if triangular(fuel) <= p {
                assert(triangular(fuel) <= p && p < triangular(fuel + 1));
            } else {
                //  T(fuel) > p, try smaller
                lemma_unpair_sum_exists_helper(p, (fuel - 1) as nat);
            }
        }
    }
}

///  Round-trip: unpair1(pair(a, b)) == a.
pub proof fn lemma_unpair1_pair(a: nat, b: nat)
    ensures
        unpair1(pair(a, b)) == a,
{
    let p = pair(a, b);
    let s = a + b;
    //  pair(a, b) = T(s) + a
    //  Need: unpair_sum(p) == s, then unpair1(p) = p - T(s) = a
    lemma_unpair_sum_exists(p);
    let k = unpair_sum(p);
    //  k satisfies T(k) <= p < T(k+1)
    //  Also s satisfies T(s) <= p < T(s+1):
    //    T(s) <= T(s) + a = p
    //    p = T(s) + a, and a <= s, so p < T(s) + s + 1 = T(s+1)
    lemma_triangular_step(s);
    assert(triangular(s) <= p);
    assert(p < triangular(s + 1));
    //  By uniqueness (T is strictly monotone), k == s
    if k < s {
        lemma_triangular_strict_mono(k + 1, s + 1);
        assert(triangular(k + 1) <= triangular(s) <= p);
        assert(false); //  contradicts p < T(k+1)
    } else if k > s {
        lemma_triangular_strict_mono(s + 1, k + 1);
        assert(triangular(s + 1) <= triangular(k) <= p);
        assert(false); //  contradicts p < T(s+1)
    }
    assert(k == s);
    //  unpair1(p) = p - T(k) = T(s) + a - T(s) = a
}

///  Round-trip: unpair2(pair(a, b)) == b.
pub proof fn lemma_unpair2_pair(a: nat, b: nat)
    ensures
        unpair2(pair(a, b)) == b,
{
    lemma_unpair1_pair(a, b);
    //  unpair2(p) = unpair_sum(p) - unpair1(p) = (a+b) - a = b
    //  Need unpair_sum(pair(a,b)) == a + b (shown in the proof above)
    let p = pair(a, b);
    let s = a + b;
    lemma_unpair_sum_exists(p);
    let k = unpair_sum(p);
    lemma_triangular_step(s);
    if k < s {
        lemma_triangular_strict_mono(k + 1, s + 1);
        assert(false);
    } else if k > s {
        lemma_triangular_strict_mono(s + 1, k + 1);
        assert(false);
    }
    assert(k == s);
    assert(unpair1(p) == a);
    //  unpair2(p) = k - unpair1(p) = s - a = b
}

//  ============================================================
//  Surjectivity and bounds for unpairing
//  ============================================================

///  unpair1 + unpair2 equals the anti-diagonal.
pub proof fn lemma_unpair_sum(p: nat)
    ensures unpair1(p) + unpair2(p) == unpair_sum(p),
{
    lemma_unpair_sum_exists(p);
    let k = unpair_sum(p);
    //  unpair1(p) = p - T(k), unpair2(p) = k - unpair1(p)
    //  sum = (p - T(k)) + (k - (p - T(k))) = k
}

///  Full roundtrip: pair(unpair1(p), unpair2(p)) == p.
pub proof fn lemma_pair_surjective(p: nat)
    ensures pair(unpair1(p), unpair2(p)) == p,
{
    lemma_unpair_sum_exists(p);
    lemma_unpair_sum(p);
    let k = unpair_sum(p);
    let a = unpair1(p);
    //  a + unpair2(p) == k, so pair(a, unpair2(p)) = T(k) + a = T(k) + (p - T(k)) = p
    assert(pair(a, unpair2(p)) == triangular(a + unpair2(p)) + a);
    assert(a + unpair2(p) == k);
    assert(triangular(k) + a == triangular(k) + (p - triangular(k)));
}

///  unpair1(p) <= p.
pub proof fn lemma_unpair1_le(p: nat)
    ensures unpair1(p) <= p,
{
    lemma_unpair_sum_exists(p);
    //  unpair1(p) = p - T(k) where T(k) <= p, so unpair1(p) <= p
}

///  unpair2(p) <= p.
pub proof fn lemma_unpair2_le(p: nat)
    ensures unpair2(p) <= p,
{
    lemma_unpair_sum_exists(p);
    lemma_unpair_sum(p);
    let k = unpair_sum(p);
    //  unpair2(p) = k - unpair1(p) <= k
    //  T(k) <= p and T(k) >= k (by lemma_triangular_ge), so k <= p
    lemma_triangular_ge(k);
}

///  When unpair1(p) >= 1, unpair2(p) < p.
pub proof fn lemma_unpair2_lt(p: nat)
    requires unpair1(p) >= 1,
    ensures unpair2(p) < p,
{
    lemma_pair_surjective(p);
    lemma_pair_pos_tag_gt_content(unpair1(p), unpair2(p));
    //  pair(unpair1(p), unpair2(p)) > unpair2(p)
    //  pair(unpair1(p), unpair2(p)) == p
    //  Therefore p > unpair2(p)
}

///  When unpair1(p) >= 1, both components of unpair2(p) are < p.
pub proof fn lemma_unpair_content_lt(p: nat)
    requires unpair1(p) >= 1,
    ensures
        unpair2(p) < p,
        unpair1(unpair2(p)) <= unpair2(p),
        unpair2(unpair2(p)) <= unpair2(p),
{
    lemma_unpair2_lt(p);
    lemma_unpair1_le(unpair2(p));
    lemma_unpair2_le(unpair2(p));
}

} //  verus!
