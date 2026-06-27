//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the prefix digit-walk-left + reverse algebra.
//!
//! Model B's per-block iteration surges the head right over the output to the frontier (pushing the output
//! from `v` onto `u` via [`crate::tm_dwalk::lemma_dwalk_right`]), emits a block there, then returns home by
//! walking LEFT back over `output ++ blk`. The return walk must **leave the masters `U` (the
//! temp/master counters) intact** — exactly the situation [`crate::tm_dec_master::lemma_walk_left_prefix`]
//! handles for the unary counter, but here over a block of arbitrary digit-symbols `1..4`. This file is
//! that gadget: [`lemma_dwalk_left_prefix`], the digit analog of `lemma_walk_left_prefix`.
//!
//! A left-walk peels `u` low-first and piles onto `v`, so the digit ORDER reverses; the home output value
//! comes out `dpack`-clean only after the second (return) walk cancels the first (surge) walk's reversal.
//! Rather than reason about that cancellation inline, this module names the reversal: a recursive digit
//! reverse [`drev`] (low-first-defined, so it folds through `dpile`/`dpack` inductively) with the bridges
//! [`lemma_dpile_zero_drev`] (`dpile(0,s) == dpack(drev(s))`), [`lemma_dpile_is_dpack_drev`] (the `v ≠ 0`
//! split), and [`lemma_drev_involution`]. The composite per-block iteration ([`crate::tm_block_iter`])
//! uses these to discharge `dpile(0, drev(combined)) == dpack(combined)` — the "there-and-back is identity"
//! fact — once, cleanly.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{dpack, dpile, pow_nat, lemma_pow_nat_unfold, lemma_dpack_pop, lemma_dpack_append};

verus! {

// ============================================================================
// drev — the low-first recursive digit reverse + its structural laws
// ============================================================================

/// `dpack([d], m) == d` — a one-digit string packs to its digit.
pub proof fn lemma_dpack_singleton(d: nat, m: nat)
    ensures
        dpack(seq![d], m) == d,
{
    assert(seq![d].len() == 1);
    assert(seq![d][0] == d);
    assert(seq![d].drop_first() =~= Seq::<nat>::empty());
    assert(dpack(seq![d].drop_first(), m) == 0);
    // dpack([d]) == [d][0] + m·dpack([d].drop_first()) == d + m·0 == d.
    assert(dpack(seq![d], m) == d + m * dpack(seq![d].drop_first(), m));
    assert(m * 0 == 0) by(nonlinear_arith);
}

/// `drev(s)` reverses the digit sequence `s`, defined low-first (peel `s[0]`, reverse the rest, append
/// `s[0]` at the high end) so it folds through `dpile`/`dpack`'s own `drop_first` recursion. The internal
/// bookkeeping device for "a left-walk peels `u` low-first then re-piles onto `v`, reversing the order".
pub open spec fn drev(s: Seq<nat>) -> Seq<nat>
    decreases s.len()
{
    if s.len() == 0 { Seq::<nat>::empty() } else { drev(s.drop_first()) + seq![s[0]] }
}

/// `drev` preserves length.
pub proof fn lemma_drev_len(s: Seq<nat>)
    ensures
        drev(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        lemma_drev_len(s.drop_first());
    }
}

/// `drev([x]) =~= [x]` — the singleton fixes.
pub proof fn lemma_drev_singleton(x: nat)
    ensures
        drev(seq![x]) =~= seq![x],
{
    let sx = seq![x];
    assert(sx.len() == 1);
    assert(sx[0] == x);
    assert(sx.drop_first() =~= Seq::<nat>::empty());
    // drev(sx) == drev(sx.drop_first()) + seq![sx[0]] == empty + [x] == [x].
    assert(drev(sx) =~= drev(sx.drop_first()) + seq![sx[0]]);
    assert(drev(sx.drop_first()) =~= Seq::<nat>::empty());
    assert(Seq::<nat>::empty() + seq![x] =~= seq![x]);
}

/// **`drev` over concatenation (the reversal law).** `drev(a + b) =~= drev(b) + drev(a)`. Induction on
/// `a` (peeling its low digit, which is also `(a+b)`'s low digit).
pub proof fn lemma_drev_concat(a: Seq<nat>, b: Seq<nat>)
    ensures
        drev(a + b) =~= drev(b) + drev(a),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(drev(a) =~= Seq::<nat>::empty());
        assert(drev(b) + drev(a) =~= drev(b));
    } else {
        assert((a + b).len() > 0);
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        // drev(a+b) == drev(a.drop_first()+b) + [a[0]]
        lemma_drev_concat(a.drop_first(), b);   // IH: drev(a.df+b) == drev(b)+drev(a.df)
        // drev(a) == drev(a.drop_first()) + [a[0]]
        assert(drev(a + b) =~= (drev(b) + drev(a.drop_first())) + seq![a[0]]);
        assert((drev(b) + drev(a.drop_first())) + seq![a[0]]
            =~= drev(b) + (drev(a.drop_first()) + seq![a[0]]));
        assert(drev(a.drop_first()) + seq![a[0]] =~= drev(a));
    }
}

/// **`drev` is an involution.** `drev(drev(s)) =~= s`. Induction on `s` via [`lemma_drev_concat`].
pub proof fn lemma_drev_involution(s: Seq<nat>)
    ensures
        drev(drev(s)) =~= s,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(drev(s) =~= Seq::<nat>::empty());
    } else {
        let rest = s.drop_first();
        // drev(s) == drev(rest) + [s[0]]
        lemma_drev_concat(drev(rest), seq![s[0]]);   // drev(drev(rest)+[s0]) == drev([s0])+drev(drev(rest))
        lemma_drev_singleton(s[0]);                  // drev([s0]) == [s0]
        lemma_drev_involution(rest);                 // drev(drev(rest)) == rest
        assert(drev(drev(s)) =~= seq![s[0]] + rest);
        assert(seq![s[0]] + rest =~= s);
    }
}

/// **`drev` preserves the digit bound.** If every digit of `s` is in `1..=n`, so is every digit of
/// `drev(s)`. Induction on `s`.
pub proof fn lemma_drev_digit_bound(s: Seq<nat>, n: nat)
    requires
        forall|k: int| 0 <= k < s.len() ==> 1 <= #[trigger] s[k] <= n,
    ensures
        forall|k: int| 0 <= k < drev(s).len() ==> 1 <= #[trigger] drev(s)[k] <= n,
    decreases s.len(),
{
    lemma_drev_len(s);
    if s.len() == 0 {
    } else {
        let rest = s.drop_first();
        assert forall|k: int| 0 <= k < rest.len() implies 1 <= #[trigger] rest[k] <= n by {
            assert(rest[k] == s[k + 1]);
        }
        lemma_drev_digit_bound(rest, n);
        lemma_drev_len(rest);
        let dr = drev(rest);
        // drev(s) == dr + [s[0]]; index k < dr.len() is dr[k] (bounded by IH); k == dr.len() is s[0].
        assert forall|k: int| 0 <= k < drev(s).len() implies 1 <= #[trigger] drev(s)[k] <= n by {
            assert(drev(s) =~= dr + seq![s[0]]);
            if k < dr.len() {
                assert(drev(s)[k] == dr[k]);
            } else {
                assert(drev(s)[k] == s[0]);
            }
        }
    }
}

// ============================================================================
// dpile / dpack / drev bridges
// ============================================================================

/// **`dpile` split off the base.** `dpile(v, s, m) == v·m^{|s|} + dpile(0, s, m)` — the starting stack `v`
/// only contributes its shifted value; the block's own contribution is `dpile(0, s)`. Induction on `s`.
pub proof fn lemma_dpile_split(v: nat, s: Seq<nat>, m: nat)
    ensures
        dpile(v, s, m) == v * pow_nat(m, s.len()) + dpile(0, s, m),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(pow_nat(m, 0) == 1);
        assert(v * 1 == v) by(nonlinear_arith);
    } else {
        let rest = s.drop_first();
        // dpile(v, s) == dpile(v·m + s[0], rest); dpile(0, s) == dpile(s[0], rest).
        assert(0nat * m + s[0] == s[0]) by(nonlinear_arith);
        lemma_dpile_split(v * m + s[0], rest, m);   // == (v·m+s[0])·m^{|rest|} + dpile(0,rest)
        lemma_dpile_split(s[0], rest, m);           // dpile(s[0],rest) == s[0]·m^{|rest|} + dpile(0,rest)
        lemma_pow_nat_unfold(m, s.len());           // m^{|s|} == m·m^{|rest|}
        assert(s.len() - 1 == rest.len());
        // (v·m+s[0])·m^{|rest|} == v·m·m^{|rest|} + s[0]·m^{|rest|} == v·m^{|s|} + s[0]·m^{|rest|}.
        assert((v * m + s[0]) * pow_nat(m, rest.len())
            == v * (m * pow_nat(m, rest.len())) + s[0] * pow_nat(m, rest.len())) by(nonlinear_arith);
    }
}

/// **`dpile` over concatenation.** `dpile(v, a + b, m) == dpile(dpile(v, a, m), b, m)` — piling `a` then
/// `b` is piling `a ++ b`. The tool for folding the emit (`dpile(dpile(U·m, od), blk)`) into a single
/// `dpile(U·m, od ++ blk)`. Induction on `a` (drop_first).
pub proof fn lemma_dpile_concat(v: nat, a: Seq<nat>, b: Seq<nat>, m: nat)
    ensures
        dpile(v, a + b, m) == dpile(dpile(v, a, m), b, m),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(dpile(v, a, m) == v);
    } else {
        // (a+b)[0] == a[0]; (a+b).drop_first() == a.drop_first() + b.
        assert((a + b).len() > 0);
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        // dpile(v, a+b) == dpile(v·m + a[0], a.drop_first() + b).
        assert(dpile(v, a + b, m) == dpile(v * m + a[0], a.drop_first() + b, m));
        lemma_dpile_concat(v * m + a[0], a.drop_first(), b, m);
        // == dpile(dpile(v·m+a[0], a.drop_first()), b) == dpile(dpile(v, a), b).
        assert(dpile(v, a, m) == dpile(v * m + a[0], a.drop_first(), m));
    }
}

/// **The reversal bridge.** `dpile(0, s, m) == dpack(drev(s), m)` — piling `s` low-first onto an empty
/// stack yields the `dpack` of `s` reversed. Induction on `s`: peel `s[0]` (the deepest pile push = the
/// HIGH `drev` digit), [`lemma_dpile_split`] off it, [`lemma_dpack_append`] the matching high block.
pub proof fn lemma_dpile_zero_drev(s: Seq<nat>, m: nat)
    ensures
        dpile(0, s, m) == dpack(drev(s), m),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(drev(s) =~= Seq::<nat>::empty());
        assert(dpack(Seq::<nat>::empty(), m) == 0);
    } else {
        let rest = s.drop_first();
        // dpile(0, s) == dpile(s[0], rest) == s[0]·m^{|rest|} + dpile(0, rest) == s[0]·m^{|rest|} + dpack(drev(rest)).
        assert(0nat * m + s[0] == s[0]) by(nonlinear_arith);
        lemma_dpile_split(s[0], rest, m);
        lemma_dpile_zero_drev(rest, m);   // dpile(0, rest) == dpack(drev(rest))
        // dpack(drev(s)) == dpack(drev(rest) + [s[0]]) == dpack(drev(rest)) + m^{|drev(rest)|}·dpack([s[0]]).
        assert(drev(s) =~= drev(rest) + seq![s[0]]);
        lemma_dpack_append(drev(rest), seq![s[0]], m);
        lemma_drev_len(rest);   // |drev(rest)| == |rest|
        lemma_dpack_singleton(s[0], m);   // dpack([s[0]]) == s[0]
        assert(s[0] * pow_nat(m, rest.len()) == pow_nat(m, rest.len()) * s[0]) by(nonlinear_arith);
    }
}

/// **The `v ≠ 0` reversal bridge.** `dpile(v, s, m) == v·m^{|s|} + dpack(drev(s), m)` — combines
/// [`lemma_dpile_split`] with [`lemma_dpile_zero_drev`]. The form the per-block return walk reads the
/// post-surge `u == dpile(U·m, output ++ blk)` through.
pub proof fn lemma_dpile_is_dpack_drev(v: nat, s: Seq<nat>, m: nat)
    ensures
        dpile(v, s, m) == v * pow_nat(m, s.len()) + dpack(drev(s), m),
{
    lemma_dpile_split(v, s, m);
    lemma_dpile_zero_drev(s, m);
}

// ============================================================================
// the prefix digit-walk-left
// ============================================================================

/// **The prefix digit-walk-left.** From a config in state `q_walk` scanning the low digit `blk[0]` of a
/// block `blk` of nonzero digit-symbols (`1 ≤ blk[k] ≤ 4`), with the rest of the block AND a high tail `w`
/// in `u` (`u == dpack(blk.drop_first()) + m^{|blk|-1}·w`, `w % m == 0`), the four loop quintuples
/// `(q_walk, s, s, q_walk, L)` (`s ∈ 1..4`) fire `blk.len()` times — peeling each digit onto `v` — and land
/// the head on `w`'s low cell (`u == w/m`, `a == w%m == 0`), still in `q_walk`. The digit analog of
/// [`crate::tm_dec_master::lemma_walk_left_prefix`]: it LEAVES the high tail `w` (the masters) intact, unlike
/// [`crate::tm_dwalk::lemma_dwalk_left`] (which assumes the rest of `u` is blank and lands `u == 0`). The
/// result stack is `dpile(c.v, blk)` (the block reversed onto `v`). Induction on `blk`.
pub proof fn lemma_dwalk_left_prefix(
    tm: Tm, c: TmConfig, q_walk: nat, blk: Seq<nat>, w: nat,
    i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        w % tm.m == 0,
        c.a == blk[0],
        c.u == dpack(blk.drop_first(), tm.m) + pow_nat(tm.m, (blk.len() - 1) as nat) * w,
        c.q == q_walk,
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[i3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[i4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
    ensures
        tm_run(tm, c, blk.len())
            == (TmConfig { u: w / tm.m, v: dpile(c.v, blk, tm.m), a: w % tm.m, q: q_walk }),
    decreases blk.len(),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);   // tm_wf ⟹ 0 < n < m, n ≥ 4 ⟹ m ≥ 5
    let s = blk[0];
    assert(1 <= s <= 4);
    // pick the firing quintuple by the scanned digit s.
    let i_s = if s == 1 { i1 } else if s == 2 { i2 } else if s == 3 { i3 } else { i4 };
    assert(tm.quints[i_s] == mk_quint(q_walk, s, s, q_walk, Dir::L));
    assert(quint_matches(tm.quints[i_s], c));
    lemma_tm_step_picks(tm, c, i_s);
    let c_next = apply_quint(tm.quints[i_s], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // L-move with a2 == s: (c.u/m, c.v*m+s, c.u%m, q_walk).
    assert(c_next.u == c.u / m);
    assert(c_next.v == c.v * m + s);
    assert(c_next.a == c.u % m);
    assert(c_next.q == q_walk);
    let rest = blk.drop_first();
    // dpile(c.v, blk) unfolds (blk nonempty) to dpile(c.v*m+s, rest).
    assert(dpile(c.v, blk, m) == dpile(c.v * m + s, rest, m));

    if rest.len() == 0 {
        // blk == [s]; dpack(rest) == 0, |blk|-1 == 0, so c.u == 0 + 1·w == w.
        assert(rest =~= Seq::<nat>::empty());
        assert(dpack(rest, m) == 0);
        assert(pow_nat(m, 0) == 1);
        assert(1nat * w == w) by(nonlinear_arith);
        assert(c.u == w);
        assert(dpile(c.v * m + s, rest, m) == c.v * m + s);   // dpile(_, empty) == _
        assert(c_next == (TmConfig { u: w / m, v: dpile(c.v, blk, m), a: w % m, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(blk.len() == 1);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // rest nonempty; rest[0] == blk[1] ∈ 1..4 < m.
        assert(rest[0] == blk[1]);
        assert(1 <= rest[0] <= 4);
        // c.u == dpack(rest) + m^{|rest|}·w == (dpack(rest.drop_first()) + m^{|rest|-1}·w)·m + rest[0].
        assert((blk.len() - 1) as nat == rest.len());
        let x = dpack(rest.drop_first(), m) + pow_nat(m, (rest.len() - 1) as nat) * w;
        assert(dpack(rest, m) == rest[0] + m * dpack(rest.drop_first(), m));   // dpack unfold
        lemma_pow_nat_unfold(m, rest.len());   // m^{|rest|} == m·m^{|rest|-1}
        assert(c.u == x * m + rest[0]) by(nonlinear_arith)
            requires
                c.u == dpack(rest, m) + pow_nat(m, rest.len()) * w,
                dpack(rest, m) == rest[0] + m * dpack(rest.drop_first(), m),
                pow_nat(m, rest.len()) == m * pow_nat(m, (rest.len() - 1) as nat),
                x == dpack(rest.drop_first(), m) + pow_nat(m, (rest.len() - 1) as nat) * w;
        lemma_div_mod_step(x, m, rest[0]);   // (x·m + rest[0])/m == x, %m == rest[0]  (rest[0] < m)
        assert(c_next.u == x);
        assert(c_next.a == rest[0]);
        // rest inherits the digit bound.
        assert forall|k: int| 0 <= k < rest.len() implies 1 <= #[trigger] rest[k] <= 4 by {
            assert(rest[k] == blk[k + 1]);
        }
        lemma_dwalk_left_prefix(tm, c_next, q_walk, rest, w, i1, i2, i3, i4);
        // IH: tm_run(c_next, rest.len()) == (w/m, dpile(c_next.v, rest), w%m, q_walk),
        //     and dpile(c.v*m+s, rest) == dpile(c.v, blk).
        assert(tm_run(tm, c, blk.len()) == tm_run(tm, c_next, rest.len()));
    }
}

} // verus!
