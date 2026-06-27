//! # GAP-2 G2-F Route (i) brick R-cmp (B-cmp.1, part 1) — the generalized digit-walks over `block ++ W`.
//!
//! The M1 compare (see `docs/gap2-input-loader-plan.md` §N+20) reads the parked `alpha` non-destructively
//! by a BALANCED there-and-back traverse over the already-compared α digits: `dwalk_right` peels them onto
//! `u` to reach the `5`-frontier-mark, then `dwalk_left` peels them back onto `v` (net change to `v` is
//! zero — the "probe" pattern). The existing [`crate::tm_dwalk::lemma_dwalk_right`] only handles a block
//! followed by a BLANK (`v` empties to `0`), but in the probe the block is followed by the `5`-mark and
//! the rest of α. This file generalizes the walk to a block followed by an **arbitrary tail value** `W`:
//! after peeling `blk`, the head lands scanning `W % m` with the tail `W / m` intact on the far stack.
//! Setting `W = 0` recovers `lemma_dwalk_right`/`left` exactly; setting `W % m == 5` is the probe's stop.
//!
//! Key structural fact: the tail `W` is **loop-invariant** — the recursion peels `blk` and always lands
//! scanning `W % m`, so the landing config is independent of `blk.len()`.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{dpack, dpile, pow_nat, lemma_pow_nat_unfold};
use crate::tm_dwalk_prefix::{drev, lemma_drev_len, lemma_drev_digit_bound, lemma_drev_involution,
    lemma_dpile_is_dpack_drev, lemma_drev_concat, lemma_drev_singleton, lemma_dpack_singleton};
use crate::tm_dstring::lemma_dpack_append;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_skip_blank::{pile_zeros, lemma_skip0_left, lemma_skip0_right, lemma_pile_zeros_shift};

verus! {

/// **The generalized digit-walk-right.** From state `q_back` scanning the low digit `blk[0]` of a block
/// `blk` of nonzero digit-symbols (`1..4`), with the rest of the block followed by an arbitrary tail
/// value `W` in `v` (`v == dpack(blk.drop_first()) + m^{blk.len()-1}·W`), the four loop quintuples
/// `(q_back, s, s, q_back, R)` fire `blk.len()` times — peeling each digit onto `u` — and land the head
/// scanning `W % m` with `v == W / m`, `u == dpile(c.u, blk)`, still in `q_back`. (`W = 0` is exactly
/// [`crate::tm_dwalk::lemma_dwalk_right`].) Induction on `blk`.
pub proof fn lemma_dwalk_right_gen(
    tm: Tm, c: TmConfig, q_back: nat, blk: Seq<nat>, w: nat,
    i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        c.a == blk[0],
        c.v == dpack(blk.drop_first(), tm.m) + pow_nat(tm.m, (blk.len() - 1) as nat) * w,
        c.q == q_back,
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
    ensures
        tm_run(tm, c, blk.len())
            == (TmConfig { u: dpile(c.u, blk, tm.m), v: w / tm.m, a: w % tm.m, q: q_back }),
    decreases blk.len(),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let s = blk[0];
    assert(1 <= s <= 4);
    let i_s = if s == 1 { i1 } else if s == 2 { i2 } else if s == 3 { i3 } else { i4 };
    assert(tm.quints[i_s] == mk_quint(q_back, s, s, q_back, Dir::R));
    assert(quint_matches(tm.quints[i_s], c));
    lemma_tm_step_picks(tm, c, i_s);
    let c_next = apply_quint(tm.quints[i_s], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // R-move with a2 == s: (c.u*m+s, c.v/m, c.v%m, q_back).
    assert(c_next.u == c.u * m + s);
    assert(c_next.v == c.v / m);
    assert(c_next.a == c.v % m);
    assert(c_next.q == q_back);
    let r = blk.drop_first();
    assert(dpile(c.u, blk, m) == dpile(c.u * m + s, r, m));   // dpile unfold (blk nonempty)

    if r.len() == 0 {
        // blk == [s]; c.v == dpack(empty) + m^0·w == 0 + 1·w == w.
        assert(dpack(r, m) == 0);
        assert(pow_nat(m, 0) == 1);
        assert(c.v == w) by(nonlinear_arith)
            requires c.v == dpack(r, m) + pow_nat(m, (blk.len() - 1) as nat) * w,
                     dpack(r, m) == 0, pow_nat(m, (blk.len() - 1) as nat) == 1;
        assert(c_next.v == w / m);
        assert(c_next.a == w % m);
        assert(c_next == (TmConfig { u: dpile(c.u, blk, m), v: w / m, a: w % m, q: q_back }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(blk.len() == 1);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // c.v == r[0] + m·(dpack(r.drop_first()) + m^{r.len()-1}·w) == rv·m + r[0].
        let rr = r.drop_first();
        let rv = dpack(rr, m) + pow_nat(m, (r.len() - 1) as nat) * w;
        assert(r[0] == blk[1]);
        assert(1 <= r[0] <= 4);
        assert(dpack(r, m) == r[0] + m * dpack(rr, m));               // dpack unfold (r nonempty)
        lemma_pow_nat_unfold(m, (blk.len() - 1) as nat);              // m^{L-1} == m·m^{L-2}
        assert((blk.len() - 1) as nat == (r.len() - 1) as nat + 1);
        assert(pow_nat(m, (blk.len() - 1) as nat) == m * pow_nat(m, (r.len() - 1) as nat));
        assert(c.v == rv * m + r[0]) by(nonlinear_arith)
            requires
                c.v == dpack(r, m) + pow_nat(m, (blk.len() - 1) as nat) * w,
                dpack(r, m) == r[0] + m * dpack(rr, m),
                pow_nat(m, (blk.len() - 1) as nat) == m * pow_nat(m, (r.len() - 1) as nat),
                rv == dpack(rr, m) + pow_nat(m, (r.len() - 1) as nat) * w;
        lemma_div_mod_step(rv, m, r[0]);   // (rv·m + r[0])/m == rv, %m == r[0]   (r[0] < m)
        assert(c_next.v == rv);
        assert(c_next.a == r[0]);
        // recursive precondition: c_next.v == dpack(r.drop_first()) + m^{r.len()-1}·w == rv.
        assert forall|k: int| 0 <= k < r.len() implies 1 <= #[trigger] r[k] <= 4 by {
            assert(r[k] == blk[k + 1]);
        }
        lemma_dwalk_right_gen(tm, c_next, q_back, r, w, i1, i2, i3, i4);
        assert(tm_run(tm, c, blk.len()) == tm_run(tm, c_next, r.len()));
    }
}

/// **The generalized digit-walk-left** — the mirror of [`lemma_dwalk_right_gen`] (`u ↔ v`, `L ↔ R`). From
/// state `q_walk` scanning `blk[0]`, with the rest of the block followed by tail `W` in `u`
/// (`u == dpack(blk.drop_first()) + m^{blk.len()-1}·W`), the loop quintuples `(q_walk, s, s, q_walk, L)`
/// fire `blk.len()` times — peeling each digit onto `v` — and land the head scanning `W % m` with
/// `u == W / m`, `v == dpile(c.v, blk)`, still in `q_walk`. (`W = 0` is exactly
/// [`crate::tm_dwalk::lemma_dwalk_left`].)
pub proof fn lemma_dwalk_left_gen(
    tm: Tm, c: TmConfig, q_walk: nat, blk: Seq<nat>, w: nat,
    i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
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
    assert(m > 4);
    let s = blk[0];
    assert(1 <= s <= 4);
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
    let r = blk.drop_first();
    assert(dpile(c.v, blk, m) == dpile(c.v * m + s, r, m));

    if r.len() == 0 {
        assert(dpack(r, m) == 0);
        assert(pow_nat(m, 0) == 1);
        assert(c.u == w) by(nonlinear_arith)
            requires c.u == dpack(r, m) + pow_nat(m, (blk.len() - 1) as nat) * w,
                     dpack(r, m) == 0, pow_nat(m, (blk.len() - 1) as nat) == 1;
        assert(c_next.u == w / m);
        assert(c_next.a == w % m);
        assert(c_next == (TmConfig { u: w / m, v: dpile(c.v, blk, m), a: w % m, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(blk.len() == 1);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        let rr = r.drop_first();
        let rv = dpack(rr, m) + pow_nat(m, (r.len() - 1) as nat) * w;
        assert(r[0] == blk[1]);
        assert(1 <= r[0] <= 4);
        assert(dpack(r, m) == r[0] + m * dpack(rr, m));
        lemma_pow_nat_unfold(m, (blk.len() - 1) as nat);
        assert((blk.len() - 1) as nat == (r.len() - 1) as nat + 1);
        assert(pow_nat(m, (blk.len() - 1) as nat) == m * pow_nat(m, (r.len() - 1) as nat));
        assert(c.u == rv * m + r[0]) by(nonlinear_arith)
            requires
                c.u == dpack(r, m) + pow_nat(m, (blk.len() - 1) as nat) * w,
                dpack(r, m) == r[0] + m * dpack(rr, m),
                pow_nat(m, (blk.len() - 1) as nat) == m * pow_nat(m, (r.len() - 1) as nat),
                rv == dpack(rr, m) + pow_nat(m, (r.len() - 1) as nat) * w;
        lemma_div_mod_step(rv, m, r[0]);
        assert(c_next.u == rv);
        assert(c_next.a == r[0]);
        assert forall|k: int| 0 <= k < r.len() implies 1 <= #[trigger] r[k] <= 4 by {
            assert(r[k] == blk[k + 1]);
        }
        lemma_dwalk_left_gen(tm, c_next, q_walk, r, w, i1, i2, i3, i4);
        assert(tm_run(tm, c, blk.len()) == tm_run(tm, c_next, r.len()));
    }
}

/// **The balanced α-probe round-trip (B-cmp.1, the composition).** Composes the right-gen walk, the
/// turnaround at the `5`-mark, and the left-gen walk into a single net-identity-on-`v` move — the M1
/// compare's non-destructive read of the parked `alpha` (see `docs/gap2-input-loader-plan.md` §N+20, the
/// side-separation "probe" pattern).
///
/// Setup: head scanning the low α digit `blk[0]` (the already-compared prefix `blk`, each digit `1..4`),
/// with the rest of the block and the `5`-marked tail above (`v == dpack(blk.drop_first()) + m^{|blk|-1}·w`,
/// `w == m·whi + 5` so the tail's low cell is the marker `5` and `whi` is α's suffix above it), output
/// sitting in `u`, state `q_back`. The machine:
///   1. **walks right** over `blk` (peeling it onto `u`), landing scanning the `5` ([`lemma_dwalk_right_gen`]);
///   2. **turns around** with one L-move on the `5`-quintuple `(q_back, 5, 5, q_walk, L)` — rewriting the
///      mark (so α is value-preserved) and flipping to the leftward state, the free pop handing the head
///      the reversed block's low digit;
///   3. **walks left** over `drev(blk)` (peeling the block back onto `v`), landing one cell into `u`
///      scanning the output frontier `u % m` ([`lemma_dwalk_left_gen`]).
/// Net effect: `v` is restored to the full α stack `dpack(blk) + m^{|blk|}·w` (the scanned α digit folded
/// back in, the `5`-mark intact), the head has stepped one cell left into `u`, ready to read the output
/// frontier. Fuel `2·|blk| + 1`. Requires `n ≥ 5` (the mark `5` must be a real symbol). The probe changes
/// no tape content — it only repositions the head and re-frames the boundary.
pub proof fn lemma_cmp_balanced_roundtrip(
    tm: Tm, c: TmConfig, q_back: nat, q_walk: nat, blk: Seq<nat>, w: nat, whi: nat,
    i1: int, i2: int, i3: int, i4: int, j: int,
    l1: int, l2: int, l3: int, l4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        c.a == blk[0],
        w == tm.m * whi + 5,
        c.v == dpack(blk.drop_first(), tm.m) + pow_nat(tm.m, (blk.len() - 1) as nat) * w,
        c.q == q_back,
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        0 <= j < tm.quints.len(),
        0 <= l1 < tm.quints.len(),
        0 <= l2 < tm.quints.len(),
        0 <= l3 < tm.quints.len(),
        0 <= l4 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
        tm.quints[j]  == mk_quint(q_back, 5, 5, q_walk, Dir::L),
        tm.quints[l1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[l2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[l3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[l4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
    ensures
        tm_run(tm, c, (2 * blk.len() + 1) as nat)
            == (TmConfig {
                    u: c.u / tm.m,
                    v: dpack(blk, tm.m) + pow_nat(tm.m, blk.len()) * w,
                    a: c.u % tm.m,
                    q: q_walk,
               }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);   // tm_wf ⟹ 0 < n < m, n ≥ 5 ⟹ m ≥ 6
    let k = blk.len();
    // w decomposition: w / m == whi, w % m == 5 (5 < m).
    assert(m * whi == whi * m) by(nonlinear_arith);
    assert(w == whi * m + 5);
    lemma_div_mod_step(whi, m, 5);
    assert(w / m == whi);
    assert(w % m == 5);

    // ── Phase 1: walk right over blk, landing on the 5-mark.
    lemma_dwalk_right_gen(tm, c, q_back, blk, w, i1, i2, i3, i4);
    let c_right = TmConfig { u: dpile(c.u, blk, m), v: w / m, a: w % m, q: q_back };
    assert(tm_run(tm, c, k) == c_right);
    assert(c_right.a == 5);

    // ── Phase 2: turnaround. The 5-quintuple (q_back, 5, 5, q_walk, L) fires.
    assert(quint_matches(tm.quints[j], c_right));   // q == q_back, a == 5
    lemma_tm_step_picks(tm, c_right, j);
    let c_turn = apply_quint(tm.quints[j], c_right, m);
    assert(tm_step(tm, c_right) == Some(c_turn));
    // L-move with a2 == 5: u' = u/m, v' = v*m + 5, a' = u%m, q' = q_walk.
    assert(c_turn.v == c_right.v * m + 5);
    assert(c_turn.v == whi * m + 5);   // c_right.v == w/m == whi
    assert(c_turn.v == w);
    assert(c_turn.q == q_walk);

    // decompose dpile(c.u, blk) to read the turnaround's u-pop.
    let dr = drev(blk);
    lemma_drev_len(blk);              // |dr| == k
    lemma_drev_digit_bound(blk, 4);   // dr digits in 1..4
    lemma_dpile_is_dpack_drev(c.u, blk, m);   // dpile(c.u, blk) == c.u·m^k + dpack(dr)
    assert(dr.len() == k);
    assert(1 <= dr[0] <= 4);          // k ≥ 1 ⟹ dr nonempty
    assert(dr[0] < m);
    assert(dpack(dr, m) == dr[0] + m * dpack(dr.drop_first(), m));   // dpack unfold (dr nonempty)
    lemma_pow_nat_unfold(m, k);       // m^k == m·m^{k-1}
    let xx = dpack(dr.drop_first(), m) + pow_nat(m, (k - 1) as nat) * c.u;
    assert(dpile(c.u, blk, m) == xx * m + dr[0]) by(nonlinear_arith)
        requires
            dpile(c.u, blk, m) == c.u * pow_nat(m, k) + dpack(dr, m),
            dpack(dr, m) == dr[0] + m * dpack(dr.drop_first(), m),
            pow_nat(m, k) == m * pow_nat(m, (k - 1) as nat),
            xx == dpack(dr.drop_first(), m) + pow_nat(m, (k - 1) as nat) * c.u;
    lemma_div_mod_step(xx, m, dr[0]);   // (xx·m + dr[0])/m == xx, %m == dr[0]
    assert(c_turn.u == dpile(c.u, blk, m) / m);
    assert(c_turn.a == dpile(c.u, blk, m) % m);
    assert(c_turn.u == xx);
    assert(c_turn.a == dr[0]);

    // ── Phase 3: walk left over dr (= drev(blk)), tail c.u.
    assert((dr.len() - 1) as nat == (k - 1) as nat);
    lemma_dwalk_left_gen(tm, c_turn, q_walk, dr, c.u, l1, l2, l3, l4);
    let c_final = TmConfig { u: c.u / m, v: dpile(c_turn.v, dr, m), a: c.u % m, q: q_walk };
    assert(tm_run(tm, c_turn, k) == c_final);

    // final v == dpile(w, dr) == w·m^k + dpack(blk).
    lemma_dpile_is_dpack_drev(w, dr, m);   // dpile(w, dr) == w·m^{|dr|} + dpack(drev(dr))
    lemma_drev_involution(blk);            // drev(dr) =~= blk
    assert(drev(dr) =~= blk);
    assert(dpack(drev(dr), m) == dpack(blk, m));
    assert(dpile(c_turn.v, dr, m) == dpile(w, dr, m));   // c_turn.v == w
    assert(dpile(w, dr, m) == w * pow_nat(m, k) + dpack(blk, m));
    assert(w * pow_nat(m, k) == pow_nat(m, k) * w) by(nonlinear_arith);
    assert(c_final.v == dpack(blk, m) + pow_nat(m, k) * w);

    // ── Compose the three runs: 2k+1 = k + (1 + k).
    lemma_tm_run_split(tm, c, k, (k + 1) as nat);     // tm_run(c, 2k+1) == tm_run(c_right, k+1)
    lemma_tm_run_split(tm, c_right, 1, k);            // tm_run(c_right, k+1) == tm_run(tm_run(c_right,1), k)
    assert(tm_run(tm, c_turn, 0) == c_turn);
    assert(tm_run(tm, c_right, 1) == c_turn);         // single step
    assert((2 * k + 1) as nat == (k + (k + 1)) as nat);
    assert(tm_run(tm, c, (2 * k + 1) as nat) == c_final);
}

/// **The marker-advance round-trip (B-cmp.2, normal-advance case).** The probe of [`lemma_cmp_balanced_roundtrip`]
/// reads the α frontier *without moving the marker*; this one **advances** it one cell deeper (the M1
/// compare's "matched a digit, step to the next α position" — see §N+20/§N+21). The recorded frontier value
/// `vk` (∈1..4) is carried in the entry state `q_back` (the "value-in-state" mechanism forced by n=5); the
/// next α digit `s` (∈1..4 — this is the *normal* case, α not yet exhausted) is read into the exit state
/// `q_walk`.
///
/// Setup is the same invariant shape as the probe: head scanning the already-restored α prefix's low digit
/// `blk[0]` (prefix `blk`, `k` digits each `1..4`), tail `w == m·whi + 5` with `whi == m·suf + s` — so the
/// stack above the prefix is `[5-marker, s, suf…]`, `5` at position `k`, `s = α[k+1]` next, `suf` beyond.
/// The machine:
///   1. **walks right** over `blk` to the `5`-mark ([`lemma_dwalk_right_gen`], state `q_back` preserving `vk`);
///   2. **marker step** `(q_back, 5, vk, q_read, R)` — restore `vk` into the marked cell (α value-preserved),
///      move R onto `α[k+1] = s`;
///   3. **read+remark** `(q_read, s, 5, q_walk, L)` — write the new `5`-mark at position `k+1`, record
///      `s = V_{k+1}` in `q_walk`, move L back onto the just-restored `vk`;
///   4. **walks left** over `[vk] ++ drev(blk)` (the prefix grown by `vk`) back to the boundary
///      ([`lemma_dwalk_left_gen`]).
/// Net effect: `v` becomes `dpack(blk ++ [vk]) + m^{k+1}·(5 + m·suf)` — the **same invariant shape** with
/// prefix `blk ++ [vk]` (now `k+1` digits), marker advanced to position `k+1`, suffix `suf`; the head has
/// stepped one cell left into `u` scanning the output frontier `u % m`, now in state `q_walk` holding the
/// next frontier value `s`. Fuel `2·|blk| + 3`. Requires `n ≥ 5`. No tape content is destroyed (α grows
/// back into `v` intact, output `u` untouched). This is the inductive step the B-cmp.5 compare loop iterates.
pub proof fn lemma_cmp_marker_advance(
    tm: Tm, c: TmConfig, q_back: nat, q_read: nat, q_walk: nat,
    blk: Seq<nat>, w: nat, whi: nat, suf: nat, vk: nat, s: nat,
    i1: int, i2: int, i3: int, i4: int, j: int, jr: int,
    l1: int, l2: int, l3: int, l4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        1 <= vk <= 4,
        1 <= s <= 4,
        c.a == blk[0],
        w == tm.m * whi + 5,
        whi == tm.m * suf + s,
        c.v == dpack(blk.drop_first(), tm.m) + pow_nat(tm.m, (blk.len() - 1) as nat) * w,
        c.q == q_back,
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        0 <= j < tm.quints.len(),
        0 <= jr < tm.quints.len(),
        0 <= l1 < tm.quints.len(),
        0 <= l2 < tm.quints.len(),
        0 <= l3 < tm.quints.len(),
        0 <= l4 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
        tm.quints[j]  == mk_quint(q_back, 5, vk, q_read, Dir::R),
        tm.quints[jr] == mk_quint(q_read, s, 5, q_walk, Dir::L),
        tm.quints[l1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[l2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[l3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[l4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
    ensures
        tm_run(tm, c, (2 * blk.len() + 3) as nat)
            == (TmConfig {
                    u: c.u / tm.m,
                    v: dpack(blk + seq![vk], tm.m)
                        + pow_nat(tm.m, (blk.len() + 1) as nat) * (tm.m * suf + 5),
                    a: c.u % tm.m,
                    q: q_walk,
               }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let k = blk.len();
    // w/whi decompositions.
    assert(m * whi == whi * m) by(nonlinear_arith);
    assert(w == whi * m + 5);
    lemma_div_mod_step(whi, m, 5);                 // w/m == whi, w%m == 5
    assert(w / m == whi);
    assert(w % m == 5);
    assert(m * suf == suf * m) by(nonlinear_arith);
    assert(whi == suf * m + s);
    lemma_div_mod_step(suf, m, s);                 // whi/m == suf, whi%m == s
    assert(whi / m == suf);
    assert(whi % m == s);

    // ── Phase 1: walk right over blk to the 5-mark.
    lemma_dwalk_right_gen(tm, c, q_back, blk, w, i1, i2, i3, i4);
    let c_right = TmConfig { u: dpile(c.u, blk, m), v: w / m, a: w % m, q: q_back };
    assert(tm_run(tm, c, k) == c_right);
    assert(c_right.a == 5);
    assert(c_right.v == whi);

    // ── Phase 2: marker step (q_back, 5, vk, q_read, R) — restore vk, move R onto α[k+1].
    assert(quint_matches(tm.quints[j], c_right));
    lemma_tm_step_picks(tm, c_right, j);
    let c_marker = apply_quint(tm.quints[j], c_right, m);
    assert(tm_step(tm, c_right) == Some(c_marker));
    // R-move a2 == vk: u' = u·m + vk, v' = v/m == suf, a' = v%m == s.
    assert(c_marker.u == dpile(c.u, blk, m) * m + vk);
    assert(c_marker.v == suf);     // (w/m)/m == whi/m == suf
    assert(c_marker.a == s);       // (w/m)%m == whi%m == s
    assert(c_marker.q == q_read);

    // ── Phase 3: read+remark (q_read, s, 5, q_walk, L) — write 5 at k+1, record s, move L onto vk.
    assert(quint_matches(tm.quints[jr], c_marker));   // q == q_read, a == s
    lemma_tm_step_picks(tm, c_marker, jr);
    let c_read = apply_quint(tm.quints[jr], c_marker, m);
    assert(tm_step(tm, c_marker) == Some(c_read));
    // L-move a2 == 5: u' = u/m, v' = v·m + 5, a' = u%m.
    assert(vk < m);
    lemma_div_mod_step(dpile(c.u, blk, m), m, vk);   // (dpile·m+vk)/m == dpile, %m == vk
    assert(c_read.u == dpile(c.u, blk, m));
    assert(c_read.v == suf * m + 5);
    assert(c_read.a == vk);
    assert(c_read.q == q_walk);

    // ── Phase 4: walk left over blk2 = [vk] ++ drev(blk) (prefix grown by vk) back to the boundary.
    let dr = drev(blk);
    lemma_drev_len(blk);              // |dr| == k
    lemma_drev_digit_bound(blk, 4);   // dr digits in 1..4
    let blk2 = seq![vk] + dr;
    assert(blk2.len() == k + 1);
    assert(blk2[0] == vk);
    assert(blk2.drop_first() =~= dr);
    assert forall|i: int| 0 <= i < blk2.len() implies 1 <= #[trigger] blk2[i] <= 4 by {
        if i == 0 {
            assert(blk2[0] == vk);
        } else {
            assert(blk2[i] == dr[i - 1]);
        }
    }
    // precondition: c_read.u == dpack(dr) + m^k·c.u == dpack(blk2.df) + m^{|blk2|-1}·c.u.
    lemma_dpile_is_dpack_drev(c.u, blk, m);          // dpile(c.u, blk) == c.u·m^k + dpack(dr)
    assert(c.u * pow_nat(m, k) == pow_nat(m, k) * c.u) by(nonlinear_arith);
    assert(c_read.u == dpack(dr, m) + pow_nat(m, k) * c.u);
    assert((blk2.len() - 1) as nat == k);
    lemma_dwalk_left_gen(tm, c_read, q_walk, blk2, c.u, l1, l2, l3, l4);
    let c_final = TmConfig { u: c.u / m, v: dpile(c_read.v, blk2, m), a: c.u % m, q: q_walk };
    assert(tm_run(tm, c_read, (k + 1) as nat) == c_final);

    // final v == dpile(suf·m+5, blk2) == (suf·m+5)·m^{k+1} + dpack(blk ++ [vk]).
    lemma_dpile_is_dpack_drev(suf * m + 5, blk2, m);   // == (suf·m+5)·m^{|blk2|} + dpack(drev(blk2))
    // drev(blk2) == drev([vk] ++ dr) == drev(dr) ++ drev([vk]) == blk ++ [vk].
    lemma_drev_concat(seq![vk], dr);
    lemma_drev_involution(blk);          // drev(dr) =~= blk
    lemma_drev_singleton(vk);            // drev([vk]) =~= [vk]
    assert(drev(blk2) =~= blk + seq![vk]);
    assert(dpack(drev(blk2), m) == dpack(blk + seq![vk], m));
    assert(blk2.len() == k + 1);
    // assemble final v: dpile(c_read.v, blk2) with c_read.v == suf·m+5.
    assert(dpile(c_read.v, blk2, m) == (suf * m + 5) * pow_nat(m, (k + 1) as nat)
        + dpack(blk + seq![vk], m));
    assert((suf * m + 5) * pow_nat(m, (k + 1) as nat)
        == pow_nat(m, (k + 1) as nat) * (m * suf + 5)) by(nonlinear_arith);
    assert(c_final.v == dpack(blk + seq![vk], m) + pow_nat(m, (k + 1) as nat) * (m * suf + 5));

    // ── Compose the four runs: 2k+3 = k + (1 + (1 + (k+1))).
    lemma_tm_run_split(tm, c, k, (k + 3) as nat);          // tm_run(c, 2k+3) == tm_run(c_right, k+3)
    lemma_tm_run_split(tm, c_right, 1, (k + 2) as nat);    // tm_run(c_right, k+3) == tm_run(c_marker, k+2)
    lemma_tm_run_split(tm, c_marker, 1, (k + 1) as nat);   // tm_run(c_marker, k+2) == tm_run(c_read, k+1)
    assert(tm_run(tm, c_marker, 0) == c_marker);
    assert(tm_run(tm, c_read, 0) == c_read);
    assert(tm_run(tm, c_right, 1) == c_marker);
    assert(tm_run(tm, c_marker, 1) == c_read);
    assert((2 * k + 3) as nat == (k + (k + 3)) as nat);
    assert(tm_run(tm, c, (2 * k + 3) as nat) == c_final);
}

/// **B-cmp.3 — the gap-cross + boundary transition** (`docs/gap2-input-loader-plan.md` §N+23, the bridge
/// into the digit COMPARE B-cmp.4). After a [`lemma_cmp_marker_advance`] the head sits **one cell into `u`**
/// scanning the output stack's low cell `U % m` (`u == U / m`), in the left-walk state `q_walk` (which
/// carries the marker value `V_k`). The output stack `U` has shape `[g consumed-output `0`s][output frontier
/// `d_o`][rest]` — i.e. `U == pile_zeros(d_o + m·out_rest, g, m)`, with `d_o ∈ 1..4` the next output digit
/// and `g ≥ 1` the gap (every prior match consumed a digit to `0`, so the gap is nonempty in steady state).
///
/// **The boundary transition (the determinism fix, see §N+23).** Output and α share the `1..4` alphabet, so
/// the compare CANNOT live in `q_walk` — the compare quintuple `(q_walk, V, …)` would collide with the
/// left-walk `(q_walk, V, V, q_walk, L)`. Instead the FIRST step over the gap-`0` switches to a fresh
/// compare-mode state `q_cmp` (the gap-`0` is the *virtual boundary marker*): step `(q_walk, 0, 0, q_cmp, L)`,
/// then skip the remaining gap with `(q_cmp, 0, 0, q_cmp, L)` ([`crate::tm_skip_blank::lemma_skip0_left`]),
/// landing the head scanning `d_o` in `q_cmp`. The crossed `0`s migrate onto `v` (`v == pile_zeros(c.v, g, m)`)
/// — popped back when the match-action walks right (balanced, no pollution). Fuel `g`. Requires `n ≥ 4`
/// (so `d_o ≤ 4 < m`). Leaves the head exactly where the compare reads: scanning `d_o ∈ 1..4` in `q_cmp`
/// (carrying `V_k`), ready for `(q_cmp, d_o, …)`.
pub proof fn lemma_cmp_gap_cross(
    tm: Tm, c: TmConfig, q_walk: nat, q_cmp: nat, g: nat, d_o: nat, out_rest: nat,
    ib: int, i0: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        1 <= d_o <= 4,
        g >= 1,
        c.a == pile_zeros(d_o + tm.m * out_rest, g, tm.m) % tm.m,
        c.u == pile_zeros(d_o + tm.m * out_rest, g, tm.m) / tm.m,
        c.q == q_walk,
        0 <= ib < tm.quints.len(),
        0 <= i0 < tm.quints.len(),
        tm.quints[ib] == mk_quint(q_walk, 0, 0, q_cmp, Dir::L),   // boundary transition q_walk → q_cmp
        tm.quints[i0] == mk_quint(q_cmp, 0, 0, q_cmp, Dir::L),    // gap skip in q_cmp
    ensures
        tm_run(tm, c, g)
            == (TmConfig { u: out_rest, v: pile_zeros(c.v, g, tm.m), a: d_o, q: q_cmp }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);   // n >= 4 ∧ n < m ⟹ m ≥ 5
    let big_x = d_o + m * out_rest;
    assert(m * out_rest == out_rest * m) by(nonlinear_arith);
    assert(big_x == out_rest * m + d_o);
    lemma_div_mod_step(out_rest, m, d_o);   // big_x / m == out_rest, big_x % m == d_o (d_o < m)

    // U = pile_zeros(big_x, g) = pile_zeros(big_x, g-1)·m ⟹ scanned low cell is a 0.
    let u0 = pile_zeros(big_x, (g - 1) as nat, m);
    assert(pile_zeros(big_x, g, m) == u0 * m);
    assert((u0 * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((u0 * m) / m == u0) by(nonlinear_arith) requires m > 1;
    assert(c.a == 0);
    assert(c.u == u0);

    // ── Step 1: boundary transition (q_walk, 0, 0, q_cmp, L) — step left into the gap, switch to q_cmp.
    lemma_tm_step_picks(tm, c, ib);
    let c1 = apply_quint(tm.quints[ib], c, m);
    assert(tm_step(tm, c) == Some(c1));
    assert(c1.u == c.u / m);   // L-move a2 == 0
    assert(c1.v == c.v * m);
    assert(c1.a == c.u % m);
    assert(c1.q == q_cmp);

    if g == 1 {
        // u0 == pile_zeros(big_x, 0) == big_x ⟹ c1 already scans d_o.
        assert(u0 == big_x);
        assert(c1.a == big_x % m);   // == d_o
        assert(c1.u == big_x / m);   // == out_rest
        assert(pile_zeros(c.v, 0, m) == c.v);
        assert(pile_zeros(c.v, 1, m) == pile_zeros(c.v, 0, m) * m);   // pile_zeros unfold
        assert(pile_zeros(c.v, 1, m) == c.v * m);
        assert(c1 == (TmConfig { u: out_rest, v: pile_zeros(c.v, 1, m), a: d_o, q: q_cmp }));
        assert(tm_run(tm, c1, 0) == c1);
        assert(tm_run(tm, c, 1) == c1);
    } else {
        // g >= 2: u0 == pile_zeros(big_x, g-1) == pile_zeros(big_x, g-2)·m ⟹ c1 still scans a 0.
        let u1 = pile_zeros(big_x, (g - 2) as nat, m);
        assert(u0 == u1 * m);
        assert((u1 * m) % m == 0) by(nonlinear_arith) requires m > 1;
        assert((u1 * m) / m == u1) by(nonlinear_arith) requires m > 1;
        assert(c1.a == 0);
        assert(c1.u == u1);
        lemma_skip0_left(tm, c1, q_cmp, (g - 2) as nat, big_x, i0);
        // ensures tm_run(c1, g-1) == { u: big_x/m, v: pile_zeros(c1.v, g-1), a: big_x%m, q: q_cmp }
        assert(((g - 2) as nat + 1) as nat == (g - 1) as nat);
        lemma_pile_zeros_shift(c.v, (g - 1) as nat, m);   // pile_zeros(c.v·m, g-1) == pile_zeros(c.v, g)
        assert(c1.v == c.v * m);
        assert(pile_zeros(c1.v, (g - 1) as nat, m) == pile_zeros(c.v, g, m));
        // compose: tm_run(c, g) == tm_run(c1, g-1).
        assert(tm_run(tm, c, g) == tm_run(tm, c1, (g - 1) as nat));
        assert(tm_run(tm, c, g)
            == (TmConfig { u: out_rest, v: pile_zeros(c.v, g, m), a: d_o, q: q_cmp }));
    }
}

/// **B-cmp.4 — the matched-digit round step** (`docs/gap2-input-loader-plan.md` §N+23). The MATCH branch of
/// the digit compare, composed end-to-end with the return walk and the marker advance into one config-level
/// round. Entry = [`lemma_cmp_gap_cross`]'s output: head scanning the output frontier `d_o` in the compare
/// state `q_cmp` (carrying the marker value `V_k = vk`), with `d_o == vk` (the MATCH), output above in `u`
/// (`u == out_rest`), and the full α stack below `g ≥ 1` consumed-output `0`s (`v == pile_zeros(α, g, m)`,
/// `α == dpack(blk) + m^{|blk|}·w` the restored prefix `blk` followed by the marker `w == m·whi + 5` and
/// α's tail, `whi == m·suf + s` so `s = α[k+1] ∈ 1..4` is the next α digit). The machine:
///   1. **compare match** `(q_cmp, vk, 0, q_back, R)` — write `0` (consume the output digit), step R toward
///      the boundary, switch to `q_back` (the marker-advance entry state for value `vk`);
///   2. **return walk** `(q_back, 0, 0, q_back, R)` — [`lemma_skip0_right`] crosses the (now `g`) gap `0`s
///      back to α-low, landing scanning `blk[0]` — exactly [`lemma_cmp_marker_advance`]'s entry;
///   3. **marker advance** — restore `vk`, read the next α digit `s` into state `q_walk`, slide the marker
///      one cell deeper, return the head to the output frontier.
/// Net effect: the α stack grows its restored prefix by `vk` and slides the marker (`(blk, k, w) → (blk++[vk],
/// k+1, m·suf+5)`); the consumed output digit becomes a `0` (the gap grows `g → g+1`); the head ends one cell
/// into `u` scanning `a == 0` (the new top gap cell), in `q_walk` holding the next frontier value `s` — the
/// **same invariant shape** B-cmp.5 iterates (feeds the next [`lemma_cmp_gap_cross`] with gap `g+1`). Fuel
/// `2·|blk| + g + 4`. Requires `n ≥ 5`. No tape content destroyed except the matched output digit (consumed
/// to `0`, as intended); α is value-preserved.
pub proof fn lemma_cmp_match_round(
    tm: Tm, c: TmConfig,
    q_cmp: nat, q_back: nat, q_read: nat, q_walk: nat,
    blk: Seq<nat>, w: nat, whi: nat, suf: nat, vk: nat, s: nat, g: nat, out_rest: nat,
    jc: int, js: int,
    i1: int, i2: int, i3: int, i4: int, j: int, jr: int,
    l1: int, l2: int, l3: int, l4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        1 <= vk <= 4,
        1 <= s <= 4,
        g >= 1,
        w == tm.m * whi + 5,
        whi == tm.m * suf + s,
        c.a == vk,                 // the matched output digit (d_o == vk)
        c.u == out_rest,
        c.v == pile_zeros(dpack(blk, tm.m) + pow_nat(tm.m, blk.len()) * w, g, tm.m),
        c.q == q_cmp,
        0 <= jc < tm.quints.len(),
        0 <= js < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        0 <= i3 < tm.quints.len(),
        0 <= i4 < tm.quints.len(),
        0 <= j < tm.quints.len(),
        0 <= jr < tm.quints.len(),
        0 <= l1 < tm.quints.len(),
        0 <= l2 < tm.quints.len(),
        0 <= l3 < tm.quints.len(),
        0 <= l4 < tm.quints.len(),
        tm.quints[jc] == mk_quint(q_cmp, vk, 0, q_back, Dir::R),    // compare match
        tm.quints[js] == mk_quint(q_back, 0, 0, q_back, Dir::R),    // gap skip right (return)
        tm.quints[i1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[i2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[i3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[i4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
        tm.quints[j]  == mk_quint(q_back, 5, vk, q_read, Dir::R),
        tm.quints[jr] == mk_quint(q_read, s, 5, q_walk, Dir::L),
        tm.quints[l1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[l2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[l3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[l4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
    ensures
        tm_run(tm, c, (2 * blk.len() + g + 4) as nat)
            == (TmConfig {
                    u: pile_zeros(out_rest, g, tm.m),
                    v: dpack(blk + seq![vk], tm.m)
                        + pow_nat(tm.m, (blk.len() + 1) as nat) * (tm.m * suf + 5),
                    a: 0,
                    q: q_walk,
               }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let k = blk.len();
    let alpha = dpack(blk, m) + pow_nat(m, k) * w;

    // ── Step 1: compare match (q_cmp, vk, 0, q_back, R) — consume output digit, step R toward boundary.
    assert(quint_matches(tm.quints[jc], c));   // q == q_cmp, a == vk
    lemma_tm_step_picks(tm, c, jc);
    let c1 = apply_quint(tm.quints[jc], c, m);
    assert(tm_step(tm, c) == Some(c1));
    // R-move a2 == 0: u' = u*m+0, v' = v/m, a' = v%m, q' = q_back.
    assert(c1.u == out_rest * m);
    let vlow = pile_zeros(alpha, (g - 1) as nat, m);
    assert(pile_zeros(alpha, g, m) == vlow * m);   // pile_zeros unfold (g >= 1)
    assert((vlow * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((vlow * m) / m == vlow) by(nonlinear_arith) requires m > 1;
    assert(c1.v == vlow);
    assert(c1.a == 0);
    assert(c1.q == q_back);

    // ── Step 2: return walk — skip0_right over the remaining gap back to α-low.
    lemma_skip0_right(tm, c1, q_back, (g - 1) as nat, alpha, js);
    assert(((g - 1) as nat + 1) as nat == g);
    let c2 = TmConfig { u: pile_zeros(c1.u, g, m), v: alpha / m, a: alpha % m, q: q_back };
    assert(tm_run(tm, c1, g) == c2);

    // α decomposition: α == ma_cv * m + blk[0], ma_cv == marker-advance's required c.v.
    let ma_cv = dpack(blk.drop_first(), m) + pow_nat(m, (k - 1) as nat) * w;
    assert(blk[0] <= 4);
    assert(dpack(blk, m) == blk[0] + m * dpack(blk.drop_first(), m));   // dpack unfold (blk nonempty)
    lemma_pow_nat_unfold(m, k);   // pow_nat(m, k) == m * pow_nat(m, k-1)
    assert(alpha == blk[0] + m * ma_cv) by(nonlinear_arith)
        requires
            alpha == dpack(blk, m) + pow_nat(m, k) * w,
            dpack(blk, m) == blk[0] + m * dpack(blk.drop_first(), m),
            pow_nat(m, k) == m * pow_nat(m, (k - 1) as nat),
            ma_cv == dpack(blk.drop_first(), m) + pow_nat(m, (k - 1) as nat) * w;
    assert(m * ma_cv == ma_cv * m) by(nonlinear_arith);
    assert(alpha == ma_cv * m + blk[0]);
    lemma_div_mod_step(ma_cv, m, blk[0]);   // alpha/m == ma_cv, alpha%m == blk[0] (blk[0] < m)
    assert(c2.v == ma_cv);
    assert(c2.a == blk[0]);

    // c2.u == pile_zeros(out_rest, g) * m.
    lemma_pile_zeros_shift(out_rest, g, m);   // pile_zeros(out_rest*m, g) == pile_zeros(out_rest, g+1)
    assert(pile_zeros(out_rest, (g + 1) as nat, m) == pile_zeros(out_rest, g, m) * m);   // unfold
    assert(c2.u == pile_zeros(out_rest, g, m) * m);

    // ── Step 3: marker advance — advance marker k→k+1, read s, return to output frontier.
    lemma_cmp_marker_advance(tm, c2, q_back, q_read, q_walk, blk, w, whi, suf, vk, s,
        i1, i2, i3, i4, j, jr, l1, l2, l3, l4);
    let c3 = TmConfig {
        u: c2.u / m,
        v: dpack(blk + seq![vk], m) + pow_nat(m, (k + 1) as nat) * (m * suf + 5),
        a: c2.u % m,
        q: q_walk,
    };
    assert(tm_run(tm, c2, (2 * k + 3) as nat) == c3);
    // c3.u == pile_zeros(out_rest, g), c3.a == 0.
    assert((pile_zeros(out_rest, g, m) * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert((pile_zeros(out_rest, g, m) * m) / m == pile_zeros(out_rest, g, m))
        by(nonlinear_arith) requires m > 1;
    assert(c3.u == pile_zeros(out_rest, g, m));
    assert(c3.a == 0);

    // ── Compose: total = 1 + g + (2k+3) = 2k + g + 4.
    assert((g + 2 * k + 3) as nat == (g + (2 * k + 3)) as nat);
    lemma_tm_run_split(tm, c, 1, (g + 2 * k + 3) as nat);    // tm_run(c, 1+(g+2k+3)) == tm_run(c1, g+2k+3)
    lemma_tm_run_split(tm, c1, g, (2 * k + 3) as nat);       // tm_run(c1, g+(2k+3)) == tm_run(c2, 2k+3)
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c, 1) == c1);                          // single step
    assert((2 * k + g + 4) as nat == (1 + (g + 2 * k + 3)) as nat);
    assert(tm_run(tm, c, (2 * k + g + 4) as nat) == c3);
}

/// **B-cmp.5 (the induction STEP) — one matched round `INV(k) → INV(k+1)`.** Composes the gap-cross
/// ([`lemma_cmp_gap_cross`], B-cmp.3) and the match round ([`lemma_cmp_match_round`], B-cmp.4) into a single
/// config-level move over the loop invariant. This is exactly the step the full compare loop (B-cmp.5)
/// iterates; isolating it keeps the loop induction (still to come) a clean `decreases n` over this brick.
///
/// Entry `c == INV(k)`: head one cell into `u` scanning the top gap-`0` (`a == 0`), output stack
/// `U == pile_zeros(d_o + m·out_rest, g, m)` (gap `g ≥ 1`, then output frontier `d_o`, then `out_rest`),
/// α stack `v == dpack(blk) + m^{|blk|}·w` (restored prefix `blk`, marker `w == m·whi + 5` hiding the
/// current α digit, `whi == m·suf + s` so `s` is the next α digit), state `q_walk`. **`d_o == vk`** is the
/// MATCH (the output frontier equals the marker value carried in state). One round runs:
/// B-cmp.3 (cross the gap into `q_cmp`) then B-cmp.4 (compare-match → return → marker-advance), landing at
/// `INV(k+1)`: α prefix grown by `vk`, marker slid one deeper, gap grown by one (`d_o` consumed to `0`),
/// head back one cell into `u` scanning `0` in `q_walk` holding the next value `s`. Fuel `2·|blk| + 2·g + 4`
/// (`g + (2·|blk| + g + 4)`; in the loop `g == |blk| == k` so this is `4k + 4`). Requires `n ≥ 5`.
pub proof fn lemma_cmp_round(
    tm: Tm, c: TmConfig,
    q_walk: nat, q_cmp: nat, q_back: nat, q_read: nat,
    blk: Seq<nat>, w: nat, whi: nat, suf: nat, vk: nat, s: nat, g: nat, d_o: nat, out_rest: nat,
    ib: int, ic: int, jc: int, js: int,
    r1: int, r2: int, r3: int, r4: int, jm: int, jr: int,
    l1: int, l2: int, l3: int, l4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        1 <= vk <= 4,
        1 <= s <= 4,
        d_o == vk,                 // the MATCH
        g >= 1,
        w == tm.m * whi + 5,
        whi == tm.m * suf + s,
        c.a == pile_zeros(d_o + tm.m * out_rest, g, tm.m) % tm.m,
        c.u == pile_zeros(d_o + tm.m * out_rest, g, tm.m) / tm.m,
        c.v == dpack(blk, tm.m) + pow_nat(tm.m, blk.len()) * w,
        c.q == q_walk,
        0 <= ib < tm.quints.len(),
        0 <= ic < tm.quints.len(),
        0 <= jc < tm.quints.len(),
        0 <= js < tm.quints.len(),
        0 <= r1 < tm.quints.len(),
        0 <= r2 < tm.quints.len(),
        0 <= r3 < tm.quints.len(),
        0 <= r4 < tm.quints.len(),
        0 <= jm < tm.quints.len(),
        0 <= jr < tm.quints.len(),
        0 <= l1 < tm.quints.len(),
        0 <= l2 < tm.quints.len(),
        0 <= l3 < tm.quints.len(),
        0 <= l4 < tm.quints.len(),
        tm.quints[ib] == mk_quint(q_walk, 0, 0, q_cmp, Dir::L),    // B-cmp.3 boundary transition
        tm.quints[ic] == mk_quint(q_cmp, 0, 0, q_cmp, Dir::L),     // B-cmp.3 gap skip
        tm.quints[jc] == mk_quint(q_cmp, vk, 0, q_back, Dir::R),   // B-cmp.4 compare match
        tm.quints[js] == mk_quint(q_back, 0, 0, q_back, Dir::R),   // B-cmp.4 return skip
        tm.quints[r1] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        tm.quints[r2] == mk_quint(q_back, 2, 2, q_back, Dir::R),
        tm.quints[r3] == mk_quint(q_back, 3, 3, q_back, Dir::R),
        tm.quints[r4] == mk_quint(q_back, 4, 4, q_back, Dir::R),
        tm.quints[jm] == mk_quint(q_back, 5, vk, q_read, Dir::R),
        tm.quints[jr] == mk_quint(q_read, s, 5, q_walk, Dir::L),
        tm.quints[l1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[l2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[l3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[l4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
    ensures
        tm_run(tm, c, (2 * blk.len() + 2 * g + 4) as nat)
            == (TmConfig {
                    u: pile_zeros(out_rest, g, tm.m),
                    v: dpack(blk + seq![vk], tm.m)
                        + pow_nat(tm.m, (blk.len() + 1) as nat) * (tm.m * suf + 5),
                    a: 0,
                    q: q_walk,
               }),
{
    let m = tm.m;
    let k = blk.len();
    let alpha = dpack(blk, m) + pow_nat(m, k) * w;

    // ── B-cmp.3: cross the gap, land scanning d_o in q_cmp.
    lemma_cmp_gap_cross(tm, c, q_walk, q_cmp, g, d_o, out_rest, ib, ic);
    let c_cmp = TmConfig { u: out_rest, v: pile_zeros(c.v, g, m), a: d_o, q: q_cmp };
    assert(tm_run(tm, c, g) == c_cmp);
    // c_cmp matches B-cmp.4's compare-config entry: c.v == alpha ⟹ c_cmp.v == pile_zeros(alpha, g).
    assert(c_cmp.v == pile_zeros(alpha, g, m));

    // ── B-cmp.4: compare-match (d_o == vk) → return → marker-advance, landing at INV(k+1).
    lemma_cmp_match_round(tm, c_cmp, q_cmp, q_back, q_read, q_walk, blk, w, whi, suf, vk, s, g, out_rest,
        jc, js, r1, r2, r3, r4, jm, jr, l1, l2, l3, l4);
    let c_next = TmConfig {
        u: pile_zeros(out_rest, g, m),
        v: dpack(blk + seq![vk], m) + pow_nat(m, (k + 1) as nat) * (m * suf + 5),
        a: 0,
        q: q_walk,
    };
    assert(tm_run(tm, c_cmp, (2 * k + g + 4) as nat) == c_next);

    // ── Compose: total = g + (2k + g + 4) = 2k + 2g + 4.
    lemma_tm_run_split(tm, c, g, (2 * k + g + 4) as nat);
    assert((2 * k + 2 * g + 4) as nat == (g + (2 * k + g + 4)) as nat);
    assert(tm_run(tm, c, (2 * k + 2 * g + 4) as nat) == c_next);
}

} // verus!
