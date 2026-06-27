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
    lemma_dpile_is_dpack_drev};
use crate::tm_run_lemmas::lemma_tm_run_split;

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

} // verus!
