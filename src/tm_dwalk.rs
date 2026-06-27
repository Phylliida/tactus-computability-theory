//! # GAP-2 G2-F Route (i) brick R-P — the digit-walk-left gadget.
//!
//! The symbol-agnostic analog of [`crate::tm_walk::lemma_walk_left_inner`]: instead of the unary loop
//! quintuple `(q_walk, 1, 1, q_walk, L)`, the digit-walk fires *one quintuple per digit symbol*
//! `(q_walk, s, s, q_walk, L)` for `s ∈ {1,2,3,4}`. From the head scanning the low digit of a block of
//! nonzero base-m digits (`α`'s digits, each `1..4`) with the rest in `u`, it peels every digit onto
//! `v` and lands the head on the left blank — the engine of the copy-and-park (R-P) relocation of `α`.
//!
//! The result stack is `dpile(c.v, blk, m)` (the block reversed onto `v`); the loop runs exactly
//! `blk.len()` steps (one per nonzero digit), stopping when the head reaches the blank `0` (where the
//! caller's turnaround quintuple `(q_walk, 0, …)` then fires). Induction on `blk`, a 4-way case split
//! on the scanned digit picking the firing quintuple.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-P). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{dpack, dpile, lemma_dpack_empty, lemma_dpack_pop};

verus! {

/// **The digit-walk-left loop.** From a config in state `q_walk` scanning the low digit `blk[0]` of a
/// block `blk` of nonzero digit-symbols (`1 ≤ blk[k] ≤ 4`), with the rest of the block in `u`
/// (`u == dpack(blk.drop_first())`), the four loop quintuples `(q_walk, s, s, q_walk, L)` (`s ∈ 1..4`)
/// fire `blk.len()` times — peeling each digit onto `v` — and land the head on the left blank
/// (`u == 0`, scanned `== 0`), still in `q_walk`. The stack `v` becomes `dpile(c.v, blk)` (the block
/// reversed on top of the original `v`).
pub proof fn lemma_dwalk_left(
    tm: Tm, c: TmConfig, q_walk: nat, blk: Seq<nat>,
    i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        c.a == blk[0],
        c.u == dpack(blk.drop_first(), tm.m),
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
            == (TmConfig { u: 0, v: dpile(c.v, blk, tm.m), a: 0, q: q_walk }),
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
    assert(quint_matches(tm.quints[i_s], c));   // q == q_walk, a == s == blk[0]
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
        // blk == [s]; c.u == dpack(empty) == 0.
        lemma_dpack_empty(m);
        assert(c.u == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(rest =~= Seq::<nat>::empty());
        assert(dpile(c.v * m + s, rest, m) == c.v * m + s);   // dpile(_, empty) == _
        assert(c_next == (TmConfig { u: 0, v: dpile(c.v, blk, m), a: 0, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(blk.len() == 1);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // rest nonempty; rest[0] == blk[1] ∈ 1..4 < m.
        assert(rest[0] == blk[1]);
        assert(1 <= rest[0] <= 4);
        lemma_dpack_pop(rest, m);   // dpack(rest)%m == rest[0], /m == dpack(rest.drop_first())
        assert(c_next.a == rest[0]);
        assert(c_next.u == dpack(rest.drop_first(), m));
        // rest inherits the digit bound.
        assert forall|k: int| 0 <= k < rest.len() implies 1 <= #[trigger] rest[k] <= 4 by {
            assert(rest[k] == blk[k + 1]);
        }
        lemma_dwalk_left(tm, c_next, q_walk, rest, i1, i2, i3, i4);
        // IH: tm_run(c_next, rest.len()) == (0, dpile(c_next.v, rest), 0, q_walk),
        //     and c_next.v == c.v*m+s ⟹ dpile(c_next.v, rest) == dpile(c.v, blk).
        assert(tm_run(tm, c, blk.len()) == tm_run(tm, c_next, rest.len()));
    }
}

/// **The digit-walk-right loop** — the mirror of [`lemma_dwalk_left`] (`u ↔ v`, `L ↔ R`). From a config
/// in state `q_back` scanning the low digit `blk[0]` of a block `blk` of nonzero digit-symbols, with the
/// rest of the block in `v` (`v == dpack(blk.drop_first())`), the four loop quintuples
/// `(q_back, s, s, q_back, R)` (`s ∈ 1..4`) fire `blk.len()` times — peeling each digit onto `u` — and
/// land the head on the right blank (`v == 0`, scanned `== 0`), still in `q_back`. The stack `u` becomes
/// `dpile(c.u, blk)`. Used by the R-cmp ping-pong re-scan of the parked α-block.
pub proof fn lemma_dwalk_right(
    tm: Tm, c: TmConfig, q_back: nat, blk: Seq<nat>,
    i1: int, i2: int, i3: int, i4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        blk.len() >= 1,
        forall|k: int| 0 <= k < blk.len() ==> 1 <= #[trigger] blk[k] <= 4,
        c.a == blk[0],
        c.v == dpack(blk.drop_first(), tm.m),
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
            == (TmConfig { u: dpile(c.u, blk, tm.m), v: 0, a: 0, q: q_back }),
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
    let rest = blk.drop_first();
    assert(dpile(c.u, blk, m) == dpile(c.u * m + s, rest, m));

    if rest.len() == 0 {
        lemma_dpack_empty(m);
        assert(c.v == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(rest =~= Seq::<nat>::empty());
        assert(dpile(c.u * m + s, rest, m) == c.u * m + s);
        assert(c_next == (TmConfig { u: dpile(c.u, blk, m), v: 0, a: 0, q: q_back }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(blk.len() == 1);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        assert(rest[0] == blk[1]);
        assert(1 <= rest[0] <= 4);
        lemma_dpack_pop(rest, m);
        assert(c_next.a == rest[0]);
        assert(c_next.v == dpack(rest.drop_first(), m));
        assert forall|k: int| 0 <= k < rest.len() implies 1 <= #[trigger] rest[k] <= 4 by {
            assert(rest[k] == blk[k + 1]);
        }
        lemma_dwalk_right(tm, c_next, q_back, rest, i1, i2, i3, i4);
        assert(tm_run(tm, c, blk.len()) == tm_run(tm, c_next, rest.len()));
    }
}

} // verus!
