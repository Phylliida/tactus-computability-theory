//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the frontier block-emit.
//!
//! Model B (home/shuttle, Danielle 2026-06-26): the emitter's tape is
//! `[iₐ ones] 0 [i_b ones] 0 [output digits] 0 [blanks]`, head shuttling. Per `(blk)ⁱ` iteration the head
//! surges right to the frontier (the first blank past the output; everything right of it is blank, so
//! `v == 0`), runs a **state cycle** writing `blk`'s digits one per step moving R, then returns home. The
//! "sequential write" step (Danielle's choreography step 3) is this module: the block lives in the
//! TM state-transition graph (distinct state per digit — they all scan the blank `0`, so determinism
//! forces distinct keys), NOT in the tape counters.
//!
//! An R-move at the frontier writes the digit onto the LEFT stack `u` (atop the output the surge brought
//! there) and pops a blank off `v` (staying `v == 0`, scanned `== 0`). So emitting `blk` appends it to the
//! `u`-side as `dpile(c.u, blk, m)` — the home-return walk ([`crate::tm_dwalk::lemma_dwalk_left`]) later
//! moves the whole `[output ++ blk]` back to `v`. This file gives the 1-step primitive
//! [`lemma_emit_one_frontier`] and the concrete singleton / triple compositions (`blk` lengths 1 and 3 —
//! the only block sizes in [`crate::gap2_fam_digits`]).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_dstring::dpile;

verus! {

/// **One frontier write (1 step).** At the frontier — head scanning the blank `0` with all-blank right
/// tape (`v == 0`) — the quintuple `(q, 0, s, q2, R)` writes the digit `s` onto `u` and moves R, popping a
/// blank: the config becomes `{u: c.u·m + s, v: 0, a: 0, q: q2}`. The atomic step of the sequential-write
/// state cycle.
pub proof fn lemma_emit_one_frontier(tm: Tm, c: TmConfig, q: nat, s: nat, q2: nat, i_e: int)
    requires
        tm_wf(tm),
        c.v == 0,
        c.a == 0,
        c.q == q,
        0 <= i_e < tm.quints.len(),
        tm.quints[i_e] == mk_quint(q, 0, s, q2, Dir::R),
    ensures
        tm_run(tm, c, 1)
            == (TmConfig { u: c.u * tm.m + s, v: 0, a: 0, q: q2 }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the quintuple matches (q == c.q, a == 0 == c.a) and fires (R-move, a2 == s).
    assert(quint_matches(tm.quints[i_e], c));
    lemma_tm_step_picks(tm, c, i_e);
    let c_next = apply_quint(tm.quints[i_e], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // R-move: u' = u·m + s, v' = v/m = 0/m = 0, a' = v%m = 0%m = 0.
    assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
    assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
    assert(c_next == (TmConfig { u: c.u * m + s, v: 0, a: 0, q: q2 }));
    assert(tm_run(tm, c_next, 0) == c_next);
    assert(tm_run(tm, c, 1) == c_next);
}

/// **Emit a singleton block `[s]` (1 step).** From the frontier config in state `q0`, the quintuple
/// `(q0, 0, s, q1, R)` lands `{u: dpile(c.u, [s], m), v: 0, a: 0, q: q1}` — the output side `u` grows by
/// the single digit `s` (`dpile(u, [s]) == u·m + s`).
pub proof fn lemma_emit_block1_frontier(tm: Tm, c: TmConfig, q0: nat, s: nat, q1: nat, i0: int)
    requires
        tm_wf(tm),
        c.v == 0,
        c.a == 0,
        c.q == q0,
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q0, 0, s, q1, Dir::R),
    ensures
        tm_run(tm, c, 1)
            == (TmConfig { u: dpile(c.u, seq![s], tm.m), v: 0, a: 0, q: q1 }),
{
    let m = tm.m;
    lemma_emit_one_frontier(tm, c, q0, s, q1, i0);
    // dpile(u, [s]) == u·m + s (one push onto the empty drop_first).
    assert(seq![s].len() == 1);
    assert(seq![s][0] == s);
    assert(seq![s].drop_first() =~= Seq::<nat>::empty());
    assert(dpile(c.u, seq![s], m) == dpile(c.u * m + s, seq![s].drop_first(), m));
    assert(dpile(c.u * m + s, Seq::<nat>::empty(), m) == c.u * m + s);
}

/// **Emit a triple block `[s0, s1, s2]` (3 steps).** From the frontier config in state `q0`, the three
/// sequential-write quintuples `(q0,0,s0,q1,R)`, `(q1,0,s1,q2,R)`, `(q2,0,s2,q3,R)` write `s0, s1, s2`
/// onto `u` in order and land `{u: dpile(c.u, [s0,s1,s2], m), v: 0, a: 0, q: q3}`. The state cycle for the
/// only multi-digit `fam_digits` blocks (`[4,1,2]`, `[4,3,2]`). Chains [`lemma_emit_one_frontier`] thrice
/// via [`lemma_tm_run_split`].
pub proof fn lemma_emit_block3_frontier(
    tm: Tm, c: TmConfig, q0: nat, s0: nat, s1: nat, s2: nat, q1: nat, q2: nat, q3: nat,
    i0: int, i1: int, i2: int,
)
    requires
        tm_wf(tm),
        c.v == 0,
        c.a == 0,
        c.q == q0,
        0 <= i0 < tm.quints.len(),
        0 <= i1 < tm.quints.len(),
        0 <= i2 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q0, 0, s0, q1, Dir::R),
        tm.quints[i1] == mk_quint(q1, 0, s1, q2, Dir::R),
        tm.quints[i2] == mk_quint(q2, 0, s2, q3, Dir::R),
    ensures
        tm_run(tm, c, 3)
            == (TmConfig { u: dpile(c.u, seq![s0, s1, s2], tm.m), v: 0, a: 0, q: q3 }),
{
    let m = tm.m;
    // step 1: write s0 ⟹ c1 = {u·m+s0, 0, 0, q1}.
    lemma_emit_one_frontier(tm, c, q0, s0, q1, i0);
    let c1 = TmConfig { u: c.u * m + s0, v: 0, a: 0, q: q1 };
    assert(tm_run(tm, c, 1) == c1);
    // step 2: write s1 ⟹ c2 = {(u·m+s0)·m+s1, 0, 0, q2}.
    lemma_emit_one_frontier(tm, c1, q1, s1, q2, i1);
    let c2 = TmConfig { u: c1.u * m + s1, v: 0, a: 0, q: q2 };
    assert(tm_run(tm, c1, 1) == c2);
    // step 3: write s2 ⟹ c3 = {((u·m+s0)·m+s1)·m+s2, 0, 0, q3}.
    lemma_emit_one_frontier(tm, c2, q2, s2, q3, i2);
    let c3 = TmConfig { u: c2.u * m + s2, v: 0, a: 0, q: q3 };
    assert(tm_run(tm, c2, 1) == c3);
    // chain 1+1+1.
    lemma_tm_run_split(tm, c, 1, 1);
    assert(tm_run(tm, c, 2) == c2);
    lemma_tm_run_split(tm, c, 2, 1);
    assert(tm_run(tm, c, 3) == c3);
    // c3.u == dpile(c.u, [s0,s1,s2]) — unfold dpile one level at a time (default fuel 1).
    let blk = seq![s0, s1, s2];
    let b1 = seq![s1, s2];
    let b2 = seq![s2];
    assert(blk.len() == 3 && b1.len() == 2 && b2.len() == 1);
    assert(blk[0] == s0 && b1[0] == s1 && b2[0] == s2);
    assert(blk.drop_first() =~= b1);
    assert(b1.drop_first() =~= b2);
    assert(b2.drop_first() =~= Seq::<nat>::empty());
    // dpile(u, [s0,s1,s2]) == dpile(u·m+s0, [s1,s2]) == dpile((u·m+s0)·m+s1, [s2]) == ((u·m+s0)·m+s1)·m+s2.
    assert(dpile(c.u, blk, m) == dpile(c.u * m + s0, b1, m));
    assert(dpile(c.u * m + s0, b1, m) == dpile((c.u * m + s0) * m + s1, b2, m));
    assert(dpile((c.u * m + s0) * m + s1, b2, m)
        == dpile(((c.u * m + s0) * m + s1) * m + s2, Seq::<nat>::empty(), m));
    assert(dpile(((c.u * m + s0) * m + s1) * m + s2, Seq::<nat>::empty(), m)
        == ((c.u * m + s0) * m + s1) * m + s2);
    assert(dpile(c.u, blk, m) == c3.u);
}

} // verus!
