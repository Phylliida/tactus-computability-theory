//! # GAP-2 G2-F Route (i) brick R-P — the copy-and-park core.
//!
//! Composes the entry handshake (deposit the ignition-held low digit `d0`) with the digit-walk to park
//! `α`'s digit sequence in a blank-delimited block, freeing `u` as workspace. The ignition layer
//! (`gap2_ignition.rs`) lands the machine at `rep1(c1)` with `c1 = {u: dpack([d2,d3,…]), v: 0, a: d1,
//! q: start(d0)}` — `d0` recorded only in the per-digit start state. Two manual steps move `d0` onto the
//! (empty) right tape `v`, after which [`crate::tm_dwalk::lemma_dwalk_left`] sweeps the whole digit
//! block onto `v`:
//!
//! ```text
//!   start(d0):   write d1 back, move R  ⟹  u = dpack([d1,d2,…]), scan = 0,        state deposit(d0)
//!   deposit(d0): write d0,      move L  ⟹  v = dpack([d0]), scan = d1, u back,     state q_walk
//!   dwalk_left over [d1,d2,…,d_{L-1}]   ⟹  v = dpile(dpack([d0]), [d1,…]), u = 0,  head on blank
//! ```
//!
//! Net: `α`'s digits are parked **reversed** in `v` (high digit lowest), `u` freed, head on a blank
//! boundary — the canonical layout the R-cmp ping-pong reads. The lemmas are generic over an abstract
//! `tm` carrying the five handshake quintuples at given indices (the eventual `psc_act` window supplies
//! them via [`crate::tm_assemble4::lemma_slot_index`]).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-P copy-and-park). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_dstring::{dpack, dpile, lemma_dpack_pop, lemma_dpack_push, lemma_dpack_empty};
use crate::tm_dwalk::lemma_dwalk_left;

verus! {

/// **The entry handshake (2 steps).** From `c = {u: dpack(tail), v: 0, a: d1, q: q_start}` (the ignition
/// output, low digit `d0` held in the start state `q_start`), the start quintuple
/// `(q_start, x, x, q_deposit, R)` (writes the scanned digit back, moves right — one per `x ∈ 1..4`) then
/// the deposit quintuple `(q_deposit, 0, d0, q_walk, L)` (deposits `d0` onto the empty `v`, moves left)
/// land `{u: dpack(tail), v: dpack([d0]), a: d1, q: q_walk}` — `d0` parked below, head back at `d1`,
/// ready for the digit-walk.
pub proof fn lemma_rp_entry(
    tm: Tm, tail: Seq<nat>, d0: nat, d1: nat,
    q_start: nat, q_deposit: nat, q_walk: nat,
    i_s1: int, i_s2: int, i_s3: int, i_s4: int, i_dep: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        1 <= d0 <= 4,
        1 <= d1 <= 4,
        0 <= i_s1 < tm.quints.len(),
        0 <= i_s2 < tm.quints.len(),
        0 <= i_s3 < tm.quints.len(),
        0 <= i_s4 < tm.quints.len(),
        0 <= i_dep < tm.quints.len(),
        tm.quints[i_s1] == mk_quint(q_start, 1, 1, q_deposit, Dir::R),
        tm.quints[i_s2] == mk_quint(q_start, 2, 2, q_deposit, Dir::R),
        tm.quints[i_s3] == mk_quint(q_start, 3, 3, q_deposit, Dir::R),
        tm.quints[i_s4] == mk_quint(q_start, 4, 4, q_deposit, Dir::R),
        tm.quints[i_dep] == mk_quint(q_deposit, 0, d0, q_walk, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: dpack(tail, tm.m), v: 0, a: d1, q: q_start }, 2)
            == (TmConfig { u: dpack(tail, tm.m), v: dpack(seq![d0], tm.m), a: d1, q: q_walk }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);   // tm_wf ⟹ 0 < n < m, n ≥ 4
    let c0 = TmConfig { u: dpack(tail, m), v: 0, a: d1, q: q_start };
    // ── step 1: the start quintuple for the scanned digit d1 fires (R-move). ──
    let i_s = if d1 == 1 { i_s1 } else if d1 == 2 { i_s2 } else if d1 == 3 { i_s3 } else { i_s4 };
    assert(tm.quints[i_s] == mk_quint(q_start, d1, d1, q_deposit, Dir::R));
    assert(quint_matches(tm.quints[i_s], c0));   // q == q_start, a == d1
    lemma_tm_step_picks(tm, c0, i_s);
    let c1 = apply_quint(tm.quints[i_s], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    // R-move, a2 == d1: u' = u·m + d1, v' = v/m = 0, a' = v%m = 0.
    assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
    assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
    lemma_dpack_push(d1, tail, m);   // dpack([d1]+tail) == d1 + m·dpack(tail)
    assert(d1 + m * dpack(tail, m) == dpack(tail, m) * m + d1) by(nonlinear_arith);
    assert(c1.u == dpack(seq![d1] + tail, m));
    assert(c1.v == 0);
    assert(c1.a == 0);
    assert(c1.q == q_deposit);
    // ── step 2: the deposit quintuple fires on the blank (L-move, writes d0). ──
    assert(quint_matches(tm.quints[i_dep], c1));   // q == q_deposit, a == 0
    lemma_tm_step_picks(tm, c1, i_dep);
    let c2 = apply_quint(tm.quints[i_dep], c1, m);
    assert(tm_step(tm, c1) == Some(c2));
    // L-move, a2 == d0: v'' = v'·m + d0 = d0, a'' = u'%m, u'' = u'/m.
    let blk1 = seq![d1] + tail;
    assert(blk1[0] == d1);
    assert(blk1.drop_first() =~= tail);
    lemma_dpack_pop(blk1, m);   // dpack(blk1)%m == d1, /m == dpack(tail)
    assert(c2.u == dpack(tail, m));
    assert(c2.a == d1);
    assert(0nat * m == 0) by(nonlinear_arith);
    // c2.v == c1.v·m + d0 == 0·m + d0 == d0 == dpack([d0]).
    assert(c2.v == d0);
    // dpack([d0]) == d0: push d0 onto the empty string.
    lemma_dpack_push(d0, Seq::<nat>::empty(), m);   // dpack([d0]+empty) == d0 + m·dpack(empty)
    lemma_dpack_empty(m);                            // dpack(empty) == 0
    assert(seq![d0] + Seq::<nat>::empty() =~= seq![d0]);
    assert(d0 + m * 0 == d0) by(nonlinear_arith);
    assert(dpack(seq![d0], m) == d0);
    assert(c2.v == dpack(seq![d0], m));
    assert(c2.q == q_walk);
    // assemble the 2-step run (fuel-0 base asserts guide tm_run's unfold, as in tm_inc).
    assert(tm_run(tm, c2, 0) == c2);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c1, 1) == c2);
    assert(tm_run(tm, c0, 1) == c1);
    lemma_tm_run_split(tm, c0, 1, 1);
    assert(tm_run(tm, c0, 2) == c2);
}

/// **Copy-and-park (entry ∘ digit-walk).** From the ignition output `{u: dpack(tail), v: 0, a: d1,
/// q: q_start}` with `α`'s digit sequence `α_digits = [d0, d1] + tail` (all digits `1..4`), the entry
/// handshake plus a left digit-walk over `[d1] + tail` park `α` reversed in `v`: after `3 + tail.len()`
/// steps the config is `{u: 0, v: dpile(dpack([d0]), [d1] + tail), a: 0, q: q_walk}` — `u` freed, head on
/// the left blank. Reading `v` low→high yields `α`'s digits in reverse.
pub proof fn lemma_rp_copy_park(
    tm: Tm, tail: Seq<nat>, d0: nat, d1: nat,
    q_start: nat, q_deposit: nat, q_walk: nat,
    i_s1: int, i_s2: int, i_s3: int, i_s4: int, i_dep: int,
    i_w1: int, i_w2: int, i_w3: int, i_w4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        1 <= d0 <= 4,
        1 <= d1 <= 4,
        forall|k: int| 0 <= k < tail.len() ==> 1 <= #[trigger] tail[k] <= 4,
        0 <= i_s1 < tm.quints.len(),
        0 <= i_s2 < tm.quints.len(),
        0 <= i_s3 < tm.quints.len(),
        0 <= i_s4 < tm.quints.len(),
        0 <= i_dep < tm.quints.len(),
        0 <= i_w1 < tm.quints.len(),
        0 <= i_w2 < tm.quints.len(),
        0 <= i_w3 < tm.quints.len(),
        0 <= i_w4 < tm.quints.len(),
        tm.quints[i_s1] == mk_quint(q_start, 1, 1, q_deposit, Dir::R),
        tm.quints[i_s2] == mk_quint(q_start, 2, 2, q_deposit, Dir::R),
        tm.quints[i_s3] == mk_quint(q_start, 3, 3, q_deposit, Dir::R),
        tm.quints[i_s4] == mk_quint(q_start, 4, 4, q_deposit, Dir::R),
        tm.quints[i_dep] == mk_quint(q_deposit, 0, d0, q_walk, Dir::L),
        tm.quints[i_w1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i_w2] == mk_quint(q_walk, 2, 2, q_walk, Dir::L),
        tm.quints[i_w3] == mk_quint(q_walk, 3, 3, q_walk, Dir::L),
        tm.quints[i_w4] == mk_quint(q_walk, 4, 4, q_walk, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: dpack(tail, tm.m), v: 0, a: d1, q: q_start },
            (3 + tail.len()) as nat)
            == (TmConfig { u: 0, v: dpile(dpack(seq![d0], tm.m), seq![d1] + tail, tm.m), a: 0,
                q: q_walk }),
{
    let m = tm.m;
    let c0 = TmConfig { u: dpack(tail, m), v: 0, a: d1, q: q_start };
    // entry: 2 steps to c_mid = {u: dpack(tail), v: dpack([d0]), a: d1, q: q_walk}.
    lemma_rp_entry(tm, tail, d0, d1, q_start, q_deposit, q_walk, i_s1, i_s2, i_s3, i_s4, i_dep);
    let c_mid = TmConfig { u: dpack(tail, m), v: dpack(seq![d0], m), a: d1, q: q_walk };
    assert(tm_run(tm, c0, 2) == c_mid);
    // digit-walk over blk = [d1] + tail (length 1 + tail.len()).
    let blk = seq![d1] + tail;
    assert(blk.len() == 1 + tail.len());
    assert(blk[0] == d1);
    assert(blk.drop_first() =~= tail);
    assert forall|k: int| 0 <= k < blk.len() implies 1 <= #[trigger] blk[k] <= 4 by {
        if k == 0 { } else { assert(blk[k] == tail[k - 1]); }
    }
    lemma_dwalk_left(tm, c_mid, q_walk, blk, i_w1, i_w2, i_w3, i_w4);
    let c_end = TmConfig { u: 0, v: dpile(c_mid.v, blk, m), a: 0, q: q_walk };
    assert(tm_run(tm, c_mid, blk.len()) == c_end);
    // split: tm_run(c0, 2 + blk.len()) == tm_run(tm_run(c0, 2), blk.len()) == tm_run(c_mid, blk.len()).
    lemma_tm_run_split(tm, c0, 2, blk.len());
    assert((2 + blk.len()) as nat == (3 + tail.len()) as nat);
    assert(tm_run(tm, c0, (3 + tail.len()) as nat) == c_end);
}

} // verus!
