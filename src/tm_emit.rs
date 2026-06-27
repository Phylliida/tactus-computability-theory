//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, foundation) — the symbol-power emit loop.
//!
//! The emitter's innermost mechanism. An **L-move with written symbol `s`** does two things at once:
//! it pops `u`'s low digit (`a' = u%m`, `u' = u/m`) *and* pushes `s` onto `v` (`v' = v·m + s`). So when
//! `u` holds a unary counter (`repunit_m(i)`) the single loop quintuple `(q_emit, 1, s, q_emit, L)`
//! consumes one counter-`1` and emits one digit `s` per step — running `i` times it lays a run of `i`
//! copies of `s` onto the output stack `v`. This is the symbol-agnostic twin of
//! [`crate::tm_walk::lemma_walk_left_inner`] (which writes `1`), and it produces the `seq_pow([s], i)`
//! digit blocks (`(1)ⁱ`, `(3)ⁱ`) of [`crate::gap2_fam_digits::u_digits`]/`uinv_digits` one iteration at
//! a time — the Production-side analog of the Evaluation-side `lemma_dds_symbol_power`.
//!
//! The result stack is [`pile_sym`]`(c.v, s, i, m)` (the loop accumulator, mirror of `pile_ones`); the
//! bridge [`lemma_pile_sym_is_dpile`] re-expresses it as `dpile(c.v, seq_pow([s], i), m)`, the form the
//! digit-seq algebra ([`crate::gap2_relnum_dds`]) speaks, so the emitted run composes with the explicit
//! `fam_digits` block decomposition.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_two_counter::{repunit_m, lemma_repunit_div_mod, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::dpile;
use crate::gap2_relnum_dds::seq_pow;

verus! {

/// `pile_sym(v, s, k, m)` = the result of pushing `k` copies of the digit `s` onto stack `v` (each push
/// is `·m + s`, the low end). The symbol-generalized [`crate::tm_walk::pile_ones`] (`s = 1`), defined by
/// the push recurrence so `m^k` stays implicit; closed form `v·m^k + s·repunit_m(k)`.
pub open spec fn pile_sym(v: nat, s: nat, k: nat, m: nat) -> nat
    decreases k
{
    if k == 0 { v } else { pile_sym(v, s, (k - 1) as nat, m) * m + s }
}

/// Pushing `k` copies of `s` onto `v·m + s` is the same as pushing `k + 1` copies onto `v` (the closed
/// forms both equal `v·m^{k+1} + s·repunit_m(k+1)`). The bridge that lets the loop induction re-fold the
/// pile — mirror of [`crate::tm_walk::lemma_pile_ones_shift`].
pub proof fn lemma_pile_sym_shift(v: nat, s: nat, k: nat, m: nat)
    ensures
        pile_sym(v * m + s, s, k, m) == pile_sym(v, s, (k + 1) as nat, m),
    decreases k,
{
    if k == 0 {
        // pile_sym(v*m+s, s, 0) == v*m+s == pile_sym(v, s, 0)*m+s == pile_sym(v, s, 1).
        assert(pile_sym(v * m + s, s, 0, m) == v * m + s);
        assert(pile_sym(v, s, 0, m) == v);
        assert(pile_sym(v, s, 1, m) == pile_sym(v, s, 0, m) * m + s);
    } else {
        lemma_pile_sym_shift(v, s, (k - 1) as nat, m);
        // pile_sym(v*m+s, s, k) == pile_sym(v*m+s, s, k-1)*m+s == pile_sym(v, s, k)*m+s == pile_sym(v, s, k+1).
    }
}

/// **The symbol-power emit loop.** From a config in state `q_emit` scanning a `1` (the inner cell of the
/// counter block), with `j0` further ones in `u` (`u == repunit_m(j0)`), the loop quintuple
/// `(q_emit, 1, s, q_emit, L)` fires `j0 + 1` times — consuming the scanned `1` and the `j0` ones in `u`,
/// emitting a copy of the digit `s` onto `v` at each step — and lands the head on the left blank
/// (`u == 0`, scanned `== 0`), still in `q_emit` (where the caller's turnaround quintuple `(q_emit, 0, …)`
/// then fires). The stack `v` becomes `pile_sym(c.v, s, j0 + 1)` (a run of `j0 + 1` copies of `s` on top
/// of the original `v`). Induction on `j0`, the exact shape of [`crate::tm_walk::lemma_walk_left_inner`]
/// with the written `1` generalized to `s`.
pub proof fn lemma_emit_symbol_power_inner(tm: Tm, c: TmConfig, q_emit: nat, s: nat, j0: nat, i_s: int)
    requires
        tm_wf(tm),
        1 <= s,
        s <= tm.n,
        0 <= i_s < tm.quints.len(),
        tm.quints[i_s] == mk_quint(q_emit, 1, s, q_emit, Dir::L),
        c.u == repunit_m(j0, tm.m),
        c.a == 1,
        c.q == q_emit,
    ensures
        tm_run(tm, c, (j0 + 1) as nat)
            == (TmConfig { u: 0, v: pile_sym(c.v, s, (j0 + 1) as nat, tm.m), a: 0, q: q_emit }),
    decreases j0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches c (q == q_emit, a == 1) and fires (L-move, a2 == s).
    lemma_tm_step_picks(tm, c, i_s);
    let c_next = (TmConfig { u: c.u / m, v: c.v * m + s, a: c.u % m, q: q_emit });
    assert(tm_step(tm, c) == Some(c_next));
    if j0 == 0 {
        // c.u == repunit(0) == 0 ⟹ c_next == (0, c.v*m+s, 0, q_emit) == (0, pile_sym(c.v,s,1), 0, q_emit).
        lemma_repunit_zero(m);
        assert(c.u == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(pile_sym(c.v, s, 0, m) == c.v);
        assert(pile_sym(c.v, s, 1, m) == pile_sym(c.v, s, 0, m) * m + s);
        assert(c_next == (TmConfig { u: 0, v: pile_sym(c.v, s, 1, m), a: 0, q: q_emit }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // c.u == repunit(j0); peel one ⟹ c_next.u == repunit(j0-1), c_next.a == 1.
        lemma_repunit_div_mod((j0 - 1) as nat, m);
        assert(((j0 - 1) as nat + 1) as nat == j0);
        assert(c_next.u == repunit_m((j0 - 1) as nat, m));
        assert(c_next.a == 1);
        lemma_emit_symbol_power_inner(tm, c_next, q_emit, s, (j0 - 1) as nat, i_s);
        // IH: tm_run(c_next, j0) == (0, pile_sym(c.v*m+s, s, j0), 0, q_emit).
        lemma_pile_sym_shift(c.v, s, j0, m);   // pile_sym(c.v*m+s, s, j0) == pile_sym(c.v, s, j0+1)
        // tm_run(c, j0+1) == tm_run(c_next, j0).
        assert(tm_run(tm, c, (j0 + 1) as nat) == tm_run(tm, c_next, j0));
    }
}

/// **The loop accumulator is the `seq_pow` digit block.** `pile_sym(v, s, k) == dpile(v, seq_pow([s], k))`
/// — re-expresses the machine-side run-of-`s`s in the digit-sequence language the Evaluation-side algebra
/// ([`crate::gap2_relnum_dds::lemma_dds_symbol_power`]) speaks, so an emitted `seq_pow([s], i)` block
/// composes with the explicit [`crate::gap2_fam_digits`] decomposition. Induction on `k`: `dpile` peels
/// the LOW copy off the front (`seq_pow([s],k)[0] == s`), `pile_sym` off the back — bridged by
/// [`lemma_pile_sym_shift`] (exactly how the loop lemma re-folds).
pub proof fn lemma_pile_sym_is_dpile(v: nat, s: nat, k: nat, m: nat)
    ensures
        pile_sym(v, s, k, m) == dpile(v, seq_pow(seq![s], k), m),
    decreases k,
{
    if k == 0 {
        assert(seq_pow(seq![s], 0) =~= Seq::<nat>::empty());
        // dpile(v, empty) == v == pile_sym(v, s, 0).
    } else {
        let k1 = (k - 1) as nat;
        let blk = seq_pow(seq![s], k);
        // seq_pow([s], k) == [s] + seq_pow([s], k-1).
        assert(blk == seq![s] + seq_pow(seq![s], k1));
        assert(blk.len() >= 1);
        assert(blk[0] == s);
        assert(blk.drop_first() =~= seq_pow(seq![s], k1));
        // dpile unfolds (blk nonempty): dpile(v, blk) == dpile(v*m+s, seq_pow([s], k1)).
        assert(dpile(v, blk, m) == dpile(v * m + s, seq_pow(seq![s], k1), m));
        lemma_pile_sym_is_dpile(v * m + s, s, k1, m);   // == pile_sym(v*m+s, s, k1)
        lemma_pile_sym_shift(v, s, k1, m);              // pile_sym(v*m+s, s, k1) == pile_sym(v, s, k1+1)
        assert((k1 + 1) as nat == k);
    }
}

} // verus!
