//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — copy-refresh foundation (seek walks).
//!
//! After a per-block loop ([`crate::tm_block_loop`]) consumes the active `temp` counter, the left tape is
//! `u == dec_u(0, m^temp·w) == m^temp·w` — the master content `w` has floated UP by `temp` cells, leaving a
//! growing blank gap between the home pivot and the master. To emit the NEXT power-block of the same phase
//! (same exponent) the machine must rebuild a fresh `temp` counter from the PRESERVED master (a copy-refresh,
//! plan §5 / the n=5 marker decision). The first ingredient is locating the master across that blank gap.
//!
//! This file builds the **seek** walks — the blank-gap analogs of [`crate::tm_dwalk`] (which walk over
//! nonzero digit blocks and stop at a blank); here the head walks over a run of blanks and stops at the
//! first NONZERO cell (the master's low digit):
//!   - [`lemma_seek_left_blanks`]: walk-LEFT over a blank gap to the master (`(q, 0, 0, q, L)`), and
//!   - [`lemma_seek_right_blanks`]: walk-RIGHT over a blank gap back to the pivot (`(q, 0, 0, q, R)`),
//!     the un-seek mirror.
//! Both are symbol-agnostic in the piled content (`v` / `u` round-trips through the seek + un-seek).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};

verus! {

/// **Seek-left over a blank gap to the master.** From `{u: m^g·r, a: 0, q: q_seek}` with `r % m != 0`
/// (the target's low digit is nonzero — the master), the loop quintuple `(q_seek, 0, 0, q_seek, L)` fires
/// `g + 1` times: it peels the initial scanned blank (the pivot) plus the `g` gap blanks of `u`, piling all
/// `g + 1` blanks onto `v` (multiplying it by `m^(g+1)`), and lands the head on the master's low digit
/// `{u: r/m, v: c.v · m^(g+1), a: r % m, q: q_seek}` — where `r % m != 0` makes the loop quintuple stop
/// firing (a different `(q_seek, s, …)` quintuple then takes over). The blank-gap analog of
/// [`crate::tm_dwalk::lemma_dwalk_left`]; induction on `g`.
pub proof fn lemma_seek_left_blanks(tm: Tm, c: TmConfig, q_seek: nat, g: nat, r: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_seek, 0, 0, q_seek, Dir::L),
        c.u == pow_nat(tm.m, g) * r,
        r % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tm_run(tm, c, (g + 1) as nat)
            == (TmConfig { u: r / tm.m, v: c.v * pow_nat(tm.m, (g + 1) as nat), a: r % tm.m, q: q_seek }),
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches (q == q_seek, a == 0) and fires (L-move, a2 == 0).
    assert(quint_matches(tm.quints[i0], c));
    lemma_tm_step_picks(tm, c, i0);
    let c_next = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // L-move, a2 == 0: u' = c.u/m, v' = c.v·m + 0, a' = c.u%m.
    assert(c_next.u == c.u / m);
    assert(c_next.v == c.v * m + 0);
    assert(c_next.a == c.u % m);
    assert(c_next.q == q_seek);
    if g == 0 {
        // u == m^0·r == r; a' == r%m ≠ 0 (master), u' == r/m. Done in one step.
        assert(pow_nat(m, 0) == 1);
        assert(1nat * r == r) by(nonlinear_arith);
        assert(c.u == r);
        assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
        assert(c.v * m + 0 == c.v * pow_nat(m, 1)) by(nonlinear_arith)
            requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: r / m, v: c.v * pow_nat(m, (g + 1) as nat), a: r % m,
            q: q_seek }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == m^g·r == m·(m^(g-1)·r); a' == 0 (still in the gap), u' == m^(g-1)·r.
        let r1 = pow_nat(m, (g - 1) as nat) * r;
        lemma_pow_nat_unfold(m, g);   // m^g == m·m^(g-1)
        assert(c.u == m * r1) by(nonlinear_arith)
            requires c.u == pow_nat(m, g) * r, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                r1 == pow_nat(m, (g - 1) as nat) * r;
        assert(m * r1 == r1 * m) by(nonlinear_arith);
        lemma_div_mod_step(r1, m, 0);   // (r1·m + 0)/m == r1, %m == 0
        assert(c_next.u == r1);
        assert(c_next.a == 0);
        // recurse on g-1.
        lemma_seek_left_blanks(tm, c_next, q_seek, (g - 1) as nat, r, i0);
        // IH: tm_run(c_next, g) == (r/m, c_next.v · m^g, r%m, q_seek); chain to g+1.
        lemma_pow_nat_unfold(m, (g + 1) as nat);   // m^(g+1) == m·m^g
        assert(c_next.v * pow_nat(m, g) == c.v * pow_nat(m, (g + 1) as nat)) by(nonlinear_arith)
            requires c_next.v == c.v * m + 0, pow_nat(m, (g + 1) as nat) == m * pow_nat(m, g);
        assert(tm_run(tm, c, (g + 1) as nat) == tm_run(tm, c_next, g));
    }
}

/// **Seek-right over a blank gap (the un-seek mirror of [`lemma_seek_left_blanks`]).** The exact `u ↔ v`,
/// `L ↔ R` swap: from `{v: m^g·rv, a: 0, q: q_seek}` with `rv % m != 0` (the target's low digit on the
/// right is nonzero), the loop quintuple `(q_seek, 0, 0, q_seek, R)` fires `g + 1` times — peeling the
/// initial scanned blank plus the `g` gap blanks of `v`, piling all `g + 1` onto `u` (multiplying it by
/// `m^(g+1)`) — and lands the head on the target's low digit `{u: c.u · m^(g+1), v: rv/m, a: rv % m,
/// q: q_seek}`. Used to walk the head back right toward home after the marked copy. Induction on `g`.
pub proof fn lemma_seek_right_blanks(tm: Tm, c: TmConfig, q_seek: nat, g: nat, rv: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_seek, 0, 0, q_seek, Dir::R),
        c.v == pow_nat(tm.m, g) * rv,
        rv % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tm_run(tm, c, (g + 1) as nat)
            == (TmConfig { u: c.u * pow_nat(tm.m, (g + 1) as nat), v: rv / tm.m, a: rv % tm.m,
                q: q_seek }),
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    assert(quint_matches(tm.quints[i0], c));
    lemma_tm_step_picks(tm, c, i0);
    let c_next = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // R-move, a2 == 0: u' = c.u·m + 0, v' = c.v/m, a' = c.v%m.
    assert(c_next.u == c.u * m + 0);
    assert(c_next.v == c.v / m);
    assert(c_next.a == c.v % m);
    assert(c_next.q == q_seek);
    if g == 0 {
        assert(pow_nat(m, 0) == 1);
        assert(1nat * rv == rv) by(nonlinear_arith);
        assert(c.v == rv);
        assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
        assert(c.u * m + 0 == c.u * pow_nat(m, 1)) by(nonlinear_arith)
            requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: c.u * pow_nat(m, (g + 1) as nat), v: rv / m, a: rv % m,
            q: q_seek }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        let rv1 = pow_nat(m, (g - 1) as nat) * rv;
        lemma_pow_nat_unfold(m, g);   // m^g == m·m^(g-1)
        assert(c.v == m * rv1) by(nonlinear_arith)
            requires c.v == pow_nat(m, g) * rv, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                rv1 == pow_nat(m, (g - 1) as nat) * rv;
        assert(m * rv1 == rv1 * m) by(nonlinear_arith);
        lemma_div_mod_step(rv1, m, 0);   // (rv1·m + 0)/m == rv1, %m == 0
        assert(c_next.v == rv1);
        assert(c_next.a == 0);
        lemma_seek_right_blanks(tm, c_next, q_seek, (g - 1) as nat, rv, i0);
        lemma_pow_nat_unfold(m, (g + 1) as nat);   // m^(g+1) == m·m^g
        assert(c_next.u * pow_nat(m, g) == c.u * pow_nat(m, (g + 1) as nat)) by(nonlinear_arith)
            requires c_next.u == c.u * m + 0, pow_nat(m, (g + 1) as nat) == m * pow_nat(m, g);
        assert(tm_run(tm, c, (g + 1) as nat) == tm_run(tm, c_next, g));
    }
}

} // verus!
