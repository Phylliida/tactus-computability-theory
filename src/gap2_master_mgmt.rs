//! # GAP-2 G2-F — master-management gadgets (`q_clean` / `load_master`), position-parametric.
//!
//! Between the two `fam_digits` emit phases the local master must change from `b+1` (the `uinv_digits(b)`
//! phase) to `a+1` (the `u_digits(a)` phase). Per the N+12 design resolution (`docs/gap2-input-loader-plan.md`,
//! "master-mgmt is LOCAL to `u`", confirmed w/ Danielle 2026-06-27) this is **WIPE-AND-LOAD**: `q_clean`
//! erases the old `b+1` master, then `load_master` rebuilds the `a+1` master from a **preserved high-tail
//! backup** (option (A): the backup sits ABOVE the master at a parametric offset `H ≥ g+M`, isolated from
//! the active workspace because every mark/deposit op is bounded by the gap `g ≥ M+2` and never reaches that
//! high — so the phase chain carries the tail through untouched). The backup placement (the offset `H` and
//! the eventual concrete layout) is Danielle's R-P/dovetail call; **everything here is parametric over it**,
//! so the layout decision plugs in only at the final `psc_act` instantiation — zero rip-out risk, the same
//! de-risking pattern as the exit-target-parametric emitter windows.
//!
//! ## This module so far — the WIPE primitive
//! [`lemma_wipe_ones_left`]: the `(q, 1, 0, q, L)` sweep, the master-erasing analog of
//! [`crate::tm_copy_refresh::lemma_unmark_fives_left`] (`5 → 1`). Reading a run of `len + 1` ones (the
//! scanned one plus `len` more in `u`), it writes a blank `0` over each and piles the blanks onto `v`,
//! landing on the tail `w` above the run. This is `q_clean`'s erase core; the round-trip framing
//! (seek-left over the gap → wipe → seek-right return) composes it with the existing
//! [`crate::tm_copy_refresh`] seek lemmas.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_emit::{pile_sym, lemma_pile_sym_shift};

verus! {

/// **Walk-LEFT over a run of ones ERASING each to a blank (the master-wipe sweep core).** The mirror of
/// [`crate::tm_copy_refresh::lemma_unmark_fives_left`] with the read symbol `5 → 1` and the written symbol
/// `1 → 0`: the quintuple `(q, 1, 0, q, L)` READS a one and WRITES a blank. From the run's lowest one with
/// `len` more ones then tail `w` above (`u == repunit(len) + m^len·w`, scanning a `1`), it fires `len + 1`
/// times — erasing each one and piling a blank `0` onto `v` — and lands the head on `w`'s low cell
/// (`a == w % m`, `u == w / m`), the erased run now `len + 1` blanks piled in `v` (`pile_sym(c.v, 0, ·)`).
/// The caller picks `w` so `w % m != 1` (the separator blank above the master, so the sweep stops). The
/// erase leg of `q_clean`. Induction on `len`; structurally identical to the proven `lemma_unmark_fives_left`.
pub proof fn lemma_wipe_ones_left(tm: Tm, c: TmConfig, q: nat, len: nat, w: nat, i1: int)
    requires
        tm_wf(tm),
        tm.n >= 1,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q, 1, 0, q, Dir::L),
        c.u == repunit_m(len, tm.m) + pow_nat(tm.m, len) * w,
        c.a == 1,
        c.q == q,
    ensures
        tm_run(tm, c, (len + 1) as nat)
            == (TmConfig { u: w / tm.m, v: pile_sym(c.v, 0, (len + 1) as nat, tm.m),
                a: w % tm.m, q: q }),
    decreases len,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m, and 1 ≤ n < m
    lemma_tm_step_picks(tm, c, i1);
    let c_next = TmConfig { u: c.u / m, v: c.v * m + 0, a: c.u % m, q: q };
    assert(tm_step(tm, c) == Some(c_next));
    if len == 0 {
        // u == repunit(0) + m^0·w == 0 + 1·w == w. One step erases the lone one, lands on w.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c.u == w) by(nonlinear_arith)
            requires c.u == repunit_m(0, m) + pow_nat(m, 0) * w, repunit_m(0, m) == 0,
                pow_nat(m, 0) == 1;
        assert(pile_sym(c.v, 0, 0, m) == c.v);
        assert(pile_sym(c.v, 0, 1, m) == pile_sym(c.v, 0, 0, m) * m + 0);
        assert(c_next == (TmConfig { u: w / m, v: pile_sym(c.v, 0, 1, m), a: w % m, q: q }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == repunit(len) + m^len·w == (repunit(len-1) + m^(len-1)·w)·m + 1.
        let x = repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        assert(repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1);   // repunit recurrence
        lemma_pow_nat_unfold(m, len);                                          // m^len == m·m^(len-1)
        assert(c.u == x * m + 1) by(nonlinear_arith)
            requires
                c.u == repunit_m(len, m) + pow_nat(m, len) * w,
                repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1,
                pow_nat(m, len) == m * pow_nat(m, (len - 1) as nat),
                x == repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        lemma_div_mod_step(x, m, 1);   // (x·m + 1)/m == x, %m == 1
        assert(c_next.u == x);
        assert(c_next.a == 1);
        lemma_wipe_ones_left(tm, c_next, q, (len - 1) as nat, w, i1);
        lemma_pile_sym_shift(c.v, 0, len, m);   // pile_sym(c.v·m+0, 0, len) == pile_sym(c.v, 0, len+1)
        assert(tm_run(tm, c, (len + 1) as nat) == tm_run(tm, c_next, len));
    }
}

} // verus!
