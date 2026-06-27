//! # GAP-2 G2-F — the input loader / init setup (item 4): laying the initial double-repunit `u`.
//!
//! Before the `fam_digits` emitter runs (`gap2_emit_seq::lemma_uinv_phase`), the local tape must hold the
//! phase-1 start config
//!   `{ u: m^g·R(b+1) + m^(g+b+2)·R(a+1), v: 0, a: 0, q: entry5(pc) }`
//! — the master `R(b+1)` floated up to gap `g`, a separator blank, then the high-tail backup `R(a+1)` (the
//! `add_hi` tail the high-tail lift carries through, `lemma_uinv_phase_tail`). Reading `u` low→high this is
//! `m^g · D` with `D = R(b+1) + m^(b+2)·R(a+1)` — **exactly the natural blank-separated two-counter layout**
//! (`b+1` ones, one blank, `a+1` ones). So item 4 is: take the two-counter block `D` from the dovetail and
//! **float it up by a gap `g`** (the phase constraints force `g ≥ max(b+3, a−b+1)`; we use `g = a+b+3`, a
//! counter concatenation, per the Danielle/port-8051 design lock 2026-06-27).
//!
//! ## This module — the SHIFT-UP primitive (the no-emit float-up)
//! [`lemma_shift_right_ones`]: the `(q, 1, 0, q, R)` sweep — the **rightward mirror** of
//! [`crate::gap2_master_mgmt::lemma_wipe_ones_left`] (`(q,1,0,q,L)`). It READS a one and WRITES a blank while
//! moving RIGHT, so each step does `u' = m·u` (the written `0` becomes `u`'s new low digit) and pops one off
//! the gap-counter in `v`. Over a gap-counter of `len+1` ones (`1` scanned + `len` in `v`) bounded above by a
//! separator `rv` (`rv % m ≠ 1`), it floats `u` up by `m^(len+1)` — i.e. inserts `len+1` blanks at `u`'s low
//! end — and lands the head on the separator. This is precisely block_loop's "consume the counter, the
//! master's absolute position is preserved" mechanic with the emit (surge) stripped: a pure *transporter*.
//! With `rv = 0` (nothing above the gap-counter) the head lands on a blank (`a == 0`, `v == 0`), giving the
//! emitter's `{ u: m^g·D, v: 0, a: 0 }` start shape directly.
//!
//! `docs/gap2-input-loader-plan.md` item 4. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_copy_refresh::{copy_u, lemma_copy_u_start, lemma_pow_nat_add};
use crate::gap2_tail_lift::add_hi;

verus! {

/// **Walk-RIGHT over a run of ones ERASING each to a blank, floating `u` up (the no-emit float-up core).**
/// The mirror of [`crate::gap2_master_mgmt::lemma_wipe_ones_left`] with the move direction `L → R`: the
/// quintuple `(q, 1, 0, q, R)` READS a one and WRITES a blank, then moves right. An `R`-step with write `0`
/// sends `u' = u·m + 0 = m·u` (the written blank is `u`'s new low digit), `v' = v/m`, `a' = v % m` — so each
/// fire shifts `u` up by one place and pops a one off the gap-counter packed in `v`. From the run's lowest
/// one (scanned, `c.a == 1`) with `len` more ones then a separator `rv` above in `v`
/// (`c.v == repunit(len) + m^len·rv`, `rv % m ≠ 1` so the sweep stops), it fires `len + 1` times and lands
/// the head on `rv`'s low cell (`a == rv % m`, `v == rv / m`), with `u` floated up to `c.u · m^(len+1)`.
/// The transporter half of item 4: with `c.u = D` and `rv = 0` the result is `{ u: m^(len+1)·D, v: 0, a: 0 }`.
/// Induction on `len`; structurally identical to the proven `lemma_wipe_ones_left`.
pub proof fn lemma_shift_right_ones(tm: Tm, c: TmConfig, q: nat, len: nat, rv: nat, i1: int)
    requires
        tm_wf(tm),
        tm.n >= 1,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q, 1, 0, q, Dir::R),
        c.v == repunit_m(len, tm.m) + pow_nat(tm.m, len) * rv,
        rv % tm.m != 1,
        c.a == 1,
        c.q == q,
    ensures
        tm_run(tm, c, (len + 1) as nat)
            == (TmConfig { u: c.u * pow_nat(tm.m, (len + 1) as nat), v: rv / tm.m,
                a: rv % tm.m, q: q }),
    decreases len,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m, and 1 ≤ n < m
    lemma_tm_step_picks(tm, c, i1);
    // R-move, write 0: u' = c.u·m + 0, v' = c.v/m, a' = c.v%m.
    let c_next = TmConfig { u: c.u * m + 0, v: c.v / m, a: c.v % m, q: q };
    assert(tm_step(tm, c) == Some(c_next));
    if len == 0 {
        // v == repunit(0) + m^0·rv == 0 + 1·rv == rv. One step pops rv's low cell.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c.v == rv) by(nonlinear_arith)
            requires c.v == repunit_m(0, m) + pow_nat(m, 0) * rv, repunit_m(0, m) == 0,
                pow_nat(m, 0) == 1;
        assert(pow_nat(m, 1) == m) by {
            lemma_pow_nat_unfold(m, 1);
            assert(pow_nat(m, 0) == 1);
            assert(m * pow_nat(m, 0) == m) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
        }
        assert(c.u * m + 0 == c.u * pow_nat(m, 1)) by(nonlinear_arith) requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: c.u * pow_nat(m, (len + 1) as nat), v: rv / m, a: rv % m,
            q: q }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // v == repunit(len) + m^len·rv == (repunit(len-1) + m^(len-1)·rv)·m + 1.
        let x = repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * rv;
        assert(repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1);   // repunit recurrence
        lemma_pow_nat_unfold(m, len);                                          // m^len == m·m^(len-1)
        assert(c.v == x * m + 1) by(nonlinear_arith)
            requires
                c.v == repunit_m(len, m) + pow_nat(m, len) * rv,
                repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1,
                pow_nat(m, len) == m * pow_nat(m, (len - 1) as nat),
                x == repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * rv;
        lemma_div_mod_step(x, m, 1);   // (x·m + 1)/m == x, %m == 1
        assert(c_next.v == x);
        assert(c_next.a == 1);
        lemma_shift_right_ones(tm, c_next, q, (len - 1) as nat, rv, i1);
        // u: c_next.u · m^len == (c.u·m) · m^len == c.u · m^(len+1).
        lemma_pow_nat_unfold(m, (len + 1) as nat);   // m^(len+1) == m·m^len
        assert(c_next.u * pow_nat(m, len) == c.u * pow_nat(m, (len + 1) as nat)) by(nonlinear_arith)
            requires c_next.u == c.u * m + 0, pow_nat(m, (len + 1) as nat) == m * pow_nat(m, len);
        assert(tm_run(tm, c, (len + 1) as nat) == tm_run(tm, c_next, len));
    }
}

/// **The initial two-counter block `D = R(b+1) + m^(b+2)·R(a+1)`** — the natural blank-separated dovetail
/// layout (`b+1` ones, one separator blank, `a+1` ones), read low→high from the home pivot. Floating it up
/// by a gap `g` yields the phase-1 emitter start (`m^g·D == copy_u(0,b+1,g) + m^(g+b+2)·R(a+1)`,
/// [`lemma_init_double_repunit_value`]).
pub open spec fn init_block(a: nat, b: nat, m: nat) -> nat {
    repunit_m((b + 1) as nat, m) + pow_nat(m, (b + 2) as nat) * repunit_m((a + 1) as nat, m)
}

/// **`m^g · D` is the phase-1 emitter start tape.** `D = init_block(a,b)`, so floating it up by the gap `g`
/// gives `copy_u(0, b+1, g) + m^(g+b+2)·R(a+1)` — exactly the `u` field of the `add_hi`-tailed config that
/// [`crate::gap2_emit_seq::lemma_uinv_phase_tail`] consumes (master `R(b+1)` at gap `g`, separator blank,
/// high-tail backup `R(a+1)` at gap `g+b+2`). Pure place-value arithmetic: `copy_u(0,b+1,g) = m^g·R(b+1)`
/// ([`lemma_copy_u_start`]) and `m^g·m^(b+2) = m^(g+b+2)` ([`lemma_pow_nat_add`]).
pub proof fn lemma_init_double_repunit_value(a: nat, b: nat, g: nat, m: nat)
    ensures
        pow_nat(m, g) * init_block(a, b, m)
            == (copy_u(0, (b + 1) as nat, g, m)
                + pow_nat(m, (g + b + 2) as nat) * repunit_m((a + 1) as nat, m)) as nat,
{
    lemma_copy_u_start((b + 1) as nat, g, m);            // copy_u(0,b+1,g) == m^g·R(b+1)
    lemma_pow_nat_add(m, g, (b + 2) as nat);             // m^(g+(b+2)) == m^g·m^(b+2)
    assert((g + (b + 2)) as nat == (g + b + 2) as nat);
    // m^g·(R(b+1) + m^(b+2)·R(a+1)) = m^g·R(b+1) + (m^g·m^(b+2))·R(a+1).
    assert(pow_nat(m, g) * init_block(a, b, m)
        == copy_u(0, (b + 1) as nat, g, m)
            + pow_nat(m, (g + b + 2) as nat) * repunit_m((a + 1) as nat, m)) by(nonlinear_arith)
        requires
            init_block(a, b, m)
                == repunit_m((b + 1) as nat, m)
                    + pow_nat(m, (b + 2) as nat) * repunit_m((a + 1) as nat, m),
            copy_u(0, (b + 1) as nat, g, m) == pow_nat(m, g) * repunit_m((b + 1) as nat, m),
            pow_nat(m, (g + b + 2) as nat) == pow_nat(m, g) * pow_nat(m, (b + 2) as nat);
}

/// **Item 4 (local frame): lay the initial double-repunit `u` by floating `D` up the gap.** From the
/// pre-shift layout `{ u: D, v: R(g−1) [the gap-counter above the scanned one], a: 1, q }` — the dovetail
/// block `D` in `u`, a gap-counter of `g` ones at the head (`1` scanned + `g−1` in `v`) bounded by the empty
/// output region (`rv = 0`) — running the `(q,1,0,q,R)` shift-up `g` steps consumes the gap-counter and
/// floats `D` up by `m^g`, landing on the home pivot in the **exact** start config
/// [`crate::gap2_emit_seq::lemma_uinv_phase_tail`] consumes:
///   `add_hi({ u: copy_u(0,b+1,g), v: 0, a: 0, q }, g+b+2, R(a+1), m)`.
/// `q` splices to `entry5(pc)` at the concrete `psc_act` instantiation. The α-block (parked to the right of
/// the output) is a separate `v`-side high tail, handled like the `u`-side `add_hi` lift — out of scope here.
pub proof fn lemma_lay_init(tm: Tm, a: nat, b: nat, g: nat, q: nat, i1: int)
    requires
        tm_wf(tm),
        tm.n >= 1,
        g >= 1,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q, 1, 0, q, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: init_block(a, b, tm.m), v: repunit_m((g - 1) as nat, tm.m), a: 1, q: q },
            g)
            == add_hi(
                TmConfig { u: copy_u(0, (b + 1) as nat, g, tm.m), v: 0, a: 0, q: q },
                (g + b + 2) as nat, repunit_m((a + 1) as nat, tm.m), tm.m),
{
    let m = tm.m;
    reveal(tm_wf);
    assert(m > 1);
    let c = TmConfig { u: init_block(a, b, m), v: repunit_m((g - 1) as nat, m), a: 1, q: q };

    // The gap-counter `v == R(g−1) == R(g−1) + m^(g−1)·0`, separator `rv = 0` (rv % m == 0 ≠ 1).
    assert(pow_nat(m, (g - 1) as nat) * 0 == 0) by(nonlinear_arith);
    assert(c.v == repunit_m((g - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * 0);
    assert((0nat) % m == 0) by(nonlinear_arith) requires m > 1;

    lemma_shift_right_ones(tm, c, q, (g - 1) as nat, 0, i1);
    // tm_run(c, (g−1)+1) == { u: D·m^g, v: 0/m, a: 0%m, q }; (g−1)+1 == g, 0/m == 0, 0%m == 0.
    assert(((g - 1) + 1) as nat == g);
    assert((0nat) / m == 0) by(nonlinear_arith) requires m > 1;

    // D·m^g == m^g·D == copy_u(0,b+1,g) + m^(g+b+2)·R(a+1) == add_hi(...).u.
    lemma_init_double_repunit_value(a, b, g, m);
    assert(init_block(a, b, m) * pow_nat(m, g) == pow_nat(m, g) * init_block(a, b, m))
        by(nonlinear_arith);
}

} // verus!
