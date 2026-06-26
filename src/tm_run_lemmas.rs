//! # GAP-2-E brick B0 — `tm_run` composition lemmas
//!
//! Foundational run-algebra for the `tm.rs` Minsky TM, the analog of `machine.rs`/`conditional_halt.rs`
//! for register machines. Every register→TM gadget (B1–B6, see `docs/gap2-register-to-tm-plan.md`) is
//! a `tm_run(tm, c, fuel_gadget) == next_config` fact; we chain them with these lemmas and convert the
//! final `tm_run … == tm_origin()` into the `tm_halts_at(tm, c, tm_origin(), fuel)` the H₀ bridge
//! (`lemma_tm_h0_iff`) consumes.
//!
//! A nicety of `tm_run`'s "None stays" semantics (a terminal config maps to itself forever): the **split
//! lemma is unconditional** — no `!tm_halts_at` side condition like the register-machine `lemma_run_split`.
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use crate::tm::{Tm, TmConfig, tm_run, tm_step, tm_halts_at, tm_terminal};

verus! {

/// A terminal config runs to itself for any fuel (`tm_step` is `None`, so `tm_run` returns it directly).
pub proof fn lemma_tm_terminal_run_identity(tm: Tm, c: TmConfig, fuel: nat)
    requires
        tm_terminal(tm, c),
    ensures
        tm_run(tm, c, fuel) == c,
{
    // tm_terminal(c) ⟹ tm_step(c) is None; tm_run(c, fuel) returns c whether fuel==0 or >0.
    assert(tm_step(tm, c) is None);
}

/// **Run split (unconditional).** Running `f1 + f2` steps equals running `f1` then `f2` more from the
/// intermediate config. Holds with no side condition because `tm_run` idles on terminal configs.
pub proof fn lemma_tm_run_split(tm: Tm, c: TmConfig, f1: nat, f2: nat)
    ensures
        tm_run(tm, c, (f1 + f2) as nat) == tm_run(tm, tm_run(tm, c, f1), f2),
    decreases f1,
{
    if f1 == 0 {
        assert(tm_run(tm, c, f1) == c);
        assert((0 + f2) as nat == f2);
    } else {
        match tm_step(tm, c) {
            Some(next) => {
                // tm_run(c, f1+f2) == tm_run(next, (f1-1)+f2); tm_run(c, f1) == tm_run(next, f1-1).
                assert((f1 + f2 - 1) as nat == ((f1 - 1) as nat + f2) as nat);
                lemma_tm_run_split(tm, next, (f1 - 1) as nat, f2);
            },
            None => {
                // c terminal: both sides collapse to c.
                lemma_tm_terminal_run_identity(tm, c, (f1 + f2) as nat);
                lemma_tm_terminal_run_identity(tm, c, f1);
                lemma_tm_terminal_run_identity(tm, c, f2);
            },
        }
    }
}

/// **`tm_run` reaches a terminal target ⟹ `tm_halts_at`.** The forward bridge: chain the gadgets to
/// land `tm_run(tm, c, f) == target` (typically `tm_origin()`), prove `target` terminal, conclude the
/// TM halts at it. Induction on `f` following the step trace.
pub proof fn lemma_tm_run_reaches_halts_at(tm: Tm, c: TmConfig, target: TmConfig, f: nat)
    requires
        tm_run(tm, c, f) == target,
        tm_terminal(tm, target),
    ensures
        tm_halts_at(tm, c, target, f),
    decreases f,
{
    if c == target {
        // first branch of tm_halts_at: c == target && tm_terminal(target).
    } else {
        // c ≠ target ⟹ c is not terminal (a terminal c would give tm_run(c,f) == c ≠ target),
        // and f > 0 (f == 0 gives tm_run(c,0) == c ≠ target).
        if f == 0 {
            assert(tm_run(tm, c, 0) == c);
            assert(false);
        }
        match tm_step(tm, c) {
            Some(next) => {
                // tm_run(c, f) == tm_run(next, f-1) == target.
                lemma_tm_run_reaches_halts_at(tm, next, target, (f - 1) as nat);
            },
            None => {
                // c terminal ⟹ tm_run(c, f) == c (f > 0, None stays) == target, contra c ≠ target.
                lemma_tm_terminal_run_identity(tm, c, f);
                assert(false);
            },
        }
    }
}

/// **`tm_halts_at` ⟹ `tm_run` lands on the (terminal) target.** The converse bridge, for the backward
/// direction (TM reaches origin ⟹ the simulated machine halted).
pub proof fn lemma_tm_halts_at_run(tm: Tm, c: TmConfig, target: TmConfig, f: nat)
    requires
        tm_halts_at(tm, c, target, f),
    ensures
        tm_run(tm, c, f) == target,
        tm_terminal(tm, target),
    decreases f,
{
    if c == target && tm_terminal(tm, target) {
        lemma_tm_terminal_run_identity(tm, c, f);
    } else {
        // not the first branch ⟹ f > 0 (else tm_halts_at is false) and tm_step(c) is Some.
        assert(f > 0);
        match tm_step(tm, c) {
            Some(next) => {
                lemma_tm_halts_at_run(tm, next, target, (f - 1) as nat);
            },
            None => {
                assert(false);
            },
        }
    }
}

/// **`tm_halts_at` is monotone in fuel.** Once the TM reaches the target within `f1`, any larger budget
/// also witnesses it. (Lets gadget-chains use a single generous fuel.)
pub proof fn lemma_tm_halts_at_monotone(tm: Tm, c: TmConfig, target: TmConfig, f1: nat, f2: nat)
    requires
        tm_halts_at(tm, c, target, f1),
        f2 >= f1,
    ensures
        tm_halts_at(tm, c, target, f2),
    decreases f1,
{
    if c == target && tm_terminal(tm, target) {
        // first branch holds at any fuel.
    } else {
        assert(f1 > 0);
        match tm_step(tm, c) {
            Some(next) => {
                lemma_tm_halts_at_monotone(tm, next, target, (f1 - 1) as nat, (f2 - 1) as nat);
            },
            None => {
                assert(false);
            },
        }
    }
}

/// **Existence-level `tm_halts_at` is preserved by prepending a finite run.** If the TM reaches a
/// terminal `target` from the post-prefix config `tm_run(tm, c, k)`, then it reaches it from `c`. The
/// workhorse for "simulate `k` steps, then the tail halts": glue the prefix fuel `k` onto the tail fuel.
pub proof fn lemma_tm_halts_at_prepend(tm: Tm, c: TmConfig, target: TmConfig, k: nat, ftail: nat)
    requires
        tm_halts_at(tm, tm_run(tm, c, k), target, ftail),
    ensures
        tm_halts_at(tm, c, target, (k + ftail) as nat),
    decreases k,
{
    if k == 0 {
        assert(tm_run(tm, c, 0) == c);
    } else {
        match tm_step(tm, c) {
            Some(next) => {
                // tm_run(c, k) == tm_run(next, k-1).
                lemma_tm_halts_at_prepend(tm, next, target, (k - 1) as nat, ftail);
                // tm_halts_at(next, target, (k-1)+ftail) ⟹ tm_halts_at(c, target, k+ftail) via the
                // Some(next) branch (c is not terminal here).
                assert((k + ftail - 1) as nat == ((k - 1) as nat + ftail) as nat);
            },
            None => {
                // c terminal: tm_run(c, k) == c, so the hypothesis is tm_halts_at(c, target, ftail);
                // a terminal c that halts at target must be target, and target stays for any fuel.
                lemma_tm_terminal_run_identity(tm, c, k);
                lemma_tm_halts_at_monotone(tm, c, target, ftail, (k + ftail) as nat);
            },
        }
    }
}

} // verus!
