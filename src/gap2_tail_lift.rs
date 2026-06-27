//! # GAP-2 G2-F — the high-tail lift (`lemma_uinv_phase_tail` substrate)
//!
//! The master-management plan (`docs/gap2-input-loader-plan.md` §N+13.1) needs the phase-1 emission
//! (`lemma_uinv_phase`) to run with the `a+1` backup preserved as a high tail `m^H·T` on the left tape
//! `u`, sitting one separator-blank above the master (`H = g' = g+b+2`). Re-threading that tail through
//! `tm_copy_refresh`'s 6500-line value arithmetic would be a trap; instead this module lifts ANY run as a
//! **black box**.
//!
//! **The decisive observation.** A config is `(u, v, a, q)` with the scanned symbol `a` and state `q` as
//! *separate fields* — they are NOT computed from `u`. Adding a high tail `add_hi(c) = {u: c.u + m^H·T,
//! ..c}` changes only `u`, so `(q, a)` are untouched and the **same quintuple fires** at every step,
//! regardless of the tail. The tail only perturbs the step *result*:
//!   - **R-move** `u' = u·m + a2`: with tail `(u + m^H·T)·m + a2 = u·m + a2 + m^(H+1)·T` — the tail rides
//!     up to offset `H+1`. *Unconditional.*
//!   - **L-move** `u' = u/m`, `a' = u%m`: with tail `(u + m^H·T)/m = u/m + m^(H-1)·T` and `(u + m^H·T)%m
//!     = u%m` *iff `H ≥ 1`* (else the tail's low digit corrupts the popped symbol). Tail rides down to
//!     `H-1`.
//!
//! So the ONLY safety condition is **`H ≥ 1` before every L-move** — a control-flow property
//! ([`tail_safe`]) tracking the offset `H ± 1` per step ([`tail_end_h`]). The lift
//! ([`lemma_run_tail`]) then says `tm_run(add_hi(c), fuel) == add_hi(tm_run(c, fuel))` with the offset
//! advanced. No value arithmetic of the underlying gadget is touched.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{
    Tm, TmConfig, tm_run, tm_terminal, apply_quint, matching_index, quint_matches,
    tm_wf, lemma_matching_index_ok,
};
use crate::tm_gadget::lemma_tm_step_picks;
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use verus_group_theory::word_numbering::lemma_div_mod_step;

verus! {

/// Add a high tail `m^h·t` to the left tape `u`, leaving the scanned symbol `a`, state `q`, and right
/// tape `v` untouched. The whole lift is about how runs commute with this map.
pub open spec fn add_hi(c: TmConfig, h: nat, t: nat, m: nat) -> TmConfig {
    TmConfig { u: (c.u + pow_nat(m, h) * t) as nat, v: c.v, a: c.a, q: c.q }
}

/// **The tail is never popped.** Running `fuel` steps from `c` with the tail at offset `h`: each R-move
/// advances the offset to `h+1` (unconditional), each L-move requires `h ≥ 1` (else the tail's low digit
/// would corrupt the popped scanned symbol) and advances to `h-1`. Mirrors `tm_run`'s recursion exactly,
/// so it is dischargeable along the same trace.
pub open spec fn tail_safe(tm: Tm, c: TmConfig, fuel: nat, h: nat) -> bool
    decreases fuel,
{
    if fuel == 0 || tm_terminal(tm, c) {
        true
    } else {
        let qt = tm.quints[matching_index(tm, c)];
        let next = apply_quint(qt, c, tm.m);
        match qt.dir {
            Dir::R => tail_safe(tm, next, (fuel - 1) as nat, (h + 1) as nat),
            Dir::L => h >= 1 && tail_safe(tm, next, (fuel - 1) as nat, (h - 1) as nat),
        }
    }
}

/// **The tail's offset after the run.** `+1` per R-move, `-1` per L-move; idles on terminal. The offset
/// at which [`lemma_run_tail`] re-deposits the tail.
pub open spec fn tail_end_h(tm: Tm, c: TmConfig, fuel: nat, h: nat) -> nat
    decreases fuel,
{
    if fuel == 0 || tm_terminal(tm, c) {
        h
    } else {
        let qt = tm.quints[matching_index(tm, c)];
        let next = apply_quint(qt, c, tm.m);
        match qt.dir {
            Dir::R => tail_end_h(tm, next, (fuel - 1) as nat, (h + 1) as nat),
            Dir::L => tail_end_h(tm, next, (fuel - 1) as nat, (h - 1) as nat),
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// per-step arithmetic: apply_quint commutes with add_hi
// ────────────────────────────────────────────────────────────────────────────

/// **One step commutes with the tail** (R-move, unconditional). `apply_quint` of an R-quint on the
/// tailed config equals the tailed result with the offset bumped to `h+1`.
proof fn lemma_apply_add_hi_r(qt: crate::tm::Quintuple, c: TmConfig, h: nat, t: nat, m: nat)
    requires
        qt.dir == Dir::R,
    ensures
        apply_quint(qt, add_hi(c, h, t, m), m) == add_hi(apply_quint(qt, c, m), (h + 1) as nat, t, m),
{
    let ch = add_hi(c, h, t, m);
    // R: u' = u·m + a2, v' = v/m, a' = v%m, q' = q2. v,a depend only on c.v (shared) ⟹ equal.
    lemma_pow_nat_unfold(m, (h + 1) as nat);   // m^(h+1) == m·m^h
    // (c.u + m^h·t)·m + a2 == c.u·m + a2 + m^(h+1)·t
    assert((ch.u * m + qt.a2) as nat == (c.u * m + qt.a2 + pow_nat(m, (h + 1) as nat) * t) as nat)
        by(nonlinear_arith)
        requires
            ch.u == (c.u + pow_nat(m, h) * t) as nat,
            pow_nat(m, (h + 1) as nat) == m * pow_nat(m, h);
}

/// **One step commutes with the tail** (L-move, needs `h ≥ 1`). `apply_quint` of an L-quint on the
/// tailed config equals the tailed result with the offset dropped to `h-1`; crucially the popped scanned
/// symbol `a' = u%m` is unaffected because `m^h·t ≡ 0 (mod m)` for `h ≥ 1`.
proof fn lemma_apply_add_hi_l(qt: crate::tm::Quintuple, c: TmConfig, h: nat, t: nat, m: nat)
    requires
        qt.dir == Dir::L,
        h >= 1,
        m > 0,
    ensures
        apply_quint(qt, add_hi(c, h, t, m), m) == add_hi(apply_quint(qt, c, m), (h - 1) as nat, t, m),
{
    let ch = add_hi(c, h, t, m);
    let x = pow_nat(m, (h - 1) as nat) * t;
    lemma_pow_nat_unfold(m, h);   // m^h == m·m^(h-1)
    // m^h·t == m·x
    assert((pow_nat(m, h) * t) as nat == (m * x) as nat) by(nonlinear_arith)
        requires pow_nat(m, h) == m * pow_nat(m, (h - 1) as nat), x == pow_nat(m, (h - 1) as nat) * t;
    // ch.u == c.u + m·x; split c.u == (c.u/m)·m + c.u%m, so ch.u == (c.u/m + x)·m + c.u%m.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c.u as int, m as int);
    assert(c.u == (c.u / m) * m + c.u % m);
    assert(ch.u == (c.u / m + x) * m + c.u % m) by(nonlinear_arith)
        requires ch.u == (c.u + m * x) as nat, c.u == (c.u / m) * m + c.u % m;
    // hence ch.u / m == c.u/m + x  and  ch.u % m == c.u%m  (0 ≤ c.u%m < m).
    assert(c.u % m < m) by(nonlinear_arith) requires m > 0;
    lemma_div_mod_step((c.u / m + x) as nat, m, (c.u % m) as nat);
    assert(ch.u / m == (c.u / m + x) as nat);
    assert(ch.u % m == c.u % m);
}

// ────────────────────────────────────────────────────────────────────────────
// the black-box lift
// ────────────────────────────────────────────────────────────────────────────

/// **The high-tail lift.** If a run of `fuel` steps from `c` never pops the tail ([`tail_safe`]), then
/// running the SAME machine from the tailed config equals the tailed run-result, with the tail
/// re-deposited at the advanced offset [`tail_end_h`]:
///   `tm_run(add_hi(c, h, t)) == add_hi(tm_run(c), tail_end_h(c, fuel, h), t)`.
/// Black box: the underlying gadget's value arithmetic is never touched — only `(q, a)` (which `add_hi`
/// preserves) decide control flow.
pub proof fn lemma_run_tail(tm: Tm, c: TmConfig, fuel: nat, h: nat, t: nat)
    requires
        tm_wf(tm),
        tail_safe(tm, c, fuel, h),
    ensures
        tm_run(tm, add_hi(c, h, t, tm.m), fuel)
            == add_hi(tm_run(tm, c, fuel), tail_end_h(tm, c, fuel, h), t, tm.m),
    decreases fuel,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 0);
    let ch = add_hi(c, h, t, m);
    if fuel == 0 {
        // both runs are the identity; tail_end_h == h.
        assert(tm_run(tm, c, 0) == c);
        assert(tm_run(tm, ch, 0) == ch);
    } else if tm_terminal(tm, c) {
        // ch has the same (q, a) ⟹ matches exactly the same quints ⟹ also terminal ⟹ both idle.
        assert(forall|i: int| #![trigger tm.quints[i]]
            quint_matches(tm.quints[i], ch) == quint_matches(tm.quints[i], c));
        assert(tm_terminal(tm, ch));
        assert(tm_run(tm, c, fuel) == c);
        assert(tm_run(tm, ch, fuel) == ch);
    } else {
        let mi = matching_index(tm, c);
        lemma_matching_index_ok(tm, c);          // mi valid, quints[mi] matches c
        let qt = tm.quints[mi];
        lemma_tm_step_picks(tm, c, mi);          // tm_step(c) == Some(apply_quint(qt, c, m))
        let next = apply_quint(qt, c, m);
        // ch matches the SAME quint (shared q, a).
        assert(quint_matches(qt, ch));
        lemma_tm_step_picks(tm, ch, mi);         // tm_step(ch) == Some(apply_quint(qt, ch, m))
        let chnext = apply_quint(qt, ch, m);
        match qt.dir {
            Dir::R => {
                lemma_apply_add_hi_r(qt, c, h, t, m);
                assert(chnext == add_hi(next, (h + 1) as nat, t, m));
                lemma_run_tail(tm, next, (fuel - 1) as nat, (h + 1) as nat, t);
                // tm_run(ch, fuel) == tm_run(chnext, fuel-1) == tm_run(add_hi(next, h+1), fuel-1)
                //   == add_hi(tm_run(next, fuel-1), tail_end_h(next, fuel-1, h+1), t);
                // tm_run(c, fuel) == tm_run(next, fuel-1); tail_end_h(c,fuel,h) unfolds to next/h+1.
            },
            Dir::L => {
                // tail_safe(c, fuel, h) ⟹ h >= 1 (L branch).
                assert(h >= 1);
                lemma_apply_add_hi_l(qt, c, h, t, m);
                assert(chnext == add_hi(next, (h - 1) as nat, t, m));
                lemma_run_tail(tm, next, (fuel - 1) as nat, (h - 1) as nat, t);
            },
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// composition: tail_safe / tail_end_h split across a run boundary
// ────────────────────────────────────────────────────────────────────────────

/// **Tail-safety composes over a split.** A run is tail-safe for `f1 + f2` steps iff it is tail-safe for
/// the first `f1` steps and the continuation (at the advanced offset) is tail-safe for the next `f2`;
/// and the final offset chains. Mirrors [`crate::tm_run_lemmas::lemma_tm_run_split`] for the offset
/// bookkeeping; induction on `f1`. This is what lets the discharge work block-by-block (each block
/// returns the head to the pivot, so every block re-enters at the same offset `h`).
pub proof fn lemma_tail_safe_split(tm: Tm, c: TmConfig, f1: nat, f2: nat, h: nat)
    requires
        tm_wf(tm),
        tail_safe(tm, c, f1, h),
        tail_safe(tm, tm_run(tm, c, f1), f2, tail_end_h(tm, c, f1, h)),
    ensures
        tail_safe(tm, c, (f1 + f2) as nat, h),
        tail_end_h(tm, c, (f1 + f2) as nat, h)
            == tail_end_h(tm, tm_run(tm, c, f1), f2, tail_end_h(tm, c, f1, h)),
    decreases f1,
{
    reveal(tm_wf);
    if f1 == 0 {
        assert(tm_run(tm, c, 0) == c);
    } else if tm_terminal(tm, c) {
        // terminal idles: tm_run(c,f1)==c, tail_end_h(c,f1,h)==h, tail_safe(c,_,h) trivially true.
        crate::tm_run_lemmas::lemma_tm_terminal_run_identity(tm, c, f1);
        assert(tm_run(tm, c, f1) == c);
    } else {
        let mi = matching_index(tm, c);
        lemma_matching_index_ok(tm, c);
        let qt = tm.quints[mi];
        lemma_tm_step_picks(tm, c, mi);
        let next = apply_quint(qt, c, tm.m);
        // one-level unfold of tm_run: tm_run(c, k) == tm_run(next, k-1) for k >= 1.
        assert(tm_run(tm, c, f1) == tm_run(tm, next, (f1 - 1) as nat));
        assert((f1 + f2 - 1) as nat == ((f1 - 1) as nat + f2) as nat);
        match qt.dir {
            Dir::R => {
                lemma_tail_safe_split(tm, next, (f1 - 1) as nat, f2, (h + 1) as nat);
            },
            Dir::L => {
                assert(h >= 1);
                lemma_tail_safe_split(tm, next, (f1 - 1) as nat, f2, (h - 1) as nat);
            },
        }
    }
}

} // verus!
