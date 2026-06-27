//! # GAP-2 G2-F — the RIGHT-tape high-tail lift (the α-block lift, `v`-side mirror of [`crate::gap2_tail_lift`])
//!
//! The global tape layout parks the input word-number α in a dedicated **α-block** to the RIGHT of the
//! emitter's output region (`docs/gap2-input-loader-plan.md` §N+11:
//! `[emit scratch: master 0 temp 0 output] 0 [α-block] 0`). So at the emitter's home pivot the right tape is
//! `v == dpack(od) + m^H·A` — the local output `dpack(od)` with the α-block `A` as a **high tail at offset
//! `H`** (the output-region size + separator). The emit phase lemmas (`gap2_emit_seq::lemma_uinv_phase`) are
//! stated in the LOCAL frame `v == dpack(od)` (output only). To apply them to the concrete machine, lift the
//! run over the α-block tail — the exact `v`-side mirror of the `u`-side `a+1`-backup lift
//! ([`crate::gap2_tail_lift::lemma_run_tail`]).
//!
//! **The mirror (L ↔ R).** A config `(u, v, a, q)` has `a, q` as separate fields, not computed from `v`, so
//! `add_hi_v(c) = {v: c.v + m^H·A, ..c}` leaves `(q, a)` untouched and the **same quintuple fires** each step.
//! The tail only perturbs the step *result*, with the roles of L and R swapped vs the `u`-side:
//!   - **L-move** `v' = v·m + a2`: with tail `(v + m^H·A)·m + a2 = v·m + a2 + m^(H+1)·A` — the tail rides up
//!     to `H+1`. *Unconditional* (an L-move pushes onto `v`, never reads its low digit).
//!   - **R-move** `v' = v/m`, `a' = v%m`: with tail `(v + m^H·A)/m = v/m + m^(H-1)·A` and `(v + m^H·A)%m =
//!     v%m` *iff `H ≥ 1`* (else the tail's low digit corrupts the popped scanned symbol). Tail rides to `H-1`.
//!
//! So the sole safety condition is **`H ≥ 1` before every R-move** ([`tail_safe_v`]) — the head never reaching
//! the α-block while shuttling over the output. The lift ([`lemma_run_tail_v`]) gives
//! `tm_run(add_hi_v(c, H, A), fuel) == add_hi_v(tm_run(c, fuel), tail_end_h_v(c, fuel, H), A)`.
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
use crate::gap2_tail_lift::lemma_match_is;
use verus_group_theory::word_numbering::lemma_div_mod_step;

verus! {

/// Add a high tail `m^h·t` to the RIGHT tape `v`, leaving the scanned symbol `a`, state `q`, and left tape
/// `u` untouched. The `v`-side analog of [`crate::gap2_tail_lift::add_hi`].
pub open spec fn add_hi_v(c: TmConfig, h: nat, t: nat, m: nat) -> TmConfig {
    TmConfig { u: c.u, v: (c.v + pow_nat(m, h) * t) as nat, a: c.a, q: c.q }
}

/// **The right-tail is never popped.** Running `fuel` steps from `c` with the tail at offset `h`: each
/// L-move advances the offset to `h+1` (unconditional — L pushes onto `v`), each R-move requires `h ≥ 1`
/// (else the tail's low digit would corrupt the popped scanned symbol) and advances to `h-1`. The L↔R mirror
/// of [`crate::gap2_tail_lift::tail_safe`].
pub open spec fn tail_safe_v(tm: Tm, c: TmConfig, fuel: nat, h: nat) -> bool
    decreases fuel,
{
    if fuel == 0 || tm_terminal(tm, c) {
        true
    } else {
        let qt = tm.quints[matching_index(tm, c)];
        let next = apply_quint(qt, c, tm.m);
        match qt.dir {
            Dir::L => tail_safe_v(tm, next, (fuel - 1) as nat, (h + 1) as nat),
            Dir::R => h >= 1 && tail_safe_v(tm, next, (fuel - 1) as nat, (h - 1) as nat),
        }
    }
}

/// **The right-tail's offset after the run.** `+1` per L-move, `-1` per R-move; idles on terminal. The
/// offset at which [`lemma_run_tail_v`] re-deposits the tail.
pub open spec fn tail_end_h_v(tm: Tm, c: TmConfig, fuel: nat, h: nat) -> nat
    decreases fuel,
{
    if fuel == 0 || tm_terminal(tm, c) {
        h
    } else {
        let qt = tm.quints[matching_index(tm, c)];
        let next = apply_quint(qt, c, tm.m);
        match qt.dir {
            Dir::L => tail_end_h_v(tm, next, (fuel - 1) as nat, (h + 1) as nat),
            Dir::R => tail_end_h_v(tm, next, (fuel - 1) as nat, (h - 1) as nat),
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// per-step arithmetic: apply_quint commutes with add_hi_v
// ────────────────────────────────────────────────────────────────────────────

/// **One step commutes with the right-tail** (L-move, unconditional). An L-move pushes `a2` onto `v`, so
/// the tail rides up to `h+1` and `(u, a)` (read from the shared `c.u`) are untouched.
proof fn lemma_apply_add_hi_v_l(qt: crate::tm::Quintuple, c: TmConfig, h: nat, t: nat, m: nat)
    requires
        qt.dir == Dir::L,
    ensures
        apply_quint(qt, add_hi_v(c, h, t, m), m)
            == add_hi_v(apply_quint(qt, c, m), (h + 1) as nat, t, m),
{
    let ch = add_hi_v(c, h, t, m);
    // L: u' = u/m, v' = v·m + a2, a' = u%m. u,a depend only on c.u (shared) ⟹ equal.
    lemma_pow_nat_unfold(m, (h + 1) as nat);   // m^(h+1) == m·m^h
    // (c.v + m^h·t)·m + a2 == c.v·m + a2 + m^(h+1)·t
    assert((ch.v * m + qt.a2) as nat == (c.v * m + qt.a2 + pow_nat(m, (h + 1) as nat) * t) as nat)
        by(nonlinear_arith)
        requires
            ch.v == (c.v + pow_nat(m, h) * t) as nat,
            pow_nat(m, (h + 1) as nat) == m * pow_nat(m, h);
}

/// **One step commutes with the right-tail** (R-move, needs `h ≥ 1`). An R-move pops `v`'s low digit; the
/// tail `m^h·t ≡ 0 (mod m)` for `h ≥ 1` leaves the popped symbol `a' = v%m` intact and rides down to `h-1`.
proof fn lemma_apply_add_hi_v_r(qt: crate::tm::Quintuple, c: TmConfig, h: nat, t: nat, m: nat)
    requires
        qt.dir == Dir::R,
        h >= 1,
        m > 0,
    ensures
        apply_quint(qt, add_hi_v(c, h, t, m), m)
            == add_hi_v(apply_quint(qt, c, m), (h - 1) as nat, t, m),
{
    let ch = add_hi_v(c, h, t, m);
    let x = pow_nat(m, (h - 1) as nat) * t;
    lemma_pow_nat_unfold(m, h);   // m^h == m·m^(h-1)
    // m^h·t == m·x
    assert((pow_nat(m, h) * t) as nat == (m * x) as nat) by(nonlinear_arith)
        requires pow_nat(m, h) == m * pow_nat(m, (h - 1) as nat), x == pow_nat(m, (h - 1) as nat) * t;
    // ch.v == c.v + m·x; split c.v == (c.v/m)·m + c.v%m, so ch.v == (c.v/m + x)·m + c.v%m.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c.v as int, m as int);
    assert(c.v == (c.v / m) * m + c.v % m);
    assert(ch.v == (c.v / m + x) * m + c.v % m) by(nonlinear_arith)
        requires ch.v == (c.v + m * x) as nat, c.v == (c.v / m) * m + c.v % m;
    // hence ch.v / m == c.v/m + x  and  ch.v % m == c.v%m  (0 ≤ c.v%m < m).
    assert(c.v % m < m) by(nonlinear_arith) requires m > 0;
    lemma_div_mod_step((c.v / m + x) as nat, m, (c.v % m) as nat);
    assert(ch.v / m == (c.v / m + x) as nat);
    assert(ch.v % m == c.v % m);
}

// ────────────────────────────────────────────────────────────────────────────
// the black-box lift
// ────────────────────────────────────────────────────────────────────────────

/// **The right-tail lift.** If a run of `fuel` steps from `c` never pops the tail ([`tail_safe_v`]), then
/// running the SAME machine from the tailed config equals the tailed run-result, with the tail re-deposited
/// at the advanced offset [`tail_end_h_v`]:
///   `tm_run(add_hi_v(c, h, t)) == add_hi_v(tm_run(c), tail_end_h_v(c, fuel, h), t)`.
/// Black box: the underlying gadget's `v`-value arithmetic is never touched — only `(q, a)` (which
/// `add_hi_v` preserves) decide control flow. The L↔R mirror of [`crate::gap2_tail_lift::lemma_run_tail`].
pub proof fn lemma_run_tail_v(tm: Tm, c: TmConfig, fuel: nat, h: nat, t: nat)
    requires
        tm_wf(tm),
        tail_safe_v(tm, c, fuel, h),
    ensures
        tm_run(tm, add_hi_v(c, h, t, tm.m), fuel)
            == add_hi_v(tm_run(tm, c, fuel), tail_end_h_v(tm, c, fuel, h), t, tm.m),
    decreases fuel,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 0);
    let ch = add_hi_v(c, h, t, m);
    if fuel == 0 {
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
        lemma_matching_index_ok(tm, c);
        let qt = tm.quints[mi];
        lemma_tm_step_picks(tm, c, mi);
        let next = apply_quint(qt, c, m);
        assert(quint_matches(qt, ch));
        lemma_tm_step_picks(tm, ch, mi);
        let chnext = apply_quint(qt, ch, m);
        match qt.dir {
            Dir::L => {
                lemma_apply_add_hi_v_l(qt, c, h, t, m);
                assert(chnext == add_hi_v(next, (h + 1) as nat, t, m));
                lemma_run_tail_v(tm, next, (fuel - 1) as nat, (h + 1) as nat, t);
            },
            Dir::R => {
                // tail_safe_v(c, fuel, h) ⟹ h >= 1 (R branch).
                assert(h >= 1);
                lemma_apply_add_hi_v_r(qt, c, h, t, m);
                assert(chnext == add_hi_v(next, (h - 1) as nat, t, m));
                lemma_run_tail_v(tm, next, (fuel - 1) as nat, (h - 1) as nat, t);
            },
        }
    }
}

/// **One-step unfold of `tail_safe_v`/`tail_end_h_v` at a known firing quint.** When quint `i` (the unique
/// match) fires at `c` with `fuel ≥ 1`, the specs reduce to their continuation at `next = apply_quint`. The
/// `v`-side analog of [`crate::gap2_tail_lift::lemma_tail_unfold`].
pub proof fn lemma_tail_unfold_v(tm: Tm, c: TmConfig, fuel: nat, h: nat, i: int)
    requires
        tm_wf(tm),
        fuel >= 1,
        0 <= i < tm.quints.len(),
        quint_matches(tm.quints[i], c),
    ensures
        ({
            let next = apply_quint(tm.quints[i], c, tm.m);
            &&& (tm.quints[i].dir == Dir::L ==> {
                    &&& tail_safe_v(tm, c, fuel, h)
                            == tail_safe_v(tm, next, (fuel - 1) as nat, (h + 1) as nat)
                    &&& tail_end_h_v(tm, c, fuel, h)
                            == tail_end_h_v(tm, next, (fuel - 1) as nat, (h + 1) as nat)
                })
            &&& (tm.quints[i].dir == Dir::R ==> {
                    &&& tail_safe_v(tm, c, fuel, h)
                            == (h >= 1 && tail_safe_v(tm, next, (fuel - 1) as nat, (h - 1) as nat))
                    &&& tail_end_h_v(tm, c, fuel, h)
                            == tail_end_h_v(tm, next, (fuel - 1) as nat, (h - 1) as nat)
                })
        }),
{
    reveal(tm_wf);
    lemma_match_is(tm, c, i);            // matching_index(tm, c) == i
    lemma_matching_index_ok(tm, c);      // !tm_terminal(tm, c)
    assert(!tm_terminal(tm, c));
}

/// **tail_safe_v for a SINGLE step** firing quint `i`. An L-step is unconditional and bumps the offset to
/// `h+1`; an R-step needs `h ≥ 1` and drops it to `h-1`. The `v`-side analog of
/// [`crate::gap2_tail_lift::lemma_step_tail_safe`].
pub proof fn lemma_step_tail_safe_v(tm: Tm, c: TmConfig, i: int, h: nat)
    requires
        tm_wf(tm),
        0 <= i < tm.quints.len(),
        quint_matches(tm.quints[i], c),
        tm.quints[i].dir == Dir::R ==> h >= 1,
    ensures
        tail_safe_v(tm, c, 1, h),
        tm.quints[i].dir == Dir::L ==> tail_end_h_v(tm, c, 1, h) == (h + 1) as nat,
        tm.quints[i].dir == Dir::R ==> tail_end_h_v(tm, c, 1, h) == (h - 1) as nat,
{
    lemma_tail_unfold_v(tm, c, 1, h, i);
}

// ────────────────────────────────────────────────────────────────────────────
// composition: tail_safe_v / tail_end_h_v split across a run boundary
// ────────────────────────────────────────────────────────────────────────────

/// **Right-tail-safety composes over a split.** The `v`-side analog of
/// [`crate::gap2_tail_lift::lemma_tail_safe_split`]; induction on `f1`.
pub proof fn lemma_tail_safe_v_split(tm: Tm, c: TmConfig, f1: nat, f2: nat, h: nat)
    requires
        tm_wf(tm),
        tail_safe_v(tm, c, f1, h),
        tail_safe_v(tm, tm_run(tm, c, f1), f2, tail_end_h_v(tm, c, f1, h)),
    ensures
        tail_safe_v(tm, c, (f1 + f2) as nat, h),
        tail_end_h_v(tm, c, (f1 + f2) as nat, h)
            == tail_end_h_v(tm, tm_run(tm, c, f1), f2, tail_end_h_v(tm, c, f1, h)),
    decreases f1,
{
    reveal(tm_wf);
    if f1 == 0 {
        assert(tm_run(tm, c, 0) == c);
    } else if tm_terminal(tm, c) {
        crate::tm_run_lemmas::lemma_tm_terminal_run_identity(tm, c, f1);
        assert(tm_run(tm, c, f1) == c);
    } else {
        let mi = matching_index(tm, c);
        lemma_matching_index_ok(tm, c);
        let qt = tm.quints[mi];
        lemma_tm_step_picks(tm, c, mi);
        let next = apply_quint(qt, c, tm.m);
        assert(tm_run(tm, c, f1) == tm_run(tm, next, (f1 - 1) as nat));
        assert((f1 + f2 - 1) as nat == ((f1 - 1) as nat + f2) as nat);
        match qt.dir {
            Dir::L => {
                lemma_tail_safe_v_split(tm, next, (f1 - 1) as nat, f2, (h + 1) as nat);
            },
            Dir::R => {
                assert(h >= 1);
                lemma_tail_safe_v_split(tm, next, (f1 - 1) as nat, f2, (h - 1) as nat);
            },
        }
    }
}

/// **Extend an accumulated `tail_safe_v` by one segment.** The `v`-side analog of
/// [`crate::gap2_tail_lift::lemma_tail_chain`]; a thin specialization of [`lemma_tail_safe_v_split`].
pub proof fn lemma_tail_v_chain(tm: Tm, c0: TmConfig, f: nat, sf: nat, h0: nat, hk: nat, hk2: nat)
    requires
        tm_wf(tm),
        tail_safe_v(tm, c0, f, h0),
        tail_end_h_v(tm, c0, f, h0) == hk,
        tail_safe_v(tm, tm_run(tm, c0, f), sf, hk),
        tail_end_h_v(tm, tm_run(tm, c0, f), sf, hk) == hk2,
    ensures
        tail_safe_v(tm, c0, (f + sf) as nat, h0),
        tail_end_h_v(tm, c0, (f + sf) as nat, h0) == hk2,
{
    lemma_tail_safe_v_split(tm, c0, f, sf, h0);
}

} // verus!
