//! # GAP-2 brick G2-D (backward) — `mm_in_H0 ⟹ TM reaches origin`
//!
//! The converse of `tm_h0::lemma_tm_halt_implies_h0`. The modular machine, by determinism, runs
//! exactly the TM's trace through the alternating reps; it can only reach the terminal origin `(0,0)`
//! when the TM itself halts at the origin config. This direction needs a **tape digit-invariant**
//! (`digits_le`): a TM-terminal config has its rep modular-terminal only when the scanned symbol is a
//! real symbol (`≤ n`), which requires the half-tapes to carry only symbol-digits. We thread that
//! invariant (preserved by every step) through the backward induction on the modular step count.
//! See `docs/gap2-register-modular-plan.md`.

use vstd::prelude::*;
use verus_group_theory::machine_group::{ModMachine, Dir, mm_in_H0, mm_terminal, mm_yields,
    mm_reaches, quad_matches, mod_machine_wf, lemma_yield_deterministic};
use vstd::arithmetic::div_mod::lemma_div_decreases;
use crate::tm::{Tm, tm_wf, quint_wf, tm_terminal, tm_step, tm_halts_at, tm_origin, TmConfig,
    matching_index, apply_quint, quint_matches, lemma_matching_index_ok, lemma_nonterminal_residues};
use crate::tm_modular::{tm_to_modmachine, rep1, rep2, rep_next, sim_target, quint_first,
    quint_second, lemma_quads_of, lemma_tm_modmachine_wf, lemma_sim_step, lemma_index_half};
use crate::tm_h0::{is_rep, lemma_tm_halt_implies_h0};

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// The tape digit-invariant: every base-m digit of `x` is a real symbol (≤ n).
// ─────────────────────────────────────────────────────────────────────────────

/// The origin config is TM-terminal: its state `0` is below every quintuple's state (`≥ n+1`).
pub proof fn lemma_origin_tm_terminal(tm: Tm)
    requires
        tm_wf(tm),
    ensures
        tm_terminal(tm, tm_origin()),
{
    reveal(tm_wf);
    assert forall|i: int| 0 <= i < tm.quints.len() implies !quint_matches(#[trigger] tm.quints[i], tm_origin()) by {
        assert(quint_wf(tm.quints[i], tm.n, tm.m));
        assert(tm.quints[i].q >= tm.n + 1);
    }
}

/// All base-`m` digits of `x` are `≤ n`.
pub open spec fn digits_le(x: nat, m: nat, n: nat) -> bool
    decreases x via digits_le_dec
{
    x == 0 || m <= 1 || (x % m <= n && digits_le(x / m, m, n))
}

#[via_fn]
proof fn digits_le_dec(x: nat, m: nat, n: nat) {
    if x != 0 && m > 1 {
        lemma_div_decreases(x as int, m as int);
    }
}

/// Configuration well-formedness: scanned is a real symbol, state in range, both half-tapes carry
/// only symbol-digits. (Preserved by every TM step — `lemma_tm_config_wf_step`.)
pub open spec fn tm_config_wf(tm: Tm, c: TmConfig) -> bool {
    &&& c.a <= tm.n
    &&& c.q < tm.m
    &&& digits_le(c.u, tm.m, tm.n)
    &&& digits_le(c.v, tm.m, tm.n)
}

/// Pushing a symbol-digit `d ≤ n` onto `x` preserves the invariant.
pub proof fn lemma_digits_le_push(x: nat, m: nat, n: nat, d: nat)
    requires
        m > 1,
        n < m,
        d <= n,
        digits_le(x, m, n),
    ensures
        digits_le(x * m + d, m, n),
{
    assert(d < m);   // d ≤ n < m
    verus_group_theory::word_numbering::lemma_div_mod_step(x, m, d);   // (x*m+d)/m==x, %m==d
    // digits_le(x*m+d) unfolds: (x*m+d)%m == d ≤ n  ∧  digits_le((x*m+d)/m == x).
    if x * m + d == 0 {
    } else {
        assert((x * m + d) % m <= n);
        assert(digits_le((x * m + d) / m, m, n));
    }
}

/// Dropping the low digit (`x / m`) preserves the invariant.
pub proof fn lemma_digits_le_pop(x: nat, m: nat, n: nat)
    requires
        m > 1,
        digits_le(x, m, n),
    ensures
        digits_le(x / m, m, n),
{
    if x == 0 {
        assert(x / m == 0);
    } else {
        // digits_le(x) = (x%m ≤ n ∧ digits_le(x/m)).
    }
}

/// The low digit of a wf tape is a real symbol.
pub proof fn lemma_digits_le_low(x: nat, m: nat, n: nat)
    requires
        m > 1,
        digits_le(x, m, n),
    ensures
        x % m <= n,
{
    if x == 0 {
        vstd::arithmetic::div_mod::lemma_small_mod(0, m);   // 0 % m == 0
    }
}

/// Every TM step preserves configuration well-formedness.
pub proof fn lemma_tm_config_wf_step(tm: Tm, c: TmConfig)
    requires
        tm_wf(tm),
        tm_config_wf(tm, c),
        !tm_terminal(tm, c),
    ensures
        tm_config_wf(tm, tm_step(tm, c).unwrap()),
{
    reveal(tm_wf);
    let m = tm.m;
    let n = tm.n;
    lemma_matching_index_ok(tm, c);
    let qt = tm.quints[matching_index(tm, c)];
    assert(quint_wf(qt, n, m));
    assert(qt.a2 <= n && n + 1 <= qt.q2 < m);
    assert(m > 1);
    let c2 = apply_quint(qt, c, m);
    assert(tm_step(tm, c) == Some(c2));
    match qt.dir {
        Dir::R => {
            // c2 = (u*m+a2, v/m, v%m, q2).
            lemma_digits_le_push(c.u, m, n, qt.a2);   // digits_le(c2.u)
            lemma_digits_le_pop(c.v, m, n);            // digits_le(c2.v)
            lemma_digits_le_low(c.v, m, n);            // c2.a = v%m ≤ n
            assert(c2.a <= n && c2.q < m);
        },
        Dir::L => {
            // c2 = (u/m, v*m+a2, u%m, q2).
            lemma_digits_le_pop(c.u, m, n);
            lemma_digits_le_push(c.v, m, n, qt.a2);
            lemma_digits_le_low(c.u, m, n);
            assert(c2.a <= n && c2.q < m);
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Terminal correspondence: a wf TM-terminal config has both reps modular-terminal.
// ─────────────────────────────────────────────────────────────────────────────

/// A well-formed TM-terminal config is modular-terminal in both encodings. (A first quad `(a,q)`
/// could only match `rep1`'s residues `(c.a, c.q)` via a quintuple match — excluded by `tm_terminal`;
/// a second quad `(q,a)` would need `c.a = state ≥ n+1`, excluded by `c.a ≤ n`.)
pub proof fn lemma_tm_terminal_to_mm_terminal(tm: Tm, c: TmConfig)
    requires
        tm_wf(tm),
        tm_config_wf(tm, c),
        tm_terminal(tm, c),
    ensures
        mm_terminal(tm_to_modmachine(tm), rep1(c, tm.m).0, rep1(c, tm.m).1),
        mm_terminal(tm_to_modmachine(tm), rep2(c, tm.m).0, rep2(c, tm.m).1),
{
    reveal(tm_wf);
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    let n = tm.n;
    let qs = tm.quints;
    lemma_quads_of(qs, m);
    assert(mm.quads.len() == 2 * qs.len());
    assert(c.a <= n && c.q < m && c.a < m);
    // residues of rep1 are (c.a, c.q); of rep2 are (c.q, c.a).
    verus_group_theory::word_numbering::lemma_div_mod_step(c.u, m, c.a);
    verus_group_theory::word_numbering::lemma_div_mod_step(c.v, m, c.q);
    verus_group_theory::word_numbering::lemma_div_mod_step(c.u, m, c.q);
    verus_group_theory::word_numbering::lemma_div_mod_step(c.v, m, c.a);
    assert forall|j: int| 0 <= j < mm.quads.len() implies
        !quad_matches(#[trigger] mm.quads[j], m, rep1(c, m).0, rep1(c, m).1)
        && !quad_matches(mm.quads[j], m, rep2(c, m).0, rep2(c, m).1)
    by {
        let p = j / 2;
        lemma_index_half(j, qs.len());
        assert(quint_wf(qs[p], n, m));
        assert(qs[p].a <= n && qs[p].q >= n + 1);
        // tm_terminal ⟹ this quintuple does not match c.
        assert(!quint_matches(qs[p], c));
        assert(!(qs[p].q == c.q && qs[p].a == c.a));
        if j % 2 == 0 {
            assert(j == 2 * p);
            assert(mm.quads[j] == quint_first(qs[p], m));
            // first quad (a=qs[p].a≤n, b=qs[p].q≥n+1).
            // rep1 match needs c.a==qs[p].a ∧ c.q==qs[p].q = quint_matches — excluded.
            // rep2 match needs c.q==qs[p].a ∧ c.a==qs[p].q; c.a≤n<n+1≤qs[p].q — excluded.
        } else {
            assert(j == 2 * p + 1);
            assert(mm.quads[j] == quint_second(qs[p], m));
            // second quad (a=qs[p].q≥n+1, b=qs[p].a≤n).
            // rep1 match needs c.a==qs[p].q; c.a≤n<n+1≤qs[p].q — excluded.
            // rep2 match needs c.q==qs[p].q ∧ c.a==qs[p].a = quint_matches — excluded.
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// `rep == (0,0) ⟹ config is the origin`.
// ─────────────────────────────────────────────────────────────────────────────

/// If an encoding of `c` is the modular origin `(0,0)`, then `c` is the origin config. (Both reps
/// are `(u·m+·, v·m+·)`; `=(0,0)` with `m>1` forces `u=v=a=q=0`.)
pub proof fn lemma_rep_origin(tm: Tm, c: TmConfig, p: (nat, nat))
    requires
        tm.m > 1,
        c.a <= tm.n,
        tm.n < tm.m,
        is_rep(p, c, tm.m),
        p == (0nat, 0nat),
    ensures
        c == tm_origin(),
{
    let m = tm.m;
    // p = rep1(c) or rep2(c); both components are nonneg multiples of m plus a residue < m.
    // (c.u*m + r) == 0 with r < m ⟹ c.u == 0 ∧ r == 0.
    assert(c.a < m);
    if p == rep1(c, m) {
        assert(c.u * m + c.a == 0 && c.v * m + c.q == 0);
        assert(c.a == 0 && c.u * m == 0 && c.q == 0 && c.v * m == 0);
        assert(c.u == 0) by (nonlinear_arith) requires c.u * m == 0, m > 0;
        assert(c.v == 0) by (nonlinear_arith) requires c.v * m == 0, m > 0;
    } else {
        assert(c.u * m + c.q == 0 && c.v * m + c.a == 0);
        assert(c.q == 0 && c.u * m == 0 && c.a == 0 && c.v * m == 0);
        assert(c.u == 0) by (nonlinear_arith) requires c.u * m == 0, m > 0;
        assert(c.v == 0) by (nonlinear_arith) requires c.v * m == 0, m > 0;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The backward induction.
// ─────────────────────────────────────────────────────────────────────────────

/// **Backward H₀ correspondence.** If an encoding `P` of a wf config `c` modular-reaches the origin
/// `(0,0)` in `k` steps, then the TM halts at the origin config from `c`. Induction on `k`: the
/// modular run is deterministic, so it follows the TM's trace (via `lemma_sim_step`) until the TM
/// halts; a halted TM config is modular-terminal (`lemma_tm_terminal_to_mm_terminal`), so the only
/// way to *reach* `(0,0)` is for that halting config to be the origin itself.
pub proof fn lemma_mm_reaches_implies_tm(tm: Tm, c: TmConfig, p: (nat, nat), k: nat)
    requires
        tm_wf(tm),
        tm_config_wf(tm, c),
        is_rep(p, c, tm.m),
        mm_reaches(tm_to_modmachine(tm), p.0, p.1, 0, 0, k),
    ensures
        exists|fuel: nat| tm_halts_at(tm, c, tm_origin(), fuel),
    decreases k,
{
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    lemma_tm_modmachine_wf(tm);
    reveal_with_fuel(mm_reaches, 1);
    if tm_terminal(tm, c) {
        lemma_tm_terminal_to_mm_terminal(tm, c);     // both reps modular-terminal
        // P modular-terminal ⟹ it yields nothing ⟹ mm_reaches forces k == 0 ⟹ P == (0,0).
        assert(mm_terminal(mm, p.0, p.1)) by {
            if p == rep1(c, m) { } else { assert(p == rep2(c, m)); }
        }
        if k != 0 {
            // mm_reaches(P,(0,0),k) with k≥1 needs a yield from P — impossible (terminal).
            assert(exists|am: nat, bm: nat| #![auto]
                mm_yields(mm, p.0, p.1, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat));
            let ambm: (nat, nat) = choose|am: nat, bm: nat| #![auto]
                mm_yields(mm, p.0, p.1, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat);
            let am = ambm.0;
            let bm = ambm.1;
            let i = choose|i: int| 0 <= i < mm.quads.len()
                && quad_matches(mm.quads[i], m, p.0, p.1)
                && verus_group_theory::machine_group::quad_step(mm.quads[i], m, p.0, p.1) == (am, bm);
            assert(0 <= i < mm.quads.len() && quad_matches(mm.quads[i], m, p.0, p.1));
            assert(!quad_matches(mm.quads[i], m, p.0, p.1));   // mm_terminal
            assert(false);
        }
        assert(k == 0);
        assert(p == (0nat, 0nat));
        lemma_rep_origin(tm, c, p);    // c == origin
        assert(tm_halts_at(tm, c, tm_origin(), 0nat));
        assert(exists|fuel: nat| tm_halts_at(tm, c, tm_origin(), fuel));
    } else {
        // c steps to c2; P yields rep_next == rep(c2). Determinism + IH.
        lemma_nonterminal_residues(tm, c);
        let qt = tm.quints[matching_index(tm, c)];
        let c2 = apply_quint(qt, c, m);
        assert(tm_step(tm, c) == Some(c2));
        let tgt = sim_target(qt, c, m);
        lemma_sim_step(tm, c);
        assert(mm_yields(mm, p.0, p.1, tgt.0, tgt.1)) by {
            if p == rep1(c, m) { } else { assert(p == rep2(c, m)); }
        }
        // k ≥ 1 (else P == (0,0) ⟹ c == origin ⟹ terminal, contra).
        if k == 0 {
            assert(p == (0nat, 0nat));
            lemma_rep_origin(tm, c, p);
            lemma_origin_tm_terminal(tm);   // origin has state 0, no quintuple matches
            assert(false);
        }
        assert(k >= 1);
        // the unique successor of P is tgt.
        assert(exists|am: nat, bm: nat| #![auto]
            mm_yields(mm, p.0, p.1, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat));
        let ambm: (nat, nat) = choose|am: nat, bm: nat| #![auto]
            mm_yields(mm, p.0, p.1, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat);
        let am = ambm.0;
        let bm = ambm.1;
        assert(mm_yields(mm, p.0, p.1, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat));
        lemma_yield_deterministic(mm, p.0, p.1, am, bm, tgt.0, tgt.1);
        assert(am == tgt.0 && bm == tgt.1);
        assert(mm_reaches(mm, tgt.0, tgt.1, 0, 0, (k - 1) as nat));
        // tgt == rep_next(qt,c,m) is rep1(c2) or rep2(c2).
        assert(tgt == rep_next(qt, c, m));
        assert(is_rep(tgt, c2, m)) by {
            match qt.dir {
                Dir::R => { assert(rep_next(qt, c, m) == rep2(c2, m)); },
                Dir::L => { assert(rep_next(qt, c, m) == rep1(c2, m)); },
            }
        }
        lemma_tm_config_wf_step(tm, c);    // tm_config_wf(c2)
        lemma_mm_reaches_implies_tm(tm, c2, tgt, (k - 1) as nat);
        let fuel2 = choose|fuel: nat| tm_halts_at(tm, c2, tm_origin(), fuel);
        assert(tm_halts_at(tm, c2, tm_origin(), fuel2));
        // c is not terminal ⟹ c ≠ origin; step to c2 ⟹ tm_halts_at(c, origin, fuel2+1).
        assert(c != tm_origin()) by {
            if c == tm_origin() { lemma_origin_tm_terminal(tm); }
        }
        assert(tm_halts_at(tm, c, tm_origin(), (fuel2 + 1) as nat));
        assert(exists|fuel: nat| tm_halts_at(tm, c, tm_origin(), fuel));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The packaged H₀ ⟺ TM-reaches-origin iff (both directions).
// ─────────────────────────────────────────────────────────────────────────────

/// **The H₀ correspondence (both directions).** For a well-formed config `c`, the modular machine
/// has `rep1(c) ∈ H₀` iff the TM, started from `c`, reaches the origin config. This is the headline
/// of the TM→modular "clean half": the modular machine's reaches-origin set is exactly the encoded
/// halting configs of the TM. Combined with a `register → TM` reduction (G2-E, deferred) it discharges
/// the machine content of `ceer_realizes`.
pub proof fn lemma_tm_h0_iff(tm: Tm, c: TmConfig)
    requires
        tm_wf(tm),
        tm_config_wf(tm, c),
    ensures
        mm_in_H0(tm_to_modmachine(tm), rep1(c, tm.m).0, rep1(c, tm.m).1)
            <==> (exists|fuel: nat| tm_halts_at(tm, c, tm_origin(), fuel)),
{
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    // ⟸ : TM reaches origin ⟹ rep1(c) ∈ H₀.
    if exists|fuel: nat| tm_halts_at(tm, c, tm_origin(), fuel) {
        let fuel = choose|fuel: nat| tm_halts_at(tm, c, tm_origin(), fuel);
        lemma_tm_halt_implies_h0(tm, c, fuel);
    }
    // ⟹ : rep1(c) ∈ H₀ ⟹ TM reaches origin.
    if mm_in_H0(mm, rep1(c, m).0, rep1(c, m).1) {
        let k = choose|k: nat| mm_reaches(mm, rep1(c, m).0, rep1(c, m).1, 0, 0, k);
        assert(is_rep(rep1(c, m), c, m));
        lemma_mm_reaches_implies_tm(tm, c, rep1(c, m), k);
    }
}

} // verus!
