//! # GAP-2 brick G2-A — a Turing-machine formalism (Minsky pair-arithmetic form)
//!
//! Aanderaa–Cohen, *Modular machines I* (1980), §1. A TM with alphabet `0..n` (0 = blank) and
//! states `n+1..m-1`. We represent a configuration in **Minsky pair form** `(u, v, a, q)`:
//!
//!   - `a` = currently scanned symbol (`0 ≤ a ≤ n`),
//!   - `q` = current state,
//!   - `u` = the left half-tape packed in base `m` (digit nearest the head is lowest),
//!   - `v` = the right half-tape packed in base `m`.
//!
//! This avoids any `Seq` tape: a TM step is *pure base-`m` arithmetic*, which is exactly the form the
//! modular machine consumes (`tm_modular.rs`). Symbols (`0..n`) and states (`n+1..m-1`) share the
//! residue space `0..m-1` — the trick that makes the TM→modular simulation work.
//!
//! See `docs/gap2-register-modular-plan.md`. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;

verus! {

/// A Turing-machine quintuple `q a a2 q2 dir`: in state `q` scanning symbol `a`, write `a2`, move
/// `dir`, enter state `q2`.
pub struct Quintuple {
    pub q: nat,    // current state
    pub a: nat,    // scanned symbol (0 ≤ a ≤ n)
    pub a2: nat,   // symbol written (0 ≤ a2 ≤ n)
    pub q2: nat,   // next state
    pub dir: Dir,
}

/// A Turing machine: alphabet `0..n`, modulus `m` (states live in `n+1..m-1`), a list of quintuples.
pub struct Tm {
    pub n: nat,
    pub m: nat,
    pub quints: Seq<Quintuple>,
}

/// A TM configuration in Minsky pair-arithmetic form.
pub struct TmConfig {
    pub u: nat,   // left half-tape, base-m packed (lowest digit nearest the head)
    pub v: nat,   // right half-tape, base-m packed
    pub a: nat,   // scanned symbol
    pub q: nat,   // state
}

/// A single quintuple is well-formed for a TM with alphabet bound `n`, modulus `m`:
/// scanned/written symbols are real symbols (`≤ n`), states lie strictly in `n+1..m-1`.
pub open spec fn quint_wf(qt: Quintuple, n: nat, m: nat) -> bool {
    &&& qt.a <= n
    &&& qt.a2 <= n
    &&& n + 1 <= qt.q < m
    &&& n + 1 <= qt.q2 < m
}

/// Well-formedness of a TM: `m > 1`, `0 < n < m`, every quintuple well-formed, and **deterministic**
/// (at most one quintuple per `(state, scanned)` pair).
#[verifier::opaque]
pub open spec fn tm_wf(tm: Tm) -> bool {
    &&& tm.m > 1
    &&& 0 < tm.n < tm.m
    &&& (forall|i: int| #![trigger tm.quints[i]]
            0 <= i < tm.quints.len() ==> quint_wf(tm.quints[i], tm.n, tm.m))
    &&& (forall|i: int, j: int|
            0 <= i < tm.quints.len() && 0 <= j < tm.quints.len()
            && #[trigger] tm.quints[i].q == #[trigger] tm.quints[j].q
            && tm.quints[i].a == tm.quints[j].a
            ==> i == j)
}

/// A quintuple matches a config when its `(state, scanned)` pair agrees.
pub open spec fn quint_matches(qt: Quintuple, c: TmConfig) -> bool {
    qt.q == c.q && qt.a == c.a
}

/// `c` is terminal: no quintuple applies.
pub open spec fn tm_terminal(tm: Tm, c: TmConfig) -> bool {
    forall|i: int| 0 <= i < tm.quints.len() ==> !quint_matches(#[trigger] tm.quints[i], c)
}

/// Apply a (matching) quintuple to a config — the pure base-`m` arithmetic step.
///   R: write a2, move right ⟹ push a2 onto `u`, pop `v`'s low digit as the new scanned.
///   L: write a2, move left  ⟹ push a2 onto `v`, pop `u`'s low digit as the new scanned.
pub open spec fn apply_quint(qt: Quintuple, c: TmConfig, m: nat) -> TmConfig {
    match qt.dir {
        Dir::R => TmConfig { u: c.u * m + qt.a2, v: c.v / m, a: c.v % m, q: qt.q2 },
        Dir::L => TmConfig { u: c.u / m, v: c.v * m + qt.a2, a: c.u % m, q: qt.q2 },
    }
}

/// The (unique, under `tm_wf`) quintuple index matching `c`, if any.
pub open spec fn matching_index(tm: Tm, c: TmConfig) -> int {
    choose|i: int| 0 <= i < tm.quints.len() && quint_matches(tm.quints[i], c)
}

/// One TM step. `None` iff terminal.
pub open spec fn tm_step(tm: Tm, c: TmConfig) -> Option<TmConfig> {
    if tm_terminal(tm, c) {
        None
    } else {
        Some(apply_quint(tm.quints[matching_index(tm, c)], c, tm.m))
    }
}

/// `c` is halted (step returns `None`).
pub open spec fn tm_is_halted(tm: Tm, c: TmConfig) -> bool {
    tm_step(tm, c) is None
}

/// Run the TM for `fuel` steps.
pub open spec fn tm_run(tm: Tm, c: TmConfig, fuel: nat) -> TmConfig
    decreases fuel,
{
    if fuel == 0 {
        c
    } else {
        match tm_step(tm, c) {
            Some(next) => tm_run(tm, next, (fuel - 1) as nat),
            None => c,
        }
    }
}

/// The TM, started from `c`, reaches the terminal config `target` within `fuel` steps.
pub open spec fn tm_halts_at(tm: Tm, c: TmConfig, target: TmConfig, fuel: nat) -> bool
    decreases fuel,
{
    if c == target && tm_terminal(tm, target) {
        true
    } else if fuel == 0 {
        false
    } else {
        match tm_step(tm, c) {
            Some(next) => tm_halts_at(tm, next, target, (fuel - 1) as nat),
            None => false,
        }
    }
}

/// The origin config: blank tape, state 0, scanning blank. Corresponds to the modular origin `(0,0)`.
pub open spec fn tm_origin() -> TmConfig {
    TmConfig { u: 0, v: 0, a: 0, q: 0 }
}

// ─────────────────────────────────────────────────────────────────────────────
// Basic facts
// ─────────────────────────────────────────────────────────────────────────────

/// Under a non-terminal config, the matching quintuple index is well-formed and it actually matches.
pub proof fn lemma_matching_index_ok(tm: Tm, c: TmConfig)
    requires
        !tm_terminal(tm, c),
    ensures
        0 <= matching_index(tm, c) < tm.quints.len(),
        quint_matches(tm.quints[matching_index(tm, c)], c),
{
    let i = choose|i: int| 0 <= i < tm.quints.len() && quint_matches(tm.quints[i], c);
    assert(0 <= i < tm.quints.len() && quint_matches(tm.quints[i], c));
}

/// A non-terminal config has a well-formed scanned symbol and state (`a ≤ n`, `n+1 ≤ q < m`),
/// read off the matching quintuple.
pub proof fn lemma_nonterminal_residues(tm: Tm, c: TmConfig)
    requires
        tm_wf(tm),
        !tm_terminal(tm, c),
    ensures
        c.a <= tm.n,
        tm.n + 1 <= c.q < tm.m,
{
    reveal(tm_wf);
    lemma_matching_index_ok(tm, c);
    let i = matching_index(tm, c);
    assert(quint_wf(tm.quints[i], tm.n, tm.m));
    assert(tm.quints[i].q == c.q && tm.quints[i].a == c.a);
}

} // verus!
