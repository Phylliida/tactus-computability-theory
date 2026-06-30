//! # GAP-2 G2-F Route (i) brick R-S — the dovetail control skeleton, layer 1: the Control-Zone layout.
//!
//! R-S re-expresses `search_rm`'s outer-`T` / inner-`s ≤ T` dovetail nesting as a **TM orchestrator**
//! over the `assemble4` n≥4 window scaffold (the per-stage body is now a base-`m` emit→reloc→compare,
//! not an RM `eq_test`, so the dovetail cannot be black-boxed as an RM — see
//! `docs/gap2-input-loader-plan.md` §N+31/§N+33). This module pins the **Control Zone (CZ)** tape
//! layout that the dovetail counters live in.
//!
//! ## Design (co-designed with Danielle, §N+33)
//! * **Three unary counters** `T` (outer bound), `s` (inner stage), `cnt = T+1−s` (the inner-loop
//!   countdown), mirroring `search_rm`'s `Treg`/`scnt`/`cnt`. A **generate-and-compare** match halts
//!   immediately (terminal accept), so the dovetail **short-circuits** — `search_rm`'s `result`
//!   accumulator is dropped entirely; the only "result" is Halt-vs-Continue, encoded in the state.
//! * **CZ-home model.** Between dovetail ops the head rests in the CZ; the dovetail loop runs there via
//!   counter gadgets, and the per-stage body is a shuttle-down-to-working-home / shuttle-back-up
//!   subroutine. The whole working region (emit masters, output, the immutable α-block) rides as an
//!   **inert tail on `v`** while the head does CZ work.
//! * **Layout.** The three counters are **blank-separated unary blocks on `u`**, low→high =
//!   `cnt`, `s`, `T`, head resting on a separator `sep() = 2` at the CZ↔working boundary:
//!   ```text
//!     u = [cnt ones] 0 [s ones] 0 [T ones]            (low digit nearest head = cnt's inner 1)
//!     a = 2   (the CZ home separator)
//!     v = vtail                                        (the inert working+α region)
//!   ```
//!   The blank `0` between blocks is the walk-stop that makes every counter op **tail-safe by
//!   construction** — a dec/peek walk over one block halts at the adjacent separator, never touching
//!   the neighbour blocks or the `v` tail. This is the same blank-delimited single-tape discipline the
//!   emitter uses (`gap2_emit_*`), here for the control counters.
//!
//! This layer ships the layout SPEC + its digit-bound / `tm_config_wf` lemma (plus two reusable digit
//! helpers). The back-edge primitives (SETUP `cnt:=T+1`, INNER_TOP peek/dec, CONT inc-s, OUTER_CONT
//! reset-s/inc-T) and the shuttle are the following layers. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use crate::tm::{Tm, TmConfig, tm_wf};
use crate::tm_two_counter::{repunit_m, sep, lemma_repunit_digits_le};
use crate::tm_h0_bwd::{digits_le, tm_config_wf, lemma_digits_le_pop, lemma_digits_le_low,
    lemma_digits_le_push};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold, lemma_pow_nat_pos, lemma_pow_high_tail};

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Reusable digit helpers (place-value bounds + a concat-at-offset for digits_le).
// ─────────────────────────────────────────────────────────────────────────────

/// A `c`-digit unary block fits in `c` base-`m` places: `repunit_m(c, m) < m^c` for `m ≥ 2`.
/// (Geometric bound `1 + m + … + m^{c−1} < m^c`.) The "blank above the block" fact the layout's
/// digit-bound proof needs to place each counter strictly below the next separator.
pub proof fn lemma_repunit_lt_pow(c: nat, m: nat)
    requires
        m >= 2,
    ensures
        repunit_m(c, m) < pow_nat(m, c),
    decreases c,
{
    if c == 0 {
        // repunit_m(0) == 0 < 1 == pow_nat(m, 0).
    } else {
        lemma_repunit_lt_pow((c - 1) as nat, m);   // repunit(c-1) < pow(m, c-1)
        lemma_pow_nat_unfold(m, c);                // pow(m, c) == m·pow(m, c-1)
        assert(repunit_m(c, m) == m * repunit_m((c - 1) as nat, m) + 1);
        assert(m * repunit_m((c - 1) as nat, m) + 1 < m * pow_nat(m, (c - 1) as nat)) by(nonlinear_arith)
            requires
                repunit_m((c - 1) as nat, m) < pow_nat(m, (c - 1) as nat),
                m >= 2;
    }
}

/// **digits_le concat-at-offset.** A low part below place `k` and a high part above compose: if every
/// digit of `low` and `high` is `≤ n` and `low < m^k` (so the two never overlap), then every digit of
/// `low + m^k·high` is `≤ n`. The tool for proving a blank-separated block stack is `tm_config_wf`.
/// Induction on `k`, peeling one place per step via [`lemma_pow_high_tail`] (`h = k, k = 1`:
/// `(low + m^k·high)/m == low/m + m^{k−1}·high`, `% m == low % m`).
pub proof fn lemma_digits_le_concat(low: nat, high: nat, k: nat, m: nat, n: nat)
    requires
        m > 1,
        n < m,
        digits_le(low, m, n),
        digits_le(high, m, n),
        low < pow_nat(m, k),
    ensures
        digits_le((low + pow_nat(m, k) * high) as nat, m, n),
    decreases k,
{
    let x = (low + pow_nat(m, k) * high) as nat;
    if k == 0 {
        assert(pow_nat(m, k) == 1);
        assert(low < 1);
        assert(low == 0);
        assert(x == high);
    } else {
        lemma_pow_nat_unfold(m, k);                               // pow(m,k) == m·pow(m,k-1)
        // pow(m,k)*high is a multiple of m^1, so /m and %m see only `low`, and /m exposes the next place.
        lemma_pow_high_tail(low, high, k, 1, m);
        assert(pow_nat(m, 1) == m) by {
            lemma_pow_nat_unfold(m, 1);
            assert(pow_nat(m, 0) == 1);
            assert(m * pow_nat(m, 0) == m) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
        }
        // x / m == low/m + m^{k-1}·high ;  x % m == low % m  (bridge pow_nat(m,1) == m).
        assert(x % pow_nat(m, 1) == low % pow_nat(m, 1));
        assert(x / pow_nat(m, 1) == low / pow_nat(m, 1) + pow_nat(m, (k - 1) as nat) * high);
        assert(x % m == low % m);
        assert(x / m == (low / m + pow_nat(m, (k - 1) as nat) * high) as nat);
        // x % m == low % m ≤ n (handles low == 0 via lemma_digits_le_low's 0 % m == 0).
        lemma_digits_le_low(low, m, n);
        // digits_le(x / m): recurse on the exposed quotient.
        lemma_digits_le_pop(low, m, n);                          // digits_le(low/m)
        lemma_fundamental_div_mod(low as int, m as int);         // low == m·(low/m) + low%m
        assert(low == m * (low / m) + low % m);
        assert(low / m < pow_nat(m, (k - 1) as nat)) by(nonlinear_arith)
            requires
                low < m * pow_nat(m, (k - 1) as nat),
                low == m * (low / m) + low % m,
                low % m >= 0;
        lemma_digits_le_concat((low / m), high, (k - 1) as nat, m, n);   // digits_le(x/m)
        // digits_le(x) via push: x == (x/m)·m + x%m, x%m ≤ n, digits_le(x/m).
        lemma_digits_le_push(x / m, m, n, x % m);                // digits_le((x/m)·m + x%m)
        lemma_fundamental_div_mod(x as int, m as int);           // x == m·(x/m) + x%m
        assert((x / m) * m == m * (x / m)) by(nonlinear_arith);
        assert(x == (x / m) * m + x % m);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The Control-Zone layout.
// ─────────────────────────────────────────────────────────────────────────────

/// The CZ counters packed on `u`, low→high blank-separated blocks `cnt`, `s`, `T`:
/// `cz_u = R(cnt) + m^{cnt+1}·( R(s) + m^{s+1}·R(T) )`, where `R = repunit_m`. The `0` digit at place
/// `cnt` (resp. `cnt+1+s`) is the separator the dec/peek walk on `cnt` (resp. `s`) stops at.
pub open spec fn cz_u(cnt: nat, s: nat, big_t: nat, m: nat) -> nat {
    (repunit_m(cnt, m)
        + pow_nat(m, (cnt + 1) as nat)
            * (repunit_m(s, m) + pow_nat(m, (s + 1) as nat) * repunit_m(big_t, m))) as nat
}

/// The CZ-home TM config: the three counters on `u`, the inert working+α region as the `v` tail, the
/// head on the home separator `sep() = 2`, in state `q`.
pub open spec fn cz_config(cnt: nat, s: nat, big_t: nat, vtail: nat, q: nat, m: nat) -> TmConfig {
    TmConfig { u: cz_u(cnt, s, big_t, m), v: vtail, a: sep(), q }
}

/// **Every digit of `cz_u` is a real symbol** (`≤ n`). Two `lemma_digits_le_concat` applications stack
/// `T` above `s` (offset `s+1`) and that block above `cnt` (offset `cnt+1`); each block is a repunit
/// (`lemma_repunit_digits_le`) sitting strictly below its separator (`lemma_repunit_lt_pow`).
pub proof fn lemma_cz_u_digits_le(cnt: nat, s: nat, big_t: nat, m: nat, n: nat)
    requires
        m >= 2,
        n >= 1,
        n < m,
    ensures
        digits_le(cz_u(cnt, s, big_t, m), m, n),
{
    let rc = repunit_m(cnt, m);
    let rs = repunit_m(s, m);
    let rt = repunit_m(big_t, m);
    lemma_repunit_digits_le(cnt, m, n);
    lemma_repunit_digits_le(s, m, n);
    lemma_repunit_digits_le(big_t, m, n);

    // inner = R(s) + m^{s+1}·R(T), digits ≤ n.
    lemma_repunit_lt_pow(s, m);                  // rs < pow(m, s)
    lemma_pow_nat_unfold(m, (s + 1) as nat);     // pow(m, s+1) == m·pow(m, s)
    lemma_pow_nat_pos(m, s);                      // pow(m, s) ≥ 1
    assert(rs < pow_nat(m, (s + 1) as nat)) by(nonlinear_arith)
        requires
            rs < pow_nat(m, s),
            pow_nat(m, (s + 1) as nat) == m * pow_nat(m, s),
            m >= 2,
            pow_nat(m, s) >= 1;
    lemma_digits_le_concat(rs, rt, (s + 1) as nat, m, n);
    let inner = (rs + pow_nat(m, (s + 1) as nat) * rt) as nat;

    // cz_u = R(cnt) + m^{cnt+1}·inner, digits ≤ n.
    lemma_repunit_lt_pow(cnt, m);                // rc < pow(m, cnt)
    lemma_pow_nat_unfold(m, (cnt + 1) as nat);   // pow(m, cnt+1) == m·pow(m, cnt)
    lemma_pow_nat_pos(m, cnt);                    // pow(m, cnt) ≥ 1
    assert(rc < pow_nat(m, (cnt + 1) as nat)) by(nonlinear_arith)
        requires
            rc < pow_nat(m, cnt),
            pow_nat(m, (cnt + 1) as nat) == m * pow_nat(m, cnt),
            m >= 2,
            pow_nat(m, cnt) >= 1;
    lemma_digits_le_concat(rc, inner, (cnt + 1) as nat, m, n);
}

/// **The CZ-home config is well-formed** (`tm_config_wf`): scanned `sep() = 2 ≤ n` (so `n ≥ 2`), state
/// `q < m`, both half-tapes carry only symbol-digits (`cz_u` via [`lemma_cz_u_digits_le`], the `v` tail
/// by hypothesis — it is the working region, itself a wf tape value).
pub proof fn lemma_cz_config_wf(tm: Tm, cnt: nat, s: nat, big_t: nat, vtail: nat, q: nat)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q < tm.m,
        digits_le(vtail, tm.m, tm.n),
    ensures
        tm_config_wf(tm, cz_config(cnt, s, big_t, vtail, q, tm.m)),
{
    reveal(tm_wf);                                // 0 < n < m, m > 1
    let m = tm.m;
    let n = tm.n;
    lemma_cz_u_digits_le(cnt, s, big_t, m, n);
    // a == sep() == 2 ≤ n (n ≥ 2); q < m; digits_le(v == vtail) by hyp.
}

} // verus!
