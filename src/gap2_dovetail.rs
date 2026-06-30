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
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, sep, lemma_repunit_digits_le, lemma_repunit_step};
use crate::tm_h0_bwd::{digits_le, tm_config_wf, lemma_digits_le_pop, lemma_digits_le_low,
    lemma_digits_le_push};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold, lemma_pow_nat_pos, lemma_pow_high_tail};
use crate::tm_walk::{pile_ones, lemma_pile_ones_shift};

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

// ─────────────────────────────────────────────────────────────────────────────
// The `cnt`-block low digit (the INNER_TOP peek read; the `cnt`-dec quotient).
// ─────────────────────────────────────────────────────────────────────────────

/// The (`s`, `T`) part of the CZ counters above `cnt`'s separator: `R(s) + m^{s+1}·R(T)`.
/// `cz_u(cnt, s, T) == R(cnt) + m^{cnt+1}·cz_rest(s, T)`.
pub open spec fn cz_rest(s: nat, big_t: nat, m: nat) -> nat {
    (repunit_m(s, m) + pow_nat(m, (s + 1) as nat) * repunit_m(big_t, m)) as nat
}

/// **The `cnt` low digit + dec quotient.** The head-nearest place of `cz_u` is `1` iff `cnt > 0`
/// (else the `cnt`/`s` separator blank `0`), and dividing it out drops one `cnt` one:
/// `cz_u(cnt,s,T)/m == cz_u(cnt−1,s,T)` for `cnt > 0` (== `cz_rest(s,T)` for `cnt == 0`). This is the
/// INNER_TOP zero-test read and, simultaneously, the `cnt`-dec step (decrement = divide out the low one).
pub proof fn lemma_cz_u_pop(cnt: nat, s: nat, big_t: nat, m: nat)
    requires
        m > 1,
    ensures
        cz_u(cnt, s, big_t, m) % m == (if cnt == 0 { 0nat } else { 1nat }),
        cz_u(cnt, s, big_t, m) / m
            == (if cnt == 0 { cz_rest(s, big_t, m) } else { cz_u((cnt - 1) as nat, s, big_t, m) }),
{
    let m1 = m;
    let rest = cz_rest(s, big_t, m);
    let cu = cz_u(cnt, s, big_t, m);
    assert(cu == repunit_m(cnt, m) + pow_nat(m, (cnt + 1) as nat) * rest);   // def (cz_rest unfold)
    if cnt == 0 {
        assert(repunit_m(0, m) == 0);
        // pow(m,1) == m
        assert(pow_nat(m, 1) == m) by {
            lemma_pow_nat_unfold(m, 1);
            assert(pow_nat(m, 0) == 1);
            assert(m * pow_nat(m, 0) == m) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
        }
        assert(cu == m * rest);
        assert(m * rest == rest * m) by(nonlinear_arith);
        lemma_div_mod_step(rest, m, 0);          // (rest*m + 0)/m == rest, %m == 0
        assert(cu == rest * m + 0);
        assert(cu % m == 0);
        assert(cu / m == rest);
    } else {
        lemma_repunit_step((cnt - 1) as nat, m); // R(cnt) == m·R(cnt-1) + 1
        assert(((cnt - 1) as nat + 1) as nat == cnt);
        lemma_pow_nat_unfold(m, (cnt + 1) as nat); // m^{cnt+1} == m·m^{cnt}
        let q = cz_u((cnt - 1) as nat, s, big_t, m);
        assert(q == repunit_m((cnt - 1) as nat, m) + pow_nat(m, cnt) * rest);   // def + (cnt-1)+1==cnt
        assert(cu == m * q + 1) by(nonlinear_arith)
            requires
                cu == repunit_m(cnt, m) + pow_nat(m, (cnt + 1) as nat) * rest,
                repunit_m(cnt, m) == m * repunit_m((cnt - 1) as nat, m) + 1,
                pow_nat(m, (cnt + 1) as nat) == m * pow_nat(m, cnt),
                q == repunit_m((cnt - 1) as nat, m) + pow_nat(m, cnt) * rest;
        assert(m * q == q * m) by(nonlinear_arith);
        lemma_div_mod_step(q, m, 1);             // (q*m + 1)/m == q, %m == 1
        assert(cu == q * m + 1);
        assert(cu % m == 1);
        assert(cu / m == q);
    }
}

/// **INNER_TOP peek-`cnt` (the zero-test back-edge).** From the CZ-home config, two steps — `L` to expose
/// `cnt`'s inner cell, `R` to write it back — restore the whole config (counters AND the inert `v` working
/// tail) and branch to `q_pos` if `cnt > 0` or `q_zero` if `cnt == 0`. The `v`-tail-generic clone of
/// [`lemma_peek_gadget`]: the L/R pass carries any `v` through (`v → v·m+2 → v`), so the working region
/// rides untouched. Three gadget quintuples at `i_entry`/`i_pos`/`i_zero`:
///   `(q_entry, 2, 2, q_branch, L)`, `(q_branch, 1, 1, q_pos, R)`, `(q_branch, 0, 0, q_zero, R)`.
pub proof fn lemma_cz_peek(
    tm: Tm, cnt: nat, s: nat, big_t: nat, vtail: nat,
    q_entry: nat, q_branch: nat, q_pos: nat, q_zero: nat,
    i_entry: int, i_pos: int, i_zero: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q_entry < tm.m,
        0 <= i_entry < tm.quints.len(),
        0 <= i_pos < tm.quints.len(),
        0 <= i_zero < tm.quints.len(),
        tm.quints[i_entry] == mk_quint(q_entry, sep(), sep(), q_branch, Dir::L),
        tm.quints[i_pos] == mk_quint(q_branch, 1, 1, q_pos, Dir::R),
        tm.quints[i_zero] == mk_quint(q_branch, 0, 0, q_zero, Dir::R),
    ensures
        cnt > 0 ==> tm_run(tm, cz_config(cnt, s, big_t, vtail, q_entry, tm.m), 2)
                    == cz_config(cnt, s, big_t, vtail, q_pos, tm.m),
        cnt == 0 ==> tm_run(tm, cz_config(cnt, s, big_t, vtail, q_entry, tm.m), 2)
                    == cz_config(cnt, s, big_t, vtail, q_zero, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);                               // n ≥ 2, n < m
    let cu = cz_u(cnt, s, big_t, m);
    let c_entry = cz_config(cnt, s, big_t, vtail, q_entry, m);

    // Step 1 (L): expose cnt's inner cell. c_branch = (cu/m, vtail·m+2, cu%m, q_branch).
    lemma_tm_step_picks(tm, c_entry, i_entry);
    let c_branch = apply_quint(tm.quints[i_entry], c_entry, m);
    assert(tm_step(tm, c_entry) == Some(c_branch));
    assert(c_branch.u == cu / m);
    assert(c_branch.v == vtail * m + sep());
    assert(c_branch.a == cu % m);
    assert(c_branch.q == q_branch);
    lemma_div_mod_step(vtail, m, sep());         // (vtail·m+2)/m == vtail, %m == 2
    lemma_cz_u_pop(cnt, s, big_t, m);            // cu%m, and cu == m·(cu/m) + cu%m below
    lemma_fundamental_div_mod(cu as int, m as int);
    assert(cu == m * (cu / m) + cu % m);

    if cnt > 0 {
        // a == 1 ⟹ the q_pos branch fires; R re-pushes the one, restoring cu and vtail.
        assert(c_branch.a == 1);
        lemma_tm_step_picks(tm, c_branch, i_pos);
        let c_final = apply_quint(tm.quints[i_pos], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        assert(c_final.u == (cu / m) * m + 1);
        assert((cu / m) * m == m * (cu / m)) by(nonlinear_arith);
        assert(c_final.u == cu);                 // cu == m·(cu/m) + 1
        assert(c_final.v == vtail);
        assert(c_final.a == sep());
        assert(c_final == cz_config(cnt, s, big_t, vtail, q_pos, m));
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    } else {
        // a == 0 ⟹ the q_zero branch fires; R re-pushes the blank, restoring cu and vtail.
        assert(c_branch.a == 0);
        lemma_tm_step_picks(tm, c_branch, i_zero);
        let c_final = apply_quint(tm.quints[i_zero], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        assert(c_final.u == (cu / m) * m + 0);
        assert((cu / m) * m == m * (cu / m)) by(nonlinear_arith);
        assert(c_final.u == cu);                 // cu == m·(cu/m) + 0
        assert(c_final.v == vtail);
        assert(c_final.a == sep());
        assert(c_final == cz_config(cnt, s, big_t, vtail, q_zero, m));
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The tailed walk-left (the dec-cnt foundation).
// ─────────────────────────────────────────────────────────────────────────────

/// **Walk-left over a unary block with a `u`-high-tail above its separator.** The tail-generic analog of
/// [`crate::tm_walk::lemma_walk_left_inner`]: from state `q_walk` scanning a `1`, with `j0` further ones in
/// `u` then a separator blank then a preserved tail (`u == repunit_m(j0) + m^{j0+1}·tail`), the loop
/// quintuple `(q_walk, 1, 1, q_walk, L)` fires `j0 + 1` times — peeling all `j0 + 1` ones onto `v` — and
/// **stops at the separator blank**, leaving the tail flush on `u` (`u == tail`, scanned `== 0`). This is
/// exactly the CZ dec/seek discipline: a walk over the `cnt` block halts at the `cnt`/`s` separator,
/// the `s,T` blocks (`tail = cz_rest`) riding untouched. `tail == 0` recovers `lemma_walk_left_inner`.
/// Induction on `j0`, the tail carried verbatim through each div/mod (the separator `0` at place `j0` is
/// what stops the loop). Mirror of `lemma_walk_left_inner` (the `v` side is already generic there).
pub proof fn lemma_walk_left_tailed(tm: Tm, c: TmConfig, q_walk: nat, j0: nat, tail: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        c.u == repunit_m(j0, tm.m) + pow_nat(tm.m, (j0 + 1) as nat) * tail,
        c.a == 1,
        c.q == q_walk,
    ensures
        tm_run(tm, c, (j0 + 1) as nat)
            == (TmConfig { u: tail, v: pile_ones(c.v, (j0 + 1) as nat, tm.m), a: 0, q: q_walk }),
    decreases j0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_tm_step_picks(tm, c, i1);
    let c_next = (TmConfig { u: c.u / m, v: c.v * m + 1, a: c.u % m, q: q_walk });
    assert(tm_step(tm, c) == Some(c_next));   // apply_quint L with a2 == 1
    if j0 == 0 {
        // c.u == repunit(0) + m^1·tail == m·tail ⟹ c_next == (tail, c.v·m+1, 0, q_walk).
        assert(repunit_m(0, m) == 0);
        assert(pow_nat(m, 1) == m) by {
            lemma_pow_nat_unfold(m, 1);
            assert(pow_nat(m, 0) == 1);
            assert(m * pow_nat(m, 0) == m) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
        }
        assert(c.u == m * tail);
        assert(m * tail == tail * m) by(nonlinear_arith);
        lemma_div_mod_step(tail, m, 0);       // (tail·m + 0)/m == tail, %m == 0
        assert(c.u == tail * m + 0);
        assert(c_next.u == tail);
        assert(c_next.a == 0);
        assert(pile_ones(c.v, 0, m) == c.v);
        assert(pile_ones(c.v, 1, m) == pile_ones(c.v, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: tail, v: pile_ones(c.v, 1, m), a: 0, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // c.u == repunit(j0) + m^{j0+1}·tail == m·(repunit(j0-1) + m^{j0}·tail) + 1: peel one.
        lemma_repunit_step((j0 - 1) as nat, m);    // repunit(j0) == m·repunit(j0-1) + 1
        assert(((j0 - 1) as nat + 1) as nat == j0);
        lemma_pow_nat_unfold(m, (j0 + 1) as nat);  // m^{j0+1} == m·m^{j0}
        let qq = (repunit_m((j0 - 1) as nat, m) + pow_nat(m, j0) * tail) as nat;
        assert(c.u == m * qq + 1) by(nonlinear_arith)
            requires
                c.u == repunit_m(j0, m) + pow_nat(m, (j0 + 1) as nat) * tail,
                repunit_m(j0, m) == m * repunit_m((j0 - 1) as nat, m) + 1,
                pow_nat(m, (j0 + 1) as nat) == m * pow_nat(m, j0),
                qq == repunit_m((j0 - 1) as nat, m) + pow_nat(m, j0) * tail;
        assert(m * qq == qq * m) by(nonlinear_arith);
        lemma_div_mod_step(qq, m, 1);              // (qq·m + 1)/m == qq, %m == 1
        assert(c_next.u == qq);
        assert(c_next.a == 1);
        // qq is the (j0-1)-tailed u; recurse.
        lemma_walk_left_tailed(tm, c_next, q_walk, (j0 - 1) as nat, tail, i1);
        lemma_pile_ones_shift(c.v, j0, m);         // pile_ones(c.v·m+1, j0) == pile_ones(c.v, j0+1)
        assert(tm_run(tm, c, (j0 + 1) as nat) == tm_run(tm, c_next, j0));
    }
}

} // verus!
