//! # GAP-2-E brick B1 — the unary-separator two-counter tape layout
//!
//! A 2-counter machine config `(c1, c2)` at state `q` is represented on the Minsky TM
//! (`tm.rs`) by the head resting **on the separator** (scanned symbol `2`), the left counter `c1`
//! as a unary block in `u`, the right counter `c2` as a unary block in `v`:
//!
//! ```text
//!   … 0 0 | 1 1 … 1 |  (2)  | 1 1 … 1 | 0 0 …       u = repunit_m(c1)   (low digit = inner 1)
//!         └─ c1 ───┘  head   └─ c2 ──┘              v = repunit_m(c2)
//! ```
//!
//! `repunit_m(c) = 1 + m + … + m^{c−1}` — a base-`m` number whose `c` lowest digits are all `1` and
//! the rest `0`. The defining recurrence `repunit_m(c+1) = m·repunit_m(c) + 1` is exactly "push a `1`",
//! the inc/dec gadgets' atomic edit (B3/B4). Because every digit of a repunit is `0` or `1 ≤ n`, the
//! layout config is `tm_config_wf` for any TM with alphabet `n ≥ 2` (so the separator `2 ≤ n`).
//!
//! See `docs/gap2-register-to-tm-plan.md`. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use crate::tm::{Tm, TmConfig, tm_wf};
use crate::tm_h0_bwd::{digits_le, tm_config_wf, lemma_digits_le_push};

verus! {

/// The separator symbol the head rests on between 2-counter steps.
pub open spec fn sep() -> nat { 2 }

/// `repunit_m(c, m) = 1 + m + m² + … + m^{c−1}` — the base-`m` value of a unary block of `c` ones
/// (low digit nearest the head). `repunit_m(0) = 0`, `repunit_m(1) = 1`, `repunit_m(2) = m + 1`.
pub open spec fn repunit_m(c: nat, m: nat) -> nat
    decreases c
{
    if c == 0 { 0 } else { m * repunit_m((c - 1) as nat, m) + 1 }
}

/// The defining "push a `1`" recurrence: `repunit_m(c+1) = m·repunit_m(c) + 1`.
pub proof fn lemma_repunit_step(c: nat, m: nat)
    ensures
        repunit_m((c + 1) as nat, m) == m * repunit_m(c, m) + 1,
{
    // definitional: repunit_m(c+1) unfolds with (c+1)-1 == c.
}

/// "Pop the inner `1`" / low digit of a nonempty block: `repunit_m(c+1) % m == 1` and
/// `repunit_m(c+1) / m == repunit_m(c)`. The arithmetic the zero-test (B2) and dec (B4) read.
pub proof fn lemma_repunit_div_mod(c: nat, m: nat)
    requires
        m > 1,
    ensures
        repunit_m((c + 1) as nat, m) % m == 1,
        repunit_m((c + 1) as nat, m) / m == repunit_m(c, m),
{
    let x = repunit_m(c, m);
    assert(repunit_m((c + 1) as nat, m) == m * x + 1);
    // (m*x + 1) % m == 1, (m*x + 1) / m == x  (1 < m).
    verus_group_theory::word_numbering::lemma_div_mod_step(x, m, 1);
    // lemma_div_mod_step gives (x*m + 1)/m == x and %m == 1; bridge m*x == x*m.
    assert(m * x == x * m) by(nonlinear_arith);
}

/// An empty block has value `0`: `repunit_m(0, m) == 0` (so its low digit is the blank `0`).
pub proof fn lemma_repunit_zero(m: nat)
    ensures
        repunit_m(0, m) == 0,
{
}

/// A nonempty block is nonzero: `repunit_m(c, m) > 0` for `c ≥ 1`, `m ≥ 1`.
pub proof fn lemma_repunit_pos(c: nat, m: nat)
    requires
        c >= 1,
        m >= 1,
    ensures
        repunit_m(c, m) > 0,
{
    assert(repunit_m(c, m) == m * repunit_m((c - 1) as nat, m) + 1);
}

/// Every base-`m` digit of a repunit is `0` or `1`, hence `≤ n` for any `n ≥ 1`.
pub proof fn lemma_repunit_digits_le(c: nat, m: nat, n: nat)
    requires
        m > 1,
        n >= 1,
        n < m,
    ensures
        digits_le(repunit_m(c, m), m, n),
    decreases c
{
    if c == 0 {
        // repunit_m(0) == 0 ⟹ digits_le holds (x == 0 branch).
    } else {
        let x = repunit_m((c - 1) as nat, m);
        lemma_repunit_digits_le((c - 1) as nat, m, n);   // digits_le(x)
        // repunit_m(c) == m*x + 1 == x*m + 1; push the digit 1 (≤ n).
        assert(m * x == x * m) by(nonlinear_arith);
        lemma_digits_le_push(x, m, n, 1);                // digits_le(x*m + 1)
        assert(repunit_m(c, m) == x * m + 1);
    }
}

/// The TM config for a 2-counter config `(c1, c2)` at state `q`: head on the separator, the two
/// counters as unary blocks left/right of the head.
pub open spec fn two_counter_config(c1: nat, c2: nat, q: nat, m: nat) -> TmConfig {
    TmConfig {
        u: repunit_m(c1, m),
        v: repunit_m(c2, m),
        a: sep(),
        q,
    }
}

/// **The layout config is well-formed.** For a TM with alphabet `n ≥ 2` (separator `2 ≤ n`), modulus
/// `m = tm.m`, and an in-range state `q < tm.m`, the encoded 2-counter config satisfies `tm_config_wf`
/// (scanned `≤ n`, state `< m`, both half-tapes carry only symbol-digits).
pub proof fn lemma_two_counter_config_wf(tm: Tm, c1: nat, c2: nat, q: nat)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q < tm.m,
    ensures
        tm_config_wf(tm, two_counter_config(c1, c2, q, tm.m)),
{
    reveal(tm_wf);
    let m = tm.m;
    let n = tm.n;
    // tm_wf gives 0 < n < m and m > 1.
    lemma_repunit_digits_le(c1, m, n);
    lemma_repunit_digits_le(c2, m, n);
    // a == sep() == 2 ≤ n; q < m.
}

} // verus!
