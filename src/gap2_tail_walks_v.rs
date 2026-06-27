//! # GAP-2 G2-F — RIGHT-tail (α-block) safety of the copy_refresh walk primitives (`v`-side mirror)
//!
//! Discharges [`crate::gap2_tail_lift_v::tail_safe_v`] for the homogeneous walk primitives of
//! `tm_copy_refresh` — the `v`-side analog of [`crate::gap2_tail_walks`]. The roles of L and R swap vs the
//! `u`-side: an **L-move pushes onto `v`** (the α-tail rides UP, unconditional), an **R-move pops `v`** (the
//! α-tail rides DOWN, needs offset `h ≥ 1`). So the *leftward* walks (`seek_left_blanks`, `run_walk_left`,
//! `unmark_fives_left`) are tail-safe **unconditionally** here (their offset RISES), and the *rightward*
//! walks (`seek_right_blanks`, `run_walk_right`) are the risky ones (offset FALLS, need `h ≥ len+1`).
//!
//! Each companion copies the matching [`crate::gap2_tail_walks`] proof's *value arithmetic* verbatim (the
//! gadget reads the same tape), swapping only the tail-tracking lift to the `v`-side. Fully verified, no
//! verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, apply_quint, quint_matches};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_two_counter::repunit_m;
use crate::tm_copy_refresh::lemma_pile_sym_div_mod;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::gap2_tail_lift_v::{tail_safe_v, tail_end_h_v, lemma_tail_unfold_v};

verus! {

/// **`seek_left_blanks` is `v`-tail-safe** for its `g+1` L-moves — UNCONDITIONAL (an L-move pushes onto `v`,
/// never popping the α-tail); offset RISES by `g+1`. `v`-side mirror of
/// [`crate::gap2_tail_walks::lemma_seek_left_tail_safe`] (same `u`-value arithmetic, tail rides up).
pub proof fn lemma_seek_left_tail_safe_v(
    tm: Tm, c: TmConfig, q_seek: nat, g: nat, r: nat, i0: int, h: nat,
)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == crate::tm_gadget::mk_quint(q_seek, 0, 0, q_seek, Dir::L),
        c.u == pow_nat(tm.m, g) * r,
        r % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tail_safe_v(tm, c, (g + 1) as nat, h),
        tail_end_h_v(tm, c, (g + 1) as nat, h) == (h + g + 1) as nat,
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    assert(quint_matches(tm.quints[i0], c));
    let c_next = apply_quint(tm.quints[i0], c, m);
    lemma_tail_unfold_v(tm, c, (g + 1) as nat, h, i0);
    // L branch (v-side): tail_safe_v(c,g+1,h) == tail_safe_v(c_next,g,h+1); UNCONDITIONAL.
    assert(c_next.u == c.u / m);
    assert(c_next.a == c.u % m);
    if g == 0 {
        assert(pow_nat(m, 0) == 1);
        assert(1nat * r == r) by(nonlinear_arith);
    } else {
        let r1 = pow_nat(m, (g - 1) as nat) * r;
        lemma_pow_nat_unfold(m, g);
        assert(c.u == m * r1) by(nonlinear_arith)
            requires c.u == pow_nat(m, g) * r, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                r1 == pow_nat(m, (g - 1) as nat) * r;
        assert(m * r1 == r1 * m) by(nonlinear_arith);
        lemma_div_mod_step(r1, m, 0);
        assert(c_next.u == r1);
        assert(c_next.a == 0);
        assert(c_next.q == q_seek);
        lemma_seek_left_tail_safe_v(tm, c_next, q_seek, (g - 1) as nat, r, i0, (h + 1) as nat);
        assert((h + 1 + g) as nat == (h + g + 1) as nat);
    }
}

/// **`run_walk_left` is `v`-tail-safe** for its `len+1` L-moves — UNCONDITIONAL; offset RISES by `len+1`.
/// `v`-side mirror of [`crate::gap2_tail_walks::lemma_run_walk_left_tail_safe`].
pub proof fn lemma_run_walk_left_tail_safe_v(
    tm: Tm, c: TmConfig, q_walk: nat, s: nat, len: nat, w: nat, i1: int, h: nat,
)
    requires
        tm_wf(tm),
        1 <= s <= tm.n,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == crate::tm_gadget::mk_quint(q_walk, s, s, q_walk, Dir::L),
        c.u == s * repunit_m(len, tm.m) + pow_nat(tm.m, len) * w,
        c.a == s,
        c.q == q_walk,
    ensures
        tail_safe_v(tm, c, (len + 1) as nat, h),
        tail_end_h_v(tm, c, (len + 1) as nat, h) == (h + len + 1) as nat,
    decreases len,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1 && s < m);
    assert(quint_matches(tm.quints[i1], c));
    let c_next = apply_quint(tm.quints[i1], c, m);
    lemma_tail_unfold_v(tm, c, (len + 1) as nat, h, i1);
    if len == 0 {
    } else {
        let x = s * repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        assert(repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1);
        lemma_pow_nat_unfold(m, len);
        assert(c.u == x * m + s) by(nonlinear_arith)
            requires
                c.u == s * repunit_m(len, m) + pow_nat(m, len) * w,
                repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1,
                pow_nat(m, len) == m * pow_nat(m, (len - 1) as nat),
                x == s * repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        lemma_div_mod_step(x, m, s);
        assert(c_next.u == x);
        assert(c_next.a == s);
        assert(c_next.q == q_walk);
        lemma_run_walk_left_tail_safe_v(tm, c_next, q_walk, s, (len - 1) as nat, w, i1, (h + 1) as nat);
        assert((h + 1 + len) as nat == (h + len + 1) as nat);
    }
}

/// **`unmark_fives_left` is `v`-tail-safe** for its `len+1` L-moves (`5→1`) — UNCONDITIONAL; offset RISES by
/// `len+1`. `v`-side mirror of [`crate::gap2_tail_walks::lemma_unmark_fives_left_tail_safe`].
pub proof fn lemma_unmark_fives_left_tail_safe_v(
    tm: Tm, c: TmConfig, q: nat, len: nat, w: nat, i1: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == crate::tm_gadget::mk_quint(q, 5, 1, q, Dir::L),
        c.u == 5 * repunit_m(len, tm.m) + pow_nat(tm.m, len) * w,
        c.a == 5,
        c.q == q,
    ensures
        tail_safe_v(tm, c, (len + 1) as nat, h),
        tail_end_h_v(tm, c, (len + 1) as nat, h) == (h + len + 1) as nat,
    decreases len,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    assert(quint_matches(tm.quints[i1], c));
    let c_next = apply_quint(tm.quints[i1], c, m);
    lemma_tail_unfold_v(tm, c, (len + 1) as nat, h, i1);
    if len == 0 {
    } else {
        let x = 5 * repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        assert(repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1);
        lemma_pow_nat_unfold(m, len);
        assert(c.u == x * m + 5) by(nonlinear_arith)
            requires
                c.u == 5 * repunit_m(len, m) + pow_nat(m, len) * w,
                repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1,
                pow_nat(m, len) == m * pow_nat(m, (len - 1) as nat),
                x == 5 * repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        lemma_div_mod_step(x, m, 5);
        assert(c_next.u == x);
        assert(c_next.a == 5);
        assert(c_next.q == q);
        lemma_unmark_fives_left_tail_safe_v(tm, c_next, q, (len - 1) as nat, w, i1, (h + 1) as nat);
        assert((h + 1 + len) as nat == (h + len + 1) as nat);
    }
}

/// **`seek_right_blanks` is `v`-tail-safe** for its `g+1` R-moves — RISKY (each R-move pops `v`); needs
/// entry offset `h ≥ g+1`, offset FALLS by `g+1`. `v`-side mirror of
/// [`crate::gap2_tail_walks::lemma_seek_right_tail_safe`] (same `v`-value arithmetic, tail rides down).
pub proof fn lemma_seek_right_tail_safe_v(
    tm: Tm, c: TmConfig, q_seek: nat, g: nat, rv: nat, i0: int, h: nat,
)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == crate::tm_gadget::mk_quint(q_seek, 0, 0, q_seek, Dir::R),
        c.v == pow_nat(tm.m, g) * rv,
        rv % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
        h >= g + 1,
    ensures
        tail_safe_v(tm, c, (g + 1) as nat, h),
        tail_end_h_v(tm, c, (g + 1) as nat, h) == (h - (g + 1)) as nat,
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    assert(quint_matches(tm.quints[i0], c));
    let c_next = apply_quint(tm.quints[i0], c, m);
    lemma_tail_unfold_v(tm, c, (g + 1) as nat, h, i0);
    // R branch (v-side): tail_safe_v(c,g+1,h) == (h>=1 && tail_safe_v(c_next,g,h-1)).
    if g == 0 {
        assert(pow_nat(m, 0) == 1);
        assert(1nat * rv == rv) by(nonlinear_arith);
    } else {
        let rv1 = pow_nat(m, (g - 1) as nat) * rv;
        lemma_pow_nat_unfold(m, g);
        assert(c.v == m * rv1) by(nonlinear_arith)
            requires c.v == pow_nat(m, g) * rv, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                rv1 == pow_nat(m, (g - 1) as nat) * rv;
        assert(m * rv1 == rv1 * m) by(nonlinear_arith);
        lemma_div_mod_step(rv1, m, 0);
        assert(c_next.v == rv1);
        assert(c_next.a == 0);
        assert(c_next.q == q_seek);
        lemma_seek_right_tail_safe_v(tm, c_next, q_seek, (g - 1) as nat, rv, i0, (h - 1) as nat);
        assert((h - 1 - g) as nat == (h - (g + 1)) as nat);
    }
}

/// **`run_walk_right` is `v`-tail-safe** for its `rem0+1` R-moves — RISKY; needs `h ≥ rem0+1`, offset FALLS
/// by `rem0+1`. `v`-side mirror of [`crate::gap2_tail_walks::lemma_run_walk_right_tail_safe`].
pub proof fn lemma_run_walk_right_tail_safe_v(
    tm: Tm, c: TmConfig, q_back: nat, s: nat, k0: nat, rem0: nat, w_pile: nat, w_hi: nat, i1b: int, h: nat,
)
    requires
        tm_wf(tm),
        1 <= s <= tm.n,
        0 <= i1b < tm.quints.len(),
        tm.quints[i1b] == crate::tm_gadget::mk_quint(q_back, s, s, q_back, Dir::R),
        c.u == s * repunit_m(k0, tm.m) + pow_nat(tm.m, k0) * w_hi,
        c.v == crate::tm_emit::pile_sym(w_pile, s, rem0, tm.m),
        c.a == s,
        c.q == q_back,
        h >= rem0 + 1,
    ensures
        tail_safe_v(tm, c, (rem0 + 1) as nat, h),
        tail_end_h_v(tm, c, (rem0 + 1) as nat, h) == (h - (rem0 + 1)) as nat,
    decreases rem0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1 && s < m);
    assert(quint_matches(tm.quints[i1b], c));
    let c_next = apply_quint(tm.quints[i1b], c, m);
    lemma_tail_unfold_v(tm, c, (rem0 + 1) as nat, h, i1b);
    let nk = (k0 + 1) as nat;
    if rem0 == 0 {
        assert((h - (0 + 1)) as nat == (h - 1) as nat);
    } else {
        lemma_pile_sym_div_mod(w_pile, s, rem0, m);
        assert(c_next.a == s);
        assert(c_next.v == crate::tm_emit::pile_sym(w_pile, s, (rem0 - 1) as nat, m));
        assert(repunit_m(nk, m) == m * repunit_m(k0, m) + 1);
        lemma_pow_nat_unfold(m, nk);
        assert(c_next.u == s * repunit_m(nk, m) + pow_nat(m, nk) * w_hi) by(nonlinear_arith)
            requires
                c.u == s * repunit_m(k0, m) + pow_nat(m, k0) * w_hi,
                c_next.u == c.u * m + s,
                repunit_m(nk, m) == m * repunit_m(k0, m) + 1,
                pow_nat(m, nk) == m * pow_nat(m, k0);
        assert(c_next.q == q_back);
        lemma_run_walk_right_tail_safe_v(tm, c_next, q_back, s, nk, (rem0 - 1) as nat, w_pile, w_hi, i1b,
            (h - 1) as nat);
        assert((h - 1 - (rem0 - 1)) as nat == (h - rem0) as nat);
    }
}

} // verus!
