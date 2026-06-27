//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the per-block iteration.
//!
//! Model B's emitter lays one `fam_digits` block onto the output per loop iteration, the head shuttling on
//! a fixed `[masters U] 0(pivot) [output] 0 [blanks]` tape. This file assembles ONE iteration from the
//! verified halves:
//!   - **surge** ([`lemma_surge`]): move R off the pivot, [`crate::tm_dwalk::lemma_dwalk_right`] over the
//!     output to the frontier — the output moves `v → u`, head at the first blank past it (`v == 0`).
//!   - **emit** ([`crate::tm_shuttle`]): a state cycle writes the block's digits onto `u` over the frontier.
//!   - **return** ([`lemma_return_walk`]): move L off the frontier, [`crate::tm_dwalk_prefix::lemma_dwalk_left_prefix`]
//!     back to the pivot — the output (now `output ++ blk`) moves `u → v`, masters `U` left intact. The two
//!     walks cancel the per-walk reversal, so the home output comes out `dpack(output ++ blk)` clean (the
//!     `drev` involution bridge).
//!   - **dec_temp** ([`crate::tm_dec_master::lemma_dec_temp`]): decrement the active counter at home.
//!
//! [`lemma_surge_emit_return_block1`]/`_block3` are the surge∘emit∘return composite for the only
//! `fam_digits` block sizes (1 and 3); [`lemma_block_iter_block1`]/`_block3` splice on `dec_temp` for the
//! full home→home iteration (`output ↦ output ++ blk`, `temp ↦ temp − 1`). The per-block LOOP (induct on
//! `temp`) builds on these next.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_dstring::{dpack, dpile, pow_nat, lemma_pow_nat_unfold, lemma_dpack_pop};
use crate::tm_dwalk::{lemma_dwalk_right};
use crate::tm_dwalk_prefix::{drev, lemma_drev_len, lemma_drev_digit_bound, lemma_drev_involution,
    lemma_dpile_is_dpack_drev, lemma_dpile_zero_drev, lemma_dpile_concat, lemma_dwalk_left_prefix};
use crate::tm_shuttle::{lemma_emit_block1_frontier, lemma_emit_block3_frontier};
use crate::tm_dec_master::{dec_u, lemma_dec_temp};
use verus_group_theory::word_numbering::lemma_div_mod_step;

verus! {

// ============================================================================
// the surge (home → frontier) and return (frontier → home) halves
// ============================================================================

/// **The surge half.** From home `{u: U, v: dpack(od), a: 0, q: q_iter}` (head on the pivot `0` before the
/// output `od`, digits `1..4`), one move-R off the pivot plus [`lemma_dwalk_right`] over `od` lands the head
/// at the frontier `{u: dpile(U·m, od), v: 0, a: 0, q: q_surge}` — the output pushed onto `u` atop the
/// pivot-0, head on the first blank past it. Handles `od` empty (no walk, the move-R already lands at the
/// frontier) and nonempty uniformly: `od.len() + 1` steps either way.
pub proof fn lemma_surge(
    tm: Tm, big_u: nat, od: Seq<nat>, q_iter: nat, q_surge: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
    ensures
        tm_run(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter }, (od.len() + 1) as nat)
            == (TmConfig { u: dpile(big_u * tm.m, od, tm.m), v: 0, a: 0, q: q_surge }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };
    // ── step 1: move-R off the pivot (q_iter, 0, 0, q_surge, R). ──
    assert(quint_matches(tm.quints[i_pivot_r], c0));
    lemma_tm_step_picks(tm, c0, i_pivot_r);
    let c1 = apply_quint(tm.quints[i_pivot_r], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    // R-move a2 == 0: u = big_u·m + 0, v = dpack(od)/m, a = dpack(od)%m.
    assert(c1.u == big_u * m);
    assert(c1.q == q_surge);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);

    if od.len() == 0 {
        assert(od =~= Seq::<nat>::empty());
        assert(dpack(od, m) == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c1.v == 0);
        assert(c1.a == 0);
        assert(dpile(big_u * m, od, m) == big_u * m);   // dpile(_, empty) == _
        assert(c1 == (TmConfig { u: dpile(big_u * m, od, m), v: 0, a: 0, q: q_surge }));
        assert((od.len() + 1) as nat == 1);
    } else {
        assert(od[0] <= 4);
        assert(od[0] < m);
        lemma_dpack_pop(od, m);   // dpack(od)%m == od[0], /m == dpack(od.drop_first())
        assert(c1.v == dpack(od.drop_first(), m));
        assert(c1.a == od[0]);
        lemma_dwalk_right(tm, c1, q_surge, od, ir1, ir2, ir3, ir4);
        let c2 = TmConfig { u: dpile(c1.u, od, m), v: 0, a: 0, q: q_surge };
        assert(tm_run(tm, c1, od.len()) == c2);
        lemma_tm_run_split(tm, c0, 1, od.len());
        assert((1 + od.len()) as nat == (od.len() + 1) as nat);
    }
}

/// **The return half.** From the post-emit frontier `{u: dpile(U·m, combined), v: 0, a: 0, q: q_eret}`
/// (`combined == output ++ blk`, digits `1..4`), one move-L off the frontier plus
/// [`lemma_dwalk_left_prefix`] back over `combined` lands home `{u: U, v: dpack(combined), a: 0, q: q_home}`
/// — the masters `U` left intact, the output value `dpack`-clean (the surge's reversal cancelled). Uses the
/// `drev` bridges: `dpile(U·m, combined) == U·m·m^N + dpack(drev(combined))` (to read the post-emit `u`),
/// and `dpile(0, drev(combined)) == dpack(drev(drev(combined))) == dpack(combined)` (the involution). `N+1`
/// steps.
pub proof fn lemma_return_walk(
    tm: Tm, big_u: nat, combined: Seq<nat>, q_eret: nat, q_home: nat,
    i_off_l: int, il1: int, il2: int, il3: int, il4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        combined.len() >= 1,
        forall|k: int| 0 <= k < combined.len() ==> 1 <= #[trigger] combined[k] <= 4,
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: dpile(big_u * tm.m, combined, tm.m), v: 0, a: 0, q: q_eret },
            (combined.len() + 1) as nat)
            == (TmConfig { u: big_u, v: dpack(combined, tm.m), a: 0, q: q_home }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let n = combined.len();
    let c3 = TmConfig { u: dpile(big_u * m, combined, m), v: 0, a: 0, q: q_eret };
    // ── step 1: move-L off the frontier (q_eret, 0, 0, q_home, L). ──
    assert(quint_matches(tm.quints[i_off_l], c3));
    lemma_tm_step_picks(tm, c3, i_off_l);
    let c4 = apply_quint(tm.quints[i_off_l], c3, m);
    assert(tm_step(tm, c3) == Some(c4));
    // L-move a2 == 0: u = c3.u/m, v = 0·m + 0 = 0, a = c3.u%m, q = q_home.
    assert(c4.v == 0);
    assert(c4.q == q_home);
    assert(tm_run(tm, c4, 0) == c4);
    assert(tm_run(tm, c3, 1) == c4);

    // read c3.u via the reversal bridge.
    lemma_dpile_is_dpack_drev(big_u * m, combined, m);   // c3.u == (big_u·m)·m^n + dpack(drev(combined))
    let dr = drev(combined);
    lemma_drev_len(combined);                            // dr.len() == n
    lemma_drev_digit_bound(combined, 4);                 // dr digits 1..4
    assert(dr.len() == n);
    assert(dr.len() >= 1);
    assert(dr[0] <= 4);
    assert(dr[0] < m);
    // dpack(dr) == dr[0] + m·dpack(dr.drop_first());  (big_u·m)·m^n == m·(big_u·m^n).
    assert(dpack(dr, m) == dr[0] + m * dpack(dr.drop_first(), m));
    assert((big_u * m) * pow_nat(m, n) == m * (big_u * pow_nat(m, n))) by(nonlinear_arith);
    let qd = big_u * pow_nat(m, n) + dpack(dr.drop_first(), m);
    assert(c3.u == qd * m + dr[0]) by(nonlinear_arith)
        requires
            c3.u == (big_u * m) * pow_nat(m, n) + dpack(dr, m),
            dpack(dr, m) == dr[0] + m * dpack(dr.drop_first(), m),
            (big_u * m) * pow_nat(m, n) == m * (big_u * pow_nat(m, n)),
            qd == big_u * pow_nat(m, n) + dpack(dr.drop_first(), m);
    lemma_div_mod_step(qd, m, dr[0]);   // (qd·m + dr[0])/m == qd, %m == dr[0]  (dr[0] < m)
    assert(c4.u == qd);
    assert(c4.a == dr[0]);

    // match dwalk_left_prefix's precondition with blk := dr, w := m·big_u.
    lemma_pow_nat_unfold(m, n);   // m^n == m·m^{n-1}
    assert(big_u * pow_nat(m, n) == pow_nat(m, (n - 1) as nat) * (m * big_u)) by(nonlinear_arith)
        requires pow_nat(m, n) == m * pow_nat(m, (n - 1) as nat);
    assert((n - 1) as nat == (dr.len() - 1) as nat);
    assert(c4.u == dpack(dr.drop_first(), m) + pow_nat(m, (dr.len() - 1) as nat) * (m * big_u));
    // (m·big_u)%m == 0 and (m·big_u)/m == big_u  (via lemma_div_mod_step on big_u with residue 0).
    assert(m * big_u == big_u * m + 0) by(nonlinear_arith);
    lemma_div_mod_step(big_u, m, 0);
    assert((m * big_u) % m == 0);
    assert((m * big_u) / m == big_u);

    lemma_dwalk_left_prefix(tm, c4, q_home, dr, (m * big_u) as nat, il1, il2, il3, il4);
    let c5 = TmConfig { u: (m * big_u) / m, v: dpile(c4.v, dr, m), a: (m * big_u) % m, q: q_home };
    assert(tm_run(tm, c4, dr.len()) == c5);
    // c5.v == dpile(0, dr) == dpack(drev(dr)) == dpack(combined).
    lemma_dpile_zero_drev(dr, m);     // dpile(0, dr) == dpack(drev(dr))
    lemma_drev_involution(combined);  // drev(dr) == drev(drev(combined)) == combined
    assert(c4.v == 0);
    assert(dpile(c4.v, dr, m) == dpack(combined, m));
    assert(c5 == (TmConfig { u: big_u, v: dpack(combined, m), a: 0, q: q_home }));
    lemma_tm_run_split(tm, c3, 1, dr.len());
    assert((1 + n) as nat == (n + 1) as nat);
}

// ============================================================================
// surge ∘ emit ∘ return  (the only fam_digits block sizes: 1 and 3)
// ============================================================================

/// **One singleton-block surge∘emit∘return.** Home `{u: U, v: dpack(od), a: 0, q: q_iter}` →
/// home `{u: U, v: dpack(od ++ [s]), a: 0, q: q_home}` in `2·|od| + 4` steps: surge, emit the digit `s` at
/// the frontier ([`lemma_emit_block1_frontier`]), return. The output gains the single digit `s` at its high
/// (frontier) end; the masters `U` are preserved.
pub proof fn lemma_surge_emit_return_block1(
    tm: Tm, big_u: nat, od: Seq<nat>, s: nat,
    q_iter: nat, q_surge: nat, q_eret: nat, q_home: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_emit < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter }, (2 * od.len() + 4) as nat)
            == (TmConfig { u: big_u, v: dpack(od + seq![s], tm.m), a: 0, q: q_home }),
{
    let m = tm.m;
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };
    // ── surge ──
    lemma_surge(tm, big_u, od, q_iter, q_surge, i_pivot_r, ir1, ir2, ir3, ir4);
    let c2 = TmConfig { u: dpile(big_u * m, od, m), v: 0, a: 0, q: q_surge };
    assert(tm_run(tm, c0, (od.len() + 1) as nat) == c2);
    // ── emit s ──
    lemma_emit_block1_frontier(tm, c2, q_surge, s, q_eret, i_emit);
    let combined = od + seq![s];
    let c3 = TmConfig { u: dpile(c2.u, seq![s], m), v: 0, a: 0, q: q_eret };
    assert(tm_run(tm, c2, 1) == c3);
    lemma_dpile_concat(big_u * m, od, seq![s], m);   // dpile(big_u·m, od+[s]) == dpile(dpile(big_u·m,od),[s])
    assert(c3.u == dpile(big_u * m, combined, m));
    // ── return ──
    assert(combined.len() == od.len() + 1);
    assert forall|k: int| 0 <= k < combined.len() implies 1 <= #[trigger] combined[k] <= 4 by {
        if k < od.len() { assert(combined[k] == od[k]); } else { assert(combined[k] == s); }
    }
    lemma_return_walk(tm, big_u, combined, q_eret, q_home, i_off_l, il1, il2, il3, il4);
    let c5 = TmConfig { u: big_u, v: dpack(combined, m), a: 0, q: q_home };
    assert(tm_run(tm, c3, (combined.len() + 1) as nat) == c5);
    // ── chain: c0 →(|od|+1) c2 →(1) c3 →(|combined|+1) c5 ──
    lemma_tm_run_split(tm, c0, (od.len() + 1) as nat, 1);
    assert((od.len() + 1 + 1) as nat == (od.len() + 2) as nat);
    assert(tm_run(tm, c0, (od.len() + 2) as nat) == c3);
    lemma_tm_run_split(tm, c0, (od.len() + 2) as nat, (combined.len() + 1) as nat);
    assert((od.len() + 2 + (combined.len() + 1)) as nat == (2 * od.len() + 4) as nat);
}

/// **One triple-block surge∘emit∘return.** Home → home in `2·|od| + 8` steps, emitting `[s0,s1,s2]` at the
/// frontier ([`lemma_emit_block3_frontier`]). The `fam_digits` triple blocks are `[4,1,2]` and `[4,3,2]`.
pub proof fn lemma_surge_emit_return_block3(
    tm: Tm, big_u: nat, od: Seq<nat>, s0: nat, s1: nat, s2: nat,
    q_iter: nat, q_surge: nat, q_e1: nat, q_e2: nat, q_eret: nat, q_home: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_e0: int, i_e1: int, i_e2: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_e0 < tm.quints.len(),
        0 <= i_e1 < tm.quints.len(),
        0 <= i_e2 < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_e0] == mk_quint(q_surge, 0, s0, q_e1, Dir::R),
        tm.quints[i_e1] == mk_quint(q_e1, 0, s1, q_e2, Dir::R),
        tm.quints[i_e2] == mk_quint(q_e2, 0, s2, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
    ensures
        tm_run(tm, TmConfig { u: big_u, v: dpack(od, tm.m), a: 0, q: q_iter }, (2 * od.len() + 8) as nat)
            == (TmConfig { u: big_u, v: dpack(od + seq![s0, s1, s2], tm.m), a: 0, q: q_home }),
{
    let m = tm.m;
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };
    // ── surge ──
    lemma_surge(tm, big_u, od, q_iter, q_surge, i_pivot_r, ir1, ir2, ir3, ir4);
    let c2 = TmConfig { u: dpile(big_u * m, od, m), v: 0, a: 0, q: q_surge };
    assert(tm_run(tm, c0, (od.len() + 1) as nat) == c2);
    // ── emit [s0,s1,s2] ──
    lemma_emit_block3_frontier(tm, c2, q_surge, s0, s1, s2, q_e1, q_e2, q_eret, i_e0, i_e1, i_e2);
    let blk = seq![s0, s1, s2];
    let combined = od + blk;
    let c3 = TmConfig { u: dpile(c2.u, blk, m), v: 0, a: 0, q: q_eret };
    assert(tm_run(tm, c2, 3) == c3);
    lemma_dpile_concat(big_u * m, od, blk, m);   // dpile(big_u·m, od+blk) == dpile(dpile(big_u·m,od),blk)
    assert(c3.u == dpile(big_u * m, combined, m));
    // ── return ──
    assert(blk.len() == 3);
    assert(combined.len() == od.len() + 3);
    assert forall|k: int| 0 <= k < combined.len() implies 1 <= #[trigger] combined[k] <= 4 by {
        if k < od.len() {
            assert(combined[k] == od[k]);
        } else {
            assert(combined[k] == blk[k - od.len()]);
        }
    }
    lemma_return_walk(tm, big_u, combined, q_eret, q_home, i_off_l, il1, il2, il3, il4);
    let c5 = TmConfig { u: big_u, v: dpack(combined, m), a: 0, q: q_home };
    assert(tm_run(tm, c3, (combined.len() + 1) as nat) == c5);
    // ── chain: c0 →(|od|+1) c2 →(3) c3 →(|combined|+1) c5 ──
    lemma_tm_run_split(tm, c0, (od.len() + 1) as nat, 3);
    assert((od.len() + 1 + 3) as nat == (od.len() + 4) as nat);
    assert(tm_run(tm, c0, (od.len() + 4) as nat) == c3);
    lemma_tm_run_split(tm, c0, (od.len() + 4) as nat, (combined.len() + 1) as nat);
    assert((od.len() + 4 + (combined.len() + 1)) as nat == (2 * od.len() + 8) as nat);
}

// ============================================================================
// the full per-block iteration: surge ∘ emit ∘ return ∘ dec_temp
// ============================================================================

/// **One singleton-block iteration.** From home `{u: dec_u(temp, w), v: dpack(od), a: 0, q: q_iter}`
/// (`temp ≥ 1`, `w % m == 0`), emits the digit `s` onto the output AND decrements the active counter:
/// lands `{u: dec_u(temp − 1, m·w), v: dpack(od ++ [s]), a: 0, q: q_back}` in `2·|od| + 2·temp + 6` steps.
/// Composes [`lemma_surge_emit_return_block1`] (`U = dec_u(temp, w)`, output `↦ od ++ [s]`) with
/// [`lemma_dec_temp`] (the master-decrement, output preserved). The per-block loop induct on `temp`.
pub proof fn lemma_block_iter_block1(
    tm: Tm, temp: nat, w: nat, od: Seq<nat>, s: nat,
    q_iter: nat, q_surge: nat, q_eret: nat, q_home: nat, q_dwalk: nat, q_disc: nat, q_back: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        temp >= 1,
        w % tm.m == 0,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_emit < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_iter },
            (2 * od.len() + 2 * temp + 6) as nat)
            == (TmConfig { u: dec_u((temp - 1) as nat, (tm.m * w) as nat, tm.m),
                v: dpack(od + seq![s], tm.m), a: 0, q: q_back }),
{
    let m = tm.m;
    let big_u = dec_u(temp, w, m);
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };
    // ── surge ∘ emit ∘ return: output od ↦ od ++ [s], masters preserved ──
    lemma_surge_emit_return_block1(tm, big_u, od, s, q_iter, q_surge, q_eret, q_home,
        i_pivot_r, ir1, ir2, ir3, ir4, i_emit, i_off_l, il1, il2, il3, il4);
    let out2 = dpack(od + seq![s], m);
    let c_mid = TmConfig { u: big_u, v: out2, a: 0, q: q_home };
    assert(tm_run(tm, c0, (2 * od.len() + 4) as nat) == c_mid);
    // ── dec_temp: temp ↦ temp − 1, output preserved ──
    lemma_dec_temp(tm, temp, w, out2, q_home, q_dwalk, q_disc, q_back,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
    let c_end = TmConfig { u: dec_u((temp - 1) as nat, (m * w) as nat, m), v: out2, a: 0, q: q_back };
    assert(tm_run(tm, c_mid, (2 * temp + 2) as nat) == c_end);
    // ── chain ──
    lemma_tm_run_split(tm, c0, (2 * od.len() + 4) as nat, (2 * temp + 2) as nat);
    assert((2 * od.len() + 4 + (2 * temp + 2)) as nat == (2 * od.len() + 2 * temp + 6) as nat);
}

/// **One triple-block iteration.** Like [`lemma_block_iter_block1`] but emits the triple `[s0,s1,s2]`
/// (the `fam_digits` triple blocks `[4,1,2]`, `[4,3,2]`): output `↦ od ++ [s0,s1,s2]`, `temp ↦ temp − 1`,
/// in `2·|od| + 2·temp + 10` steps. Composes [`lemma_surge_emit_return_block3`] with [`lemma_dec_temp`].
pub proof fn lemma_block_iter_block3(
    tm: Tm, temp: nat, w: nat, od: Seq<nat>, s0: nat, s1: nat, s2: nat,
    q_iter: nat, q_surge: nat, q_e1: nat, q_e2: nat, q_eret: nat, q_home: nat,
    q_dwalk: nat, q_disc: nat, q_back: nat,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_e0: int, i_e1: int, i_e2: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        temp >= 1,
        w % tm.m == 0,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_e0 < tm.quints.len(),
        0 <= i_e1 < tm.quints.len(),
        0 <= i_e2 < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_e0] == mk_quint(q_surge, 0, s0, q_e1, Dir::R),
        tm.quints[i_e1] == mk_quint(q_e1, 0, s1, q_e2, Dir::R),
        tm.quints[i_e2] == mk_quint(q_e2, 0, s2, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_iter },
            (2 * od.len() + 2 * temp + 10) as nat)
            == (TmConfig { u: dec_u((temp - 1) as nat, (tm.m * w) as nat, tm.m),
                v: dpack(od + seq![s0, s1, s2], tm.m), a: 0, q: q_back }),
{
    let m = tm.m;
    let big_u = dec_u(temp, w, m);
    let c0 = TmConfig { u: big_u, v: dpack(od, m), a: 0, q: q_iter };
    lemma_surge_emit_return_block3(tm, big_u, od, s0, s1, s2,
        q_iter, q_surge, q_e1, q_e2, q_eret, q_home,
        i_pivot_r, ir1, ir2, ir3, ir4, i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4);
    let out2 = dpack(od + seq![s0, s1, s2], m);
    let c_mid = TmConfig { u: big_u, v: out2, a: 0, q: q_home };
    assert(tm_run(tm, c0, (2 * od.len() + 8) as nat) == c_mid);
    lemma_dec_temp(tm, temp, w, out2, q_home, q_dwalk, q_disc, q_back,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
    let c_end = TmConfig { u: dec_u((temp - 1) as nat, (m * w) as nat, m), v: out2, a: 0, q: q_back };
    assert(tm_run(tm, c_mid, (2 * temp + 2) as nat) == c_end);
    lemma_tm_run_split(tm, c0, (2 * od.len() + 8) as nat, (2 * temp + 2) as nat);
    assert((2 * od.len() + 8 + (2 * temp + 2)) as nat == (2 * od.len() + 2 * temp + 10) as nat);
}

} // verus!
