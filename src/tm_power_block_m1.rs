//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the per-power-block step, `M = 1`.
//!
//! The `big_m = 1` (exponent `i = 1`, i.e. `exp = 0`) dispatch of the periodic power-block step
//! ([`crate::tm_power_block`]). The master is a single one; the copy is one `j = 0` iteration, so this uses
//! [`lemma_copy_refresh_m1`] (`g ≥ 3`) in place of the `M ≥ 2` [`crate::tm_copy_refresh::lemma_copy_refresh`].
//! Otherwise identical: rebuild a fresh single-cell temp, then consume it emitting `(blk)^1`, landing back at
//! `copy_u(0, 1, g)` (master stationary). Fixed gap `g = M + 2 = 3` keeps `block_loop`'s `w % m == 0`
//! separator (`w = m^(g−1)·R(1) = m^2·R(1)`).
//!
//! The `m1` copy lands DIRECTLY on the pivot (no temp-walk-right), so the bridge quint `i_one_r =
//! (q_urt,1,1,q_urt,R)` is a fresh `block_loop` quint here (no shared `i_urtemp`); `q_urt := q_loop` still
//! splices the two phases with no glue.
//!
//! `docs/gap2-input-loader-plan.md` §5 / §N+10. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_two_counter::repunit_m;
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold};
use crate::tm_dec_master::dec_u;
use crate::tm_block_loop::{loop_fuel_b1, lemma_block_loop_block1, loop_fuel_b3, lemma_block_loop_block3,
    lemma_dec_u_zero};
use crate::tm_copy_refresh::{copy_u, lemma_copy_refresh_m1, lemma_copy_u_start, lemma_pow_nat_add};
use crate::gap2_relnum_dds::seq_pow;

verus! {

/// Total fuel of one `M = 1` singleton power-block step: the copy-refresh-m1 rebuild (`6g + 12`) + the loop.
pub open spec fn power_block_fuel_b1_m1(g: nat, odlen: nat) -> nat {
    ((6 * g + 12) + loop_fuel_b1(odlen, 1)) as nat
}

/// **One singleton power-block `(s)^1`, the `M = 1` periodic step (`g ≥ 3`).** Mirror of
/// [`crate::tm_power_block::lemma_power_block_step_block1`] using [`lemma_copy_refresh_m1`].
pub proof fn lemma_power_block_step_block1_m1(
    tm: Tm, g: nat, od: Seq<nat>, s: nat,
    // ── copy_refresh_m1 states ──
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_t: nat, q_a: nat, q_b: nat, q_turn: nat, q_turng: nat, q_ret: nat, q_home: nat,
    q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    // ── block_loop states (q_loop := q_urt) ──
    q_guard: nat, q_iter: nat, q_surge: nat, q_eret: nat, q_bhome: nat, q_dwalk: nat, q_disc: nat,
    q_exit: nat,
    // ── copy_refresh_m1 quint indices ──
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_cpeel: int, i_ctemp: int, i_ct2g: int, i_cgap: int, i_cmark: int, i_crf2g: int, i_crgap: int,
    i_crg2t: int,
    i_tpeel: int, i_ttemp: int, i_tt2g: int, i_tgap: int, i_ta2b: int,
    i_tturn: int, i_tmaster: int, i_tm2g: int, i_trgap: int, i_tg2t: int,
    i_upeel: int, i_utemp: int, i_ut2g: int, i_ugap: int, i_uu1: int,
    i_uturn: int, i_umaster: int, i_um2g: int, i_urgap: int, i_ug2t: int,
    // ── block_loop quint indices ──
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        g >= 3,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        // ── copy_refresh_m1 index bounds ──
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        0 <= i_cpeel < tm.quints.len(),
        0 <= i_ctemp < tm.quints.len(),
        0 <= i_ct2g < tm.quints.len(),
        0 <= i_cgap < tm.quints.len(),
        0 <= i_cmark < tm.quints.len(),
        0 <= i_crf2g < tm.quints.len(),
        0 <= i_crgap < tm.quints.len(),
        0 <= i_crg2t < tm.quints.len(),
        0 <= i_tpeel < tm.quints.len(),
        0 <= i_ttemp < tm.quints.len(),
        0 <= i_tt2g < tm.quints.len(),
        0 <= i_tgap < tm.quints.len(),
        0 <= i_ta2b < tm.quints.len(),
        0 <= i_tturn < tm.quints.len(),
        0 <= i_tmaster < tm.quints.len(),
        0 <= i_tm2g < tm.quints.len(),
        0 <= i_trgap < tm.quints.len(),
        0 <= i_tg2t < tm.quints.len(),
        0 <= i_upeel < tm.quints.len(),
        0 <= i_utemp < tm.quints.len(),
        0 <= i_ut2g < tm.quints.len(),
        0 <= i_ugap < tm.quints.len(),
        0 <= i_uu1 < tm.quints.len(),
        0 <= i_uturn < tm.quints.len(),
        0 <= i_umaster < tm.quints.len(),
        0 <= i_um2g < tm.quints.len(),
        0 <= i_urgap < tm.quints.len(),
        0 <= i_ug2t < tm.quints.len(),
        // ── block_loop index bounds ──
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
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
        // ── copy_refresh_m1 quints (j=0 copy) ──
        tm.quints[i_dpeel] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_cpeel] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_ctemp] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_ct2g] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_cgap] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_cmark] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_crf2g] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_crgap] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_crg2t] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
        // ── copy_refresh_m1 quints (terminate; home == q_home) ──
        tm.quints[i_tpeel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_ttemp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_tt2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_tgap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_ta2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_tturn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_tmaster] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_tm2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_trgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_tg2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        // ── copy_refresh_m1 quints (unmark; home == q_ret) ──
        tm.quints[i_upeel] == mk_quint(q_ret, 0, 0, q_ut, Dir::L),
        tm.quints[i_utemp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_ut2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_ugap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_uu1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_uturn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_umaster] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_um2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_urgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_ug2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
        // ── block_loop quints (q_loop := q_urt) ──
        tm.quints[i_peek] == mk_quint(q_urt, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_bhome, Dir::L),
        tm.quints[il1] == mk_quint(q_bhome, 1, 1, q_bhome, Dir::L),
        tm.quints[il2] == mk_quint(q_bhome, 2, 2, q_bhome, Dir::L),
        tm.quints[il3] == mk_quint(q_bhome, 3, 3, q_bhome, Dir::L),
        tm.quints[il4] == mk_quint(q_bhome, 4, 4, q_bhome, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_bhome, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_urt, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_urt, 1, 1, q_urt, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b1_m1(g, od.len()))
            == (TmConfig { u: copy_u(0, 1, g, tm.m),
                v: dpack(od + seq_pow(seq![s], 1), tm.m), a: 0, q: q_exit }),
{
    let m = tm.m;
    reveal(tm_wf);
    assert(m > 4);
    let c0 = TmConfig { u: copy_u(0, 1, g, m), v: dpack(od, m), a: 0, q: q_dh0 };

    // ── PHASE A — COPY-REFRESH (M=1): copy_u(0,1,g) → dec_u(1, m^(g−1)·R(1)) @ q_urt. ──
    lemma_copy_refresh_m1(tm, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_t, q_a, q_b, q_turn, q_turng, q_ret, q_home,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b, i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t);
    let w = (pow_nat(m, (g - 1) as nat) * repunit_m(1, m)) as nat;
    let c1 = TmConfig { u: dec_u(1, w, m), v: dpack(od, m), a: 0, q: q_urt };
    assert(tm_run(tm, c0, (6 * g + 12) as nat) == c1);

    // ── w % m == 0: g − 1 ≥ 2 ⟹ m | m^(g−1) | w. ──
    assert(g - 1 >= 1);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    let xx = (pow_nat(m, (g - 1 - 1) as nat) * repunit_m(1, m)) as nat;
    assert(w == m * xx) by(nonlinear_arith)
        requires
            w == pow_nat(m, (g - 1) as nat) * repunit_m(1, m),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 1 - 1) as nat),
            xx == pow_nat(m, (g - 1 - 1) as nat) * repunit_m(1, m);
    assert(w % m == 0) by {
        assert(w == xx * m) by(nonlinear_arith) requires w == m * xx;
        lemma_div_mod_step(xx, m, 0);
    }

    // ── PHASE B — CONSUME LOOP (temp = 1): dec_u(1, w) @ q_urt → dec_u(0, m·w) @ q_exit. ──
    lemma_block_loop_block1(tm, 1, w, od, s,
        q_urt, q_guard, q_iter, q_surge, q_eret, q_bhome, q_dwalk, q_disc, q_exit,
        i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
    let c2 = TmConfig {
        u: dec_u(0, (pow_nat(m, 1) * w) as nat, m),
        v: dpack(od + seq_pow(seq![s], 1), m), a: 0, q: q_exit };
    assert(tm_run(tm, c1, loop_fuel_b1(od.len(), 1)) == c2);

    // ── dec_u(0, m·w) == copy_u(0,1,g): m^1·m^(g−1)·R(1) == m^g·R(1). ──
    lemma_dec_u_zero((pow_nat(m, 1) * w) as nat, m);
    lemma_pow_nat_add(m, 1, (g - 1) as nat);
    assert((1 + (g - 1)) as nat == g);
    lemma_copy_u_start(1, g, m);
    assert(dec_u(0, (pow_nat(m, 1) * w) as nat, m) == copy_u(0, 1, g, m)) by(nonlinear_arith)
        requires
            dec_u(0, (pow_nat(m, 1) * w) as nat, m) == pow_nat(m, 1) * w,
            w == pow_nat(m, (g - 1) as nat) * repunit_m(1, m),
            pow_nat(m, g) == pow_nat(m, 1) * pow_nat(m, (g - 1) as nat),
            copy_u(0, 1, g, m) == pow_nat(m, g) * repunit_m(1, m);
    assert(c2.u == copy_u(0, 1, g, m));

    // ── chain: COPY-REFRESH ∘ CONSUME-LOOP. ──
    lemma_tm_run_split(tm, c0, (6 * g + 12) as nat, loop_fuel_b1(od.len(), 1));
    assert(power_block_fuel_b1_m1(g, od.len())
        == ((6 * g + 12) + loop_fuel_b1(od.len(), 1)) as nat);
    assert(tm_run(tm, c0, power_block_fuel_b1_m1(g, od.len())) == c2);
}

/// Total fuel of one `M = 1` triple power-block step.
pub open spec fn power_block_fuel_b3_m1(g: nat, odlen: nat) -> nat {
    ((6 * g + 12) + loop_fuel_b3(odlen, 1)) as nat
}

/// **One triple power-block `(s0,s1,s2)^1`, the `M = 1` periodic step (`g ≥ 3`).** The 3-digit analog of
/// [`lemma_power_block_step_block1_m1`].
pub proof fn lemma_power_block_step_block3_m1(
    tm: Tm, g: nat, od: Seq<nat>, s0: nat, s1: nat, s2: nat,
    // ── copy_refresh_m1 states ──
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_t: nat, q_a: nat, q_b: nat, q_turn: nat, q_turng: nat, q_ret: nat, q_home: nat,
    q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    // ── block_loop states (q_loop := q_urt) ──
    q_guard: nat, q_iter: nat, q_surge: nat, q_e1: nat, q_e2: nat, q_eret: nat, q_bhome: nat,
    q_dwalk: nat, q_disc: nat, q_exit: nat,
    // ── copy_refresh_m1 quint indices ──
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_cpeel: int, i_ctemp: int, i_ct2g: int, i_cgap: int, i_cmark: int, i_crf2g: int, i_crgap: int,
    i_crg2t: int,
    i_tpeel: int, i_ttemp: int, i_tt2g: int, i_tgap: int, i_ta2b: int,
    i_tturn: int, i_tmaster: int, i_tm2g: int, i_trgap: int, i_tg2t: int,
    i_upeel: int, i_utemp: int, i_ut2g: int, i_ugap: int, i_uu1: int,
    i_uturn: int, i_umaster: int, i_um2g: int, i_urgap: int, i_ug2t: int,
    // ── block_loop quint indices ──
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_e0: int, i_e1: int, i_e2: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        g >= 3,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        // ── copy_refresh_m1 index bounds ──
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        0 <= i_cpeel < tm.quints.len(),
        0 <= i_ctemp < tm.quints.len(),
        0 <= i_ct2g < tm.quints.len(),
        0 <= i_cgap < tm.quints.len(),
        0 <= i_cmark < tm.quints.len(),
        0 <= i_crf2g < tm.quints.len(),
        0 <= i_crgap < tm.quints.len(),
        0 <= i_crg2t < tm.quints.len(),
        0 <= i_tpeel < tm.quints.len(),
        0 <= i_ttemp < tm.quints.len(),
        0 <= i_tt2g < tm.quints.len(),
        0 <= i_tgap < tm.quints.len(),
        0 <= i_ta2b < tm.quints.len(),
        0 <= i_tturn < tm.quints.len(),
        0 <= i_tmaster < tm.quints.len(),
        0 <= i_tm2g < tm.quints.len(),
        0 <= i_trgap < tm.quints.len(),
        0 <= i_tg2t < tm.quints.len(),
        0 <= i_upeel < tm.quints.len(),
        0 <= i_utemp < tm.quints.len(),
        0 <= i_ut2g < tm.quints.len(),
        0 <= i_ugap < tm.quints.len(),
        0 <= i_uu1 < tm.quints.len(),
        0 <= i_uturn < tm.quints.len(),
        0 <= i_umaster < tm.quints.len(),
        0 <= i_um2g < tm.quints.len(),
        0 <= i_urgap < tm.quints.len(),
        0 <= i_ug2t < tm.quints.len(),
        // ── block_loop index bounds ──
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
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
        // ── copy_refresh_m1 quints (j=0 copy) ──
        tm.quints[i_dpeel] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_cpeel] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_ctemp] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_ct2g] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_cgap] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_cmark] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_crf2g] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_crgap] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_crg2t] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
        // ── copy_refresh_m1 quints (terminate; home == q_home) ──
        tm.quints[i_tpeel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_ttemp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_tt2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_tgap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_ta2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_tturn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_tmaster] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_tm2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_trgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_tg2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        // ── copy_refresh_m1 quints (unmark; home == q_ret) ──
        tm.quints[i_upeel] == mk_quint(q_ret, 0, 0, q_ut, Dir::L),
        tm.quints[i_utemp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_ut2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_ugap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_uu1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_uturn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_umaster] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_um2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_urgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_ug2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
        // ── block_loop quints (q_loop := q_urt; triple emit) ──
        tm.quints[i_peek] == mk_quint(q_urt, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_e0] == mk_quint(q_surge, 0, s0, q_e1, Dir::R),
        tm.quints[i_e1] == mk_quint(q_e1, 0, s1, q_e2, Dir::R),
        tm.quints[i_e2] == mk_quint(q_e2, 0, s2, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_bhome, Dir::L),
        tm.quints[il1] == mk_quint(q_bhome, 1, 1, q_bhome, Dir::L),
        tm.quints[il2] == mk_quint(q_bhome, 2, 2, q_bhome, Dir::L),
        tm.quints[il3] == mk_quint(q_bhome, 3, 3, q_bhome, Dir::L),
        tm.quints[il4] == mk_quint(q_bhome, 4, 4, q_bhome, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_bhome, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_urt, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_urt, 1, 1, q_urt, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b3_m1(g, od.len()))
            == (TmConfig { u: copy_u(0, 1, g, tm.m),
                v: dpack(od + seq_pow(seq![s0, s1, s2], 1), tm.m), a: 0, q: q_exit }),
{
    let m = tm.m;
    reveal(tm_wf);
    assert(m > 4);
    let c0 = TmConfig { u: copy_u(0, 1, g, m), v: dpack(od, m), a: 0, q: q_dh0 };

    // ── PHASE A — COPY-REFRESH (M=1). ──
    lemma_copy_refresh_m1(tm, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_t, q_a, q_b, q_turn, q_turng, q_ret, q_home,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b, i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t);
    let w = (pow_nat(m, (g - 1) as nat) * repunit_m(1, m)) as nat;
    let c1 = TmConfig { u: dec_u(1, w, m), v: dpack(od, m), a: 0, q: q_urt };
    assert(tm_run(tm, c0, (6 * g + 12) as nat) == c1);

    // ── w % m == 0. ──
    assert(g - 1 >= 1);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    let xx = (pow_nat(m, (g - 1 - 1) as nat) * repunit_m(1, m)) as nat;
    assert(w == m * xx) by(nonlinear_arith)
        requires
            w == pow_nat(m, (g - 1) as nat) * repunit_m(1, m),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 1 - 1) as nat),
            xx == pow_nat(m, (g - 1 - 1) as nat) * repunit_m(1, m);
    assert(w % m == 0) by {
        assert(w == xx * m) by(nonlinear_arith) requires w == m * xx;
        lemma_div_mod_step(xx, m, 0);
    }

    // ── PHASE B — CONSUME LOOP (temp = 1, triple). ──
    lemma_block_loop_block3(tm, 1, w, od, s0, s1, s2,
        q_urt, q_guard, q_iter, q_surge, q_e1, q_e2, q_eret, q_bhome, q_dwalk, q_disc, q_exit,
        i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r);
    let c2 = TmConfig {
        u: dec_u(0, (pow_nat(m, 1) * w) as nat, m),
        v: dpack(od + seq_pow(seq![s0, s1, s2], 1), m), a: 0, q: q_exit };
    assert(tm_run(tm, c1, loop_fuel_b3(od.len(), 1)) == c2);

    // ── dec_u(0, m·w) == copy_u(0,1,g). ──
    lemma_dec_u_zero((pow_nat(m, 1) * w) as nat, m);
    lemma_pow_nat_add(m, 1, (g - 1) as nat);
    assert((1 + (g - 1)) as nat == g);
    lemma_copy_u_start(1, g, m);
    assert(dec_u(0, (pow_nat(m, 1) * w) as nat, m) == copy_u(0, 1, g, m)) by(nonlinear_arith)
        requires
            dec_u(0, (pow_nat(m, 1) * w) as nat, m) == pow_nat(m, 1) * w,
            w == pow_nat(m, (g - 1) as nat) * repunit_m(1, m),
            pow_nat(m, g) == pow_nat(m, 1) * pow_nat(m, (g - 1) as nat),
            copy_u(0, 1, g, m) == pow_nat(m, g) * repunit_m(1, m);
    assert(c2.u == copy_u(0, 1, g, m));

    // ── chain. ──
    lemma_tm_run_split(tm, c0, (6 * g + 12) as nat, loop_fuel_b3(od.len(), 1));
    assert(power_block_fuel_b3_m1(g, od.len())
        == ((6 * g + 12) + loop_fuel_b3(od.len(), 1)) as nat);
    assert(tm_run(tm, c0, power_block_fuel_b3_m1(g, od.len())) == c2);
}

} // verus!
