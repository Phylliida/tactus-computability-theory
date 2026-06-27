//! # GAP-2 G2-F — tail-safety of the per-power-block PERIODIC step (`power_block` upper half)
//!
//! The 8-block phase-1 emission (`uinv_phase`) carries the `a+1` backup as a preserved high tail
//! `m^H·T` on the left tape `u`. Each power-block step is `copy_refresh ∘ block_loop`; this module
//! discharges its [`tail_safe`] by the **2-piece chain** — [`lemma_copy_refresh_tail_safe`]
//! ([`crate::gap2_tail_phase1`]) ∘ [`lemma_block_loop_block1_tail_safe`]
//! ([`crate::gap2_tail_emit`]) — at the constant home offset `H_0 = g + M + 1`. Both pieces are
//! net-displacement-0, so the chained step is too: the master returns to gap `g`, the tail to `H_0`.
//!
//! **The bridge is the black box.** `lemma_run_tail` never inspects the value arithmetic; the only
//! obligations are `tm_run(c0, copy_refresh_fuel) == c1` (so the second segment's entry config is
//! `tm_run` of the first) and the two segment companions, chained by [`lemma_tail_chain`]. The
//! signature is the source [`crate::tm_power_block::lemma_power_block_step_block1`]'s requires
//! VERBATIM; only the `ensures` (→ tail_safe) and the body (→ 2-piece chain) differ.
//!
//! `docs/gap2-input-loader-plan.md` §N+14. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_two_counter::repunit_m;
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold};
use crate::tm_dec_master::dec_u;
use crate::tm_block_loop::{loop_fuel_b1, loop_fuel_b3};
use crate::tm_copy_refresh::{copy_u, copy_refresh_fuel, lemma_copy_refresh};
use crate::tm_power_block::{power_block_fuel_b1, power_block_fuel_b3};
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_tail_chain};
use crate::gap2_tail_phase1::lemma_copy_refresh_tail_safe;
use crate::gap2_tail_emit::{lemma_block_loop_block1_tail_safe, lemma_block_loop_block3_tail_safe};

use crate::tm_copy_refresh::lemma_copy_refresh_m1;
use crate::tm_power_block_m1::{power_block_fuel_b1_m1, power_block_fuel_b3_m1};
use crate::gap2_tail_phase1_m1::lemma_copy_refresh_m1_tail_safe;

verus! {

/// **`lemma_power_block_step_block1` is tail-safe** for its `power_block_fuel_b1` steps at the home
/// offset `H_0 = g + M + 1`, net-displacement-0. The 2-piece chain: copy-refresh rebuild
/// ([`lemma_copy_refresh_tail_safe`]) ∘ consuming loop ([`lemma_block_loop_block1_tail_safe`]),
/// each net-disp-0 at `H_0`. The loop's `h ≥ temp+1` margin holds trivially (`H_0 ≥ M+1`).
pub proof fn lemma_power_block_step_block1_tail_safe(
    tm: Tm, big_m: nat, g: nat, od: Seq<nat>, s: nat,
    // ── copy_refresh states ──
    // j=0 deposit-first
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    // home-cycle (q_home here is the COPY-side home, distinct from the loop's q_bhome)
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    // terminate walk-back
    q_turn: nat, q_turng: nat, q_ret: nat,
    // unmark (q_urt is the SHARED bridge state = the loop's q_loop)
    q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    // ── block_loop states (q_loop := q_urt) ──
    q_guard: nat, q_iter: nat, q_surge: nat, q_eret: nat, q_bhome: nat, q_dwalk: nat, q_disc: nat,
    q_exit: nat,
    // ── copy_refresh quint indices ──
    i_dpeel0: int, i_dtemp0: int, i_dins0: int, i_dwb0: int,
    i_peel0: int, i_temp0: int, i_t2g0: int, i_gap0: int, i_mark0: int, i_rf2g0: int, i_rgap0: int,
    i_rg2t0: int,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_turn: int, i_master: int, i_tm2g: int, i_trgap: int, i_tg2t: int, i_trtemp: int,
    i_upeel: int, i_utemp: int, i_ut2g: int, i_ugap: int, i_uu1: int, i_uurest: int,
    i_uturn: int, i_umaster: int, i_um2g: int, i_urgap: int, i_ug2t: int, i_urtemp: int,
    // ── block_loop quint indices (i_one_r := i_urtemp) ──
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        // ── copy_refresh index bounds ──
        0 <= i_dpeel0 < tm.quints.len(),
        0 <= i_dtemp0 < tm.quints.len(),
        0 <= i_dins0 < tm.quints.len(),
        0 <= i_dwb0 < tm.quints.len(),
        0 <= i_peel0 < tm.quints.len(),
        0 <= i_temp0 < tm.quints.len(),
        0 <= i_t2g0 < tm.quints.len(),
        0 <= i_gap0 < tm.quints.len(),
        0 <= i_mark0 < tm.quints.len(),
        0 <= i_rf2g0 < tm.quints.len(),
        0 <= i_rgap0 < tm.quints.len(),
        0 <= i_rg2t0 < tm.quints.len(),
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_tm2g < tm.quints.len(),
        0 <= i_trgap < tm.quints.len(),
        0 <= i_tg2t < tm.quints.len(),
        0 <= i_trtemp < tm.quints.len(),
        0 <= i_upeel < tm.quints.len(),
        0 <= i_utemp < tm.quints.len(),
        0 <= i_ut2g < tm.quints.len(),
        0 <= i_ugap < tm.quints.len(),
        0 <= i_uu1 < tm.quints.len(),
        0 <= i_uurest < tm.quints.len(),
        0 <= i_uturn < tm.quints.len(),
        0 <= i_umaster < tm.quints.len(),
        0 <= i_um2g < tm.quints.len(),
        0 <= i_urgap < tm.quints.len(),
        0 <= i_ug2t < tm.quints.len(),
        0 <= i_urtemp < tm.quints.len(),
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
        // ── copy_refresh quints (j=0 deposit-first) ──
        tm.quints[i_dpeel0] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp0] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins0] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb0] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_peel0] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp0] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g0] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap0] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark0] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g0] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap0] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t0] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
        // ── copy_refresh quints (home-cycle) ──
        tm.quints[i_peel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_mark] == mk_quint(q_b, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
        tm.quints[i_dpeel] == mk_quint(q_rt, 0, 0, q_dw, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw, 0, 1, q_home, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_home, 1, 1, q_home, Dir::R),
        // ── copy_refresh quints (terminate walk-back) ──
        tm.quints[i_turn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_master] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_tm2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_trgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_tg2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        tm.quints[i_trtemp] == mk_quint(q_ret, 1, 1, q_ret, Dir::R),
        // ── copy_refresh quints (unmark; home == q_ret) ──
        tm.quints[i_upeel] == mk_quint(q_ret, 0, 0, q_ut, Dir::L),
        tm.quints[i_utemp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_ut2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_ugap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_uu1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_uurest] == mk_quint(q_uf, 5, 1, q_uf, Dir::L),
        tm.quints[i_uturn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_umaster] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_um2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_urgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_ug2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
        tm.quints[i_urtemp] == mk_quint(q_urt, 1, 1, q_urt, Dir::R),
        // ── block_loop quints (q_loop := q_urt, i_one_r := i_urtemp) ──
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
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b1(big_m, g, od.len()), (g + big_m + 1) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b1(big_m, g, od.len()), (g + big_m + 1) as nat)
            == (g + big_m + 1) as nat,
{
    let m = tm.m;
    reveal(tm_wf);
    let h0 = (g + big_m + 1) as nat;
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: dpack(od, m), a: 0, q: q_dh0 };

    // ── PHASE A — COPY-REFRESH bridge: tm_run(c0, crf) == c1, tail_safe at h0 → h0. ──
    lemma_copy_refresh(tm, big_m, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        q_turn, q_turng, q_ret,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp);
    let w = (pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m)) as nat;
    let c1 = TmConfig { u: dec_u(big_m, w, m), v: dpack(od, m), a: 0, q: q_urt };
    assert(tm_run(tm, c0, copy_refresh_fuel(big_m, g)) == c1);
    lemma_copy_refresh_tail_safe(tm, big_m, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        q_turn, q_turng, q_ret,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp);

    // ── w % m == 0 (the loop's separator): g − M ≥ 2 ⟹ m | m^(g−M) | w. ──
    assert(g - big_m >= 1);
    lemma_pow_nat_unfold(m, (g - big_m) as nat);
    let xx = (pow_nat(m, (g - big_m - 1) as nat) * repunit_m(big_m, m)) as nat;
    assert(w == m * xx) by(nonlinear_arith)
        requires
            w == pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat),
            xx == pow_nat(m, (g - big_m - 1) as nat) * repunit_m(big_m, m);
    assert(w % m == 0) by {
        assert(w == xx * m) by(nonlinear_arith) requires w == m * xx;
        lemma_div_mod_step(xx, m, 0);
    }

    // ── PHASE B — CONSUME LOOP: tail_safe(c1, loop_fuel, h0) → h0. ──
    lemma_block_loop_block1_tail_safe(tm, big_m, w, od, s,
        q_urt, q_guard, q_iter, q_surge, q_eret, q_bhome, q_dwalk, q_disc, q_exit,
        i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_urtemp, h0);

    // ── chain: COPY-REFRESH ∘ CONSUME-LOOP at h0 (both net-disp-0). ──
    lemma_tail_chain(tm, c0, copy_refresh_fuel(big_m, g), loop_fuel_b1(od.len(), big_m), h0, h0, h0);
    assert(power_block_fuel_b1(big_m, g, od.len())
        == (copy_refresh_fuel(big_m, g) + loop_fuel_b1(od.len(), big_m)) as nat);
}

/// **`lemma_power_block_step_block3` is tail-safe** for its `power_block_fuel_b3` steps at the home
/// offset `H_0 = g + M + 1`, net-displacement-0. The 3-digit analog of
/// [`lemma_power_block_step_block1_tail_safe`]: same copy-refresh rebuild, but the consuming loop
/// emits a 3-symbol run per turn ([`lemma_block_loop_block3_tail_safe`]).
pub proof fn lemma_power_block_step_block3_tail_safe(
    tm: Tm, big_m: nat, g: nat, od: Seq<nat>, s0: nat, s1: nat, s2: nat,
    // ── copy_refresh states ──
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    q_turn: nat, q_turng: nat, q_ret: nat,
    q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    // ── block_loop states (q_loop := q_urt; q_e1/q_e2 are the triple-emit intermediates) ──
    q_guard: nat, q_iter: nat, q_surge: nat, q_e1: nat, q_e2: nat, q_eret: nat, q_bhome: nat,
    q_dwalk: nat, q_disc: nat, q_exit: nat,
    // ── copy_refresh quint indices ──
    i_dpeel0: int, i_dtemp0: int, i_dins0: int, i_dwb0: int,
    i_peel0: int, i_temp0: int, i_t2g0: int, i_gap0: int, i_mark0: int, i_rf2g0: int, i_rgap0: int,
    i_rg2t0: int,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_turn: int, i_master: int, i_tm2g: int, i_trgap: int, i_tg2t: int, i_trtemp: int,
    i_upeel: int, i_utemp: int, i_ut2g: int, i_ugap: int, i_uu1: int, i_uurest: int,
    i_uturn: int, i_umaster: int, i_um2g: int, i_urgap: int, i_ug2t: int, i_urtemp: int,
    // ── block_loop quint indices (i_one_r := i_urtemp) ──
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_e0: int, i_e1: int, i_e2: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        // ── copy_refresh index bounds ──
        0 <= i_dpeel0 < tm.quints.len(),
        0 <= i_dtemp0 < tm.quints.len(),
        0 <= i_dins0 < tm.quints.len(),
        0 <= i_dwb0 < tm.quints.len(),
        0 <= i_peel0 < tm.quints.len(),
        0 <= i_temp0 < tm.quints.len(),
        0 <= i_t2g0 < tm.quints.len(),
        0 <= i_gap0 < tm.quints.len(),
        0 <= i_mark0 < tm.quints.len(),
        0 <= i_rf2g0 < tm.quints.len(),
        0 <= i_rgap0 < tm.quints.len(),
        0 <= i_rg2t0 < tm.quints.len(),
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_tm2g < tm.quints.len(),
        0 <= i_trgap < tm.quints.len(),
        0 <= i_tg2t < tm.quints.len(),
        0 <= i_trtemp < tm.quints.len(),
        0 <= i_upeel < tm.quints.len(),
        0 <= i_utemp < tm.quints.len(),
        0 <= i_ut2g < tm.quints.len(),
        0 <= i_ugap < tm.quints.len(),
        0 <= i_uu1 < tm.quints.len(),
        0 <= i_uurest < tm.quints.len(),
        0 <= i_uturn < tm.quints.len(),
        0 <= i_umaster < tm.quints.len(),
        0 <= i_um2g < tm.quints.len(),
        0 <= i_urgap < tm.quints.len(),
        0 <= i_ug2t < tm.quints.len(),
        0 <= i_urtemp < tm.quints.len(),
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
        // ── copy_refresh quints (j=0 deposit-first) ──
        tm.quints[i_dpeel0] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp0] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins0] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb0] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_peel0] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp0] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g0] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap0] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark0] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g0] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap0] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t0] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
        // ── copy_refresh quints (home-cycle) ──
        tm.quints[i_peel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_mark] == mk_quint(q_b, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
        tm.quints[i_dpeel] == mk_quint(q_rt, 0, 0, q_dw, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw, 0, 1, q_home, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_home, 1, 1, q_home, Dir::R),
        // ── copy_refresh quints (terminate walk-back) ──
        tm.quints[i_turn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_master] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_tm2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_trgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_tg2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        tm.quints[i_trtemp] == mk_quint(q_ret, 1, 1, q_ret, Dir::R),
        // ── copy_refresh quints (unmark; home == q_ret) ──
        tm.quints[i_upeel] == mk_quint(q_ret, 0, 0, q_ut, Dir::L),
        tm.quints[i_utemp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_ut2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_ugap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_uu1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_uurest] == mk_quint(q_uf, 5, 1, q_uf, Dir::L),
        tm.quints[i_uturn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_umaster] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_um2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_urgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_ug2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
        tm.quints[i_urtemp] == mk_quint(q_urt, 1, 1, q_urt, Dir::R),
        // ── block_loop quints (q_loop := q_urt, i_one_r := i_urtemp; triple emit) ──
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
    ensures
        tail_safe(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b3(big_m, g, od.len()), (g + big_m + 1) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b3(big_m, g, od.len()), (g + big_m + 1) as nat)
            == (g + big_m + 1) as nat,
{
    let m = tm.m;
    reveal(tm_wf);
    let h0 = (g + big_m + 1) as nat;
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: dpack(od, m), a: 0, q: q_dh0 };

    // ── PHASE A — COPY-REFRESH bridge: tm_run(c0, crf) == c1, tail_safe at h0 → h0. ──
    lemma_copy_refresh(tm, big_m, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        q_turn, q_turng, q_ret,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp);
    let w = (pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m)) as nat;
    let c1 = TmConfig { u: dec_u(big_m, w, m), v: dpack(od, m), a: 0, q: q_urt };
    assert(tm_run(tm, c0, copy_refresh_fuel(big_m, g)) == c1);
    lemma_copy_refresh_tail_safe(tm, big_m, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        q_turn, q_turng, q_ret,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp);

    // ── w % m == 0 (the loop's separator). ──
    assert(g - big_m >= 1);
    lemma_pow_nat_unfold(m, (g - big_m) as nat);
    let xx = (pow_nat(m, (g - big_m - 1) as nat) * repunit_m(big_m, m)) as nat;
    assert(w == m * xx) by(nonlinear_arith)
        requires
            w == pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat),
            xx == pow_nat(m, (g - big_m - 1) as nat) * repunit_m(big_m, m);
    assert(w % m == 0) by {
        assert(w == xx * m) by(nonlinear_arith) requires w == m * xx;
        lemma_div_mod_step(xx, m, 0);
    }

    // ── PHASE B — CONSUME LOOP (triple): tail_safe(c1, loop_fuel_b3, h0) → h0. ──
    lemma_block_loop_block3_tail_safe(tm, big_m, w, od, s0, s1, s2,
        q_urt, q_guard, q_iter, q_surge, q_e1, q_e2, q_eret, q_bhome, q_dwalk, q_disc, q_exit,
        i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_urtemp, h0);

    // ── chain: COPY-REFRESH ∘ CONSUME-LOOP at h0 (both net-disp-0). ──
    lemma_tail_chain(tm, c0, copy_refresh_fuel(big_m, g), loop_fuel_b3(od.len(), big_m), h0, h0, h0);
    assert(power_block_fuel_b3(big_m, g, od.len())
        == (copy_refresh_fuel(big_m, g) + loop_fuel_b3(od.len(), big_m)) as nat);
}


/// **`lemma_power_block_step_block1_m1` is tail-safe** for its `power_block_fuel_b1_m1` steps at the home
/// offset `H_0 = g + 2` (`= g + M + 1`, `M = 1`), net-displacement-0. The 2-piece chain:
/// [`crate::gap2_tail_phase1_m1::lemma_copy_refresh_m1_tail_safe`] ∘
/// [`lemma_block_loop_block1_tail_safe`] (at `temp = 1`). The loop's `h ≥ temp+1` margin holds (`g+2 ≥ 2`).
pub proof fn lemma_power_block_step_block1_m1_tail_safe(
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
        tail_safe(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b1_m1(g, od.len()), (g + 2) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b1_m1(g, od.len()), (g + 2) as nat)
            == (g + 2) as nat,
{
    let m = tm.m;
    reveal(tm_wf);
    let h0 = (g + 2) as nat;
    let c0 = TmConfig { u: copy_u(0, 1, g, m), v: dpack(od, m), a: 0, q: q_dh0 };

    // ── PHASE A — COPY-REFRESH (M=1) bridge: tm_run(c0, 6g+12) == c1, tail_safe at h0 → h0. ──
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
    lemma_copy_refresh_m1_tail_safe(tm, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_t, q_a, q_b, q_turn, q_turng, q_ret, q_home,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b, i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t);

    // ── w % m == 0 (the loop's separator): g − 1 ≥ 2 ⟹ m | m^(g−1) | w. ──
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

    // ── PHASE B — CONSUME LOOP (temp = 1): tail_safe(c1, loop_fuel, h0) → h0. ──
    lemma_block_loop_block1_tail_safe(tm, 1, w, od, s,
        q_urt, q_guard, q_iter, q_surge, q_eret, q_bhome, q_dwalk, q_disc, q_exit,
        i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
        i_emit, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r, h0);

    // ── chain: COPY-REFRESH ∘ CONSUME-LOOP at h0 (both net-disp-0). ──
    lemma_tail_chain(tm, c0, (6 * g + 12) as nat, loop_fuel_b1(od.len(), 1), h0, h0, h0);
    assert(power_block_fuel_b1_m1(g, od.len()) == ((6 * g + 12) + loop_fuel_b1(od.len(), 1)) as nat);
}

/// **`lemma_power_block_step_block3_m1` is tail-safe** for its `power_block_fuel_b3_m1` steps at the home
/// offset `H_0 = g + 2`, net-displacement-0. The triple-emit `M = 1` analog of
/// [`lemma_power_block_step_block1_m1_tail_safe`]: same copy-refresh-m1 rebuild,
/// [`lemma_block_loop_block3_tail_safe`] (at `temp = 1`).
pub proof fn lemma_power_block_step_block3_m1_tail_safe(
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
        tail_safe(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b3_m1(g, od.len()), (g + 2) as nat),
        tail_end_h(tm,
            TmConfig { u: copy_u(0, 1, g, tm.m), v: dpack(od, tm.m), a: 0, q: q_dh0 },
            power_block_fuel_b3_m1(g, od.len()), (g + 2) as nat)
            == (g + 2) as nat,
{
    let m = tm.m;
    reveal(tm_wf);
    let h0 = (g + 2) as nat;
    let c0 = TmConfig { u: copy_u(0, 1, g, m), v: dpack(od, m), a: 0, q: q_dh0 };

    // ── PHASE A — COPY-REFRESH (M=1) bridge: tm_run(c0, 6g+12) == c1, tail_safe at h0 → h0. ──
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
    lemma_copy_refresh_m1_tail_safe(tm, g, dpack(od, m),
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_t, q_a, q_b, q_turn, q_turng, q_ret, q_home,
        q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b, i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t);

    // ── w % m == 0 (the loop's separator). ──
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

    // ── PHASE B — CONSUME LOOP (triple, temp = 1): tail_safe(c1, loop_fuel_b3, h0) → h0. ──
    lemma_block_loop_block3_tail_safe(tm, 1, w, od, s0, s1, s2,
        q_urt, q_guard, q_iter, q_surge, q_e1, q_e2, q_eret, q_bhome, q_dwalk, q_disc, q_exit,
        i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
        i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
        i_pivot, i_one_l, i_erase, i_disc, i_one_r, h0);

    // ── chain: COPY-REFRESH ∘ CONSUME-LOOP at h0 (both net-disp-0). ──
    lemma_tail_chain(tm, c0, (6 * g + 12) as nat, loop_fuel_b3(od.len(), 1), h0, h0, h0);
    assert(power_block_fuel_b3_m1(g, od.len()) == ((6 * g + 12) + loop_fuel_b3(od.len(), 1)) as nat);
}

} // verus!
