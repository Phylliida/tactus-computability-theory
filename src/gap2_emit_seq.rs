//! # GAP-2 G2-F Route (i) — the EMITTER SEQUENCER (16-block chain over `assemble5`).
//!
//! Chains the per-block phase lemmas ([`crate::gap2_emit_power`], [`crate::gap2_emit_power3`],
//! [`crate::gap2_emit_window`]) into the full `fam_digits = uinv_digits(b) ++ u_digits(a)` emission. The
//! splice is pure STATE IDENTIFICATION (§N+11/§N+12): each block's exit `qexit = entry5(pc+1)` makes
//! `Config_term(k) ≡ Config_init(k+1)` IDENTICALLY, so the chain composes via [`lemma_tm_run_split`] with no
//! glue steps. A singleton block ending at `entry5(pc+1)` needs its 4 walk-back self-loops there; those
//! COINCIDE with the next window's inert off-0 self-loops, exposed by `lemma_*_walkback`.
//!
//! ## This module — the 2-block splice (proof-of-concept, validates the mechanic end-to-end)
//! [`lemma_chain_seret1_pbb1`] chains a single singleton into a single power-block. The template the full
//! 8-block per-phase chain instantiates per block-pair. `docs/gap2-input-loader-plan.md` §N+12.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_assemble5::{entry5, tm_mod5};
use crate::tm_dstring::dpack;
use crate::tm_copy_refresh::copy_u;
use crate::gap2_relnum_dds::seq_pow;
use crate::tm_power_block::power_block_fuel_b1;
use crate::gap2_fam_digits::uinv_digits;
use crate::gap2_emit_window::{seret1x_gen, lemma_seret1x_phase, seret3x_gen, lemma_seret3x_phase};
use crate::gap2_emit_power::{pbb1x_gen, lemma_pbb1x_phase, lemma_pbb1x_phase_any, lemma_pbb1x_walkback, pb1_fuel};
use crate::gap2_emit_power3::{pbb3x_gen, lemma_pbb3x_phase_any, lemma_pbb3x_walkback, pb3_fuel};

verus! {

/// **Digit-bound under concatenation.** If `od_prev` and `emit` both have digits in `[1,4]`, so does
/// `od_prev ++ emit`. The output-accumulation invariant maintainer for the chain.
pub proof fn cat_bound(od_prev: Seq<nat>, emit: Seq<nat>)
    requires
        forall|j: int| 0 <= j < od_prev.len() ==> 1 <= #[trigger] od_prev[j] <= 4,
        forall|j: int| 0 <= j < emit.len() ==> 1 <= #[trigger] emit[j] <= 4,
    ensures
        forall|j: int| 0 <= j < (od_prev + emit).len() ==> 1 <= #[trigger] (od_prev + emit)[j] <= 4,
{
    let cat = od_prev + emit;
    assert forall|j: int| 0 <= j < cat.len() implies 1 <= #[trigger] cat[j] <= 4 by {
        if j < od_prev.len() { assert(cat[j] == od_prev[j]); } else { assert(cat[j] == emit[j - od_prev.len()]); }
    }
}

/// Fuel of the FIRST half (blocks 0–3) of the `uinv_digits` phase:
/// `[4]·(4,1,2)ⁱ·[3]·(4,3,2)ⁱ`, master `M`, starting output length `l0`.
pub open spec fn uinv_half_a_fuel(big_m: nat, g: nat, l0: nat) -> nat {
    let l1 = (l0 + 1) as nat;
    let l2 = (l1 + 3 * big_m) as nat;
    let l3 = (l2 + 1) as nat;
    ((2 * l0 + 4) + pb3_fuel(big_m, g, l1) + (2 * l2 + 4) + pb3_fuel(big_m, g, l3)) as nat
}

/// **First half of the `uinv` phase (blocks 0–3): `[4] · (4,1,2)^M · [3] · (4,3,2)^M`.** Chains a
/// singleton, triple-power, singleton, triple-power over windows `pc..pc+3` (each exiting onto the next's
/// home pivot `entry5(pc+k+1)`). The two singletons' walk-backs come from the following power windows; the
/// last block (pbb3 at `pc+3`) exits onto `entry5(pc+4)` — block 4's home pivot in the second half. The
/// 8-block per-phase chain is this composed with its `uinv_half_b` analog (§N+12 addendum).
pub proof fn lemma_uinv_half_a(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc + 3 <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(4, entry5(pc + 1), i as nat),
        forall|i: int| (pc + 1) * 288 <= i < (pc + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 1, 2, entry5(pc + 2), i as nat),
        forall|i: int| (pc + 2) * 288 <= i < (pc + 2) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(3, entry5(pc + 3), i as nat),
        forall|i: int| (pc + 3) * 288 <= i < (pc + 3) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 3, 2, entry5(pc + 4), i as nat),
        1 <= big_m,
        g >= big_m + 2,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            uinv_half_a_fuel(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq![4nat] + seq_pow(seq![4nat, 1nat, 2nat], big_m)
                    + seq![3nat] + seq_pow(seq![4nat, 3nat, 2nat], big_m), tm.m),
                a: 0, q: entry5(pc + 4) }),
{
    let m = tm.m;
    let bigu = copy_u(0, big_m, g, m);
    let c0 = TmConfig { u: bigu, v: dpack(od, m), a: 0, q: entry5(pc) };

    // ── block 0: seret1[4] @ pc → entry5(pc+1). Walk-back from pc+1 (pbb3). ──
    lemma_pbb3x_walkback(tm, len, pc + 1, 4, 1, 2, entry5(pc + 2), 1);
    lemma_pbb3x_walkback(tm, len, pc + 1, 4, 1, 2, entry5(pc + 2), 2);
    lemma_pbb3x_walkback(tm, len, pc + 1, 4, 1, 2, entry5(pc + 2), 3);
    lemma_pbb3x_walkback(tm, len, pc + 1, 4, 1, 2, entry5(pc + 2), 4);
    lemma_seret1x_phase(tm, len, pc, bigu, od, 4, entry5(pc + 1),
        ((pc + 1) * 288 + 1) as int, ((pc + 1) * 288 + 2) as int,
        ((pc + 1) * 288 + 3) as int, ((pc + 1) * 288 + 4) as int);
    let od1 = od + seq![4nat];
    let c1 = TmConfig { u: bigu, v: dpack(od1, m), a: 0, q: entry5(pc + 1) };
    assert(tm_run(tm, c0, (2 * od.len() + 4) as nat) == c1);

    // ── block 1: pbb3(4,1,2) @ pc+1 → entry5(pc+2). ──
    cat_bound(od, seq![4nat]);
    lemma_pbb3x_phase_any(tm, len, pc + 1, big_m, g, od1, 4, 1, 2, entry5(pc + 2));
    let od2 = od1 + seq_pow(seq![4nat, 1nat, 2nat], big_m);
    let c2 = TmConfig { u: bigu, v: dpack(od2, m), a: 0, q: entry5(pc + 2) };
    assert(tm_run(tm, c1, pb3_fuel(big_m, g, od1.len())) == c2);

    // ── block 2: seret1[3] @ pc+2 → entry5(pc+3). Walk-back from pc+3 (pbb3). ──
    crate::gap2_relnum_dds::lemma_seq_pow_bound(seq![4nat, 1nat, 2nat], big_m, 1, 4);
    cat_bound(od1, seq_pow(seq![4nat, 1nat, 2nat], big_m));
    lemma_pbb3x_walkback(tm, len, pc + 3, 4, 3, 2, entry5(pc + 4), 1);
    lemma_pbb3x_walkback(tm, len, pc + 3, 4, 3, 2, entry5(pc + 4), 2);
    lemma_pbb3x_walkback(tm, len, pc + 3, 4, 3, 2, entry5(pc + 4), 3);
    lemma_pbb3x_walkback(tm, len, pc + 3, 4, 3, 2, entry5(pc + 4), 4);
    lemma_seret1x_phase(tm, len, pc + 2, bigu, od2, 3, entry5(pc + 3),
        ((pc + 3) * 288 + 1) as int, ((pc + 3) * 288 + 2) as int,
        ((pc + 3) * 288 + 3) as int, ((pc + 3) * 288 + 4) as int);
    let od3 = od2 + seq![3nat];
    let c3 = TmConfig { u: bigu, v: dpack(od3, m), a: 0, q: entry5(pc + 3) };
    assert(tm_run(tm, c2, (2 * od2.len() + 4) as nat) == c3);

    // ── block 3: pbb3(4,3,2) @ pc+3 → entry5(pc+4). ──
    cat_bound(od2, seq![3nat]);
    lemma_pbb3x_phase_any(tm, len, pc + 3, big_m, g, od3, 4, 3, 2, entry5(pc + 4));
    let od4 = od3 + seq_pow(seq![4nat, 3nat, 2nat], big_m);
    let c4 = TmConfig { u: bigu, v: dpack(od4, m), a: 0, q: entry5(pc + 4) };
    assert(tm_run(tm, c3, pb3_fuel(big_m, g, od3.len())) == c4);

    // ── lengths (fuel matching). ──
    crate::gap2_relnum_dds::lemma_seq_pow_len(seq![4nat, 1nat, 2nat], big_m);
    crate::gap2_relnum_dds::lemma_seq_pow_len(seq![4nat, 3nat, 2nat], big_m);
    assert(od1.len() == od.len() + 1);
    assert(od2.len() == od.len() + 1 + 3 * big_m);
    assert(od3.len() == od.len() + 2 + 3 * big_m);

    // ── compose: c0 →F0 c1 →F1 c2 →F2 c3 →F3 c4. ──
    let f0 = (2 * od.len() + 4) as nat;
    let f1 = pb3_fuel(big_m, g, od1.len());
    let f2 = (2 * od2.len() + 4) as nat;
    let f3 = pb3_fuel(big_m, g, od3.len());
    lemma_tm_run_split(tm, c0, f0, f1);
    lemma_tm_run_split(tm, c0, (f0 + f1) as nat, f2);
    lemma_tm_run_split(tm, c0, (f0 + f1 + f2) as nat, f3);
    assert(uinv_half_a_fuel(big_m, g, od.len()) == (f0 + f1 + f2 + f3) as nat);
    assert(od + seq![4nat] + seq_pow(seq![4nat, 1nat, 2nat], big_m)
        + seq![3nat] + seq_pow(seq![4nat, 3nat, 2nat], big_m) =~= od4);
}

/// Fuel of the SECOND half (blocks 4–7) of the `uinv_digits` phase:
/// `[2]·(1)ⁱ·[4,1,2]·(3)ⁱ`, master `M`, starting output length `l4`.
pub open spec fn uinv_half_b_fuel(big_m: nat, g: nat, l4: nat) -> nat {
    let l5 = (l4 + 1) as nat;
    let l6 = (l5 + big_m) as nat;
    let l7 = (l6 + 3) as nat;
    ((2 * l4 + 4) + pb1_fuel(big_m, g, l5) + (2 * l6 + 8) + pb1_fuel(big_m, g, l7)) as nat
}

/// **Second half of the `uinv` phase (blocks 4–7): `[2] · (1)^M · [4,1,2] · (3)^M`.** Chains
/// singleton·single-power·triple-singleton·single-power over windows `pc4..pc4+3`. The last block (pbb1 at
/// `pc4+3`) exits onto the EXTERNAL `qend` (the phase boundary / master-mgmt). Parametric in the starting
/// output `od4` (the first half's accumulated output).
pub proof fn lemma_uinv_half_b(tm: Tm, len: nat, pc4: nat, big_m: nat, g: nat, od4: Seq<nat>, qend: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc4 + 3 <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc4 * 288 <= i < pc4 * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(2, entry5(pc4 + 1), i as nat),
        forall|i: int| (pc4 + 1) * 288 <= i < (pc4 + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(1, entry5(pc4 + 2), i as nat),
        forall|i: int| (pc4 + 2) * 288 <= i < (pc4 + 2) * 288 + 288 ==> #[trigger] tm.quints[i] == seret3x_gen(4, 1, 2, entry5(pc4 + 3), i as nat),
        forall|i: int| (pc4 + 3) * 288 <= i < (pc4 + 3) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(3, qend, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        forall|k: int| 0 <= k < od4.len() ==> 1 <= #[trigger] od4[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od4, tm.m), a: 0, q: entry5(pc4) },
            uinv_half_b_fuel(big_m, g, od4.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od4 + seq![2nat] + seq_pow(seq![1nat], big_m)
                    + seq![4nat, 1nat, 2nat] + seq_pow(seq![3nat], big_m), tm.m),
                a: 0, q: qend }),
{
    let m = tm.m;
    let bigu = copy_u(0, big_m, g, m);
    let c4 = TmConfig { u: bigu, v: dpack(od4, m), a: 0, q: entry5(pc4) };

    // ── block 4: seret1[2] @ pc4 → entry5(pc4+1). Walk-back from pc4+1 (pbb1). ──
    lemma_pbb1x_walkback(tm, len, pc4 + 1, 1, entry5(pc4 + 2), 1);
    lemma_pbb1x_walkback(tm, len, pc4 + 1, 1, entry5(pc4 + 2), 2);
    lemma_pbb1x_walkback(tm, len, pc4 + 1, 1, entry5(pc4 + 2), 3);
    lemma_pbb1x_walkback(tm, len, pc4 + 1, 1, entry5(pc4 + 2), 4);
    lemma_seret1x_phase(tm, len, pc4, bigu, od4, 2, entry5(pc4 + 1),
        ((pc4 + 1) * 288 + 1) as int, ((pc4 + 1) * 288 + 2) as int,
        ((pc4 + 1) * 288 + 3) as int, ((pc4 + 1) * 288 + 4) as int);
    let od5 = od4 + seq![2nat];
    let c5 = TmConfig { u: bigu, v: dpack(od5, m), a: 0, q: entry5(pc4 + 1) };
    assert(tm_run(tm, c4, (2 * od4.len() + 4) as nat) == c5);

    // ── block 5: pbb1(1) @ pc4+1 → entry5(pc4+2). ──
    cat_bound(od4, seq![2nat]);
    lemma_pbb1x_phase_any(tm, len, pc4 + 1, big_m, g, od5, 1, entry5(pc4 + 2));
    let od6 = od5 + seq_pow(seq![1nat], big_m);
    let c6 = TmConfig { u: bigu, v: dpack(od6, m), a: 0, q: entry5(pc4 + 2) };
    assert(tm_run(tm, c5, pb1_fuel(big_m, g, od5.len())) == c6);

    // ── block 6: seret3(4,1,2) @ pc4+2 → entry5(pc4+3). Walk-back from pc4+3 (pbb1). ──
    crate::gap2_relnum_dds::lemma_seq_pow_bound(seq![1nat], big_m, 1, 4);
    cat_bound(od5, seq_pow(seq![1nat], big_m));
    lemma_pbb1x_walkback(tm, len, pc4 + 3, 3, qend, 1);
    lemma_pbb1x_walkback(tm, len, pc4 + 3, 3, qend, 2);
    lemma_pbb1x_walkback(tm, len, pc4 + 3, 3, qend, 3);
    lemma_pbb1x_walkback(tm, len, pc4 + 3, 3, qend, 4);
    lemma_seret3x_phase(tm, len, pc4 + 2, bigu, od6, 4, 1, 2, entry5(pc4 + 3),
        ((pc4 + 3) * 288 + 1) as int, ((pc4 + 3) * 288 + 2) as int,
        ((pc4 + 3) * 288 + 3) as int, ((pc4 + 3) * 288 + 4) as int);
    let od7 = od6 + seq![4nat, 1nat, 2nat];
    let c7 = TmConfig { u: bigu, v: dpack(od7, m), a: 0, q: entry5(pc4 + 3) };
    assert(tm_run(tm, c6, (2 * od6.len() + 8) as nat) == c7);

    // ── block 7: pbb1(3) @ pc4+3 → qend. ──
    cat_bound(od6, seq![4nat, 1nat, 2nat]);
    lemma_pbb1x_phase_any(tm, len, pc4 + 3, big_m, g, od7, 3, qend);
    let od8 = od7 + seq_pow(seq![3nat], big_m);
    let c8 = TmConfig { u: bigu, v: dpack(od8, m), a: 0, q: qend };
    assert(tm_run(tm, c7, pb1_fuel(big_m, g, od7.len())) == c8);

    // ── lengths (fuel matching). ──
    crate::gap2_relnum_dds::lemma_seq_pow_len(seq![1nat], big_m);
    assert(od5.len() == od4.len() + 1);
    assert(od6.len() == od4.len() + 1 + big_m);
    assert(od7.len() == od4.len() + 4 + big_m);

    // ── compose: c4 →F4 c5 →F5 c6 →F6 c7 →F7 c8. ──
    let f4 = (2 * od4.len() + 4) as nat;
    let f5 = pb1_fuel(big_m, g, od5.len());
    let f6 = (2 * od6.len() + 8) as nat;
    let f7 = pb1_fuel(big_m, g, od7.len());
    lemma_tm_run_split(tm, c4, f4, f5);
    lemma_tm_run_split(tm, c4, (f4 + f5) as nat, f6);
    lemma_tm_run_split(tm, c4, (f4 + f5 + f6) as nat, f7);
    assert(uinv_half_b_fuel(big_m, g, od4.len()) == (f4 + f5 + f6 + f7) as nat);
    assert(od4 + seq![2nat] + seq_pow(seq![1nat], big_m)
        + seq![4nat, 1nat, 2nat] + seq_pow(seq![3nat], big_m) =~= od8);
}

/// Total fuel of the full `uinv_digits` phase (8 blocks) — both halves.
pub open spec fn uinv_phase_fuel(big_m: nat, g: nat, l0: nat) -> nat {
    let l4 = (l0 + 2 + 6 * big_m) as nat;   // after blocks 0–3: +1 +3M +1 +3M
    (uinv_half_a_fuel(big_m, g, l0) + uinv_half_b_fuel(big_m, g, l4)) as nat
}

/// **The full `uinv_digits(b)` phase (8 blocks).** Composes the two halves: from the home pivot of window
/// `pc` with master `M = b+1`, after `uinv_phase_fuel` steps the output has grown by exactly
/// `uinv_digits(b)` (`= uinv_digits(M-1)`) and the head sits on the home pivot of the external phase
/// boundary `qend`. The first of the two `fam_digits` phases (the `u_digits(a)` phase is the structural
/// analog). `docs/gap2-input-loader-plan.md` §N+12.
pub proof fn lemma_uinv_phase(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>, qend: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc + 7 <= len,
        tm.quints.len() == 288 * (len + 1),
        // blocks 0–3 (first half):
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(4, entry5(pc + 1), i as nat),
        forall|i: int| (pc + 1) * 288 <= i < (pc + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 1, 2, entry5(pc + 2), i as nat),
        forall|i: int| (pc + 2) * 288 <= i < (pc + 2) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(3, entry5(pc + 3), i as nat),
        forall|i: int| (pc + 3) * 288 <= i < (pc + 3) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 3, 2, entry5(pc + 4), i as nat),
        // blocks 4–7 (second half):
        forall|i: int| (pc + 4) * 288 <= i < (pc + 4) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(2, entry5(pc + 5), i as nat),
        forall|i: int| (pc + 5) * 288 <= i < (pc + 5) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(1, entry5(pc + 6), i as nat),
        forall|i: int| (pc + 6) * 288 <= i < (pc + 6) * 288 + 288 ==> #[trigger] tm.quints[i] == seret3x_gen(4, 1, 2, entry5(pc + 7), i as nat),
        forall|i: int| (pc + 7) * 288 <= i < (pc + 7) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(3, qend, i as nat),
        1 <= big_m,
        g >= big_m + 2,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            uinv_phase_fuel(big_m, g, od.len()))
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + uinv_digits((big_m - 1) as nat), tm.m), a: 0, q: qend }),
{
    let m = tm.m;
    let bigu = copy_u(0, big_m, g, m);
    let c0 = TmConfig { u: bigu, v: dpack(od, m), a: 0, q: entry5(pc) };

    // ── first half (blocks 0–3). ──
    lemma_uinv_half_a(tm, len, pc, big_m, g, od);
    let od4 = od + seq![4nat] + seq_pow(seq![4nat, 1nat, 2nat], big_m)
        + seq![3nat] + seq_pow(seq![4nat, 3nat, 2nat], big_m);
    let c4 = TmConfig { u: bigu, v: dpack(od4, m), a: 0, q: entry5(pc + 4) };
    assert(tm_run(tm, c0, uinv_half_a_fuel(big_m, g, od.len())) == c4);

    // ── od4 digits ∈ 1..4 and length (for the second half's start). ──
    crate::gap2_relnum_dds::lemma_seq_pow_bound(seq![4nat, 1nat, 2nat], big_m, 1, 4);
    crate::gap2_relnum_dds::lemma_seq_pow_bound(seq![4nat, 3nat, 2nat], big_m, 1, 4);
    cat_bound(od, seq![4nat]);
    cat_bound(od + seq![4nat], seq_pow(seq![4nat, 1nat, 2nat], big_m));
    cat_bound(od + seq![4nat] + seq_pow(seq![4nat, 1nat, 2nat], big_m), seq![3nat]);
    cat_bound(od + seq![4nat] + seq_pow(seq![4nat, 1nat, 2nat], big_m) + seq![3nat],
        seq_pow(seq![4nat, 3nat, 2nat], big_m));
    crate::gap2_relnum_dds::lemma_seq_pow_len(seq![4nat, 1nat, 2nat], big_m);
    crate::gap2_relnum_dds::lemma_seq_pow_len(seq![4nat, 3nat, 2nat], big_m);
    assert(od4.len() == od.len() + 2 + 6 * big_m);

    // ── second half (blocks 4–7), starting at od4 / window pc+4. ──
    lemma_uinv_half_b(tm, len, pc + 4, big_m, g, od4, qend);
    let od8 = od4 + seq![2nat] + seq_pow(seq![1nat], big_m)
        + seq![4nat, 1nat, 2nat] + seq_pow(seq![3nat], big_m);
    let c8 = TmConfig { u: bigu, v: dpack(od8, m), a: 0, q: qend };
    assert(tm_run(tm, c4, uinv_half_b_fuel(big_m, g, od4.len())) == c8);

    // ── compose the two halves. ──
    lemma_tm_run_split(tm, c0, uinv_half_a_fuel(big_m, g, od.len()), uinv_half_b_fuel(big_m, g, od4.len()));
    assert(uinv_phase_fuel(big_m, g, od.len())
        == (uinv_half_a_fuel(big_m, g, od.len()) + uinv_half_b_fuel(big_m, g, od4.len())) as nat);

    // ── output equality: od8 =~= od ++ uinv_digits(M-1) (i = (M-1)+1 = M). ──
    assert((big_m - 1) as nat + 1 == big_m);
    assert(od8 =~= od + uinv_digits((big_m - 1) as nat));
}

/// **2-block splice: singleton `[s]` then power-block `(s2)^M`.** A well-formed n=5 assemble5 machine whose
/// window `pc` carries the exit-parametric singleton (`qexit = entry5(pc+1)`) and window `pc+1` carries the
/// exit-parametric power-block (`qexit`) runs both back-to-back with NO glue: from the home pivot in window
/// `pc` after `(2|od|+4) + power_block_fuel_b1(M,g,|od|+1)` steps the output has grown by `[s] ++ (s2)^M`
/// and the head sits on the home pivot in `qexit`. Validates the §N+12 splice mechanic concretely.
pub proof fn lemma_chain_seret1_pbb1(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>,
    s: nat, s2: nat, qexit: nat)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc + 1 <= len,
        tm.quints.len() == 288 * (len + 1),
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(s, entry5(pc + 1), i as nat),
        forall|i: int| (pc + 1) * 288 <= i < (pc + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(s2, qexit, i as nat),
        2 <= big_m,
        g >= big_m + 2,
        1 <= s <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            (2 * od.len() + 4 + power_block_fuel_b1(big_m, g, (od.len() + 1) as nat)) as nat)
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq![s] + seq_pow(seq![s2], big_m), tm.m), a: 0, q: qexit }),
{
    let m = tm.m;
    let bigu = copy_u(0, big_m, g, m);

    // ── locate the singleton's walk-back quints from window pc+1's off-0 self-loops (== qexit_sing). ──
    lemma_pbb1x_walkback(tm, len, pc + 1, s2, qexit, 1);
    lemma_pbb1x_walkback(tm, len, pc + 1, s2, qexit, 2);
    lemma_pbb1x_walkback(tm, len, pc + 1, s2, qexit, 3);
    lemma_pbb1x_walkback(tm, len, pc + 1, s2, qexit, 4);
    let jl1 = ((pc + 1) * 288 + 1) as int;
    let jl2 = ((pc + 1) * 288 + 2) as int;
    let jl3 = ((pc + 1) * 288 + 3) as int;
    let jl4 = ((pc + 1) * 288 + 4) as int;

    // ── singleton phase: c0 → c1 @ entry5(pc+1) (= the power-block's home pivot, q_dh0). ──
    let c0 = TmConfig { u: bigu, v: dpack(od, m), a: 0, q: entry5(pc) };
    lemma_seret1x_phase(tm, len, pc, bigu, od, s, entry5(pc + 1), jl1, jl2, jl3, jl4);
    let od1 = od + seq![s];
    let c1 = TmConfig { u: bigu, v: dpack(od1, m), a: 0, q: entry5(pc + 1) };
    assert(tm_run(tm, c0, (2 * od.len() + 4) as nat) == c1);

    // ── power-block phase: c1 → c2 @ qexit. ──
    assert forall|k: int| 0 <= k < od1.len() implies 1 <= #[trigger] od1[k] <= 4 by {
        if k < od.len() { assert(od1[k] == od[k]); } else { assert(od1[k] == s); }
    }
    lemma_pbb1x_phase(tm, len, pc + 1, big_m, g, od1, s2, qexit);
    let c2 = TmConfig { u: bigu, v: dpack(od1 + seq_pow(seq![s2], big_m), m), a: 0, q: qexit };
    assert(od1.len() == od.len() + 1);
    assert(tm_run(tm, c1, power_block_fuel_b1(big_m, g, od1.len())) == c2);

    // ── compose: c0 →(2|od|+4) c1 →(fuel) c2. ──
    lemma_tm_run_split(tm, c0, (2 * od.len() + 4) as nat, power_block_fuel_b1(big_m, g, od1.len()));
    assert(od + seq![s] + seq_pow(seq![s2], big_m) =~= od1 + seq_pow(seq![s2], big_m));
}

/// **3-block chain: singleton `[sa]` · power `(t0,t1,t2)^M` · FINAL singleton `[sb]`.** Exercises all three
/// splice situations of the §N+12 sequencer: singleton→power (walk-back from the next window), power→
/// singleton (trivial config-equality — the power exits on `entry5(pc+2)` = the next singleton's home
/// pivot), and the FINAL singleton whose `qexit = qfinal` is external (the `q_cmp` hand-off) so `qfinal`
/// must be made walk-back-compatible — its 4 self-loops `(qfinal, 1..4, qfinal, L)` are supplied as
/// `kf1..kf4`. Uses the unified [`lemma_pbb3x_phase_any`] (M=1 or M≥2). The full template for the 8-block
/// per-phase chain.
pub proof fn lemma_chain_s1_p3_s1(tm: Tm, len: nat, pc: nat, big_m: nat, g: nat, od: Seq<nat>,
    sa: nat, t0: nat, t1: nat, t2: nat, sb: nat, qfinal: nat,
    kf1: int, kf2: int, kf3: int, kf4: int)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc + 2 <= len,
        tm.quints.len() == 288 * (len + 1),
        // window pc: singleton [sa], exits onto pc+1's home pivot.
        forall|i: int| pc * 288 <= i < pc * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(sa, entry5(pc + 1), i as nat),
        // window pc+1: triple power-block (t0,t1,t2), exits onto pc+2's home pivot.
        forall|i: int| (pc + 1) * 288 <= i < (pc + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(t0, t1, t2, entry5(pc + 2), i as nat),
        // window pc+2: final singleton [sb], exits onto the external qfinal.
        forall|i: int| (pc + 2) * 288 <= i < (pc + 2) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(sb, qfinal, i as nat),
        // qfinal walk-back-compatible (the q_cmp hand-off carries the 4 inert off-0 self-loops).
        0 <= kf1 < tm.quints.len(),
        0 <= kf2 < tm.quints.len(),
        0 <= kf3 < tm.quints.len(),
        0 <= kf4 < tm.quints.len(),
        tm.quints[kf1] == mk_quint(qfinal, 1, 1, qfinal, Dir::L),
        tm.quints[kf2] == mk_quint(qfinal, 2, 2, qfinal, Dir::L),
        tm.quints[kf3] == mk_quint(qfinal, 3, 3, qfinal, Dir::L),
        tm.quints[kf4] == mk_quint(qfinal, 4, 4, qfinal, Dir::L),
        1 <= big_m,
        g >= big_m + 2,
        1 <= sa <= 4,
        1 <= t0 <= 4,
        1 <= t1 <= 4,
        1 <= t2 <= 4,
        1 <= sb <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: dpack(od, tm.m), a: 0, q: entry5(pc) },
            (2 * od.len() + 4
                + pb3_fuel(big_m, g, (od.len() + 1) as nat)
                + (2 * (od.len() + 1 + 3 * big_m) + 4)) as nat)
            == (TmConfig { u: copy_u(0, big_m, g, tm.m),
                v: dpack(od + seq![sa] + seq_pow(seq![t0, t1, t2], big_m) + seq![sb], tm.m), a: 0, q: qfinal }),
{
    let m = tm.m;
    let bigu = copy_u(0, big_m, g, m);
    let c0 = TmConfig { u: bigu, v: dpack(od, m), a: 0, q: entry5(pc) };

    // ── block 0: singleton [sa] @ pc → entry5(pc+1). Walk-back from pc+1's off-0 (pbb3). ──
    lemma_pbb3x_walkback(tm, len, pc + 1, t0, t1, t2, entry5(pc + 2), 1);
    lemma_pbb3x_walkback(tm, len, pc + 1, t0, t1, t2, entry5(pc + 2), 2);
    lemma_pbb3x_walkback(tm, len, pc + 1, t0, t1, t2, entry5(pc + 2), 3);
    lemma_pbb3x_walkback(tm, len, pc + 1, t0, t1, t2, entry5(pc + 2), 4);
    lemma_seret1x_phase(tm, len, pc, bigu, od, sa, entry5(pc + 1),
        ((pc + 1) * 288 + 1) as int, ((pc + 1) * 288 + 2) as int,
        ((pc + 1) * 288 + 3) as int, ((pc + 1) * 288 + 4) as int);
    let oda = od + seq![sa];
    let ca = TmConfig { u: bigu, v: dpack(oda, m), a: 0, q: entry5(pc + 1) };
    assert(tm_run(tm, c0, (2 * od.len() + 4) as nat) == ca);

    // ── block 1: power (t0,t1,t2)^M @ pc+1 → entry5(pc+2). ──
    assert forall|k: int| 0 <= k < oda.len() implies 1 <= #[trigger] oda[k] <= 4 by {
        if k < od.len() { assert(oda[k] == od[k]); } else { assert(oda[k] == sa); }
    }
    lemma_pbb3x_phase_any(tm, len, pc + 1, big_m, g, oda, t0, t1, t2, entry5(pc + 2));
    let odb = oda + seq_pow(seq![t0, t1, t2], big_m);
    let cb = TmConfig { u: bigu, v: dpack(odb, m), a: 0, q: entry5(pc + 2) };
    assert(oda.len() == od.len() + 1);
    assert(tm_run(tm, ca, pb3_fuel(big_m, g, oda.len())) == cb);

    // ── block 2: FINAL singleton [sb] @ pc+2 → qfinal. Walk-back from qfinal (the kf hypotheses). ──
    let trip = seq![t0, t1, t2];
    crate::gap2_relnum_dds::lemma_seq_pow_bound(trip, big_m, 1, 4);
    crate::gap2_relnum_dds::lemma_seq_pow_len(trip, big_m);
    assert(trip.len() == 3);
    assert(odb == oda + seq_pow(trip, big_m));
    assert forall|k: int| 0 <= k < odb.len() implies 1 <= #[trigger] odb[k] <= 4 by {
        if k < oda.len() {
            assert(odb[k] == oda[k]);
        } else {
            assert(odb[k] == seq_pow(trip, big_m)[k - oda.len()]);
        }
    }
    lemma_seret1x_phase(tm, len, pc + 2, bigu, odb, sb, qfinal, kf1, kf2, kf3, kf4);
    let cc = TmConfig { u: bigu, v: dpack(odb + seq![sb], m), a: 0, q: qfinal };
    assert(odb.len() == od.len() + 1 + 3 * big_m);
    assert(tm_run(tm, cb, (2 * odb.len() + 4) as nat) == cc);

    // ── compose the three segments. ──
    lemma_tm_run_split(tm, c0, (2 * od.len() + 4) as nat, pb3_fuel(big_m, g, oda.len()));
    lemma_tm_run_split(tm, c0, (2 * od.len() + 4 + pb3_fuel(big_m, g, oda.len())) as nat,
        (2 * odb.len() + 4) as nat);
    assert(od + seq![sa] + seq_pow(seq![t0, t1, t2], big_m) + seq![sb] =~= odb + seq![sb]);
}

} // verus!
