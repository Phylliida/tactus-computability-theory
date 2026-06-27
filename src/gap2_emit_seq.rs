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
use crate::gap2_emit_window::{seret1x_gen, lemma_seret1x_phase};
use crate::gap2_emit_power::{pbb1x_gen, lemma_pbb1x_phase, lemma_pbb1x_walkback};
use crate::gap2_emit_power3::{pbb3x_gen, lemma_pbb3x_phase_any, lemma_pbb3x_walkback, pb3_fuel};

verus! {

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
