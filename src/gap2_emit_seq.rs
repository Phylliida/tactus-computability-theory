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
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_assemble5::{entry5, tm_mod5};
use crate::tm_dstring::dpack;
use crate::tm_copy_refresh::copy_u;
use crate::gap2_relnum_dds::seq_pow;
use crate::tm_power_block::power_block_fuel_b1;
use crate::gap2_emit_window::{seret1x_gen, lemma_seret1x_phase};
use crate::gap2_emit_power::{pbb1x_gen, lemma_pbb1x_phase, lemma_pbb1x_walkback};

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

} // verus!
