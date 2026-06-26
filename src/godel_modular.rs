//! # GAP-2 — the machine-content core: `RM(k)` halts ⟺ `mm_in_H0`.
//!
//! Composes the three verified halting equivalences end-to-end, collapsing the whole reduction pipeline
//! `RM(k) → RM(2) → TM → ModMachine` into a single iff:
//!
//! ```text
//!   (∃F. run_halts(rm_k, c, F))
//!     ⟺ mm_in_H0(tm_to_modmachine(rm_to_tm(rm_k_to_rm2(rm_k))), rep1(enc).0, rep1(enc).1)
//! ```
//!
//!  - `godel_run::lemma_godel_halts_iff`   — `RM(k)` halts ⟺ `rm_k_to_rm2(RM(k))` halts (M6, the k→2 Gödel layer);
//!  - `tm_run_sim::lemma_rm_tm_origin_iff` — `RM(2)` halts ⟺ `rm_to_tm` reaches the origin (B6);
//!  - `tm_h0_bwd::lemma_tm_h0_iff`         — reaches origin ⟺ `mm_in_H0` (G2-B..D).
//!
//! This is the self-contained "machine content" G2-F consumes: with `mm`/`config_encode` pinned to this
//! composition, `mm_in_H0(mm, enc(a,b))` reduces to `RM(k)` (the CEER dovetail enumerator) halting,
//! which is the bridge to `declared_equiv`/`ceer_realizes`. No verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::godel_assemble::{rm_k_to_rm2, block_start, lemma_rm_k_to_rm2_wf, lemma_block_start_le, lemma_rm2_len};
use crate::godel_dispatch::rm2_config_enc;
use crate::godel_run::lemma_godel_halts_iff;
use crate::tm_run_sim::{rm_config_enc, lemma_rm_tm_origin_iff};
use crate::tm_assemble::{rm_to_tm, lemma_rm_to_tm_wf, entry, tm_mod};
use crate::tm::{tm_origin, tm_halts_at};
use crate::tm_h0_bwd::{tm_config_wf, lemma_tm_h0_iff};
use crate::tm_modular::{tm_to_modmachine, rep1};
use crate::tm_two_counter::{two_counter_config, lemma_two_counter_config_wf};
use verus_group_theory::machine_group::mm_in_H0;

verus! {

/// The Gödel encoding of a well-formed RM(k) config is a well-formed config of the assembled RM(2).
pub proof fn lemma_rm2_config_wf(rm_k: RegisterMachine, c_k: Configuration)
    requires
        config_wf(rm_k, c_k),
    ensures
        config_wf(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k)),
{
    let instrs = rm_k.instructions;
    let rm2 = rm_k_to_rm2(rm_k);
    let c2 = rm2_config_enc(instrs, c_k);
    lemma_block_start_le(instrs, c_k.pc, instrs.len());     //  block_start(c_k.pc) <= block_start(len)
    lemma_rm2_len(instrs);                                  //  rm2.len() == block_start(len)
    assert(c2.pc <= rm2.instructions.len());
    assert(c2.registers.len() == 2);
}

/// The B6 layout encoding of a well-formed RM(2) config is a well-formed TM config of `rm_to_tm`.
pub proof fn lemma_rm_config_enc_wf(rm2: RegisterMachine, c2: Configuration)
    requires
        machine_wf(rm2),
        rm2.num_regs == 2,
        config_wf(rm2, c2),
    ensures
        tm_config_wf(rm_to_tm(rm2), rm_config_enc(rm2, c2)),
{
    let tm = rm_to_tm(rm2);
    let len = rm2.instructions.len();
    lemma_rm_to_tm_wf(rm2);                                 //  tm_wf(tm)
    assert(tm.n == 2);
    assert(tm.m == tm_mod(len));
    //  q = entry(c2.pc) < tm.m, since c2.pc <= len.
    assert(c2.pc <= len);
    assert(entry(c2.pc) < tm.m) by {
        assert(16 * c2.pc <= 16 * len) by(nonlinear_arith) requires c2.pc <= len;
    }
    lemma_two_counter_config_wf(tm, c2.registers[0], c2.registers[1], entry(c2.pc));
    assert(rm_config_enc(rm2, c2) == two_counter_config(c2.registers[0], c2.registers[1], entry(c2.pc), tm.m));
}

/// **The machine-content core.** `RM(k)` halts from `c` iff the encoded pair sits in `H₀` of the
/// modular machine `tm_to_modmachine(rm_to_tm(rm_k_to_rm2(rm_k)))`. The whole pipeline collapsed.
pub proof fn lemma_rm_k_halts_iff_mm_in_H0(rm_k: RegisterMachine, c_k: Configuration)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
    ensures
        ({
            let rm2 = rm_k_to_rm2(rm_k);
            let c2 = rm2_config_enc(rm_k.instructions, c_k);
            let tm = rm_to_tm(rm2);
            let ctm = rm_config_enc(rm2, c2);
            let mm = tm_to_modmachine(tm);
            (exists|f: nat| run_halts(rm_k, c_k, f))
                <==> mm_in_H0(mm, rep1(ctm, tm.m).0, rep1(ctm, tm.m).1)
        }),
{
    let instrs = rm_k.instructions;
    let rm2 = rm_k_to_rm2(rm_k);
    let c2 = rm2_config_enc(instrs, c_k);
    let tm = rm_to_tm(rm2);
    let ctm = rm_config_enc(rm2, c2);

    lemma_rm_k_to_rm2_wf(rm_k);            //  machine_wf(rm2)
    lemma_rm2_config_wf(rm_k, c_k);        //  config_wf(rm2, c2)
    lemma_rm_to_tm_wf(rm2);                //  tm_wf(tm)
    lemma_rm_config_enc_wf(rm2, c2);       //  tm_config_wf(tm, ctm)

    //  RM(k) halts ⟺ RM(2) halts.
    lemma_godel_halts_iff(rm_k, c_k);
    //  RM(2) halts ⟺ tm reaches origin.
    lemma_rm_tm_origin_iff(rm2, c2);
    //  tm reaches origin ⟺ mm_in_H0.
    lemma_tm_h0_iff(tm, ctm);
}

} //  verus!
