//  GAP-2 / L0 brick B-L0.2c — the dovetailing search register machine `search_rm(e)`.
//
//  ONE `RegisterMachine` whose halting on input `pair(a,b)` is exactly `declared_equiv(e,a,b)`. It
//  dovetails an outer bound `T = 0,1,2,…` over an inner stage loop `s = 0..=T`, simulating the
//  enumerator `E = e.enumerator` for `T+1` fuel via the B-L0.1 `instrument`, and re-pairing each
//  declared output to compare (both orientations) against the preserved input. See
//  docs/gap2-l0-search-rm-plan.md (B-L0.2c / B-L0.3).
//
//  The instruction list is a `Seq::new` over a per-index region dispatch (`srm_instr`) rather than a
//  `+`-concatenation, so every `m.instructions[i] == srm_instr(e,i)` access is O(region-dispatch),
//  not O(deep concat-unfold) — essential for keeping the gadget-frame derivations within budget.
//
//  Register map (num_regs = 29 + ne, ne = E.num_regs):
//    0 inp   1 zero   2 fuel   3 Treg   4 scnt   5 cnt   6 result
//    7 d1A  8 d1B  9 d2A  10 d2B                       (declared-pair backups)
//    11 xk1 12 nc1 13 ii1 14 tt1 15 ibak1 16 p1 17 ic1 (orientation-1 pair+eq working set)
//    18 xk2 19 nc2 20 ii2 21 tt2 22 ibak2 23 p2 24 ic2 (orientation-2 pair+eq working set)
//    25 bakA 26 bakB 27 bakC 28 bakD                   (preserve-copy backups)
//    29 .. 29+ne   E-bank (reg_offset = 29)
//
//  PC layout (linear; loops are DecJump back-edges):
//    [0,8)   SETUP        cnt := T+1
//    8       INNER_TOP    DecJump{cnt, IE}
//    [9, 9+2ne)           clear E-bank
//    clear ii1, clear ii2,  B2 load scnt -> E[0],  B3 set fuel := T+1
//    instrument(E)  halted_pc = CMP, timeout_pc = CONT
//    CMP comparison (80 instrs): backups, 2x pair+eq, Inc result on match
//    CONT  Inc scnt; DecJump{zero, INNER_TOP}
//    IE    DISPATCH DecJump{result, OC}; HALT
//    OC    clear scnt; Inc Treg; DecJump{zero, OUTER_TOP=0}

use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::{CEER, ceer_wf};
use crate::multi_output_primitives::{mk_inc, mk_dj, copy_instrs};
use crate::search_rm_arith::double_dist_instrs;
use crate::search_rm_compare::{clear_instrs, eq_test_instrs};
use crate::search_rm_clearbank::clear_bank_instrs;
use crate::search_rm_sim::instrument_instructions;

verus! {

//  ============================================================
//  Dimensions + pc offsets (functions of ne, ni)
//  ============================================================

pub open spec fn srm_ne(e: CEER) -> nat { e.enumerator.num_regs }
pub open spec fn srm_ni(e: CEER) -> nat { e.enumerator.instructions.len() }
pub open spec fn srm_numregs(e: CEER) -> nat { 29 + srm_ne(e) }

pub open spec fn srm_it(e: CEER) -> nat { 8 }                                 //  INNER_TOP
pub open spec fn srm_b1(e: CEER) -> nat { 9 }                                 //  clear E-bank base
pub open spec fn srm_clrii1(e: CEER) -> nat { 9 + 2 * srm_ne(e) }
pub open spec fn srm_clrii2(e: CEER) -> nat { 11 + 2 * srm_ne(e) }
pub open spec fn srm_b2(e: CEER) -> nat { 13 + 2 * srm_ne(e) }                //  load scnt -> E[0]
pub open spec fn srm_b3(e: CEER) -> nat { 20 + 2 * srm_ne(e) }                //  set fuel := T+1
pub open spec fn srm_instr_pc(e: CEER) -> nat { 30 + 2 * srm_ne(e) }          //  instrument base
pub open spec fn srm_cmp(e: CEER) -> nat { 30 + 2 * srm_ne(e) + 2 * srm_ni(e) }  //  halted_pc / CMP
pub open spec fn srm_cont(e: CEER) -> nat { srm_cmp(e) + 80 }                 //  timeout_pc / CONT_INNER
pub open spec fn srm_ie(e: CEER) -> nat { srm_cont(e) + 2 }                   //  INNER_EXIT / DISPATCH
pub open spec fn srm_oc(e: CEER) -> nat { srm_ie(e) + 2 }                     //  OUTER_CONT
pub open spec fn srm_total(e: CEER) -> nat { srm_oc(e) + 4 }

///  The 23-instruction forward-pair subroutine block at `sp` (mirrors `pair_subroutine_frame`).
pub open spec fn pair_sub_instrs(
    x_in: nat, y_in: nat, xk: nat, nc: nat, i: nat, t: nat, ibak: nat, zero: nat, p: nat, sp: nat,
) -> Seq<Instruction> {
    seq![
        mk_dj(x_in, sp + 4),      //  +0
        mk_inc(nc),               //  +1
        mk_inc(xk),               //  +2
        mk_dj(zero, sp),          //  +3
        mk_dj(y_in, sp + 7),      //  +4
        mk_inc(nc),               //  +5
        mk_dj(zero, sp + 4),      //  +6
        mk_dj(nc, sp + 17),       //  +7
        mk_inc(i),                //  +8
        mk_dj(i, sp + 12),        //  +9
        mk_inc(ibak),             //  +10
        mk_dj(zero, sp + 9),      //  +11
        mk_dj(ibak, sp + 16),     //  +12
        mk_inc(t),                //  +13
        mk_inc(i),                //  +14
        mk_dj(zero, sp + 12),     //  +15
        mk_dj(zero, sp + 7),      //  +16
        mk_dj(t, sp + 20),        //  +17
        mk_inc(p),                //  +18
        mk_dj(zero, sp + 17),     //  +19
        mk_dj(xk, sp + 23),       //  +20
        mk_inc(p),                //  +21
        mk_dj(zero, sp + 20)      //  +22
    ]
}

//  ============================================================
//  Per-index region dispatch
//  ============================================================

pub open spec fn srm_instr(e: CEER, i: int) -> Instruction {
    let ne = srm_ne(e);
    let cmp = srm_cmp(e);
    let cont = srm_cont(e);
    let ie = srm_ie(e);
    let oc = srm_oc(e);
    //  --- SETUP [0,8): cnt := T+1 ---
    if i < 4 { double_dist_instrs(3, 5, 25, 1, 0)[i] }
    else if i < 7 { copy_instrs(25, 3, 1, 4)[i - 4] }
    else if i < 8 { mk_inc(5) }
    //  --- INNER_TOP guard ---
    else if i < 9 { mk_dj(5, ie as nat) }
    //  --- clear E-bank [9, 9+2ne) ---
    else if i < 9 + 2 * ne { clear_bank_instrs(29, ne, 1, 9)[i - 9] }
    //  --- clear ii1, ii2 ---
    else if i < 11 + 2 * ne { clear_instrs(13, 1, (9 + 2 * ne) as nat)[i - (9 + 2 * ne)] }
    else if i < 13 + 2 * ne { clear_instrs(20, 1, (11 + 2 * ne) as nat)[i - (11 + 2 * ne)] }
    //  --- B2: load scnt -> E[0], restore scnt ---
    else if i < 17 + 2 * ne { double_dist_instrs(4, 29, 25, 1, (13 + 2 * ne) as nat)[i - (13 + 2 * ne)] }
    else if i < 20 + 2 * ne { copy_instrs(25, 4, 1, (17 + 2 * ne) as nat)[i - (17 + 2 * ne)] }
    //  --- B3: clear fuel, Treg -> fuel, Inc (fuel := T+1), restore Treg ---
    else if i < 22 + 2 * ne { clear_instrs(2, 1, (20 + 2 * ne) as nat)[i - (20 + 2 * ne)] }
    else if i < 26 + 2 * ne { double_dist_instrs(3, 2, 26, 1, (22 + 2 * ne) as nat)[i - (22 + 2 * ne)] }
    else if i < 27 + 2 * ne { mk_inc(2) }
    else if i < 30 + 2 * ne { copy_instrs(26, 3, 1, (27 + 2 * ne) as nat)[i - (27 + 2 * ne)] }
    //  --- instrument(E) [30+2ne, cmp) ---
    else if i < cmp {
        instrument_instructions(e.enumerator.instructions, 29, srm_instr_pc(e), cmp, cont, 2, 1)[i - (30 + 2 * ne)]
    }
    //  --- CMP comparison block [cmp, cmp+80) ---
    else if i < cmp + 4 { double_dist_instrs(30, 7, 8, 1, cmp)[i - cmp] }
    else if i < cmp + 8 { double_dist_instrs(31, 9, 10, 1, (cmp + 4) as nat)[i - (cmp + 4)] }
    else if i < cmp + 31 { pair_sub_instrs(7, 9, 11, 12, 13, 14, 15, 1, 16, (cmp + 8) as nat)[i - (cmp + 8)] }
    else if i < cmp + 35 { double_dist_instrs(0, 17, 27, 1, (cmp + 31) as nat)[i - (cmp + 31)] }
    else if i < cmp + 38 { copy_instrs(27, 0, 1, (cmp + 35) as nat)[i - (cmp + 35)] }
    else if i < cmp + 43 { eq_test_instrs(16, 17, 1, (cmp + 44) as nat, (cmp + 38) as nat)[i - (cmp + 38)] }
    else if i < cmp + 44 { mk_inc(6) }
    else if i < cmp + 67 { pair_sub_instrs(10, 8, 18, 19, 20, 21, 22, 1, 23, (cmp + 44) as nat)[i - (cmp + 44)] }
    else if i < cmp + 71 { double_dist_instrs(0, 24, 28, 1, (cmp + 67) as nat)[i - (cmp + 67)] }
    else if i < cmp + 74 { copy_instrs(28, 0, 1, (cmp + 71) as nat)[i - (cmp + 71)] }
    else if i < cmp + 79 { eq_test_instrs(23, 24, 1, (cmp + 80) as nat, (cmp + 74) as nat)[i - (cmp + 74)] }
    else if i < cmp + 80 { mk_inc(6) }
    //  --- CONT: Inc scnt; DecJump{zero, INNER_TOP} ---
    else if i < cont + 1 { mk_inc(4) }
    else if i < cont + 2 { mk_dj(1, srm_it(e)) }
    //  --- IE: DISPATCH DecJump{result, OC}; HALT ---
    else if i < ie + 1 { mk_dj(6, oc as nat) }
    else if i < ie + 2 { Instruction::Halt }
    //  --- OC: clear scnt; Inc Treg; DecJump{zero, OUTER_TOP=0} ---
    else if i < oc + 2 { clear_instrs(4, 1, oc as nat)[i - oc] }
    else if i < oc + 3 { mk_inc(3) }
    else if i < oc + 4 { mk_dj(1, 0) }
    else { Instruction::Halt }
}

pub open spec fn search_rm(e: CEER) -> RegisterMachine {
    RegisterMachine {
        instructions: Seq::new(srm_total(e), |i: int| srm_instr(e, i)),
        num_regs: srm_numregs(e),
    }
}

///  Instruction access: `m.instructions[i] == srm_instr(e, i)` for in-range `i`.
pub proof fn lemma_srm_index(e: CEER, i: int)
    requires 0 <= i < srm_total(e),
    ensures search_rm(e).instructions[i] == srm_instr(e, i),
{
}

//  ============================================================
//  Well-formedness
//  ============================================================

pub open spec fn instr_wf(ins: Instruction, numregs: nat, total: nat) -> bool {
    match ins {
        Instruction::Inc { register } => register < numregs,
        Instruction::DecJump { register, target } => register < numregs && target <= total,
        Instruction::Halt => true,
    }
}

pub open spec fn block_wf(s: Seq<Instruction>, numregs: nat, total: nat) -> bool {
    forall|j: int| 0 <= j < s.len() ==> #[trigger] instr_wf(s[j], numregs, total)
}

proof fn lemma_clear_bank_block_wf(start_reg: nat, count: nat, zero: nat, sp: nat, numregs: nat, total: nat)
    requires
        zero < numregs,
        start_reg + count <= numregs,
        sp + 2 * count <= total,
    ensures
        block_wf(clear_bank_instrs(start_reg, count, zero, sp), numregs, total),
{
    let blk = clear_bank_instrs(start_reg, count, zero, sp);
    assert forall|j: int| 0 <= j < blk.len() implies #[trigger] instr_wf(blk[j], numregs, total) by {
        assert(blk.len() == 2 * count);
        if j % 2 == 0 {
            assert(j / 2 < count) by(nonlinear_arith) requires 0 <= j < 2 * count, j % 2 == 0;
            assert(start_reg + j / 2 < numregs);
            assert(sp + j + 2 <= total);
        } else {
            assert(sp + j - 1 <= total);
        }
    }
}

proof fn lemma_instrument_block_wf(e: CEER, numregs: nat, total: nat)
    requires
        ceer_wf(e),
        29 + srm_ne(e) == numregs,
        srm_cmp(e) <= total,
        srm_cont(e) <= total,
    ensures
        block_wf(instrument_instructions(e.enumerator.instructions, 29, srm_instr_pc(e),
            srm_cmp(e), srm_cont(e), 2, 1), numregs, total),
{
    reveal(machine_wf);
    assert(machine_wf(e.enumerator)) by { reveal(ceer_wf); }
    let ni = srm_ni(e);
    let ne = srm_ne(e);
    let blk = instrument_instructions(e.enumerator.instructions, 29, srm_instr_pc(e),
        srm_cmp(e), srm_cont(e), 2, 1);
    assert forall|j: int| 0 <= j < blk.len() implies #[trigger] instr_wf(blk[j], numregs, total) by {
        assert(blk.len() == 2 * ni);
        if j % 2 == 0 {
        } else {
            assert(j / 2 < ni) by(nonlinear_arith) requires 0 <= j < 2 * ni, j % 2 == 1;
            let instr = e.enumerator.instructions[j / 2];
            assert(match instr {
                Instruction::Inc { register } => register < ne,
                Instruction::DecJump { register, target } => register < ne && target <= ni,
                Instruction::Halt => true,
            });
            match instr {
                Instruction::Inc { register } => { assert(register + 29 < numregs); },
                Instruction::DecJump { register, target } => {
                    assert(register + 29 < numregs);
                    assert(srm_instr_pc(e) + 2 * target <= srm_cmp(e)) by { assert(target <= ni); }
                },
                Instruction::Halt => {},
            }
        }
    }
}

///  Each dispatched instruction is well formed (registers in bounds, targets `<= total`).
proof fn lemma_srm_instr_wf(e: CEER, i: int)
    requires ceer_wf(e), 0 <= i < srm_total(e),
    ensures instr_wf(srm_instr(e, i), srm_numregs(e), srm_total(e)),
{
    assert(srm_ne(e) >= 3) by { reveal(ceer_wf); }
    let ne = srm_ne(e);
    let nr = srm_numregs(e);
    let tot = srm_total(e);
    let cmp = srm_cmp(e);
    if i < 9 + 2 * ne {
        //  SETUP / guard / clear E-bank
        if i < 9 {
        } else {
            lemma_clear_bank_block_wf(29, ne, 1, 9, nr, tot);
            assert(instr_wf(clear_bank_instrs(29, ne, 1, 9)[i - 9], nr, tot));
        }
    } else if i < 30 + 2 * ne {
        //  clears, B2, B3 — small fixed gadgets, targets manifestly <= tot
    } else if i < cmp {
        lemma_instrument_block_wf(e, nr, tot);
        assert(instr_wf(instrument_instructions(e.enumerator.instructions, 29, srm_instr_pc(e),
            cmp, srm_cont(e), 2, 1)[i - (30 + 2 * ne)], nr, tot));
    } else if i < cmp + 80 {
        //  CMP comparison block — fixed gadgets (incl. pair_sub_instrs), targets within [cmp, cmp+80] <= tot
    } else {
        //  CONT / IE / OC tail — fixed, targets srm_it/srm_oc/0 <= tot
    }
}

pub proof fn lemma_search_rm_wf(e: CEER)
    requires ceer_wf(e),
    ensures
        machine_wf(search_rm(e)),
        search_rm(e).num_regs >= 3,
        search_rm(e).instructions.len() == srm_total(e),
{
    reveal(machine_wf);
    assert(srm_ne(e) >= 3) by { reveal(ceer_wf); }
    let m = search_rm(e);
    let nr = srm_numregs(e);
    let tot = srm_total(e);
    assert(m.instructions.len() == tot);
    assert(m.num_regs == nr);
    assert forall|i: int| #![trigger m.instructions[i]] 0 <= i < m.instructions.len()
    implies match m.instructions[i] {
        Instruction::Inc { register } => register < m.num_regs,
        Instruction::DecJump { register, target } => register < m.num_regs && target <= m.instructions.len(),
        Instruction::Halt => true,
    } by {
        lemma_srm_index(e, i);
        lemma_srm_instr_wf(e, i);
        assert(instr_wf(srm_instr(e, i), nr, tot));
    }
}

} //  verus!
