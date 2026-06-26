//  GAP-2 / L0 brick B-L0.2c — the dovetailing search register machine `search_rm(e)`.
//
//  ONE `RegisterMachine` whose halting on input `pair(a,b)` is exactly `declared_equiv(e,a,b)`. It
//  dovetails an outer bound `T = 0,1,2,…` over an inner stage loop `s = 0..=T`, simulating the
//  enumerator `E = e.enumerator` for `T+1` fuel via the B-L0.1 `instrument`, and re-pairing each
//  declared output to compare (both orientations) against the preserved input. See
//  docs/gap2-l0-search-rm-plan.md (B-L0.2c / B-L0.3).
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
//    clear ii1, clear ii2
//    B2 load scnt -> E[0]   B3 set fuel := T+1
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

//  ============================================================
//  Block instruction sequences
//  ============================================================

///  SETUP (8 instrs at pc 0): `cnt := T+1` via double_dist(Treg -> cnt, bakA); copy(bakA -> Treg); Inc cnt.
pub open spec fn srm_setup_instrs() -> Seq<Instruction> {
    double_dist_instrs(3, 5, 25, 1, 0)
        + copy_instrs(25, 3, 1, 4)
        + seq![mk_inc(5)]
}

///  CMP comparison block (80 instrs at `cmp`): backup the declared pair, then for each of the two
///  orientations compute the forward `pair` and destructively compare to a fresh copy of `inp`,
///  incrementing `result` on a match.
pub open spec fn srm_cmp_instrs(cmp: nat, ie: nat) -> Seq<Instruction> {
    double_dist_instrs(30, 7, 8, 1, cmp)                                //  bk1: E[1] -> d1A,d1B   [4]
        + double_dist_instrs(31, 9, 10, 1, cmp + 4)                     //  bk2: E[2] -> d2A,d2B   [4]
        + pair_sub_instrs(7, 9, 11, 12, 13, 14, 15, 1, 16, cmp + 8)    //  o1 pair(d1,d2)->p1      [23]
        + double_dist_instrs(0, 17, 27, 1, cmp + 31)                    //  o1 load inp -> ic1,bakC [4]
        + copy_instrs(27, 0, 1, cmp + 35)                              //  o1 restore inp          [3]
        + eq_test_instrs(16, 17, 1, cmp + 44, cmp + 38)                //  o1 eq_test(p1,ic1)      [5]
        + seq![mk_inc(6)]                                              //  o1 Inc result           [1]
        + pair_sub_instrs(10, 8, 18, 19, 20, 21, 22, 1, 23, cmp + 44) //  o2 pair(d2,d1)->p2      [23]
        + double_dist_instrs(0, 24, 28, 1, cmp + 67)                    //  o2 load inp -> ic2,bakD [4]
        + copy_instrs(28, 0, 1, cmp + 71)                              //  o2 restore inp          [3]
        + eq_test_instrs(23, 24, 1, cmp + 80, cmp + 74)                //  o2 eq_test(p2,ic2)      [5]
        + seq![mk_inc(6)]                                              //  o2 Inc result           [1]
}

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
//  The machine
//  ============================================================

pub open spec fn search_rm(e: CEER) -> RegisterMachine {
    RegisterMachine {
        instructions:
            srm_setup_instrs()                                                       //  [0,8)
            + seq![mk_dj(5, srm_ie(e))]                                              //  INNER_TOP guard
            + clear_bank_instrs(29, srm_ne(e), 1, srm_b1(e))                         //  clear E-bank
            + clear_instrs(13, 1, srm_clrii1(e))                                     //  clear ii1
            + clear_instrs(20, 1, srm_clrii2(e))                                     //  clear ii2
            + double_dist_instrs(4, 29, 25, 1, srm_b2(e))                            //  B2: scnt -> E[0],bakA
            + copy_instrs(25, 4, 1, srm_b2(e) + 4)                                   //  B2: restore scnt
            + clear_instrs(2, 1, srm_b3(e))                                          //  B3: clear fuel
            + double_dist_instrs(3, 2, 26, 1, srm_b3(e) + 2)                         //  B3: Treg -> fuel,bakB
            + seq![mk_inc(2)]                                                        //  B3: fuel := T+1
            + copy_instrs(26, 3, 1, srm_b3(e) + 7)                                   //  B3: restore Treg
            + instrument_instructions(e.enumerator.instructions, 29, srm_instr_pc(e),
                  srm_cmp(e), srm_cont(e), 2, 1)                                     //  instrument(E)
            + srm_cmp_instrs(srm_cmp(e), srm_ie(e))                                  //  CMP comparison
            + seq![mk_inc(4), mk_dj(1, srm_it(e))]                                   //  CONT: Inc scnt; loop
            + seq![mk_dj(6, srm_oc(e)), Instruction::Halt]                           //  IE: dispatch; HALT
            + clear_instrs(4, 1, srm_oc(e))                                          //  OC: clear scnt
            + seq![mk_inc(3), mk_dj(1, 0)],                                          //  OC: Inc Treg; loop OT
        num_regs: srm_numregs(e),
    }
}

//  ============================================================
//  Well-formedness (modular: block_wf preserved by concatenation)
//  ============================================================

pub open spec fn instr_wf(ins: Instruction, numregs: nat, total: nat) -> bool {
    match ins {
        Instruction::Inc { register } => register < numregs,
        Instruction::DecJump { register, target } => register < numregs && target <= total,
        Instruction::Halt => true,
    }
}

pub open spec fn block_wf(s: Seq<Instruction>, numregs: nat, total: nat) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] instr_wf(s[i], numregs, total)
}

proof fn lemma_block_wf_concat(a: Seq<Instruction>, b: Seq<Instruction>, numregs: nat, total: nat)
    requires block_wf(a, numregs, total), block_wf(b, numregs, total),
    ensures block_wf(a + b, numregs, total),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies #[trigger] instr_wf((a + b)[i], numregs, total) by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
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
            //  DecJump{start_reg + j/2, sp + j + 2}
            assert(j / 2 < count) by(nonlinear_arith) requires 0 <= j < 2 * count, j % 2 == 0;
            assert(start_reg + j / 2 < numregs);
            assert(sp + j + 2 <= total);
        } else {
            //  DecJump{zero, sp + j - 1}
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
            //  guard DecJump{2, srm_cont(e)}
        } else {
            //  body = instrument_body(E.instructions[j/2], 29, srm_instr_pc, srm_cmp, 1)
            assert(j / 2 < ni) by(nonlinear_arith) requires 0 <= j < 2 * ni, j % 2 == 1;
            let instr = e.enumerator.instructions[j / 2];
            //  machine_wf(E): the j/2-th instruction is well formed
            assert(match instr {
                Instruction::Inc { register } => register < ne,
                Instruction::DecJump { register, target } => register < ne && target <= ni,
                Instruction::Halt => true,
            });
            match instr {
                Instruction::Inc { register } => { assert(register + 29 < numregs); },
                Instruction::DecJump { register, target } => {
                    assert(register + 29 < numregs);
                    assert(srm_instr_pc(e) + 2 * target <= srm_cmp(e)) by {
                        assert(target <= ni);
                    }
                },
                Instruction::Halt => {},
            }
        }
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

    //  --- length ---
    assert(m.instructions.len() == tot);

    //  --- block_wf of each summand ---
    let b0 = srm_setup_instrs();
    let b1 = seq![mk_dj(5, srm_ie(e))];
    let b2 = clear_bank_instrs(29, srm_ne(e), 1, srm_b1(e));
    let b3 = clear_instrs(13, 1, srm_clrii1(e));
    let b4 = clear_instrs(20, 1, srm_clrii2(e));
    let b5 = double_dist_instrs(4, 29, 25, 1, srm_b2(e));
    let b6 = copy_instrs(25, 4, 1, srm_b2(e) + 4);
    let b7 = clear_instrs(2, 1, srm_b3(e));
    let b8 = double_dist_instrs(3, 2, 26, 1, srm_b3(e) + 2);
    let b9 = seq![mk_inc(2)];
    let b10 = copy_instrs(26, 3, 1, srm_b3(e) + 7);
    let b11 = instrument_instructions(e.enumerator.instructions, 29, srm_instr_pc(e),
        srm_cmp(e), srm_cont(e), 2, 1);
    let b12 = srm_cmp_instrs(srm_cmp(e), srm_ie(e));
    let b13 = seq![mk_inc(4), mk_dj(1, srm_it(e))];
    let b14 = seq![mk_dj(6, srm_oc(e)), Instruction::Halt];
    let b15 = clear_instrs(4, 1, srm_oc(e));
    let b16 = seq![mk_inc(3), mk_dj(1, 0)];

    assert(block_wf(b0, nr, tot));
    assert(block_wf(b1, nr, tot));
    lemma_clear_bank_block_wf(29, srm_ne(e), 1, srm_b1(e), nr, tot);
    assert(block_wf(b3, nr, tot));
    assert(block_wf(b4, nr, tot));
    assert(block_wf(b5, nr, tot));
    assert(block_wf(b6, nr, tot));
    assert(block_wf(b7, nr, tot));
    assert(block_wf(b8, nr, tot));
    assert(block_wf(b9, nr, tot));
    assert(block_wf(b10, nr, tot));
    lemma_instrument_block_wf(e, nr, tot);
    lemma_srm_cmp_block_wf(e, nr, tot);
    assert(block_wf(b13, nr, tot));
    assert(block_wf(b14, nr, tot));
    assert(block_wf(b15, nr, tot));
    assert(block_wf(b16, nr, tot));

    //  --- fold the concatenation ---
    lemma_block_wf_concat(b0, b1, nr, tot);
    lemma_block_wf_concat(b0 + b1, b2, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2, b3, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3, b4, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4, b5, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5, b6, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6, b7, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7, b8, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8, b9, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9, b10, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10, b11, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11, b12, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12, b13, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13, b14, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14, b15, nr, tot);
    lemma_block_wf_concat(b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15, b16, nr, tot);
    assert(m.instructions == b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15 + b16);
    assert(block_wf(m.instructions, nr, tot));

    //  --- conclude machine_wf ---
    assert(m.num_regs == nr);
    assert forall|i: int| #![trigger m.instructions[i]] 0 <= i < m.instructions.len()
    implies match m.instructions[i] {
        Instruction::Inc { register } => register < m.num_regs,
        Instruction::DecJump { register, target } => register < m.num_regs && target <= m.instructions.len(),
        Instruction::Halt => true,
    } by {
        assert(instr_wf(m.instructions[i], nr, tot));
    }
}

///  block_wf of the 80-instruction CMP block.
proof fn lemma_srm_cmp_block_wf(e: CEER, numregs: nat, total: nat)
    requires
        ceer_wf(e),
        29 + srm_ne(e) == numregs,
        srm_cmp(e) + 80 <= total,
        srm_ie(e) <= total,
    ensures
        block_wf(srm_cmp_instrs(srm_cmp(e), srm_ie(e)), numregs, total),
{
    assert(srm_ne(e) >= 3) by { reveal(ceer_wf); }
    let cmp = srm_cmp(e);
    let ie = srm_ie(e);
    let p1 = pair_sub_instrs(7, 9, 11, 12, 13, 14, 15, 1, 16, cmp + 8);
    let p2 = pair_sub_instrs(10, 8, 18, 19, 20, 21, 22, 1, 23, cmp + 44);
    let d_bk1 = double_dist_instrs(30, 7, 8, 1, cmp);
    let d_bk2 = double_dist_instrs(31, 9, 10, 1, cmp + 4);
    let d_o1 = double_dist_instrs(0, 17, 27, 1, cmp + 31);
    let c_o1 = copy_instrs(27, 0, 1, cmp + 35);
    let eq_o1 = eq_test_instrs(16, 17, 1, cmp + 44, cmp + 38);
    let d_o2 = double_dist_instrs(0, 24, 28, 1, cmp + 67);
    let c_o2 = copy_instrs(28, 0, 1, cmp + 71);
    let eq_o2 = eq_test_instrs(23, 24, 1, cmp + 80, cmp + 74);
    assert(block_wf(d_bk1, numregs, total));
    assert(block_wf(d_bk2, numregs, total));
    assert(block_wf(p1, numregs, total));
    assert(block_wf(d_o1, numregs, total));
    assert(block_wf(c_o1, numregs, total));
    assert(block_wf(eq_o1, numregs, total));
    assert(block_wf(seq![mk_inc(6)], numregs, total));
    assert(block_wf(p2, numregs, total));
    assert(block_wf(d_o2, numregs, total));
    assert(block_wf(c_o2, numregs, total));
    assert(block_wf(eq_o2, numregs, total));
    lemma_block_wf_concat(d_bk1, d_bk2, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2, p1, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1, d_o1, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1, c_o1, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1, eq_o1, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1, seq![mk_inc(6)], numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1 + seq![mk_inc(6)], p2, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1 + seq![mk_inc(6)] + p2, d_o2, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1 + seq![mk_inc(6)] + p2 + d_o2, c_o2, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1 + seq![mk_inc(6)] + p2 + d_o2 + c_o2, eq_o2, numregs, total);
    lemma_block_wf_concat(d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1 + seq![mk_inc(6)] + p2 + d_o2 + c_o2 + eq_o2, seq![mk_inc(6)], numregs, total);
    assert(srm_cmp_instrs(cmp, ie) ==
        d_bk1 + d_bk2 + p1 + d_o1 + c_o1 + eq_o1 + seq![mk_inc(6)] + p2 + d_o2 + c_o2 + eq_o2 + seq![mk_inc(6)]);
}

} //  verus!
