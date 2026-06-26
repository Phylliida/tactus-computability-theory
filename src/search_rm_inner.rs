//  GAP-2 / L0 brick B-L0.2c — the dovetail inner body (one (T,s) iteration), built as small phase
//  lemmas (each ~4 gadgets, isolated budget) chained via `lemma_run_add`. See search_rm.rs for the
//  machine layout and docs/gap2-l0-search-rm-plan.md (B-L0.2c).

use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::{CEER, ceer_wf};
use crate::multi_output_primitives::{mk_inc, mk_dj, lemma_copy_loop_inner};
use crate::search_rm_clearbank::{clear_bank_instrs, lemma_clear_bank};
use crate::search_rm_compare::lemma_clear_loop;
use crate::search_rm_arith::{lemma_run_add, lemma_double_dist_inner, lemma_run_preserves_len};
use crate::search_rm_sim::{instr_configs_agree, instrument_frame, instrument_instructions};
use crate::search_rm_outcome::lemma_instrument_outcome;
use crate::search_rm::*;

verus! {

//  ============================================================
//  Register invariants
//  ============================================================

///  Every working temporary EXCEPT ii1(13)/ii2(20) is zero. At INNER_TOP the ii's may be dirty (from
///  the previous iteration's pair subroutines); they are cleared in the reset phase.
pub open spec fn srm_temps_top(c: Configuration) -> bool {
    &&& c.registers[7] == 0   && c.registers[8] == 0   && c.registers[9] == 0   && c.registers[10] == 0
    &&& c.registers[11] == 0  && c.registers[12] == 0  && c.registers[14] == 0  && c.registers[15] == 0
    &&& c.registers[16] == 0  && c.registers[17] == 0
    &&& c.registers[18] == 0  && c.registers[19] == 0  && c.registers[21] == 0  && c.registers[22] == 0
    &&& c.registers[23] == 0  && c.registers[24] == 0
    &&& c.registers[25] == 0  && c.registers[26] == 0  && c.registers[27] == 0  && c.registers[28] == 0
}

///  All working temporaries are zero (incl. ii1/ii2) — holds from B2 through the CMP entry.
pub open spec fn srm_temps_zero(c: Configuration) -> bool {
    &&& srm_temps_top(c)
    &&& c.registers[13] == 0
    &&& c.registers[20] == 0
}

///  Control registers: zero, inp, Treg, scnt, cnt, result (NOT fuel, which is set in the reset phase).
pub open spec fn srm_ctrl(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.registers.len() == srm_numregs(e)
    &&& c.registers[1] == 0
    &&& c.registers[0] == inp_v
    &&& c.registers[3] == t_v
    &&& c.registers[4] == s_v
    &&& c.registers[5] == cnt_v
    &&& c.registers[6] == r_v
}

///  The whole E-bank [29, 29+ne) is zero.
pub open spec fn srm_ebank_zero(e: CEER, c: Configuration) -> bool {
    forall|r: int| 29 <= r < 29 + srm_ne(e) ==> #[trigger] c.registers[r] == 0
}

///  The E-bank holds `initial_config(E, s)`: reg 0 = s, the rest 0.
pub open spec fn srm_ebank_init(e: CEER, c: Configuration, s_v: nat) -> bool {
    &&& c.registers[29] == s_v
    &&& (forall|r: int| 30 <= r < 29 + srm_ne(e) ==> #[trigger] c.registers[r] == 0)
}

///  At INNER_TOP with the per-iteration register state (ii1/ii2 may be dirty).
pub open spec fn srm_at_top(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == 8
    &&& srm_ctrl(e, c, inp_v, t_v, s_v, cnt_v, r_v)
    &&& srm_temps_top(c)
}

///  At B2 (post-reset): E-bank all zero.
pub open spec fn srm_at_b2(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == srm_b2(e)
    &&& srm_ctrl(e, c, inp_v, t_v, s_v, cnt_v, r_v)
    &&& srm_temps_zero(c)
    &&& srm_ebank_zero(e, c)
}

///  At B3 (post-load-scnt): E-bank = initial_config(E, s).
pub open spec fn srm_at_b3(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == srm_b3(e)
    &&& srm_ctrl(e, c, inp_v, t_v, s_v, cnt_v, r_v)
    &&& srm_temps_zero(c)
    &&& srm_ebank_init(e, c, s_v)
}

///  At the instrument entry (post-set-fuel): E-bank = initial_config(E, s), fuel = T+1 (= phi).
pub open spec fn srm_at_instr(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == srm_instr_pc(e)
    &&& srm_ctrl(e, c, inp_v, t_v, s_v, cnt_v, r_v)
    &&& srm_temps_zero(c)
    &&& srm_ebank_init(e, c, s_v)
    &&& c.registers[2] == t_v + 1
}

//  ============================================================
//  Phase R1 — guard (cnt>0) + clear E-bank + clear ii1 + clear ii2.  INNER_TOP -> B2.
//  ============================================================

#[verifier::rlimit(8000)]
pub proof fn lemma_srm_phase_r1(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_top(e, c, inp_v, t_v, s_v, cnt_v, r_v),
        cnt_v > 0,
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == srm_b2(e)
            && srm_at_b2(e, run(search_rm(e), c, g), inp_v, t_v, s_v, (cnt_v - 1) as nat, r_v),
{
    reveal(ceer_wf);
    let m = search_rm(e);
    let ne = srm_ne(e);
    let nr = srm_numregs(e);

    //  --- guard at pc 8: DecJump{cnt=5, ie}; cnt>0 ⇒ decrement, pc 8->9 ---
    lemma_srm_index(e, 8);
    assert(m.instructions[8] == mk_dj(5, srm_ie(e)));
    assert(!is_halted(m, c));
    let c0 = step(m, c).unwrap();
    assert(c0.pc == 9);
    assert(c0.registers == c.registers.update(5, (cnt_v - 1) as nat));
    assert(run(m, c, 1) == c0) by { lemma_run_unfold(m, c, 1); }

    //  --- clear E-bank: clear_bank(29, ne, 1, 9) ---
    assert forall|j: int| 0 <= j < 2 * ne implies
        m.instructions[(9 + j) as int] == #[trigger] clear_bank_instrs(29, ne, 1, 9)[j]
    by {
        lemma_srm_index(e, 9 + j);
        assert(srm_instr(e, 9 + j) == clear_bank_instrs(29, ne, 1, 9)[j]);
    }
    assert(c0.registers[1] == 0) by { assert(5 != 1); }
    lemma_clear_bank(m, c0, 29, ne, 1, 9);
    let g1 = choose|g: nat|
        run(m, c0, g).pc == 9 + 2 * ne
        && run(m, c0, g).registers.len() == m.num_regs
        && (forall|r: int| 0 <= r < m.num_regs as int ==>
                run(m, c0, g).registers[r] == (if 29 <= r && r < 29 + ne { 0nat } else { c0.registers[r] }));
    let c1 = run(m, c0, g1);
    assert(m.num_regs == nr);
    assert(c1.pc == 9 + 2 * ne);
    assert(c1.pc == srm_clrii1(e));

    //  --- clear ii1 at clrii1: clear_instrs(13, 1, clrii1) ---
    lemma_srm_index(e, srm_clrii1(e) as int);
    lemma_srm_index(e, srm_clrii1(e) as int + 1);
    assert(m.instructions[srm_clrii1(e) as int] == mk_dj(13, srm_clrii1(e) + 2));
    assert(m.instructions[(srm_clrii1(e) + 1) as int] == mk_dj(1, srm_clrii1(e)));
    assert(c1.pc == srm_clrii1(e));
    assert(c1.registers[1] == 0) by { assert(!(29 <= 1 < 29 + ne)); }
    lemma_clear_loop(m, c1, 13, 1, srm_clrii1(e), c1.registers[13]);
    let s2: nat = (2 * c1.registers[13] + 1) as nat;
    let c2 = run(m, c1, s2);
    assert(c2.pc == srm_clrii2(e));
    assert(c2.registers[13] == 0);

    //  --- clear ii2 at clrii2: clear_instrs(20, 1, clrii2) ---
    lemma_srm_index(e, srm_clrii2(e) as int);
    lemma_srm_index(e, srm_clrii2(e) as int + 1);
    assert(m.instructions[srm_clrii2(e) as int] == mk_dj(20, srm_clrii2(e) + 2));
    assert(m.instructions[(srm_clrii2(e) + 1) as int] == mk_dj(1, srm_clrii2(e)));
    assert(c2.registers[1] == 0) by { assert(20 != 13); }
    lemma_clear_loop(m, c2, 20, 1, srm_clrii2(e), c2.registers[20]);
    let s3: nat = (2 * c2.registers[20] + 1) as nat;
    let c3 = run(m, c2, s3);
    assert(c3.pc == srm_clrii2(e) + 2);
    assert(c3.pc == srm_b2(e));
    assert(c3.registers[20] == 0);

    //  --- compose: run(m, c, g) == c3 ---
    lemma_run_add(m, c1, s2, s3);
    lemma_run_add(m, c0, g1, (s2 + s3) as nat);
    lemma_run_add(m, c, 1, (g1 + s2 + s3) as nat);
    let g: nat = (1 + g1 + s2 + s3) as nat;
    assert(run(m, c, g) == c3);

    //  --- register postconditions ---
    //  control + temps preserved through the three clears (none touches 0,1,3,4,5(after guard),6 or non-ii temps)
    assert(c3.registers.len() == nr);
    assert(c3.registers[1] == 0);
    assert(c3.registers[0] == inp_v);
    assert(c3.registers[3] == t_v);
    assert(c3.registers[4] == s_v);
    assert(c3.registers[5] == (cnt_v - 1) as nat);
    assert(c3.registers[6] == r_v);
    assert(c3.registers[13] == 0) by { assert(c2.registers[13] == 0); }
    assert(srm_temps_zero(c3));
    assert(srm_ebank_zero(e, c3)) by {
        //  E-bank zeroed by clear_bank; ii-clears (regs 13,20) don't touch r>=29
        assert forall|r: int| 29 <= r < 29 + ne implies #[trigger] c3.registers[r] == 0 by {
            assert(c1.registers[r] == 0);
        }
    }
    assert(srm_at_b2(e, c3, inp_v, t_v, s_v, (cnt_v - 1) as nat, r_v));
}

//  ============================================================
//  Phase R2a — load scnt into E[0] (preserving scnt).  B2 -> B3.
//  ============================================================

#[verifier::rlimit(8000)]
pub proof fn lemma_srm_phase_r2a(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_b2(e, c, inp_v, t_v, s_v, cnt_v, r_v),
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == srm_b3(e)
            && srm_at_b3(e, run(search_rm(e), c, g), inp_v, t_v, s_v, cnt_v, r_v),
{
    reveal(ceer_wf);
    let m = search_rm(e);
    let ne = srm_ne(e);
    let b2 = srm_b2(e);

    //  --- double_dist(scnt=4 -> E0=29, bakA=25, zero=1, sp=b2) ---
    lemma_srm_index(e, b2 as int);
    lemma_srm_index(e, b2 as int + 1);
    lemma_srm_index(e, b2 as int + 2);
    lemma_srm_index(e, b2 as int + 3);
    assert(m.instructions[b2 as int] == mk_dj(4, b2 + 4));
    assert(m.instructions[(b2 + 1) as int] == mk_inc(29));
    assert(m.instructions[(b2 + 2) as int] == mk_inc(25));
    assert(m.instructions[(b2 + 3) as int] == mk_dj(1, b2));
    assert(c.registers[29] == 0) by { assert(srm_ebank_zero(e, c)); }
    lemma_double_dist_inner(m, c, 4, 29, 25, 1, b2, 0, 0, s_v);
    let d1s: nat = (4 * s_v + 1) as nat;
    let c1 = run(m, c, d1s);
    lemma_run_preserves_len(m, c, d1s);
    assert(c1.pc == b2 + 4);
    assert(c1.registers[29] == s_v);
    assert(c1.registers[25] == s_v);
    assert(c1.registers[4] == 0);
    assert(c1.registers[1] == 0) by { assert(1 != 4 && 1 != 29 && 1 != 25); }

    //  --- copy(bakA=25 -> scnt=4, zero=1, sp=b2+4) ---
    lemma_srm_index(e, b2 as int + 4);
    lemma_srm_index(e, b2 as int + 5);
    lemma_srm_index(e, b2 as int + 6);
    assert(m.instructions[(b2 + 4) as int] == mk_dj(25, b2 + 4 + 3));
    assert(m.instructions[(b2 + 5) as int] == mk_inc(4));
    assert(m.instructions[(b2 + 6) as int] == mk_dj(1, b2 + 4));
    lemma_copy_loop_inner(m, c1, 25, 4, 1, (b2 + 4) as nat, s_v, 0, s_v);
    let c2s: nat = (3 * s_v + 1) as nat;
    let c2 = run(m, c1, c2s);
    lemma_run_preserves_len(m, c1, c2s);
    assert(c2.pc == b2 + 7);
    assert(c2.pc == srm_b3(e));
    assert(c2.registers[4] == s_v);
    assert(c2.registers[25] == 0);

    //  --- compose ---
    lemma_run_add(m, c, d1s, c2s);
    let g: nat = (d1s + c2s) as nat;
    assert(run(m, c, g) == c2);

    //  --- postcondition ---
    assert(srm_ctrl(e, c2, inp_v, t_v, s_v, cnt_v, r_v));
    assert(srm_temps_zero(c2)) by {
        //  only reg 25 touched (then restored to 0); others preserved
    }
    assert(srm_ebank_init(e, c2, s_v)) by {
        assert(c2.registers[29] == s_v) by { assert(29 != 25 && 29 != 4); }
        assert forall|r: int| 30 <= r < 29 + ne implies #[trigger] c2.registers[r] == 0 by {
            assert(c.registers[r] == 0) by { assert(srm_ebank_zero(e, c)); }
        }
    }
    assert(srm_at_b3(e, c2, inp_v, t_v, s_v, cnt_v, r_v));
}

//  ============================================================
//  Phase R2b — set fuel := T+1 (preserving Treg).  B3 -> instrument entry.
//  ============================================================

#[verifier::rlimit(10000)]
pub proof fn lemma_srm_phase_r2b(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_b3(e, c, inp_v, t_v, s_v, cnt_v, r_v),
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == srm_instr_pc(e)
            && srm_at_instr(e, run(search_rm(e), c, g), inp_v, t_v, s_v, cnt_v, r_v),
{
    reveal(ceer_wf);
    let m = search_rm(e);
    let ne = srm_ne(e);
    let b3 = srm_b3(e);

    //  --- clear fuel: clear_instrs(2, 1, b3) ---
    lemma_srm_index(e, b3 as int);
    lemma_srm_index(e, b3 as int + 1);
    assert(m.instructions[b3 as int] == mk_dj(2, b3 + 2));
    assert(m.instructions[(b3 + 1) as int] == mk_dj(1, b3));
    lemma_clear_loop(m, c, 2, 1, b3, c.registers[2]);
    let f1: nat = (2 * c.registers[2] + 1) as nat;
    let c1 = run(m, c, f1);
    assert(c1.pc == b3 + 2);
    assert(c1.registers[2] == 0);
    assert(c1.registers[1] == 0) by { assert(1 != 2); }

    //  --- double_dist(Treg=3 -> fuel=2, bakB=26, zero=1, sp=b3+2) ---
    lemma_srm_index(e, b3 as int + 2);
    lemma_srm_index(e, b3 as int + 3);
    lemma_srm_index(e, b3 as int + 4);
    lemma_srm_index(e, b3 as int + 5);
    assert(m.instructions[(b3 + 2) as int] == mk_dj(3, b3 + 2 + 4));
    assert(m.instructions[(b3 + 3) as int] == mk_inc(2));
    assert(m.instructions[(b3 + 4) as int] == mk_inc(26));
    assert(m.instructions[(b3 + 5) as int] == mk_dj(1, b3 + 2));
    assert(c1.registers[3] == t_v) by { assert(3 != 2); }
    assert(c1.registers[26] == 0) by { assert(26 != 2); }
    lemma_double_dist_inner(m, c1, 3, 2, 26, 1, (b3 + 2) as nat, 0, 0, t_v);
    let f2: nat = (4 * t_v + 1) as nat;
    let c2 = run(m, c1, f2);
    lemma_run_preserves_len(m, c1, f2);
    assert(c2.pc == b3 + 6);
    assert(c2.registers[2] == t_v);
    assert(c2.registers[26] == t_v);
    assert(c2.registers[3] == 0);

    //  --- Inc fuel at b3+6: fuel := T+1 ---
    lemma_srm_index(e, b3 as int + 6);
    assert(m.instructions[(b3 + 6) as int] == mk_inc(2));
    assert(!is_halted(m, c2));
    let c3 = step(m, c2).unwrap();
    assert(c3.pc == b3 + 7);
    assert(c3.registers == c2.registers.update(2, (t_v + 1) as nat));
    assert(run(m, c2, 1) == c3) by { lemma_run_unfold(m, c2, 1); }
    assert(c3.registers[2] == t_v + 1);
    assert(c3.registers[26] == t_v) by { assert(26 != 2); }
    assert(c3.registers[3] == 0) by { assert(3 != 2); }
    assert(c3.registers[1] == 0) by { assert(1 != 2); }

    //  --- copy(bakB=26 -> Treg=3, zero=1, sp=b3+7) ---
    lemma_srm_index(e, b3 as int + 7);
    lemma_srm_index(e, b3 as int + 8);
    lemma_srm_index(e, b3 as int + 9);
    assert(m.instructions[(b3 + 7) as int] == mk_dj(26, b3 + 7 + 3));
    assert(m.instructions[(b3 + 8) as int] == mk_inc(3));
    assert(m.instructions[(b3 + 9) as int] == mk_dj(1, b3 + 7));
    lemma_copy_loop_inner(m, c3, 26, 3, 1, (b3 + 7) as nat, t_v, 0, t_v);
    let f4: nat = (3 * t_v + 1) as nat;
    let c4 = run(m, c3, f4);
    lemma_run_preserves_len(m, c3, f4);
    assert(c4.pc == b3 + 10);
    assert(c4.pc == srm_instr_pc(e));
    assert(c4.registers[3] == t_v);
    assert(c4.registers[26] == 0);
    assert(c4.registers[2] == t_v + 1) by { assert(2 != 26 && 2 != 3); }

    //  --- compose ---
    lemma_run_add(m, c2, 1, f4);
    lemma_run_add(m, c1, f2, (1 + f4) as nat);
    lemma_run_add(m, c, f1, (f2 + 1 + f4) as nat);
    let g: nat = (f1 + f2 + 1 + f4) as nat;
    assert(run(m, c, g) == c4);

    //  --- postcondition ---
    //  every reg except {2(fuel),3(Treg),26(bakB)} is preserved c -> c4 (chain the 4 gadget frames)
    let nr = srm_numregs(e);
    assert forall|r: int| 0 <= r < nr as int && r != 2 && r != 3 && r != 26
        implies c4.registers[r] == c.registers[r] by {
        assert(c1.registers[r] == c.registers[r]);
        assert(c2.registers[r] == c1.registers[r]);
        assert(c3.registers[r] == c2.registers[r]);
        assert(c4.registers[r] == c3.registers[r]);
    }
    assert(srm_ctrl(e, c4, inp_v, t_v, s_v, cnt_v, r_v));
    assert(srm_temps_zero(c4));
    assert(srm_ebank_init(e, c4, s_v)) by {
        assert forall|r: int| 30 <= r < 29 + ne implies #[trigger] c4.registers[r] == 0 by {
            assert(c.registers[r] == 0) by { assert(srm_ebank_init(e, c, s_v)); }
        }
    }
    assert(srm_at_instr(e, c4, inp_v, t_v, s_v, cnt_v, r_v));
}

//  ============================================================
//  Phase I — run the instrument; land on CMP (halted) or CONT (timeout).
//  ============================================================

///  At the instrument sink: the host is on CMP (halted) or CONT (timeout), control + temps preserved,
///  and the E-bridge holds: reaching CMP ⟺-strong the enumerator halted within T+1, E-bank == its
///  halt config; and if the enumerator halts within T, CMP is reached.
pub open spec fn srm_at_sink(e: CEER, cs: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& (cs.pc == srm_cmp(e) || cs.pc == srm_cont(e))
    &&& srm_ctrl(e, cs, inp_v, t_v, s_v, cnt_v, r_v)
    &&& srm_temps_zero(cs)
    &&& (cs.pc == srm_cmp(e) ==>
            run_halts(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat)
            && (forall|r: int| 0 <= r < srm_ne(e) ==>
                    #[trigger] cs.registers[29 + r]
                        == run(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat).registers[r]))
    &&& (run_halts(e.enumerator, initial_config(e.enumerator, s_v), t_v) ==> cs.pc == srm_cmp(e))
}

#[verifier::rlimit(8000)]
pub proof fn lemma_srm_phase_i(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_instr(e, c, inp_v, t_v, s_v, cnt_v, r_v),
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).registers.len() == srm_numregs(e)
            && srm_at_sink(e, run(search_rm(e), c, g), inp_v, t_v, s_v, cnt_v, r_v),
{
    reveal(ceer_wf);
    let m = search_rm(e);
    let ne = srm_ne(e);
    let ni = srm_ni(e);
    let nr = srm_numregs(e);
    let cmp = srm_cmp(e);
    let cont = srm_cont(e);
    let ipc = srm_instr_pc(e);
    let phi = (t_v + 1) as nat;
    let csub = initial_config(e.enumerator, s_v);
    assert(machine_wf(e.enumerator));
    assert(config_wf(e.enumerator, csub));

    //  --- instr_configs_agree ---
    assert(csub.pc == 0);
    assert(c.pc == ipc) by { assert(srm_at_instr(e, c, inp_v, t_v, s_v, cnt_v, r_v)); }
    assert forall|r: int| 0 <= r < ne as int implies c.registers[(r + 29) as int] == csub.registers[r] by {
        if r == 0 {
            assert(c.registers[29] == s_v) by { assert(srm_ebank_init(e, c, s_v)); }
            assert(csub.registers[0] == s_v);
        } else {
            assert(c.registers[(r + 29) as int] == 0) by { assert(srm_ebank_init(e, c, s_v)); }
            assert(csub.registers[r] == 0);
        }
    }
    assert(c.registers[1] == 0);
    assert(c.registers[2] == phi);
    assert(instr_configs_agree(e.enumerator, 29, ipc, 2, 1, phi, csub, c));

    //  --- instrument_frame ---
    assert forall|j: int| 0 <= j < 2 * ni implies
        m.instructions[(ipc + j) as int] == #[trigger] instrument_instructions(e.enumerator.instructions, 29, ipc, cmp, cont, 2, 1)[j]
    by {
        lemma_srm_index(e, ipc + j);
        assert(srm_instr(e, ipc + j) == instrument_instructions(e.enumerator.instructions, 29, ipc, cmp, cont, 2, 1)[j]);
    }
    assert(instrument_frame(e.enumerator, m, 29, ipc, cmp, cont, 2, 1)) by {
        assert(cmp == ipc + 2 * ni);
        assert(cmp <= m.instructions.len());
    }

    //  --- run the instrument ---
    lemma_instrument_outcome(e.enumerator, m, 29, ipc, cmp, cont, 2, 1, csub, c, phi);
    let g = choose|g: nat| g <= 2 * phi + 1
        && (run(m, c, g).pc == cmp || run(m, c, g).pc == cont)
        && run(m, c, g).registers.len() == m.num_regs
        && (run(m, c, g).pc == cmp ==>
                run_halts(e.enumerator, csub, phi)
                && (forall|r: int| 0 <= r < e.enumerator.num_regs as int ==>
                        #[trigger] run(m, c, g).registers[(r + 29) as int] == run(e.enumerator, csub, phi).registers[r]))
        && (run_halts(e.enumerator, csub, (phi - 1) as nat) ==> run(m, c, g).pc == cmp)
        && run(m, c, g).registers[1] == 0
        && (forall|jj: int| 0 <= jj < m.num_regs as int
                && (jj < 29 || jj >= 29 + e.enumerator.num_regs)
                && jj != 2 && jj != 1
                ==> #[trigger] run(m, c, g).registers[jj] == c.registers[jj]);
    let cs = run(m, c, g);
    assert(cs.registers.len() == nr);

    //  --- derive srm_at_sink(cs) ---
    //  control + temps preserved (all < 29, != 2, != 1, except reg 1 which == 0 separately)
    assert(srm_ctrl(e, cs, inp_v, t_v, s_v, cnt_v, r_v)) by {
        assert(cs.registers[0] == c.registers[0]) by { assert(0 < 29 && 0 != 2 && 0 != 1); }
        assert(cs.registers[3] == c.registers[3]) by { assert(3 < 29 && 3 != 2 && 3 != 1); }
        assert(cs.registers[4] == c.registers[4]) by { assert(4 < 29 && 4 != 2 && 4 != 1); }
        assert(cs.registers[5] == c.registers[5]) by { assert(5 < 29 && 5 != 2 && 5 != 1); }
        assert(cs.registers[6] == c.registers[6]) by { assert(6 < 29 && 6 != 2 && 6 != 1); }
    }
    assert(srm_temps_zero(cs)) by {
        //  each temp t in 7..28 (not 13,20): t<29, t!=2, t!=1, so cs[t]==c[t]==0
    }
    //  E-bridge: phi == t_v+1, phi-1 == t_v
    assert((phi - 1) as nat == t_v);
    assert(srm_at_sink(e, cs, inp_v, t_v, s_v, cnt_v, r_v)) by {
        //  soundness arm
        if cs.pc == cmp {
            assert(run_halts(e.enumerator, csub, phi));
            assert forall|r: int| 0 <= r < ne as int implies
                #[trigger] cs.registers[29 + r] == run(e.enumerator, csub, phi).registers[r] by {
                assert(cs.registers[(r + 29) as int] == run(e.enumerator, csub, phi).registers[r]);
                assert((r + 29) as int == 29 + r);
            }
        }
        //  completeness arm: run_halts within t_v (= phi-1) ⇒ cmp
        assert(run_halts(e.enumerator, csub, t_v) ==> cs.pc == cmp);
    }
}

//  ============================================================
//  CMP comparison phases
//  ============================================================

///  The enumerator's declared pair at stage s with fuel T+1: (reg1, reg2) of the halt config.
pub open spec fn srm_decl1(e: CEER, s_v: nat, t_v: nat) -> nat {
    run(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat).registers[1]
}
pub open spec fn srm_decl2(e: CEER, s_v: nat, t_v: nat) -> nat {
    run(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat).registers[2]
}

///  All registers 11..28 are zero (the pair/eq/backup working set + ii1/ii2; NOT the d-backups 7..10).
pub open spec fn srm_work_zero(c: Configuration) -> bool {
    &&& c.registers[11] == 0 && c.registers[12] == 0 && c.registers[13] == 0 && c.registers[14] == 0
    &&& c.registers[15] == 0 && c.registers[16] == 0 && c.registers[17] == 0 && c.registers[18] == 0
    &&& c.registers[19] == 0 && c.registers[20] == 0 && c.registers[21] == 0 && c.registers[22] == 0
    &&& c.registers[23] == 0 && c.registers[24] == 0 && c.registers[25] == 0 && c.registers[26] == 0
    &&& c.registers[27] == 0 && c.registers[28] == 0
}

///  At CMP (halted): control + temps zero + the E-bridge (E-bank == enumerator halt config @ T+1).
pub open spec fn srm_at_cmp(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == srm_cmp(e)
    &&& srm_ctrl(e, c, inp_v, t_v, s_v, cnt_v, r_v)
    &&& srm_temps_zero(c)
    &&& run_halts(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat)
    &&& (forall|r: int| 0 <= r < srm_ne(e) ==>
            #[trigger] c.registers[29 + r]
                == run(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat).registers[r])
}

///  After C0 (backups): d1A=d1B=d1, d2A=d2B=d2; working set 11..28 still zero.
pub open spec fn srm_post_c0(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == srm_cmp(e) + 8
    &&& srm_ctrl(e, c, inp_v, t_v, s_v, cnt_v, r_v)
    &&& c.registers[7] == srm_decl1(e, s_v, t_v) && c.registers[8] == srm_decl1(e, s_v, t_v)
    &&& c.registers[9] == srm_decl2(e, s_v, t_v) && c.registers[10] == srm_decl2(e, s_v, t_v)
    &&& srm_work_zero(c)
}

#[verifier::rlimit(8000)]
pub proof fn lemma_srm_phase_c0(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_cmp(e, c, inp_v, t_v, s_v, cnt_v, r_v),
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == srm_cmp(e) + 8
            && srm_post_c0(e, run(search_rm(e), c, g), inp_v, t_v, s_v, cnt_v, r_v),
{
    reveal(ceer_wf);
    let m = search_rm(e);
    let ne = srm_ne(e);
    let cmp = srm_cmp(e);
    let d1 = srm_decl1(e, s_v, t_v);
    let d2 = srm_decl2(e, s_v, t_v);
    assert(ne >= 3);
    assert(c.registers[30] == d1) by {
        let r1: int = 1;
        assert(0 <= r1 < ne);
        assert(c.registers[29 + r1] == run(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat).registers[r1]);
    }
    assert(c.registers[31] == d2) by {
        let r2: int = 2;
        assert(0 <= r2 < ne);
        assert(c.registers[29 + r2] == run(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat).registers[r2]);
    }

    //  --- bk1: double_dist(E1=30 -> d1A=7, d1B=8, zero=1, sp=cmp) ---
    lemma_srm_index(e, cmp as int);
    lemma_srm_index(e, cmp as int + 1);
    lemma_srm_index(e, cmp as int + 2);
    lemma_srm_index(e, cmp as int + 3);
    assert(m.instructions[cmp as int] == mk_dj(30, cmp + 4));
    assert(m.instructions[(cmp + 1) as int] == mk_inc(7));
    assert(m.instructions[(cmp + 2) as int] == mk_inc(8));
    assert(m.instructions[(cmp + 3) as int] == mk_dj(1, cmp));
    lemma_double_dist_inner(m, c, 30, 7, 8, 1, cmp, 0, 0, d1);
    let s1: nat = (4 * d1 + 1) as nat;
    let c1 = run(m, c, s1);
    lemma_run_preserves_len(m, c, s1);
    assert(c1.pc == cmp + 4);
    assert(c1.registers[7] == d1 && c1.registers[8] == d1);
    assert(c1.registers[31] == d2) by { assert(31 != 30 && 31 != 7 && 31 != 8); }
    assert(c1.registers[9] == 0) by { assert(9 != 30 && 9 != 7 && 9 != 8); }
    assert(c1.registers[10] == 0) by { assert(10 != 30 && 10 != 7 && 10 != 8); }
    assert(c1.registers[1] == 0) by { assert(1 != 30 && 1 != 7 && 1 != 8); }

    //  --- bk2: double_dist(E2=31 -> d2A=9, d2B=10, zero=1, sp=cmp+4) ---
    lemma_srm_index(e, cmp as int + 4);
    lemma_srm_index(e, cmp as int + 5);
    lemma_srm_index(e, cmp as int + 6);
    lemma_srm_index(e, cmp as int + 7);
    assert(m.instructions[(cmp + 4) as int] == mk_dj(31, cmp + 4 + 4));
    assert(m.instructions[(cmp + 5) as int] == mk_inc(9));
    assert(m.instructions[(cmp + 6) as int] == mk_inc(10));
    assert(m.instructions[(cmp + 7) as int] == mk_dj(1, cmp + 4));
    lemma_double_dist_inner(m, c1, 31, 9, 10, 1, (cmp + 4) as nat, 0, 0, d2);
    let s2: nat = (4 * d2 + 1) as nat;
    let c2 = run(m, c1, s2);
    lemma_run_preserves_len(m, c1, s2);
    assert(c2.pc == cmp + 8);
    assert(c2.registers[9] == d2 && c2.registers[10] == d2);
    assert(c2.registers[7] == d1) by { assert(7 != 31 && 7 != 9 && 7 != 10); }
    assert(c2.registers[8] == d1) by { assert(8 != 31 && 8 != 9 && 8 != 10); }

    //  --- compose ---
    lemma_run_add(m, c, s1, s2);
    let g: nat = (s1 + s2) as nat;
    assert(run(m, c, g) == c2);

    //  --- postcondition ---
    let nr = srm_numregs(e);
    assert forall|r: int| 0 <= r < nr as int && r != 30 && r != 31 && r != 7 && r != 8 && r != 9 && r != 10
        implies c2.registers[r] == c.registers[r] by {
        assert(c1.registers[r] == c.registers[r]);
        assert(c2.registers[r] == c1.registers[r]);
    }
    assert(srm_ctrl(e, c2, inp_v, t_v, s_v, cnt_v, r_v));
    assert(srm_work_zero(c2));
    assert(srm_post_c0(e, c2, inp_v, t_v, s_v, cnt_v, r_v));
}

///  Local `run` unfold helper (private copy).
proof fn lemma_run_unfold(m: RegisterMachine, c: Configuration, fuel: nat)
    requires !is_halted(m, c), fuel > 0,
    ensures run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

} //  verus!
