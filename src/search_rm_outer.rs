//  GAP-2 / L0 brick B-L0.2c/B-L0.3 — assemble the dovetail: inner body (one (T,s) iteration) from
//  the phase lemmas, the bounded inner loop over s, the outer round, and the halts-iff. See
//  search_rm_inner.rs for the phases and docs/gap2-l0-search-rm-plan.md.

use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::{CEER, ceer_wf, declared_pair};
use crate::ceer::{declared_equiv, stage_declares};
use crate::pairing::{pair, lemma_pair_injective};
use crate::search_rm::*;
use crate::search_rm_inner::*;
use crate::search_rm_arith::{lemma_run_add, lemma_double_dist_inner, lemma_run_preserves_len};
use crate::multi_output_primitives::{mk_inc, mk_dj, lemma_copy_loop_inner, lemma_not_halted_means_not_run_halts};
use crate::search_rm_compare::lemma_clear_loop;
use crate::conditional_halt::lemma_run_halts_split;

verus! {

//  ============================================================
//  Outer-loop top predicate + SETUP phase
//  ============================================================

///  At OUTER_TOP (pc 0) for bound T: Treg=T, scnt=cnt=result=0, zero=0, inp=inp_v, temps clean
///  (E-bank/fuel may be dirty — cleared at INNER_TOP).
pub open spec fn srm_at_outer_top(e: CEER, c: Configuration, inp_v: nat, t_v: nat) -> bool {
    &&& c.pc == 0
    &&& c.registers.len() == srm_numregs(e)
    &&& c.registers[0] == inp_v
    &&& c.registers[1] == 0
    &&& c.registers[3] == t_v
    &&& c.registers[4] == 0
    &&& c.registers[5] == 0
    &&& c.registers[6] == 0
    &&& srm_temps_top(c)
}

///  SETUP: cnt := T+1 via double_dist(Treg->cnt,bakA); copy(bakA->Treg); Inc cnt.  OUTER_TOP -> INNER_TOP.
#[verifier::rlimit(10000)]
pub proof fn lemma_srm_phase_setup(e: CEER, c: Configuration, inp_v: nat, t_v: nat)
    requires
        ceer_wf(e),
        srm_at_outer_top(e, c, inp_v, t_v),
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == 8
            && srm_at_top(e, run(search_rm(e), c, g), inp_v, t_v, 0, (t_v + 1) as nat, 0),
{
    let m = search_rm(e);
    let nr = srm_numregs(e);
    //  double_dist(3 -> 5, 25, sp=0): cnt:=T, bakA:=T, Treg:=0
    lemma_srm_outer_index(e, 0); lemma_srm_outer_index(e, 1);
    lemma_srm_outer_index(e, 2); lemma_srm_outer_index(e, 3);
    assert(m.instructions[0] == mk_dj(3, 4));
    assert(m.instructions[1] == mk_inc(5));
    assert(m.instructions[2] == mk_inc(25));
    assert(m.instructions[3] == mk_dj(1, 0));
    lemma_double_dist_inner(m, c, 3, 5, 25, 1, 0, 0, 0, t_v);
    let g1: nat = (4 * t_v + 1) as nat;
    let c1 = run(m, c, g1);
    lemma_run_preserves_len(m, c, g1);
    assert(c1.pc == 4);
    assert(c1.registers[5] == t_v && c1.registers[25] == t_v && c1.registers[3] == 0);
    assert(c1.registers[1] == 0) by { assert(1 != 3 && 1 != 5 && 1 != 25); }

    //  copy(25 -> 3, sp=4): Treg:=T, bakA:=0
    lemma_srm_outer_index(e, 4); lemma_srm_outer_index(e, 5); lemma_srm_outer_index(e, 6);
    assert(m.instructions[4] == mk_dj(25, 4 + 3));
    assert(m.instructions[5] == mk_inc(3));
    assert(m.instructions[6] == mk_dj(1, 4));
    lemma_copy_loop_inner(m, c1, 25, 3, 1, 4, t_v, 0, t_v);
    let g2: nat = (3 * t_v + 1) as nat;
    let c2 = run(m, c1, g2);
    lemma_run_preserves_len(m, c1, g2);
    assert(c2.pc == 7);
    assert(c2.registers[3] == t_v && c2.registers[25] == 0);
    assert(c2.registers[5] == t_v) by { assert(5 != 25 && 5 != 3); }

    //  Inc cnt(5) @7: cnt := T+1
    lemma_srm_outer_index(e, 7);
    assert(m.instructions[7] == mk_inc(5));
    assert(!is_halted(m, c2));
    let c3 = step(m, c2).unwrap();
    assert(c3.pc == 8);
    assert(c3.registers == c2.registers.update(5, (t_v + 1) as nat));
    assert(run(m, c2, 1) == c3) by { lemma_outer_run_unfold(m, c2, 1); }

    //  compose + postcondition
    lemma_run_add(m, c1, g2, 1);
    lemma_run_add(m, c, g1, (g2 + 1) as nat);
    let g: nat = (g1 + g2 + 1) as nat;
    assert(run(m, c, g) == c3);
    assert(c3.registers[5] == t_v + 1);
    //  every reg except {3(Treg),5(cnt),25(bakA)} preserved c -> c3
    assert forall|r: int| 0 <= r < nr as int && r != 3 && r != 5 && r != 25 implies c3.registers[r] == c.registers[r] by {
        assert(c1.registers[r] == c.registers[r]);
        assert(c2.registers[r] == c1.registers[r]);
        assert(c3.registers[r] == c2.registers[r]);
    }
    assert(srm_ctrl(e, c3, inp_v, t_v, 0, (t_v + 1) as nat, 0));
    assert(srm_temps_top(c3));
    assert(srm_at_top(e, c3, inp_v, t_v, 0, (t_v + 1) as nat, 0));
}

//  ============================================================
//  lemma_inner_body — one inner iteration: INNER_TOP(cnt>0) -> next INNER_TOP
//  ============================================================

#[verifier::rlimit(20000)]
pub proof fn lemma_inner_body(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_top(e, c, inp_v, t_v, s_v, cnt_v, r_v),
        cnt_v > 0,
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == 8
            && srm_at_top(e, run(search_rm(e), c, g), inp_v, t_v, (s_v + 1) as nat, (cnt_v - 1) as nat,
                    run(search_rm(e), c, g).registers[6])
            && run(search_rm(e), c, g).registers[6] >= r_v
            && (run(search_rm(e), c, g).registers[6] > r_v ==> declared_match(e, s_v, inp_v))
            && (run_halts(e.enumerator, initial_config(e.enumerator, s_v), t_v) && declared_match(e, s_v, inp_v)
                    ==> run(search_rm(e), c, g).registers[6] > r_v),
{
    let m = search_rm(e);
    let cm1 = (cnt_v - 1) as nat;
    let s1 = (s_v + 1) as nat;

    //  --- R1: top -> B2 ---
    lemma_srm_phase_r1(e, c, inp_v, t_v, s_v, cnt_v, r_v);
    let g1 = choose|g: nat| run(m, c, g).pc == srm_b2(e)
        && srm_at_b2(e, run(m, c, g), inp_v, t_v, s_v, cm1, r_v);
    let c_b2 = run(m, c, g1);

    //  --- R2a: B2 -> B3 ---
    lemma_srm_phase_r2a(e, c_b2, inp_v, t_v, s_v, cm1, r_v);
    let g2 = choose|g: nat| run(m, c_b2, g).pc == srm_b3(e)
        && srm_at_b3(e, run(m, c_b2, g), inp_v, t_v, s_v, cm1, r_v);
    let c_b3 = run(m, c_b2, g2);

    //  --- R2b: B3 -> instrument entry ---
    lemma_srm_phase_r2b(e, c_b3, inp_v, t_v, s_v, cm1, r_v);
    let g3 = choose|g: nat| run(m, c_b3, g).pc == srm_instr_pc(e)
        && srm_at_instr(e, run(m, c_b3, g), inp_v, t_v, s_v, cm1, r_v);
    let c_in = run(m, c_b3, g3);

    //  --- I: instrument -> sink ---
    lemma_srm_phase_i(e, c_in, inp_v, t_v, s_v, cm1, r_v);
    let g4 = choose|g: nat| run(m, c_in, g).registers.len() == srm_numregs(e)
        && srm_at_sink(e, run(m, c_in, g), inp_v, t_v, s_v, cm1, r_v);
    let c_s = run(m, c_in, g4);

    //  reduce to: from c_s reach next top with the result facts, in g5 steps.
    let g_pre = (g1 + g2 + g3 + g4) as nat;
    lemma_run_add(m, c_b3, g3, g4);
    lemma_run_add(m, c_b2, g2, (g3 + g4) as nat);
    lemma_run_add(m, c, g1, (g2 + g3 + g4) as nat);
    assert(run(m, c, g_pre) == c_s);

    if c_s.pc == srm_cmp(e) {
        //  --- halted case: C0 + C1 + C2 + F ---
        //  srm_at_sink @cmp gives run_halts(E,T+1) and the E-bridge forall; build srm_at_cmp.
        assert(run_halts(e.enumerator, initial_config(e.enumerator, s_v), (t_v + 1) as nat));
        assert(srm_at_cmp(e, c_s, inp_v, t_v, s_v, cm1, r_v));
        lemma_srm_phase_c0(e, c_s, inp_v, t_v, s_v, cm1, r_v);
        let g5 = choose|g: nat| run(m, c_s, g).pc == srm_cmp(e) + 8
            && srm_post_c0(e, run(m, c_s, g), inp_v, t_v, s_v, cm1, r_v);
        let c_c0 = run(m, c_s, g5);

        lemma_srm_phase_c1(e, c_c0, inp_v, t_v, s_v, cm1, r_v);
        let g6 = choose|g: nat| run(m, c_c0, g).pc == srm_cmp(e) + 44
            && srm_post_c1(e, run(m, c_c0, g), inp_v, t_v, s_v, cm1, r_v);
        let c_c1 = run(m, c_c0, g6);
        let r1 = if srm_match1(e, s_v, t_v, inp_v) { (r_v + 1) as nat } else { r_v };
        assert(srm_at_c44(e, c_c1, inp_v, t_v, s_v, cm1, r1));

        lemma_srm_phase_c2(e, c_c1, inp_v, t_v, s_v, cm1, r1);
        let r2 = if srm_match2(e, s_v, t_v, inp_v) { (r1 + 1) as nat } else { r1 };
        let g7 = choose|g: nat| run(m, c_c1, g).pc == srm_cont(e)
            && srm_at_cont(e, run(m, c_c1, g), inp_v, t_v, s_v, cm1, r2);
        let c_ct = run(m, c_c1, g7);

        lemma_srm_phase_f(e, c_ct, inp_v, t_v, s_v, cm1, r2);
        let g8 = choose|g: nat| run(m, c_ct, g).pc == 8
            && srm_at_top(e, run(m, c_ct, g), inp_v, t_v, s1, cm1, r2);
        let c_f = run(m, c_ct, g8);

        //  compose c_s -> c_f
        lemma_run_add(m, c_c1, g7, g8);
        lemma_run_add(m, c_c0, g6, (g7 + g8) as nat);
        lemma_run_add(m, c_s, g5, (g6 + g7 + g8) as nat);
        lemma_run_add(m, c, g_pre, (g5 + g6 + g7 + g8) as nat);
        let g: nat = (g_pre + g5 + g6 + g7 + g8) as nat;
        assert(run(m, c, g) == c_f);
        assert(c_f.registers[6] == r2);

        //  result facts: r2 >= r_v; r2 > r_v <=> match1 || match2 <=> declared_match
        lemma_srm_decl_is_declared(e, s_v, t_v);
        assert(declared_match(e, s_v, inp_v) == (srm_match1(e, s_v, t_v, inp_v) || srm_match2(e, s_v, t_v, inp_v))) by {
            assert(declared_pair(e, s_v) == Some((srm_decl1(e, s_v, t_v), srm_decl2(e, s_v, t_v))));
        }
        assert(r2 >= r_v);
        assert(r2 > r_v ==> declared_match(e, s_v, inp_v));
        assert(run_halts(e.enumerator, initial_config(e.enumerator, s_v), t_v)
            && declared_match(e, s_v, inp_v) ==> r2 > r_v);
        assert(srm_at_top(e, c_f, inp_v, t_v, s1, cm1, c_f.registers[6]));
    } else {
        //  --- timeout case: c_s.pc == cont; F directly. result unchanged. ---
        assert(c_s.pc == srm_cont(e));
        assert(srm_at_cont(e, c_s, inp_v, t_v, s_v, cm1, r_v)) by {
            assert(srm_temps_top(c_s));
        }
        lemma_srm_phase_f(e, c_s, inp_v, t_v, s_v, cm1, r_v);
        let g5 = choose|g: nat| run(m, c_s, g).pc == 8
            && srm_at_top(e, run(m, c_s, g), inp_v, t_v, s1, cm1, r_v);
        let c_f = run(m, c_s, g5);
        lemma_run_add(m, c, g_pre, g5);
        let g: nat = (g_pre + g5) as nat;
        assert(run(m, c, g) == c_f);
        assert(c_f.registers[6] == r_v);
        //  COMPLETE arm vacuous: run_halts(E,init(s),t_v) ⇒ c_s.pc == cmp, contradiction.
        assert(run_halts(e.enumerator, initial_config(e.enumerator, s_v), t_v)
            && declared_match(e, s_v, inp_v) ==> c_f.registers[6] > r_v) by {
            if run_halts(e.enumerator, initial_config(e.enumerator, s_v), t_v) {
                assert(c_s.pc == srm_cmp(e));   //  srm_at_sink completeness
                assert(false);
            }
        }
        assert(srm_at_top(e, c_f, inp_v, t_v, s1, cm1, c_f.registers[6]));
    }
}

//  ============================================================
//  lemma_inner_loop — the bounded loop over s; INNER_TOP(cnt) -> INNER_EXIT
//  ============================================================

#[verifier::rlimit(20000)]
pub proof fn lemma_inner_loop(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s0: nat, cnt_v: nat, r0: nat,
)
    requires
        ceer_wf(e),
        srm_at_top(e, c, inp_v, t_v, s0, cnt_v, r0),
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == srm_ie(e)
            && run(search_rm(e), c, g).registers.len() == srm_numregs(e)
            && run(search_rm(e), c, g).registers[0] == inp_v
            && run(search_rm(e), c, g).registers[3] == t_v
            && run(search_rm(e), c, g).registers[1] == 0
            && run(search_rm(e), c, g).registers[5] == 0
            && srm_temps_top(run(search_rm(e), c, g))
            && run(search_rm(e), c, g).registers[6] >= r0
            && (run(search_rm(e), c, g).registers[6] > r0 ==>
                    exists|s: nat| s0 <= s < s0 + cnt_v && declared_match(e, s, inp_v))
            && ((exists|s: nat| s0 <= s < s0 + cnt_v
                    && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                    && declared_match(e, s, inp_v))
                ==> run(search_rm(e), c, g).registers[6] > r0),
    decreases cnt_v,
{
    let m = search_rm(e);
    if cnt_v == 0 {
        //  guard at pc 8: DecJump{cnt=5, ie}; cnt==0 ⇒ jump to ie
        lemma_srm_outer_index(e, 8);
        assert(m.instructions[8] == mk_dj(5, srm_ie(e)));
        assert(c.registers[5] == 0);
        assert(!is_halted(m, c));
        let c1 = step(m, c).unwrap();
        assert(c1.pc == srm_ie(e));
        assert(c1.registers == c.registers);
        assert(run(m, c, 1) == c1) by { lemma_outer_run_unfold(m, c, 1); }
        assert(c1.registers[5] == 0);
        assert(srm_temps_top(c1));
        assert(c1.registers[6] >= r0);
        assert(c1.registers[6] > r0 ==> exists|s: nat| s0 <= s < s0 + cnt_v && declared_match(e, s, inp_v));
        assert((exists|s: nat| s0 <= s < s0 + cnt_v
            && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v) && declared_match(e, s, inp_v))
            ==> c1.registers[6] > r0);
    } else {
        //  one iteration via inner_body, then recurse
        lemma_inner_body(e, c, inp_v, t_v, s0, cnt_v, r0);
        let gb = choose|g: nat| run(m, c, g).pc == 8
            && srm_at_top(e, run(m, c, g), inp_v, t_v, (s0 + 1) as nat, (cnt_v - 1) as nat, run(m, c, g).registers[6])
            && run(m, c, g).registers[6] >= r0
            && (run(m, c, g).registers[6] > r0 ==> declared_match(e, s0, inp_v))
            && (run_halts(e.enumerator, initial_config(e.enumerator, s0), t_v) && declared_match(e, s0, inp_v)
                    ==> run(m, c, g).registers[6] > r0);
        let cn = run(m, c, gb);
        let rp = cn.registers[6];

        lemma_inner_loop(e, cn, inp_v, t_v, (s0 + 1) as nat, (cnt_v - 1) as nat, rp);
        let gr = choose|g: nat|
            run(m, cn, g).pc == srm_ie(e)
            && run(m, cn, g).registers.len() == srm_numregs(e)
            && run(m, cn, g).registers[0] == inp_v
            && run(m, cn, g).registers[3] == t_v
            && run(m, cn, g).registers[1] == 0
            && run(m, cn, g).registers[5] == 0
            && srm_temps_top(run(m, cn, g))
            && run(m, cn, g).registers[6] >= rp
            && (run(m, cn, g).registers[6] > rp ==>
                    exists|s: nat| (s0 + 1) <= s < (s0 + 1) + (cnt_v - 1) && declared_match(e, s, inp_v))
            && ((exists|s: nat| (s0 + 1) <= s < (s0 + 1) + (cnt_v - 1)
                    && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                    && declared_match(e, s, inp_v))
                ==> run(m, cn, g).registers[6] > rp);
        let cf = run(m, cn, gr);
        lemma_run_add(m, c, gb, gr);
        let g: nat = (gb + gr) as nat;
        assert(run(m, c, g) == cf);
        let rf = cf.registers[6];

        assert(rf >= r0) by { assert(rp >= r0); }
        //  SOUND
        assert(rf > r0 ==> exists|s: nat| s0 <= s < s0 + cnt_v && declared_match(e, s, inp_v)) by {
            if rf > r0 {
                if rp > r0 {
                    //  s0 declared
                    assert(declared_match(e, s0, inp_v));
                    assert(s0 <= s0 < s0 + cnt_v);
                } else {
                    assert(rp == r0);
                    assert(rf > rp);
                    let sw = choose|s: nat| (s0 + 1) <= s < (s0 + 1) + (cnt_v - 1) && declared_match(e, s, inp_v);
                    assert(s0 <= sw < s0 + cnt_v);
                    assert(declared_match(e, sw, inp_v));
                }
            }
        }
        //  COMPLETE
        assert((exists|s: nat| s0 <= s < s0 + cnt_v
            && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v) && declared_match(e, s, inp_v))
            ==> rf > r0) by {
            if exists|s: nat| s0 <= s < s0 + cnt_v
                && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v) && declared_match(e, s, inp_v) {
                let sw = choose|s: nat| s0 <= s < s0 + cnt_v
                    && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v) && declared_match(e, s, inp_v);
                if sw == s0 {
                    assert(rp > r0);
                } else {
                    assert((s0 + 1) <= sw < (s0 + 1) + (cnt_v - 1));
                    assert(rf > rp);
                }
            }
        }
    }
}

//  ============================================================
//  Dispatch: at INNER_EXIT, result>0 -> HALT; result==0 -> OUTER_CONT -> next OUTER_TOP
//  ============================================================

pub proof fn lemma_dispatch_halt(e: CEER, c: Configuration)
    requires
        ceer_wf(e),
        c.pc == srm_ie(e),
        c.registers.len() == srm_numregs(e),
        c.registers[6] > 0,
    ensures
        run_halts(search_rm(e), c, 1),
{
    let m = search_rm(e);
    lemma_srm_outer_index(e, srm_ie(e) as int);
    lemma_srm_outer_index(e, srm_ie(e) as int + 1);
    assert(m.instructions[srm_ie(e) as int] == mk_dj(6, srm_oc(e)));
    assert(m.instructions[(srm_ie(e) + 1) as int] == Instruction::Halt);
    assert(!is_halted(m, c));
    let c1 = step(m, c).unwrap();
    assert(c1.pc == srm_ie(e) + 1);   //  result>0 ⇒ decrement, fall through
    assert(is_halted(m, c1));
    assert(step(m, c) == Some(c1));
    assert(run_halts(m, c1, 0));
    assert(run_halts(m, c, 1));
}

#[verifier::rlimit(10000)]
pub proof fn lemma_dispatch_continue(e: CEER, c: Configuration, inp_v: nat, t_v: nat)
    requires
        ceer_wf(e),
        c.pc == srm_ie(e),
        c.registers.len() == srm_numregs(e),
        c.registers[0] == inp_v,
        c.registers[1] == 0,
        c.registers[3] == t_v,
        c.registers[5] == 0,
        c.registers[6] == 0,
        srm_temps_top(c),
    ensures
        exists|g: nat| g >= 1
            && #[trigger] run(search_rm(e), c, g).pc == 0
            && srm_at_outer_top(e, run(search_rm(e), c, g), inp_v, (t_v + 1) as nat)
            && !run_halts(search_rm(e), c, g),
{
    let m = search_rm(e);
    let nr = srm_numregs(e);
    let oc = srm_oc(e);
    //  DISPATCH: DecJump{6, oc}; result==0 ⇒ jump oc
    lemma_srm_outer_index(e, srm_ie(e) as int);
    assert(m.instructions[srm_ie(e) as int] == mk_dj(6, oc));
    assert(!is_halted(m, c));
    let c1 = step(m, c).unwrap();
    assert(c1.pc == oc);
    assert(c1.registers == c.registers);
    assert(run(m, c, 1) == c1) by { lemma_outer_run_unfold(m, c, 1); }

    //  OUTER_CONT: clear scnt(4) at oc
    lemma_srm_outer_index(e, oc as int);
    lemma_srm_outer_index(e, oc as int + 1);
    assert(m.instructions[oc as int] == mk_dj(4, oc + 2));
    assert(m.instructions[(oc + 1) as int] == mk_dj(1, oc));
    assert(c1.registers[1] == 0);
    lemma_clear_loop(m, c1, 4, 1, oc, c1.registers[4]);
    let gs: nat = (2 * c1.registers[4] + 1) as nat;
    let c2 = run(m, c1, gs);
    assert(c2.pc == oc + 2);
    assert(c2.registers[4] == 0);

    //  Inc Treg(3) at oc+2
    lemma_srm_outer_index(e, oc as int + 2);
    assert(m.instructions[(oc + 2) as int] == mk_inc(3));
    assert(!is_halted(m, c2));
    let c3 = step(m, c2).unwrap();
    assert(c3.pc == oc + 3);
    assert(c3.registers == c2.registers.update(3, (c2.registers[3] + 1) as nat));
    assert(run(m, c2, 1) == c3) by { lemma_outer_run_unfold(m, c2, 1); }

    //  DecJump{zero=1, 0} at oc+3; zero==0 ⇒ jump 0
    lemma_srm_outer_index(e, oc as int + 3);
    assert(m.instructions[(oc + 3) as int] == mk_dj(1, 0));
    assert(c3.registers[1] == 0) by { assert(1 != 3); }
    assert(!is_halted(m, c3));
    let c4 = step(m, c3).unwrap();
    assert(c4.pc == 0);
    assert(c4.registers == c3.registers);
    assert(run(m, c3, 1) == c4) by { lemma_outer_run_unfold(m, c3, 1); }

    //  compose
    lemma_run_add(m, c2, 1, 1);
    lemma_run_add(m, c1, gs, 2);
    lemma_run_add(m, c, 1, (gs + 2) as nat);
    let g: nat = (1 + gs + 2) as nat;
    assert(run(m, c, g) == c4);

    //  Treg = t+1
    assert(c2.registers[3] == c1.registers[3]) by { assert(3 != 4); }
    assert(c2.registers[3] == t_v);
    assert(c4.registers[3] == t_v + 1);
    //  everything except {3(Treg),4(scnt)} preserved c -> c4
    assert forall|r: int| 0 <= r < nr as int && r != 3 && r != 4 implies c4.registers[r] == c.registers[r] by {
        assert(c1.registers[r] == c.registers[r]);
        assert(c2.registers[r] == c1.registers[r]);
        assert(c3.registers[r] == c2.registers[r]);
        assert(c4.registers[r] == c3.registers[r]);
    }
    assert(srm_at_outer_top(e, c4, inp_v, (t_v + 1) as nat)) by {
        assert(c4.registers[0] == inp_v);
        assert(c4.registers[1] == 0);
        assert(c4.registers[5] == 0);
        assert(c4.registers[6] == 0);
        assert(c4.registers[4] == 0);
        assert(srm_temps_top(c4));
    }
    //  no halt: c4.pc==0 is a DecJump (SETUP), not halted ⇒ ¬run_halts within g
    assert(!is_halted(m, c4)) by { lemma_srm_outer_index(e, 0); }
    lemma_not_halted_means_not_run_halts(m, c, g);
}

//  ============================================================
//  Round: OUTER_TOP@t -> INNER_EXIT (dispatch), with result facts
//  ============================================================

#[verifier::rlimit(15000)]
pub proof fn lemma_round_to_dispatch(e: CEER, c: Configuration, inp_v: nat, t_v: nat)
    requires
        ceer_wf(e),
        srm_at_outer_top(e, c, inp_v, t_v),
    ensures
        exists|g: nat| g >= 1
            && #[trigger] run(search_rm(e), c, g).pc == srm_ie(e)
            && run(search_rm(e), c, g).registers.len() == srm_numregs(e)
            && run(search_rm(e), c, g).registers[0] == inp_v
            && run(search_rm(e), c, g).registers[1] == 0
            && run(search_rm(e), c, g).registers[3] == t_v
            && run(search_rm(e), c, g).registers[5] == 0
            && srm_temps_top(run(search_rm(e), c, g))
            && !run_halts(search_rm(e), c, g)
            && (run(search_rm(e), c, g).registers[6] > 0 ==>
                    exists|s: nat| s < t_v + 1 && declared_match(e, s, inp_v))
            && ((exists|s: nat| s < t_v + 1
                    && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                    && declared_match(e, s, inp_v))
                ==> run(search_rm(e), c, g).registers[6] > 0),
{
    let m = search_rm(e);
    //  SETUP -> INNER_TOP@(cnt=t+1, s0=0, r0=0)
    lemma_srm_phase_setup(e, c, inp_v, t_v);
    let gs = choose|g: nat| run(m, c, g).pc == 8
        && srm_at_top(e, run(m, c, g), inp_v, t_v, 0, (t_v + 1) as nat, 0);
    let ctop = run(m, c, gs);

    //  inner_loop over s = 0..t  (cnt = t+1)
    lemma_inner_loop(e, ctop, inp_v, t_v, 0, (t_v + 1) as nat, 0);
    let gi = choose|g: nat|
        run(m, ctop, g).pc == srm_ie(e)
        && run(m, ctop, g).registers.len() == srm_numregs(e)
        && run(m, ctop, g).registers[0] == inp_v
        && run(m, ctop, g).registers[3] == t_v
        && run(m, ctop, g).registers[1] == 0
        && run(m, ctop, g).registers[5] == 0
        && srm_temps_top(run(m, ctop, g))
        && run(m, ctop, g).registers[6] >= 0
        && (run(m, ctop, g).registers[6] > 0 ==>
                exists|s: nat| 0 <= s < 0 + (t_v + 1) && declared_match(e, s, inp_v))
        && ((exists|s: nat| 0 <= s < 0 + (t_v + 1)
                && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                && declared_match(e, s, inp_v))
            ==> run(m, ctop, g).registers[6] > 0);
    let cd = run(m, ctop, gi);
    lemma_run_add(m, c, gs, gi);
    let g: nat = (gs + gi) as nat;
    assert(run(m, c, g) == cd);
    assert(gs >= 1) by { if gs == 0 { assert(run(m, c, 0) == c); } }
    assert(g >= 1);
    assert(!is_halted(m, cd)) by { lemma_srm_outer_index(e, srm_ie(e) as int); }
    lemma_not_halted_means_not_run_halts(m, c, g);
}

//  ============================================================
//  Outer inductions + halts-iff
//  ============================================================

///  ⟸ : if some round T_w >= t detects a declaring stage, the machine halts from c.
#[verifier::rlimit(15000)]
pub proof fn lemma_outer_reaches(e: CEER, c: Configuration, inp_v: nat, t_v: nat, tw: nat)
    requires
        ceer_wf(e),
        srm_at_outer_top(e, c, inp_v, t_v),
        t_v <= tw,
        exists|s: nat| s < tw + 1
            && run_halts(e.enumerator, initial_config(e.enumerator, s), tw)
            && declared_match(e, s, inp_v),
    ensures
        exists|fuel: nat| run_halts(search_rm(e), c, fuel),
    decreases tw - t_v,
{
    let m = search_rm(e);
    lemma_round_to_dispatch(e, c, inp_v, t_v);
    let gd = choose_round(e, c, inp_v, t_v);
    let cd = run(m, c, gd);
    if cd.registers[6] > 0 {
        lemma_dispatch_halt(e, cd);
        //  ¬run_halts(M,c,gd) ⇒ ¬run_halts(M,c,gd-1); split at gd-1, f2=1
        lemma_run_monotone_neg(m, c, (gd - 1) as nat, gd);
        lemma_run_halts_split(m, c, (gd - 1) as nat, 1);
        assert((gd - 1) + 1 + 1 == gd + 1);
        assert(run_halts(m, c, (gd + 1) as nat));
    } else {
        //  cd[6]==0 ⇒ (round COMPLETE contrapositive) no declaring stage at round t_v ⇒ t_v < tw
        assert(t_v < tw) by {
            if t_v == tw {
                assert(exists|s: nat| s < t_v + 1
                    && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                    && declared_match(e, s, inp_v));
                assert(cd.registers[6] > 0);
            }
        }
        lemma_dispatch_continue(e, cd, inp_v, t_v);
        let gc = choose_continue(e, cd, inp_v, t_v);
        let cn = run(m, cd, gc);
        lemma_outer_reaches(e, cn, inp_v, (t_v + 1) as nat, tw);
        let f = choose|fuel: nat| run_halts(m, cn, fuel);
        lemma_run_add(m, c, gd, gc);
        assert(run(m, c, (gd + gc) as nat) == cn);
        assert(!is_halted(m, cn)) by { lemma_srm_outer_index(e, 0); }
        lemma_not_halted_means_not_run_halts(m, c, (gd + gc) as nat);
        //  ¬run_halts(M,c,gd+gc) ⇒ ¬run_halts(M,c,gd+gc-1); split, f2=f
        lemma_run_monotone_neg(m, c, (gd + gc - 1) as nat, (gd + gc) as nat);
        lemma_run_halts_split(m, c, (gd + gc - 1) as nat, f);
        assert((gd + gc - 1) + f + 1 == gd + gc + f);
        assert(run_halts(m, c, (gd + gc + f) as nat));
    }
}

///  ⟹ (contrapositive): if no stage declares, the machine never halts from c.
#[verifier::rlimit(15000)]
pub proof fn lemma_outer_loops(e: CEER, c: Configuration, inp_v: nat, t_v: nat, fuel: nat)
    requires
        ceer_wf(e),
        srm_at_outer_top(e, c, inp_v, t_v),
        forall|s: nat| !declared_match(e, s, inp_v),
    ensures
        !run_halts(search_rm(e), c, fuel),
    decreases fuel,
{
    let m = search_rm(e);
    lemma_round_to_dispatch(e, c, inp_v, t_v);
    let gd = choose_round(e, c, inp_v, t_v);
    let cd = run(m, c, gd);
    //  result == 0 (SOUND: result>0 ⇒ some declared_match, contradiction)
    assert(cd.registers[6] == 0) by {
        if cd.registers[6] > 0 {
            let sw = choose|s: nat| s < t_v + 1 && declared_match(e, s, inp_v);
            assert(!declared_match(e, sw, inp_v));
        }
    }
    lemma_dispatch_continue(e, cd, inp_v, t_v);
    let gc = choose_continue(e, cd, inp_v, t_v);
    let cn = run(m, cd, gc);
    lemma_run_add(m, c, gd, gc);
    let gtot: nat = (gd + gc) as nat;
    assert(run(m, c, gtot) == cn);
    assert(gtot >= 1) by { assert(gd >= 1); }
    assert(!is_halted(m, cn)) by { lemma_srm_outer_index(e, 0); }
    lemma_not_halted_means_not_run_halts(m, c, gtot);
    if fuel <= gtot {
        lemma_run_monotone_neg(m, c, fuel, gtot);
    } else {
        lemma_outer_loops(e, cn, inp_v, (t_v + 1) as nat, (fuel - gtot) as nat);
        lemma_run_monotone_neg(m, c, (gtot - 1) as nat, gtot);
        lemma_run_halts_split(m, c, (gtot - 1) as nat, (fuel - gtot) as nat);
        assert((gtot - 1) + (fuel - gtot) + 1 == fuel);
    }
}

///  declared_match against pair(a,b) is exactly stage_declares(e,s,a,b).
pub proof fn lemma_declared_match_iff_stage(e: CEER, s: nat, a: nat, b: nat)
    ensures declared_match(e, s, pair(a, b)) <==> stage_declares(e, s, a, b),
{
    match declared_pair(e, s) {
        Some(pr) => {
            if pair(pr.0, pr.1) == pair(a, b) { lemma_pair_injective(pr.0, pr.1, a, b); }
            if pair(pr.1, pr.0) == pair(a, b) { lemma_pair_injective(pr.1, pr.0, a, b); }
            if pr.0 == a && pr.1 == b { }
            if pr.0 == b && pr.1 == a { }
        },
        None => {},
    }
}

///  THE HALTS-IFF (B-L0.3): search_rm(e) halts on pair(a,b) iff (a,b) is declared at some stage.
pub proof fn lemma_search_rm_halts_iff(e: CEER, a: nat, b: nat)
    requires ceer_wf(e),
    ensures
        halts(search_rm(e), pair(a, b)) <==> declared_equiv(e, a, b),
{
    let m = search_rm(e);
    let inp = pair(a, b);
    let init = initial_config(m, inp);
    assert(srm_numregs(e) > 0) by { reveal(ceer_wf); }
    assert(srm_at_outer_top(e, init, inp, 0)) by {
        assert(init.registers[0] == inp);
        assert(forall|i: int| 1 <= i < srm_numregs(e) as int ==> init.registers[i] == 0);
    }
    //  ⟸
    if declared_equiv(e, a, b) {
        let s0 = choose|s: nat| stage_declares(e, s, a, b);
        lemma_declared_match_iff_stage(e, s0, a, b);
        assert(declared_match(e, s0, inp));
        //  declared_pair Some ⇒ halts(E, s0)
        assert(halts(e.enumerator, s0)) by {
            match declared_pair(e, s0) { Some(_) => { reveal(ceer_wf); }, None => {} }
        }
        let f0 = choose|f: nat| run_halts(e.enumerator, initial_config(e.enumerator, s0), f);
        let tw = if s0 >= f0 { s0 } else { f0 };
        assert(s0 < tw + 1);
        assert(run_halts(e.enumerator, initial_config(e.enumerator, s0), tw)) by {
            lemma_run_monotone(e.enumerator, initial_config(e.enumerator, s0), f0, tw);
        }
        assert(exists|s: nat| s < tw + 1
            && run_halts(e.enumerator, initial_config(e.enumerator, s), tw)
            && declared_match(e, s, inp));
        lemma_outer_reaches(e, init, inp, 0, tw);
        let fuel = choose|fuel: nat| run_halts(m, init, fuel);
        assert(halts(m, inp));
    }
    //  ⟹
    if halts(m, inp) {
        let big = choose|fuel: nat| run_halts(m, init, fuel);
        if !declared_equiv(e, a, b) {
            assert forall|s: nat| !declared_match(e, s, inp) by {
                lemma_declared_match_iff_stage(e, s, a, b);
                assert(!stage_declares(e, s, a, b));
            }
            lemma_outer_loops(e, init, inp, 0, big);
            assert(false);
        }
    }
}

///  choose helper: extract the round-to-dispatch witness g.
proof fn choose_round(e: CEER, c: Configuration, inp_v: nat, t_v: nat) -> (g: nat)
    requires
        ceer_wf(e),
        srm_at_outer_top(e, c, inp_v, t_v),
    ensures
        g >= 1
        && run(search_rm(e), c, g).pc == srm_ie(e)
        && run(search_rm(e), c, g).registers.len() == srm_numregs(e)
        && run(search_rm(e), c, g).registers[0] == inp_v
        && run(search_rm(e), c, g).registers[1] == 0
        && run(search_rm(e), c, g).registers[3] == t_v
        && run(search_rm(e), c, g).registers[5] == 0
        && srm_temps_top(run(search_rm(e), c, g))
        && !run_halts(search_rm(e), c, g)
        && (run(search_rm(e), c, g).registers[6] > 0 ==>
                exists|s: nat| s < t_v + 1 && declared_match(e, s, inp_v))
        && ((exists|s: nat| s < t_v + 1
                && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                && declared_match(e, s, inp_v))
            ==> run(search_rm(e), c, g).registers[6] > 0),
{
    lemma_round_to_dispatch(e, c, inp_v, t_v);
    let m = search_rm(e);
    choose|g: nat| g >= 1
        && run(m, c, g).pc == srm_ie(e)
        && run(m, c, g).registers.len() == srm_numregs(e)
        && run(m, c, g).registers[0] == inp_v
        && run(m, c, g).registers[1] == 0
        && run(m, c, g).registers[3] == t_v
        && run(m, c, g).registers[5] == 0
        && srm_temps_top(run(m, c, g))
        && !run_halts(m, c, g)
        && (run(m, c, g).registers[6] > 0 ==>
                exists|s: nat| s < t_v + 1 && declared_match(e, s, inp_v))
        && ((exists|s: nat| s < t_v + 1
                && run_halts(e.enumerator, initial_config(e.enumerator, s), t_v)
                && declared_match(e, s, inp_v))
            ==> run(m, c, g).registers[6] > 0)
}

///  choose helper: extract the dispatch-continue witness g.
proof fn choose_continue(e: CEER, c: Configuration, inp_v: nat, t_v: nat) -> (g: nat)
    requires
        ceer_wf(e),
        c.pc == srm_ie(e),
        c.registers.len() == srm_numregs(e),
        c.registers[0] == inp_v, c.registers[1] == 0, c.registers[3] == t_v,
        c.registers[5] == 0, c.registers[6] == 0, srm_temps_top(c),
    ensures
        g >= 1
        && run(search_rm(e), c, g).pc == 0
        && srm_at_outer_top(e, run(search_rm(e), c, g), inp_v, (t_v + 1) as nat)
        && !run_halts(search_rm(e), c, g),
{
    lemma_dispatch_continue(e, c, inp_v, t_v);
    let m = search_rm(e);
    choose|g: nat| g >= 1
        && run(m, c, g).pc == 0
        && srm_at_outer_top(e, run(m, c, g), inp_v, (t_v + 1) as nat)
        && !run_halts(m, c, g)
}

///  Monotonicity (negative): ¬run_halts at the larger fuel ⇒ ¬run_halts at the smaller.
proof fn lemma_run_monotone_neg(m: RegisterMachine, c: Configuration, f1: nat, f2: nat)
    requires f1 <= f2, !run_halts(m, c, f2),
    ensures !run_halts(m, c, f1),
{
    if run_halts(m, c, f1) {
        lemma_run_monotone(m, c, f1, f2);
        assert(false);
    }
}

///  Local index/unfold helpers for this module.
proof fn lemma_srm_outer_index(e: CEER, i: int)
    requires 0 <= i < srm_total(e),
    ensures search_rm(e).instructions[i] == srm_instr(e, i),
{
    lemma_srm_index(e, i);
}

proof fn lemma_outer_run_unfold(m: RegisterMachine, c: Configuration, fuel: nat)
    requires !is_halted(m, c), fuel > 0,
    ensures run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

} //  verus!
