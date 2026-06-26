//  GAP-2 / L0 brick B-L0.2c/B-L0.3 — assemble the dovetail: inner body (one (T,s) iteration) from
//  the phase lemmas, the bounded inner loop over s, the outer round, and the halts-iff. See
//  search_rm_inner.rs for the phases and docs/gap2-l0-search-rm-plan.md.

use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::{CEER, ceer_wf, declared_pair};
use crate::search_rm::*;
use crate::search_rm_inner::*;
use crate::search_rm_arith::{lemma_run_add, lemma_double_dist_inner, lemma_run_preserves_len};
use crate::multi_output_primitives::{mk_inc, mk_dj, lemma_copy_loop_inner};
use crate::search_rm_compare::lemma_clear_loop;

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
