//  GAP-2 / L0 brick B-L0.2c/B-L0.3 — assemble the dovetail: inner body (one (T,s) iteration) from
//  the phase lemmas, the bounded inner loop over s, the outer round, and the halts-iff. See
//  search_rm_inner.rs for the phases and docs/gap2-l0-search-rm-plan.md.

use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::{CEER, ceer_wf, declared_pair};
use crate::search_rm::*;
use crate::search_rm_inner::*;
use crate::search_rm_arith::lemma_run_add;

verus! {

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

} //  verus!
