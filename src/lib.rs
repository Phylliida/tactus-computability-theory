// tactus-computability-theory — the ZFC -> CEER -> finitely-presented-group pipeline.
// Goal: theorem_zfc_equiv_in_fp_group() in higman.rs (ZFC provable-equivalence
// is the word problem of a f.p. group). This is the 22-module goal cone of
// verus-computability-theory; the vestigial compspec_subst_* suite is omitted.
//
// Bridge modules (ceer_benign, ceer_group, higman, ...) import verus_group_theory
// (the clean export from ../tactus-group-theory; see check.sh).
#[cfg(verus_keep_ghost)] pub mod machine;
#[cfg(verus_keep_ghost)] pub mod computation;
#[cfg(verus_keep_ghost)] pub mod pairing;
#[cfg(verus_keep_ghost)] pub mod formula;
#[cfg(verus_keep_ghost)] pub mod proof_system;
#[cfg(verus_keep_ghost)] pub mod proof_encoding;
#[cfg(verus_keep_ghost)] pub mod zfc;
#[cfg(verus_keep_ghost)] pub mod ceer;
#[cfg(verus_keep_ghost)] pub mod computable;
#[cfg(verus_keep_ghost)] pub mod conditional_halt;
#[cfg(verus_keep_ghost)] pub mod multi_output_primitives;
#[cfg(verus_keep_ghost)] pub mod multi_output_machine;
#[cfg(verus_keep_ghost)] pub mod machine_axioms;
#[cfg(verus_keep_ghost)] pub mod church_turing;
#[cfg(verus_keep_ghost)] pub mod enumerator_computable;
#[cfg(verus_keep_ghost)] pub mod compspec_decode;
#[cfg(verus_keep_ghost)] pub mod zfc_enumerator;
#[cfg(verus_keep_ghost)] pub mod zfc_ceer;
#[cfg(verus_keep_ghost)] pub mod ceer_group;
#[cfg(verus_keep_ghost)] pub mod ceer_group_backward;
#[cfg(verus_keep_ghost)] pub mod ceer_benign;
#[cfg(verus_keep_ghost)] pub mod higman;

// Layer 0.5 wiring: instantiate verus_group_theory::cohen_layer05's abstract Miller embedding
// C0 -> C with the concrete CEER declared-relator family (decls_fam). See ceer_layer05.rs.
#[cfg(verus_keep_ghost)] pub mod ceer_layer05;

// Layer 0.5 step (ii): the native ceer_group_equiv <=> equiv_in_c0_limit derivation-translation
// bridge. See ceer_layer05_bridge.rs.
#[cfg(verus_keep_ghost)] pub mod ceer_layer05_bridge;

// GAP-2 brick G2-A: a Turing-machine formalism in Minsky pair-arithmetic form (the source the
// TM->modular simulation consumes). See tm.rs / docs/gap2-register-modular-plan.md.
#[cfg(verus_keep_ghost)] pub mod tm;

// GAP-2 brick G2-B: the TM->modular construction (Aanderaa-Cohen Thm 2, 2 quads per quintuple) +
// determinism well-formedness. See tm_modular.rs.
#[cfg(verus_keep_ghost)] pub mod tm_modular;

// GAP-2 brick G2-D (forward): the H0 correspondence -- a TM run reaching the origin config lands
// the modular machine in H0, by chaining lemma_step_preserves_h0 along the run. See tm_h0.rs.
#[cfg(verus_keep_ghost)] pub mod tm_h0;

// GAP-2 brick G2-D (backward): mm_in_H0 => the TM reaches the origin. Needs the tape digit-invariant
// + terminal correspondence; backward induction on the modular step count. See tm_h0_bwd.rs.
#[cfg(verus_keep_ghost)] pub mod tm_h0_bwd;

// GAP-2-E brick B0: tm_run composition lemmas (split/terminal-identity/halts-at bridges) — the
// run-algebra foundation for the register->TM simulation gadgets. See tm_run_lemmas.rs /
// docs/gap2-register-to-tm-plan.md.
#[cfg(verus_keep_ghost)] pub mod tm_run_lemmas;

// GAP-2-E brick B1: the unary-separator two-counter tape layout (repunit_m blocks + wf). The config
// representation the simulation gadgets edit. See tm_two_counter.rs.
#[cfg(verus_keep_ghost)] pub mod tm_two_counter;

// GAP-2-E gadget infra: deterministic step selection (lemma_tm_step_picks) + the bounded
// zero-test/peek gadget (B2). See tm_gadget.rs.
#[cfg(verus_keep_ghost)] pub mod tm_gadget;

// GAP-2-E brick B3 (part 1): the walk-left ones-loop (pile_ones + lemma_walk_left_inner), the heart
// of the inc/dec walk gadgets. See tm_walk.rs.
#[cfg(verus_keep_ghost)] pub mod tm_walk;

// GAP-2-E brick B3 (assembly): the inc gadget (lemma_inc) -- sep-peel + walk-left + turnaround +
// walk-back, two_counter_config(c1,c2) -> (c1+1,c2) in 2(c1+1) steps. See tm_inc.rs.
#[cfg(verus_keep_ghost)] pub mod tm_inc;

// GAP-2-E brick B4: the dec gadget (lemma_dec) -- walk-left to blank + erase + discard + walk-back,
// two_counter_config(c1,c2) -> (c1-1,c2) in 2(c1+1) steps (c1>=1). See tm_dec.rs.
#[cfg(verus_keep_ghost)] pub mod tm_dec;

// GAP-2-E brick B5.0: the exit-routing "bounce" gadget (lemma_bounce_left/right) -- a 2-step
// trampoline converting a gadget's exit state to the next instruction's entry state, counters
// unchanged, keeping each instruction block's quintuples in one state-window. See tm_bounce.rs.
#[cfg(verus_keep_ghost)] pub mod tm_bounce;

// GAP-2-E brick B5.1: the right-counter walk loops (lemma_walk_right_inner / walk_back_left_inner) --
// u<->v, L<->R mirrors of tm_walk.rs, for the right counter c2 (in v). See tm_walk_right.rs.
#[cfg(verus_keep_ghost)] pub mod tm_walk_right;

// GAP-2-E brick B5.2: the right-counter gadgets (lemma_peek_right / inc_right / dec_right) -- u<->v,
// L<->R mirrors of the peek/inc/dec gadgets, operating on c2 (in v). See tm_right_gadgets.rs.
#[cfg(verus_keep_ghost)] pub mod tm_right_gadgets;

// GAP-2-E brick B5.3: the rm_to_tm assembly (uniform 48-quint windows per program position +
// cleanup) and tm_wf (quint_wf + determinism via index-recovery arithmetic). See tm_assemble.rs.
#[cfg(verus_keep_ghost)] pub mod tm_assemble;

// GAP-2-E brick B5.4/B5.5: per-instruction one-step simulation (tm_reaches + lemma_quint_at +
// per-instruction sim lemmas + the unified one-step lemma_sim_step). See tm_sim.rs.
#[cfg(verus_keep_ghost)] pub mod tm_sim;

// GAP-2-E brick B6 (part 1): the cleanup phase + Halt routing reach the origin (lemma_cleanup +
// phase A/B/C + lemma_sim_halt), reusing the parametric peek/dec/bounce gadgets. See tm_cleanup.rs.
#[cfg(verus_keep_ghost)] pub mod tm_cleanup;

// GAP-2-E brick B6 (part 2): the full run simulation + the halting iff. Chains lemma_sim_step along
// the 2-counter run + cleanup (forward) and inducts on TM fuel with positive-fuel sim (backward) to
// prove rm-halts ⟺ rm_to_tm reaches the origin (lemma_rm_tm_origin_iff). See tm_run_sim.rs.
#[cfg(verus_keep_ghost)] pub mod tm_run_sim;

// GAP-2 / L1 number-theory core: gcd + Bézout + the coprimality lemmas (multiplicative, powers,
// non-divisibility) consumed by the Gödel k→2 encoding. Pairwise-coprime base ⇒ the DecJump
// zero-test divisibility iff, dodging primality. See number_theory.rs.
#[cfg(verus_keep_ghost)] pub mod number_theory;

// GAP-2 / L1 Gödel encoding: the Sylvester pairwise-coprime base sequence + godel(regs) +
// the divisibility iff `base(i) | godel(regs) ⟺ regs[i] ≥ 1` (the 2-counter DecJump zero-test
// arithmetic). See godel.rs.
#[cfg(verus_keep_ghost)] pub mod godel;

// GAP-2 / L0 brick B-L0.1: fuel-instrumented bounded simulation. `instrument` guards each original
// instruction with a `DecJump{fuel, TIMEOUT}` so a run always returns within `fuel` steps with a
// HALTED-or-TIMEOUT verdict (a non-halting enumerator stage cannot wedge the dovetail). The bounded
// analogue of multi_output_primitives::lemma_embed_reaches_target. See
// docs/gap2-l0-search-rm-plan.md and search_rm_sim.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_sim;

// GAP-2 / L0 brick B-L0.2a: register-machine arithmetic for the dovetail driver — `double_dist_instrs`
// (drain one register into two), the primitive for the forward-`pair` comparison. See search_rm_arith.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_arith;

// GAP-2 / L0 brick B-L0.2b: the nat-equality comparison gadget `eq_test_instrs` (destructive compare,
// EQUAL exit iff (a)==(b)) — tests `pair(reg1,reg2) == input` in the HALTED comparison. See search_rm_compare.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_compare;

// GAP-2 interface skeleton: the register->modular machine reduction (Aanderaa-Cohen Thm 2),
// supplying the `mm` whose H0 realizes the CEER declared pairs. Type-level plumbing + the
// reduction target; the simulation-correctness proofs are the deferred GAP-2 impl. See
// modular_reduction.rs.
#[cfg(verus_keep_ghost)] pub mod modular_reduction;

// GAP-1 item-3b brick B2: the conditional relator-set match — connects the Miller direct-limit
// p_infty(ceer_decls_fam(e)) to Cohen's c_pred(mm,2,m,is_S_canonical) via the block-shift relabeling,
// using B1 (decode bridge) + B3 (relabel-iso). Conditional on the GAP-2 ceer_realizes hypothesis.
// See ceer_relator_match.rs.
#[cfg(verus_keep_ghost)] pub mod ceer_relator_match;

// GAP-1 item-3b assembly: chains B2 (relator match) onto item-3a (lemma_ceer_limit_commutation),
// the L0.5 bridge, and GAP-3 (faithful+sound) into the conditional axiom-removal chain
// ceer_group_equiv ⟺ equiv(h3_pres,...). Conditional on the GAP-2 ceer_realizes hypothesis.
// See ceer_fp_conditional.rs.
#[cfg(verus_keep_ghost)] pub mod ceer_fp_conditional;
