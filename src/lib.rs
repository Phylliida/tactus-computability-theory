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

// GAP-2 / L1 k→2 reduction gadgets (M1 move, M2 multiply/divide/div-test): register-machine loops
// over {Inc, DecJump, Jump} with NO free scratch — every back-edge is a `Jump` (R-ii). The 2-counter
// analogues of multi_output_primitives' copy/dist loops. See docs/gap2-register-to-tm-plan.md.
#[cfg(verus_keep_ghost)] pub mod godel_gadgets;

// GAP-2 / L1 k→2 reduction gadgets (M2 divide / non-destructive divisibility-test): the divide
// back-loop `÷k` (divisible branch) + the non-destructive `Div?((n),k)[E1]` test (rebuild-into-dst,
// verdict in the exit pc). Consumes godel.rs's value lemmas at M3. See docs/gap2-register-to-tm-plan.md.
#[cfg(verus_keep_ghost)] pub mod godel_gadgets2;

// GAP-2 / L1 k→2 reduction M3 block compositions: move + back-loop = the three RM(2) ops
// (multiply C1·=base(i) / divide C1/=base(i) / non-destructive divtest k|C1) at the value level.
// Parametric in k + block addresses; M5 plugs in the Gödel invariant. See godel_blocks.rs.
#[cfg(verus_keep_ghost)] pub mod godel_blocks;

// GAP-2 / L1 k→2 reduction M5 per-instruction sims: the M3 blocks wrapped with godel.rs value lemmas
// so each RM(2) block simulates one RM(k) instruction on the Gödel-encoded state (Inc=multiply,
// DecJump=Div?+divide/jump, Jump=jump). Parametric in addresses. See godel_sim.rs.
#[cfg(verus_keep_ghost)] pub mod godel_sim;

// GAP-2 / L1 k→2 reduction M4: assemble `rm_k_to_rm2` — lay the per-instruction RM(2) blocks
// (godel_blocks/godel_sim) end-to-end via a non-uniform prefix-sum address map (`block_start`), remap
// jump targets through it, and prove the layout-match (`lemma_block_at`) + `machine_wf`. See godel_assemble.rs.
#[cfg(verus_keep_ghost)] pub mod godel_assemble;

// GAP-2 / L1 k→2 reduction M5-dispatch: the one-step simulation. Dispatches on the RM(k) instruction
// at the current pc, picks the matching M5 per-instruction sim, and shows the assembled RM(2) machine
// runs from rm2_config_enc(c) to rm2_config_enc(step(c)). See godel_dispatch.rs.
#[cfg(verus_keep_ghost)] pub mod godel_dispatch;

// GAP-2 / L1 k→2 reduction M6: the run simulation + halting equivalence. Chains lemma_sim_step along
// a run (forward) and inducts on RM(2) fuel (backward, using g>=1 gadget progress) to prove
// RM(k) halts <==> rm_k_to_rm2(RM(k)) halts on the godel-encoded config. See godel_run.rs.
#[cfg(verus_keep_ghost)] pub mod godel_run;

// GAP-2 machine-content core: compose the three halting equivalences (godel_halts_iff +
// rm_tm_origin_iff + tm_h0_iff) into RM(k) halts <==> mm_in_H0 of the assembled modular machine.
// The self-contained brick G2-F consumes. See godel_modular.rs.
#[cfg(verus_keep_ghost)] pub mod godel_modular;

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

// GAP-2 / L0 brick B-L0.2c (pre): contiguous register-bank clear `clear_bank_instrs` — resets the
// embedded enumerator's `ne`-register bank between dovetail iterations (the `instrument` run leaves it
// dirty). Symbolic-length unrolled clear block, proven by induction on count. See search_rm_clearbank.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_clearbank;

// GAP-2 / L0 brick B-L0.2c (pre): combined instrument outcome `lemma_instrument_outcome` — merges the
// ⟸ (instrument_halts) and ⟹ (reaches_sink) instrument lemmas into ONE existential step-count, so the
// dovetail's inner body sees a single halt/timeout outcome (no witness mismatch). See search_rm_outcome.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_outcome;

// GAP-2 / L0 brick B-L0.2c: the dovetailing search machine `search_rm(e)` — one RegisterMachine whose
// halting on `pair(a,b)` is `declared_equiv(e,a,b)`. Definition + offsets + machine_wf. See search_rm.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm;

// GAP-2 / L0 brick B-L0.2c: the dovetail inner body (one (T,s) iteration) as chained phase lemmas.
// See search_rm_inner.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_inner;

// GAP-2 / L0 brick B-L0.2c/B-L0.3: assemble lemma_inner_body, the bounded inner loop, the outer
// round, and the halts-iff. See search_rm_outer.rs.
#[cfg(verus_keep_ghost)] pub mod search_rm_outer;

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

// GAP-2 G2-F brick B-FR: the ignition/frame lemmas. Appending "ignition" quads (residue (i,0),
// i!=0) to a base modular machine does not disturb H0-reachability on the running region
// (beta%m != 0), so the (alpha,0)->running input transition can be spliced onto the existing
// tm_to_modmachine H0 reduction. See gap2_ignition.rs / docs/gap2-input-loader-plan.md.
#[cfg(verus_keep_ghost)] pub mod gap2_ignition;

// GAP-2 G2-F brick B-relnum (spec) + B-W bridge §4.4: the family-relator <-> declared-pair
// correspondence. Proves the set-equality { r : r != eps && dbar_union_pred(ceer_decls_fam(e),r) }
// = { fam_relator(a,b) : declared_pair(e,s)=Some((a,b)) }, the spec backbone the generate-and-compare
// relator-decider targets. Machine-architecture-independent. See gap2_relnum.rs.
#[cfg(verus_keep_ghost)] pub mod gap2_relnum;

// GAP-2 G2-F Route (i) brick R-AL: the n=4 uniform-window TM assembler -- the substrate for
// psc_tm(e). A tm_wf TM over alphabet 0..4 (so word-number digits 1..4 fit as tape symbols), built
// from a pluggable per-position action table; the alphabet-widened analog of tm_assemble.rs. The
// counter gadget step-lemmas (all tm.n>=2-monotone) fire verbatim on it. See tm_assemble4.rs.
#[cfg(verus_keep_ghost)] pub mod tm_assemble4;

// psc_tm(e) at n=5: the alphabet-widened (marker `5`) bump of tm_assemble4. STRIDE=48 windows
// (entry5(pc)=6+48pc, 288 quints/window) so each emitter block / master-mgmt gadget gets its own
// window with headroom; the n>=5-monotone power-block step fires verbatim. See tm_assemble5.rs.
#[cfg(verus_keep_ghost)] pub mod tm_assemble5;

// GAP-2 G2-F Route (i) brick R-P (foundation): the base-m digit-string algebra. alpha's digits 1..4
// as a Seq<nat> packed low-first by dpack; pop/push/digits_le/append lemmas -- the symbol-agnostic
// analog of repunit_m, the foundation the copy-and-park (R-P) + ping-pong compare (R-cmp) digit-walk
// loops read. See tm_dstring.rs.
#[cfg(verus_keep_ghost)] pub mod tm_dstring;

// GAP-2 G2-F Route (i) brick R-P: the digit-walk-left gadget. The symbol-agnostic analog of
// tm_walk::lemma_walk_left_inner -- one loop quintuple (q_walk,s,s,q_walk,L) per digit symbol s in
// 1..4 walks the head over a dpack block of nonzero digits onto v, landing on the blank turnaround.
// The engine of the copy-and-park relocation of alpha. See tm_dwalk.rs.
#[cfg(verus_keep_ghost)] pub mod tm_dwalk;

// GAP-2 G2-F Route (i) brick R-P: the copy-and-park core. lemma_rp_entry (2-step handshake depositing
// the ignition-held low digit d0 onto v) + lemma_rp_copy_park (entry o dwalk_left) park alpha's digit
// sequence reversed in v, freeing u as workspace -- the canonical layout R-cmp reads. See tm_rp.rs.
#[cfg(verus_keep_ghost)] pub mod tm_rp;

// GAP-2 G2-F Route (i) brick R-P (assembly): the copy-and-park psc_act window dispatch over the
// assemble4 scaffold. rp_act places the start/deposit/walk quintuples in windows 0..=4; lemma_rp_phase
// splices lemma_rp_copy_park onto any psc_tm whose first five windows carry them. Pins the ignition
// handoff state start(d0) = entry4(d0). See gap2_psc_rp.rs / docs/gap2-input-loader-plan.md §5 (R-P).
#[cfg(verus_keep_ghost)] pub mod gap2_psc_rp;

// GAP-2 G2-F Route (i) brick R-relnum-gen (spec foundation): relnum as a dpack digit block. The
// decode_word <-> dpack bridge (lemma_decode_word_is_dpack) pins the digit ORDER (decode_word's last
// symbol = dpack's lowest digit), and lemma_relnum_is_dpack gives relnum = dpack(decode_digit_seq(...)) --
// the emitter's spec target and the compare's invariant. See gap2_relnum_digits.rs.
#[cfg(verus_keep_ghost)] pub mod gap2_relnum_digits;

// GAP-2 G2-F Route (i) brick R-relnum-gen (spec): rho drops out of the digit analysis. The block-shift
// relabel rho = relabel_hom(...,cb) is invisible to decode_word because letter_digit(cb,2,.) un-shifts it
// (lemma_decode_rho_unshift); lemma_relnum_no_rho gives relnum = decode_word(0,2,m,fam_relator(a,b)).
// See gap2_rho_unshift.rs.
#[cfg(verus_keep_ghost)] pub mod gap2_rho_unshift;

// GAP-2 G2-F Route (i) brick R-relnum-gen: the digit-sequence structural library (Production-proof side).
// How decode_digit_seq distributes over ++ (REVERSAL: dds(w1++w2)=dds(w2)++dds(w1)), word_power
// (=seq_pow(dds(w),k)), symbol_power, and singletons -- so fam_relator decomposes into explicit emitter
// digit blocks. See gap2_relnum_dds.rs / docs/gap2-input-loader-plan.md §5.
#[cfg(verus_keep_ghost)] pub mod gap2_relnum_dds;

// GAP-2 G2-F Route (i) brick R-relnum-gen: inverse_word over the block constructors. The two distribution
// laws inverse_word(symbol_power(s,k))=symbol_power(s⁻¹,k) and inverse_word(word_power(w,k))=
// word_power(inverse_word(w),k) -- so inverse_word(u_b) rewrites into the same primitive shapes as u_a.
// See gap2_inverse.rs / docs/gap2-input-loader-plan.md §5.
#[cfg(verus_keep_ghost)] pub mod gap2_inverse;

// GAP-2 G2-F Route (i) brick R-relnum-gen: the fam_relator decomposition. fam_relator(a,b) = u_a ++
// inverse_word(u_b) (apply_embedding bridge); the 3-letter b/b⁻¹ inverses; inverse_word(u_b) as 8
// explicit primitive pieces. See gap2_fam_split.rs / docs/gap2-input-loader-plan.md §5.
#[cfg(verus_keep_ghost)] pub mod gap2_fam_split;

// GAP-2 G2-F Route (i) brick R-relnum-gen: the explicit decode_digit_seq(fam_relator) pattern (the
// emitter's target). dds(0,2,fam_relator(a,b)) == fam_digits(a,b) = uinv_digits(b) ++ u_digits(a), an
// explicit seq_pow/singleton block concatenation. See gap2_fam_digits.rs.
#[cfg(verus_keep_ghost)] pub mod gap2_fam_digits;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, foundation): the symbol-power emit loop. The loop
// quintuple (q_emit,1,s,q_emit,L) consumes a repunit(i) counter in u and piles i copies of digit s onto
// v -- the symbol-agnostic twin of tm_walk::lemma_walk_left_inner, producing the seq_pow([s],i) blocks of
// fam_digits one iteration at a time. lemma_pile_sym_is_dpile bridges the accumulator to the digit-seq
// algebra. See tm_emit.rs / docs/gap2-input-loader-plan.md §5 (R-relnum-gen STEP 2).
#[cfg(verus_keep_ghost)] pub mod tm_emit;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B home/shuttle): the frontier block-emit. The
// "sequential write" step -- a state cycle (e_k,0,blk[k],e_{k+1},R) writes blk's digits onto u over the
// frontier blanks (v==0), appending dpile(c.u,blk). lemma_emit_one_frontier + block1/block3 compositions
// (the only fam_digits block sizes). See tm_shuttle.rs / docs/gap2-input-loader-plan.md §5 (STEP 2 model B).
#[cfg(verus_keep_ghost)] pub mod tm_shuttle;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): the master-decrement foundation.
// lemma_walk_left_prefix -- the generalized walk-left over a repunit PREFIX with a high tail w (the
// i_b/i_a separator + i_a), the dec_master analog of lemma_walk_left_inner that LEAVES w intact (lands
// u==w/m, a==w%m) instead of assuming a bare counter (u==0). Foundation for dec_master + home_config.
// See tm_dec_master.rs / docs/gap2-input-loader-plan.md §5 (STEP 2 model B).
#[cfg(verus_keep_ghost)] pub mod tm_dec_master;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): the prefix digit-walk-left + reverse algebra.
// lemma_dwalk_left_prefix -- the digit analog of lemma_walk_left_prefix: walk left over a block of digit
// symbols 1..4 leaving a high tail w (the masters) intact. Plus the drev (low-first digit reverse) bridges
// (dpile(0,s)==dpack(drev(s)), drev involution) the per-block return walk uses to cancel the surge's
// reversal. See tm_dwalk_prefix.rs / docs/gap2-input-loader-plan.md §5 (STEP 2 model B).
#[cfg(verus_keep_ghost)] pub mod tm_dwalk_prefix;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): the per-block iteration. Assembles ONE
// emitter iteration from the verified halves -- surge (move-R + dwalk_right to frontier) + emit + return
// (move-L + dwalk_left_prefix home) + dec_temp -- into lemma_block_iter_block1/_block3: home->home,
// output ++= blk, temp -> temp-1. See tm_block_iter.rs / docs/gap2-input-loader-plan.md §5 (STEP 2 model B).
#[cfg(verus_keep_ghost)] pub mod tm_block_iter;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): the per-block LOOP. Wraps the iteration body
// in a TM loop with a 2-step non-destructive guard (peek the counter at home, branch continue/exit).
// lemma_block_loop_block1: (s)^temp emitted onto the output, counter consumed, master shifted m^temp.
// See tm_block_loop.rs / docs/gap2-input-loader-plan.md §5 (STEP 2 model B).
#[cfg(verus_keep_ghost)] pub mod tm_block_loop;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): copy-refresh foundation. The blank-gap "seek"
// walks (left to the master, right back to the pivot) that bracket the marked unary copy rebuilding a fresh
// temp counter from the preserved master. See tm_copy_refresh.rs / docs/gap2-input-loader-plan.md §5.
#[cfg(verus_keep_ghost)] pub mod tm_copy_refresh;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): the per-power-block PERIODIC step. Composes
// lemma_copy_refresh ∘ lemma_block_loop into one run emitting (blk)^M, master stationary (gap g=M+2 fixed).
// See tm_power_block.rs / docs/gap2-input-loader-plan.md §5, §N+10.
#[cfg(verus_keep_ghost)] pub mod tm_power_block;

// GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B): the M=1 (exp=0) dispatch of the per-power-block
// step, using lemma_copy_refresh_m1. See tm_power_block_m1.rs / docs/gap2-input-loader-plan.md §5, §N+10.
#[cfg(verus_keep_ghost)] pub mod tm_power_block_m1;

// GAP-2 G2-F Route (i): emitter WINDOWS over the assemble5 scaffold. Each fam_digits block becomes one
// STRIDE=48 window; a phase lemma (analog of gap2_psc_rp::lemma_rp_phase) proves the block's step about
// the concrete machine. Starts with the singleton-emit window. See gap2_emit_window.rs / §N+11.
#[cfg(verus_keep_ghost)] pub mod gap2_emit_window;

// GAP-2 G2-F Route (i): the POWER-BLOCK window (block1, (s)^M) over assemble5 -- the fattest emitter
// window (32 states/64 quints, full copy_refresh+block_loop). See gap2_emit_power.rs / §N+11.
#[cfg(verus_keep_ghost)] pub mod gap2_emit_power;

// GAP-2 G2-F Route (i): the TRIPLE power-block window (block3, (s0,s1,s2)^M) over assemble5 -- 34 states,
// the triple-emit block_loop. The (4,1,2)^i / (4,3,2)^i power-blocks. See gap2_emit_power3.rs / §N+11.
#[cfg(verus_keep_ghost)] pub mod gap2_emit_power3;

// GAP-2 G2-F Route (i): the EMITTER SEQUENCER -- chains per-block phase lemmas (state-id splice, no glue)
// into the full fam_digits emission. See gap2_emit_seq.rs / §N+12.
#[cfg(verus_keep_ghost)] pub mod gap2_emit_seq;
#[cfg(verus_keep_ghost)] pub mod gap2_master_mgmt;
#[cfg(verus_keep_ghost)] pub mod gap2_tail_lift;
#[cfg(verus_keep_ghost)] pub mod gap2_tail_walks;
#[cfg(verus_keep_ghost)] pub mod gap2_tail_phases;
#[cfg(verus_keep_ghost)] pub mod gap2_tail_phase1;
// The M=1 path of copy_refresh tail-safety (mark_terminate_m1 / unmark_m1 / copy_refresh_m1).
#[cfg(verus_keep_ghost)] pub mod gap2_tail_phase1_m1;
#[cfg(verus_keep_ghost)] pub mod gap2_tail_emit;
// Upper half of the emit-loop tail-lift: the per-power-block PERIODIC step (copy_refresh ∘ block_loop)
// is tail_safe at the home offset H_0 = g+M+1. See gap2_tail_power.rs / §N+14.
#[cfg(verus_keep_ghost)] pub mod gap2_tail_power;
