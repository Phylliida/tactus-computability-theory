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

// GAP-2 interface skeleton: the register->modular machine reduction (Aanderaa-Cohen Thm 2),
// supplying the `mm` whose H0 realizes the CEER declared pairs. Type-level plumbing + the
// reduction target; the simulation-correctness proofs are the deferred GAP-2 impl. See
// modular_reduction.rs.
#[cfg(verus_keep_ghost)] pub mod modular_reduction;
