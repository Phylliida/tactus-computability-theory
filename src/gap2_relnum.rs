//! # GAP-2 G2-F brick B-relnum (spec target) + B-W bridge §4.4 — the family-relator ↔ declared-pair
//! correspondence.
//!
//! `docs/gap2-input-loader-plan.md` §2.2 (S), §4.4. Co-designed with Danielle (port 8051), 2026-06-26.
//!
//! ## Why this brick exists
//! The relator-decider machine `psc_tm(e)` accepts (halts to the origin on) an input word-number `α`
//! iff `α ∈ { relnum(a,b) : (a,b) a declared pair of the CEER }`, where `relnum(a,b)` is the c-block
//! word-number of the collapsed family relator `ρ(collapse(g_a g_b⁻¹))` — the *generate-and-compare*
//! design. To discharge [`ceer_realizes`](crate::ceer_relator_match::ceer_realizes), whose two `forall`
//! clauses quantify over the Miller collapsed-relator family `dbar_union_pred(ceer_decls_fam(e), r)`,
//! we need the SET-EQUALITY bridging the two views:
//!
//! ```text
//!   { r : r ≠ ε ∧ dbar_union_pred(ceer_decls_fam(e), r) }  =  { fam_relator(a,b) : declared_pair(e,s)=Some((a,b)) }
//! ```
//!
//! This module proves both inclusions ([`lemma_fam_relator_from_dbar`] forward,
//! [`lemma_dbar_from_declared`] backward) at the *spec/group-theory* level — independent of how the
//! machine is eventually built (TM read-loop or modular-machine prefix). With the machine's halting
//! semantics in hand, B-W composes these with `relnum := decode_word ∘ ρ ∘ fam_relator` to discharge
//! both directions of `ceer_realizes`. The `r ≠ ε` bookkeeping in `ceer_realizes`'s BWD clause is then
//! free: `α ≠ 0` forces `r ≠ ε` because `decode_word(cb,2,m, ρ(ε)) = decode_word(cb,2,m,ε) = 0`.
//!
//! Fully constructive — no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::symbol::{Symbol, symbol_valid, generator_index};
use verus_group_theory::word::{Word, empty_word, word_valid};
use verus_group_theory::benign::apply_embedding;
use verus_group_theory::miller_collapse::miller_collapse_emb;
use verus_group_theory::miller_collapse_preserve::dbar;
use verus_group_theory::miller_collapse_limit::{dbar_union_pred, lemma_emb_slice_independent,
    lemma_seq_index_contains};
use verus_group_theory::word_numbering_decode::decode_word;
use verus_group_theory::machine_group::ModMachine;
use crate::ceer::{CEER, declared_pair};
use crate::ceer_group::ceer_relator;
use crate::ceer_layer05::{ceer_to_word, ceer_decls_fam, ceer_decls_fam_at, ceer_relator_at};
use crate::ceer_relator_match::{cb_of, rho};

verus! {

// ============================================================================
// The canonical collapsed family relator + the relnum spec target
// ============================================================================

/// The minimal generator-slice over which `ceer_relator(a,b) = [Gen(a), Inv(b)]` is a valid word:
/// `max(a,b) + 1`.
pub open spec fn rel_slice(a: nat, b: nat) -> nat {
    (if a >= b { a } else { b }) + 1
}

/// The canonical collapsed family relator for a declared pair `(a,b)`: the Miller-collapse image of
/// `[Gen(a), Inv(b)]` taken at the minimal valid slice `rel_slice(a,b)`. Slice-independent
/// (`lemma_emb_slice_independent`), so this canonical representative equals the `dbar`-slice value at
/// every larger slice — the content of [`lemma_dbar_slice_is_fam_relator`].
pub open spec fn fam_relator(a: nat, b: nat) -> Word {
    apply_embedding(miller_collapse_emb(rel_slice(a, b), 0, 1), ceer_to_word(ceer_relator(a, b)))
}

/// **B-relnum spec target.** The word-number the relator-decider machine compares `α` against for a
/// declared pair `(a,b)`: the c-block word-number of `ρ(collapsed family relator)`. The
/// generate-and-compare search computes this per stage; the bridge lemmas below show the
/// family-relator decode-image set equals `{ relnum(a,b) : (a,b) a declared pair }`.
pub open spec fn relnum(e: CEER, mm: ModMachine, m: nat, a: nat, b: nat) -> nat {
    decode_word(cb_of(mm), 2, m, rho(e, mm, m, fam_relator(a, b)))
}

/// `relnum` is exactly the `decode_word(cb,2,m, ρ(fam_relator(a,b)))` form `ceer_realizes` reads
/// (definitional; stated for the B-W consumer).
pub proof fn lemma_relnum_is_decode(e: CEER, mm: ModMachine, m: nat, a: nat, b: nat)
    ensures
        decode_word(cb_of(mm), 2, m, rho(e, mm, m, fam_relator(a, b))) == relnum(e, mm, m, a, b),
{
}

// ============================================================================
// Validity helper
// ============================================================================

/// `ceer_to_word(ceer_relator(a,b)) = [Gen(a), Inv(b)]` is a valid word over any slice past both
/// indices.
pub proof fn lemma_ceer_relator_word_valid(a: nat, b: nat, n: nat)
    requires
        a < n,
        b < n,
    ensures
        word_valid(ceer_to_word(ceer_relator(a, b)), n),
{
    let w = ceer_to_word(ceer_relator(a, b));
    let rel = ceer_relator(a, b);
    assert(rel.len() == 2);
    assert(w.len() == 2);
    assert(w[0] == Symbol::Gen(a));
    assert(w[1] == Symbol::Inv(b));
    assert forall|i: int| 0 <= i < w.len() implies symbol_valid(#[trigger] w[i], n) by {
        if i == 0 {
            assert(generator_index(w[0]) == a);
        } else {
            assert(i == 1);
            assert(generator_index(w[1]) == b);
        }
    }
}

// ============================================================================
// The slice value of a declared pair IS the canonical fam_relator
// ============================================================================

/// At any slice `big_m` past both indices of a declared pair, the `dbar`-slice entry for stage `s`
/// is exactly the canonical `fam_relator(a,b)` (slice-independence of the collapse).
pub proof fn lemma_dbar_slice_is_fam_relator(e: CEER, s: nat, a: nat, b: nat, big_m: nat)
    requires
        declared_pair(e, s) == Some((a, b)),
        a < big_m,
        b < big_m,
        s < big_m,
    ensures
        dbar(big_m, ceer_decls_fam_at(e, big_m))[s as int] == fam_relator(a, b),
{
    let w = ceer_to_word(ceer_relator(a, b));
    let emb_big = miller_collapse_emb(big_m, 0, 1);
    // ceer_relator_at(e,s,big_m) = w (declared_pair Some((a,b)), a,b < big_m → the fitting branch).
    assert(ceer_relator_at(e, s, big_m) == w);
    // ceer_decls_fam_at(e,big_m) = Seq::new(big_m, |s| ceer_relator_at(e,s,big_m)); index at s.
    assert(ceer_decls_fam_at(e, big_m)[s as int] == ceer_relator_at(e, s, big_m));
    // dbar(big_m, decls)[s] = apply_embedding(emb_big, decls[s]) = apply_embedding(emb_big, w).
    assert(dbar(big_m, ceer_decls_fam_at(e, big_m))[s as int] == apply_embedding(emb_big, w));
    // slice independence: emb_big on w == emb(rel_slice(a,b)) on w == fam_relator(a,b).
    lemma_ceer_relator_word_valid(a, b, rel_slice(a, b));   // word_valid(w, rel_slice(a,b))
    assert(rel_slice(a, b) <= big_m);
    lemma_emb_slice_independent(rel_slice(a, b), big_m, w);
}

// ============================================================================
// The two inclusions of the set-equality
// ============================================================================

/// **FORWARD.** A nonempty collapsed family relator `r` of the CEER family comes from a declared pair:
/// some stage `s` has `declared_pair(e,s) = Some((a,b))` with `r = fam_relator(a,b)`. (The hook the
/// machine reads: it enumerates stages `s`, computes `declared_pair(e,s)`, and accepts the matching
/// `relnum`.)
pub proof fn lemma_fam_relator_from_dbar(e: CEER, r: Word)
    requires
        dbar_union_pred(ceer_decls_fam(e), r),
        r != empty_word(),
    ensures
        exists|s: nat, a: nat, b: nat|
            #![trigger declared_pair(e, s), fam_relator(a, b)]
            declared_pair(e, s) == Some((a, b)) && r == fam_relator(a, b),
{
    let fam = ceer_decls_fam(e);
    let big_m = choose|big_m: nat| (#[trigger] dbar(big_m, fam(big_m))).contains(r);
    assert(dbar(big_m, fam(big_m)).contains(r));
    assert(fam(big_m) == ceer_decls_fam_at(e, big_m));
    let d = dbar(big_m, ceer_decls_fam_at(e, big_m));
    assert(d.len() == big_m);
    let si = choose|si: int| 0 <= si < d.len() && d[si] == r;
    assert(0 <= si < big_m && d[si] == r);
    let s = si as nat;
    let emb_big = miller_collapse_emb(big_m, 0, 1);
    // d[si] = apply_embedding(emb_big, ceer_relator_at(e, s, big_m)) = r ≠ ε.
    assert(ceer_decls_fam_at(e, big_m)[si] == ceer_relator_at(e, s, big_m));
    assert(d[si] == apply_embedding(emb_big, ceer_relator_at(e, s, big_m)));
    // r ≠ ε ⟹ the raw relator is nonempty (apply_embedding maps ε to ε).
    assert(ceer_relator_at(e, s, big_m) != empty_word()) by {
        if ceer_relator_at(e, s, big_m) == empty_word() {
            assert(empty_word().len() == 0);
            assert(apply_embedding(emb_big, empty_word()) == empty_word());
            assert(d[si] == empty_word());
            assert(false);
        }
    }
    // A nonempty raw relator forces declared_pair Some with both indices < big_m.
    match declared_pair(e, s) {
        Some(pair) => {
            assert(pair.0 < big_m && pair.1 < big_m) by {
                if !(pair.0 < big_m && pair.1 < big_m) {
                    assert(ceer_relator_at(e, s, big_m) == empty_word());
                }
            }
            let a = pair.0;
            let b = pair.1;
            assert(pair == (a, b));
            assert(declared_pair(e, s) == Some((a, b)));
            lemma_dbar_slice_is_fam_relator(e, s, a, b, big_m);
            assert(d[si] == fam_relator(a, b));
            assert(r == fam_relator(a, b));
            assert(declared_pair(e, s) == Some((a, b)) && r == fam_relator(a, b));
        },
        None => {
            assert(ceer_relator_at(e, s, big_m) == empty_word());
            assert(false);
        },
    }
}

/// **BACKWARD.** Every declared pair contributes its `fam_relator` to the CEER collapsed-relator
/// family. (Picks a slice past `s`, `a`, `b`; the slice entry is `fam_relator(a,b)` and lands in the
/// `dbar` union.)
pub proof fn lemma_dbar_from_declared(e: CEER, s: nat, a: nat, b: nat)
    requires
        declared_pair(e, s) == Some((a, b)),
    ensures
        dbar_union_pred(ceer_decls_fam(e), fam_relator(a, b)),
{
    let fam = ceer_decls_fam(e);
    // a slice past s, a, b.
    let mx = if s >= a && s >= b { s } else if a >= b { a } else { b };
    let big_m = mx + 1;
    assert(s < big_m && a < big_m && b < big_m);
    lemma_dbar_slice_is_fam_relator(e, s, a, b, big_m);
    assert(fam(big_m) == ceer_decls_fam_at(e, big_m));
    let d = dbar(big_m, ceer_decls_fam_at(e, big_m));
    assert(d.len() == big_m);
    assert(d[s as int] == fam_relator(a, b));
    lemma_seq_index_contains(d, s as int);
    assert(dbar(big_m, fam(big_m)).contains(fam_relator(a, b)));
    assert(dbar_union_pred(fam, fam_relator(a, b))) by {
        assert(dbar(big_m, fam(big_m)).contains(fam_relator(a, b)));
    }
}

} // verus!
