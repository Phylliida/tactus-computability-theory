# Scope: an *explicit* finitely-presented group for ZFC (removing `axiom_ceer_fp_embedding`)

## Goal

Replace the existence axiom with a **constructive** Higman/Aanderaa–Cohen embedding,
so that `theorem_zfc_equiv_in_fp_group` is backed by an **explicit, printable finite
presentation** `H = ⟨ generators | relators ⟩` whose word problem *is* ZFC-provable
equivalence — no `external_body`, no `admit`.

## Why the current axiom exists (and why the naive route can't replace it)

- The CEER group `G = ⟨g₀,g₁,… | g_a g_b⁻¹ for declared (a,b)⟩` has **infinitely many
  generators**. The rope trick (`benign_witness_valid`) needs a **finitely generated**
  group, so `G` must first be faithfully embedded in a f.g. group.
- The naive telescope `gₙ = y⁻ⁿ x yⁿ` into F₂ is **provably wrong** (`docs/two-gen-backward-bug.md`):
  declaring `g₀=g₁` forces `[x,y⁻¹]=1`, F₂ goes abelian (ℤ×ℤ), and *all* `gₙ` collapse.
- The correct route is the **machine-group (Aanderaa–Cohen) encoding**: encode the ZFC
  *enumerator machine* as an HNN tower so relations fire on exactly the declared pairs.
  This is what the (dropped) `machine_group.rs` / `machine_group_faithful.rs` were.

## The construction (already defined, explicit)

`machine_group.rs`: `machine_group_presentation(data) = hnn_presentation(machine_hnn_data(data))`
- **Base:** free group on `num_states + 2` generators (one `q_s` per machine state, plus `α, β`).
- **Stable letters / relators:** one HNN association per machine transition quadruple.
- **Config encoding:** `config_word(s,α,β) = q_s · αᵅ · βᵝ`.
- Finite states ⟹ **finite, explicit presentation.** Fully readable.

The ZFC enumerator machine is already proven correct in this crate (`zfc_enumerator`,
`enumerator_computable`), so `data` is concrete.

## Proof obligations (status today, on the dropped modules)

| # | Obligation | What it says | Status | Difficulty |
|---|---|---|---|---|
| 1 | `lemma_machine_step_gives_equiv` | one machine step ⟹ `config_word` equiv (HNN conjugation) | `admit()` | **moderate** (word manipulation; `lemma_translate_hnn_relator` available) |
| 2 | `lemma_machine_run_gives_equiv` | fuel induction over #1 | `admit()` | **easy** (induction) |
| 3 | `axiom_machine_hnn_isomorphic` | HNN structural iso | `external_body` | **moderate** |
| 4 | `axiom_config_words_free_injective` | config words equal in the **free base** ⟹ same params | **PROVEN** ✓ | (done) |
| 5 | **`axiom_machine_group_backward`** | `config_word(C₁)≡config_word(C₂)` in `G_M` ⟹ a valid **machine trace** C₁→C₂ | `external_body` | **HARD — the crux** |
| 6 | Bridge `G_M ↔ ZFC CEER` | `f(σ)=f(τ)` in `G_M` ⟺ ZFC⊢σ↔τ, via the enumerator | not yet built | **moderate–hard** |

**#5 is the real theorem** (Boone–Novikov / Aanderaa–Cohen faithfulness). The note in
the source already states the proof shape: *"the derivation either stays in the base
(⟹ C₁=C₂ by free injectivity, #4 ✓) or uses stable letters (each = one machine step);
the full argument requires pinch elimination in the HNN tower."*

## The substrate we build on (already proven in tactus, clean)

- **`britton_lemma_full`** (`britton_via_tower.rs`, the 194-verified Britton stack) — the
  exact tool #5 needs. Plus `lemma_hnn_step_tower_equiv`, `lemma_hnn_derivation_to_tower_equiv`,
  `lemma_translate_*`, `lemma_tower_textbook_chain_from_hnn_iso`.
- **`lemma_rope_trick`** — benign subgroup of F₂ ⟹ explicit f.p. group. Proven.
- **`benign`, `hnn`** — clean, no axioms.
- Free-group normal-form machinery (used by #4, already proven).

So this is **not "prove Higman from scratch."** Britton's lemma — the hardest piece — is
done. #5 is *applying* it to this specific HNN tower and extracting the trace from the
Britton-reduced stable-letter sequence.

## Effort estimate

- **Forward (#1–#3):** ~1–2 focused weeks. Word-manipulation + inductions, HNN translate
  lemmas in hand.
- **Backward faithfulness (#5):** the bulk. Applying `britton_lemma_full` to the machine
  HNN, then **pinch-elimination ⟹ trace extraction**. Genuinely deep; **several weeks to
  ~2 months**, dominated by how much trace-extraction machinery must be built on top of
  the Britton normal form (the main unknown).
- **Bridge (#6):** ~1–2 weeks, leveraging the proven enumerator.

**Total: ~1.5–3 months of focused work**, comparable to (perhaps a bit larger than) the
computability-theory port we just completed. Well-defined, not open-ended.

## Why Lean makes this materially more tractable (the instinct was right)

1. `britton_lemma_full` + the HNN tower are **already ported and proven** in tactus.
2. #5 is **structural induction on derivations / normal forms** — Lean's strength and Z3's
   weakness. This is precisely the class of proof that stalled the project on Z3 and
   motivated the move to Lean.
3. #1/#3's word manipulation is the kind Lean handles cleanly.
4. The base case (#4) is already done, in this style.

## Recommended first step (de-risk before committing the full ~quarter)

Revive `machine_group.rs` into a `tactus-group-theory` module and **prove the forward
direction (#1, #2)** first — the easier admits. This (a) validates the encoding end-to-end
on Lean, (b) exercises the HNN translate lemmas, and (c) gives a real calibration point for
how hard #5's pinch-elimination will be — turning the "weeks vs. 2 months" uncertainty into
a measured estimate before we commit to the backward direction.

**Payoff when done:** an explicit finite presentation — free group on `(#states + 2)`
generators plus one HNN stable letter per ZFC-enumerator-machine transition — that a
machine has checked *is* a foundation of mathematics. Printable. No axioms.
