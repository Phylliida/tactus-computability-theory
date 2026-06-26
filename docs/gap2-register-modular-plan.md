# GAP-2 — register → modular machine reduction (build plan, paper-faithful)

Discharges `ceer_realizes` (`src/ceer_relator_match.rs:81`), the sole undischarged hypothesis of the
explicit Higman chain. Route (Aanderaa–Cohen, *Modular machines I*, 1980, §1 + Thm 2; companion-confirmed
2026-06-26): **register machine → Turing machine → modular machine**. The TM→modular half is the paper's
explicit, well-specified construction (the "clean half"); register→TM is ref [18] (NOT in repo, the
reinvention-risk "dragon"). We build the clean half first.

## The source, pinned (paper pp. 2–4, read from PDF images, not the garbled OCR)

- **TM** = quintuples `q a a' q' D`, `D ∈ {L,R}`. Alphabet = naturals `0..n` (0 = blank). States =
  `n+1 .. m-1` (and possibly 0; we take states **strictly** in `n+1..m-1`, 0 reserved for "halted").
- **Config** `…b₁b₀ q a c₀c₁…` (state `q` left of scanned `a`): `u = Σbᵢmⁱ`, `v = Σcᵢmⁱ` (digit nearest
  head is lowest). Minsky form `(u, v, a, q) ∈ ℕ⁴`. **Packed base m**, not base n — symbols and states
  share the residue space `0..m-1`, which is the whole trick.
- **Pair encodings** (both represent the same config): `rep1 = (um+a, vm+q)`, `rep2 = (um+q, vm+a)`.
- **TM step** (pure arithmetic, no Seq tape):
  - `q a a' q' R`: `(u,v,a,q) ↦ (u·m+a', v div m, v mod m, q')`  (write a', move right: pop c₀=v mod m)
  - `q a a' q' L`: `(u,v,a,q) ↦ (u div m, v·m+a', u mod m, q')`  (write a', move left: pop b₀=u mod m)
- **Modular machine** `M`: modulus `m`, and **two quadruples per quintuple** `q a a' q' D`:
  `(a, q, a'm+q', D)` and `(q, a, a'm+q', D)`. (`c = a'm+q' < m²` since a'≤n<m, q'<m.)
- **Simulation** (the four cases, verified by arithmetic — see `lemma_sim_*`):
  - `R` from `rep1(C)` → `rep2(C')`;  `R` from `rep2(C)` → `rep2(C')`
  - `L` from `rep1(C)` → `rep1(C')`;  `L` from `rep2(C)` → `rep1(C')`
  where `C' = tm_step(C)`. (Both quads needed because the rep alternates with move direction.)
  Target pair for an R-quad: `(u·m²+a'm+q', v)`; both `rep1` and `rep2` of `C` carry residues that fire
  the right quad and land there. Paper p.3 gives exactly `(um²+a'm+q', v)` and `(u, vm²+a'm+q')`.
- **Determinism of `M`** (`mod_machine_wf`): with symbols `≤ n` and states `≥ n+1` DISJOINT, a first quad
  `(a,q)` (low,high) and a second quad `(q',a')` (high,low) can never share a residue pair; TM determinism
  (≤1 quintuple per `(q,a)`) gives the rest. **No special-state q₀ machinery needed at this layer** —
  the 0-as-blank-or-state ambiguity (paper §3) is a *register→TM* concern.
- **`(0,0)` is automatically terminal** when states ⊆ `n+1..m-1`: every quad has a residue ≥ n+1 in one
  coordinate (first quad b=q≥n+1, second quad a=q≥n+1), so none begins with `(0,0)`. ✓ ⟹ `mm_terminal(M,0,0)`.
- **`H₀` correspondence**: `(0,0)` is `rep1((u,v,a,q)=(0,0,0,0))` — blank tape, state 0, scanning blank.
  A TM that, on accepting, cleans to this config has `mm_in_H0(M, rep1(C₀)) ⟺ T halts to blank/state-0`.

## The decisive reuse (makes H₀ almost free)

`verus_group_theory::machine_group` already exports, verified:
- `lemma_yield_deterministic` — `M` deterministic ⟹ unique yield.
- **`lemma_step_preserves_h0(mm,a,b,a2,b2)`** — `mm_yields(mm,a,b,a2,b2) ⟹ (mm_in_H0(a,b) ⟺ mm_in_H0(a2,b2))`.
- `lemma_origin_in_H0` — `mm_terminal(mm,0,0) ⟹ mm_in_H0(mm,0,0)`.

So: prove the per-step sim `mm_yields(M, rep(C), rep(C'))` once; then `lemma_step_preserves_h0` gives
`mm_in_H0(rep(C)) ⟺ mm_in_H0(rep(C'))`; induct over `tm_run` to get `mm_in_H0(rep(C₀)) ⟺ mm_in_H0(rep(C_halt))`,
and `C_halt = (0,0,0,0)` ⟹ `mm_in_H0(rep(C₀)) ⟺ T accepts`. **The H₀ direction is then a short induction.**

## Brick decomposition

- **G2-A `tm.rs` — TM formalism.** `Tm{n,m,quints:Seq<Quintuple>}`, `Quintuple{q,a,a2,q2,dir}` (reuse
  `Dir`), `TmConfig{u,v,a,q}`. `tm_wf`, `tm_config_wf` (`c.a≤n ∧ c.q<m` + tape digit-invariant for the
  terminal corresp.), `quint_matches`, `tm_terminal`, `apply_quint`, `tm_step`, `tm_run`, `tm_halts_at`.
- **G2-B `tm_modular.rs` — construction + wf.** `quint_to_quads(qt,m)` (2 quads), `quads_of(quints,m)`
  (flatten), `tm_to_modmachine(tm)`. `lemma_quads_of_index` (index k ↦ quint k/2, sub k%2). 
  `lemma_tm_modmachine_wf` (`mod_machine_wf`, determinism via disjoint sym/state ranges).
- **G2-C — encoding + per-step simulation (the arithmetic heart).** `rep1`/`rep2`; `lemma_sim_step`:
  both reps of `C` `mm_yields` the right rep of `C' = tm_step(C)` (4 cases). Membership of the firing quad
  in `quads_of` via `lemma_quads_of_index`.
- **G2-D — terminal corresp. + H₀ corresp.** `lemma_tm_terminal_iff` (needs digit-invariant, c.a≤n);
  `lemma_mm_terminal_origin`; induction `lemma_run_sim` ⟹ `mm_in_H0(rep1(C₀)) ⟺ tm_halts_at(tm,C₀,origin)`.
- **G2-E (dragon, deferred) — register → TM** (ref [18], the genuine new formalism, ~90% of remaining
  GAP-2 effort; companion-confirmed 2026-06-26). **Key simplification found this session:** my TM's
  `(u,v)` ARE two base-`m` stacks (`tm_step` pushes/pops the low digit), so the modular machine is a
  **2-stack machine** and register→TM = **register → 2-counter machine** (counter = a unary stack:
  inc=push a `1`-symbol, dec=pop, zero-test = top digit is blank; each ≈ 1 TM quintuple). Route
  (Minsky 1967, *Computation: Finite and Infinite Machines* — anchor, do NOT reinvent):
  - **register (k regs) → 2-counter via Gödel encoding**: one counter holds `2^{r0}·3^{r1}·5^{r2}·…`,
    the other is scratch. `Inc(rᵢ)` = multiply by `pᵢ`; `DecJump(rᵢ,t)` = divisibility-test + divide by
    `pᵢ`. `multiply(C,p)`/`divide(C,p)` are the canonical 2-counter subroutines (the bulk; prove
    correctness + termination + scratch-restored-to-0, preserving the Gödel invariant `C = ∏ pᵢ^{rᵢ}`).
    Structure: a **bisimulation** — one RM step ↔ N counter steps. (Possible lighter alt: register →
    multi-stack (1 reg = 1 stack, trivial) → 2-stack via an interleaving encoding — cleaner inductive
    invariants than primes, but less standard for the modular equivalence; evaluate before committing.)
  - **2-counter → TM**: each counter is a `(u or v)` stack; map counter ops to `tm_step`. Need the TM to
    **clean up to the origin config `(0,0,0,0)`** on accept (the "halts on blank tape" condition).
  - the dovetail **search RM** `search_rm(e)` (input `enc(a,b)`, halts ⟺ `declared_equiv(e,a,b)`) built
    with the existing `multi_output_machine`/`multi_output_primitives` RM-composition infra. Then
    `ceer_to_modmachine(e) := tm_to_modmachine(rm_to_tm(search_rm(e)))`.
- **G2-F — wire `enc` to the word-numbering + discharge `ceer_realizes`** (the `decode∘ρ` packaging is
  GAP-1's, already proven; apply `lemma_tm_h0_iff` + identify `enc(a,b) = decode∘ρ(collapsed relator)`
  + the search-RM correctness, giving `mm_in_H0(mm, enc(a,b)) ⟺ declared_equiv(e,a,b)`).

**Status 2026-06-26:** **G2-A..G2-D COMPLETE & VERIFIED** (the clean half — TM→modular simulation +
full H₀ iff, `lemma_tm_h0_iff`). G2-E (register→2-counter→TM) + G2-F remain — the deferred,
co-design-gated dragon. Nothing here uses verifier escape hatches; `ceer_realizes` stays a sound
`requires`-hypothesis until G2-E/F land.
