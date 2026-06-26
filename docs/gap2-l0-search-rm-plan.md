# GAP-2-L0 — `search_rm(e)`: the dovetailing search register machine

Builds a register machine `search_rm(e)` that, on an input encoding the pair `(a,b)`, **halts iff
`declared_equiv(e, a, b)`** — i.e. iff some stage `s` of the CEER enumerator halts and declares `(a,b)`.
This is the top of the GAP-2 reduction chain: `search_rm(e)` is the `RM(k)` that L1 (k→2 Gödel) then
reduces to a 2-counter machine, which L2 (`rm_to_tm`, DONE) turns into a TM whose origin-reachability is
realized as `H₀` of a modular machine — discharging the machine content of `ceer_realizes` (G2-F).

**Status 2026-06-26:** DESIGN ONLY (this note). L0 is UNBLOCKED (it builds an `RM(k)` with as many
scratch registers as it wants, so it does NOT hit the 2-counter unconditional-jump gate that blocks the
L1 *machine* — see `gap2-register-to-tm-plan.md` §"L1 MACHINE BLOCKER"). The dovetail + fuel-instrumentation
is a STANDARD construction (textbook computability), so designing it solo is routine proof-engineering,
not an architecture fork.

## The exact contract

```
declared_equiv(e, a, b)  ⟺  ∃ s. stage_declares(e, s, a, b)
                         ⟺  ∃ s. ( halts(e.enumerator, s) ∧ {reg1,reg2 of the halt config} == {a,b} )
```
(`ceer.rs`: `declared_pair`/`stage_declares`/`declared_equiv`.) We want a `RegisterMachine` `M = search_rm(e)`
with `halts(M, input(a,b)) ⟺ declared_equiv(e,a,b)`, where `input(a,b) = pair(a,b)` (`pairing.rs`).

The predicate is **Σ₁**: `∃ (s, fuel). run_halts(E, init(s), fuel) ∧ pair_matches`. So we dovetail over the
single bound `T` and inside it over `s ≤ T`, simulating `E` for at most `T` steps.

## The core obstruction (why this isn't just `embed`-and-run)

`lemma_embed_reaches_target` (multi_output_primitives) runs an embedded sub-machine **to its halt** — it
diverges if the sub-machine doesn't halt. The enumerator `E` need NOT halt on every stage `s`, so we
cannot run `E` on `s` to completion; a non-halting stage would wedge the dovetail forever and miss later
declaring stages. We need a **fuel-bounded** simulation that always returns after `≤ fuel` steps with a
verdict {halted-with-pair | still-running}.

## Brick order

### B-L0.1 — fuel-instrumentation transform (the one genuinely-new brick)
`instrument(E) : RegisterMachine` adds a dedicated `fuel` register and, before each original step,
guards it: conceptually each original `pc` becomes a 2-instruction window
```
  guard(pc):  DecJump(fuel, TIMEOUT)     ; fuel==0 ⟹ goto TIMEOUT ; else fuel--, fall to body(pc)
  body(pc):   <the original instruction, with targets remapped pc ↦ guard(pc)>
```
plus a distinguished `HALTED` sink (reached when `E` would halt) and a `TIMEOUT` sink. Original Inc/DecJump
targets `t` remap to `guard(t)`; original `Halt` (and `pc == len`) routes to `HALTED`.

**Correctness `lemma_instrument_bounded`** (induct on `fuel`): from a config encoding `E`-config `c` with
`fuel = F`, `instrument(E)` reaches
- `HALTED` carrying `run(E, c, t)`'s registers, if `E` halts at some `t ≤ F` (`t = ` first halt time); or
- `TIMEOUT` carrying `run(E, c, F)`'s registers, if `E` has not halted within `F` steps.
This is the bounded analogue of `lemma_embed_reaches_target`; the per-step lemma mirrors
`lemma_embed_step_sim` but consumes one `fuel` unit per simulated step and exits to `TIMEOUT` at `fuel==0`.
Reuse `embed_instructions` shifting machinery for the target remap; the guard is the new content.

### B-L0.2 — the dovetail driver
Outer loop over `T = 0,1,2,…` (a bound register, only ever incremented — its loop-backs use a zero
scratch, fine at `RM(k)`). Inner loop over `s = 0..T`. Each inner iteration:
1. **reset** the `E`-bank to `init(E, s)` (clear bank via copy-to-scratch loops, set reg0 := s) and set
   `fuel := T`;
2. run `instrument(E)` (embedded via `embed_instructions`) using B-L0.1 → lands in `HALTED` or `TIMEOUT`;
3. if `HALTED`: compare `(reg1,reg2)` against the decoded `(a,b)` (equality via destructive-compare
   gadgets); on `{reg1,reg2} == {a,b}` jump to the machine's global `Halt`. Else continue the inner loop.
After `s == T`, `T += 1`, repeat. Reuse `copy_instrs`/`triple_dist_instrs` for bank setup + comparison;
`pair`/`unpair1`/`unpair2` (pairing.rs) to decode `(a,b)` from the input once at entry.

### B-L0.3 — assembly + the halts-iff
`lemma_search_rm_halts_iff`: `halts(search_rm(e), pair(a,b)) ⟺ declared_equiv(e,a,b)`.
- **(⟸)** declaring stage `s₀` with halt fuel `f₀`: at outer bound `T = max(s₀,f₀)` the inner iteration
  `s = s₀` runs `instrument(E)` with `fuel = T ≥ f₀` → `HALTED` with the declared pair → match → halt.
  (Monotonicity of `run_halts` in fuel gives `T ≥ f₀ ⟹ halted within T`.)
- **(⟹)** a halt of `search_rm` happened at some `(T,s)` reaching `HALTED` with a matching pair ⟹
  `run_halts(E, init(s), T)` ∧ pair matches ⟹ `stage_declares(e,s,a,b)` ⟹ `declared_equiv`.

## Reuse map (already verified, in this crate)
- `machine.rs`: `run`/`run_halts`/`step`/`machine_wf`/`config_wf`, monotonicity (`lemma_run_monotone`),
  determinism (`lemma_run_deterministic`).
- `multi_output_primitives.rs`: `embed_instructions` + `lemma_embed_step_sim`/`lemma_embed_reaches_target`
  (model the B-L0.1 per-step + bounded lemmas on), `copy_instrs`/`triple_dist_instrs` + their loop lemmas,
  the fuel-composition helpers (`lemma_run_split`/`lemma_run_halts_split`/`lemma_not_halted_*`).
- `multi_output_machine.rs`: the phase-chaining pattern (`lemma_multi_output_for_input`) is the template
  for B-L0.2's per-iteration phase composition.
- `pairing.rs`: `pair`/`unpair1`/`unpair2` + injectivity/surjectivity/bounds for input decode + dovetail.
- `ceer.rs`: `declared_pair`/`stage_declares`/`declared_equiv`/`lemma_declared_pair_well_defined`.

## Guard-rails
- No `assume`/`admit`/`external_body`. The fuel register makes every simulation terminating, so the whole
  `search_rm` is a legitimate total construction whose *halting* (not its individual gadget runs) encodes
  the Σ₁ predicate.
- `search_rm` uses many registers freely (E-bank + fuel + scratch + bound/index) — it is the `RM(k)` input
  to L1, NOT the 2-counter machine, so the L1-machine gate does not apply here.
- Keep B-L0.1 (bounded sim) and B-L0.2 (dovetail) in separate modules to limit trigger pollution.

## Open design notes
- **Reset cost:** re-running `E` from `init(s)` each `(T,s)` (clear-bank + set reg0) is `O(bank)` per
  iteration — fine (correctness only; the TM/modular blow-up is downstream and irrelevant to existence).
- **Pair symmetry:** `stage_declares` accepts `(a,b)` OR `(b,a)`; the B-L0.2 comparison must test both
  orientations (two compares, OR the jump).
- **`HALTED` vs `TIMEOUT` register frame:** B-L0.1 must preserve `reg1,reg2` of the simulated `E`-config
  into the `HALTED` exit so B-L0.2 can read the declared pair (mirror `lemma_embed_reaches_target`'s
  register-frame postcondition).
