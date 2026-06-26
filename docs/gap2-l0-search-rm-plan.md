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

### B-L0.1 — fuel-instrumentation transform (the one genuinely-new brick) — ✅ DONE 2026-06-26 (7/0)

**Built in `src/search_rm_sim.rs` (7 verified, 0 errors), exactly the design below.** The "2-instruction
window" is realised as a **stride-2 layout**: `instrument_instructions(instrs, reg_offset, pc_offset,
halted_pc, timeout_pc, fuel_reg, scratch)` puts the guard `DecJump{fuel_reg, timeout_pc}` at even slot
`pc_offset+2i` and the remapped body at odd slot `pc_offset+2i+1`; DecJump targets `t` remap to
`pc_offset+2t`, `Halt` → `DecJump{scratch, halted_pc}`, and `halted_pc = pc_offset + 2*len` unifies
"fall off the end" with "jump to len". The toolkit (all consumed by B-L0.2):
- **`instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, phi, c_sub, c)`** — host `c`
  tracks E-config `c_sub` *at the guard* of `c_sub.pc`, E-bank shifted by `reg_offset`, scratch held 0,
  `phi` fuel left.  **`instrument_frame(...)`** — the structural side-conditions (layout match, bank/sink
  disjointness, bounds, `halted_pc != timeout_pc`).
- **`lemma_instrument_halts`** (⟸): `run_halts(E, c_sub, phi-1)` ⟹ reaches `halted_pc` within `2*phi`
  steps carrying `run(E, c_sub, phi-1)`'s registers in the shifted bank. (The `phi-1` budget gives one
  guard's slack so a `Halt`-instruction halt, which costs an extra guard vs a `pc==len` halt, still lands
  on HALTED — the fuel-boundary fencepost, handled by being generous with fuel in the dovetail.)
- **`lemma_instrument_reaches_sink`** (⟹): always reaches `halted_pc` or `timeout_pc` within `2*phi+1`
  steps (totality), and **reaching `halted_pc` ⟹ `run_halts(E, c_sub, phi)` ∧ E-bank == `run(E,c_sub,phi)`**
  (soundness — a HALTED verdict reflects a genuine declaration). This is the ⟹ direction's workhorse.
- Helpers `lemma_instrument_estep` (guard+body = 2 host steps advance 1 E-step), `lemma_instrument_halt_instr`,
  `lemma_instrument_guard_timeout`, `lemma_run_add` (run composition `run(m,c,a+b)==run(m,run(m,c,a),b)`).

*(Original design, for reference:)*
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

> **⚠ DESIGN SHARPENED 2026-06-26 (correcting the original note).** The original step 3 said "compare
> against the *decoded* `(a,b)` … `unpair1`/`unpair2` to decode `(a,b)` from the input." But
> `pairing.rs`'s `pair`/`unpair1`/`unpair2` are **spec functions (math), NOT register-machine
> subroutines** — and *unpairing* on an RM is the harder direction (inverse-triangular row search).
> **Avoid it entirely by comparing in the FORWARD direction.** Since `pair` is injective
> (`lemma_pair_injective`) and the input is `pair(a,b)`:
>
>   `{reg1,reg2} == {a,b}`  ⟺  `pair(reg1,reg2) == input`  ∨  `pair(reg2,reg1) == input`.
>
> So **re-pair E's declared output and compare to the preserved input** — needing only the *forward*
> `pair` (a couple of accumulation loops, no search) + a destructive nat-equality loop. No unpairing.

The driver `search_rm(e)` is one `RM(k)` machine (`k` = E-bank `ne` + the registers below). The input
`pair(a,b)` lands in reg 0; **first copy it to a preserved register `inp`** (it is never decoded).
Outer loop over `T = 0,1,2,…` (a bound register, only ever incremented — its back-edges use a guaranteed-0
scratch as `DecJump{zero, top}`, exactly as `copy_instrs` does; fine at `RM(k)`). Inner loop over `s = 0..T`.
Each inner iteration:
1. **reset** the E-bank to `initial_config(E, s)` (clear the `ne`-register bank via copy-to-scratch
   drains, then set bank-reg 0 := `s` by copying a preserved `s`-register) and set `fuel := T` (copy `T`);
2. run `instrument(E)` (the B-L0.1 block, embedded at the driver's `pc_offset`) → lands on `halted_pc`
   or `timeout_pc` (by `lemma_instrument_reaches_sink`, ≤ `2T+1` steps);
3. on `halted_pc`: read the E-bank's `reg1,reg2`; **compute `pair(reg1,reg2)` and `pair(reg2,reg1)`**
   into scratch, **destructive-compare each to a copy of `inp`**; on either match jump to the global
   `Halt`. Else continue the inner loop.
After `s == T`, `T += 1`, repeat. Reuse `copy_instrs`/`triple_dist_instrs` for bank setup + the
preserve-copies; the new arithmetic is the **RM forward-`pair` subroutine** (B-L0.2a below).

**B-L0.2a — RM forward-`pair` subroutine — ✅ DONE 2026-06-26 (`src/search_rm_arith.rs`, 15/0).**
`double_dist_instrs` (drain a register into two, independent accumulators) + `lemma_triangular_loop`
(`t := triangular(n)` via outer countdown + inner `copy(i→ibak)`+`double_dist(ibak→t,i)`, `lemma_tri_step`
recurrence) + `lemma_pair_subroutine` (`p := pair(x,y) = triangular(x+y)+x`, verified against spec
`pairing::pair`). Reusable; consumed by B-L0.2's comparison. *(original design:)* `pair(x,y) =
triangular(x+y) + x`, `triangular(n) = n(n+1)/2 = Σ_{k≤n} k`. RM construction: `sum := x+y` (two drains),
then `triangular` by an **outer countdown of a copy of `sum`** that, on iteration with running index `i`,
adds `i` to the accumulator `t` (inner add via a distribute-and-restore of `i`, reusing the
`triple_dist`/`copy` loop lemmas), then `pair := t + x`. Correctness proven against the spec `pair`/
`triangular` with the existing `pairing.rs` lemmas. This is self-contained and reusable; build it FIRST.

**B-L0.2b — bank reset + nat-equality — ✅ GADGETS DONE 2026-06-26 (`src/search_rm_compare.rs`, 3/0).**
`lemma_eq_test_loop` (`eq_test_instrs(a,b,zero,neq,sp)`: destructive compare, reaches `sp+5` iff `(a)==(b)`,
else `neq`) + `lemma_clear_loop` (`clear_instrs(r,zero,sp)`: drain `r` to 0 in `2v+1` steps). Bank reset =
`clear` each E-bank register + `copy` a preserved `s` into bank-reg-0.

> **✅ GADGET TOOLKIT COMPLETE.** Everything the dovetail assembly chains is now built + verified:
> `instrument` (B-L0.1), forward `pair` (B-L0.2a), `eq_test` + `clear` (B-L0.2b), plus the existing
> `copy_instrs`/`triple_dist_instrs`/`double_dist_instrs`. **The ONLY remaining L0 work is the assembly
> (B-L0.2c + B-L0.3) — no new gadget arithmetic.**

**B-L0.2c — loop assembly + `machine_wf`** (the remaining hard phase): lay out the phases in disjoint
pc-windows (à la `tm_assemble`/`multi_output_machine`), each gadget keyed in its own window; the outer/inner
loop control via `DecJump{zero, window_top}` back-edges. Suggested proof architecture (mirrors
`lemma_embed_reaches_target` / the tm_run_sim run-inductions):
- **Register map** (one `RM(k)`): E-bank `[E0..E0+ne)`; `fuel`, `zero` (the instrument's); `inp` (preserved
  input); `Treg`, `sreg` (loop counters); `skeep` (preserved copy of `s` for the bank reset); plus the
  `pair` working set (`xk,nc,i,t,ibak,p`) and the two `eq_test` operands (`pc1`, a copy of `inp`). All
  distinct — bundle distinctness in a `search_rm_regs_wf` spec like `pair_subroutine_frame`'s `all_distinct9`.
- **`lemma_inner_iter`** (one `(T,s)` pass, NOT a loop — a straight-line chain): from a config at the inner
  window top with bank/fuel set for `(s, T)`, chain `clear`×ne + `copy(skeep→E0)` (reset) → set `fuel:=T`
  → `lemma_instrument_reaches_sink` → on `halted_pc`, `lemma_pair_subroutine` ×2 + `lemma_eq_test_loop` ×2 →
  reach global `Halt` iff the pair matches, else the inner back-edge. Chain via `lemma_run_add` (the
  toolkit's existential step-counts compose exactly as in `lemma_pair_subroutine`). Reuse the soundness
  arm of `lemma_instrument_reaches_sink` (`halted_pc ⇒ run_halts(E,init(s),T) ∧ bank==run(...)`).
- **`machine_wf`**: every `(state,scanned)`… no — for an RM it is just: `num_regs>0` + every Inc/DecJump
  register `< num_regs` + every DecJump target `≤ len`. All targets are manifest window offsets ⇒ a
  `Seq::new`-indexed `gen`-style constructor with a per-index bound lemma (cf. `tm_assemble`'s `lemma_gen_key`).

### B-L0.3 — assembly + the halts-iff
`lemma_search_rm_halts_iff`: `halts(search_rm(e), pair(a,b)) ⟺ declared_equiv(e,a,b)`.
- **(⟸)** declaring stage `s₀` with halt fuel `f₀`: at outer bound `T = max(s₀,f₀)` the inner iteration
  `s = s₀` runs `instrument(E)` with `fuel = T ≥ f₀` → `HALTED` with the declared pair → match → halt.
  (Monotonicity of `run_halts` in fuel gives `T ≥ f₀ ⟹ halted within T`.)
- **(⟹)** a halt of `search_rm` happened at some `(T,s)` reaching `HALTED` with a matching pair ⟹
  `run_halts(E, init(s), T)` ∧ pair matches ⟹ `stage_declares(e,s,a,b)` ⟹ `declared_equiv`.
- **The comparison↔declaration link** (the compare-by-repairing correctness): the gadget reaches the
  match-exit iff `pair(reg1,reg2)==inp ∨ pair(reg2,reg1)==inp`. With `inp == pair(a,b)`,
  `lemma_pair_injective` turns each disjunct into `(reg1,reg2)==(a,b)` resp. `(reg2,reg1)==(a,b)`, i.e.
  exactly `stage_declares`'s `(reg1==a∧reg2==b) ∨ (reg1==b∧reg2==a)`. The HALTED soundness gives
  `(reg1,reg2) == declared_pair(e,s)` (via `lemma_declared_pair_well_defined` tying the chosen-fuel halt
  to the `T`-fuel halt), closing the iff.

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
