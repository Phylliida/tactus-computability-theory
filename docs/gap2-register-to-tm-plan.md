# GAP-2-E — register machine → Turing machine (the deferred dragon)

Builds `rm_to_tm(R)` : a Minsky `(u,v,a,q)` TM (the `tm.rs` formalism, G2-A) that **reaches the
origin config `(0,0,0,0)`** iff register machine `R` halts. Feeding it through the verified
`tm_to_modmachine` + `lemma_tm_h0_iff` (G2-B..D) realizes `R`'s halting set as `H₀`, discharging the
machine content of `ceer_realizes` (`src/ceer_relator_match.rs:81`, the sole open GAP-2 obligation).

Companion-confirmed design (port 8051, 2026-06-26): **Route A** (RM `k` → RM `2` → TM), unary-separator
tape, eat the unbounded walk with copy-loop-style monotone invariants, build `search_rm` at the RM level.

## The exact contract we must hit (`lemma_tm_h0_iff`, `tm_h0_bwd.rs:347`)

```
tm_wf(tm) ∧ tm_config_wf(tm, c) ⟹
  ( mm_in_H0(tm_to_modmachine(tm), rep1(c).0, rep1(c).1)  ⟺  ∃fuel. tm_halts_at(tm, c, tm_origin(), fuel) )
```

So `rm_to_tm(R)` must:
1. be `tm_wf` (m>1, 0<n<m, every quintuple wf, **deterministic** — ≤1 quint per `(state,scanned)`);
2. on the encoded init config `C(α)` satisfy `tm_config_wf` (scanned ≤ n, state < m, both half-tapes
   carry only symbol-digits ≤ n — the `digits_le` invariant);
3. **reach `tm_origin() = (0,0,0,0)` exactly when `R` halts** — i.e. a CLEANUP phase that blanks the
   whole tape and drops to state 0 on accept. `tm_origin()` is `tm_terminal` automatically (state 0 is
   below every quint's state ≥ n+1), so once we land there we stay (`tm_halts_at` true).
   If `R` loops, the TM must loop too and never transiently hit `(0,0,0,0)` (never use state 0 except as
   the post-cleanup halt; never present a fully-blank tape in state 0 mid-run).

## The tape layout — why **2** blocks, and why it's shift-free

Alphabet: `0`=blank, `1`=mark, `2`=separator (so `n ≥ 2`). States `≥ n+1`. The two-counter config
`(c1, c2)` ⟼ TM config with the head resting **on the separator** (`a = 2`):

```
 ... 0 0 | 1 1 … 1 |  (2)  | 1 1 … 1 | 0 0 …
         └─ c1 ───┘  head   └─ c2 ──┘
   u = repunit_m(c1)  (low digit = inner 1, nearest head)
   v = repunit_m(c2)  (low digit = inner 1, nearest head)
   a = 2,  q = current 2-counter state
```
`repunit_m(c) = 1+m+…+m^{c-1} = (m^c−1)/(m−1)`; note `repunit_m(c+1) = m·repunit_m(c) + 1`.

**Why exactly two blocks (the crux observation).** Each counter grows/shrinks **shift-free at its
OUTER (blank-adjacent) end**: c1 at the far left, c2 at the far right. A third block in a row would have
no free blank end → every inc/dec would have to *shift* the tail (an O(tape) insertion gadget). With two
blocks the separator never moves and no content is ever shifted:
- `inc(c1)`: walk left through c1's 1s to the blank, write a `1` (block extends left), walk back to `2`.
- `dec(c1)`: walk left to the outer boundary 1, blank it (left boundary moves right by 1), walk back.
- `zero-test(c1)`: **bounded** — peek `u % m` (the inner cell next to the separator): `1` ⟺ c1>0,
  blank ⟺ c1=0. (`[L write d][R write back]` restores `u,v`; nets only a state/scanned change.)
- c2 symmetric (right side, R-moves).

So the only unbounded gadgets are inc/dec (a walk to the outer end). Each is a single decreasing-fuel
loop whose invariant is the `multi_output_primitives::lemma_copy_loop_inner` pattern: "walk while scanned
is `1`, count carried digits; the carried digits return on the walk back." Concretely the gadget effect
is a clean repunit edit `repunit(c±1)` proven by induction, no tape-sequence abstraction needed — we work
directly in `(u,v)` arithmetic, mirroring the existing register copy-loop proofs.

## The reduction layers

```
 R = RegisterMachine(k)                                    [the CEER enumerator, or search_rm(e)]
   │  L0: build search_rm(e) at the RM level (dovetail the enumerator over stages; reuse
   │      embed_instructions + copy/triple-dist loop gadgets + lemma_embed_reaches_target).
   ▼
 RM(k)                                                     [Inc/DecJump/Halt, k registers]
   │  L1: k → 2  (Gödel)  — THE ONE OPEN SUB-DECISION (see below).
   ▼
 RM(2) = 2-counter machine                                [counters C1,C2; only Inc/DecJump]
   │  L2: 2-counter → TM  — the isolated hard core; build the unary-separator gadget library.
   ▼
 Tm  (rm_to_tm)
   │  G2-B..D (DONE): tm_to_modmachine + lemma_tm_h0_iff
   ▼
 ModMachine  with  H₀ = encoded halting set of R
```

### L1 (k → 2) — the one open sub-decision

The Gödel route `C = ∏ pⱼ^{rⱼ}` (one counter the product, one scratch) implements `Inc(rᵢ)` =
multiply-by-`pᵢ` and `DecJump(rᵢ)` = divisibility-test-and-divide-by-`pᵢ`. Multiply/divide-by-constant
on 2 counters are clean copy-loops (invariant `subtracted + p·quotient + partial = original`, **no
number theory**). The divisibility *test* loop is likewise pure arithmetic. The ONLY number-theoretic
fact is connecting the test back to the register: `pᵢ | ∏ pⱼ^{rⱼ} ⟺ rᵢ ≥ 1`.
- `rᵢ ≥ 1 ⟹ pᵢ | C`: trivial (factor out one `pᵢ`).
- `rᵢ = 0 ⟹ pᵢ ∤ C`: needs **Euclid / coprimality** (`pᵢ` coprime to each other `pⱼ`). This is the
  only genuinely number-theoretic obligation in the whole dragon.

Alternatives that avoid Euclid both have their own cost, so they are NOT obviously better:
- **k-block tape** (skip RM(2), put k unary blocks on the TM): inner blocks have no free blank end ⟹
  every inc/dec needs an insertion/shift gadget. Worse than one Euclid lemma.
- **pairing/interleaving** encode (r₀..r_{k−1}) into one counter: decode/encode is triangular-number /
  Cantor-pairing arithmetic on counters — messier than Euclid.

**PICK: Gödel-primes (Option A), isolate the Euclid fact to a single lemma** (`lemma_prime_div_godel`).
Two companion passes disagreed (one → Route A, one → Option C "avoid number theory, use a shift gadget"),
because the second glossed the **shift gadget**: in the `(u,v)` Minsky model, inserting a `1` into an
*inner* block is a genuine O(tape) shift loop (carry a symbol through the state, window invariant), and
shift-free growth is possible only for **≤2 blocks** (the two far blank ends). So the real trade is
*one standard Euclid lemma* (Option A) vs *a bespoke shift-gadget loop* (Option C). Option A wins:
its 2-block TM gadgets are shift-free and the k→2 multiply/divide reuse the existing copy-loop infra;
Euclid is bounded, self-contained, low-risk (check `vstd::arithmetic` first, prove from scratch if absent).
L1 is **not on the critical path** — the L2 TM gadget library below is needed identically regardless, so
build L2 first and settle the Euclid lemma when L1 is reached.

### L2 (2-counter → TM) — the universal foundation, build FIRST

Parametric-in-layout gadget library over the unary-separator tape (k=2 is the special case; the gadgets
are written once and reused). Bottom-up brick order (companion's priority):

- **B0 `tm_run` composition lemmas** (`tm.rs` analogs of `machine.rs`): `tm_run` split
  (`tm_run(f1+f2) = tm_run(tm_run(·,f1),f2)`), monotone, determinism, halted-identity, and a
  `tm_halts_at` ∘ composition lemma. Needed to chain every gadget. **← start here, unblocked.**
- **B1 layout spec** : `two_counter_config(c1,c2,q) : TmConfig` (= `(repunit(c1), repunit(c2), 2, q)`),
  `repunit_m`, and `lemma_two_counter_config_wf` (`tm_config_wf`: digits ≤ n, since repunit digits ∈{0,1}).
- **B2 zero-test gadget** (bounded): `[L peek][R restore]`; `lemma_zerotest` — lands in one of two
  states by `c=0?`, config otherwise unchanged.
- **B3 inc gadget** (walk-left loop + write + walk-back): `lemma_inc` — `two_counter_config(c1,c2,q)`
  runs to `two_counter_config(c1+1,c2,q')` in fuel `2·(c1+1)`. **DESIGN (left counter):** two states
  `(q_walk, q_back)`, quintuples
  ```
    (q_walk, 2, 2, q_walk, L)   peel the separator, head left
    (q_walk, 1, 1, q_walk, L)   peel a block-1, head left
    (q_walk, 0, 1, q_back, R)   at the left blank: WRITE the new 1 (the inc), turn around
    (q_back, 1, 1, q_back, R)   walk back over a block-1, head right
  ```
  The walk-back ends with the head back **on the separator** (scanned `2`) in state `q_back` — that IS
  `two_counter_config(c1+1, c2, q_back)`; `q_back` is the gadget's *exit* state (the next gadget keys its
  entry on `(q_back, 2)`; determinism is fine since `(q_back,1)` vs `(q_back,2)` differ). Trace from
  `two_counter_config(c1,c2,q_walk)`: `c1+1` L-steps to the blank (peel sep + `c1` ones, `u→0`,
  scanned→0), 1 turnaround R-step (write 1), `c1` walk-back R-steps → `(repunit(c1+1), repunit(c2), 2,
  q_back)`. Works for `c1=0` (1+1+0 = 2 steps; turnaround pops the separator straight back).
  **Pile invariant (the cost):** during the walk the peeled symbols pile onto `v` — after `j` L-steps
  `v_j = repunit(c2)·m^{j} + 2·m^{j-1} + repunit(j-1)` (define recursively `v_j = v_{j-1}·m + digit` to
  dodge raw `m^j`; carry it through a decreasing-fuel loop lemma `lemma_walk_left_inner` exactly like
  `multi_output_primitives::lemma_copy_loop_inner`). Walk-back is the mirror loop reconstructing `u`.
- **B4 dec gadget**: `lemma_dec` — to `two_counter_config(c1−1,c2,q')` for `c1 ≥ 1`. **REFINED DESIGN
  (reuses both walk loops):** walk left **to the blank** (same as inc: sep-peel + `lemma_walk_left_inner`
  `j0=c1−1`, `c1+1` steps), then erase the outermost 1 — which the walk-out left as the pile's low digit.
  Quintuples (5, vs inc's 4):
  ```
    (q_walk, 2, 2, q_walk, L)   peel separator
    (q_walk, 1, 1, q_walk, L)   walk left over block-1s
    (q_walk, 0, 0, q_disc, R)   turnaround: WRITE 0 (erase) — the outer 1 pops into scanned, u stays 0
    (q_disc, 1, 0, q_back, R)   DISCARD that popped 1 (write 0, don't push it back onto u)
    (q_back, 1, 1, q_back, R)   walk back (lemma_walk_back_inner, k0=0)
  ```
  After the erase-turnaround: `(0, pile_ones(V1, c1−1), 1, q_disc)` (`V1 = repunit(c2)·m+2`). The discard
  step pops again: for **`c1 = 1`** it pops `V1` itself → lands directly on `two_counter_config(0,c2,q_back)`
  (no walk-back); for **`c1 ≥ 2`** → `(0, pile_ones(V1,c1−2), 1, q_back)`, then `lemma_walk_back_inner`
  (`k0=0, rem0=c1−2`) reconstructs `u = repunit(c1−1)`. Total `2c1+2` steps. The `c1=1` vs `c1≥2` split is
  the one wrinkle (the discard either lands on the separator or feeds the walk-back). **DecJump** folds the
  B2 zero-test: peek first; if `c1=0` jump to target, else run this dec. Right-counter inc/dec are the
  L↔R mirror (walk via R-moves through `v`).

  **Status: inc (B3) DONE & verified (`tm_inc.rs lemma_inc`, 5 verified). Dec (B4) = this design, next.**
- **B5 per-instruction simulation — ✅ DONE & verified (full crate 400/0).** See the B5 status
  block below for the architecture. `lemma_sim_step` (`tm_sim.rs`): one non-halting 2-counter step
  ↔ one gadget run, `tm_reaches(rm_to_tm(R2), enc(c), enc(step(c)))`.
- **B6 run simulation + cleanup — ✅ DONE & verified (full crate 426/0).** `tm_run_sim.rs`
  `lemma_rm_tm_origin_iff`: a wf 2-counter machine halts from a wf config `c` **iff**
  `rm_to_tm` reaches `tm_origin()` from `rm_config_enc(rm,c) = two_counter_config(c.r0,c.r1,entry(c.pc))`.
  See the B6 status block below for the architecture. The cleanup quintuples were ALREADY built into
  `rm_to_tm` (the `pc==len` window, `cleanup_act` in `tm_assemble.rs`): B6 proved they reach origin
  + the run induction (both directions); the constructor is frozen.

### G2-F (wiring, after L0–L2)

`config_encode` (currently the `(0,0)` placeholder in `modular_reduction.rs`) is OURS to define — pick it
to equal the TM init layout for input `decode(α)`. Then `lemma_tm_h0_iff` + `decode∘ρ` (GAP-1, proven)
identify `mm_in_H0(mm, enc(a,b)) ⟺ declared_equiv(e,a,b)` and discharge `ceer_realizes`.

## Invariants & guard-rails
- No `assume` / `admit` / `external_body`. Full end-to-end.
- The TM stays deterministic: per-instruction quintuple blocks use disjoint state ranges; `tm_wf`'s
  "≤1 quint per (state,scanned)" is discharged by construction (each `(state,scanned)` keyed uniquely).
- Never transiently hit `(0,0,0,0)`: simulation states are all ≥ n+1 and ≠ the final halt state; the
  blank-tape-in-state-0 config appears only as the genuine post-cleanup origin.
- Work in `(u,v)` arithmetic with repunit formulas + decreasing-fuel loop lemmas (no separate tape-seq
  abstraction) — matches the verified `multi_output_primitives` copy-loop style.

**Status 2026-06-26:** design locked. **DONE & verified, all committed, purely additive; full crate
426/0:** B0 `tm_run_lemmas.rs`, B1 `tm_two_counter.rs`, gadget infra + B2 `tm_gadget.rs`, B3
`tm_walk.rs`+`tm_inc.rs`, B4 `tm_dec.rs`, B5.0 `tm_bounce.rs` (exit-routing
trampoline), B5.1 `tm_walk_right.rs` (right walk loops), B5.2 `tm_right_gadgets.rs` (peek/inc/dec
right mirrors), B5.3 `tm_assemble.rs` (`rm_to_tm` + `tm_wf`), B5.4/B5.5 `tm_sim.rs`
(`lemma_sim_step`), **B6 (this session)**: `tm_cleanup.rs` (cleanup phases A/B/C + `lemma_sim_halt`),
`tm_run_sim.rs` (run induction + the halting iff `lemma_rm_tm_origin_iff`). **NEXT =**
L1 (k→2 Gödel, the one Euclid lemma), L0 (search_rm dovetailer), G2-F (wire `config_encode`/`enc` +
discharge `ceer_realizes`).

### B6 architecture (the run simulation + halting iff — read before L0/L1/G2-F)

`rm_config_enc(rm,c) = two_counter_config(c.registers[0], c.registers[1], entry(c.pc), tm_mod(len))`
is the layout encoding of a register-machine config. The headline `lemma_rm_tm_origin_iff`
(`tm_run_sim.rs`):

> `(∃F. run_halts(rm,c,F))  ⟺  (∃fuel. tm_halts_at(rm_to_tm(rm), rm_config_enc(rm,c), tm_origin(), fuel))`

for any `machine_wf` 2-counter `rm` and `config_wf` `c`. G2-F will set `config_encode` to
`rm_config_enc(rm, initial_config(rm, input))` and compose with `tm_h0::lemma_tm_h0_iff`
(`tm_halts_at(.,origin) ⟺ mm_in_H0`) to get `rm halts ⟺ mm_in_H0`, the machine content of
`ceer_realizes`.

- **`tm_cleanup.rs` (B6 part 1):** proves the already-built `cleanup_act` quintuples reach origin.
  - `lemma_cleanup_phaseA` (induct on `c1`): peek+dec+bounce-back-to-`entry(len)` loop drains the
    left counter — `(c1,c2,entry(len)) →* (0,c2,entry(len)+6)`. Reuses `lemma_peek_gadget` + `lemma_dec`
    + `lemma_bounce_left`, quintuples extracted at window `pc=len` via `lemma_quint_at(rm,len,off,sym)`.
  - `lemma_cleanup_phaseB` (induct on `c2`, L↔R mirror): `(c1,c2,entry(len)+6) →* (c1,0,entry(len)+12)`.
  - `lemma_cleanup_phaseC`: the single `(entry(len)+12, 2, 0, 0, R)` quintuple — `(0,0,entry(len)+12) →¹ origin`.
  - `lemma_cleanup`: A (right counter untouched) → B (left already 0) → C.
  - `lemma_sim_halt`: a `Halt` instruction bounces `entry(pc) → entry(len)` (the cleanup entry), via
    `lemma_bounce_left` on the `halt_act` quintuples.
- **`tm_sim.rs` (strengthened this session):** added `tm_reaches_pos` (reaches in `≥1` steps) + intro;
  the 4 per-instruction sims + `lemma_sim_step` now ALSO ensure `tm_reaches_pos` (the gadget fuels are
  all `≥2`). `lemma_sim_decjump_right` needed `return`-isolation of its two branches to stay under rlimit.
- **`tm_run_sim.rs` (B6 part 2):**
  - `lemma_sim_run` (induct on run fuel `F`): chains `lemma_sim_step` (transitively, via
    `lemma_tm_reaches_trans`) to `tm_reaches(enc(c), enc(run(rm,c,F)))`.
  - `lemma_run_halts_is_halted` / `lemma_run_preserves_config_wf` / `lemma_rm_terminal_cases`
    (halt config is `pc==len` OR a `Halt`) — the run bookkeeping.
  - **Forward** `lemma_rm_halts_implies_tm_origin`: run-sim to the halted config, then cleanup
    (a `Halt` first routes via `lemma_sim_halt`; a `pc==len` halt IS the cleanup entry), then
    `lemma_tm_run_reaches_halts_at` (origin terminal via `lemma_origin_tm_terminal`).
  - **Backward** `lemma_tm_origin_implies_rm_halts` (induct on TM fuel `f`): if `rm` is halted, done
    (no cleanup reasoning needed); else `tm_reaches_pos` gives `g≥1` to `enc(step(c))`, `g≤f` because
    origin is terminal (else origin `==` `enc(step(c))`, whose state `≥3`), run-split peels `g`, recurse
    on `f−g < f`. The `g≥1` is exactly why `tm_reaches_pos` is needed — a `DecJump`-on-zero self-loop
    (`enc(c)==enc(step(c))`) would otherwise admit `g=0` and never terminate.

### ⚠ FOUNDATION FIX (this session, committed): `quint_wf` q2 bound weakened

`quint_wf` originally required `n+1 ≤ q2 < m` for the **next**-state field. That made
`tm_origin()=(0,0,0,0)` unreachable (`apply_quint` sets `q := q2`; reaching state 0 needs `q2=0`),
so `tm_halts_at(.,origin,.)` — hence the whole `lemma_tm_h0_iff` reduction — was vacuous for any
`tm_wf` TM. **Fix:** drop the `n+1 ≤ q2` lower bound, keep `q2 < m`. State 0 stays terminal via the
**current**-state `q ≥ n+1` (`lemma_origin_tm_terminal`); no contract proof used `q2 ≥ n+1` (only
`lemma_tm_config_wf_step` asserted it incidentally — needs only `q2 < m`). The cleanup's final
blank-separator quintuple `(CC, 2, 0, 0, R)` uses `q2=0`.

### B5 architecture (the `rm_to_tm` assembly — read before B6)

`rm_to_tm(R2)` (a 2-counter machine: `num_regs=2`, reg 0 = left counter `c1` in `u`, reg 1 = right
counter `c2` in `v`) is one **uniform** layout (`tm_assemble.rs`):
- `n = 2` (alphabet 0=blank,1=mark,2=separator). `entry(pc) = 3 + 16·pc`. `m = tm_mod(len) =
  19 + 16·len` where `len = R2.instructions.len()`.
- Every program position `pc ∈ [0, len]` owns a **16-state window** `[entry(pc), entry(pc)+16)` and
  contributes **exactly 48 = 16·3 quintuples**, one per `(state-offset, scanned-symbol)` ∈
  `[0,16)×{0,1,2}`. `quints = Seq::new(48·(len+1), |idx| gen(R2, idx))`,
  `gen`: `pc=idx/48, off=(idx%48)/3, sym=(idx%48)%3`, quintuple `= mk_quint(entry(pc)+off, sym,
  pos_act(R2,pc,off,sym)…)`. Real gadget transitions fill the slots they use; the rest are inert
  dummies `(entry+off, sym, sym, entry, L)` keyed at their own `(off,sym)` (never on-trajectory).
- Instruction gadgets at `pc<len` (`inc_left/right_act`, `decjump_left/right_act`, `halt_act`), the
  **cleanup** at `pc=len` (`cleanup_act`).
- **Window → state offsets** (gadgets reuse the existing left + new right gadgets + bounce):
  - **Inc** (off 0–2): s0=walk(entry), s1=back/bounce-entry, s2=bounce-mid. exit→`entry(pc+1)`.
  - **DecJump** (off 0–5): s0=peek-entry, s1=peek-branch (pos→s2, zero→`entry(target)`), s2=dec-walk,
    s3=dec-disc, s4=dec-back/bounce-entry, s5=bounce-mid. exit→`entry(pc+1)`.
  - **Halt** (off 0–1): a left bounce routing `entry(pc) → entry(len)` (cleanup entry).
  - **Cleanup** (off 0–12): phase A (0–5) peek+dec-left loop `c1`→0; phase B (6–11) peek+dec-right
    loop `c2`→0; phase C (12) `(CC,2,0,0,R)` → `tm_origin()`.
- **`tm_wf` (`lemma_rm_to_tm_wf`)**: `quint_wf` per quintuple (state `=entry(pc)+off` and scanned
  `=sym` are MANIFEST in `gen`; written symbol / next state bounded by `lemma_act_bounds`);
  **determinism** by recovering the flat index from `(q,a)` via pure div/mod (stride 16 > max offset
  15) — fully decoupled from the gadget table via `lemma_gen_key`.
- **B5.4/B5.5 (`tm_sim.rs`)**: `tm_reaches` (∃fuel run, transitive via run-split) + `lemma_quint_at`
  (extract the quintuple at flat index `pc·48+off·3+sym`) + four per-instruction sims + the unified
  `lemma_sim_step`. **B6 entry points**: chain `lemma_sim_step` along the 2-counter run with
  `lemma_tm_reaches_trans`; then prove `tm_reaches(two_counter_config(0,0,entry(len)), tm_origin())`
  (cleanup correctness, the dec-loops + blank-sep) and convert via
  `tm_run_lemmas::lemma_tm_run_reaches_halts_at` (origin is terminal: `lemma_origin_tm_terminal`).
  Init config: `config_encode` (G2-F) picks `two_counter_config(c1_in, 0, entry(0))`.
Lessons banked for the next builder:
- `tm_run(.,1)==X` unfolds need an explicit `assert(tm_run(.,0)==X)` hint right before (Z3 is
  context-sensitive — adding/removing asserts elsewhere can flip these; keep the hints).
- Build next configs as `let c = apply_quint(tm.quints[i], prev, m);` then assert its *fields*; do NOT
  assert `tm_step(prev)==Some(handbuilt_struct)` (Verus won't match a hand-built struct to `apply_quint`).
- Recursive spec fns (`pile_ones`, `repunit_m`) need explicit one-step unfold asserts (`pile_ones(v,1)==
  pile_ones(v,0)*m+1`, etc.); they don't auto-fold in comparisons.
- `(c-1)+1 == c` substitutions inside `repunit_m(...)`/fuel args need explicit bridge asserts.
- Per-module check: `./check.sh --verify-module <name>` (NOT the MCP per-module path — it bypasses the
  Lean toolchain). A transient "could not find module" / "Failed to spawn lake" = a concurrent verus run;
  serialize and re-run. Baseline full-crate check carries 20 pre-existing group-theory errors (the `/20`).
