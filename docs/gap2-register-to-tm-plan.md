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
- **B5 per-instruction simulation** : assemble Inc/DecJump quintuple blocks (relocated like
  `embed_instructions`), prove one 2-counter step ↔ one gadget run; thread `tm_wf` determinism.
- **B6 run simulation + cleanup** : induct over the 2-counter run; on halt, the cleanup phase
  (`dec` both to 0, blank the separator, state→0) reaches `tm_origin()`. Gives
  `rm2_halts(R2,in) ⟺ ∃fuel. tm_halts_at(rm_to_tm(R2), C(in), origin, fuel)`.

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

**Status 2026-06-26:** design locked. **DONE & verified, all committed, purely additive (no edits to
existing modules):** B0 `tm_run_lemmas.rs` (run-split/halts-at bridges), B1 `tm_two_counter.rs` (layout +
repunit + wf), gadget infra + B2 `tm_gadget.rs` (`lemma_tm_step_picks` + bounded peek), B3 `tm_walk.rs`
(both walk loops) + `tm_inc.rs` (`lemma_inc`, the full inc walk gadget). **NEXT = B4 dec gadget** (design
above), then B5 (per-instruction Inc/DecJump quintuple blocks + one-RM-step↔one-gadget-run), B6 (run sim
+ cleanup-to-origin), L1 (k→2 Gödel, the one Euclid lemma), L0 (search_rm dovetailer), G2-F (wire
`config_encode`/`enc` + discharge `ceer_realizes`). Lessons banked for the next builder:
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
