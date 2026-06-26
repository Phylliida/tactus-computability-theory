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

#### ✅ L1 NUMBER-THEORY FOUNDATION DONE 2026-06-26 (this session, additive, full crate 477/0).

The Euclid obligation is discharged — and **primality is dodged entirely**. Two new modules, both
fully verified, no verifier escape hatches:
- **`src/number_theory.rs` (36/0)** — the reusable coprimality core: `gcd` (Euclid), `ext_gcd`/
  `lemma_bezout` (Bézout, ported from the verified `verus-fixed-point` Z3 `number_theory.rs`), and the
  three derived facts the Gödel proof consumes: `lemma_coprime_mul` (multiplicative, via "multiply one
  Bézout eq by `c`" to dodge the degree-3 product identity Lean's `nonlinear_arith` chokes on),
  `lemma_coprime_pow`, `lemma_coprime_not_divides` (`a≥2` coprime to `x` ⟹ `a∤x`). Plus generic
  divisibility plumbing (`lemma_mod_self`/`lemma_divides_mul`/`lemma_divides_trans`).
- **`src/godel.rs` (21/0)** — the **Sylvester/Euclid pairwise-coprime base**
  `base(0)=2, base(j)=1+∏_{i<j}base(i)`, the encoding `godel(regs)=∏ base(j)^{regs[j]}`, the headline
  **`lemma_godel_div_iff`**: for `i<regs.len()`, `base(i) | godel(regs) ⟺ regs[i] ≥ 1` (the `DecJump`
  zero-test arithmetic), AND the register-op value arithmetic **`lemma_godel_inc`** (`Inc(rᵢ)` ⟺
  `godel ×= base(i)`) / **`lemma_godel_dec`** (`godel = base(i)·godel(rᵢ−1)` for `rᵢ≥1`, the divide).
  The base is pairwise coprime because `base(j) ≡ 1 (mod base(i))` for `i<j` (`base(i) | ∏_{i<j}base(i)`),
  so coprimality is a one-liner — NO `nth_prime`/primality/injectivity. The inc/dec lemmas are the
  abstract-value facts the multiply/divide gadget proofs will consume, **independent of the machine
  blocker below** (they stand whatever R-ii/R-iii resolves to).

Lean-backend lessons banked: `nonlinear_arith` proves ring identities up to ~degree-2 substitution (the
ported `lemma_divides_linear_combination` works) but NOT a raw degree-3 product identity — decompose;
`(x*y) as int == (x as int)*(y as int)` needs a PLAIN assert (not inside `by(nonlinear_arith)`, which
loses the cast); `vstd::arithmetic::div_mod` (`lemma_fundamental_div_mod{,_converse}`, `lemma_small_mod`)
all work; `lemma_fundamental_div_mod_converse` wants `x == q*d + r` (q·d order, commute if needed).

#### ⚠⚠ L1 MACHINE BLOCKER — the 2-counter unconditional-jump gap (CO-DESIGN GATE, 2026-06-26).

**Before building the multiply/divide gadgets, a foundational obstruction was found + rigorously
confirmed (independently + companion port 8051):** `machine.rs`'s instruction set is
`Inc{r}` (control falls to `pc+1`, NO goto field) / `DecJump{r,target}` / `Halt`. The ONLY backward
control transfer is `DecJump(r,L)`, which **decrements `r`** on the `r>0` branch. So an unconditional
`goto L` is realizable ONLY as `DecJump(z,L)` with `z` **guaranteed 0** at that point. **Counting
argument:** any loop running `T` times takes its back-edge `T` times; if that back-edge is `DecJump(z,L)`
it needs `z≡0` (else it decrements live data / exits forward). A multiply/divide loop (and even a plain
`move C1→C2`) has back-edges where **both** `C1` and `C2` are generally nonzero — so neither can be the
zero register. **Hence `{Inc→+1, DecJump}` with exactly 2 registers cannot implement
move/multiply/divide; every nontrivial loop needs a 3rd always-zero scratch (2 data + 1 goto-register).**
This is exactly why the existing `copy_instrs`/`triple_dist_instrs` infra uses a dedicated zero scratch
(reg 3). The classical "2-counter machines are universal" result uses Minsky's RICHER set
(`INC(r,goto)`, `JZDEC(r,goto0,goto1)` with explicit successors) where gotos are free — strictly
stronger than `machine.rs`.

**Why this is a real gate (not a free fix):** the whole downstream pipeline `RM(2) → 2-block TM → modular
machine` is **intrinsically 2-coordinate** — the Aanderaa–Cohen modular machine operates on a *pair*
`(α,β)`/`(u,v)` and has exactly two tape blocks. So the companion's first instinct (add a **3rd tape
block** for the goto-register) **breaks the modular target** (`tm_to_modmachine`/`lemma_tm_h0_iff`,
frozen + verified, assume 2 coordinates). The goto-register carries no *data*, only *control* — and
control is the TM **state**, not a tape coordinate. So the dimensionally-honest fix keeps data
2-dimensional and enriches control flow. Candidate resolutions (Danielle's call — touches frozen verified
`rm_to_tm` + `machine.rs`):
  - **(R-ii) Add an unconditional `Jump{target}` to `Instruction`** + one trivial TM state-jump
    quintuple-window in `tm_assemble.rs`. Clean semantics, no extra block/coordinate; cost = the enum
    variant ripples through every `match` on `Instruction` (`step`/`machine_wf`/`lemma_step_preserves_*`,
    `embed_instructions`, all `tm_*` dispatch). Mechanical but wide.
  - **(R-iii) Zero-register convention:** `rm_to_tm` accepts `num_regs=3` but treats reg 2 (provably
    never `Inc`'d) as a pure goto-register compiled to a TM state-jump with NO tape block (TM stays
    2-block, modular stays 2-coord). No enum change; cost = `rm_to_tm`'s contract must carry the
    "reg 2 never incremented / always 0" invariant, slightly breaking RM↔TM state uniformity.
  - **(R-i) [REJECTED] 3-block tape** — breaks the 2-coordinate modular machine downstream.

**Recommendation to surface: R-ii or R-iii** (both keep the modular pipeline 2-coordinate). NOT taken
solo — modifying the frozen, verified `rm_to_tm`/`machine.rs` is a co-design decision. **The L1
number-theory foundation above is independent of this choice and stands regardless.**

#### ✅ TEXTBOOK RESOLUTION 2026-06-26 — Shepherdson–Sturgis confirms R-ii (Danielle's paper).

Danielle supplied **`ComputabilityOfRecursiveFunctions.pdf`** (Shepherdson & Sturgis, *J. ACM* 1963 —
the canonical register-machine / URM source). It settles the L1 instruction-set question authoritatively,
and the standing guidance ("follow the textbook, don't reinvent") points squarely at it. Key facts:

- **The URM's basic set (§2)** is the *separated* one: `P(n)` (increment), `D(n)` (decrement, used only
  on a non-empty register), `O(n)` (clear), `C(m,n)` (copy), **`J[E1]` (unconditional jump)**, and
  **`J(m)[E1]` (jump if register m is empty — a *non-destructive* test, no decrement).** This is exactly
  the set our `machine.rs` is *missing* the jump primitives from: ours fuses test+decrement into
  `DecJump`-on-zero and has no unconditional jump.
- **Theorem 10.2 (Minsky, via S–S):** with operations `a=P(n)`, `b=D(n)`, `f=J(n)[test]` and **exactly
  two registers**, the machine computes *all* partial recursive functions (Gödel `∏ pᵢ^{xᵢ}` coding). So
  2 registers genuinely suffice — but *only* with the separated test-jump + a derivable unconditional `J`.
- **The unconditional jump is derivable** from `{P,D,J(n)-test}` via a *compensated subroutine* (S–S §10
  proof of the Lemma): `J[m] = P(1); J(1)[m+1]` with line `m` recompiled to `P(1); D(1); old-line-m`. It
  temporarily perturbs and restores one register. **This trick does NOT translate to our fused
  `DecJump`-on-zero** (opposite polarity *and* fused decrement: after `Inc(1)`, `DecJump(1,L)` decrements
  and falls through — never an unconditional jump). With only 2 *live* registers and no guaranteed-zero
  register to save into, our fused primitive provably cannot realize the back-edge. **So the counting
  argument in the blocker above is correct, and the textbook's own resolution is to have the separated
  test + an (un)conditional jump available.**

**Conclusion (still Danielle's call to execute):** the faithful fix is **R-ii — add an unconditional
`Jump{target}` to `Instruction`** (matching S–S's `J[E1]`). That is precisely the missing primitive: the
loop back-edges in the k→2 multiply/divide gadgets become `Jump{loop_top}` (no register consumed), while
`DecJump` continues to serve as the fused test-and-decrement *guard* (= S–S's `J(n)[body]; D(n)` in one).
With `Jump` available, Theorem 10.2's 2-register multiply/divide port directly, consuming the already-built
`lemma_godel_div_iff`. Cost is the enum-variant ripple through every `match Instruction` (`step`,
`machine_wf`, `embed_instructions`, the `tm_*` dispatch + one trivial TM state-jump quintuple-window) — wide
but mechanical, and it keeps data 2-dimensional so the frozen `tm_to_modmachine`/`lemma_tm_h0_iff` stay
2-coordinate. R-iii (zero-register convention) remains the lower-enum-disruption alternative but still
touches `rm_to_tm`'s contract. **Either way `rm_to_tm`/`machine.rs` get un-frozen — that is the gate.**
Until it's taken, **L0 (`search_rm`) is the unblocked path** (it builds an `RM(k)` with free scratch, so it
never needs the 2-register back-edge) — see `gap2-l0-search-rm-plan.md`.

#### ✅ R-ii DONE 2026-06-26 — `Jump{target}` added, full crate 554/0 (commit `de7796f`).

Danielle took the co-design call (port 8051): **R-ii GO**, `target <= len` in `machine_wf`. `Jump`'s TM
gadget `jump_act` is a bit-for-bit `halt_act` clone routing `entry(pc)→entry(target)` (reuses
`lemma_bounce_left`); `lemma_sim_jump` mirrors `lemma_sim_halt`. Embed/instrument map `Jump→DecJump{scratch}`
to keep relocated machines Jump-free. Parser quirk: struct literal `Instruction::Jump{target}` in `requires`
→ `mk_jump(target)` spec constructor. `machine.rs`/`rm_to_tm` un-frozen + re-verified, no escape hatches.

#### ✅ k→2 GADGET DESIGN LOCKED 2026-06-26 — textbook-faithful (S–S Lemma before Thm 10.2).

The S–S Lemma (lines 992–1013 of the paper) gives multiply / divide / **non-destructive** divisibility-test
using `N+1` registers from the basic set `{P (=Inc), D (=dec), J(n) (test), J (uncond)}`. For 2-counter (10.2)
`N=1`: **`C1` = the Gödel register `∏ base(i)^{r_i}`** (Sylvester base from `godel.rs`), **`C2`** = the single
`+1` scratch. **All derived ops come from our `{Inc, DecJump, Jump}`** — R-ii's `Jump` is exactly the missing
primitive (S–S derive `J` uncond from `{P,D,test}` via the compensated subroutine; our *fused* `DecJump`
couldn't, so we added `J` directly).

**The restoration concern (Danielle) is resolved by the textbook's FACTORING, not by an undo:** S–S do NOT use
a fused test-and-divide (which builds the quotient in `(n)` and must undo it on the not-divisible path).
Instead:
- **`Div?((n),k)[E1]` — non-destructive divisibility test.** Move `(n)→(n+1)`, then walk `(n+1)` down while
  **rebuilding `(n)` via `Inc` per decrement**, in groups of `k`. The *first* decrement of a group hitting
  zero ⟹ divisible (exit `E1`); a *mid-group* zero ⟹ not divisible (exit 0). On **both** exits `(n)=N` is
  restored. The verdict is carried purely in WHICH exit — no quotient is left in `(n)`, so nothing to undo.
- **`(n)÷k` — separate destructive divide**, invoked ONLY on the divisible branch.

So `DecJump(r_i, target)` translates to `[Div?(C1,base(i))[do_div]; Jump(target); do_div: C1÷=base(i);
continue]` — on the not-divisible (`r_i=0`) branch `C1` is already intact and `Jump(target)` preserves it.
`Inc(r_i)` translates to `C1 × base(i)`. `Halt→Halt`, `Jump→Jump`.

**Gadgets from `{Inc, DecJump, Jump}` (all loops use `Jump` for the unconditional back-edge):**
- **move `(n)→(n+1)`**: `loop: DecJump(n, done); Inc(n+1); Jump(loop); done:` (consumes `n` into `n+1`).
- **multiply `(n)×k`**: `move (n)→(n+1)`; `loop2: DecJump(n+1, done2); Inc(n)×k; Jump(loop2); done2:`.
- **divide `(n)÷k`** (divisible only): `move (n)→(n+1)`; `loop: [DecJump(n+1, done)]×k; Inc(n); Jump(loop)`.
- **`Div?((n),k)[E1]`** (non-destructive): `move (n)→(n+1)`; `tloop: DecJump(n+1, E1); Inc(n);
  [DecJump(n+1, not_div); Inc(n)]×(k-1); Jump(tloop)`. (`E1` = divisible; `not_div` = exit 0.)

**Gadget lemmas are PARAMETRIC in `k`** (induction over the counter / over `k`), instantiated at `k=base(i)` —
so `base(i)`'s (doubly-exponential, Sylvester) *magnitude* never enters the proofs; only `k` as a symbol +
the `godel.rs` value lemmas (`lemma_godel_inc/dec/div_iff`). Brick order: **M1** move + multiply + lemmas →
**M2** divide + non-destructive `Div?` + lemmas → **M3** per-instruction block translation → **M4** assemble
`rm_k_to_rm2` + `machine_wf` → **M5** one-step sim (`C1 = godel(regs)` invariant, consumes godel lemmas) →
**M6** run-sim + halts-iff (`halts(rm_k, input) ⟺ halts(rm2, godel(initial_config))`). Then **G2-F** wires
`config_encode` + discharges `ceer_realizes`. The induction follows `search_rm_arith`'s copy/double_dist
loop-lemma style (decreasing-fuel inner loop, recurrence per group).

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
`tm_run_sim.rs` (run induction + the halting iff `lemma_rm_tm_origin_iff`).

**Status update 2026-06-26 (this session):** **L1 number-theory foundation DONE** (`number_theory.rs`
36/0 + `godel.rs` 15/0, full crate 477/0 — `lemma_godel_div_iff`, Sylvester-coprime base, no primality;
see the L1 §). **A blocker was found for the L1 *machine*:** the `{Inc→+1, DecJump}` 2-register
instruction set cannot loop without a 3rd always-zero goto-register, but the pipeline is intrinsically
2-coordinate — see the **L1 MACHINE BLOCKER** § above (co-design gate, Danielle's call: R-ii add `Jump`,
or R-iii zero-register convention; both keep the modular target 2-coordinate). **NEXT =**
(1) resolve the L1 machine blocker with Danielle (R-ii / R-iii), then build the multiply/divide gadgets
consuming `lemma_godel_div_iff`; OR (2) **L0 (search_rm dovetailer) is UNBLOCKED** — it builds an
`RM(k)` with as many scratch registers as it wants (reuses the `multi_output`/`embed_instructions` infra),
so it does not hit the 2-counter gate; its own subtlety is the fuel-instrumented *bounded* simulation
(plain embed-and-run hangs on non-halting enumerator stages). Then G2-F (wire `config_encode`/`enc` +
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
