use vstd::prelude::*;
use crate::pairing::*;
use crate::machine::*;
use crate::conditional_halt::*;
use crate::multi_output_machine::*;

verus! {

//  ============================================================
//  CompSpec: Primitive Recursive Computation Specifications
//  ============================================================
//
//  A CompSpec is a formal witness that a function nat → nat is
//  primitive recursive (hence register-machine computable).
//
//  All functions are nat → nat. Multiple arguments are encoded
//  via Cantor pairing: f(x, y) becomes f(pair(x, y)).

///  A specification of a primitive recursive computation.
pub enum CompSpec {
    ///  Constant: input → value
    Const { value: nat },
    ///  Identity: input → input
    Id,
    ///  Successor: input → input + 1
    Succ,
    ///  Predecessor (saturating): input → max(input - 1, 0)
    Pred,
    ///  Addition: input → eval(left) + eval(right)
    Add { left: Box<CompSpec>, right: Box<CompSpec> },
    ///  Multiplication: input → eval(left) * eval(right)
    Mul { left: Box<CompSpec>, right: Box<CompSpec> },
    ///  Composition: input → eval(outer, eval(inner, input))
    Comp { outer: Box<CompSpec>, inner: Box<CompSpec> },
    ///  Cantor pairing: input → pair(eval(left), eval(right))
    CantorPair { left: Box<CompSpec>, right: Box<CompSpec> },
    ///  First projection: input → unpair1(eval(inner))
    CantorFst { inner: Box<CompSpec> },
    ///  Second projection: input → unpair2(eval(inner))
    CantorSnd { inner: Box<CompSpec> },
    ///  Conditional: input → if eval(cond) == 0 then eval(then_br) else eval(else_br)
    IfZero { cond: Box<CompSpec>, then_br: Box<CompSpec>, else_br: Box<CompSpec> },
    ///  Equality: input → if eval(left) == eval(right) then 1 else 0
    Eq { left: Box<CompSpec>, right: Box<CompSpec> },
    ///  Less-than: input → if eval(left) < eval(right) then 1 else 0
    Lt { left: Box<CompSpec>, right: Box<CompSpec> },
    ///  Bounded primitive recursion:
    ///    count = eval(count_fn, input)
    ///    acc_0 = eval(base, input)
    ///    acc_{i+1} = eval(step, pair(i, pair(acc_i, input)))
    ///    result = acc_count
    BoundedRec { count_fn: Box<CompSpec>, base: Box<CompSpec>, step: Box<CompSpec> },
}

///  Iterate a step function `count` times.
///    iterate(f, 0, acc, input) = acc
///    iterate(f, n+1, acc, input) = iterate(f, n, f(pair(n, pair(acc, input))), input)
pub open spec fn iterate(
    step_fn: spec_fn(nat) -> nat,
    count: nat,
    acc: nat,
    input: nat,
) -> nat
    decreases count,
{
    if count == 0 {
        acc
    } else {
        iterate(
            step_fn,
            (count - 1) as nat,
            step_fn(pair((count - 1) as nat, pair(acc, input))),
            input,
        )
    }
}

///  Evaluate a CompSpec on an input.
pub open spec fn eval_comp(c: CompSpec, input: nat) -> nat
    decreases c, 0nat,
{
    match c {
        CompSpec::Const { value } => value,
        CompSpec::Id => input,
        CompSpec::Succ => input + 1,
        CompSpec::Pred => if input > 0 { (input - 1) as nat } else { 0 },
        CompSpec::Add { left, right } =>
            eval_comp(*left, input) + eval_comp(*right, input),
        CompSpec::Mul { left, right } =>
            eval_comp(*left, input) * eval_comp(*right, input),
        CompSpec::Comp { outer, inner } =>
            eval_comp(*outer, eval_comp(*inner, input)),
        CompSpec::CantorPair { left, right } =>
            pair(eval_comp(*left, input), eval_comp(*right, input)),
        CompSpec::CantorFst { inner } =>
            unpair1(eval_comp(*inner, input)),
        CompSpec::CantorSnd { inner } =>
            unpair2(eval_comp(*inner, input)),
        CompSpec::IfZero { cond, then_br, else_br } =>
            if eval_comp(*cond, input) == 0 {
                eval_comp(*then_br, input)
            } else {
                eval_comp(*else_br, input)
            },
        CompSpec::Eq { left, right } =>
            if eval_comp(*left, input) == eval_comp(*right, input) { 1nat } else { 0nat },
        CompSpec::Lt { left, right } =>
            if eval_comp(*left, input) < eval_comp(*right, input) { 1nat } else { 0nat },
        CompSpec::BoundedRec { count_fn, base, step } => {
            compspec_iterate(*step, eval_comp(*count_fn, input), eval_comp(*base, input), input)
        },
    }
}

///  Closure-free bounded recursion: applies eval_comp(step, ...) count times.
///  Mutually recursive with eval_comp — step is a proper subterm of the original
///  BoundedRec, so (step, count) < (BoundedRec{..step..}, 0) lexicographically.
pub open spec fn compspec_iterate(
    step: CompSpec, count: nat, acc: nat, input: nat,
) -> nat
    decreases step, count,
{
    if count == 0 {
        acc
    } else {
        compspec_iterate(
            step,
            (count - 1) as nat,
            eval_comp(step, pair((count - 1) as nat, pair(acc, input))),
            input,
        )
    }
}

///  One-step unfolding of compspec_iterate.
pub proof fn lemma_compspec_iterate_unfold(
    step: CompSpec, count: nat, acc: nat, input: nat,
)
    requires
        count > 0,
    ensures
        compspec_iterate(step, count, acc, input)
            == compspec_iterate(step, (count - 1) as nat,
                eval_comp(step, pair((count - 1) as nat, pair(acc, input))),
                input),
{
}

///  Iterate is extensional: pointwise-equal step functions give equal results.
pub proof fn lemma_iterate_ext(
    f1: spec_fn(nat) -> nat,
    f2: spec_fn(nat) -> nat,
    count: nat, acc: nat, input: nat,
)
    requires
        forall|x: nat| #[trigger] f1(x) == f2(x),
    ensures
        iterate(f1, count, acc, input) == iterate(f2, count, acc, input),
    decreases count,
{
    if count > 0 {
        let arg = pair((count - 1) as nat, pair(acc, input));
        assert(f1(arg) == f2(arg));
        lemma_iterate_ext(f1, f2, (count - 1) as nat, f1(arg), input);
    }
}

///  Unfolding lemma: eval_comp(BoundedRec{...}) == compspec_iterate(step, n, b, input).
///  Trivially true now that eval_comp uses compspec_iterate directly.
pub proof fn lemma_eval_bounded_rec(
    count_fn: CompSpec, base: CompSpec, step: CompSpec, input: nat,
)
    ensures
        eval_comp(
            CompSpec::BoundedRec {
                count_fn: Box::new(count_fn),
                base: Box::new(base),
                step: Box::new(step),
            },
            input,
        ) == compspec_iterate(
            step,
            eval_comp(count_fn, input),
            eval_comp(base, input),
            input,
        ),
{
}

//  ============================================================
//  Core Church-Turing Axioms
//  ============================================================

///  Core axiom 1: Every CompSpec defines a total computable function.
///
///  There exists a register machine that always halts and whose output
///  (register 0) equals eval_comp(c, input) for every input.
///
///  Justification: each CompSpec operation (constant, successor, predecessor,
///  addition, multiplication, composition, pairing, projection, conditional,
///  comparison, bounded recursion) is primitive recursive. Every primitive
///  recursive function is register-machine computable — this is a standard
///  theorem in computability theory.
#[verifier::external_body]
pub proof fn axiom_comp_spec_total(c: CompSpec)
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) &&
            (forall|s: nat| halts(rm, s)) &&
            (forall|s: nat| output(rm, s) == eval_comp(c, s)),
{
}

//  ============================================================
//  Sub-axioms for axiom_compose_partial_machine
//  ============================================================

///  Sub-axiom A: Three total register machines can be merged into
///  a single total machine with >= 3 registers that computes all
///  three functions simultaneously.
///
///  Given total machines computing f_h, f_1, f_2, there exists a
///  machine rm with num_regs >= 3 that:
///    - halts on every input
///    - on halting, reg[0] = f_h(s), reg[1] = f_1(s), reg[2] = f_2(s)
///
///  Justification: standard register machine composition. The combined
///  machine runs each sub-machine in sequence using disjoint register
///  banks, copying each result to the designated output register.
///  Specifically:
///    1. Run rm_halts (copies input, executes, stores reg[0] result to reg_h)
///    2. Run rm_out1 (copies input, executes, stores reg[0] result to reg 1)
///    3. Run rm_out2 (copies input, executes, stores reg[0] result to reg 2)
///    4. Copy reg_h to reg 0; halt
///  Register copying (dec-source/inc-target loops) and input restoration
///  are standard register machine primitives. Since all sub-machines are
///  total, the combined machine always halts.
pub proof fn axiom_total_multi_output_machine(
    rm_halts: RegisterMachine,
    rm_out1: RegisterMachine,
    rm_out2: RegisterMachine,
    f_h: spec_fn(nat) -> nat,
    f_1: spec_fn(nat) -> nat,
    f_2: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_halts) &&
        (forall|s: nat| halts(rm_halts, s)) &&
        (forall|s: nat| output(rm_halts, s) == f_h(s)),
        machine_wf(rm_out1) &&
        (forall|s: nat| halts(rm_out1, s)) &&
        (forall|s: nat| output(rm_out1, s) == f_1(s)),
        machine_wf(rm_out2) &&
        (forall|s: nat| halts(rm_out2, s)) &&
        (forall|s: nat| output(rm_out2, s) == f_2(s)),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s)) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[0] == f_h(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[1] == f_1(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == f_2(s)
                )),
{
    lemma_total_multi_output_machine(rm_halts, rm_out1, rm_out2, f_h, f_1, f_2);
}

///  Sub-axiom B: A total multi-output machine can be converted into
///  a partial machine that halts iff register 0 would be nonzero.
///
///  Given a total machine rm_total with num_regs >= 3 that on halting
///  places f_h(s) in reg[0], f_1(s) in reg[1], f_2(s) in reg[2],
///  there exists a machine rm that:
///    - halts on input s iff f_h(s) != 0
///    - when halting, reg[1] = f_1(s), reg[2] = f_2(s)
///
///  Justification: the combined machine first runs rm_total to
///  completion (always halts since rm_total is total), then tests
///  reg[0]: if nonzero, halts; if zero, enters an infinite loop
///  (e.g., `Inc reg_scratch; DecJump reg_scratch self`).
///  The output registers 1 and 2 are not modified by the conditional
///  halt/loop logic, so they retain their values.
pub proof fn axiom_conditional_halt_on_reg0(
    rm_total: RegisterMachine,
    f_h: spec_fn(nat) -> nat,
    f_1: spec_fn(nat) -> nat,
    f_2: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_total) && rm_total.num_regs >= 3 &&
        (forall|s: nat| halts(rm_total, s)) &&
        (forall|s: nat, fuel: nat|
            run_halts(rm_total, initial_config(rm_total, s), fuel) ==> (
                run(rm_total, initial_config(rm_total, s), fuel).registers[0] == f_h(s) &&
                run(rm_total, initial_config(rm_total, s), fuel).registers[1] == f_1(s) &&
                run(rm_total, initial_config(rm_total, s), fuel).registers[2] == f_2(s)
            )),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> f_h(s) != 0) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[1] == f_1(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == f_2(s)
                )),
{
    lemma_conditional_halt_on_reg0(rm_total, f_h, f_1, f_2);
}

///  Core axiom 2: Three total register machines can be composed into a
///  partial machine that conditionally halts.
///
///  Given machines computing halts_fn, out1_fn, out2_fn (all total),
///  there exists a machine that:
///    - halts on input s iff halts_fn(s) != 0
///    - when halting, register 1 = out1_fn(s), register 2 = out2_fn(s)
///
///  Derived from:
///    1. axiom_total_multi_output_machine — merge three total machines
///       into one total machine with results in regs 0, 1, 2
///    2. axiom_conditional_halt_on_reg0 — convert total machine to
///       partial machine that halts iff reg 0 is nonzero
pub proof fn axiom_compose_partial_machine(
    rm_halts: RegisterMachine,
    rm_out1: RegisterMachine,
    rm_out2: RegisterMachine,
    halts_fn: spec_fn(nat) -> nat,
    out1_fn: spec_fn(nat) -> nat,
    out2_fn: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_halts) &&
        (forall|s: nat| halts(rm_halts, s)) &&
        (forall|s: nat| output(rm_halts, s) == halts_fn(s)),
        machine_wf(rm_out1) &&
        (forall|s: nat| halts(rm_out1, s)) &&
        (forall|s: nat| output(rm_out1, s) == out1_fn(s)),
        machine_wf(rm_out2) &&
        (forall|s: nat| halts(rm_out2, s)) &&
        (forall|s: nat| output(rm_out2, s) == out2_fn(s)),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> halts_fn(s) != 0) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[1] == out1_fn(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == out2_fn(s)
                )),
{
    //  Step 1: Merge three total machines into one total multi-output machine
    axiom_total_multi_output_machine(
        rm_halts, rm_out1, rm_out2,
        halts_fn, out1_fn, out2_fn,
    );

    //  Step 2: Choose the witness total multi-output machine
    let rm_total = choose|rm: RegisterMachine|
        machine_wf(rm) && rm.num_regs >= 3 &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat, fuel: nat|
            run_halts(rm, initial_config(rm, s), fuel) ==> (
                run(rm, initial_config(rm, s), fuel).registers[0] == halts_fn(s) &&
                run(rm, initial_config(rm, s), fuel).registers[1] == out1_fn(s) &&
                run(rm, initial_config(rm, s), fuel).registers[2] == out2_fn(s)
            ));

    //  Step 3: Convert to a partial machine that halts iff reg 0 is nonzero
    axiom_conditional_halt_on_reg0(
        rm_total,
        halts_fn, out1_fn, out2_fn,
    );
}

//  ============================================================
//  Derived Church-Turing Theorem
//  ============================================================

///  Every CompSpec-definable partial function has a register machine.
///
///  Previously an axiom (external_body). Now derived from:
///    1. axiom_comp_spec_total (CompSpec → total register machine)
///    2. axiom_compose_partial_machine (compose total machines into partial one)
///
///  A "partial function" is specified by:
///    - halts_check: CompSpec whose output is nonzero iff the machine should halt
///    - output1, output2: CompSpec giving the two output values when halting
pub proof fn axiom_computable_partial_fn(
    halts_check: CompSpec,
    output1: CompSpec,
    output2: CompSpec,
)
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> eval_comp(halts_check, s) != 0) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[1] == eval_comp(output1, s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == eval_comp(output2, s)
                )),
{
    //  Step 1: Get total machines for each CompSpec
    axiom_comp_spec_total(halts_check);
    axiom_comp_spec_total(output1);
    axiom_comp_spec_total(output2);

    //  Step 2: Choose the witness machines
    let rm_h = choose|rm: RegisterMachine|
        machine_wf(rm) &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat| output(rm, s) == eval_comp(halts_check, s));
    let rm_1 = choose|rm: RegisterMachine|
        machine_wf(rm) &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat| output(rm, s) == eval_comp(output1, s));
    let rm_2 = choose|rm: RegisterMachine|
        machine_wf(rm) &&
        (forall|s: nat| halts(rm, s)) &&
        (forall|s: nat| output(rm, s) == eval_comp(output2, s));

    //  Step 3: Compose into a partial machine
    axiom_compose_partial_machine(
        rm_h, rm_1, rm_2,
        |s: nat| eval_comp(halts_check, s),
        |s: nat| eval_comp(output1, s),
        |s: nat| eval_comp(output2, s),
    );
}

} //  verus!
