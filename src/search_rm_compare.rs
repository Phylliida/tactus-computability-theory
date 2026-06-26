//  GAP-2 / L0 brick B-L0.2b — register-machine comparison gadget for the dovetail driver.
//
//  `eq_test_instrs(a, b, zero, neq, sp)` destructively compares registers `a` and `b` (draining both)
//  and lands at `sp + 5` (the EQUAL exit, fall-through) iff `(a) == (b)`, else jumps to `neq`. Used to
//  test `pair(reg1,reg2) == input` in the HALTED comparison (re-pairing avoids unpairing).
//
//  Layout (`sp = start_pc`):
//    sp+0  DecJump{a,    sp+3}    a==0 ⇒ check-b; else a--, fall
//    sp+1  DecJump{b,    neq}     b==0 (a was >0) ⇒ UNEQUAL; else b--, fall
//    sp+2  DecJump{zero, sp}      loop
//    sp+3  DecJump{b,    sp+5}    a==0: b==0 ⇒ EQUAL (sp+5); else b--, fall
//    sp+4  DecJump{zero, neq}     (b>0) ⇒ UNEQUAL
//  EQUAL exit = sp+5,  UNEQUAL exit = neq.
//
//  See docs/gap2-l0-search-rm-plan.md (B-L0.2b).

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::mk_dj;
use crate::search_rm_arith::{lemma_run_add, lemma_run_preserves_len};

verus! {

proof fn lemma_run_unfold_step(m: RegisterMachine, c: Configuration, fuel: nat)
    requires
        !is_halted(m, c),
        fuel > 0,
    ensures
        step(m, c) is Some,
        run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

pub open spec fn eq_test_instrs(a: nat, b: nat, zero: nat, neq: nat, sp: nat) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: a,    target: sp + 3 },
        Instruction::DecJump { register: b,    target: neq },
        Instruction::DecJump { register: zero, target: sp },
        Instruction::DecJump { register: b,    target: sp + 5 },
        Instruction::DecJump { register: zero, target: neq },
    ]
}

///  Side-condition bundle: the 5 instructions are laid out at `sp`, registers distinct + in bounds,
///  and `neq` is outside the gadget body (so reaching it is a genuine UNEQUAL verdict).
pub open spec fn eq_test_frame(m: RegisterMachine, a: nat, b: nat, zero: nat, neq: nat, sp: nat) -> bool {
    &&& sp + 5 <= m.instructions.len()
    &&& m.instructions[sp as int]       == mk_dj(a, sp + 3)
    &&& m.instructions[(sp + 1) as int] == mk_dj(b, neq)
    &&& m.instructions[(sp + 2) as int] == mk_dj(zero, sp)
    &&& m.instructions[(sp + 3) as int] == mk_dj(b, sp + 5)
    &&& m.instructions[(sp + 4) as int] == mk_dj(zero, neq)
    &&& a < m.num_regs && b < m.num_regs && zero < m.num_regs
    &&& a != b && a != zero && b != zero
    &&& neq != sp + 5
    &&& (neq < sp || neq >= sp + 5)
}

///  The exit pc determined by the comparison: `sp + 5` (EQUAL) iff `va == vb`, else `neq`.
pub open spec fn eq_exit_pc(va: nat, vb: nat, neq: nat, sp: nat) -> nat {
    if va == vb { sp + 5 } else { neq }
}

///  `eq_test` reaches `eq_exit_pc(va,vb,neq,sp)`: the EQUAL exit iff `(a)==(b)`, else `neq`; `zero`
///  and all registers other than `a`,`b` are preserved.
#[verifier::rlimit(4000)]
pub proof fn lemma_eq_test_loop(
    m: RegisterMachine, c: Configuration,
    a: nat, b: nat, zero: nat, neq: nat, sp: nat, va: nat, vb: nat,
)
    requires
        eq_test_frame(m, a, b, zero, neq, sp),
        c.pc == sp,
        c.registers.len() == m.num_regs,
        c.registers[a as int] == va,
        c.registers[b as int] == vb,
        c.registers[zero as int] == 0,
    ensures
        exists|g: nat|
            #[trigger] run(m, c, g).pc == eq_exit_pc(va, vb, neq, sp)
            && run(m, c, g).registers[zero as int] == 0
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int && r != a as int && r != b as int
                    ==> #[trigger] run(m, c, g).registers[r] == c.registers[r]),
    decreases va,
{
    if va == 0 {
        //  sp+0: DecJump{a, sp+3}, a==0 ⇒ jump to sp+3 (registers unchanged)
        assert(m.instructions[c.pc as int] == mk_dj(a, sp + 3));
        assert(c.registers[a as int] == 0);
        assert(!is_halted(m, c));
        let c1 = step(m, c).unwrap();
        assert(c1.pc == sp + 3 && c1.registers == c.registers);
        lemma_run_unfold_step(m, c, 1);
        assert(run(m, c, 1) == c1);
        //  sp+3: DecJump{b, sp+5}
        assert(m.instructions[c1.pc as int] == mk_dj(b, sp + 5));
        if vb == 0 {
            //  b==0 ⇒ jump to sp+5 (EQUAL), registers unchanged
            let c2 = step(m, c1).unwrap();
            assert(c2.pc == sp + 5 && c2.registers == c1.registers);
            lemma_run_add(m, c, 1, 1);
            lemma_run_unfold_step(m, c1, 1);
            assert(run(m, c, 2) == c2);
            assert(eq_exit_pc(va, vb, neq, sp) == sp + 5);
            assert(run(m, c, 2).pc == eq_exit_pc(va, vb, neq, sp));
        } else {
            //  b>0 ⇒ b--, fall to sp+4; sp+4: DecJump{zero, neq} ⇒ jump to neq (UNEQUAL)
            let c2 = step(m, c1).unwrap();
            assert(c2.pc == sp + 4);
            assert(m.instructions[c2.pc as int] == mk_dj(zero, neq));
            assert(c2.registers[zero as int] == 0) by { assert(zero != b); }
            let c3 = step(m, c2).unwrap();
            assert(c3.pc == neq && c3.registers == c2.registers);
            lemma_run_unfold_step(m, c1, 2);
            lemma_run_unfold_step(m, c2, 1);
            assert(run(m, c1, 2) == c3);
            lemma_run_add(m, c, 1, 2);
            assert(run(m, c, 3) == c3);
            assert(eq_exit_pc(va, vb, neq, sp) == neq);
            //  frame: c3.registers == c2.registers == c1.registers.update(b,..) == c.update(b,..)
            assert forall|r: int| 0 <= r < m.num_regs as int && r != a as int && r != b as int
            implies #[trigger] run(m, c, 3).registers[r] == c.registers[r] by { }
        }
    } else {
        //  va > 0: sp+0 DecJump{a, sp+3}, a>0 ⇒ a--, fall to sp+1
        assert(m.instructions[c.pc as int] == mk_dj(a, sp + 3));
        assert(!is_halted(m, c));
        let c1 = step(m, c).unwrap();
        assert(c1.pc == sp + 1);
        assert(c1.registers == c.registers.update(a as int, (va - 1) as nat));
        //  sp+1: DecJump{b, neq}
        assert(m.instructions[c1.pc as int] == mk_dj(b, neq));
        assert(c1.registers[b as int] == vb) by { assert(b != a); }
        if vb == 0 {
            //  b==0 ⇒ jump to neq (UNEQUAL), since va>0=vb
            let c2 = step(m, c1).unwrap();
            assert(c2.pc == neq && c2.registers == c1.registers);
            lemma_run_unfold_step(m, c, 2);
            lemma_run_unfold_step(m, c1, 1);
            assert(run(m, c, 2) == c2);
            assert(eq_exit_pc(va, vb, neq, sp) == neq) by { assert(va != vb); }
            assert forall|r: int| 0 <= r < m.num_regs as int && r != a as int && r != b as int
            implies #[trigger] run(m, c, 2).registers[r] == c.registers[r] by { }
        } else {
            //  b>0 ⇒ b--, fall to sp+2; sp+2: DecJump{zero, sp} ⇒ loop back to sp
            let c2 = step(m, c1).unwrap();
            assert(c2.pc == sp + 2);
            assert(c2.registers == c1.registers.update(b as int, (vb - 1) as nat));
            assert(m.instructions[c2.pc as int] == mk_dj(zero, sp));
            assert(c2.registers[zero as int] == 0) by { assert(zero != a && zero != b); }
            let c3 = step(m, c2).unwrap();
            assert(c3.pc == sp && c3.registers == c2.registers);
            assert(c3.registers[a as int] == (va - 1) as nat) by { assert(a != b); }
            assert(c3.registers[b as int] == (vb - 1) as nat);
            assert(c3.registers[zero as int] == 0);
            assert(c3.registers.len() == m.num_regs);
            //  run(m,c,3) == c3
            lemma_run_unfold_step(m, c, 3);
            lemma_run_unfold_step(m, c1, 2);
            lemma_run_unfold_step(m, c2, 1);
            assert(run(m, c, 3) == c3);

            //  recurse from c3 (va-1, vb-1)
            lemma_eq_test_loop(m, c3, a, b, zero, neq, sp, (va - 1) as nat, (vb - 1) as nat);
            let g_inner = choose|g: nat|
                run(m, c3, g).pc == eq_exit_pc((va - 1) as nat, (vb - 1) as nat, neq, sp)
                && run(m, c3, g).registers[zero as int] == 0
                && run(m, c3, g).registers.len() == m.num_regs
                && (forall|r: int| 0 <= r < m.num_regs as int && r != a as int && r != b as int
                        ==> #[trigger] run(m, c3, g).registers[r] == c3.registers[r]);
            lemma_run_add(m, c, 3, g_inner);
            let g: nat = (3 + g_inner) as nat;
            assert(run(m, c, g) == run(m, c3, g_inner));
            assert(eq_exit_pc((va - 1) as nat, (vb - 1) as nat, neq, sp) == eq_exit_pc(va, vb, neq, sp)) by {
                assert((va - 1 == vb - 1) == (va == vb));
            }
            //  frame: out-of-{a,b} regs of run(m,c,g) == c3's == c's
            assert forall|r: int| 0 <= r < m.num_regs as int && r != a as int && r != b as int
            implies #[trigger] run(m, c, g).registers[r] == c.registers[r]
            by {
                assert(run(m, c3, g_inner).registers[r] == c3.registers[r]);
                assert(c3.registers[r] == c.registers[r]);
            }
        }
    }
}

} //  verus!
