//  GAP-2 / L0 brick B-L0.2c (pre) — contiguous register-bank clear.
//
//  `clear_bank_instrs(start_reg, count, zero, sp)` lays `count` two-instruction `clear` gadgets back
//  to back, zeroing registers `[start_reg, start_reg + count)`. Used to reset the embedded
//  enumerator's register bank between dovetail iterations (the `instrument` run leaves it dirty).
//  `count` is symbolic (= the enumerator's register count `ne`), so the bank cannot be cleared by a
//  loop over register *addresses* (RM registers are literal-addressed) — it is genuinely `2*ne`
//  unrolled gadgets, and this lemma proves the whole block by induction on `count`.
//
//  See docs/gap2-l0-search-rm-plan.md (B-L0.2c).

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::mk_dj;
use crate::search_rm_arith::lemma_run_add;
use crate::search_rm_compare::lemma_clear_loop;

verus! {

///  `count` back-to-back `clear` gadgets at `sp`: gadget `k` (clearing `start_reg + k`) sits at the
///  even slot `sp + 2k` (`DecJump{start_reg+k, sp+2k+2}`) and odd slot `sp + 2k + 1`
///  (`DecJump{zero, sp+2k}`). Exit at `sp + 2*count`.
pub open spec fn clear_bank_instrs(start_reg: nat, count: nat, zero: nat, sp: nat) -> Seq<Instruction> {
    Seq::new(2 * count, |j: int|
        if j % 2 == 0 {
            Instruction::DecJump { register: (start_reg + j / 2) as nat, target: (sp + j + 2) as nat }
        } else {
            Instruction::DecJump { register: zero, target: (sp + j - 1) as nat }
        }
    )
}

///  Dropping the first gadget: `clear_bank(start, count, sp)[j+2] == clear_bank(start+1, count-1, sp+2)[j]`.
proof fn lemma_clear_bank_shift(start_reg: nat, count: nat, zero: nat, sp: nat)
    requires count > 0,
    ensures
        forall|j: int| 0 <= j < 2 * (count - 1) ==>
            #[trigger] clear_bank_instrs(start_reg, count, zero, sp)[j + 2]
                == clear_bank_instrs((start_reg + 1) as nat, (count - 1) as nat, zero, (sp + 2) as nat)[j],
{
    let a = clear_bank_instrs(start_reg, count, zero, sp);
    let b = clear_bank_instrs((start_reg + 1) as nat, (count - 1) as nat, zero, (sp + 2) as nat);
    assert forall|j: int| 0 <= j < 2 * (count - 1) implies
        #[trigger] a[j + 2] == b[j]
    by {
        assert((j + 2) / 2 == j / 2 + 1) by(nonlinear_arith);
        assert((j + 2) % 2 == j % 2) by(nonlinear_arith);
        if j % 2 == 0 {
            //  a[j+2] = DecJump{start + (j+2)/2, sp+(j+2)+2}; b[j] = DecJump{(start+1)+j/2, (sp+2)+j+2}
        } else {
            //  a[j+2] = DecJump{zero, sp+(j+2)-1}; b[j] = DecJump{zero, (sp+2)+j-1}
        }
    }
}

///  Running `clear_bank_instrs(start_reg, count, zero, sp)` from its top reaches `sp + 2*count` with
///  every register in `[start_reg, start_reg + count)` zeroed and every other register preserved.
pub proof fn lemma_clear_bank(
    m: RegisterMachine, c: Configuration,
    start_reg: nat, count: nat, zero: nat, sp: nat,
)
    requires
        sp + 2 * count <= m.instructions.len(),
        forall|j: int| 0 <= j < 2 * count ==>
            m.instructions[(sp + j) as int] == #[trigger] clear_bank_instrs(start_reg, count, zero, sp)[j],
        c.pc == sp,
        c.registers.len() == m.num_regs,
        c.registers[zero as int] == 0,
        zero < m.num_regs,
        start_reg + count <= m.num_regs,
        zero < start_reg || zero >= start_reg + count,
    ensures
        exists|g: nat|
            #[trigger] run(m, c, g).pc == sp + 2 * count
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int ==>
                    run(m, c, g).registers[r] ==
                        (if start_reg <= r && r < start_reg + count { 0nat } else { c.registers[r] })),
    decreases count,
{
    if count == 0 {
        let g: nat = 0;
        assert(run(m, c, g) == c);
        assert(run(m, c, g).pc == sp + 2 * count);
        assert forall|r: int| 0 <= r < m.num_regs as int implies
            run(m, c, g).registers[r] ==
                (if start_reg <= r && r < start_reg + count { 0nat } else { c.registers[r] })
        by {
            assert(!(start_reg <= r && r < start_reg + count));
        }
    } else {
        let v0 = c.registers[start_reg as int];
        //  first gadget at sp / sp+1
        assert(clear_bank_instrs(start_reg, count, zero, sp)[0] == mk_dj(start_reg, sp + 2)) by {
            assert((0int) % 2 == 0);
        }
        assert(clear_bank_instrs(start_reg, count, zero, sp)[1] == mk_dj(zero, sp)) by {
            assert((1int) % 2 == 1);
        }
        assert(m.instructions[sp as int] == mk_dj(start_reg, sp + 2));
        assert(m.instructions[(sp + 1) as int] == mk_dj(zero, sp));
        assert(start_reg != zero);
        assert(start_reg < m.num_regs);

        lemma_clear_loop(m, c, start_reg, zero, sp, v0);
        let c1 = run(m, c, 2 * v0 + 1);
        assert(c1.pc == sp + 2);
        assert(c1.registers[start_reg as int] == 0);
        assert(c1.registers[zero as int] == 0) by { assert(zero != start_reg); }

        //  recursion frame via the shift identity
        lemma_clear_bank_shift(start_reg, count, zero, sp);
        assert forall|j: int| 0 <= j < 2 * (count - 1) implies
            m.instructions[((sp + 2) + j) as int]
                == #[trigger] clear_bank_instrs((start_reg + 1) as nat, (count - 1) as nat, zero, (sp + 2) as nat)[j]
        by {
            assert(m.instructions[(sp + (j + 2)) as int] == clear_bank_instrs(start_reg, count, zero, sp)[j + 2]);
            assert((sp + (j + 2)) as int == ((sp + 2) + j) as int);
        }

        lemma_clear_bank(m, c1, (start_reg + 1) as nat, (count - 1) as nat, zero, (sp + 2) as nat);
        let g_inner = choose|g: nat|
            run(m, c1, g).pc == (sp + 2) + 2 * (count - 1)
            && run(m, c1, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int ==>
                    run(m, c1, g).registers[r] ==
                        (if (start_reg + 1) <= r && r < (start_reg + 1) + (count - 1) { 0nat } else { c1.registers[r] }));
        let c2 = run(m, c1, g_inner);
        assert(c2.pc == sp + 2 * count) by {
            assert((sp + 2) + 2 * (count - 1) == sp + 2 * count);
        }

        let g: nat = (2 * v0 + 1 + g_inner) as nat;
        lemma_run_add(m, c, (2 * v0 + 1) as nat, g_inner);
        assert(run(m, c, g) == c2);

        assert forall|r: int| 0 <= r < m.num_regs as int implies
            run(m, c, g).registers[r] ==
                (if start_reg <= r && r < start_reg + count { 0nat } else { c.registers[r] })
        by {
            if (start_reg + 1) <= r && r < (start_reg + 1) + (count - 1) {
                assert(c2.registers[r] == 0);
                assert(start_reg <= r && r < start_reg + count);
            } else if r == start_reg as int {
                assert(c2.registers[r] == c1.registers[r]);
                assert(c1.registers[start_reg as int] == 0);
                assert(start_reg <= r && r < start_reg + count);
            } else {
                assert(c2.registers[r] == c1.registers[r]);
                assert(c1.registers[r] == c.registers[r]) by { assert(r != start_reg as int); }
                assert(!(start_reg <= r && r < start_reg + count));
            }
        }
    }
}

} //  verus!
