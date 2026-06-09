use vstd::prelude::*;
use crate::formula::*;

verus! {

//  ============================================================
//  Proof data structures
//  ============================================================

///  Justification for a proof line.
pub enum Justification {
    ///  The formula is a logic axiom instance.
    LogicAxiom,
    ///  The formula is from the assumption set.
    Assumption,
    ///  Modus ponens: from line `premise_line` (φ) and line `implication_line` (φ→ψ), derive ψ.
    ModusPonens { premise_line: nat, implication_line: nat },
    ///  Universal generalization: from line `premise_line` (φ), derive ∀var.φ.
    Generalization { premise_line: nat, var: nat },
}

///  A formal proof: a sequence of (formula, justification) pairs.
pub struct Proof {
    pub lines: Seq<(Formula, Justification)>,
}

//  ============================================================
//  Axiom schemas
//  ============================================================

///  φ → φ  (identity / self-implication)
pub open spec fn is_axiom_identity(f: Formula) -> bool {
    exists|phi: Formula|
        f == mk_implies(phi, phi)
}

///  (φ → ψ) → ((ψ → φ) → (φ ↔ ψ))  (biconditional introduction)
pub open spec fn is_axiom_iff_intro(f: Formula) -> bool {
    exists|phi: Formula, psi: Formula|
        f == mk_implies(
            mk_implies(phi, psi),
            mk_implies(mk_implies(psi, phi), mk_iff(phi, psi))
        )
}

///  (φ ↔ ψ) → (φ → ψ)  (biconditional elimination left)
pub open spec fn is_axiom_iff_elim_left(f: Formula) -> bool {
    exists|phi: Formula, psi: Formula|
        f == mk_implies(mk_iff(phi, psi), mk_implies(phi, psi))
}

///  (φ ↔ ψ) → (ψ → φ)  (biconditional elimination right)
pub open spec fn is_axiom_iff_elim_right(f: Formula) -> bool {
    exists|phi: Formula, psi: Formula|
        f == mk_implies(mk_iff(phi, psi), mk_implies(psi, phi))
}

///  (φ → ψ) → ((ψ → χ) → (φ → χ))  (hypothetical syllogism)
pub open spec fn is_axiom_hyp_syllogism(f: Formula) -> bool {
    exists|phi: Formula, psi: Formula, chi: Formula|
        f == mk_implies(
            mk_implies(phi, psi),
            mk_implies(mk_implies(psi, chi), mk_implies(phi, chi))
        )
}

///  (∀x.φ) → φ[x/t]  (universal instantiation)
pub open spec fn is_axiom_universal_inst(f: Formula) -> bool {
    exists|phi: Formula, var: nat, t: Term|
        f == mk_implies(mk_forall(var, phi), subst(phi, var, t))
}

///  (∀x.(φ→ψ)) → ((∀x.φ) → (∀x.ψ))  (quantifier distribution)
pub open spec fn is_axiom_quantifier_dist(f: Formula) -> bool {
    exists|phi: Formula, psi: Formula, var: nat|
        f == mk_implies(
            mk_forall(var, mk_implies(phi, psi)),
            mk_implies(mk_forall(var, phi), mk_forall(var, psi))
        )
}

///  φ → ∀x.φ  when x is not free in φ  (vacuous quantification)
pub open spec fn is_axiom_vacuous_quant(f: Formula) -> bool {
    exists|phi: Formula, var: nat|
        !free_vars(phi).contains(var) &&
        f == mk_implies(phi, mk_forall(var, phi))
}

///  x = x  (equality reflexivity)
pub open spec fn is_axiom_eq_refl(f: Formula) -> bool {
    exists|t: Term|
        f == mk_eq(t, t)
}

///  x = y → (φ[z/x] → φ[z/y])  (equality substitution, Leibniz left)
pub open spec fn is_axiom_eq_subst_left(f: Formula) -> bool {
    exists|x: Term, y: Term, phi: Formula, var: nat|
        f == mk_implies(
            mk_eq(x, y),
            mk_implies(subst(phi, var, x), subst(phi, var, y))
        )
}

///  x = y → (φ[z/y] → φ[z/x])  (equality substitution, Leibniz right)
pub open spec fn is_axiom_eq_subst_right(f: Formula) -> bool {
    exists|x: Term, y: Term, phi: Formula, var: nat|
        f == mk_implies(
            mk_eq(x, y),
            mk_implies(subst(phi, var, y), subst(phi, var, x))
        )
}

///  Combined logic axiom check.
#[verifier::opaque]
pub open spec fn is_logic_axiom(f: Formula) -> bool {
    is_axiom_identity(f)
    || is_axiom_iff_intro(f)
    || is_axiom_iff_elim_left(f)
    || is_axiom_iff_elim_right(f)
    || is_axiom_hyp_syllogism(f)
    || is_axiom_universal_inst(f)
    || is_axiom_quantifier_dist(f)
    || is_axiom_vacuous_quant(f)
    || is_axiom_eq_refl(f)
    || is_axiom_eq_subst_left(f)
    || is_axiom_eq_subst_right(f)
}

//  ============================================================
//  Proof validity
//  ============================================================

///  Check that line i of a proof is validly justified.
pub open spec fn line_valid(
    proof: Proof,
    i: nat,
    assumptions: spec_fn(Formula) -> bool,
) -> bool
    recommends i < proof.lines.len(),
{
    if i >= proof.lines.len() {
        false
    } else {
        let (formula, justification) = proof.lines[i as int];
        match justification {
            Justification::LogicAxiom => is_logic_axiom(formula),
            Justification::Assumption => assumptions(formula),
            Justification::ModusPonens { premise_line, implication_line } => {
                premise_line < i && implication_line < i &&
                proof.lines[premise_line as int].0 == {
                    //  The implication line must be φ→ψ where premise line is φ and current is ψ
                    let imp = proof.lines[implication_line as int].0;
                    //  Check: implication_line is "premise → formula"
                    proof.lines[premise_line as int].0
                } && {
                    let premise = proof.lines[premise_line as int].0;
                    let imp_formula = proof.lines[implication_line as int].0;
                    imp_formula == mk_implies(premise, formula)
                }
            },
            Justification::Generalization { premise_line, var } => {
                premise_line < i && {
                    let premise = proof.lines[premise_line as int].0;
                    formula == mk_forall(var, premise)
                }
            },
        }
    }
}

///  A proof is valid if all lines are validly justified.
pub open spec fn is_valid_proof(proof: Proof, assumptions: spec_fn(Formula) -> bool) -> bool {
    proof.lines.len() > 0 &&
    forall|i: nat| #[trigger] line_valid(proof, i, assumptions) || i >= proof.lines.len()
}

///  The conclusion of a proof (the formula on the last line).
pub open spec fn proof_conclusion(proof: Proof) -> Formula
    recommends proof.lines.len() > 0,
{
    proof.lines[proof.lines.len() - 1].0
}

///  A formula is provable from assumptions if there exists a valid proof concluding it.
pub open spec fn provable_from(phi: Formula, assumptions: spec_fn(Formula) -> bool) -> bool {
    exists|proof: Proof|
        #[trigger] is_valid_proof(proof, assumptions) &&
        proof_conclusion(proof) == phi
}

//  ============================================================
//  Proof manipulation
//  ============================================================

///  Shift line references in a justification by offset.
pub open spec fn shift_justification(j: Justification, offset: nat) -> Justification {
    match j {
        Justification::LogicAxiom => Justification::LogicAxiom,
        Justification::Assumption => Justification::Assumption,
        Justification::ModusPonens { premise_line, implication_line } =>
            Justification::ModusPonens {
                premise_line: premise_line + offset,
                implication_line: implication_line + offset,
            },
        Justification::Generalization { premise_line, var } =>
            Justification::Generalization {
                premise_line: premise_line + offset,
                var,
            },
    }
}

///  Shift all line references in a proof by offset.
pub open spec fn shift_proof(proof: Proof, offset: nat) -> Proof {
    Proof {
        lines: Seq::new(proof.lines.len(), |i: int|
            (proof.lines[i].0, shift_justification(proof.lines[i].1, offset))
        ),
    }
}

//  ============================================================
//  Core proof lemmas
//  ============================================================

///  Any assumption is provable from the assumption set (1-line proof).
pub proof fn lemma_provable_assumption(phi: Formula, assumptions: spec_fn(Formula) -> bool)
    requires
        assumptions(phi),
    ensures
        provable_from(phi, assumptions),
{
    let proof = Proof { lines: seq![(phi, Justification::Assumption)] };
    assert(proof.lines.len() == 1);
    assert(proof.lines[0] == (phi, Justification::Assumption));
    assert(line_valid(proof, 0, assumptions)) by {
        reveal(is_logic_axiom);
    };
    assert forall|i: nat| #[trigger] line_valid(proof, i, assumptions) || i >= proof.lines.len() by {
        if i == 0 {
            assert(line_valid(proof, 0, assumptions));
        }
    };
    assert(is_valid_proof(proof, assumptions));
    assert(proof_conclusion(proof) == phi);
}

///  A logic axiom is provable from any assumptions (1-line proof).
pub proof fn lemma_provable_logic_axiom(phi: Formula, assumptions: spec_fn(Formula) -> bool)
    requires
        is_logic_axiom(phi),
    ensures
        provable_from(phi, assumptions),
{
    let proof = Proof { lines: seq![(phi, Justification::LogicAxiom)] };
    assert(line_valid(proof, 0, assumptions));
    assert forall|i: nat| #[trigger] line_valid(proof, i, assumptions) || i >= proof.lines.len() by {
        if i == 0 {
            assert(line_valid(proof, 0, assumptions));
        }
    };
    assert(is_valid_proof(proof, assumptions));
    assert(proof_conclusion(proof) == phi);
}

///  Shifted proof preserves validity.
proof fn lemma_shift_proof_valid(proof: Proof, offset: nat, assumptions: spec_fn(Formula) -> bool)
    requires
        is_valid_proof(proof, assumptions),
    ensures
        shift_proof(proof, offset).lines.len() == proof.lines.len(),
        forall|i: nat| i < proof.lines.len() ==>
            shift_proof(proof, offset).lines[i as int].0 == proof.lines[i as int].0,
{
    let shifted = shift_proof(proof, offset);
    assert(shifted.lines.len() == proof.lines.len());
}

///  Concatenation of valid proofs preserves validity.
pub proof fn lemma_proof_concat(
    p1: Proof,
    p2: Proof,
    assumptions: spec_fn(Formula) -> bool,
) -> (combined: Proof)
    requires
        is_valid_proof(p1, assumptions),
        is_valid_proof(p2, assumptions),
    ensures
        is_valid_proof(combined, assumptions),
        combined.lines.len() == p1.lines.len() + p2.lines.len(),
        proof_conclusion(combined) == proof_conclusion(p2),
        //  First part matches p1
        forall|i: nat| i < p1.lines.len() ==>
            combined.lines[i as int].0 == p1.lines[i as int].0,
{
    let offset = p1.lines.len();
    let shifted_p2 = shift_proof(p2, offset);
    let combined = Proof {
        lines: p1.lines + shifted_p2.lines,
    };

    //  Prove all lines are valid
    assert forall|i: nat| #[trigger] line_valid(combined, i, assumptions) || i >= combined.lines.len() by {
        if i < combined.lines.len() {
            if i < p1.lines.len() {
                //  Line from p1
                assert(combined.lines[i as int] == p1.lines[i as int]);
                assert(line_valid(p1, i, assumptions));
                //  Need to show line_valid(combined, i, assumptions)
                let (formula, justification) = p1.lines[i as int];
                match justification {
                    Justification::LogicAxiom => {
                        assert(is_logic_axiom(formula));
                    },
                    Justification::Assumption => {
                        assert(assumptions(formula));
                    },
                    Justification::ModusPonens { premise_line, implication_line } => {
                        assert(premise_line < i && implication_line < i);
                        assert(combined.lines[premise_line as int] == p1.lines[premise_line as int]);
                        assert(combined.lines[implication_line as int] == p1.lines[implication_line as int]);
                    },
                    Justification::Generalization { premise_line, var } => {
                        assert(premise_line < i);
                        assert(combined.lines[premise_line as int] == p1.lines[premise_line as int]);
                    },
                }
            } else {
                //  Line from shifted p2
                let j = (i - offset) as nat;
                assert(combined.lines[i as int] == shifted_p2.lines[j as int]);
                assert(shifted_p2.lines[j as int].0 == p2.lines[j as int].0);
                assert(line_valid(p2, j, assumptions));
                let (formula, justification) = p2.lines[j as int];
                let shifted_just = shift_justification(justification, offset);
                assert(combined.lines[i as int] == (formula, shifted_just));
                match justification {
                    Justification::LogicAxiom => {
                        assert(is_logic_axiom(formula));
                    },
                    Justification::Assumption => {
                        assert(assumptions(formula));
                    },
                    Justification::ModusPonens { premise_line, implication_line } => {
                        assert(premise_line < j && implication_line < j);
                        let sp = premise_line + offset;
                        let si = implication_line + offset;
                        assert(combined.lines[sp as int].0 == p2.lines[premise_line as int].0);
                        assert(combined.lines[si as int].0 == p2.lines[implication_line as int].0);
                        let premise = p2.lines[premise_line as int].0;
                        let imp_formula = p2.lines[implication_line as int].0;
                        assert(imp_formula == mk_implies(premise, formula));
                    },
                    Justification::Generalization { premise_line, var } => {
                        assert(premise_line < j);
                        let sp = premise_line + offset;
                        assert(combined.lines[sp as int].0 == p2.lines[premise_line as int].0);
                    },
                }
            }
        }
    };

    assert(combined.lines.len() > 0);
    assert(is_valid_proof(combined, assumptions));

    //  Conclusion
    assert(combined.lines[combined.lines.len() - 1]
        == shifted_p2.lines[shifted_p2.lines.len() - 1]);
    assert(shifted_p2.lines[shifted_p2.lines.len() - 1].0
        == p2.lines[p2.lines.len() - 1].0);
    assert(proof_conclusion(combined) == proof_conclusion(p2));

    combined
}

///  Modus ponens for provability: if provable(φ) and provable(φ→ψ), then provable(ψ).
pub proof fn lemma_provable_mp(
    phi: Formula,
    psi: Formula,
    assumptions: spec_fn(Formula) -> bool,
)
    requires
        provable_from(phi, assumptions),
        provable_from(mk_implies(phi, psi), assumptions),
    ensures
        provable_from(psi, assumptions),
{
    let p_phi = choose|p: Proof| is_valid_proof(p, assumptions) && proof_conclusion(p) == phi;
    let p_imp = choose|p: Proof| is_valid_proof(p, assumptions) && proof_conclusion(p) == mk_implies(phi, psi);

    let combined = lemma_proof_concat(p_phi, p_imp, assumptions);
    let n = combined.lines.len();

    //  Add MP line
    let mp_line = (psi, Justification::ModusPonens {
        premise_line: (p_phi.lines.len() - 1) as nat,
        implication_line: (n - 1) as nat,
    });
    let final_proof = Proof { lines: combined.lines.push(mp_line) };

    assert(final_proof.lines.len() == n + 1);
    assert(final_proof.lines[n as int] == mp_line);

    //  Verify the MP line is valid
    let premise_idx: nat = (p_phi.lines.len() - 1) as nat;
    let imp_idx: nat = (n - 1) as nat;
    assert(premise_idx < n);
    assert(imp_idx < n);
    assert(final_proof.lines[premise_idx as int].0 == phi);
    assert(final_proof.lines[imp_idx as int].0 == mk_implies(phi, psi));

    //  All previous lines still valid
    assert forall|i: nat| #[trigger] line_valid(final_proof, i, assumptions)
        || i >= final_proof.lines.len()
    by {
        if i < final_proof.lines.len() {
            if i < n {
                assert(final_proof.lines[i as int] == combined.lines[i as int]);
                assert(line_valid(combined, i, assumptions));
                let (formula, justification) = combined.lines[i as int];
                match justification {
                    Justification::LogicAxiom => {
                        assert(is_logic_axiom(formula));
                    },
                    Justification::Assumption => {
                        assert(assumptions(formula));
                    },
                    Justification::ModusPonens { premise_line, implication_line } => {
                        assert(premise_line < i && implication_line < i);
                        assert(final_proof.lines[premise_line as int]
                            == combined.lines[premise_line as int]);
                        assert(final_proof.lines[implication_line as int]
                            == combined.lines[implication_line as int]);
                    },
                    Justification::Generalization { premise_line, var } => {
                        assert(premise_line < i);
                        assert(final_proof.lines[premise_line as int]
                            == combined.lines[premise_line as int]);
                    },
                }
            } else {
                //  i == n, the MP line
                assert(i == n);
            }
        }
    };

    assert(is_valid_proof(final_proof, assumptions));
    assert(proof_conclusion(final_proof) == psi);
}

//  ============================================================
//  Iff reflexivity: φ ↔ φ
//  ============================================================

///  Construct a proof of φ ↔ φ from any assumptions.
pub proof fn lemma_provable_iff_refl(phi: Formula, assumptions: spec_fn(Formula) -> bool)
    ensures
        provable_from(mk_iff(phi, phi), assumptions),
{
    //  Line 0: φ→φ           (axiom: identity)
    //  Line 1: (φ→φ)→((φ→φ)→(φ↔φ))  (axiom: iff_intro)
    //  Line 2: (φ→φ)→(φ↔φ)   (MP: 0, 1)
    //  Line 3: φ↔φ           (MP: 0, 2)

    let id = mk_implies(phi, phi);
    let iff_intro_inst = mk_implies(id, mk_implies(id, mk_iff(phi, phi)));
    let step2 = mk_implies(id, mk_iff(phi, phi));
    let goal = mk_iff(phi, phi);

    let proof = Proof { lines: seq![
        (id, Justification::LogicAxiom),
        (iff_intro_inst, Justification::LogicAxiom),
        (step2, Justification::ModusPonens { premise_line: 0, implication_line: 1 }),
        (goal, Justification::ModusPonens { premise_line: 0, implication_line: 2 }),
    ] };

    //  Verify axiom instances
    assert(is_axiom_identity(id)) by {
        assert(id == mk_implies(phi, phi));
    };
    assert(is_logic_axiom(id)) by { reveal(is_logic_axiom); };

    assert(is_axiom_iff_intro(iff_intro_inst)) by {
        assert(iff_intro_inst == mk_implies(
            mk_implies(phi, phi),
            mk_implies(mk_implies(phi, phi), mk_iff(phi, phi))
        ));
    };
    assert(is_logic_axiom(iff_intro_inst)) by { reveal(is_logic_axiom); };

    //  Verify MP steps
    assert(proof.lines[0].0 == id);
    assert(proof.lines[1].0 == iff_intro_inst);
    assert(iff_intro_inst == mk_implies(id, step2));
    assert(step2 == mk_implies(id, goal));

    assert forall|i: nat| #[trigger] line_valid(proof, i, assumptions) || i >= proof.lines.len() by {
        if i < proof.lines.len() {
            if i == 0 {
                assert(is_logic_axiom(id));
            } else if i == 1 {
                assert(is_logic_axiom(iff_intro_inst));
            } else if i == 2 {
                //  MP(0, 1): premise=id, imp=iff_intro_inst=id→step2
                assert(proof.lines[0].0 == id);
                assert(proof.lines[1].0 == mk_implies(id, step2));
            } else {
                //  i == 3, MP(0, 2): premise=id, imp=step2=id→goal
                assert(proof.lines[0].0 == id);
                assert(proof.lines[2].0 == mk_implies(id, goal));
            }
        }
    };

    assert(is_valid_proof(proof, assumptions));
    assert(proof_conclusion(proof) == goal);
}

//  ============================================================
//  Iff symmetry: φ↔ψ implies ψ↔φ
//  ============================================================

///  Given provable(φ↔ψ), construct a proof of ψ↔φ.
pub proof fn lemma_provable_iff_sym(
    phi: Formula,
    psi: Formula,
    assumptions: spec_fn(Formula) -> bool,
)
    requires
        provable_from(mk_iff(phi, psi), assumptions),
    ensures
        provable_from(mk_iff(psi, phi), assumptions),
{
    let iff_phi_psi = mk_iff(phi, psi);

    //  First prove ψ→φ
    //  (φ↔ψ)→(ψ→φ) is iff_elim_right axiom
    let elim_r = mk_implies(iff_phi_psi, mk_implies(psi, phi));
    assert(is_axiom_iff_elim_right(elim_r)) by {
        assert(elim_r == mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)));
    };
    assert(is_logic_axiom(elim_r)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(elim_r, assumptions);
    lemma_provable_mp(iff_phi_psi, mk_implies(psi, phi), assumptions);
    //  Now provable(ψ→φ)

    //  Then prove φ→ψ
    let elim_l = mk_implies(iff_phi_psi, mk_implies(phi, psi));
    assert(is_axiom_iff_elim_left(elim_l)) by {
        assert(elim_l == mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)));
    };
    assert(is_logic_axiom(elim_l)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(elim_l, assumptions);
    lemma_provable_mp(iff_phi_psi, mk_implies(phi, psi), assumptions);
    //  Now provable(φ→ψ)

    //  Use iff_intro for ψ↔φ: (ψ→φ)→((φ→ψ)→(ψ↔φ))
    let iff_intro_inst = mk_implies(
        mk_implies(psi, phi),
        mk_implies(mk_implies(phi, psi), mk_iff(psi, phi))
    );
    assert(is_axiom_iff_intro(iff_intro_inst)) by {
        assert(iff_intro_inst == mk_implies(
            mk_implies(psi, phi),
            mk_implies(mk_implies(phi, psi), mk_iff(psi, phi))
        ));
    };
    assert(is_logic_axiom(iff_intro_inst)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(iff_intro_inst, assumptions);

    //  MP: provable(ψ→φ) + provable((ψ→φ)→((φ→ψ)→(ψ↔φ))) => provable((φ→ψ)→(ψ↔φ))
    lemma_provable_mp(mk_implies(psi, phi), mk_implies(mk_implies(phi, psi), mk_iff(psi, phi)), assumptions);

    //  MP: provable(φ→ψ) + provable((φ→ψ)→(ψ↔φ)) => provable(ψ↔φ)
    lemma_provable_mp(mk_implies(phi, psi), mk_iff(psi, phi), assumptions);
}

//  ============================================================
//  Iff transitivity: φ↔ψ and ψ↔χ implies φ↔χ
//  ============================================================

///  Given provable(φ↔ψ) and provable(ψ↔χ), construct a proof of φ↔χ.
pub proof fn lemma_provable_iff_trans(
    phi: Formula,
    psi: Formula,
    chi: Formula,
    assumptions: spec_fn(Formula) -> bool,
)
    requires
        provable_from(mk_iff(phi, psi), assumptions),
        provable_from(mk_iff(psi, chi), assumptions),
    ensures
        provable_from(mk_iff(phi, chi), assumptions),
{
    let iff_phi_psi = mk_iff(phi, psi);
    let iff_psi_chi = mk_iff(psi, chi);

    //  Extract φ→ψ from φ↔ψ
    let elim_l1 = mk_implies(iff_phi_psi, mk_implies(phi, psi));
    assert(is_axiom_iff_elim_left(elim_l1)) by {
        assert(elim_l1 == mk_implies(mk_iff(phi, psi), mk_implies(phi, psi)));
    };
    assert(is_logic_axiom(elim_l1)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(elim_l1, assumptions);
    lemma_provable_mp(iff_phi_psi, mk_implies(phi, psi), assumptions);
    //  provable(φ→ψ)

    //  Extract ψ→χ from ψ↔χ
    let elim_l2 = mk_implies(iff_psi_chi, mk_implies(psi, chi));
    assert(is_axiom_iff_elim_left(elim_l2)) by {
        assert(elim_l2 == mk_implies(mk_iff(psi, chi), mk_implies(psi, chi)));
    };
    assert(is_logic_axiom(elim_l2)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(elim_l2, assumptions);
    lemma_provable_mp(iff_psi_chi, mk_implies(psi, chi), assumptions);
    //  provable(ψ→χ)

    //  Hyp syllogism: (φ→ψ)→((ψ→χ)→(φ→χ))
    let hs1 = mk_implies(
        mk_implies(phi, psi),
        mk_implies(mk_implies(psi, chi), mk_implies(phi, chi))
    );
    assert(is_axiom_hyp_syllogism(hs1)) by {
        assert(hs1 == mk_implies(
            mk_implies(phi, psi),
            mk_implies(mk_implies(psi, chi), mk_implies(phi, chi))
        ));
    };
    assert(is_logic_axiom(hs1)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(hs1, assumptions);
    lemma_provable_mp(mk_implies(phi, psi), mk_implies(mk_implies(psi, chi), mk_implies(phi, chi)), assumptions);
    lemma_provable_mp(mk_implies(psi, chi), mk_implies(phi, chi), assumptions);
    //  provable(φ→χ)

    //  Now get χ→φ: extract ψ→φ from φ↔ψ, χ→ψ from ψ↔χ, compose
    let elim_r1 = mk_implies(iff_phi_psi, mk_implies(psi, phi));
    assert(is_axiom_iff_elim_right(elim_r1)) by {
        assert(elim_r1 == mk_implies(mk_iff(phi, psi), mk_implies(psi, phi)));
    };
    assert(is_logic_axiom(elim_r1)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(elim_r1, assumptions);
    lemma_provable_mp(iff_phi_psi, mk_implies(psi, phi), assumptions);
    //  provable(ψ→φ)

    let elim_r2 = mk_implies(iff_psi_chi, mk_implies(chi, psi));
    assert(is_axiom_iff_elim_right(elim_r2)) by {
        assert(elim_r2 == mk_implies(mk_iff(psi, chi), mk_implies(chi, psi)));
    };
    assert(is_logic_axiom(elim_r2)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(elim_r2, assumptions);
    lemma_provable_mp(iff_psi_chi, mk_implies(chi, psi), assumptions);
    //  provable(χ→ψ)

    //  Hyp syllogism: (χ→ψ)→((ψ→φ)→(χ→φ))
    let hs2 = mk_implies(
        mk_implies(chi, psi),
        mk_implies(mk_implies(psi, phi), mk_implies(chi, phi))
    );
    assert(is_axiom_hyp_syllogism(hs2)) by {
        assert(hs2 == mk_implies(
            mk_implies(chi, psi),
            mk_implies(mk_implies(psi, phi), mk_implies(chi, phi))
        ));
    };
    assert(is_logic_axiom(hs2)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(hs2, assumptions);
    lemma_provable_mp(mk_implies(chi, psi), mk_implies(mk_implies(psi, phi), mk_implies(chi, phi)), assumptions);
    lemma_provable_mp(mk_implies(psi, phi), mk_implies(chi, phi), assumptions);
    //  provable(χ→φ)

    //  Finally, iff_intro: (φ→χ)→((χ→φ)→(φ↔χ))
    let iff_intro_inst = mk_implies(
        mk_implies(phi, chi),
        mk_implies(mk_implies(chi, phi), mk_iff(phi, chi))
    );
    assert(is_axiom_iff_intro(iff_intro_inst)) by {
        assert(iff_intro_inst == mk_implies(
            mk_implies(phi, chi),
            mk_implies(mk_implies(chi, phi), mk_iff(phi, chi))
        ));
    };
    assert(is_logic_axiom(iff_intro_inst)) by { reveal(is_logic_axiom); };
    lemma_provable_logic_axiom(iff_intro_inst, assumptions);
    lemma_provable_mp(mk_implies(phi, chi), mk_implies(mk_implies(chi, phi), mk_iff(phi, chi)), assumptions);
    lemma_provable_mp(mk_implies(chi, phi), mk_iff(phi, chi), assumptions);
    //  provable(φ↔χ)
}

} //  verus!
