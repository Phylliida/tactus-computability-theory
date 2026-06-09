use vstd::prelude::*;
use crate::formula::*;
use crate::proof_system::*;

verus! {

//  ============================================================
//  Variable conventions for axioms
//  ============================================================

//  We use fixed variable indices for axiom formulas:
//  0=x, 1=y, 2=z, 3=w, 4=p, 5=u

pub open spec fn v_x() -> Term { mk_var(0) }
pub open spec fn v_y() -> Term { mk_var(1) }
pub open spec fn v_z() -> Term { mk_var(2) }
pub open spec fn v_w() -> Term { mk_var(3) }
pub open spec fn v_p() -> Term { mk_var(4) }
pub open spec fn v_u() -> Term { mk_var(5) }

//  ============================================================
//  ZFC Axioms (concrete formulas)
//  ============================================================

///  Extensionality: ∀x.∀y. (∀z. z∈x ↔ z∈y) → x=y
pub open spec fn extensionality_axiom() -> Formula {
    mk_forall(0, mk_forall(1,
        mk_implies(
            mk_forall(2, mk_iff(mk_in(v_z(), v_x()), mk_in(v_z(), v_y()))),
            mk_eq(v_x(), v_y())
        )
    ))
}

///  Pairing: ∀x.∀y.∃p.∀z. z∈p ↔ (z=x ∨ z=y)
pub open spec fn pairing_axiom() -> Formula {
    mk_forall(0, mk_forall(1, mk_exists(4,
        mk_forall(2,
            mk_iff(mk_in(v_z(), v_p()), mk_or(mk_eq(v_z(), v_x()), mk_eq(v_z(), v_y())))
        )
    )))
}

///  Union: ∀x.∃u.∀z. z∈u ↔ ∃y.(z∈y ∧ y∈x)
pub open spec fn union_axiom() -> Formula {
    mk_forall(0, mk_exists(5,
        mk_forall(2,
            mk_iff(
                mk_in(v_z(), v_u()),
                mk_exists(1, mk_and(mk_in(v_z(), v_y()), mk_in(v_y(), v_x())))
            )
        )
    ))
}

///  Power Set: ∀x.∃p.∀z. z∈p ↔ (∀w. w∈z → w∈x)
pub open spec fn powerset_axiom() -> Formula {
    mk_forall(0, mk_exists(4,
        mk_forall(2,
            mk_iff(
                mk_in(v_z(), v_p()),
                mk_forall(3, mk_implies(mk_in(v_w(), v_z()), mk_in(v_w(), v_x())))
            )
        )
    ))
}

///  Infinity: ∃x. (∃z. z∈x ∧ ∀w. ¬(w∈z)) ∧ (∀y. y∈x → ∃z. z∈x ∧ ∀w. w∈z ↔ (w∈y ∨ w=y))
///  (There exists a set containing the empty set and closed under successor s(y) = y ∪ {y})
pub open spec fn infinity_axiom() -> Formula {
    mk_exists(0,
        mk_and(
            //  Empty set is in x: ∃z. z∈x ∧ ∀w. ¬(w∈z)
            mk_exists(2, mk_and(mk_in(v_z(), v_x()), mk_forall(3, mk_not(mk_in(v_w(), v_z()))))),
            //  Closed under successor: ∀y. y∈x → ∃z. z∈x ∧ ∀w. (w∈z ↔ (w∈y ∨ w=y))
            mk_forall(1, mk_implies(mk_in(v_y(), v_x()),
                mk_exists(2, mk_and(mk_in(v_z(), v_x()),
                    mk_forall(3, mk_iff(mk_in(v_w(), v_z()), mk_or(mk_in(v_w(), v_y()), mk_eq(v_w(), v_y()))))
                ))
            ))
        )
    )
}

///  Foundation (Regularity): ∀x. (∃y. y∈x) → (∃y. y∈x ∧ ¬∃z. (z∈y ∧ z∈x))
pub open spec fn foundation_axiom() -> Formula {
    mk_forall(0, mk_implies(
        mk_exists(1, mk_in(v_y(), v_x())),
        mk_exists(1, mk_and(
            mk_in(v_y(), v_x()),
            mk_not(mk_exists(2, mk_and(mk_in(v_z(), v_y()), mk_in(v_z(), v_x()))))
        ))
    ))
}

///  Choice (simplified): ∀x. (∀y. y∈x → ∃z. z∈y) →
///    ∃u. ∀y. y∈x → ∃z. (z∈y ∧ z∈u ∧ ∀w. (w∈y ∧ w∈u) → w=z)
///  (Every family of nonempty sets has a choice function, selecting exactly one element per member.)
pub open spec fn choice_axiom() -> Formula {
    mk_forall(0, mk_implies(
        //  Premise: all members of x are nonempty
        mk_forall(1, mk_implies(mk_in(v_y(), v_x()), mk_exists(2, mk_in(v_z(), v_y())))),
        //  Conclusion: there exists a choice set u
        mk_exists(5, mk_forall(1, mk_implies(mk_in(v_y(), v_x()),
            mk_exists(2, mk_and(mk_and(mk_in(v_z(), v_y()), mk_in(v_z(), v_u())),
                mk_forall(3, mk_implies(mk_and(mk_in(v_w(), v_y()), mk_in(v_w(), v_u())),
                    mk_eq(v_w(), v_z())
                ))
            ))
        )))
    ))
}

//  ============================================================
//  Replacement Schema
//  ============================================================

///  Check if formula f is an instance of the Replacement schema:
///  ∀x. (∀y.∀z. (φ(x,y) ∧ φ(x,z)) → y=z) → ∀u.∃v.∀y. y∈v ↔ ∃x.(x∈u ∧ φ(x,y))
///
///  We use a simplified structural check: f must be of the right shape with
///  some inner formula phi.
pub open spec fn is_replacement_axiom(f: Formula) -> bool {
    //  For now, a predicate — checking the exact structure is verbose but possible.
    //  We use an exists over the inner formula.
    exists|phi: Formula, x_var: nat, y_var: nat, z_var: nat, u_var: nat, v_var: nat|
        x_var != y_var && x_var != z_var && y_var != z_var &&
        u_var != x_var && u_var != y_var && v_var != x_var && v_var != y_var && u_var != v_var &&
        f == mk_forall(x_var, mk_implies(
            //  Functionality: ∀y.∀z. (φ(x,y) ∧ φ(x,z)) → y=z
            mk_forall(y_var, mk_forall(z_var, mk_implies(
                mk_and(phi, subst(phi, z_var, mk_var(y_var))),  //  simplified: check phi mentions z_var
                mk_eq(mk_var(y_var), mk_var(z_var))
            ))),
            //  Range is a set: ∀u.∃v.∀y. y∈v ↔ ∃x.(x∈u ∧ φ(x,y))
            mk_forall(u_var, mk_exists(v_var, mk_forall(y_var,
                mk_iff(
                    mk_in(mk_var(y_var), mk_var(v_var)),
                    mk_exists(x_var, mk_and(mk_in(mk_var(x_var), mk_var(u_var)), phi))
                )
            )))
        ))
}

//  ============================================================
//  Combined ZFC axiom predicate
//  ============================================================

///  A formula is a ZFC axiom if it's one of the 7 fixed axioms or a Replacement instance.
#[verifier::opaque]
pub open spec fn is_zfc_axiom(f: Formula) -> bool {
    f == extensionality_axiom()
    || f == pairing_axiom()
    || f == union_axiom()
    || f == powerset_axiom()
    || f == infinity_axiom()
    || f == foundation_axiom()
    || f == choice_axiom()
    || is_replacement_axiom(f)
}

///  A formula is provable in ZFC if it's provable from ZFC axioms.
pub open spec fn provable_in_zfc(phi: Formula) -> bool {
    provable_from(phi, |f: Formula| is_zfc_axiom(f))
}

} //  verus!
