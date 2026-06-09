use vstd::prelude::*;
use crate::pairing::*;

verus! {

///  A first-order term. For ZFC, we only need variables.
pub enum Term {
    Var { index: nat },
}

///  A first-order formula in the language of set theory (=, ∈).
pub enum Formula {
    Eq { left: Term, right: Term },
    In { left: Term, right: Term },
    Not { sub: Box<Formula> },
    And { left: Box<Formula>, right: Box<Formula> },
    Or { left: Box<Formula>, right: Box<Formula> },
    Implies { left: Box<Formula>, right: Box<Formula> },
    Iff { left: Box<Formula>, right: Box<Formula> },
    Forall { var: nat, sub: Box<Formula> },
    Exists { var: nat, sub: Box<Formula> },
}

//  ============================================================
//  Structural size
//  ============================================================

///  Structural size of a term.
pub open spec fn term_size(t: Term) -> nat {
    match t {
        Term::Var { .. } => 1,
    }
}

///  Structural size of a formula.
pub open spec fn formula_size(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { .. } => 1,
        Formula::In { .. } => 1,
        Formula::Not { sub } => 1 + formula_size(*sub),
        Formula::And { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Or { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Implies { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Iff { left, right } => 1 + formula_size(*left) + formula_size(*right),
        Formula::Forall { var, sub } => 1 + formula_size(*sub),
        Formula::Exists { var, sub } => 1 + formula_size(*sub),
    }
}

///  Formula size is always positive.
pub proof fn lemma_formula_size_pos(f: Formula)
    ensures
        formula_size(f) >= 1,
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_formula_size_pos(*sub); },
        Formula::And { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Or { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Implies { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Iff { left, right } => { lemma_formula_size_pos(*left); lemma_formula_size_pos(*right); },
        Formula::Forall { var, sub } => { lemma_formula_size_pos(*sub); },
        Formula::Exists { var, sub } => { lemma_formula_size_pos(*sub); },
    }
}

//  ============================================================
//  Free variables
//  ============================================================

///  Free variables of a term.
pub open spec fn term_free_vars(t: Term) -> Set<nat> {
    match t {
        Term::Var { index } => set![index],
    }
}

///  Free variables of a formula.
pub open spec fn free_vars(f: Formula) -> Set<nat>
    decreases f,
{
    match f {
        Formula::Eq { left, right } => term_free_vars(left).union(term_free_vars(right)),
        Formula::In { left, right } => term_free_vars(left).union(term_free_vars(right)),
        Formula::Not { sub } => free_vars(*sub),
        Formula::And { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Or { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Implies { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Iff { left, right } => free_vars(*left).union(free_vars(*right)),
        Formula::Forall { var, sub } => free_vars(*sub).remove(var),
        Formula::Exists { var, sub } => free_vars(*sub).remove(var),
    }
}

///  A formula is a sentence if it has no free variables.
pub open spec fn is_sentence(f: Formula) -> bool {
    free_vars(f) =~= Set::empty()
}

///  Check if variable v is free in formula f.
pub open spec fn has_free_var(f: Formula, v: nat) -> bool {
    free_vars(f).contains(v)
}

///  Sentences have no free variables.
pub proof fn lemma_sentence_no_free_var(f: Formula, v: nat)
    requires
        is_sentence(f),
    ensures
        !has_free_var(f, v),
{
}

///  has_free_var decomposes for Not.
pub proof fn lemma_has_free_var_not(sub: Formula, v: nat)
    ensures
        has_free_var(Formula::Not { sub: Box::new(sub) }, v) == has_free_var(sub, v),
{
}

///  has_free_var decomposes for binary connectives.
pub proof fn lemma_has_free_var_binary(left: Formula, right: Formula, v: nat)
    ensures
        has_free_var(Formula::And { left: Box::new(left), right: Box::new(right) }, v)
            == (has_free_var(left, v) || has_free_var(right, v)),
        has_free_var(Formula::Or { left: Box::new(left), right: Box::new(right) }, v)
            == (has_free_var(left, v) || has_free_var(right, v)),
        has_free_var(Formula::Implies { left: Box::new(left), right: Box::new(right) }, v)
            == (has_free_var(left, v) || has_free_var(right, v)),
        has_free_var(Formula::Iff { left: Box::new(left), right: Box::new(right) }, v)
            == (has_free_var(left, v) || has_free_var(right, v)),
{
}

///  has_free_var decomposes for quantifiers.
pub proof fn lemma_has_free_var_quantifier(var: nat, sub: Formula, v: nat)
    ensures
        has_free_var(Formula::Forall { var, sub: Box::new(sub) }, v)
            == (has_free_var(sub, v) && v != var),
        has_free_var(Formula::Exists { var, sub: Box::new(sub) }, v)
            == (has_free_var(sub, v) && v != var),
{
}

///  Traversal cost: actual number of BoundedRec steps to process formula f
///  when checking variable v. Accounts for quantifier short-circuiting.
pub open spec fn traversal_cost(f: Formula, v: nat) -> nat
    decreases f,
{
    match f {
        Formula::Eq { .. } => 1,
        Formula::In { .. } => 1,
        Formula::Not { sub } => 1 + traversal_cost(*sub, v),
        Formula::And { left, right } => 1 + traversal_cost(*left, v) + traversal_cost(*right, v),
        Formula::Or { left, right } => 1 + traversal_cost(*left, v) + traversal_cost(*right, v),
        Formula::Implies { left, right } => 1 + traversal_cost(*left, v) + traversal_cost(*right, v),
        Formula::Iff { left, right } => 1 + traversal_cost(*left, v) + traversal_cost(*right, v),
        Formula::Forall { var, sub } =>
            if var == v { 1 } else { 1 + traversal_cost(*sub, v) },
        Formula::Exists { var, sub } =>
            if var == v { 1 } else { 1 + traversal_cost(*sub, v) },
    }
}

///  Cost of traversing a formula for substitution checking.
///  When bound var == subst var, the checker shortcuts (cost 1, not 1+cost(sub)).
pub open spec fn subst_traversal_cost(f: Formula, var: nat) -> nat
    decreases f,
{
    match f {
        Formula::Eq { .. } => 1,
        Formula::In { .. } => 1,
        Formula::Not { sub } => 1 + subst_traversal_cost(*sub, var),
        Formula::And { left, right } => 1 + subst_traversal_cost(*left, var) + subst_traversal_cost(*right, var),
        Formula::Or { left, right } => 1 + subst_traversal_cost(*left, var) + subst_traversal_cost(*right, var),
        Formula::Implies { left, right } => 1 + subst_traversal_cost(*left, var) + subst_traversal_cost(*right, var),
        Formula::Iff { left, right } => 1 + subst_traversal_cost(*left, var) + subst_traversal_cost(*right, var),
        Formula::Forall { var: v, sub } =>
            if v == var { 1 } else { 1 + subst_traversal_cost(*sub, var) },
        Formula::Exists { var: v, sub } =>
            if v == var { 1 } else { 1 + subst_traversal_cost(*sub, var) },
    }
}

pub proof fn lemma_subst_traversal_cost_pos(f: Formula, var: nat)
    ensures subst_traversal_cost(f, var) >= 1,
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_subst_traversal_cost_pos(*sub, var); },
        Formula::And { left, right } => { lemma_subst_traversal_cost_pos(*left, var); },
        Formula::Or { left, right } => { lemma_subst_traversal_cost_pos(*left, var); },
        Formula::Implies { left, right } => { lemma_subst_traversal_cost_pos(*left, var); },
        Formula::Iff { left, right } => { lemma_subst_traversal_cost_pos(*left, var); },
        Formula::Forall { var: v, sub } => {},
        Formula::Exists { var: v, sub } => {},
    }
}

pub proof fn lemma_subst_cost_le_formula_size(f: Formula, var: nat)
    ensures subst_traversal_cost(f, var) <= formula_size(f),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_subst_cost_le_formula_size(*sub, var); },
        Formula::And { left, right } => {
            lemma_subst_cost_le_formula_size(*left, var);
            lemma_subst_cost_le_formula_size(*right, var);
        },
        Formula::Or { left, right } => {
            lemma_subst_cost_le_formula_size(*left, var);
            lemma_subst_cost_le_formula_size(*right, var);
        },
        Formula::Implies { left, right } => {
            lemma_subst_cost_le_formula_size(*left, var);
            lemma_subst_cost_le_formula_size(*right, var);
        },
        Formula::Iff { left, right } => {
            lemma_subst_cost_le_formula_size(*left, var);
            lemma_subst_cost_le_formula_size(*right, var);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {} else {
                lemma_subst_cost_le_formula_size(*sub, var);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {} else {
                lemma_subst_cost_le_formula_size(*sub, var);
            }
        },
    }
}

///  encode(f) >= subst_traversal_cost(f, var) when encode(f) > 0.
///  Proof: pair(tag, content) >= tag + content >= subst_cost by induction.
///  Edge case: Eq(Var(0), Var(0)) has encode=0, cost=1 — excluded by precondition.
pub proof fn lemma_encode_ge_subst_cost(f: Formula, var: nat)
    requires encode(f) != 0,
    ensures encode(f) >= subst_traversal_cost(f, var),
    decreases f,
{
    lemma_encode_is_pair(f);
    match f {
        Formula::Eq { .. } => {
            //  encode(f) >= 1 (since encode(f) != 0) and subst_cost = 1
            lemma_subst_traversal_cost_pos(f, var);
        },
        Formula::In { left, right } => {
            //  encode = pair(1, ...) >= 1 = subst_cost
            lemma_pair_ge_sum(1nat, pair(encode_term(left), encode_term(right)));
        },
        Formula::Not { sub } => {
            //  encode = pair(2, encode(sub)) >= 2 + encode(sub)
            //  subst_cost = 1 + subst_cost(sub) <= 1 + encode(sub) (by induction or edge case)
            lemma_pair_ge_sum(2nat, encode(*sub));
            if encode(*sub) != 0 {
                lemma_encode_ge_subst_cost(*sub, var);
            } else {
                //  sub = Eq(Var(0), Var(0)), subst_cost(sub) = 1, encode(sub) = 0
                //  2 + 0 = 2 >= 1 + 1 = subst_cost(f)
            }
        },
        Formula::And { left, right } => {
            lemma_pair_ge_sum(3nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_subst_cost(*left, var); }
            else { lemma_subst_traversal_cost_pos(*left, var); }
            if encode(*right) != 0 { lemma_encode_ge_subst_cost(*right, var); }
            else { lemma_subst_traversal_cost_pos(*right, var); }
        },
        Formula::Or { left, right } => {
            lemma_pair_ge_sum(4nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_subst_cost(*left, var); }
            else { lemma_subst_traversal_cost_pos(*left, var); }
            if encode(*right) != 0 { lemma_encode_ge_subst_cost(*right, var); }
            else { lemma_subst_traversal_cost_pos(*right, var); }
        },
        Formula::Implies { left, right } => {
            lemma_pair_ge_sum(5nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_subst_cost(*left, var); }
            else { lemma_subst_traversal_cost_pos(*left, var); }
            if encode(*right) != 0 { lemma_encode_ge_subst_cost(*right, var); }
            else { lemma_subst_traversal_cost_pos(*right, var); }
        },
        Formula::Iff { left, right } => {
            lemma_pair_ge_sum(6nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_subst_cost(*left, var); }
            else { lemma_subst_traversal_cost_pos(*left, var); }
            if encode(*right) != 0 { lemma_encode_ge_subst_cost(*right, var); }
            else { lemma_subst_traversal_cost_pos(*right, var); }
        },
        Formula::Forall { var: v, sub } => {
            lemma_pair_ge_sum(7nat, pair(v, encode(*sub)));
            lemma_pair_ge_sum(v, encode(*sub));
            if v == var {
                //  subst_cost = 1, encode >= 7 + v + encode(sub) >= 7 >= 1
            } else {
                if encode(*sub) != 0 { lemma_encode_ge_subst_cost(*sub, var); }
                else { lemma_subst_traversal_cost_pos(*sub, var); }
            }
        },
        Formula::Exists { var: v, sub } => {
            lemma_pair_ge_sum(8nat, pair(v, encode(*sub)));
            lemma_pair_ge_sum(v, encode(*sub));
            if v == var {
            } else {
                if encode(*sub) != 0 { lemma_encode_ge_subst_cost(*sub, var); }
                else { lemma_subst_traversal_cost_pos(*sub, var); }
            }
        },
    }
}

///  Traversal cost is bounded by formula size.
pub proof fn lemma_traversal_cost_le_size(f: Formula, v: nat)
    ensures
        traversal_cost(f, v) <= formula_size(f),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_traversal_cost_le_size(*sub, v); },
        Formula::And { left, right } => {
            lemma_traversal_cost_le_size(*left, v);
            lemma_traversal_cost_le_size(*right, v);
        },
        Formula::Or { left, right } => {
            lemma_traversal_cost_le_size(*left, v);
            lemma_traversal_cost_le_size(*right, v);
        },
        Formula::Implies { left, right } => {
            lemma_traversal_cost_le_size(*left, v);
            lemma_traversal_cost_le_size(*right, v);
        },
        Formula::Iff { left, right } => {
            lemma_traversal_cost_le_size(*left, v);
            lemma_traversal_cost_le_size(*right, v);
        },
        Formula::Forall { var, sub } => { lemma_traversal_cost_le_size(*sub, v); },
        Formula::Exists { var, sub } => { lemma_traversal_cost_le_size(*sub, v); },
    }
}

///  Traversal cost is always >= 1.
pub proof fn lemma_traversal_cost_pos(f: Formula, v: nat)
    ensures
        traversal_cost(f, v) >= 1,
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        _ => {},
    }
}

///  For sentences: encode(f) >= traversal_cost(f, v).
///  Sentences can't be atomic Eq/In (they have free vars), so tag >= 2.
///  Uses pair(a, b) >= a + b to show encode grows at least as fast as cost.
pub proof fn lemma_sentence_encode_ge_cost(f: Formula, v: nat)
    requires
        is_sentence(f),
    ensures
        encode(f) >= traversal_cost(f, v),
{
    //  Sentences can't be Eq or In (those have non-empty free_vars).
    //  So encode(f) != 0 (only Eq(Var(0),Var(0)) has encode 0, and it's not a sentence).
    lemma_sentence_no_free_var(f, v);
    //  Sentences can't be Eq or In — those have non-empty free_vars.
    //  So tag >= 2, encode >= 2 > 0.
    lemma_encode_is_pair(f);
    lemma_pair_ge_sum(formula_tag(f), formula_content(f));
    assert(formula_tag(f) >= 2nat) by {
        match f {
            Formula::Eq { left, right } => {
                //  Contradiction: free_vars non-empty but is_sentence requires empty
                assert(free_vars(f).contains(encode_term(left)));
            },
            Formula::In { left, right } => {
                assert(free_vars(f).contains(encode_term(left)));
            },
            _ => {},
        }
    }
    lemma_encode_ge_cost_inner(f, v);
}

///  Inner helper: encode(f) >= traversal_cost(f, v) when !has_free_var(f, v)
///  and f is not Eq(Var(0), Var(0)).
///  For the Eq(Var(0), Var(0)) edge case, encode = 0 < 1 = cost.
///  But this formula is never a sentence.
pub proof fn lemma_encode_ge_cost_inner(f: Formula, v: nat)
    requires
        !has_free_var(f, v),
        //  Exclude the one edge case: Eq(Var(0), Var(0))
        !(encode(f) == 0nat),
    ensures
        encode(f) >= traversal_cost(f, v),
    decreases f,
{
    match f {
        Formula::Eq { left, right } => {
            //  encode = pair(0, pair(a, b)) >= 1 (since encode > 0 by precondition)
            //  cost = 1. So encode >= 1 = cost. ✓
        },
        Formula::In { left, right } => {
            //  encode = pair(1, pair(a, b)) >= 1. cost = 1. ✓
            lemma_pair_gt_components(1nat, pair(encode_term(left), encode_term(right)));
        },
        Formula::Not { sub } => {
            lemma_has_free_var_not(*sub, v);
            //  encode(f) = pair(2, encode(sub)). cost = 1 + cost(sub).
            //  pair(2, x) >= 2 + x (from pair_ge_sum).
            //  If encode(sub) > 0: by IH, encode(sub) >= cost(sub).
            //    So encode(f) >= 2 + encode(sub) >= 2 + cost(sub) > 1 + cost(sub) = cost(f). ✓
            //  If encode(sub) == 0: encode(f) = pair(2, 0) = 5. cost(sub) = 1. cost(f) = 2. 5 >= 2. ✓
            lemma_pair_ge_sum(2nat, encode(*sub));
            if encode(*sub) > 0 {
                lemma_encode_ge_cost_inner(*sub, v);
            }
        },
        Formula::And { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            lemma_pair_ge_sum(3nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) > 0 { lemma_encode_ge_cost_inner(*left, v); }
            if encode(*right) > 0 { lemma_encode_ge_cost_inner(*right, v); }
            lemma_traversal_cost_pos(*left, v);
            lemma_traversal_cost_pos(*right, v);
        },
        Formula::Or { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            lemma_pair_ge_sum(4nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) > 0 { lemma_encode_ge_cost_inner(*left, v); }
            if encode(*right) > 0 { lemma_encode_ge_cost_inner(*right, v); }
            lemma_traversal_cost_pos(*left, v);
            lemma_traversal_cost_pos(*right, v);
        },
        Formula::Implies { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            lemma_pair_ge_sum(5nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) > 0 { lemma_encode_ge_cost_inner(*left, v); }
            if encode(*right) > 0 { lemma_encode_ge_cost_inner(*right, v); }
            lemma_traversal_cost_pos(*left, v);
            lemma_traversal_cost_pos(*right, v);
        },
        Formula::Iff { left, right } => {
            lemma_has_free_var_binary(*left, *right, v);
            lemma_encode_is_pair(f);
            lemma_pair_ge_sum(6nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) > 0 { lemma_encode_ge_cost_inner(*left, v); }
            if encode(*right) > 0 { lemma_encode_ge_cost_inner(*right, v); }
            lemma_traversal_cost_pos(*left, v);
            lemma_traversal_cost_pos(*right, v);
        },
        Formula::Forall { var, sub } => {
            lemma_has_free_var_quantifier(var, *sub, v);
            lemma_encode_is_pair(f);
            lemma_pair_ge_sum(7nat, pair(var, encode(*sub)));
            lemma_pair_ge_sum(var, encode(*sub));
            if var != v {
                if encode(*sub) > 0 { lemma_encode_ge_cost_inner(*sub, v); }
                lemma_traversal_cost_pos(*sub, v);
            }
        },
        Formula::Exists { var, sub } => {
            lemma_has_free_var_quantifier(var, *sub, v);
            lemma_encode_is_pair(f);
            lemma_pair_ge_sum(8nat, pair(var, encode(*sub)));
            lemma_pair_ge_sum(var, encode(*sub));
            if var != v {
                if encode(*sub) > 0 { lemma_encode_ge_cost_inner(*sub, v); }
                lemma_traversal_cost_pos(*sub, v);
            }
        },
    }
}

///  has_free_var for atomic formulas (Eq, In).
pub proof fn lemma_has_free_var_atomic(left: Term, right: Term, v: nat)
    ensures
        has_free_var(Formula::Eq { left, right }, v)
            == (encode_term(left) == v || encode_term(right) == v),
        has_free_var(Formula::In { left, right }, v)
            == (encode_term(left) == v || encode_term(right) == v),
{
}

//  ============================================================
//  Substitution
//  ============================================================

///  Substitute term t for variable var in a term.
pub open spec fn subst_term(term: Term, var: nat, t: Term) -> Term {
    match term {
        Term::Var { index } => if index == var { t } else { term },
    }
}

///  Substitute term t for variable var in a formula (naive, no capture avoidance).
pub open spec fn subst(f: Formula, var: nat, t: Term) -> Formula
    decreases f,
{
    match f {
        Formula::Eq { left, right } =>
            Formula::Eq { left: subst_term(left, var, t), right: subst_term(right, var, t) },
        Formula::In { left, right } =>
            Formula::In { left: subst_term(left, var, t), right: subst_term(right, var, t) },
        Formula::Not { sub } =>
            Formula::Not { sub: Box::new(subst(*sub, var, t)) },
        Formula::And { left, right } =>
            Formula::And { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Or { left, right } =>
            Formula::Or { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Implies { left, right } =>
            Formula::Implies { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Iff { left, right } =>
            Formula::Iff { left: Box::new(subst(*left, var, t)), right: Box::new(subst(*right, var, t)) },
        Formula::Forall { var: v, sub } =>
            if v == var { f } else { Formula::Forall { var: v, sub: Box::new(subst(*sub, var, t)) } },
        Formula::Exists { var: v, sub } =>
            if v == var { f } else { Formula::Exists { var: v, sub: Box::new(subst(*sub, var, t)) } },
    }
}

//  ============================================================
//  Helper constructors
//  ============================================================

pub open spec fn mk_var(i: nat) -> Term {
    Term::Var { index: i }
}

pub open spec fn mk_eq(left: Term, right: Term) -> Formula {
    Formula::Eq { left, right }
}

pub open spec fn mk_in(left: Term, right: Term) -> Formula {
    Formula::In { left, right }
}

pub open spec fn mk_not(f: Formula) -> Formula {
    Formula::Not { sub: Box::new(f) }
}

pub open spec fn mk_and(left: Formula, right: Formula) -> Formula {
    Formula::And { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_or(left: Formula, right: Formula) -> Formula {
    Formula::Or { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_implies(left: Formula, right: Formula) -> Formula {
    Formula::Implies { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_iff(left: Formula, right: Formula) -> Formula {
    Formula::Iff { left: Box::new(left), right: Box::new(right) }
}

pub open spec fn mk_forall(var: nat, sub: Formula) -> Formula {
    Formula::Forall { var, sub: Box::new(sub) }
}

pub open spec fn mk_exists(var: nat, sub: Formula) -> Formula {
    Formula::Exists { var, sub: Box::new(sub) }
}

//  ============================================================
//  Gödel encoding
//  ============================================================

///  Encode a term as a natural number.
pub open spec fn encode_term(t: Term) -> nat {
    match t {
        Term::Var { index } => index,
    }
}

///  Encode a formula as a natural number using Cantor pairing.
///  Tags: 0=Eq, 1=In, 2=Not, 3=And, 4=Or, 5=Implies, 6=Iff, 7=Forall, 8=Exists
pub open spec fn encode(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { left, right } =>
            pair(0, pair(encode_term(left), encode_term(right))),
        Formula::In { left, right } =>
            pair(1, pair(encode_term(left), encode_term(right))),
        Formula::Not { sub } =>
            pair(2, encode(*sub)),
        Formula::And { left, right } =>
            pair(3, pair(encode(*left), encode(*right))),
        Formula::Or { left, right } =>
            pair(4, pair(encode(*left), encode(*right))),
        Formula::Implies { left, right } =>
            pair(5, pair(encode(*left), encode(*right))),
        Formula::Iff { left, right } =>
            pair(6, pair(encode(*left), encode(*right))),
        Formula::Forall { var, sub } =>
            pair(7, pair(var, encode(*sub))),
        Formula::Exists { var, sub } =>
            pair(8, pair(var, encode(*sub))),
    }
}

///  Gödel encoding is injective.
pub proof fn lemma_encode_injective(f1: Formula, f2: Formula)
    requires
        encode(f1) == encode(f2),
    ensures
        f1 == f2,
    decreases f1,
{
    //  Different tags => different first component of outer pair => contradiction
    //  Same tag => inner pair equal => recursive injectivity
    match f1 {
        Formula::Eq { left: l1, right: r1 } => {
            //  encode(f1) = pair(0, pair(encode_term(l1), encode_term(r1)))
            //  f2 must also have tag 0
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Eq { left: l2, right: r2 } => {
                    lemma_pair_injective(0, pair(encode_term(l1), encode_term(r1)),
                                         0, pair(encode_term(l2), encode_term(r2)));
                    lemma_pair_injective(encode_term(l1), encode_term(r1),
                                         encode_term(l2), encode_term(r2));
                },
                _ => {},
            }
        },
        Formula::In { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::In { left: l2, right: r2 } => {
                    lemma_pair_injective(1, pair(encode_term(l1), encode_term(r1)),
                                         1, pair(encode_term(l2), encode_term(r2)));
                    lemma_pair_injective(encode_term(l1), encode_term(r1),
                                         encode_term(l2), encode_term(r2));
                },
                _ => {},
            }
        },
        Formula::Not { sub: s1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Not { sub: s2 } => {
                    lemma_pair_injective(2, encode(*s1), 2, encode(*s2));
                    lemma_encode_injective(*s1, *s2);
                },
                _ => {},
            }
        },
        Formula::And { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::And { left: l2, right: r2 } => {
                    lemma_pair_injective(3, pair(encode(*l1), encode(*r1)),
                                         3, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Or { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Or { left: l2, right: r2 } => {
                    lemma_pair_injective(4, pair(encode(*l1), encode(*r1)),
                                         4, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Implies { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Implies { left: l2, right: r2 } => {
                    lemma_pair_injective(5, pair(encode(*l1), encode(*r1)),
                                         5, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Iff { left: l1, right: r1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Iff { left: l2, right: r2 } => {
                    lemma_pair_injective(6, pair(encode(*l1), encode(*r1)),
                                         6, pair(encode(*l2), encode(*r2)));
                    lemma_pair_injective(encode(*l1), encode(*r1),
                                         encode(*l2), encode(*r2));
                    lemma_encode_injective(*l1, *l2);
                    lemma_encode_injective(*r1, *r2);
                },
                _ => {},
            }
        },
        Formula::Forall { var: v1, sub: s1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Forall { var: v2, sub: s2 } => {
                    lemma_pair_injective(7, pair(v1, encode(*s1)),
                                         7, pair(v2, encode(*s2)));
                    lemma_pair_injective(v1, encode(*s1), v2, encode(*s2));
                    lemma_encode_injective(*s1, *s2);
                },
                _ => {},
            }
        },
        Formula::Exists { var: v1, sub: s1 } => {
            lemma_tag_determines_variant(f1, f2);
            match f2 {
                Formula::Exists { var: v2, sub: s2 } => {
                    lemma_pair_injective(8, pair(v1, encode(*s1)),
                                         8, pair(v2, encode(*s2)));
                    lemma_pair_injective(v1, encode(*s1), v2, encode(*s2));
                    lemma_encode_injective(*s1, *s2);
                },
                _ => {},
            }
        },
    }
}

///  Helper: the tag (first component of pair) determines the formula variant.
///  If encode(f1) == encode(f2), they must have the same tag.
proof fn lemma_tag_determines_variant(f1: Formula, f2: Formula)
    requires
        encode(f1) == encode(f2),
    ensures
        formula_tag(f1) == formula_tag(f2),
{
    let t1 = formula_tag(f1);
    let c1 = formula_content(f1);
    let t2 = formula_tag(f2);
    let c2 = formula_content(f2);
    //  encode(f1) = pair(t1, c1) = pair(t2, c2) = encode(f2)
    assert(pair(t1, c1) == pair(t2, c2));
    lemma_pair_injective(t1, c1, t2, c2);
}

///  Extract the tag from a formula (matches encoding tag assignment).
pub open spec fn formula_tag(f: Formula) -> nat {
    match f {
        Formula::Eq { .. } => 0,
        Formula::In { .. } => 1,
        Formula::Not { .. } => 2,
        Formula::And { .. } => 3,
        Formula::Or { .. } => 4,
        Formula::Implies { .. } => 5,
        Formula::Iff { .. } => 6,
        Formula::Forall { .. } => 7,
        Formula::Exists { .. } => 8,
    }
}

///  Extract the content (second component of pair) from a formula encoding.
pub open spec fn formula_content(f: Formula) -> nat
    decreases f,
{
    match f {
        Formula::Eq { left, right } => pair(encode_term(left), encode_term(right)),
        Formula::In { left, right } => pair(encode_term(left), encode_term(right)),
        Formula::Not { sub } => encode(*sub),
        Formula::And { left, right } => pair(encode(*left), encode(*right)),
        Formula::Or { left, right } => pair(encode(*left), encode(*right)),
        Formula::Implies { left, right } => pair(encode(*left), encode(*right)),
        Formula::Iff { left, right } => pair(encode(*left), encode(*right)),
        Formula::Forall { var, sub } => pair(var, encode(*sub)),
        Formula::Exists { var, sub } => pair(var, encode(*sub)),
    }
}

///  encode(f) == pair(formula_tag(f), formula_content(f)).
pub proof fn lemma_encode_is_pair(f: Formula)
    ensures
        encode(f) == pair(formula_tag(f), formula_content(f)),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { .. } => {},
        Formula::And { .. } => {},
        Formula::Or { .. } => {},
        Formula::Implies { .. } => {},
        Formula::Iff { .. } => {},
        Formula::Forall { .. } => {},
        Formula::Exists { .. } => {},
    }
}

proof fn lemma_subst_tag_binary(tag: nat, el: nat, er: nat, sl: nat, sr: nat)
    requires tag >= 3 && tag <= 6,
    ensures
        unpair1(pair(tag, pair(el, er))) == unpair1(pair(tag, pair(sl, sr))),
{
    lemma_unpair1_pair(tag, pair(el, er));
    lemma_unpair1_pair(tag, pair(sl, sr));
}

proof fn lemma_subst_tag_atomic_unary(f: Formula, var: nat, t: Term)
    requires formula_tag(f) <= 2,
    ensures unpair1(encode(f)) == unpair1(encode(subst(f, var, t))),
{
    match f {
        Formula::Eq { left, right } => {
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(0nat, pair(encode_term(subst_term(left, var, t)),
                encode_term(subst_term(right, var, t))));
        },
        Formula::In { left, right } => {
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(1nat, pair(encode_term(subst_term(left, var, t)),
                encode_term(subst_term(right, var, t))));
        },
        Formula::Not { sub } => {
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair1_pair(2nat, encode(subst(*sub, var, t)));
        },
        _ => {},
    }
}

proof fn lemma_subst_tag_quantifier(f: Formula, var: nat, t: Term)
    requires formula_tag(f) >= 7,
    ensures unpair1(encode(f)) == unpair1(encode(subst(f, var, t))),
{
    match f {
        Formula::Forall { var: v, sub } => {
            lemma_unpair1_pair(7nat, pair(v, encode(*sub)));
            if v == var {} else {
                lemma_unpair1_pair(7nat, pair(v, encode(subst(*sub, var, t))));
            }
        },
        Formula::Exists { var: v, sub } => {
            lemma_unpair1_pair(8nat, pair(v, encode(*sub)));
            if v == var {} else {
                lemma_unpair1_pair(8nat, pair(v, encode(subst(*sub, var, t))));
            }
        },
        _ => {},
    }
}

proof fn lemma_subst_tag_compound(f: Formula, var: nat, t: Term)
    requires formula_tag(f) >= 3,
    ensures unpair1(encode(f)) == unpair1(encode(subst(f, var, t))),
{
    if formula_tag(f) >= 7 {
        lemma_subst_tag_quantifier(f, var, t);
    } else {
        match f {
            Formula::And { left, right } => {
                lemma_subst_tag_binary(3, encode(*left), encode(*right),
                    encode(subst(*left, var, t)), encode(subst(*right, var, t)));
            },
            Formula::Or { left, right } => {
                lemma_subst_tag_binary(4, encode(*left), encode(*right),
                    encode(subst(*left, var, t)), encode(subst(*right, var, t)));
            },
            Formula::Implies { left, right } => {
                lemma_subst_tag_binary(5, encode(*left), encode(*right),
                    encode(subst(*left, var, t)), encode(subst(*right, var, t)));
            },
            Formula::Iff { left, right } => {
                lemma_subst_tag_binary(6, encode(*left), encode(*right),
                    encode(subst(*left, var, t)), encode(subst(*right, var, t)));
            },
            _ => {},
        }
    }
}

///  Substitution preserves formula tags in the encoding.
pub proof fn lemma_subst_preserves_tag(f: Formula, var: nat, t: Term)
    ensures unpair1(encode(f)) == unpair1(encode(subst(f, var, t))),
    decreases f,
{
    match f {
        Formula::Eq { .. } | Formula::In { .. } | Formula::Not { .. } => {
            lemma_subst_tag_atomic_unary(f, var, t);
        },
        _ => {
            lemma_subst_tag_compound(f, var, t);
        },
    }
}

//  ============================================================
//  Decoding: reconstruct Formula from Gödel number
//  ============================================================

///  Decode a term from its Gödel number.
pub open spec fn decode_term(n: nat) -> Term {
    Term::Var { index: n }
}

///  Decode a formula from its Gödel number.
///  Dispatches on tag (unpair1) and recursively decodes sub-formulas.
pub open spec fn decode_formula(n: nat) -> Formula
    decreases n
    via decode_formula_decreases
{
    let tag = unpair1(n);
    let content = unpair2(n);
    if tag == 0 {
        Formula::Eq { left: decode_term(unpair1(content)), right: decode_term(unpair2(content)) }
    } else if tag == 1 {
        Formula::In { left: decode_term(unpair1(content)), right: decode_term(unpair2(content)) }
    } else if tag == 2 {
        Formula::Not { sub: Box::new(decode_formula(content)) }
    } else if tag == 3 {
        Formula::And { left: Box::new(decode_formula(unpair1(content))), right: Box::new(decode_formula(unpair2(content))) }
    } else if tag == 4 {
        Formula::Or { left: Box::new(decode_formula(unpair1(content))), right: Box::new(decode_formula(unpair2(content))) }
    } else if tag == 5 {
        Formula::Implies { left: Box::new(decode_formula(unpair1(content))), right: Box::new(decode_formula(unpair2(content))) }
    } else if tag == 6 {
        Formula::Iff { left: Box::new(decode_formula(unpair1(content))), right: Box::new(decode_formula(unpair2(content))) }
    } else if tag == 7 {
        Formula::Forall { var: unpair1(content), sub: Box::new(decode_formula(unpair2(content))) }
    } else if tag == 8 {
        Formula::Exists { var: unpair1(content), sub: Box::new(decode_formula(unpair2(content))) }
    } else {
        //  Default for invalid tags
        Formula::Eq { left: Term::Var { index: 0 }, right: Term::Var { index: 0 } }
    }
}

#[via_fn]
proof fn decode_formula_decreases(n: nat) {
    //  Show all recursive calls use strictly smaller arguments.
    //  For tags 1-8: content = unpair2(n) < n (since unpair1(n) >= 1).
    //  For binary (tags 3-6): unpair1(content) <= content < n and unpair2(content) <= content < n.
    if unpair1(n) >= 1 {
        lemma_unpair2_lt(n);
        lemma_unpair1_le(unpair2(n));
        lemma_unpair2_le(unpair2(n));
    }
}

///  Roundtrip: decode_term(encode_term(t)) == t.
pub proof fn lemma_decode_encode_term(t: Term)
    ensures decode_term(encode_term(t)) == t,
{
    match t { Term::Var { index } => {} }
}

///  Roundtrip: decode_formula(encode(f)) == f.
pub proof fn lemma_decode_encode_formula(f: Formula)
    ensures decode_formula(encode(f)) == f,
    decreases f,
{
    match f {
        Formula::Eq { left, right } => {
            lemma_unpair1_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair2_pair(0nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(encode_term(left), encode_term(right));
            lemma_unpair2_pair(encode_term(left), encode_term(right));
            lemma_decode_encode_term(left);
            lemma_decode_encode_term(right);
        },
        Formula::In { left, right } => {
            lemma_unpair1_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair2_pair(1nat, pair(encode_term(left), encode_term(right)));
            lemma_unpair1_pair(encode_term(left), encode_term(right));
            lemma_unpair2_pair(encode_term(left), encode_term(right));
            lemma_decode_encode_term(left);
            lemma_decode_encode_term(right);
        },
        Formula::Not { sub } => {
            lemma_unpair1_pair(2nat, encode(*sub));
            lemma_unpair2_pair(2nat, encode(*sub));
            lemma_decode_encode_formula(*sub);
        },
        Formula::And { left, right } => {
            lemma_unpair1_pair(3nat, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(3nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(encode(*left), encode(*right));
            lemma_unpair2_pair(encode(*left), encode(*right));
            lemma_decode_encode_formula(*left);
            lemma_decode_encode_formula(*right);
        },
        Formula::Or { left, right } => {
            lemma_unpair1_pair(4nat, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(4nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(encode(*left), encode(*right));
            lemma_unpair2_pair(encode(*left), encode(*right));
            lemma_decode_encode_formula(*left);
            lemma_decode_encode_formula(*right);
        },
        Formula::Implies { left, right } => {
            lemma_unpair1_pair(5nat, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(5nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(encode(*left), encode(*right));
            lemma_unpair2_pair(encode(*left), encode(*right));
            lemma_decode_encode_formula(*left);
            lemma_decode_encode_formula(*right);
        },
        Formula::Iff { left, right } => {
            lemma_unpair1_pair(6nat, pair(encode(*left), encode(*right)));
            lemma_unpair2_pair(6nat, pair(encode(*left), encode(*right)));
            lemma_unpair1_pair(encode(*left), encode(*right));
            lemma_unpair2_pair(encode(*left), encode(*right));
            lemma_decode_encode_formula(*left);
            lemma_decode_encode_formula(*right);
        },
        Formula::Forall { var, sub } => {
            lemma_unpair1_pair(7nat, pair(var, encode(*sub)));
            lemma_unpair2_pair(7nat, pair(var, encode(*sub)));
            lemma_unpair1_pair(var, encode(*sub));
            lemma_unpair2_pair(var, encode(*sub));
            lemma_decode_encode_formula(*sub);
        },
        Formula::Exists { var, sub } => {
            lemma_unpair1_pair(8nat, pair(var, encode(*sub)));
            lemma_unpair2_pair(8nat, pair(var, encode(*sub)));
            lemma_unpair1_pair(var, encode(*sub));
            lemma_unpair2_pair(var, encode(*sub));
            lemma_decode_encode_formula(*sub);
        },
    }
}

///  Encode-after-decode roundtrip for valid formula encodings.
///  If n is in the image of encode, then encode(decode_formula(n)) == n.
pub proof fn lemma_encode_decode_formula(n: nat)
    requires exists|f: Formula| encode(f) == n,
    ensures encode(decode_formula(n)) == n,
{
    let f: Formula = choose|f: Formula| encode(f) == n;
    lemma_decode_encode_formula(f);
    //  decode_formula(encode(f)) == f
    //  So encode(decode_formula(n)) == encode(decode_formula(encode(f))) == encode(f) == n
}


//  ============================================================
//  Eq-subst compatibility: two formulas with same structure,
//  differing only at term positions where one has x and other has y.
//  ============================================================

pub open spec fn eq_subst_term_compatible(t1: Term, t2: Term, x: Term, y: Term) -> bool {
    t1 == t2 || (t1 == x && t2 == y)
}

pub open spec fn eq_subst_compatible(f1: Formula, f2: Formula, x: Term, y: Term) -> bool
    decreases f1,
{
    match f1 {
        Formula::Eq { left: l1, right: r1 } => match f2 {
            Formula::Eq { left: l2, right: r2 } =>
                eq_subst_term_compatible(l1, l2, x, y) && eq_subst_term_compatible(r1, r2, x, y),
            _ => false,
        },
        Formula::In { left: l1, right: r1 } => match f2 {
            Formula::In { left: l2, right: r2 } =>
                eq_subst_term_compatible(l1, l2, x, y) && eq_subst_term_compatible(r1, r2, x, y),
            _ => false,
        },
        Formula::Not { sub: s1 } => match f2 {
            Formula::Not { sub: s2 } => eq_subst_compatible(*s1, *s2, x, y),
            _ => false,
        },
        Formula::And { left: l1, right: r1 } => match f2 {
            Formula::And { left: l2, right: r2 } =>
                eq_subst_compatible(*l1, *l2, x, y) && eq_subst_compatible(*r1, *r2, x, y),
            _ => false,
        },
        Formula::Or { left: l1, right: r1 } => match f2 {
            Formula::Or { left: l2, right: r2 } =>
                eq_subst_compatible(*l1, *l2, x, y) && eq_subst_compatible(*r1, *r2, x, y),
            _ => false,
        },
        Formula::Implies { left: l1, right: r1 } => match f2 {
            Formula::Implies { left: l2, right: r2 } =>
                eq_subst_compatible(*l1, *l2, x, y) && eq_subst_compatible(*r1, *r2, x, y),
            _ => false,
        },
        Formula::Iff { left: l1, right: r1 } => match f2 {
            Formula::Iff { left: l2, right: r2 } =>
                eq_subst_compatible(*l1, *l2, x, y) && eq_subst_compatible(*r1, *r2, x, y),
            _ => false,
        },
        Formula::Forall { var: v1, sub: s1 } => match f2 {
            Formula::Forall { var: v2, sub: s2 } =>
                v1 == v2 && eq_subst_compatible(*s1, *s2, x, y),
            _ => false,
        },
        Formula::Exists { var: v1, sub: s1 } => match f2 {
            Formula::Exists { var: v2, sub: s2 } =>
                v1 == v2 && eq_subst_compatible(*s1, *s2, x, y),
            _ => false,
        },
    }
}

///  Compatible formulas have the same size.
pub proof fn lemma_eq_subst_compatible_same_size(f1: Formula, f2: Formula, x: Term, y: Term)
    requires eq_subst_compatible(f1, f2, x, y),
    ensures formula_size(f1) == formula_size(f2),
    decreases f1,
{
    match f1 {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub: s1 } => match f2 {
            Formula::Not { sub: s2 } => { lemma_eq_subst_compatible_same_size(*s1, *s2, x, y); },
            _ => {},
        },
        Formula::And { left: l1, right: r1 } => match f2 {
            Formula::And { left: l2, right: r2 } => {
                lemma_eq_subst_compatible_same_size(*l1, *l2, x, y);
                lemma_eq_subst_compatible_same_size(*r1, *r2, x, y);
            },
            _ => {},
        },
        Formula::Or { left: l1, right: r1 } => match f2 {
            Formula::Or { left: l2, right: r2 } => {
                lemma_eq_subst_compatible_same_size(*l1, *l2, x, y);
                lemma_eq_subst_compatible_same_size(*r1, *r2, x, y);
            },
            _ => {},
        },
        Formula::Implies { left: l1, right: r1 } => match f2 {
            Formula::Implies { left: l2, right: r2 } => {
                lemma_eq_subst_compatible_same_size(*l1, *l2, x, y);
                lemma_eq_subst_compatible_same_size(*r1, *r2, x, y);
            },
            _ => {},
        },
        Formula::Iff { left: l1, right: r1 } => match f2 {
            Formula::Iff { left: l2, right: r2 } => {
                lemma_eq_subst_compatible_same_size(*l1, *l2, x, y);
                lemma_eq_subst_compatible_same_size(*r1, *r2, x, y);
            },
            _ => {},
        },
        Formula::Forall { var: v1, sub: s1 } => match f2 {
            Formula::Forall { var: v2, sub: s2 } => {
                lemma_eq_subst_compatible_same_size(*s1, *s2, x, y);
            },
            _ => {},
        },
        Formula::Exists { var: v1, sub: s1 } => match f2 {
            Formula::Exists { var: v2, sub: s2 } => {
                lemma_eq_subst_compatible_same_size(*s1, *s2, x, y);
            },
            _ => {},
        },
    }
}

///  Any formula is eq_subst_compatible with itself (at term level, t == t always holds).
pub proof fn lemma_eq_subst_compatible_reflexive(f: Formula, x: Term, y: Term)
    ensures eq_subst_compatible(f, f, x, y),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_eq_subst_compatible_reflexive(*sub, x, y); },
        Formula::And { left, right } => {
            lemma_eq_subst_compatible_reflexive(*left, x, y);
            lemma_eq_subst_compatible_reflexive(*right, x, y);
        },
        Formula::Or { left, right } => {
            lemma_eq_subst_compatible_reflexive(*left, x, y);
            lemma_eq_subst_compatible_reflexive(*right, x, y);
        },
        Formula::Implies { left, right } => {
            lemma_eq_subst_compatible_reflexive(*left, x, y);
            lemma_eq_subst_compatible_reflexive(*right, x, y);
        },
        Formula::Iff { left, right } => {
            lemma_eq_subst_compatible_reflexive(*left, x, y);
            lemma_eq_subst_compatible_reflexive(*right, x, y);
        },
        Formula::Forall { var, sub } => { lemma_eq_subst_compatible_reflexive(*sub, x, y); },
        Formula::Exists { var, sub } => { lemma_eq_subst_compatible_reflexive(*sub, x, y); },
    }
}

///  subst(phi, var, x) and subst(phi, var, y) are eq_subst_compatible.
pub proof fn lemma_subst_eq_subst_compatible(phi: Formula, var: nat, x: Term, y: Term)
    ensures eq_subst_compatible(subst(phi, var, x), subst(phi, var, y), x, y),
    decreases phi,
{
    match phi {
        Formula::Eq { left, right } => {
            //  subst_term cases: if index == var → (x, y) compatible; else → (t, t) compatible
        },
        Formula::In { left, right } => {},
        Formula::Not { sub } => { lemma_subst_eq_subst_compatible(*sub, var, x, y); },
        Formula::And { left, right } => {
            lemma_subst_eq_subst_compatible(*left, var, x, y);
            lemma_subst_eq_subst_compatible(*right, var, x, y);
        },
        Formula::Or { left, right } => {
            lemma_subst_eq_subst_compatible(*left, var, x, y);
            lemma_subst_eq_subst_compatible(*right, var, x, y);
        },
        Formula::Implies { left, right } => {
            lemma_subst_eq_subst_compatible(*left, var, x, y);
            lemma_subst_eq_subst_compatible(*right, var, x, y);
        },
        Formula::Iff { left, right } => {
            lemma_subst_eq_subst_compatible(*left, var, x, y);
            lemma_subst_eq_subst_compatible(*right, var, x, y);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {
                //  subst returns phi unchanged → both sides identical → reflexive
                lemma_eq_subst_compatible_reflexive(phi, x, y);
            } else {
                lemma_subst_eq_subst_compatible(*sub, var, x, y);
            }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {
                lemma_eq_subst_compatible_reflexive(phi, x, y);
            } else {
                lemma_subst_eq_subst_compatible(*sub, var, x, y);
            }
        },
    }
}

///  Substitution preserves formula size.
pub proof fn lemma_subst_preserves_size(f: Formula, var: nat, t: Term)
    ensures formula_size(subst(f, var, t)) == formula_size(f),
    decreases f,
{
    match f {
        Formula::Eq { .. } => {},
        Formula::In { .. } => {},
        Formula::Not { sub } => { lemma_subst_preserves_size(*sub, var, t); },
        Formula::And { left, right } => {
            lemma_subst_preserves_size(*left, var, t);
            lemma_subst_preserves_size(*right, var, t);
        },
        Formula::Or { left, right } => {
            lemma_subst_preserves_size(*left, var, t);
            lemma_subst_preserves_size(*right, var, t);
        },
        Formula::Implies { left, right } => {
            lemma_subst_preserves_size(*left, var, t);
            lemma_subst_preserves_size(*right, var, t);
        },
        Formula::Iff { left, right } => {
            lemma_subst_preserves_size(*left, var, t);
            lemma_subst_preserves_size(*right, var, t);
        },
        Formula::Forall { var: v, sub } => {
            if v == var {} else { lemma_subst_preserves_size(*sub, var, t); }
        },
        Formula::Exists { var: v, sub } => {
            if v == var {} else { lemma_subst_preserves_size(*sub, var, t); }
        },
    }
}

///  encode(f) >= formula_size(f) when encode(f) > 0.
pub proof fn lemma_encode_ge_formula_size(f: Formula)
    requires encode(f) != 0,
    ensures encode(f) >= formula_size(f),
    decreases f,
{
    lemma_encode_is_pair(f);
    match f {
        Formula::Eq { .. } => {},
        Formula::In { left, right } => {
            lemma_pair_ge_sum(1nat, pair(encode_term(left), encode_term(right)));
        },
        Formula::Not { sub } => {
            lemma_pair_ge_sum(2nat, encode(*sub));
            if encode(*sub) != 0 {
                lemma_encode_ge_formula_size(*sub);
            } else {
                lemma_formula_size_pos(*sub);
            }
        },
        Formula::And { left, right } => {
            lemma_pair_ge_sum(3nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_formula_size(*left); }
            else { lemma_formula_size_pos(*left); }
            if encode(*right) != 0 { lemma_encode_ge_formula_size(*right); }
            else { lemma_formula_size_pos(*right); }
        },
        Formula::Or { left, right } => {
            lemma_pair_ge_sum(4nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_formula_size(*left); }
            else { lemma_formula_size_pos(*left); }
            if encode(*right) != 0 { lemma_encode_ge_formula_size(*right); }
            else { lemma_formula_size_pos(*right); }
        },
        Formula::Implies { left, right } => {
            lemma_pair_ge_sum(5nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_formula_size(*left); }
            else { lemma_formula_size_pos(*left); }
            if encode(*right) != 0 { lemma_encode_ge_formula_size(*right); }
            else { lemma_formula_size_pos(*right); }
        },
        Formula::Iff { left, right } => {
            lemma_pair_ge_sum(6nat, pair(encode(*left), encode(*right)));
            lemma_pair_ge_sum(encode(*left), encode(*right));
            if encode(*left) != 0 { lemma_encode_ge_formula_size(*left); }
            else { lemma_formula_size_pos(*left); }
            if encode(*right) != 0 { lemma_encode_ge_formula_size(*right); }
            else { lemma_formula_size_pos(*right); }
        },
        Formula::Forall { var, sub } => {
            lemma_pair_ge_sum(7nat, pair(var, encode(*sub)));
            lemma_pair_ge_sum(var, encode(*sub));
            if encode(*sub) != 0 { lemma_encode_ge_formula_size(*sub); }
            else { lemma_formula_size_pos(*sub); }
        },
        Formula::Exists { var, sub } => {
            lemma_pair_ge_sum(8nat, pair(var, encode(*sub)));
            lemma_pair_ge_sum(var, encode(*sub));
            if encode(*sub) != 0 { lemma_encode_ge_formula_size(*sub); }
            else { lemma_formula_size_pos(*sub); }
        },
    }
}

} //  verus!
