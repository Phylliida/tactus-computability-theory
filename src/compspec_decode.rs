use vstd::prelude::*;
use crate::pairing::*;
use crate::computable::*;
use crate::formula::*;
use crate::proof_system::*;
use crate::proof_encoding::*;
use crate::zfc::*;
use crate::zfc_enumerator::*;
use crate::enumerator_computable::*;

verus! {

//  ============================================================
//  CompSpec helper constructors
//  ============================================================

///  BoundedRec step input: pair(i, pair(acc, original_input))
///  Extract the accumulator.
pub open spec fn br_acc() -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(
        CompSpec::CantorSnd { inner: Box::new(CompSpec::Id) }
    )}
}

///  BoundedRec step: scan to last element of encoded sequence.
///  If unpair2(acc) == 0: stay (at last element). Else: advance to unpair2(acc).
pub open spec fn seq_scan_step() -> CompSpec {
    CompSpec::IfZero {
        cond: Box::new(CompSpec::CantorSnd { inner: Box::new(br_acc()) }),
        then_br: Box::new(br_acc()),
        else_br: Box::new(CompSpec::CantorSnd { inner: Box::new(br_acc()) }),
    }
}

///  Scan to last pair in encoded nat sequence.
///  For s = encode_nat_seq([e1, ..., en]), returns pair(en + 1, 0).
pub open spec fn get_last_pair() -> CompSpec {
    CompSpec::BoundedRec {
        count_fn: Box::new(CompSpec::Id),
        base: Box::new(CompSpec::Id),
        step: Box::new(seq_scan_step()),
    }
}

///  Get last element from encoded nat sequence.
///  = unpair1(get_last_pair(s)) - 1
pub open spec fn last_seq_elem() -> CompSpec {
    CompSpec::Comp {
        outer: Box::new(CompSpec::Pred),
        inner: Box::new(CompSpec::CantorFst {
            inner: Box::new(get_last_pair()),
        }),
    }
}

///  Get formula encoding from last encoded proof line.
///  encode_line = pair(encode_formula, encode_justification)
///  So formula_enc = unpair1(last_seq_elem(s))
pub open spec fn last_formula_enc() -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(last_seq_elem()) }
}

///  Get Iff data from formula encoding.
///  For Iff: encode(Iff{l,r}) = pair(6, pair(encode(l), encode(r)))
///  iff_data = unpair2(formula_enc) = pair(encode(l), encode(r))
pub open spec fn iff_data() -> CompSpec {
    CompSpec::CantorSnd { inner: Box::new(last_formula_enc()) }
}

//  ============================================================
//  Concrete CompSpec terms for output extraction
//  ============================================================

///  CompSpec for output1: extract encode(left) from valid proof code.
///  = unpair1(iff_data(s)) = unpair1(unpair2(unpair1(last_elem(s))))
pub open spec fn output1_comp_term() -> CompSpec {
    CompSpec::CantorFst { inner: Box::new(iff_data()) }
}

///  CompSpec for output2: extract encode(right) from valid proof code.
///  = unpair2(iff_data(s)) = unpair2(unpair2(unpair1(last_elem(s))))
pub open spec fn output2_comp_term() -> CompSpec {
    CompSpec::CantorSnd { inner: Box::new(iff_data()) }
}

//  ============================================================
//  Correctness: scan step evaluates correctly
//  ============================================================

///  The scan step advances through the sequence or stays at last element.
proof fn lemma_seq_scan_step_eval(acc: nat, i: nat, input: nat)
    ensures
        eval_comp(seq_scan_step(), pair(i, pair(acc, input))) ==
            if unpair2(acc) == 0 { acc } else { unpair2(acc) },
{
    let x = pair(i, pair(acc, input));
    assert(eval_comp(br_acc(), x) == acc) by {
        lemma_unpair1_pair(acc, input);
        lemma_unpair2_pair(i, pair(acc, input));
    };
}

///  Once at a position with unpair2 == 0, scanning stays there.
proof fn lemma_scan_stays_at_last(acc: nat, fuel: nat, input: nat)
    requires
        unpair2(acc) == 0,
    ensures
        iterate(
            |x: nat| eval_comp(seq_scan_step(), x),
            fuel, acc, input) == acc,
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let step_fn = |x: nat| eval_comp(seq_scan_step(), x);
        lemma_seq_scan_step_eval(acc, (fuel - 1) as nat, input);
        assert(step_fn(pair((fuel - 1) as nat, pair(acc, input))) == acc);
        lemma_scan_stays_at_last(acc, (fuel - 1) as nat, input);
    }
}

//  ============================================================
//  Helper: iterate is input-independent for our scan step
//  ============================================================

///  Our scan step only depends on acc, not on the original input.
///  So iterate produces the same result regardless of the input parameter.
proof fn lemma_iterate_input_independent(fuel: nat, acc: nat, input1: nat, input2: nat)
    ensures
        iterate(
            |x: nat| eval_comp(seq_scan_step(), x), fuel, acc, input1)
        == iterate(
            |x: nat| eval_comp(seq_scan_step(), x), fuel, acc, input2),
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let step_fn = |x: nat| eval_comp(seq_scan_step(), x);
        lemma_seq_scan_step_eval(acc, (fuel - 1) as nat, input1);
        lemma_seq_scan_step_eval(acc, (fuel - 1) as nat, input2);
        let next_acc = if unpair2(acc) == 0 { acc } else { unpair2(acc) };
        lemma_iterate_input_independent(
            (fuel - 1) as nat, next_acc, input1, input2);
    }
}

///  Extra fuel beyond convergence doesn't change the result.
proof fn lemma_iterate_extra_fuel(fuel1: nat, fuel2: nat, acc: nat, input: nat)
    requires
        fuel2 >= fuel1,
        unpair2(iterate(
            |x: nat| eval_comp(seq_scan_step(), x), fuel1, acc, input)) == 0,
    ensures
        iterate(
            |x: nat| eval_comp(seq_scan_step(), x), fuel2, acc, input)
        == iterate(
            |x: nat| eval_comp(seq_scan_step(), x), fuel1, acc, input),
    decreases fuel2,
{
    let step_fn = |x: nat| eval_comp(seq_scan_step(), x);
    if fuel2 == fuel1 {
    } else if fuel1 == 0 {
        //  iterate at fuel1=0 returns acc, and unpair2(acc) == 0
        //  iterate at fuel2 stays at acc by lemma_scan_stays_at_last
        lemma_scan_stays_at_last(acc, fuel2, input);
    } else {
        //  Both take one step: same next_acc
        lemma_seq_scan_step_eval(acc, (fuel1 - 1) as nat, input);
        lemma_seq_scan_step_eval(acc, (fuel2 - 1) as nat, input);
        let next_acc = if unpair2(acc) == 0 { acc } else { unpair2(acc) };
        if unpair2(acc) == 0 {
            //  Already at last, both stay
            lemma_scan_stays_at_last(acc, (fuel1 - 1) as nat, input);
            lemma_scan_stays_at_last(acc, (fuel2 - 1) as nat, input);
        } else {
            //  Both advance to next_acc = unpair2(acc)
            lemma_iterate_extra_fuel(
                (fuel1 - 1) as nat, (fuel2 - 1) as nat, next_acc, input);
        }
    }
}

//  ============================================================
//  Correctness: get_last_pair on encoded sequences
//  ============================================================

///  For encoded sequences, eval_comp(get_last_pair(), enc) correctly finds the last pair.
///  Result is encode_nat_seq(seq![last_element]) = pair(last_element + 1, 0).
pub proof fn lemma_get_last_pair_correct(s: Seq<nat>)
    requires
        s.len() > 0,
    ensures
        eval_comp(get_last_pair(), encode_nat_seq(s))
            == encode_nat_seq(seq![s[s.len() - 1]]),
    decreases s.len(),
{
    let enc = encode_nat_seq(s);
    let tail_seq = s.subrange(1, s.len() as int);
    let tail_enc = encode_nat_seq(tail_seq);
    let step_fn = |x: nat| eval_comp(seq_scan_step(), x);
    lemma_encode_nat_seq_structure(s);

    //  eval_comp(get_last_pair(), enc) = iterate(step_fn, enc, enc, enc)

    if s.len() == 1 {
        //  unpair2(enc) == 0, so iterate stays at enc
        lemma_scan_stays_at_last(enc, enc, enc);
    } else {
        //  unpair2(enc) = tail_enc != 0, first step advances to tail_enc
        lemma_encode_nat_seq_nonempty(tail_seq);
        assert(tail_enc != 0);

        //  First step: iterate(enc, enc, enc) → iterate(enc-1, tail_enc, enc)
        lemma_encode_nat_seq_nonempty(s);
        lemma_seq_scan_step_eval(enc, (enc - 1) as nat, enc);

        //  Input independence: iterate(enc-1, tail_enc, enc) == iterate(enc-1, tail_enc, tail_enc)
        lemma_iterate_input_independent(
            (enc - 1) as nat, tail_enc, enc, tail_enc);

        //  By induction: iterate(tail_enc, tail_enc, tail_enc) == encode_nat_seq(seq![s.last()])
        lemma_get_last_pair_correct(tail_seq);
        assert(tail_seq[tail_seq.len() - 1] == s[s.len() - 1]);

        //  Fuel sufficiency: enc - 1 >= tail_enc, and tail_enc fuel is enough
        lemma_pair_pos_tag_gt_content(s[0] + 1, tail_enc);
        assert(enc > tail_enc);
        //  iterate(tail_enc, tail_enc, tail_enc) converges (unpair2 of result == 0)
        let result = iterate(step_fn, tail_enc, tail_enc, tail_enc);
        assert(result == encode_nat_seq(seq![s[s.len() - 1]]));
        lemma_encode_nat_seq_structure(seq![s[s.len() - 1]]);
        assert(unpair2(result) == 0);

        //  Extra fuel: iterate(enc-1, tail_enc, tail_enc) == iterate(tail_enc, tail_enc, tail_enc)
        lemma_iterate_extra_fuel(
            tail_enc, (enc - 1) as nat, tail_enc, tail_enc);
    }
}

//  ============================================================
//  Main output correctness proofs
//  ============================================================

///  Helper: trace eval_comp through the unpairing chain for a valid proof code.
pub proof fn lemma_output_eval_chain(s: nat, p: Proof)
    requires
        encode_proof(p) == s,
        p.lines.len() > 0,
        conclusion_is_iff_of_sentences(proof_conclusion(p)),
    ensures ({
        let conclusion = proof_conclusion(p);
        let (enc_left, enc_right) = extract_iff_pair(conclusion);
        eval_comp(output1_comp_term(), s) == enc_left &&
        eval_comp(output2_comp_term(), s) == enc_right
    }),
{
    let n = p.lines.len();
    let conclusion = proof_conclusion(p);
    let (enc_left, enc_right) = extract_iff_pair(conclusion);
    let last_line = p.lines[n - 1];
    assert(last_line.0 == conclusion);

    //  Step 1: Build the line encoding sequence
    let line_encs = Seq::new(n, |i: int| encode_line(p.lines[i]));
    assert(s == encode_nat_seq(line_encs));
    assert(line_encs.len() > 0);

    //  Step 2: get_last_pair(s) finds the last encoded line
    lemma_get_last_pair_correct(line_encs);
    let last_enc_line = line_encs[n - 1];
    assert(last_enc_line == encode_line(last_line));
    let last_pair = encode_nat_seq(seq![last_enc_line]);
    assert(eval_comp(get_last_pair(), s) == last_pair);

    //  Step 3: last_seq_elem(s) = Pred(unpair1(last_pair)) = last_enc_line
    lemma_encode_nat_seq_structure(seq![last_enc_line]);
    //  last_pair = pair(last_enc_line + 1, 0)
    //  unpair1(last_pair) = last_enc_line + 1
    //  Pred(last_enc_line + 1) = last_enc_line

    //  Step 4: last_formula_enc(s) = unpair1(last_enc_line) = encode(conclusion)
    //  last_enc_line = encode_line(last_line) = pair(encode(conclusion), encode_justification(last_line.1))
    lemma_unpair1_pair(encode(conclusion), encode_justification(last_line.1));
    //  unpair1(last_enc_line) = encode(conclusion)

    //  Step 5: iff_data(s) = unpair2(encode(conclusion))
    //  conclusion = Iff{left, right}
    //  encode(Iff{left, right}) = pair(6, pair(encode(left), encode(right)))
    //  Need to match the Iff pattern
    match conclusion {
        Formula::Iff { left, right } => {
            let el = encode(*left);
            let er = encode(*right);
            assert(encode(conclusion) == pair(6, pair(el, er)));
            lemma_unpair2_pair(6nat, pair(el, er));
            //  unpair2(encode(conclusion)) = pair(el, er)

            //  Step 6: output1 = unpair1(pair(el, er)) = el = enc_left
            lemma_unpair1_pair(el, er);
            //  Step 6b: output2 = unpair2(pair(el, er)) = er = enc_right
            lemma_unpair2_pair(el, er);
        },
        _ => {
            //  conclusion_is_iff_of_sentences requires Iff
            assert(false);
        },
    }
}

///  The output1 CompSpec term computes the first output of enumerator_spec.
pub proof fn lemma_output1_comp_correct()
    ensures
        is_output1_comp(output1_comp_term()),
{
    assert forall|s: nat| is_valid_iff_proof_code(s) implies
        (#[trigger] eval_comp(output1_comp_term(), s)) == enumerator_spec(s).unwrap().0
    by {
        let p: Proof = choose|p: Proof|
            encode_proof(p) == s &&
            is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
            p.lines.len() > 0 &&
            conclusion_is_iff_of_sentences(proof_conclusion(p));
        lemma_output_eval_chain(s, p);
    };
}

///  The output2 CompSpec term computes the second output of enumerator_spec.
pub proof fn lemma_output2_comp_correct()
    ensures
        is_output2_comp(output2_comp_term()),
{
    assert forall|s: nat| is_valid_iff_proof_code(s) implies
        (#[trigger] eval_comp(output2_comp_term(), s)) == enumerator_spec(s).unwrap().1
    by {
        let p: Proof = choose|p: Proof|
            encode_proof(p) == s &&
            is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
            p.lines.len() > 0 &&
            conclusion_is_iff_of_sentences(proof_conclusion(p));
        lemma_output_eval_chain(s, p);
    };
}

} //  verus!
