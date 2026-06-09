use vstd::prelude::*;
use crate::pairing::*;
use crate::formula::*;
use crate::proof_system::*;

verus! {

//  ============================================================
//  Proof encoding: Gödel-encode proofs as natural numbers
//  ============================================================

///  Encode a justification as a natural number.
///  Tags: 0=LogicAxiom, 1=Assumption, 2=ModusPonens, 3=Generalization
pub open spec fn encode_justification(j: Justification) -> nat {
    match j {
        Justification::LogicAxiom => pair(0, 0),
        Justification::Assumption => pair(1, 0),
        Justification::ModusPonens { premise_line, implication_line } =>
            pair(2, pair(premise_line, implication_line)),
        Justification::Generalization { premise_line, var } =>
            pair(3, pair(premise_line, var)),
    }
}

///  Encode a proof line (formula, justification) as a natural number.
pub open spec fn encode_line(line: (Formula, Justification)) -> nat {
    pair(encode(line.0), encode_justification(line.1))
}

///  Encode a sequence of natural numbers.
///  Empty → 0, non-empty → pair(head + 1, encode_nat_seq(tail)).
pub open spec fn encode_nat_seq(s: Seq<nat>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        pair(s[0] + 1, encode_nat_seq(s.subrange(1, s.len() as int)))
    }
}

///  Encode a proof as a natural number.
pub open spec fn encode_proof(p: Proof) -> nat {
    encode_nat_seq(
        Seq::new(p.lines.len(), |i: int| encode_line(p.lines[i]))
    )
}

//  ============================================================
//  Injectivity lemmas
//  ============================================================

///  Tag of a justification encoding.
spec fn justification_tag(j: Justification) -> nat {
    match j {
        Justification::LogicAxiom => 0,
        Justification::Assumption => 1,
        Justification::ModusPonens { .. } => 2,
        Justification::Generalization { .. } => 3,
    }
}

///  Content of a justification encoding.
spec fn justification_content(j: Justification) -> nat {
    match j {
        Justification::LogicAxiom => 0,
        Justification::Assumption => 0,
        Justification::ModusPonens { premise_line, implication_line } =>
            pair(premise_line, implication_line),
        Justification::Generalization { premise_line, var } =>
            pair(premise_line, var),
    }
}

///  Justification encoding is injective.
pub proof fn lemma_encode_justification_injective(j1: Justification, j2: Justification)
    requires
        encode_justification(j1) == encode_justification(j2),
    ensures
        j1 == j2,
{
    lemma_pair_injective(
        justification_tag(j1), justification_content(j1),
        justification_tag(j2), justification_content(j2),
    );
    match j1 {
        Justification::LogicAxiom => {
            match j2 {
                Justification::LogicAxiom => {},
                _ => { assert(false); },
            }
        },
        Justification::Assumption => {
            match j2 {
                Justification::Assumption => {},
                _ => { assert(false); },
            }
        },
        Justification::ModusPonens { premise_line: p1, implication_line: i1 } => {
            match j2 {
                Justification::ModusPonens { premise_line: p2, implication_line: i2 } => {
                    lemma_pair_injective(p1, i1, p2, i2);
                },
                _ => { assert(false); },
            }
        },
        Justification::Generalization { premise_line: p1, var: v1 } => {
            match j2 {
                Justification::Generalization { premise_line: p2, var: v2 } => {
                    lemma_pair_injective(p1, v1, p2, v2);
                },
                _ => { assert(false); },
            }
        },
    }
}

///  Proof line encoding is injective.
pub proof fn lemma_encode_line_injective(l1: (Formula, Justification), l2: (Formula, Justification))
    requires
        encode_line(l1) == encode_line(l2),
    ensures
        l1 == l2,
{
    lemma_pair_injective(
        encode(l1.0), encode_justification(l1.1),
        encode(l2.0), encode_justification(l2.1),
    );
    lemma_encode_injective(l1.0, l2.0);
    lemma_encode_justification_injective(l1.1, l2.1);
}

///  Non-empty sequence has non-zero encoding.
pub proof fn lemma_encode_nat_seq_nonempty(s: Seq<nat>)
    requires
        s.len() > 0,
    ensures
        encode_nat_seq(s) > 0,
{
    lemma_pair_gt_components(s[0] + 1, encode_nat_seq(s.subrange(1, s.len() as int)));
}

///  Nat-sequence encoding is injective.
pub proof fn lemma_encode_nat_seq_injective(s1: Seq<nat>, s2: Seq<nat>)
    requires
        encode_nat_seq(s1) == encode_nat_seq(s2),
    ensures
        s1 =~= s2,
    decreases s1.len(),
{
    if s1.len() == 0 {
        if s2.len() > 0 {
            lemma_encode_nat_seq_nonempty(s2);
        }
    } else if s2.len() == 0 {
        lemma_encode_nat_seq_nonempty(s1);
    } else {
        let t1 = s1.subrange(1, s1.len() as int);
        let t2 = s2.subrange(1, s2.len() as int);
        lemma_pair_injective(
            s1[0] + 1, encode_nat_seq(t1),
            s2[0] + 1, encode_nat_seq(t2),
        );
        lemma_encode_nat_seq_injective(t1, t2);
        assert(s1.len() == s2.len()) by {
            assert(t1.len() == t2.len());
        };
        assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
            if i == 0 {
            } else {
                assert(s1[i] == t1[i - 1]);
                assert(s2[i] == t2[i - 1]);
            }
        };
    }
}

///  Proof encoding is injective.
pub proof fn lemma_encode_proof_injective(p1: Proof, p2: Proof)
    requires
        encode_proof(p1) == encode_proof(p2),
    ensures
        p1 == p2,
{
    let s1 = Seq::new(p1.lines.len(), |i: int| encode_line(p1.lines[i]));
    let s2 = Seq::new(p2.lines.len(), |i: int| encode_line(p2.lines[i]));
    lemma_encode_nat_seq_injective(s1, s2);
    assert(p1.lines.len() == p2.lines.len());
    assert forall|i: int| 0 <= i < p1.lines.len() implies p1.lines[i] == p2.lines[i] by {
        assert(s1[i] == encode_line(p1.lines[i]));
        assert(s2[i] == encode_line(p2.lines[i]));
        assert(s1[i] == s2[i]);
        lemma_encode_line_injective(p1.lines[i], p2.lines[i]);
    };
    assert(p1.lines =~= p2.lines);
}

//  ============================================================
//  Decode: last element of encoded nat sequence
//  ============================================================

///  Spec function: recursively find last element of encoded nat sequence.
pub open spec fn decode_nat_seq_last(enc: nat) -> nat
    decreases enc
    via decode_nat_seq_last_decreases
{
    if enc == 0 {
        0  //  undefined for empty
    } else if unpair1(enc) == 0 {
        0  //  invalid encoding (elements stored as value+1 >= 1)
    } else if unpair2(enc) == 0 {
        (unpair1(enc) - 1) as nat
    } else {
        decode_nat_seq_last(unpair2(enc))
    }
}

#[via_fn]
proof fn decode_nat_seq_last_decreases(enc: nat) {
    if enc != 0 && unpair1(enc) >= 1 {
        lemma_unpair2_lt(enc);
    }
}

///  For non-empty sequences, decode_nat_seq_last recovers the last element.
pub proof fn lemma_decode_nat_seq_last(s: Seq<nat>)
    requires
        s.len() > 0,
    ensures
        decode_nat_seq_last(encode_nat_seq(s)) == s[s.len() - 1],
    decreases s.len(),
{
    let enc = encode_nat_seq(s);
    let tail_seq = s.subrange(1, s.len() as int);
    let tail_enc = encode_nat_seq(tail_seq);

    //  enc = pair(s[0] + 1, tail_enc)
    lemma_unpair1_pair(s[0] + 1, tail_enc);
    lemma_unpair2_pair(s[0] + 1, tail_enc);
    assert(unpair1(enc) == s[0] + 1);
    assert(unpair2(enc) == tail_enc);

    if s.len() == 1 {
        //  tail_seq is empty, tail_enc = 0
        assert(tail_seq.len() == 0);
        assert(tail_enc == 0);
        assert(unpair2(enc) == 0);
        //  decode_nat_seq_last(enc) = unpair1(enc) - 1 = s[0] + 1 - 1 = s[0]
        assert(decode_nat_seq_last(enc) == s[0]);
    } else {
        //  tail is non-empty
        assert(tail_seq.len() > 0);
        lemma_encode_nat_seq_nonempty(tail_seq);
        assert(tail_enc > 0);
        assert(unpair2(enc) != 0);
        //  decode_nat_seq_last(enc) = decode_nat_seq_last(tail_enc)
        //  Need: tail_enc < enc for decreases
        lemma_pair_pos_tag_gt_content(s[0] + 1, tail_enc);
        assert(enc > tail_enc);
        //  By induction: decode_nat_seq_last(tail_enc) = tail_seq.last()
        lemma_decode_nat_seq_last(tail_seq);
        assert(decode_nat_seq_last(tail_enc) == tail_seq[tail_seq.len() - 1]);
        //  tail_seq.last() == s.last()
        assert(tail_seq[tail_seq.len() - 1] == s[s.len() - 1]);
    }
}

///  For non-empty sequences, unpair1 of the last pair is last_element + 1.
pub proof fn lemma_encode_nat_seq_structure(s: Seq<nat>)
    requires
        s.len() > 0,
    ensures
        encode_nat_seq(s) != 0,
        unpair1(encode_nat_seq(s)) == s[0] + 1,
        unpair2(encode_nat_seq(s)) == encode_nat_seq(s.subrange(1, s.len() as int)),
{
    let enc = encode_nat_seq(s);
    let tail = s.subrange(1, s.len() as int);
    lemma_encode_nat_seq_nonempty(s);
    lemma_unpair1_pair(s[0] + 1, encode_nat_seq(tail));
    lemma_unpair2_pair(s[0] + 1, encode_nat_seq(tail));
}

///  encode_nat_seq(s) >= s.len() for all sequences.
pub proof fn lemma_encode_nat_seq_ge_len(s: Seq<nat>)
    ensures encode_nat_seq(s) >= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let tail = s.subrange(1, s.len() as int);
        lemma_encode_nat_seq_ge_len(tail);
        lemma_pair_ge_sum(s[0] + 1, encode_nat_seq(tail));
    }
}

//  ============================================================
//  Decoding: reconstruct from Gödel numbers
//  ============================================================

///  Decode a justification from its Gödel number.
pub open spec fn decode_justification(n: nat) -> Justification {
    let tag = unpair1(n);
    let content = unpair2(n);
    if tag == 0 {
        Justification::LogicAxiom
    } else if tag == 1 {
        Justification::Assumption
    } else if tag == 2 {
        Justification::ModusPonens { premise_line: unpair1(content), implication_line: unpair2(content) }
    } else if tag == 3 {
        Justification::Generalization { premise_line: unpair1(content), var: unpair2(content) }
    } else {
        Justification::LogicAxiom  //  default
    }
}

///  Decode a proof line from its Gödel number.
pub open spec fn decode_line(n: nat) -> (Formula, Justification) {
    (decode_formula(unpair1(n)), decode_justification(unpair2(n)))
}

///  Decode a nat sequence from its Gödel number.
pub open spec fn decode_nat_seq(n: nat) -> Seq<nat>
    decreases n
    via decode_nat_seq_decreases
{
    if n == 0 {
        Seq::empty()
    } else if unpair1(n) == 0 {
        Seq::empty()  //  invalid encoding (elements are stored as value+1)
    } else {
        seq![(unpair1(n) - 1) as nat] + decode_nat_seq(unpair2(n))
    }
}

#[via_fn]
proof fn decode_nat_seq_decreases(n: nat) {
    if n != 0 && unpair1(n) >= 1 {
        lemma_unpair2_lt(n);
    }
}

///  Decode a proof from its Gödel number.
pub open spec fn decode_proof(s: nat) -> Proof {
    let elems = decode_nat_seq(s);
    Proof { lines: Seq::new(elems.len(), |i: int| decode_line(elems[i])) }
}

//  ============================================================
//  Decoding roundtrip lemmas
//  ============================================================

///  Roundtrip: decode_justification(encode_justification(j)) == j.
pub proof fn lemma_decode_encode_justification(j: Justification)
    ensures decode_justification(encode_justification(j)) == j,
{
    match j {
        Justification::LogicAxiom => {
            lemma_unpair1_pair(0nat, 0nat);
        },
        Justification::Assumption => {
            lemma_unpair1_pair(1nat, 0nat);
        },
        Justification::ModusPonens { premise_line, implication_line } => {
            lemma_unpair1_pair(2nat, pair(premise_line, implication_line));
            lemma_unpair2_pair(2nat, pair(premise_line, implication_line));
            lemma_unpair1_pair(premise_line, implication_line);
            lemma_unpair2_pair(premise_line, implication_line);
        },
        Justification::Generalization { premise_line, var } => {
            lemma_unpair1_pair(3nat, pair(premise_line, var));
            lemma_unpair2_pair(3nat, pair(premise_line, var));
            lemma_unpair1_pair(premise_line, var);
            lemma_unpair2_pair(premise_line, var);
        },
    }
}

///  Roundtrip: decode_line(encode_line(l)) == l.
pub proof fn lemma_decode_encode_line(l: (Formula, Justification))
    ensures decode_line(encode_line(l)) == l,
{
    lemma_unpair1_pair(encode(l.0), encode_justification(l.1));
    lemma_unpair2_pair(encode(l.0), encode_justification(l.1));
    lemma_decode_encode_formula(l.0);
    lemma_decode_encode_justification(l.1);
}

///  Roundtrip: decode_nat_seq(encode_nat_seq(s)) == s.
pub proof fn lemma_decode_encode_nat_seq(s: Seq<nat>)
    ensures decode_nat_seq(encode_nat_seq(s)) =~= s,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        lemma_encode_nat_seq_nonempty(s);
        lemma_unpair1_pair(s[0] + 1, encode_nat_seq(tail));
        lemma_unpair2_pair(s[0] + 1, encode_nat_seq(tail));
        lemma_decode_encode_nat_seq(tail);
        //  decode_nat_seq(encode_nat_seq(s))
        //  = seq![s[0]] + decode_nat_seq(encode_nat_seq(tail))
        //  = seq![s[0]] + tail  (by IH)
        //  = s
        assert(s =~= seq![s[0]] + tail);
    }
}

///  Roundtrip: decode_proof(encode_proof(p)) == p.
pub proof fn lemma_decode_encode_proof(p: Proof)
    ensures decode_proof(encode_proof(p)) == p,
{
    let lines = Seq::new(p.lines.len(), |i: int| encode_line(p.lines[i]));
    lemma_decode_encode_nat_seq(lines);
    //  decode_nat_seq(encode_nat_seq(lines)) =~= lines
    //  So decode_proof(encode_proof(p)).lines =~=
    //    Seq::new(lines.len(), |i| decode_line(lines[i]))
    //  = Seq::new(p.lines.len(), |i| decode_line(encode_line(p.lines[i])))
    //  = Seq::new(p.lines.len(), |i| p.lines[i])  (by decode_encode_line roundtrip)
    //  =~= p.lines
    assert forall|i: int| 0 <= i < p.lines.len() implies
        decode_line(#[trigger] lines[i]) == p.lines[i]
    by {
        lemma_decode_encode_line(p.lines[i]);
    }
    assert(decode_proof(encode_proof(p)).lines =~= p.lines);
}

} //  verus!
