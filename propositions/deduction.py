# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""
from propositions.proofs import _inline_proof_once
from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from itertools import chain


def lemma_for_corollary(conditional: InferenceRule, rules) -> Proof:
    lemma_statement = InferenceRule([conditional.conclusion.first], conditional.conclusion.second)
    line0 = Proof.Line(conditional.conclusion.first)
    line1 = Proof.Line(conditional.conclusion, conditional, [])
    line2 = Proof.Line(conditional.conclusion.second, MP, [0, 1])
    lines = [line0, line1, line2]
    lemma = Proof(lemma_statement, rules, lines)
    return lemma


def lemma_for_combine(double_conditional, rules) -> Proof:
    lemma_statement = InferenceRule([double_conditional.conclusion.first, double_conditional.conclusion.second.first],
                                    double_conditional.conclusion.second.second)
    line0 = Proof.Line(double_conditional.conclusion.first)
    line1 = Proof.Line(double_conditional.conclusion, double_conditional, [])
    line2 = Proof.Line(double_conditional.conclusion.second, MP, [0, 1])
    line3 = Proof.Line(double_conditional.conclusion.second.first)
    line4 = Proof.Line(double_conditional.conclusion.second.second, MP, [3, 2])
    lines = [line0, line1, line2, line3, line4]
    lemma = Proof(lemma_statement, rules, lines)
    return lemma


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    statement_assumptions = antecedent_proof.statement.assumptions
    statement_conclusion = consequent
    lemma_statement = InferenceRule([conditional.conclusion.first], conditional.conclusion.second)
    statement = InferenceRule(statement_assumptions, statement_conclusion)
    rules = antecedent_proof.rules.union({conditional, MP, lemma_statement})

    sub_line = Proof.Line(statement_conclusion, lemma_statement, [len(antecedent_proof.lines) - 1])
    sub_lines = list(antecedent_proof.lines)
    sub_lines.append(sub_line)
    proof = Proof(statement, rules, sub_lines)

    lemma = lemma_for_corollary(conditional, rules)
    return inline_proof(proof, lemma)
    # Task 5.3a


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)

    lemma_statement = InferenceRule([double_conditional.conclusion.first, double_conditional.conclusion.second.first],
                                    double_conditional.conclusion.second.second)
    statement_assumptions = antecedent1_proof.statement.assumptions
    statement_conclusion = consequent
    statement = InferenceRule(statement_assumptions, statement_conclusion)
    rules = antecedent1_proof.rules.union({double_conditional, MP, lemma_statement})

    lemma = lemma_for_combine(double_conditional, rules)

    # Adding the assumption of the second proof, the statement of the second proof and merging both proofs
    sub_lines1 = list(antecedent1_proof.lines)
    sub_line_assumption = Proof.Line(antecedent2_proof.statement.assumptions[-1])
    sub_lines1.append(sub_line_assumption)
    sub_line1 = Proof.Line(antecedent2_proof.statement.conclusion, antecedent2_proof.statement,
                           [len(sub_lines1) - 2, len(sub_lines1) - 1]) if len(
        antecedent1_proof.statement.assumptions) > 1 else Proof.Line(antecedent2_proof.statement.conclusion,
                                                                     antecedent2_proof.statement,
                                                                     [len(sub_lines1) - 1])
    sub_lines1.append(sub_line1)
    proof1 = Proof(statement, rules, sub_lines1)
    proof = inline_proof(proof1, antecedent2_proof)

    # Adding the statement of the lemma and merging the proofs
    sub_lines = list(proof.lines)
    sub_line = Proof.Line(statement_conclusion, lemma_statement, [len(antecedent1_proof.lines) - 1,
                                                                  len(antecedent1_proof.lines) + len(
                                                                      antecedent2_proof.lines) - 1])
    sub_lines.append(sub_line)

    proof = Proof(proof.statement, proof.rules, sub_lines)
    return inline_proof(proof, lemma)
    # Task 5.3b


def _case1(line: Proof.Line) -> Proof.Line:
    return Proof.Line(Formula.parse('({assm}->{assm})'.format(assm=line.formula)), I0, [])


def _case2(line: Proof.Line, assumption_to_remove: Formula, line_number: int) -> List:
    line1 = line
    line2 = Proof.Line(
        Formula.parse("({line1}->({assm}->{line1}))".format(line1=line1.formula, assm=assumption_to_remove)),
        I1, [])
    line3 = Proof.Line(Formula.parse("({assm}->{line1})".format(line1=line1.formula, assm=assumption_to_remove)),
                       MP, [line_number, line_number + 1])
    return [line1, line2, line3]


def _case3(line, line_dic, assumption_to_remove, lines, num, offset):
    lemma_assumptions = []
    for assumption in line.assumptions:
        lemma_assumptions.append(line_dic[assumption])
    line1 = Proof.Line((D.specialize(
        {'p': assumption_to_remove, 'q': lines[lemma_assumptions[0]].formula.second,
         'r': lines[lemma_assumptions[1]].formula.second.second}).conclusion), D, [])
    line2 = Proof.Line(Formula.parse(
        "({first}->({assm}->{sec}))".format(first=lines[lemma_assumptions[0]].formula,
                                            assm=assumption_to_remove,
                                            sec=lines[lemma_assumptions[1]].formula.second.second)), MP,
        [lemma_assumptions[1], num + offset])
    line3 = Proof.Line(Formula.parse("({assm}->{con})".format(assm=assumption_to_remove, con=line.formula)), MP,
                       [lemma_assumptions[0], num + offset + 1])
    return [line1, line2, line3]


# def _case3(line: Proof.Line, assumption_to_remove: Formula, line_number:int) -> List:
#     line1 = Proof.Line(D.specialize({'p': str(assumption_to_remove), 'q':str()}))
def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    rules = proof.rules.union({MP, I0, I1, D})
    assumption_to_remove = proof.statement.assumptions[-1]
    statement_assumptions = proof.statement.assumptions[:-1]
    statement_conclusion = Formula.parse(
        "({assm}->{con})".format(assm=assumption_to_remove, con=proof.statement.conclusion))
    statement = InferenceRule(statement_assumptions, statement_conclusion)
    lines = []
    line_dic = {}
    offset = 0
    for num, line in enumerate(proof.lines):
        if line.formula == assumption_to_remove:
            # case 1
            new_line = _case1(line)
            lines.append(new_line)
            line_dic.update({num: num + offset})
            continue
        elif line.formula in statement_assumptions or not line.rule.assumptions:
            # case 2
            new_lines = _case2(line, assumption_to_remove, num + offset)
            lines += new_lines
            offset += 2
            line_dic.update({num: num + offset})
            pass
        elif line.rule is MP:
            # case 3
            new_lines = _case3(line, line_dic, assumption_to_remove, lines, num, offset)
            offset += 2
            lines += new_lines
            line_dic.update({num: num + offset})
            pass
    return Proof(statement, rules, lines)
    # Task 5.4


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules

    statement_assumptions = proof_of_affirmation.statement.assumptions
    statement = InferenceRule(statement_assumptions, conclusion)
    rules = proof_of_negation.rules.union(proof_of_affirmation.rules.union({I2, MP}))
    lines = list(proof_of_affirmation.lines)
    end_of_aff_proof = len(lines)
    for line in proof_of_negation.lines:
        if line.is_assumption():
            lines.append(line)
        else:
            assumptions = []
            for assumption in line.assumptions:
                assumptions.append(assumption + end_of_aff_proof)
            lines.append(Proof.Line(line.formula, line.rule, assumptions))
    end_of_neg_proof = len(lines) - 1
    line1 = Proof.Line(I2.specialize({'p': proof_of_affirmation.statement.conclusion, 'q': conclusion}).conclusion, I2,
                       [])
    line2 = Proof.Line(line1.formula.second, MP, [end_of_neg_proof, end_of_neg_proof + 1])
    line3 = Proof.Line(conclusion, MP, [end_of_aff_proof - 1, end_of_neg_proof + 2])
    lines.extend([line1, line2, line3])
    return Proof(statement, rules, lines)

    # Task 5.6


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    new_proof = remove_assumption(proof)
    to_prove = Formula.parse(str(proof.statement.assumptions[-1]).replace("~", "", 1))
    statement = InferenceRule(new_proof.statement.assumptions, to_prove)
    rules = new_proof.rules.union({N, NI})
    end_of_proof = len(new_proof.lines) - 1

    line1 = Proof.Line(N.specialize({'p': Formula.parse(str(proof.statement.conclusion).replace("~", "", 1)),
                                     'q': Formula.parse(
                                         str(proof.statement.assumptions[-1]).replace("~", "", 1))}).conclusion, N, [])
    line2 = Proof.Line(line1.formula.second, MP, [end_of_proof, end_of_proof + 1])
    line3 = Proof.Line(Formula.parse("(p->p)"), I0, [])
    line4 = Proof.Line(MP.specialize({'p': Formula.parse("(p->p)"), 'q': to_prove}).conclusion, MP,
                       [end_of_proof + 3, end_of_proof + 2])
    lines = list(new_proof.lines)

    lines.extend([line1, line2, line3, line4])
    return Proof(statement, rules, lines)
    # Task 5.7
