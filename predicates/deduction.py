# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


def _case1(lines_dic, prover: Prover, assumption: Formula, line: Proof.Line):
    tau_line = prover.add_tautology(Formula.parse(f'({assumption}->{assumption})'))


def _case2(lines_dic, prover: Prover, assumption: Formula, line: Proof.Line):
    a = line.formula
    a_line = prover._add_line(line)
    tau_formula = Formula.parse("({a}->({ph}->{a}))".format(a=a, ph=assumption))
    tau_line = prover.add_tautology(tau_formula)
    mp_line = prover.add_mp("({ph}->{a})".format(a=a, ph=assumption), tau_line - 1, tau_line)


def _case3(lines_dic, prover: Prover, assumption: Formula, line: Proof.Line):
    a = prover._lines[lines_dic[line.antecedent_line_number]].formula.second
    b = line.formula
    tau_formula = Formula.parse(
        "(({ph}->({a}->{b}))->(({ph}->{a})->({ph}->{b})))".format(ph=assumption, a=a, b=b))
    tau_line = prover.add_tautology(tau_formula)
    mp1_formula = Formula.parse("(({ph}->{a})->({ph}->{b}))".format(ph=assumption, a=a, b=b))
    mp_line1 = prover.add_mp(mp1_formula, lines_dic[line.conditional_line_number], tau_line)
    mp2_formula = Formula.parse("({ph}->{b})".format(ph=assumption, b=b))
    mp_line2 = prover.add_mp(mp2_formula, lines_dic[line.antecedent_line_number], mp_line1)


def _case4(lines_dic, prover: Prover, assumption: Formula, line: Proof.Line):
    inside_line_num = line.predicate_line_number
    inside_formula = prover._lines[lines_dic[inside_line_num]].formula
    var = line.formula.variable
    ug_line = prover.add_ug(f"A{var}[{inside_formula}]", lines_dic[inside_line_num])

    us_formula = Formula.parse(f'(A{var}[{inside_formula}]->({assumption}->{line.formula}))')
    predicate = line.formula.predicate
    sub_map = {"x": var, "Q": assumption, "R": predicate.substitute({var: Term("_")})}
    us_line = prover.add_instantiated_assumption(us_formula, Prover.US, sub_map)

    mp_line = prover.add_mp(f'({assumption}->{line.formula})', ug_line, us_line)


def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    assumptions = [assum for assum in proof.assumptions if assum.formula != assumption]
    conclusion = Formula.parse(f'({assumption}->{proof.conclusion})')
    prover = Prover(assumptions, print_as_proof_forms)
    lines_dic = {}
    offset = 0
    for num, line in enumerate(proof.lines):
        if line.formula == assumption:
            # case1 Φ
            _case1(lines_dic, prover, assumption, line)
            lines_dic[num] = num + offset
        elif isinstance(line, proof.MPLine):
            # case3 a, (a->b), b (mp)
            _case3(lines_dic, prover, assumption, line)
            offset += 2
            lines_dic[num] = num + offset

        elif isinstance(line, proof.UGLine):
            # case4 a, Ax[a]
            _case4(lines_dic, prover, assumption, line)
            offset += 2
            lines_dic[num] = num + offset
        else:
            # case2 a
            _case2(lines_dic, prover, assumption, line)
            offset += 2
            lines_dic[num] = num + offset
    return prover.qed()
    # Task 11.1


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    to_prove = f'~{assumption}'
    new_proof = remove_assumption(proof, assumption)
    prover = Prover(new_proof.assumptions, print_as_proof_forms)
    conclusion = new_proof.conclusion
    prover.add_proof(conclusion, new_proof)

    line1 = prover.add_tautology(f'~{proof.conclusion}')
    line2 = prover.add_tautological_implication(to_prove, {line1 - 1, line1})

    return prover.qed()

    # Task 11.2
