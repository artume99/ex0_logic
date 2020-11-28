# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *


def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable `x` that is assigned the
    value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    formula_list = list(map(lambda m: Formula.parse(m[0]) if m[1] else Formula.parse('~' + m[0]), model.items()))
    formula_list = sorted(formula_list, key=lambda f: str(f.variables()))
    return formula_list
    # Task 6.1a


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    rules = AXIOMATIC_SYSTEM
    statement_assumption = formulas_capturing_model(model)
    formula_value = evaluate(formula, model)
    statement_conclusion = formula if formula_value else Formula.parse('~' + str(formula))
    statement = InferenceRule(statement_assumption, statement_conclusion)
    if is_variable(formula.root):
        lines = [Proof.Line(statement_conclusion)]
        return Proof(statement, rules, lines)
    if is_binary(formula.root):
        if formula_value:
            if not evaluate(formula.first, model):
                proof_first = prove_in_model(formula.first, model)
                full_proof = prove_corollary(proof_first, statement_conclusion, I2)
            else:
                proof_first = prove_in_model(formula.second, model)
                full_proof = prove_corollary(proof_first, statement_conclusion, I1)
        else:
            proof_first = prove_in_model(formula.first, model)
            proof_second = prove_in_model(formula.second, model)
            full_proof = combine_proofs(proof_first, proof_second, statement_conclusion, NI)
    else:
        if formula_value:
            full_proof = prove_in_model(formula.first, model)
        else:
            proof_first = prove_in_model(formula.first, model)
            full_proof = prove_corollary(proof_first, statement_conclusion, NN)
    return Proof(statement, rules, full_proof.lines)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption` ``'`` instead of
            `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    proof_aff = remove_assumption(proof_from_affirmation)
    proof_neg = remove_assumption(proof_from_negation)
    proof_combine = combine_proofs(proof_aff, proof_neg, proof_from_affirmation.statement.conclusion, R)
    return proof_combine
    # Task 6.2


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    if len(model) == len(tautology.variables()):
        return prove_in_model(tautology, model)
    variables_not_in_model = sorted([v for v in tautology.variables() if v not in model])
    check_on_var = variables_not_in_model[0]
    variables_not_in_model.remove(check_on_var)
    new_model = {check_on_var: True}
    new_model.update(model)
    aff_proof = prove_tautology(tautology, new_model)
    new_model[check_on_var] = False
    neg_proof = prove_tautology(tautology, new_model)
    return reduce_assumption(aff_proof, neg_proof)

    # Task 6.3a


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    if is_tautology(formula):
        return prove_tautology(formula)
    else:
        for model in all_models(list(formula.variables())):
            if not evaluate(formula, model):
                return model
    # Task 6.3b


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    formula = str(rule.conclusion)
    for assumption in reversed(rule.assumptions):
        formula = "({assum}->{f})".format(assum=assumption, f=formula)
    return Formula.parse(formula)
    # Task 6.4a


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    formula_to_proof = encode_as_formula(rule)
    proof_tau = prove_tautology(formula_to_proof)
    proof = proof_tau
    for assumption in rule.assumptions:
        last_idx = len(proof.lines) - 1
        last_form = proof.lines[last_idx].formula.second
        line1 = Proof.Line(assumption)
        line2 = Proof.Line(MP.specialize({'p': assumption, 'q': last_form}).conclusion, MP,
                           [last_idx + 1, last_idx])
        lines = list(proof.lines)
        lines.extend([line1, line2])
        proof = Proof(rule, AXIOMATIC_SYSTEM, lines)
    return proof
    # Task 6.4b


def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})
    all_variables = []
    for formula in formulas:
        all_variables.extend(formula.variables())
    all_var_models = list(all_models(all_variables))
    available_models = _delete_models(all_var_models, formulas)
    if len(available_models) > 0:
        return available_models[0]
    formula_to_disproof = Formula.parse("~{I0}".format(I0=I0.conclusion))
    rule = InferenceRule(formulas, formula_to_disproof)
    proof = prove_sound_inference(rule)
    return proof
    # Task 6.5


def _delete_models(available_models: List[Model], formulas: Sequence[Formula], start=0) -> List[Model]:
    new_start = len(available_models)
    for num, model in enumerate(available_models[start:]):
        for formula in formulas:
            if not evaluate(formula, model):
                available_models.remove(model)
                new_start = num + start
                break
            continue
        return _delete_models(available_models, formulas, new_start)
    return available_models


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
