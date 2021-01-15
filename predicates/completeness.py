# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""

from typing import AbstractSet, Container, Set, Union, Iterable
import collections
import re
from itertools import product
from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    sets = set_out_of_sentences_creator(sentences)
    world = sets.world
    relations = sets.relations
    groups = create_permutation_dict(world, relations)
    for relation_name, relation_arity in relations:
        group = groups[relation_arity]
        for a in group:
            positive = Formula(relation_name, list(a))
            negative = Formula("~", Formula(relation_name, list(a)))
            if not (positive in sentences or negative in sentences):
                return False
    return True

    # Task 12.1.1


def create_permutation_dict(world: Set[str], relations) -> Dict[int, Iterable]:
    """
    Creates a dictionary of products based on different repeats.
    :param world:
    :param relations:
    :return:
    """
    group_dict = {}
    for relation in relations:
        arity = relation[1]
        if arity in group_dict:
            continue
        group = product(world, repeat=arity)
        group_dict[arity] = group
    return group_dict


def set_out_of_sentences_creator(sentences: AbstractSet[Formula]):
    world = set()
    relations = set()
    quantifiers = set()
    for formula in sentences:
        world.update(formula.constants())
        relations.update(formula.relations())
        if is_quantifier(formula.root):
            quantifiers.add(formula)
    Sets = collections.namedtuple("Sentences_sets", 'world relations quantifiers')
    return Sets(world, relations, quantifiers)


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    sets = set_out_of_sentences_creator(sentences)
    world = sets.world
    quantifiers = sets.quantifiers

    universally = [quantifier for quantifier in quantifiers if quantifier.root == 'A']
    for formula in universally:
        predicate = formula.predicate
        var = formula.variable
        for c in world:
            inst = predicate.substitute({var: Term(c)})
            if inst not in sentences:
                return False
    return True

    # Task 12.1.2


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    sets = set_out_of_sentences_creator(sentences)
    world = sets.world
    quantifiers = sets.quantifiers
    found = False

    universally = [quantifier for quantifier in quantifiers if quantifier.root == 'E']
    for formula in universally:
        predicate = formula.predicate
        var = formula.variable
        for c in world:
            inst = predicate.substitute({var: Term(c)})
            if inst in sentences:
                found = True
                break
        if not found:
            return False
        found = False
    return True

    # Task 12.1.3


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)

    universe = model.universe
    root = unsatisfied.root
    if root == 'A':
        for c in universe:
            var = unsatisfied.variable
            unsatisfied_new = unsatisfied.predicate.substitute({var: Term(c)})
            if not model.evaluate_formula(unsatisfied_new):
                return find_unsatisfied_quantifier_free_sentence(sentences, model, unsatisfied_new)
    elif root == 'E':
        for c in universe:
            var = unsatisfied.variable
            unsatisfied_new = unsatisfied.predicate.substitute({var: Term(c)})
            if unsatisfied_new in sentences:
                return find_unsatisfied_quantifier_free_sentence(sentences, model, unsatisfied_new)
    return unsatisfied

    # Task 12.2


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # ______________________ A SOLUTION USING REGEX, JUST FOR FUN ___________________ #
    # pattern = "(\w+\([^)]*\))"
    # primitive = set()
    # for match in re.finditer(pattern, str(quantifier_free)):
    #     primitive.add(Formula.parse(match.string))
    # return primitive
    # _____________________ SOLUTION WITHOUT REGEX __________________________________ #
    primitive = set()
    root = quantifier_free.root
    if is_binary(root):
        primitive.update(get_primitives(quantifier_free.first))
        primitive.update(get_primitives(quantifier_free.second))
    elif is_unary(root):
        primitive.update(get_primitives(quantifier_free.first))
    elif is_relation(root):
        primitive.update({quantifier_free})
    return primitive

    # Task 12.3.1


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    constants = get_constants(sentences)
    constants_meanings = dict(zip(constants, constants))
    relation_meanings = create_relation_meanings(sentences)
    model = Model(constants, constants_meanings, relation_meanings)

    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            unsatisfied = find_unsatisfied_quantifier_free_sentence(sentences, model, sentence)
            proof = prove_contradiction(unsatisfied, sentences)
            return proof
    return model

    # Task 12.3.2


def prove_contradiction(unsatisfied: Formula, sentences: AbstractSet[Formula]) -> Proof:
    """
    proves that contradiction of (p&q)&(~q&p) (always false)
    :param unsatisfied:
    :param sentences:
    :return:
    """
    assumptions = Prover.AXIOMS.union(sentences)
    prover = Prover(assumptions)
    step1 = prover.add_assumption(unsatisfied)
    primitives = get_primitives(unsatisfied)

    steps = {step1}
    abs_primitives = list()
    for primitive in primitives:
        primitive_in_sentences = primitive if (primitive in sentences) else Formula("~", primitive)
        abs_primitives.append(primitive_in_sentences)
        steps.add(prover.add_assumption(primitive_in_sentences))
    unsatisfied_and_assumptions = add_and_to_assumptions(unsatisfied, abs_primitives)
    prover.add_tautological_implication(unsatisfied_and_assumptions, steps)  # (p&q)&(~q&p)

    return prover.qed()


def add_and_to_assumptions(unsatisfied, primitives: List[Formula]) -> Formula:
    if len(primitives) == 1:
        return Formula('&', unsatisfied, primitives[0])
    return Formula("&", unsatisfied, add_and_to_assumptions(primitives[0], primitives[1:]))


def create_relation_meanings(formulas: AbstractSet[Formula]):
    relation_meanings = {}
    for formula in formulas:
        if not is_relation(formula.root):
            continue
        primitive = get_primitives(formula)
        for p in primitive:
            if p not in formulas:
                continue
            name = p.root
            args = [str(arg) for arg in p.arguments]
            if name not in relation_meanings:
                relation_meanings[name] = set()
            relation_meanings[name].add(tuple(args))
    return relation_meanings


def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0

    proof1 = proof_by_way_of_contradiction(proof_from_affirmation, affirmed_assumption.formula)
    proof2 = proof_by_way_of_contradiction(proof_from_negation, negated_assumption.formula)
    prover = Prover(common_assumptions)
    conclusion_of_proof1 = prover.add_proof(proof1.conclusion, proof1)
    conclusion_of_proof2 = prover.add_proof(proof2.conclusion, proof2)
    contradiction = Formula.parse(f'({proof1.conclusion}&{proof2.conclusion})')
    taut = prover.add_tautological_implication(contradiction, {conclusion_of_proof1, conclusion_of_proof2})
    return prover.qed()
    # Task 12.4


def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0

    proof_without_instantiation = proof_by_way_of_contradiction(proof, instantiation)  # Proofs ~R(c)
    prover = Prover(proof_without_instantiation.assumptions)
    assumption = prover.add_assumption(universal)
    inst = prover.add_universal_instantiation(instantiation, assumption, constant)  # Proofs R(c)
    add_proof = prover.add_proof(proof_without_instantiation.conclusion, proof_without_instantiation)
    contradiction = Formula("&", instantiation, proof_without_instantiation.conclusion)
    final = prover.add_tautological_implication(contradiction, {inst, add_proof})
    return prover.qed()
    # Task 12.5


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    universe = get_constants(sentences)
    closed = set(sentences)
    for sentence in sentences:
        if sentence.root == 'A':
            for c in universe:
                var = sentence.variable
                sub = sentence.predicate.substitute({var: Term(c)})
                if sub not in closed:
                    closed.add(sub)
    return closed

    # Task 12.6


def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in given the proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    lines = []
    assumptions = set()
    for assumption in proof.assumptions:
        new_assumption = create_new_scheme(assumption, constant, variable)
        assumptions.update({new_assumption})
    conclusion = proof.conclusion.substitute({constant: Term(variable)})
    for line in proof.lines:
        new_formula = line.formula.substitute({constant: Term(variable)})
        new_line = None
        if isinstance(line, proof.AssumptionLine):
            new_line = add_constant_assumption(line, constant, variable)
        elif isinstance(line, Proof.TautologyLine):
            new_line = Proof.TautologyLine(new_formula)
        elif isinstance(line, Proof.MPLine):
            new_line = Proof.MPLine(new_formula, line.antecedent_line_number, line.conditional_line_number)
        elif isinstance(line, Proof.UGLine):
            new_line = Proof.UGLine(new_formula, line.predicate_line_number)
        lines.append(new_line)
    return Proof(assumptions, conclusion, lines)
    # Task 12.7.1


def create_new_scheme(scheme: Schema, constant, variable):
    new_formula = scheme.formula.substitute({constant: Term(variable)})
    templates = scheme.templates
    new_templates = templates
    if constant in templates:
        new_templates = templates.difference({constant}).union({variable})
    new_scheme = Schema(new_formula, new_templates)
    return new_scheme


def add_constant_assumption(line: Proof.Line, constant: str, variable: str = 'zz'):
    scheme = line.assumption
    new_formula = scheme.formula.substitute({constant: Term(variable)})
    sub_formula = line.formula.substitute({constant: Term(variable)})
    templates = scheme.templates
    new_templates = templates
    if constant in templates:
        new_templates = templates.difference({constant}).union({variable})
    new_scheme = Schema(new_formula, new_templates)

    sub_map = {}
    for var, sub in line.instantiation_map.items():
        if isinstance(sub, str):
            value = variable if sub == constant else sub
        else:
            value = sub.substitute({constant: Term(variable)}) if constant in sub.constants() else sub
        sub_map[var] = value
    return Proof.AssumptionLine(sub_formula, new_scheme, sub_map)


def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()

    # Task 12.7.2
    var = "zz"
    proof_w_constant = replace_constant(proof, constant)
    new_witness = witness.substitute({constant: Term(var)})
    proof1 = proof_by_way_of_contradiction(proof_w_constant, new_witness)
    not_witness = proof1.conclusion

    assumptions = proof1.assumptions
    prover = Prover(assumptions)
    add_contradiction = prover.add_proof(not_witness, proof1)

    ug_on_not_witness = prover.add_ug(f'A{var}[{not_witness}]', add_contradiction)
    sub_var = existential.variable
    sub_witness = not_witness.substitute({var: Term(sub_var)})
    ui_on_not_witness = prover.add_universal_instantiation(sub_witness, ug_on_not_witness, sub_var)
    ug_on_sub_witness_ui = prover.add_ug(f'A{sub_var}[{sub_witness}]', ui_on_not_witness)

    # _____________________ PROOF OF A[~R(X)] - > ~E[R(X)] _____________________
    using_ui_assum = prover.add_instantiated_assumption(f'(A{sub_var}[{sub_witness}]->{sub_witness})', prover.UI,
                                                        {'R': sub_witness.substitute({sub_var: Term("_")}),
                                                         'x': sub_var,
                                                         'c': sub_var})
    taut_not_p_to_q = prover.add_tautological_implication(f'({sub_witness.first}->~A{sub_var}[{sub_witness}])',
                                                          {using_ui_assum})
    add_assumption = prover.add_assumption(existential)
    taut_not_p_to_q_ug = prover.add_ug(f'A{sub_var}[({sub_witness.first}->~A{sub_var}[{sub_witness}])]',
                                       taut_not_p_to_q)
    inst_map = {'R': sub_witness.first.substitute({sub_var: Term("_")}),
                'Q': Formula.parse(f'~A{sub_var}[{sub_witness}]'),
                "x": sub_var}
    f = prover.ES.instantiate(inst_map)
    using_ES = prover.add_instantiated_assumption(f, prover.ES, inst_map)
    finish_proof = prover.add_tautological_implication(f'~A{sub_var}[{sub_witness}]',
                                                       {add_assumption, using_ES, taut_not_p_to_q_ug})

    contradiction = prover.add_tautological_implication(f'(~A{sub_var}[{sub_witness}]&A{sub_var}[{sub_witness}])',
                                                        {finish_proof, ug_on_sub_witness_ui})

    return prover.qed()


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    universe = get_constants(sentences)
    closed = set(sentences)
    found = False
    for sentence in sentences:
        if sentence.root == "E":
            var = sentence.variable
            for c in universe:
                formula = sentence.predicate.substitute({var: Term(c)})
                if formula in closed:
                    found = True
                    break
            if not found:
                z = next(fresh_constant_name_generator)
                add_formula = sentence.predicate.substitute({var: Term(z)})
                closed.add(add_formula)
            found = False
    return closed

    # Task 12.8
