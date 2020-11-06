# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple
from itertools import product

from propositions.syntax import *
from propositions.proofs import *
import tabulate

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]
SEPARATOR = '|'


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


PARAMETER_TO_ACTION = {'T': True,
                       'F': False,
                       '&': lambda first, second: first and second,
                       '|': lambda first, second: first or second,
                       '->': lambda first, second: (not first) or second,
                       '~': lambda first: not first}


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    if is_variable(formula.root):
        return model.get(formula.root)
    if is_constant(formula.root):
        return PARAMETER_TO_ACTION.get(formula.root)
    if is_unary(formula.root):
        return PARAMETER_TO_ACTION.get(formula.root)(evaluate(formula.first, model))
    if is_binary(formula.root):
        return PARAMETER_TO_ACTION.get(formula.root)(evaluate(formula.first, model), evaluate(formula.second, model))


# Task 2.1


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    models = list(product([False, True], repeat=len(variables)))  # Creates every permutation of false and true
    table = list()
    dict_tuple = dict()
    for model in models:
        for item in zip(variables, model):
            dict_tuple[item[0]] = item[1]
        table.append(dict_tuple)
        dict_tuple = dict()
    return table
    # Task 2.2


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    truth_table = list()
    for model in models:
        truth_table.append(evaluate(formula, model))
    return truth_table
    # Task 2.3


BOOL_DICT = {False: 'F', True: 'T'}


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    sorted_models = all_models(sorted(list(formula.variables())))
    truth_table_values = list(truth_values(formula, sorted_models))
    i = 0
    table = [[BOOL_DICT.get(exp) for exp in model.values()] for model in
             sorted_models]  # Create a list of rows for the tabulate
    for row in table:
        row.append(BOOL_DICT.get(truth_table_values[i]))
        i += 1
    headers = sorted(list(formula.variables())) + [str(formula)]
    truth_table = tabulate.tabulate(table, headers, tablefmt='orgtbl')
    truth_table = truth_table.replace('+', SEPARATOR)
    print(truth_table)

    # Task 2.4


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    return all(truth_values(formula, all_models(list(formula.variables()))))
    # Task 2.5a


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    return not any(truth_values(formula, all_models(list(formula.variables()))))
    # Task 2.5b


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    return any(truth_values(formula, all_models(list(formula.variables()))))
    # Task 2.5c


def create_written_formula(string: str, op: str) -> str:
    """
    Adds on parenthesis to the existing formula
    :param op: operator to find and parenthesis around
    :param string: the string we would want to add parenthesis on
    :return: the new string
    """
    if string.find(op) == -1:
        return string
    stripped_string = string[string.find(op) + 1:]
    stable_string = string[0:string.find(op)]
    return '(' + stable_string + op + create_written_formula(stripped_string, op) + ')'


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    true_element_list = list()
    for clause in model.keys():
        if model.get(clause):
            true_element_list.append(clause)  # Adds the element as T
        else:
            true_element_list.append('~' + clause)  # Adds the element as F
    formula_str = '&'.join(true_element_list)
    if len(true_element_list) > 1:
        formula_str = create_written_formula(formula_str, '&')  # Adds the parenthesis
    return Formula.parse(formula_str)

    # Task 2.6


def formula_gather(formulas: list) -> Formula:
    """
    Creates a big formula from small formulas, separates them with "or"
    :param formulas: list of formulas
    :return: the larger formula
    """
    if len(formulas) <= 1:
        return formulas[0]
    return Formula('|', formulas[0], formula_gather(formulas[1:]))


def contradiction_dnf(my_variables: list):
    """
    Creates a contradiction clause
    :param my_variables: list of variables to create the clause
    :return: A formula
    """
    string = my_variables[0] + '&~' + my_variables[0]
    my_variables.remove(my_variables[0])
    for var in my_variables:
        string += '&' + var + '&~' + var
    string = create_written_formula(string, '&')
    return Formula.parse(string)


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    my_variables = list(variables)
    models = all_models(variables)
    formulas = list()
    for i, boolean in enumerate(values):
        if boolean:
            mini_formula = _synthesize_for_model(list(models)[i])
            formulas.append(mini_formula)
    if len(formulas) == 0:
        formulas.append(contradiction_dnf(my_variables))  # Creates a contradiction clause
    elif len(formulas) == 1:
        return formulas[0]
    return formula_gather(formulas)

    # Task 2.7


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9


# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
