# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""
import itertools
from typing import AbstractSet, List, Set, Dict

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Returns:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    universe = model.universe
    constants = model.constant_meanings
    relations = dict(model.relation_meanings)
    for func in model.function_meanings:
        new_relation_name = function_name_to_relation_name(func)
        relation_set = set()
        for val in model.function_meanings[func]:
            relation_set.add((model.function_meanings[func][val], *val))
        new_relation = {new_relation_name: relation_set}
        relations.update(new_relation)
    return Model(universe, constants, relations)
    # Task 8.1


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    universe = model.universe
    constants = model.constant_meanings
    functions = dict(model.function_meanings)
    relations = dict(model.relation_meanings)

    for relation in model.relation_meanings:
        new_function_name = relation_name_to_function_name(relation)
        if new_function_name not in original_functions:
            continue
        function_dict = dict()
        variables_set = set()
        for tup in model.relation_meanings[relation]:
            if len(tup) <= 1:  # Checks if the tuple is too small to handle 2 or more variables
                return None
            y_val, x_val = tup[0], tup[1:]
            if x_val in variables_set:  # Checks if same values of x contribute different values
                return None
            variables_set.add(x_val)
            function_dict[tuple(x_val)] = y_val

        if not omega_cover(function_dict, universe):  # Checks if the current function covers all the ω in Ω
            return None
        new_function = {new_function_name: function_dict}
        functions.update(new_function)
        del relations[relation]
    return Model(universe, constants, relations, functions)
    # Task 8.2


def omega_cover(function_dict: dict, universe):
    """

    :param function_dict:
    :param universe:
    :return: True if the current function covers all the ω in Ω, false otherwise
    """
    return len(function_dict) == len(universe) ** len(next(iter(function_dict)))


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert variable[0] != 'z'
    formulas = list()
    _compile_term_helper(term, formulas)
    return formulas
    # Task 8.3


def _compile_term_helper(term: Term, formulas: list):
    if is_variable(term.root) or is_constant(term.root):
        return term.root
    compiled_args = [_compile_term_helper(arg, formulas) for arg in term.arguments]
    z = next(fresh_variable_name_generator)
    compiled_args = ','.join(compiled_args)
    substitute = f'{z}={term.root}({compiled_args})'
    formulas.append(Formula.parse(substitute))
    return z


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    new_formula = None
    if is_relation(formula.root) or is_equality(formula.root):
        compiled_terms = list()
        variables = list()
        # The next for loop creates a list of free variables and a list of compiled terms via compile_term function
        for term in formula.arguments:
            if is_function(term.root):
                compiled_terms.extend(_compile_term(term))
            else:
                variables.append(term)
        # Creates a list of the compiled term with formula i.e. [z1=f(x), R(z1)]
        new_relations_list = [*compiled_terms, create_relation_with_z(formula, compiled_terms, variables)]
        # Creates the wanted formula i.e. Az1[F(z1,x)->R(z1)]
        if compiled_terms:
            new_formula = concatenate_relation(new_relations_list)
        else:
            new_formula = formula
    if is_binary(formula.root):
        first_formula = replace_functions_with_relations_in_formula(formula.first)
        second_formula = replace_functions_with_relations_in_formula(formula.second)
        new_formula = Formula(formula.root, first_formula, second_formula)

    if is_unary(formula.root):
        first_formula = replace_functions_with_relations_in_formula(formula.first)
        new_formula = Formula(formula.root, first_formula)

    if is_quantifier(formula.root):
        predicate_formula = replace_functions_with_relations_in_formula(formula.predicate)
        new_formula = Formula(formula.root, formula.variable, predicate_formula)
    return new_formula

    # Task 8.4


def concatenate_relation(formulas: List[Formula], i: int = 0) -> Formula:
    """
    Concatenate relation with the list of formulas, putting an 'A' (all) statement for each of the formulas
    :param formulas: list of formulas with the relation at the end
    :param i: indicator on the string to know where we are
    :return:a concatenate formula
    Example:
    >>> concatenate_relation([Formula.parse("z1=f(x)"),Formula.parse("z2=g(x)"),Formula.parse("R(z1)")])
    :return formula of "Az1[(F(z1,x)&G(z2,x)->R(z1)]"
    """
    if i == len(formulas) - 1:
        new_formulas = multiple_equality_to_relation(formulas[:-1])
        new_formulas = '&'.join(new_formulas)
        return Formula('&', Formula.parse(create_written_formula(new_formulas, '&')), formulas[i])
    new_relation = equality_to_relation(formulas[i])
    var = new_relation.arguments[0].root
    new_formula = Formula('E', var, concatenate_relation(formulas, i + 1))
    return new_formula


def create_relation_with_z(formula: Formula, compiled_terms: List[Formula],
                           compiled_vars: List[Term] = None) -> Formula:
    """
    Creates a relation that contains only z as arguments
    :param formula: the formula we want to change the arguments
    :param compiled_terms: the terms in the form of z=f(x)
    :param compiled_vars: free variables
    :return: formula with only z and free variables as arguments
    For example:
            >>> create_relation_with_z(Formula.parse("R(f(g(x))"),[Formula.parse("z1=f(z1)"),Formula.parse("z2=g(x)")])
            :returns formula of R(z1)
    """
    if compiled_vars is None:
        compiled_vars = []
    relation_name = formula.root
    length_of_arguments = len(formula.arguments)
    relation_arguments = [c_term.arguments[0] for c_term in compiled_terms]
    relation_arguments += compiled_vars
    return Formula(relation_name, relation_arguments[-length_of_arguments:])


def equality_to_relation(formula: Formula) -> Formula:
    """
    Creates a relation from equality i.e: z1=f(x) to F(z1,x)
    :param formula: formula with equality as its root
    :return:
    """
    arg1 = formula.arguments[0]
    arg2 = formula.arguments[1]
    relation_name = function_name_to_relation_name(arg2.root)
    relation_terms = [arg1, *arg2.arguments]
    return Formula(relation_name, relation_terms)


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


def multiple_equality_to_relation(formulas: List[Formula]) -> list:
    """
    Creates a list of formulas from that has been transposed to relations i.e: z1=f(x),z2=g(x) to F(z1,x),G(z2,x)
    :param formulas: list of formulas with equality as its root
    :return:
    """
    new_formula = list()
    for formula in formulas:
        new_formula.append(str(equality_to_relation(formula)))
    return new_formula


def replace_functions_with_relations_in_formulas(formulas: AbstractSet[Formula]) -> Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    formulas_set = set()
    for formula in formulas:
        replaced_formula = replace_functions_with_relations_in_formula(formula)
        formulas_set.add(replaced_formula)
        for relation in replaced_formula.relations():
            if relation in formula.relations():
                continue
            # for every x there is a y
            additional_formula = Formula('A', 'x',
                                         Formula('E', 'z', Formula(relation[0], [Term.parse('z'), Term.parse('x')])))
            # If 2 x's gives us the same y, then x1=x2
            additional_formula2 = Formula.parse(
                "Ax[Az1[Az2[(({F}(z1,x)&{F}(z2,x))->z1=z2)]]]".format(F=relation[0]))
            super_additional = Formula('&', additional_formula, additional_formula2)
            formulas_set.add(super_additional)
    return formulas_set
    # Task 8.5


EQ_RELATION = "SAME"
def replace_equality_with_SAME_in_formula(formula: Formula) -> Formula:
    new_formula = None
    if is_equality(formula.root):
        new_relation_name = EQ_RELATION
        return Formula(new_relation_name, formula.arguments)
    if is_relation(formula.root):
        return formula
    if is_binary(formula.root):
        first_formula = replace_equality_with_SAME_in_formula(formula.first)
        second_formula = replace_equality_with_SAME_in_formula(formula.second)
        new_formula = Formula(formula.root, first_formula, second_formula)

    if is_unary(formula.root):
        first_formula = replace_equality_with_SAME_in_formula(formula.first)
        new_formula = Formula(formula.root, first_formula)

    if is_quantifier(formula.root):
        predicate_formula = replace_equality_with_SAME_in_formula(formula.predicate)
        new_formula = Formula(formula.root, formula.variable, predicate_formula)
    return new_formula


REQUIREMENTS = {"reflexive": lambda rel: Formula.parse("Ax[{relation}(x,x)]".format(relation=rel)),
                "symmetry": lambda rel: Formula.parse(
                    "Ax[Ay[({relation}(x,y)->{relation}(y,x))]]".format(relation=rel)),
                "transitivity": lambda rel: Formula.parse(
                    "Ax[Ay[Az[(({relation}(x,y)&{relation}(y,z))->{relation}(x,z))]]]".format(relation=rel)),
                "unary_R": lambda eq, rel: Formula.parse("Ax[Ay[({eq}(x,y)->({r}(x)->{r}(y)))]]".format(eq=eq, r=rel)),
                "binary_R": lambda eq, rel: Formula.parse(
                    "Ax1[Ax2[Ay1[Ay2[(({eq}(x1,y1)&{eq}(x2,y2))->({r}(x1,x2)->{r}(y1,y2)))]]]]".format(eq=eq, r=rel))
                }


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    formulas_set = set()
    for formula in formulas:
        compiled_formula = replace_equality_with_SAME_in_formula(formula)
        formulas_set.add(compiled_formula)
        ref_and_sym = Formula("&", REQUIREMENTS["reflexive"](EQ_RELATION), REQUIREMENTS["symmetry"](EQ_RELATION))
        ref_and_sym_and_tran = Formula("&", ref_and_sym, REQUIREMENTS["transitivity"](EQ_RELATION))
        for relation in formula.relations():
            if relation[1] == 1:
                unary_req_and_bi_req = REQUIREMENTS["unary_R"](EQ_RELATION, relation[0])
            else:
                unary_req_and_bi_req = REQUIREMENTS["binary_R"](EQ_RELATION, relation[0])
            all_req = Formula('&', ref_and_sym_and_tran, unary_req_and_bi_req)
            formulas_set.add(all_req)
    return formulas_set

    # Task 8.6


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Returns:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    universe = model.universe
    constants = model.constant_meanings
    functions = model.function_meanings
    relations = dict(model.relation_meanings)
    new_relation_name = EQ_RELATION
    new_relation_set = set()
    for om in universe:
        new_relation_set.add(tuple([om, om]))
    relations.update({new_relation_name: new_relation_set})
    return Model(universe, constants, relations, functions)
    # Task 8.7


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
#     universe = set(model.universe)
#     constants = dict(model.constant_meanings)
#     functions = dict(model.function_meanings)
#     relations = dict(model.relation_meanings)
#     eq_relation_meaning = sorted(list(relations[EQ_RELATION]))
#     eq_classes = {}
#     # for key, group in itertools.groupby(eq_relation_meaning, lambda k: k[0]):
#     #     eq_classes[key] = list(group)
#     # for key in eq_classes:
#     #     for ls in eq_classes[key]:
#     #         if ls[0] != ls[1]:
#     #             eq_classes[ls]
#     # print(eq_classes)
#     create_eq_classes(eq_relation_meaning)
#     return Model(universe, constants, relations, functions)
#     # Task 8.8
#
#
# def create_eq_classes(classes: List):
#     eq_classes: Dict[set] = {}
#     for tup in classes:
#         print(*eq_classes.values())
#         if tup[0] not in eq_classes:
#             eq_classes[tup[0]] = set()
#         eq_classes[tup[0]].add(tup[1])
