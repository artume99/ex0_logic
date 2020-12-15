# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations

import copy
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen, \
    memoized_parameterless_method

from propositions.syntax import Formula as PropositionalFormula, \
    is_variable as is_propositional_variable


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """
    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (((string[0] >= '0' and string[0] <= '9') or \
             (string[0] >= 'a' and string[0] <= 'd')) and \
            string.isalnum()) or string == '_'


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'u' and string[0] <= 'z' and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= 'f' and string[0] <= 't' and string.isalnum()


def check_forbidden(variables: set, forbidden_variables):
    for var in variables:
        if var in forbidden_variables:
            raise ForbiddenVariableError(var)


@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0
        self.FUNC_SET = set()
        self.CONST_SET = set()
        self.VAR_SET = set()

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        elif is_function(self.root):
            arguments = self.arguments
            constructed_string = self.root + "("
            for i in range(len(arguments)):
                if i < len(arguments) - 1:
                    constructed_string = constructed_string + str(arguments[
                                                                      i]) + ","
                else:
                    constructed_string = constructed_string + str(arguments[i])
            constructed_string = constructed_string + ")"
            return constructed_string
        else:
            raise Exception("unknown syntax")
        # Task 7.1

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        remained_term = ""
        term = None
        if is_function(string[0]):
            root, remained_term = string.split('(', 1)
            arguments = []
            # While loop to catch all the arguments of the formula
            while True:
                arg, remained_term = Term._parse_prefix(remained_term)
                arguments.append(arg)
                if remained_term[0] == ')':  # End of arguments
                    break
                remained_term = remained_term[1:]
            remained_term = remained_term.replace(')', "", 1)  # Remove closing parenthesis
            term = Term(root, arguments)
        if is_constant(string[0]) or is_variable(string[0]):
            finished_string, i = Term._construct_variable_name(string)
            term = Term(finished_string)
            remained_term = string[i:]
        return term, remained_term

        # Task 7.3.1

    @staticmethod
    def _construct_variable_name(string: str) -> Tuple[str, int]:
        i = 0
        finished_string = ''
        while i < len(string) and (
                is_variable(string[0:i + 1]) or is_constant(string[0:i + 1])):
            finished_string += string[i]
            i += 1
        return finished_string, i

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        return Term._parse_prefix(string)[0]
        # Task 7.3.2

    def set_creator(self, func_set, const_set, var_set):
        if is_function(self.root):
            for arg in self.arguments:
                arg.set_creator(func_set, const_set, var_set)
            func_set.add((self.root, len(self.arguments)))
        if is_constant(self.root):
            const_set.add(self.root)
        if is_variable(self.root):
            var_set.add(self.root)

    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        if not self.CONST_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET)
        return self.CONST_SET
        # Task 7.5.1

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        if not self.VAR_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET)
        return self.VAR_SET
        # Task 7.5.2

    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        if not self.FUNC_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET)
        return self.FUNC_SET
        # Task 7.5.3

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        if self.root in substitution_map:  # Checks if the current root needs to be replaced
            sub_term = substitution_map[self.root]
            if is_variable(sub_term.root):
                check_forbidden(set(sub_term.root), forbidden_variables)
                return Term(sub_term.root)
            if is_constant(sub_term.root):
                return Term(sub_term.root)
            if is_function(sub_term.root):
                check_forbidden(sub_term.variables(), forbidden_variables)
                return Term(sub_term.root, sub_term.arguments)

        if is_function(self.root):
            sub_args = [arg.substitute(substitution_map, forbidden_variables) for arg in self.arguments]
            return Term(self.root, sub_args)
        return self  # If no change needed return the current term

        # Task 9.1


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == '='


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= 'F' and string[0] <= 'T' and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == '&' or string == '|' or string == '->'


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == 'A' or string == 'E'


def root_check(string: str):
    """
    Creating and checking the validation of a root
    :param string: a string from which we construct root
    :return: a root and a the modified string
    """
    new_string = string
    root = string[0]
    if root == '-' and len(string) >= 2:
        root = string[0:2]
        new_string = string[1:]
    return root, new_string


@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the root, if the
                root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate
        self.CONST_SET = set()
        self.VAR_SET = set()
        self.FREE_VAR_SET = set()
        self.FUNC_SET = set()
        self.RELATION_SET = set()

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        elif is_equality(self.root):
            return str(self.arguments[0]) + "=" + str(self.arguments[1])
        elif is_unary(self.root):
            return self.root + str(self.first)
        elif is_quantifier(self.root):
            return self.root + self.variable + "[" + str(self.predicate) + "]"
        elif is_binary(self.root):
            return "(" + str(self.first) + self.root + str(self.second) + ")"
        elif is_relation(self.root):
            arguments = self.arguments
            relation_string = self.root + "("
            if len(arguments) == 0:
                relation_string = relation_string + ")"
            for i in range(len(arguments)):
                if i < len(arguments) - 1:
                    relation_string = relation_string + str(arguments[i]) + ","
                else:
                    relation_string = relation_string + str(arguments[i]) + ")"
            return relation_string
        else:
            raise Exception("unknown syntax")
        # Task 7.2

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        remained_string = copy.deepcopy(string)
        formula = None
        if string[0] == '(':
            first_formula, remained_string = Formula._parse_prefix(string[1:])  # Creating the first formula
            root, remained_string = root_check(remained_string)
            second_formula, remained_string = Formula._parse_prefix(remained_string[1:])  # Creating the second formula
            remained_string = remained_string.replace(")", '', 1)  # Checking and removing the closing parentheses
            formula = Formula(root, first_formula, second_formula)

        if is_quantifier(string[0]):
            before, remained_string = string.split('[', 1)
            root, var = before[0], before[1:]
            predicate, remained_string = Formula._parse_prefix(remained_string)
            remained_string = remained_string.replace("]", '', 1)
            formula = Formula(root, var, predicate)

        if is_variable(string[0]) or is_constant(string[0]) or is_function(string[0]):
            first, remained_string = Term._parse_prefix(string)
            eq = remained_string[0]
            second, remained_string = Term._parse_prefix(remained_string[1:])
            formula = Formula(eq, [first, second])

        if is_relation(string[0]):
            root, remained_string = string.split('(', 1)
            arguments = []
            if remained_string[0] == ')':
                remained_string = remained_string.replace(')', "", 1)
                formula = Formula(root, arguments)
            else:
                # While loop to catch all the arguments of the formula
                while True:
                    arg, remained_string = Term._parse_prefix(remained_string)
                    arguments.append(arg)
                    if remained_string[0] == ')':  # End of arguments
                        break
                    remained_string = remained_string[1:]
                remained_string = remained_string.replace(')', "", 1)  # Remove closing parenthesis
                formula = Formula(root, arguments)

        if is_unary(string[0]):
            formula, remained_string = Formula._parse_prefix(string[1:])  # Recursive call for the unary parameter
            formula = Formula(string[0], formula)
        return formula, remained_string

        # Task 7.4.1

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        return Formula._parse_prefix(string)[0]
        # Task 7.4.2

    def set_creator(self, func_set: set, const_set: set, var_set: set, relation_set: set, free_var_set: set,
                    bad_vars=None):
        if bad_vars is None:
            bad_vars = set()
        if is_binary(self.root):
            self.first.set_creator(func_set, const_set, var_set, relation_set, free_var_set, bad_vars)
            self.second.set_creator(func_set, const_set, var_set, relation_set, free_var_set, bad_vars)
        if is_unary(self.root):
            self.first.set_creator(func_set, const_set, var_set, relation_set, free_var_set, bad_vars)
        if is_quantifier(self.root):
            bad_vars.add(self.variable)
            var_set.add(self.variable)
            self.predicate.set_creator(func_set, const_set, var_set, relation_set, free_var_set, bad_vars)
            bad_vars.clear()  # Clears the bad vars for next quantifier
        if is_relation(self.root):
            relation_set.add((self.root, len(self.arguments)))
            for arg in self.arguments:
                func_set.update(arg.functions())
                const_set.update(arg.constants())
                variables = arg.variables()
                var_set.update(variables)
                variables = var_set - bad_vars
                free_var_set.update(variables)

        if is_equality(self.root):
            func_set.update(self.arguments[0].functions(), self.arguments[1].functions())
            const_set.update(self.arguments[0].constants(), self.arguments[1].constants())
            variables = self.arguments[0].variables().union(self.arguments[1].variables())
            var_set.update(variables)
            variables = var_set - bad_vars
            free_var_set.update(variables)

    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        if not self.CONST_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET, self.RELATION_SET, self.FREE_VAR_SET)
        return self.CONST_SET
        # Task 7.6.1

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        if not self.VAR_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET, self.RELATION_SET, self.FREE_VAR_SET)
        return self.VAR_SET
        # Task 7.6.2

    @memoized_parameterless_method
    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.
        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6.3
        free_variables = set()
        forbidden = set()
        return self.free_variables_helper(free_variables, forbidden)

    @staticmethod
    def handle_forbidden(variables: set, forbidden: set):
        """
        method to clean forbidden-s out of variables
        Args:
            variables: given variables
            forbidden: given forbidden variables
        Returns: set of non forbidden-s
        """
        new_set = set()
        for var in variables:
            if var not in forbidden:
                new_set.add(var)
        return new_set

    def free_variables_helper(self, free_variables: set, forbidden: set):
        """
        method to handle free variables
        Args:
            free_variables: free variables till now
            forbidden: forbiddens till now
        Returns:
        """
        if is_equality(self.root):
            first_sub_vars = self.arguments[0].variables()
            second_sub_vars = self.arguments[1].variables()
            variables = first_sub_vars.union(second_sub_vars)
            variables = Formula.handle_forbidden(variables, forbidden)
            free_variables = free_variables.union(variables)
        elif is_relation(self.root):
            arguments = self.arguments
            for arg in arguments:
                sub_variables = arg.variables()
                free_variables = free_variables.union(sub_variables)
            free_variables = Formula.handle_forbidden(free_variables,
                                                      forbidden)
        elif is_unary(self.root) | is_binary(self.root):
            free_variables = free_variables.union(self.first.free_variables())
            free_variables = Formula.handle_forbidden(free_variables,
                                                      forbidden)
        if is_binary(self.root):
            free_variables = free_variables.union(self.second.free_variables())
            free_variables = Formula.handle_forbidden(free_variables,
                                                      forbidden)
        elif is_quantifier(self.root):
            var = self.variable
            forbidden.add(var)
            free_variables = free_variables.union(
                self.predicate.free_variables())
            free_variables = Formula.handle_forbidden(free_variables,
                                                      forbidden)
        return free_variables

    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        if not self.FUNC_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET, self.RELATION_SET, self.FREE_VAR_SET)
        return self.FUNC_SET
        # Task 7.6.4

    @memoized_parameterless_method
    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        if not self.RELATION_SET:
            self.set_creator(self.FUNC_SET, self.CONST_SET, self.VAR_SET, self.RELATION_SET, self.FREE_VAR_SET)
        return self.RELATION_SET

    def formula_relations_helper(self, relations: set):
        """
        helper method for formula functions finder
        Args:
            relations: functions till now
        Returns: all formula functions
        """
        if is_equality(self.root):
            first_sub_rels = self.arguments[0].relations()
            second_sub_rels = self.arguments[1].relations()
            relations = relations.union(first_sub_rels)
            relations = relations.union(second_sub_rels)
        elif is_relation(self.root):
            arguments = self.arguments
            arg_len = len(arguments)
            relations.add((self.root, arg_len))
            for arg in arguments:
                sub_relations = arg.relations()
                relations = relations.union(sub_relations)
        elif is_unary(self.root) | is_binary(self.root):
            relations = relations.union(self.first.relations())
        if is_binary(self.root):
            relations = relations.union(self.second.relations())
        elif is_quantifier(self.root):
            relations = relations.union(self.predicate.relations())
        return relations

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
            Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        if is_relation(self.root) or is_equality(self.root):
            sub_args = [arg.substitute(substitution_map, forbidden_variables) for arg in self.arguments]
            return Formula(self.root, sub_args)
        if is_binary(self.root):
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables),
                           self.second.substitute(substitution_map, forbidden_variables))
        if is_unary(self.root):
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables))
        if is_quantifier(self.root):
            extended_forbidden = set(forbidden_variables).union(self.variable)
            new_sub_map = {var: sub for var, sub in substitution_map.items() if var != self.variable}
            return Formula(self.root, self.variable, self.predicate.substitute(new_sub_map, extended_forbidden))
        return self  # If no change needed return the current term
        # Task 9.2

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each atomic
            propositional formula to the subformula for which it was
            substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(x=7->~Q(y)))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(z2->~z3)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(z5->~z6)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each atomic propositional subformula
                of the given skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each atomic propositional subformula with
            the formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(z2->~z3))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(x=7->~Q(y)))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
