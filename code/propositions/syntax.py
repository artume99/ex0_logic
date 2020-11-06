# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations

import copy
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdigit())


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'


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
    # For Chapter 3:
    # return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}


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
    """An immutable propositional formula in tree representation, composed from
    atomic propositions, and operators applied to them.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    OP_SET_OPTION = 1
    VAR_SET_OPTION = 2
    VAR_SET: set
    OP_SET: set

    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second
        self.VAR_SET = set()
        self.OP_SET = set()

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        rep = ""
        if self.root:
            if is_unary(self.root):
                rep += self.root + repr(self.first)
            elif is_binary(self.root):
                rep += '(' + repr(self.first)
                rep += self.root
                rep += repr(self.second) + ')'
            else:
                rep += self.root
        return rep

        # Task 1.1

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

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        return self.set_creator(self.VAR_SET_OPTION)
        # Task 1.2

    def set_creator(self, status: int):
        """
        Creates a set of both variables and operators, only if those haven't been created before
        :param status: which set do we need
        :return: the set required
        """
        if status == self.OP_SET_OPTION and self.OP_SET == set():  # if the operator set is empty and that's the set
            # what we are looking for
            self.set_creator_helper(self.VAR_SET, self.OP_SET)
        elif status == self.VAR_SET_OPTION and self.VAR_SET == set():  # if the variables set is empty and that's the
            # set what we are looking for
            self.set_creator_helper(self.VAR_SET, self.OP_SET)
        return {
            self.OP_SET_OPTION: self.OP_SET,
            self.VAR_SET_OPTION: self.VAR_SET
        }.get(status)

    def set_creator_helper(self, var_set: Set = None, op_set: Set = None):
        """
        A helper to find all the variables in the formula
        :param op_set: a set of operators to append up on
        :param var_set: a set on variables to append up on
        :return: just changes the sets.
        """
        if is_unary(self.root):
            op_set.add(self.root)
            self.first.set_creator_helper(var_set, op_set)
        elif is_binary(self.root):
            op_set.add(self.root)
            self.first.set_creator_helper(var_set, op_set)
            self.second.set_creator_helper(var_set, op_set)
        else:
            if is_variable(self.root):  # to remove the option of constants
                var_set.add(self.root)
            else:
                op_set.add(self.root)
            return

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        return self.set_creator(self.OP_SET_OPTION)
        # Task 1.3

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator follows by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        new_string = copy.deepcopy(string)
        formula = None
        finished_string = str()
        i = 0
        if not string:
            return formula, new_string
        if string[0] == '(':
            first_formula, new_string = Formula._parse_prefix(string[1:])  # Creating the first formula

            root, new_string = root_check(new_string)
            if not is_binary(root):  # Checking the "middle" part, if it is binary
                return None, new_string

            second_formula, new_string = Formula._parse_prefix(new_string[1:])  # Creating the second formula
            if new_string == str() or not new_string[0] == ')':
                return None, string

            new_string = new_string.replace(")", '', 1)  # Checking and removing the closing parentheses
            formula = Formula(root, first_formula, second_formula)

        elif is_variable(string[0]) or is_constant(string[0]):
            while i < len(string) and (
                    is_variable(string[0:i + 1]) or is_constant(string[0:i + 1])):  # Creating a variable/constant
                finished_string += string[i]
                i += 1
            formula = Formula(finished_string)
            new_string = string[i:]

        elif is_binary(string[0]):
            formula = None

        elif is_unary(string[0]):
            if len(string) < 2:
                return formula, new_string
            formula, new_string = Formula._parse_prefix(string[1:])  # Recursive call for the unary parameter
            formula = Formula(string[0], formula)

        return formula, new_string
        # Task 1.4

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        return not Formula._parse_prefix(string)[1] and not string == str()

    # Task 1.5

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        return Formula._parse_prefix(string)[0]
        # Task 1.6

    # Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variables originating in the current formula are substituted (i.e.,
            variables originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operators originating in the current formula are substituted (i.e.,
            operators originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
