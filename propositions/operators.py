# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    sub_F = dict({'F': Formula.parse('(p&~p)')})
    sub_T = dict({'T': Formula.parse('(p|~p)')})
    sub_F.update(sub_T)
    sub_iff = dict({'<->': Formula.parse('((p&q)|(~p&~q))')})
    sub_F.update(sub_iff)
    sub_xor = dict({'+': Formula.parse('((p&~q)|(~p&q))')})
    sub_F.update(sub_xor)
    sub_if = dict({'->': Formula.parse('(~p|q)')})
    sub_F.update(sub_if)
    sub_nand = dict({'-&': Formula.parse('~(p&q)')})
    sub_F.update(sub_nand)
    sub_nor = dict({'-|': Formula.parse('~(p|q)')})
    sub_F.update(sub_nor)
    return formula.substitute_operators(sub_F)
    # Task 3.5


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    sub_F = dict({'F': Formula.parse('(p&~p)')})
    sub_or = dict({'|': Formula.parse('~(~p&~q)')})
    sub_F.update(sub_or)
    sub_T = dict({'T': Formula.parse('~(~p&~~p)')})
    sub_F.update(sub_T)
    sub_iff = dict({'<->': Formula.parse('~(~(p&q)&~(~p&~q))')})
    sub_F.update(sub_iff)
    sub_xor = dict({'+': Formula.parse('~(~(p&~q)&~(~p&q))')})
    sub_F.update(sub_xor)
    sub_if = dict({'->': Formula.parse('~(~~p&~q)')})
    sub_F.update(sub_if)
    sub_nand = dict({'-&': Formula.parse('~(p&q)')})
    sub_F.update(sub_nand)
    sub_nor = dict({'-|': Formula.parse('~~(~p&~q)')})
    sub_F.update(sub_nor)
    return formula.substitute_operators(sub_F)

    # Task 3.6a


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    sub_F = dict({'F': Formula.parse('((p-&(p-&p))-&(p-&(p-&p)))')})
    sub_not = dict({'~': Formula.parse('(p-&p)')})
    sub_F.update(sub_not)
    sub_and = dict({'&': Formula.parse('((p-&q)-&(p-&q))')})
    sub_F.update(sub_and)
    sub_and.update(sub_not)
    sub_or = dict({'|': Formula.parse('((p-&p)-&(q-&q))')})
    sub_F.update(sub_or)
    sub_T = dict({'T': Formula.parse('((p-&p)-&p)')})
    sub_F.update(sub_T)
    sub_iff = dict({'<->': Formula.parse('~(~(p&q)&~(~p&~q))').substitute_operators(sub_and)})
    sub_F.update(sub_iff)
    sub_xor = dict({'+': (Formula.parse('~(~(p&~q)&~(~p&q))')).substitute_operators(sub_and)})
    sub_F.update(sub_xor)
    sub_if = dict({'->': Formula.parse('~(~~p&~q)').substitute_operators(sub_and)})
    sub_F.update(sub_if)
    sub_nor = dict({'-|': Formula.parse('~~(~p&~q)').substitute_operators(sub_and)})
    sub_F.update(sub_nor)
    return formula.substitute_operators(sub_F)
    # Task 3.6b


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    sub_F = dict({'F': Formula.parse('~(p->p)')})
    sub_nand = dict({'-&': Formula.parse('(q->(p->~(p->p)))')})
    sub_F.update(sub_nand)
    sub_and = dict({'&': (Formula.parse('((p-&q)-&(p-&q))')).substitute_operators(sub_nand)})
    sub_F.update(sub_and)
    sub_or = dict({'|': Formula.parse('((p-&p)-&(q-&q))').substitute_operators(sub_nand)})
    sub_F.update(sub_or)
    sub_T = dict({'T': Formula.parse('~~(p->p)')})
    sub_F.update(sub_T)
    sub_iff = dict({'<->': Formula.parse('~(~(p&q)&~(~p&~q))').substitute_operators(sub_and)})
    sub_F.update(sub_iff)
    sub_xor = dict({'+': (Formula.parse('~(~(p&~q)&~(~p&q))')).substitute_operators(sub_and)})
    sub_F.update(sub_xor)
    sub_if = dict({'->': Formula.parse('~(~~p&~q)').substitute_operators(sub_and)})
    sub_F.update(sub_if)
    sub_nor = dict({'-|': Formula.parse('~~(~p&~q)').substitute_operators(sub_and)})
    sub_F.update(sub_nor)
    return formula.substitute_operators(sub_F)
    # Task 3.6c


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    sub_nand = dict({'-&': Formula.parse('(q->(p->F))')})
    sub_F = dict({'~': Formula.parse('(p-&p)').substitute_operators(sub_nand)})
    sub_F.update(sub_nand)
    sub_and = dict({'&': (Formula.parse('((p-&q)-&(p-&q))')).substitute_operators(sub_F)})
    sub_F.update(sub_and)
    sub_or = dict({'|': Formula.parse('((p-&p)-&(q-&q))').substitute_operators(sub_nand)})
    sub_F.update(sub_or)
    sub_and.update(sub_F)
    sub_T = dict({'T': Formula.parse('((p-&p)-&p)').substitute_operators(sub_nand)})
    sub_F.update(sub_T)
    sub_iff = dict({'<->': Formula.parse('~(~(p&q)&~(~p&~q))').substitute_operators(sub_and)})
    sub_F.update(sub_iff)
    sub_xor = dict({'+': (Formula.parse('~(~(p&~q)&~(~p&q))')).substitute_operators(sub_and)})
    sub_F.update(sub_xor)
    sub_if = dict({'->': Formula.parse('~(~~p&~q)').substitute_operators(sub_and)})
    sub_F.update(sub_if)
    sub_nor = dict({'-|': Formula.parse('~~(~p&~q)').substitute_operators(sub_and)})
    sub_F.update(sub_nor)
    return formula.substitute_operators(sub_F)
    # Task 3.6d
