# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    stringed_formula = str(formula)
    return not ('E' in stringed_formula or 'A' in stringed_formula)
    # Task 11.3.1


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    f = formula
    while is_quantifier(f.root):
        f = f.predicate
    return is_quantifier_free(f)
    # Task 11.3.2


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def _uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions)
    root = formula.root
    new_formula = formula
    if is_relation(root) or is_equality(root):
        prover.add_tautology(equivalence_of(formula, formula))
    if is_quantifier(root):
        predicate_f, predicate_p = _uniquely_rename_quantified_variables(formula.predicate)
        new_formula, var, new_var = new_quantifier_formula(predicate_f, formula)

        conclusion = predicate_p.conclusion
        add = prover.add_proof(conclusion, predicate_p)

        prove_quantifier(formula, new_formula, predicate_f, var, new_var, prover, add)
    if is_binary(root):
        first_f, first_p = _uniquely_rename_quantified_variables(formula.first)
        second_f, second_p = _uniquely_rename_quantified_variables(formula.second)
        new_formula = Formula(root, first_f, second_f)

        conclusion = first_p.conclusion
        add_1 = prover.add_proof(conclusion, first_p)
        conclusion = second_p.conclusion
        add_2 = prover.add_proof(conclusion, second_p)

        add_equivalence_tau_implication(prover, formula, new_formula, {add_1, add_2})
    if is_unary(root):
        first_f, first_p = _uniquely_rename_quantified_variables(formula.first)
        new_formula = Formula(root, first_f)
        conclusion = first_p.conclusion
        add = prover.add_proof(conclusion, first_p)
        add_equivalence_tau_implication(prover, formula, new_formula, {add})
    return new_formula, prover.qed()
    # Task 11.5


def prove_quantifier(formula: Formula, new_formula: Formula, predicate: Formula, var: str, new_var: str, prover: Prover,
                     step: int):
    p = prover.qed().conclusion
    q = equivalence_of(formula, new_formula)
    if formula.root == 'A':
        assumption = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
    else:
        assumption = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
    R = formula.predicate.substitute({var: Term("_")})
    Q = predicate.substitute({var: Term("_")})
    use_axiom = prover.add_instantiated_assumption("({p}->{q})".format(p=p, q=q), assumption,
                                                   {"R": R, "Q": Q, "x": var, "y": new_var})
    mp = prover.add_mp(q, step, use_axiom)
    return mp


def add_equivalence_tau_implication(prover: Prover, formula1: Formula, formula2: Formula, steps: set):
    equivalence = equivalence_of(formula1, formula2)
    prover.add_tautological_implication(equivalence, steps)


def new_quantifier_formula(predicate: Formula, formula: Formula):
    z = next(fresh_variable_name_generator)
    var = formula.variable
    predicate = predicate.substitute({var: Term(z)})
    new_formula = Formula(formula.root, z, predicate)
    return new_formula, var, z


def _pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions)
    new_formula = formula
    if is_quantifier(formula.first.root):
        quant_dict = {"A": ["E", 14, 0], "E": ["A", 15, 1]}  # mapping the transition and the wanted axioms
        quantifier = formula.first
        var = quantifier.variable
        new_quantifier = quant_dict[quantifier.root][0]
        negative = Formula("~", quantifier.predicate)
        new_predicate, proof = _pull_out_quantifications_across_negation(negative)
        new_formula = Formula(new_quantifier, var, new_predicate)

        conclusion = proof.conclusion
        add = prover.add_proof(conclusion, proof)
        negative_form = Formula(new_quantifier, var, negative)
        mp = axiom_14_15_basic_proof(prover, negative, new_predicate, [negative_form, new_formula], var, new_quantifier,
                                     add)

        assumption = ADDITIONAL_QUANTIFICATION_AXIOMS[quant_dict[quantifier.root][2]]
        R = quantifier.predicate.substitute({var: Term("_")})
        formula_eq_to_negative = equivalence_of(formula, Formula(new_quantifier, var, negative))
        use_axiom = prover.add_instantiated_assumption(formula_eq_to_negative, assumption, {"R": R, "x": var})

        formula_eq_to_final = equivalence_of(formula, new_formula)
        prover.add_tautological_implication(formula_eq_to_final, {mp, use_axiom})
    else:
        prover.add_tautology(equivalence_of(formula, formula))
    return new_formula, prover.qed()
    # Task 11.6


LEFT_BINARY_AXIOM = {"A": {"&": 2, "|": 6, "->": 10}, "E": {"&": 3, "|": 7, "->": 11}}


def _pull_out_quantifications_from_left_across_binary_operator(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions)
    new_formula = formula
    if is_quantifier(formula.first.root):
        quant_dict = {"A": ["E", 14], "E": ["A", 15]}  # mapping the transition and the wanted axioms
        op = formula.root
        quantifier = formula.first
        var = quantifier.variable
        new_quantifier_root = quant_dict[quantifier.root][0] if op == '->' else quantifier.root

        to_prove = Formula(op, quantifier.predicate, formula.second)
        predicate, proof = _pull_out_quantifications_from_left_across_binary_operator(to_prove)
        new_formula = Formula(new_quantifier_root, var, predicate)
        conclusion = proof.conclusion
        add = prover.add_proof(conclusion, proof)
        new_quantifier_form = Formula(new_quantifier_root, var, to_prove)
        mp = axiom_14_15_basic_proof(prover, to_prove, predicate, [new_quantifier_form, new_formula], var,
                                     new_quantifier_root, add)

        formula_eq_to_new = equivalence_of(formula, new_quantifier_form)
        assumption = ADDITIONAL_QUANTIFICATION_AXIOMS[LEFT_BINARY_AXIOM[quantifier.root][op]]
        R = quantifier.predicate.substitute({var: Term("_")})
        Q = formula.second
        use_axiom = prover.add_instantiated_assumption(formula_eq_to_new, assumption, {"R": R, "Q": Q, "x": var})

        formula_eq_to_new_formula = equivalence_of(formula, new_formula)
        prover.add_tautological_implication(formula_eq_to_new_formula, {mp, use_axiom})
    else:
        prover.add_tautology(equivalence_of(formula, formula))
    return new_formula, prover.qed()

    # Task 11.7.1


RIGHT_BINARY_AXIOM = {"A": {"&": 4, "|": 8, "->": 12}, "E": {"&": 5, "|": 9, "->": 13}}


def _pull_out_quantifications_from_right_across_binary_operator(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions)
    new_formula = formula
    if is_quantifier(formula.second.root):
        op = formula.root
        quantifier = formula.second
        var = quantifier.variable
        new_quantifier_root = quantifier.root

        to_prove = Formula(op, formula.first, quantifier.predicate)
        predicate, proof = _pull_out_quantifications_from_right_across_binary_operator(to_prove)
        new_formula = Formula(new_quantifier_root, var, predicate)
        new_quantifier_form = Formula(new_quantifier_root, var, to_prove)
        conclusion = proof.conclusion
        add = prover.add_proof(conclusion, proof)
        mp = axiom_14_15_basic_proof(prover, to_prove, predicate, [new_quantifier_form, new_formula], var,
                                     new_quantifier_root, add)

        formula_eq_to_new = equivalence_of(formula, new_quantifier_form)
        assumption = ADDITIONAL_QUANTIFICATION_AXIOMS[RIGHT_BINARY_AXIOM[quantifier.root][op]]
        R = quantifier.predicate.substitute({var: Term("_")})
        Q = formula.first
        use_axiom = prover.add_instantiated_assumption(formula_eq_to_new, assumption, {"R": R, "Q": Q, "x": var})

        formula_eq_to_new_formula = equivalence_of(formula, new_formula)
        prover.add_tautological_implication(formula_eq_to_new_formula, {mp, use_axiom})
    else:
        prover.add_tautology(equivalence_of(formula, formula))
    return new_formula, prover.qed()
    # Task 11.7.2


def _pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions)
    left_f, left_p = _pull_out_quantifications_from_left_across_binary_operator(formula)
    conclusion = left_p.conclusion
    add1 = prover.add_proof(conclusion, left_p)
    inner_predicate, list_of_vars = get_inner_predicate(left_f)  # gets the deepest predicate with all the used vars

    right_f, right_p = _pull_out_quantifications_from_right_across_binary_operator(inner_predicate)
    conclusion = right_p.conclusion
    add2 = prover.add_proof(conclusion, right_p)

    for quantifier, var in list_of_vars:
        add_quantifier_to_left = Formula(quantifier, var, inner_predicate)
        add_quantifier_to_right = Formula(quantifier, var, right_f)
        add2 = axiom_14_15_basic_proof(prover, inner_predicate, right_f,
                                       [add_quantifier_to_left, add_quantifier_to_right], var, quantifier, add2)
        inner_predicate = add_quantifier_to_left
        right_f = add_quantifier_to_right
    new_formula = right_f
    prover.add_tautological_implication(equivalence_of(formula, new_formula), {add1, add2})

    return new_formula, prover.qed()
    # Task 11.8


def axiom_14_15_basic_proof(prover: Prover, r_formula: Formula, q_formula: Formula, eq_formulas: List[Formula],
                            var: str, quantifier: str, last_step: int) -> int:
    quant_dict = {"A": 14, "E": 15}  # mapping the wanted axioms
    p = prover.qed().conclusion
    q = equivalence_of(eq_formulas[0], eq_formulas[1])
    R = r_formula.substitute({var: Term("_")})
    Q = q_formula.substitute({var: Term("_")})
    assumption = ADDITIONAL_QUANTIFICATION_AXIOMS[quant_dict[quantifier]]
    use_axiom = prover.add_instantiated_assumption("({p}->{q})".format(p=p, q=q), assumption,
                                                   {"R": R, "Q": Q, "x": var, "y": var})
    mp = prover.add_mp(q, last_step, use_axiom)
    return mp


def get_inner_predicate(formula: Formula):
    inner_predicate = formula
    list_of_vars = []
    while is_quantifier(inner_predicate.root):
        list_of_vars.append([inner_predicate.root, inner_predicate.variable])
        inner_predicate = inner_predicate.predicate
    list_of_vars.reverse()
    return inner_predicate, list_of_vars


def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.10
