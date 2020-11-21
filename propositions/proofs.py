# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, \
    Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]


def longest_to_shortest_map(specialization_map1, specialization_map2):
    """

    :param specialization_map1:
    :param specialization_map2:
    :return: returns longest map and then the shortest map
    """
    if len(specialization_map1) > len(specialization_map2):
        longer_map = specialization_map1
        shorter_map = specialization_map2
    else:
        longer_map = specialization_map2
        shorter_map = specialization_map1
    return longer_map, shorter_map


@frozen
class InferenceRule:  # Clal heisek
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
               self.assumptions == other.assumptions and \
               self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        variables_set = self.assumption_variables()
        variables_set.update(self.conclusion_variables())
        return variables_set
        # Task 4.1

    def assumption_variables(self) -> Set[str]:
        """

        :return: returns the assumptions variables
        """
        variables = set()
        for formula in self.assumptions:
            for var in formula.variables():
                variables.add(var)
        return variables

    def conclusion_variables(self) -> Set[str]:
        """

        :return: returns the conclusion variables
        """
        return {var for var in self.conclusion.variables()}

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)
        switched_assumptions = []
        for assumption in self.assumptions:
            switched_assumptions.append(assumption.substitute_variables(specialization_map))
        switched_conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(switched_assumptions, switched_conclusion)

        # Task 4.4

    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        if specialization_map1 is None or specialization_map2 is None:
            return None
        longer_map, shorter_map = longest_to_shortest_map(specialization_map1, specialization_map2)
        united_specialization_map = dict(shorter_map)
        for var in longer_map:
            if var in shorter_map:
                if longer_map[var] != shorter_map[var]:
                    return None
            united_specialization_map.update({var: longer_map[var]})
        return united_specialization_map
        # Task 4.5a

    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        if is_variable(general.root):
            return {general.root: specialization}  # if we reached a leaf, map it with the whole specialization
        if is_constant(general.root):
            return {} if general.root == specialization.root else None  # return None if the constants are different
        spec_map = {}
        if specialization.root != general.root:
            return None  # different roots immediately denys specialization

        # Recursion on the tree #
        if is_binary(general.root):
            sub_map_first = InferenceRule._formula_specialization_map(general.first, specialization.first)
            if sub_map_first is None:
                return None

            sub_map_second = InferenceRule._formula_specialization_map(general.second, specialization.second)
            if sub_map_second is None:
                return None

            spec_map = InferenceRule._merge_specialization_maps(sub_map_first, sub_map_second)
            if spec_map is None:
                return None

        if is_unary(general.root):
            sub_map = InferenceRule._formula_specialization_map(general.first, specialization.first)
            if sub_map is None:
                return None
            spec_map.update(sub_map)
        return spec_map
        # Task 4.5b

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        specialization_map = {}
        if len(self.assumptions) != len(specialization.assumptions):
            return None
        for spec_assumption, assumption in zip(specialization.assumptions, self.assumptions):
            sub_spec_map = InferenceRule._formula_specialization_map(assumption, spec_assumption)
            if sub_spec_map is None:
                return None
            specialization_map = InferenceRule._merge_specialization_maps(sub_spec_map, specialization_map)
        conclusion_map = InferenceRule._formula_specialization_map(self.conclusion, specialization.conclusion)
        if conclusion_map is None:
            return None
        specialization_map = InferenceRule._merge_specialization_maps(conclusion_map, specialization_map)
        if not specialization_map:
            return None
        return specialization_map
        # Task 4.5c

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None


@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple of zero
                or more numbers of previous lines in the proof whose formulas
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]
        if line.is_assumption():  # No rule for this line
            return None
        assumptions = []
        for assumption in line.assumptions:
            assumptions.append(self.lines[assumption].formula)  # Taking the assumptions from previous lines
        conclusion = line.formula
        return InferenceRule(assumptions, conclusion)

        # Task 4.6a

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]
        if line.is_assumption():
            return line.formula in self.statement.assumptions  # Checks if it is part of the axioms
        if line.rule not in self.rules:
            return False
        inference_rule = self.rule_for_line(line_number)
        for assumption in line.assumptions:
            if assumption >= line_number:  # Checks if the assumptions are from previous lines
                return False
        return inference_rule.is_specialization_of(line.rule)

        # Task 4.6b

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        for line in range(len(self.lines)):
            if not self.is_line_valid(line):
                return False
        if not self.lines:  # No lines in the proof
            return False
        if self.lines[(len(self.lines) - 1)].is_assumption():
            if self.lines[(len(self.lines) - 1)].formula != self.statement.conclusion:
                return False
        elif self.rule_for_line(
                len(self.lines) - 1).conclusion != self.statement.conclusion:  # Checks if we reached the
            # conclusion at the end of the proof
            return False
        return True
        # Task 4.6c


# Chapter 5 tasks

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    new_lines = []
    lemma = specialization
    rules = proof.rules
    spec_map = InferenceRule.specialization_map(proof.statement, lemma)  # Creating the map to substitute the variables
    for i, line in enumerate(proof.lines):
        if line.is_assumption():
            new_lines.append(
                Proof.Line(
                    line.formula.substitute_variables(spec_map)))  # If assumption we only need the formula of the line
            continue
        specialized_rule_line = proof.rule_for_line(i).specialize(spec_map)
        new_lines.append(Proof.Line(specialized_rule_line.conclusion, line.rule, line.assumptions))
    return Proof(lemma, rules, new_lines)
    # Task 5.1


def _scan_proof_and_add_lines(lemma_spec_proof, lemma_assumption_dict, lines, line_number) -> Tuple[int, list]:
    assumption_counter = 0
    line_number_dic = {}  # A dictionary between proof numbers and the modified proof lines
    real_line_number = 0
    for num, line in enumerate(lemma_spec_proof.lines):
        if line.is_assumption():
            assumption_counter += 1
            continue
        assumptions = []
        line_number_dic.update({num: real_line_number})
        for i, assumption in enumerate(line.assumptions):
            if lemma_spec_proof.lines[assumption].is_assumption():  # If it is assumption, check where it was mapped to
                assumptions.append(lemma_assumption_dict[lemma_spec_proof.lines[assumption].formula])
            else:
                assumptions.append(line_number_dic[assumption] + line_number)
        lines.append(Proof.Line(line.formula, line.rule, assumptions))
        real_line_number += 1
    return assumption_counter, lines


def _map_between_assumption_and_line(assumptions, lines) -> dict:
    lemma_assumption_dict = {}
    for l, n in zip(lines, assumptions):
        lemma_assumption_dict.update({n: l})
    return lemma_assumption_dict


def _inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) \
        -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()

    lines = list(main_proof.lines[0:line_number])
    lemma_spec_proof = prove_specialization(lemma_proof, main_proof.rule_for_line(line_number))

    lemma_assumptions = list(main_proof.lines[line_number].assumptions)
    lemma_statement_assumptions = lemma_spec_proof.statement.assumptions

    # This is a dictionary that maps every assumption to its place in the main proof
    lemma_assumption_dict = _map_between_assumption_and_line(lemma_statement_assumptions, lemma_assumptions)
    assumption_counter, lines = _scan_proof_and_add_lines(lemma_spec_proof, lemma_assumption_dict, lines, line_number)
    last_proof_line = len(lemma_proof.lines) - assumption_counter

    last_lines = list(main_proof.lines[line_number + 1:])
    for line in last_lines:
        if line.is_assumption():
            lines.append(line)
            continue
        assumptions = []
        for assumption in line.assumptions:
            assumptions.append(
                assumption + last_proof_line - 1) if line_number <= assumption else assumptions.append(
                assumption)
        lines.append(Proof.Line(line.formula, line.rule, assumptions))
    rules = set(main_proof.rules.union(lemma_proof.rules))
    return Proof(main_proof.statement, rules, lines)


# Task 5.2a


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    for i, line in enumerate(main_proof.lines):
        if line.is_assumption():
            continue
        if main_proof.rule_for_line(i).is_specialization_of(lemma_proof.statement):
            proof = _inline_proof_once(main_proof, i, lemma_proof)
            return inline_proof(proof,
                                lemma_proof)  # After we changed one line, we go back to the proof to search for more
    rules = main_proof.rules.union(lemma_proof.rules).difference(
        {lemma_proof.statement})  # Because for some reason they included the lemma rule, so we got to remove it
    print(Proof(main_proof.statement, rules, main_proof.lines))
    return Proof(main_proof.statement, rules, main_proof.lines)
    # Task 5.2b
