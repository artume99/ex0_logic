# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/soundness.py

"""Programmatic proof of the soundness of Propositional Logic."""

from typing import Tuple

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *


def rule_nonsoundness_from_specialization_nonsoundness(
        general: InferenceRule, specialization: InferenceRule, model: Model) \
        -> Model:
    """Demonstrated the non-soundness of the given general inference rule given
    an example of the non-soundness of the given specialization of this rule.

    Parameters:
        general: inference rule to the soundness of which to find a
            counterexample.
        specialization: non-sound specialization of `general`.
        model: model in which `specialization` does not hold.

    Returns:
        A model in which `general` does not hold.
    """
    assert specialization.is_specialization_of(general)
    assert not evaluate_inference(specialization, model)
    spec_map = InferenceRule.specialization_map(general, specialization)
    counter_model = {}
    for gen, spec in spec_map.items():  # Loop over the map use the formula of the specialize rule to evaluate the
        # value of the general formula, this should give us a counter example
        counter_model.update({gen: evaluate(spec, model)})
    return counter_model
    # Task 4.9


def nonsound_rule_of_nonsound_proof(proof: Proof, model: Model) -> \
        Tuple[InferenceRule, Model]:
    """Finds a non-sound inference rule used by the given valid proof of a
    non-sound inference rule, and demonstrates the non-soundness of the former
    rule.

    Parameters:
        proof: valid proof of a non-sound inference rule.
        model: model in which the inference rule proved by the given proof does
            not hold.

    Returns:
        A pair of a non-sound inference rule used in the given proof and a model
        in which this rule does not hold.
    """
    assert proof.is_valid()
    assert not evaluate_inference(proof.statement, model)
    counter_model = {}
    counter_inference_rule = None
    for line_number, line in enumerate(proof.lines):
        # Loop over the lines and check if each line rule is true. if we meet a bad line (by the given model),
        # find the counter model example from the previous method.
        line_rule = proof.rule_for_line(line_number)
        if line_rule is None:
            continue
        if not evaluate_inference(line_rule, model):
            counter_model = rule_nonsoundness_from_specialization_nonsoundness(line.rule, line_rule, model)
            counter_inference_rule = line.rule
    return counter_inference_rule, counter_model

    # Task 4.10
