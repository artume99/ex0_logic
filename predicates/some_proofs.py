# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/some_proofs.py

"""Some proofs in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import equivalence_of


def syllogism_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.qed()


def syllogism_proof_with_universal_instantiation(print_as_proof_forms: bool =
                                                 False) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.qed()


def syllogism_all_all_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.qed()


def syllogism_all_all_proof_with_tautological_implication(print_as_proof_forms:
bool = False) -> \
        Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_implication(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.qed()


def syllogism_all_exists_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R': 'Man(_)', 'Q': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_implication(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.qed()


def syllogism_all_exists_proof_with_existential_derivation(print_as_proof_forms:
bool = False) -> \
        Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.qed()


def lovers_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)
    
    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'},
                    print_as_proof_forms)
    # Task 10.4
    assump_1_form = Formula.parse("Ax[Ey[Loves(x,y)]]")
    first_assumption = prover.add_assumption(assump_1_form)

    # Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]
    assump_2_form = Formula.parse("Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]")
    second_assumption = prover.add_assumption(assump_2_form)

    exists_y_loves_x_y = "Ey[Loves(x,y)]"
    exists_loves_x_y_index = prover.add_universal_instantiation(
        exists_y_loves_x_y,
        first_assumption,
        assump_1_form.variable)

    x_clean_index = prover.add_universal_instantiation(
        "Az[Ay[(Loves(x,y)->Loves(z,x))]]",
        second_assumption,
        assump_2_form.variable)

    all_y_loves_to_love = "Ay[(Loves(x,y)->Loves(z,x))]"
    a_var = "z"
    z_clean_index = prover.add_universal_instantiation(
        all_y_loves_to_love,
        x_clean_index,
        a_var)

    loves_to_love = "(Loves(x,y)->Loves(z,x))"
    a_var = "y"
    y_clean_index = prover.add_universal_instantiation(
        loves_to_love,
        z_clean_index,
        a_var)

    loves_z_x = "Loves(z,x)"
    e_s_line = prover.add_existential_derivation(loves_z_x,
                                                 exists_loves_x_y_index,
                                                 y_clean_index)

    all_z = "Az[Loves(z,x)]"
    all_y = "Ax[" + all_z + "]"

    all_z_index = prover.add_ug(all_z, e_s_line)
    prover.add_ug(all_y, all_z_index)
    return prover.qed()


def homework_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)
    
    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'}, print_as_proof_forms)
    assump_1_form = Formula.parse("~Ex[(Homework(x)&Fun(x)]")
    first_assumption = prover.add_assumption(assump_1_form)

    # Ex[(Homework(x)&Reading(x))]
    assump_2_form = Formula.parse("Ex[(Homework(x)&Reading(x))]")
    second_assumption = prover.add_assumption(assump_2_form)

    EI_form = Formula.parse("((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])")
    ei_dict = {"R": "(Homework(_)&Fun(_))",
               "x": "x",
               "c": "x"
               }
    ei_line = prover.add_instantiated_assumption(EI_form, Prover.EI, ei_dict)

    taut_line = Formula.parse(
        "(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))")
    tautulogy_line = prover.add_tautological_implication(taut_line, {ei_line})

    not_all_homework_fun = Formula.parse("~(Homework(x)&Fun(x))")
    mp_line = prover.add_mp(not_all_homework_fun, first_assumption,
                            tautulogy_line)

    EI_form = Formula.parse("((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])")
    ei_dict = {"R": "(Reading(_)&~Fun(_))",
               "x": "x",
               "c": "x"
               }
    ei_2_line = prover.add_instantiated_assumption(EI_form, Prover.EI, ei_dict)

    taut_line_2 = Formula.parse("((Homework(x)&Reading(x))->(Reading(x)&~Fun("
                                "x)))")
    tautulogy_line_2 = prover.add_tautological_implication(taut_line_2,
                                                           {mp_line})

    taut_line_3 = Formula.parse(
        "((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])")
    tautulogy_line_3 = prover.add_tautological_implication(taut_line_3,
                                                           {ei_2_line,
                                                            tautulogy_line_2})

    existence = Formula.parse("Ex[(Reading(x)&~Fun(x))]")
    prover.add_existential_derivation(existence,
                                      second_assumption, tautulogy_line_3)
    # Task 10.5
    return prover.qed()


#: The three group axioms
GROUP_AXIOMS = frozenset({'plus(0,x)=x', 'plus(minus(x),x)=0',
                          'plus(plus(x,y),z)=plus(x,plus(y,z))'})


def right_neutral_proof(stop_before_flipped_equality: bool,
                        stop_before_free_instantiation: bool,
                        stop_before_substituted_equality: bool,
                        stop_before_chained_equality: bool,
                        print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof constructed up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof constructed up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof constructed up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof constructed up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(_,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(_,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),_),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),_)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),_)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)', flipped_associativity,
        {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(_,x)')
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.qed()


def unique_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), print_as_proof_forms)
    # __________GROUP AXIOMS__________ #
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    a_associativity = prover.add_assumption(
        'plus(plus(x,y),z)=plus(x,plus(y,z))')

    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_a_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', a_associativity)
    first_line = "plus(a,c)=a"
    first_assump_line = prover.add_assumption(first_line)

    instance = Formula.parse(
        "plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)")

    sub_map = {"x": "minus(a)",
               "y": "a",
               "z": "c"}
    minus_plus_ = prover.add_free_instantiation(instance,
                                                flipped_a_associativity,
                                                sub_map)

    instance = Formula.parse("plus(minus(a),a)=0")
    sub_map = {"x": "a"}
    negation_c = prover.add_free_instantiation(instance, negation, sub_map)

    sub = "plus(plus(minus(a),a),c)=plus(0,c)"
    param_term = "plus(_,c)"
    plus_minus = prover.add_substituted_equality(sub, negation_c, param_term)

    chained_lines = [minus_plus_, plus_minus]
    chained = "plus(minus(a),plus(a,c))=plus(0,c)"
    chained_line = prover.add_chained_equality(chained, chained_lines)

    sub = "plus(minus(a),plus(a,c))=plus(minus(a),a)"
    param_term = "plus(minus(a),_)"
    after_first_assump = prover.add_substituted_equality(sub,
                                                         first_assump_line,
                                                         param_term)

    sub = "plus(0,c)=plus(minus(a),plus(a,c))"
    flipped_chained = prover.add_flipped_equality(sub, chained_line)

    instance = Formula.parse("c=plus(0,c)")
    sub_map = {"x": "c"}
    c_is_0_c = prover.add_free_instantiation(instance, flipped_zero, sub_map)

    instance = Formula.parse("plus(minus(a),a)=0")
    sub_map = {"x": "a"}
    a_minus_a_0 = prover.add_free_instantiation(instance, negation, sub_map)

    chained_lines = [c_is_0_c, flipped_chained, after_first_assump,
                     a_minus_a_0]
    chained = "c=0"
    chained_line = prover.add_chained_equality(chained, chained_lines)

    # Task 10.10
    return prover.qed()


#: The six field axioms
FIELD_AXIOMS = frozenset(GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'}))


def multiply_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # In the next assumptions and proof in general, a stands for addition, m for multiplication

    # ___________________________GROUP AXIOMS_____________________________ #
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    a_associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')

    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_a_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', a_associativity)

    # __________________________FIELD AXIOMS________________________________ #
    a_commutativity = prover.add_assumption('plus(x,y)=plus(y,x)')
    m_commutativity = prover.add_assumption('times(x,y)=times(y,x)')
    one = prover.add_assumption('times(x,1)=x')
    m_associativity = prover.add_assumption('times(times(x,y),z)=times(x,times(y,z))')
    distributivity = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    inverse = prover.add_assumption('(~x=0->Ey[times(y,x)=1])')

    flipped_a_commutativity = prover.add_flipped_equality('plus(y,x)=plus(x,y)', a_commutativity)
    flipped_m_commutativity = prover.add_flipped_equality('times(y,x)=times(x,y)', m_commutativity)
    flipped_one = prover.add_flipped_equality('x=times(x,1)', one)
    flipped_m_associativity = prover.add_flipped_equality('times(x,times(y,z))=times(times(x,y),z)', m_associativity)
    flipped_distributivity = prover.add_flipped_equality('plus(times(x,y),times(x,z))=times(x,plus(y,z))',
                                                         distributivity)

    # ___________________________PROOF START_________________________________ #
    step1 = prover.add_free_instantiation("0=plus(0,0)", flipped_zero, {"x": "0"})
    step2 = prover.add_substituted_equality("times(x,0)=times(x,plus(0,0))", step1, "times(x,_)")
    step3 = prover.add_free_instantiation("times(x,plus(0,0))=plus(times(x,0),times(x,0))", distributivity,
                                          {"x": "x", "y": "0", "z": "0"})
    step4 = prover.add_chained_equality("times(x,0)=plus(times(x,0),times(x,0))", [step2, step3])
    # PROOF OF PLUS(A,C)=A -> C=0
    ins_negation = prover.add_free_instantiation("0=plus(minus(times(x,0)),times(x,0))", flipped_negation,
                                                 {"x": "times(x,0)"})
    flipped_ins_negation = prover.add_flipped_equality("plus(minus(times(x,0)),times(x,0))=0", ins_negation)

    step5 = prover.add_substituted_equality(
        "plus(minus(times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))", step4,
        "plus(minus(times(x,0)),_)")
    step6 = prover.add_free_instantiation(
        "plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=plus(plus(minus(times(x,0)),times(x,0)),times(x,0))",
        flipped_a_associativity, {"x": "minus(times(x,0))", "y": "times(x,0)", "z": "times(x,0)"})
    step7 = prover.add_substituted_equality("plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(0,times(x,0))",
                                            flipped_ins_negation, "plus(_,times(x,0))")
    chained = prover.add_chained_equality("0=plus(0,times(x,0))", [ins_negation, step5, step6, step7])
    step8 = prover.add_free_instantiation("plus(0,times(x,0))=times(x,0)", zero, {"x": "times(x,0)"})
    step9 = prover.add_chained_equality("0=times(x,0)", [chained, step8])
    step10 = prover.add_free_instantiation("times(x,0)=times(0,x)", m_commutativity, {"x": "x", "y": "0"})
    step11 = prover.add_chained_equality("0=times(0,x)", [step9, step10])
    step12 = prover.add_flipped_equality("times(0,x)=0", step11)

    # Task 10.11
    return prover.qed()


#: Axiom schema of induction
INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
#: The seven axioms of Peano arithmetic
PEANO_AXIOMS = frozenset({'(s(x)=s(y)->x=y)', '~s(x)=0', 'plus(x,0)=x',
                          'plus(x,s(y))=s(plus(x,y))', 'times(x,0)=0',
                          'times(x,s(y))=plus(times(x,y),x)', INDUCTION_AXIOM})


def peano_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # # _________________________AXIOMS_________________________ #
    # same_successor = prover.add_assumption("(s(x)=s(y)->x=y)")
    # zero_first = prover.add_assumption("~s(x)=0")
    # zero_add = prover.add_assumption("plus(x,0)=x")
    # successor_addition = prover.add_assumption("plus(x,s(y))=s(plus(x,y))")
    # zero_mult = prover.add_assumption("times(x,0)=0")
    # successor_multiplication = prover.add_assumption("times(x,s(y))=plus(times(x,y),x)")
    #
    # flipped_zero_add = prover.add_flipped_equality("x=plus(x,0)", zero_add)
    # flipped_successor_addition = prover.add_flipped_equality("s(plus(x,y))=plus(x,s(y))", successor_addition)
    # flipped_zero_mult = prover.add_flipped_equality("0=times(x,0)", zero_mult)
    # flipped_multiplication = prover.add_flipped_equality("plus(times(x,y),x)=times(x,s(y))", successor_multiplication)

    # ________________________PROOF START_______________________ #
    axiom_1 = prover.add_assumption("(s(x)=s(y)->x=y)")
    axiom_2 = prover.add_assumption("~s(x)=0")
    axiom_3 = prover.add_assumption("plus(x,0)=x")
    axiom_4 = prover.add_assumption("plus(x,s(y))=s(plus(x,y))")
    axiom_5 = prover.add_assumption("times(x,0)=0")
    axiom_6 = prover.add_assumption("times(x,s(y))=plus(times(x,y),x)")

    # axiom_7 = prover.add_assumption("((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])")

    sub_map = {"x": "0"}
    instance = "plus(0,0)=0"
    base_induction = prover.add_free_instantiation(instance, axiom_3, sub_map)

    sub_map = {"x": "0",
               "y": "x"}
    instance = "plus(0,s(x))=s(plus(0,x))"
    s_0_plus = prover.add_free_instantiation(instance, axiom_4, sub_map)

    sub_map = {"R": Formula.parse("plus(0,s(x))=s(_)"),
               "c": Term.parse("plus(0,x)"),
               "d": Term.parse("x")}

    # (plus(0,x)=x->plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))
    me_instantiation = prover.ME.instantiate(sub_map)
    apply_ME = prover.add_instantiated_assumption(me_instantiation, prover.ME,
                                                  sub_map)

    # plus(0,s(x))=s(plus(0,x)) is true, a->b->c
    taut = prover.add_tautological_implication(
        "(plus(0,x)=x->plus(0,s(x))=s(x))", {s_0_plus, apply_ME})

    quantified = Formula.parse("Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]")
    ug_line = prover.add_ug(quantified, taut)

    # induction :  "((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])"
    sub_map = {"R": "plus(0,_)=_"}
    instance = \
        "((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])"
    using_induction = prover.add_instantiated_assumption(instance,
                                                         INDUCTION_AXIOM,
                                                         sub_map)
    final_line = "Ax[plus(0,x)=x]"
    taut_of_ands = prover.add_tautological_implication(final_line,
                                                       {base_induction,
                                                        ug_line,
                                                        using_induction})

    ui_line = "plus(0,x)=x"
    conclusion_line = prover.add_universal_instantiation(ui_line, taut_of_ands, "x")
    # Task 10.12
    return prover.qed()


#: Axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})


def russell_paradox_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)

    ui_map = {"R": Formula.parse("((In(_,y)->~In(_,_))&(~In(_,_)->In(_,y)))"), 'x': "x", "c": Term.parse("y")}
    ui_inst = prover.UI.instantiate(ui_map)
    step1 = prover.add_instantiated_assumption(ui_inst, prover.UI, ui_map)

    false = "(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))"  # we have false -> false, and its always true
    step2 = prover.add_tautology(false)

    step3 = prover.add_instantiated_assumption("Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]", COMPREHENSION_AXIOM,
                                               {"R": "~In(_,_)"})

    paradox = "(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->(z=z&~z=z))"
    step4 = prover.add_tautological_implication(paradox, {step1, step2})

    step6 = prover.add_existential_derivation("(z=z&~z=z)", step3, step4)

    # Task 10.13
    return prover.qed()


def _not_exists_not_implies_all_proof(formula: Formula, variable: str,
                                      print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.1


def _exists_not_implies_not_all_proof(formula: Formula, variable: str,
                                      print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.2


def not_all_iff_exists_not_proof(formula: Formula, variable: str,
                                 print_as_proof_forms: bool = False) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.3
