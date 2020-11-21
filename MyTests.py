from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.deduction import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction_test import *

# r1 = InferenceRule([], Formula.parse('((x|y)->((~x|x)->(y|x)))'))
# r3 =
# proof = Proof(
#     InferenceRule([Formula.parse('(x|y)')], Formula.parse('(y|x)')),
#     {R1, R2},
#     [Proof.Line(Formula.parse('(x|y)')),
#      Proof.Line(Formula.parse('(~x|x)'), R2, []),
#      Proof.Line(Formula.parse('(y|x)'), R1, [0, 1])])
#
# print(remove_assumption(proof))
