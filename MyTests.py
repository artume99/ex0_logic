from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.deduction import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction_test import *
from propositions.tautology import *

proof = prove_in_model(Formula.parse('(p->q7)'),{'q7': False, 'p': True})
print(proof)
proof = prove_in_model(Formula.parse('(p->q7)'), {'q7': False, 'p': False})
print(proof)

