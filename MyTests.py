from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.deduction import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction_test import *
from propositions.tautology import *

from predicates.syntax import *

Term._parse_prefix("plus(s(x),3)")
print(Term._parse_prefix("plus(s(x),3)"))
# string = "plus(s(x),3)"
# split = string.index('(')
# root, args = string[:split], string[split:]
# print(root,args)
# args = args.strip("()").split(',')
# print(args)
#
