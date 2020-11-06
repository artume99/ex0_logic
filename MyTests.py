from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *

# print_truth_table(Formula.parse('~(p&q76)'))
# print(Formula.parse('~((x-&x)-|(y-&y))'))
# sub_F = dict({'F': Formula.parse('((p-&(p-&p))-&(p-&(p-&p)))')})
# # sub_not = dict({'~': Formula.parse('(p-&p)')})
# # sub_F.update(sub_not)
# # sub_and = dict({'&': Formula.parse('((p-&p)-&(p-&p))')})
# # sub_F.update(sub_and)
# # sub_or = dict({'|': Formula.parse('((p-&p)-&(q-&q))')})
# # sub_F.update(sub_or)
# # sub_T = dict({'T': Formula.parse('((p-&p)-&p)')})
# # sub_F.update(sub_T)
# # sub_iff = dict({'<->': Formula.parse('~(~(p&q)&~(~p&~q))')})
# # sub_F.update(sub_iff)
# # sub_and.update(sub_not)
# # sub_xor = dict({'+': (Formula.parse('~(~(p&~q)&~(~p&q))')).substitute_operators(sub_and)})
# # sub_F.update(sub_xor)
# # sub_if = dict({'->': Formula.parse('~(~~p&~q)')})
# # sub_F.update(sub_if)
# # sub_nand = dict({'-&': Formula.parse('~(p&q)')})
# # sub_F.update(sub_nand)
# # sub_nor = dict({'-|': Formula.parse('~~(~p&~q)')})
# # sub_F.update(sub_nor)
# # print(sub_F)
sub_nand = dict({'-&': Formula.parse('((p->~(p->p))->q)')})
sub_and = dict(
        {'&': Formula.parse('((((p->~(p->p))->q)->~(((p->~(p->p))->q)->((p->~(p->p))->q)))->((p->~(p->p))->q))')})

print(Formula.parse('((p-&q)-&(p-&q))').substitute_operators(sub_nand))
print(Formula.parse('~(~(p&~q)&~(~p&q))').substitute_operators(sub_and))


# print(Formula.parse('(p-&q)').substitute_operators({'-&': Formula.parse('(p->F)')}))
