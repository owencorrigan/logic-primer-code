from logic import *

a1 = axiom1.sub({P: P, Q: P.IMPLIES(P)})
a2 = axiom2.sub({P: P, Q: P.IMPLIES(P), R: P})
a3 = a2.modus_ponens()
a4 = axiom1.sub({P: P, Q: P})
l1 = a3.modus_ponens()

print(l1.proof())

b1 = l1.sub({P: NOT(P)})
b2 = axiom3.sub({P: P, Q: P})
l2 = b2.modus_ponens()

print(l2.proof())

c1 = axiom2.assume(P.IMPLIES(Q.IMPLIES(R)))
c2 = c1.assume(P.IMPLIES(Q))
c3 = c2.modus_ponens()
l3 = c3.modus_ponens()

print(l3.proof())

l4 = l3.sub({P: P, Q: Q.IMPLIES(P), R: R})

print(l4.proof())

e1 = axiom1.assume(P)
l5 = e1.modus_ponens()

print(l5.proof())
