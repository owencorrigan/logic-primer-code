class STATEMENT:
    def IMPLIES(self, q, reason = None, prev_step = None):
        return IMPLIES(self, q, reason, prev_step)
    
    def proof(self):
        steps = ["Q.E.D"]
        while self is not None:
            steps.append(str(self) + " " + self.reason)
            self = self.prev_step
        
        return "\n".join(steps[::-1])

known = {}

class IMPLIES(STATEMENT):
    def __init__(self, p, q, reason, prev_step = None):
        self.p = p
        self.q = q
        self.prev_step = prev_step
        self.reason = reason
        
    def sub(self, t, known = known):
        s2 = (self.p.sub(t)).IMPLIES(self.q.sub(t), "SUB: "+ str(t), self)
        if (str(self) in known) and (str(s2) not in known):
            known[str(s2)] = s2
        return s2
    
    def modus_ponens(self, known = known):
        if(str(self.p) in known):
            if(str(self.q) not in known):
                self.q.prev_step = self
                self.q.reason = "Modus Ponens"
                known[str(self.q)] = self.q
            return self.q
        else:
            raise Exception(str(self.p) + ": proposition is not proved")
    
    def __str__(self):
        return "(" + str(self.p) + " → " + str(self.q) + ")"
    
    __repr__ = __str__ 
    
    def __eq__(self, other):
        return (type(self) == type(other) and
                self.p == other.p and self.q == other.q)

class NOT(STATEMENT):
    def __init__(self, p, reason = None, prev_step = None):
        self.p = p
        self.prev_step = prev_step
        self.reason = reason
        
    def sub(self, t, known = known):
        s2 = NOT(self.p.sub(t), "SUB: "+ str(t), self)
        if (str(self) in known) and (str(s2) not in known):
            known[str(s2)] = s2
        return s2
            
    def __str__(self):
        return "¬" + str(self.p)
    
    __repr__ = __str__ 
    
    def __eq__(self, other):
        return (type(self) == type(other) and
                self.p == other.p)
       
class VAR(STATEMENT):
    def __init__(self, val, prev_step = None):
        self.val = val
        self.prev_step = prev_step
        
    def sub(self, t):
        return t[self]
        
    def __str__(self):
        return self.val
        
    __repr__ = __str__
    
P, Q, R, S, T, U = VAR("P"), VAR("Q"), VAR("R"), VAR("S"), VAR("T"), VAR("U")

axiom1 = P.IMPLIES(Q.IMPLIES(P), "axiom 1")
axiom2 = (P.IMPLIES(Q.IMPLIES(R))).IMPLIES(
          P.IMPLIES(Q).IMPLIES(P.IMPLIES(R)), "axiom 2")
axiom3 = (NOT(P).IMPLIES(NOT(Q))).IMPLIES(
          (NOT(P).IMPLIES(Q)).IMPLIES(P), "axiom 3")
  
for i in [axiom1, axiom2, axiom3]:
    known[str(i)] = i


