class STATEMENT:
    def IMPLIES(self, q, reason = None, prev_step = None, hypotheses = []):
        return IMPLIES(self, q, reason = reason, prev_step = prev_step,
                       hypotheses = hypotheses)
    
    def proof(self):
        steps = ["Q.E.D"]
        while self is not None:
            steps.append(self.full_str() + " " + self.reason)
            self = self.prev_step
        
        return "\n".join(steps[::-1]) + "\n"
    
    def full_str(self):
        hyp_strings = ", ".join([str(i) for i in self.hypotheses])
        if(hyp_strings != ""):
            hyp_strings += " "
        return hyp_strings + "⊢ " + str(self)
        

known = {}

class IMPLIES(STATEMENT):
    def __init__(self, p, q, reason, prev_step, hypotheses):
        self.p = p
        self.q = q
        self.prev_step = prev_step
        self.reason = reason
        self.hypotheses = hypotheses
        
    def sub(self, t, known = known):
        hyp_sub = [i.sub(t) for i in self.hypotheses if 
                   i.sub(t).full_str() not in known]
        s2 = (self.p.sub(t)).IMPLIES(self.q.sub(t), reason = "SUB: " + str(t), 
              prev_step = self, hypotheses = hyp_sub)
        if (self.full_str() in known) and (s2.full_str() not in known):
            known[s2.full_str()] = s2
        return s2
    
    def modus_ponens(self, known = known):
        str_hyps = [str(i) for i in self.hypotheses]
        if(self.p.full_str() in known or str(self.p) in str_hyps):
            if(self.q.full_str() not in known):
                self.q.prev_step = self
                self.q.reason = "Modus Ponens"
                self.q.hypotheses = self.hypotheses
                known[self.q.full_str()] = self.q
            return self.q
        else:
            raise Exception(self.p.full_str() + ": proposition is not proved")
    
    def assume(self, s):
        return IMPLIES(self.p, self.q, self.reason, self.prev_step, 
                       self.hypotheses[:] + [s])
        
    def __str__(self):
        return "(" + str(self.p) + " → " + str(self.q) + ")"
    
    __repr__ = __str__
    
    def __eq__(self, other):
        return (type(self) == type(other) and
                self.p == other.p and self.q == other.q)


class NOT(STATEMENT):
    def __init__(self, p, reason = None, prev_step = None, hypotheses = []):
        self.p = p
        self.prev_step = prev_step
        self.reason = reason
        self.hypotheses = hypotheses
        
    def sub(self, t, known = known):
        hyp_sub = [i.sub(t) for i in self.hypotheses if 
                   i.sub(t).full_str() not in known]
        s2 = NOT(self.p.sub(t), reason = "SUB: " + str(t), prev_step = self, 
                 hypotheses = hyp_sub)
        if (self.full_str() in known) and (s2.full_str() not in known):
            known[s2.full_str()] = s2
        return s2
            
    def __str__(self):
        return "¬" + str(self.p)
    
    __repr__ = __str__
    
    def __eq__(self, other):
        return (type(self) == type(other) and
                self.p == other.p)
       
       
class VAR(STATEMENT):
    def __init__(self, val, prev_step = None, reason = None, hypotheses = []):
        self.val = val
        self.prev_step = prev_step
        self.reason = reason
        self.hypotheses = hypotheses
        
    def sub(self, t):
        return t[self]
        
    def __str__(self):
        return self.val
        
    __repr__ = __str__
        
    
P, Q, R, S, T, U = VAR("P"), VAR("Q"), VAR("R"), VAR("S"), VAR("T"), VAR("U")

axiom1 = P.IMPLIES(Q.IMPLIES(P), reason = "axiom 1")
axiom2 = (P.IMPLIES(Q.IMPLIES(R))).IMPLIES(
          P.IMPLIES(Q).IMPLIES(P.IMPLIES(R)), reason = "axiom 2")
axiom3 = (NOT(P).IMPLIES(NOT(Q))).IMPLIES(
          (NOT(P).IMPLIES(Q)).IMPLIES(P), reason = "axiom 3")
  
for i in [axiom1, axiom2, axiom3]:
    known[i.full_str()] = i


