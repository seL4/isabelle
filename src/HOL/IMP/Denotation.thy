(*  Title:      HOL/IMP/Denotation.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Denotational semantics of commands
*)

Denotation = Natural + 

types com_den = "(state*state)set"

constdefs
  Gamma :: [bexp,com_den] => (com_den => com_den)
           "Gamma b cd == (%phi.{(s,t). (s,t) : (phi O cd) & b(s)} Un 
                                 {(s,t). s=t & ~b(s)})"
    
consts
  C     :: com => com_den

primrec
  C_skip    "C(SKIP) = Id"
  C_assign  "C(x :== a) = {(s,t). t = s[x::=a(s)]}"
  C_comp    "C(c0 ; c1) = C(c1) O C(c0)"
  C_if      "C(IF b THEN c1 ELSE c2) = {(s,t). (s,t) : C(c1) & b(s)} Un
                                       {(s,t). (s,t) : C(c2) & ~ b(s)}"
  C_while   "C(WHILE b DO c) = lfp (Gamma b (C c))"

end
