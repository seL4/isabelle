(*  Title: 	HOL/IMP/Denotation.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Denotational semantics of expressions & commands
*)

Denotation = Com + 

types com_den = "(state*state)set"
consts
  A     :: "aexp => state => nat"
  B     :: "bexp => state => bool"
  C     :: "com => com_den"
  Gamma :: "[bexp,com_den] => (com_den => com_den)"

primrec A aexp
  A_nat	"A(N(n)) = (%s. n)"
  A_loc	"A(X(x)) = (%s. s(x))" 
  A_op1	"A(Op1 f a) = (%s. f(A a s))"
  A_op2	"A(Op2 f a0 a1) = (%s. f (A a0 s) (A a1 s))"

primrec B bexp
  B_true  "B(true) = (%s. True)"
  B_false "B(false) = (%s. False)"
  B_op	  "B(ROp f a0 a1) = (%s. f (A a0 s) (A a1 s))" 
  B_not	  "B(noti(b)) = (%s. ~(B b s))"
  B_and	  "B(b0 andi b1) = (%s. (B b0 s) & (B b1 s))"
  B_or	  "B(b0 ori b1) = (%s. (B b0 s) | (B b1 s))"

defs
  Gamma_def	"Gamma b cd ==   \
\		   (%phi.{st. st : (phi O cd) & B b (fst st)} Un \
\	                 {st. st : id & ~B b (fst st)})"

primrec C com
  C_skip    "C(skip) = id"
  C_assign  "C(x := a) = {st . snd(st) = fst(st)[A a (fst st)/x]}"
  C_comp    "C(c0 ; c1) = C(c1) O C(c0)"
  C_if	    "C(ifc b then c0 else c1) =   \
\		   {st. st:C(c0) & (B b (fst st))} Un \
\	           {st. st:C(c1) & ~(B b (fst st))}"
  C_while   "C(while b do c) = lfp (Gamma b (C c))"

end
