(*  Title: 	ZF/IMP/Denotation.thy
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Denotational semantics of expressions & commands
*)

Denotation = Com + 

consts
  A     :: "i => i => i"
  B     :: "i => i => i"
  C     :: "i => i"
  Gamma :: "[i,i,i] => i"

rules	(*NOT definitional*)
  A_nat_def	"A(N(n)) == (%sigma. n)"
  A_loc_def	"A(X(x)) == (%sigma. sigma`x)" 
  A_op1_def	"A(Op1(f,a)) == (%sigma. f`A(a,sigma))"
  A_op2_def	"A(Op2(f,a0,a1)) == (%sigma. f`<A(a0,sigma),A(a1,sigma)>)"


  B_true_def	"B(true) == (%sigma. 1)"
  B_false_def	"B(false) == (%sigma. 0)"
  B_op_def	"B(ROp(f,a0,a1)) == (%sigma. f`<A(a0,sigma),A(a1,sigma)>)" 


  B_not_def	"B(noti(b)) == (%sigma. not(B(b,sigma)))"
  B_and_def	"B(b0 andi b1) == (%sigma. B(b0,sigma) and B(b1,sigma))"
  B_or_def	"B(b0 ori b1) == (%sigma. B(b0,sigma) or B(b1,sigma))"

  C_skip_def	"C(skip) == id(loc->nat)"
  C_assign_def	"C(x := a) == {io:(loc->nat)*(loc->nat). 
			       snd(io) = fst(io)[A(a,fst(io))/x]}"

  C_comp_def	"C(c0 ; c1) == C(c1) O C(c0)"
  C_if_def	"C(ifc b then c0 else c1) == {io:C(c0). B(b,fst(io))=1} Un 
			 	             {io:C(c1). B(b,fst(io))=0}"

  Gamma_def	"Gamma(b,c) == (%phi.{io : (phi O C(c)). B(b,fst(io))=1} Un 
			 	     {io : id(loc->nat). B(b,fst(io))=0})"

  C_while_def	"C(while b do c) == lfp((loc->nat)*(loc->nat), Gamma(b,c))"

end
