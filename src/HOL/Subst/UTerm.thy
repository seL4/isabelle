(*  Title: 	Substitutions/UTerm.thy
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Simple term structure for unifiation.
Binary trees with leaves that are constants or variables.
*)

UTerm = Sexp +

types uterm 1

arities 
  uterm     :: (term)term

consts
  uterm     :: 'a item set => 'a item set
  Rep_uterm :: 'a uterm => 'a item
  Abs_uterm :: 'a item => 'a uterm
  VAR       :: 'a item => 'a item
  CONST     :: 'a item => 'a item
  COMB      :: ['a item, 'a item] => 'a item
  Var       :: 'a => 'a uterm
  Const     :: 'a => 'a uterm
  Comb      :: ['a uterm, 'a uterm] => 'a uterm
  UTerm_rec :: "['a item, 'a item => 'b, 'a item => 'b, 
                ['a item , 'a item, 'b, 'b]=>'b] => 'b"
  uterm_rec :: "['a uterm, 'a => 'b, 'a => 'b, 
                ['a uterm, 'a uterm,'b,'b]=>'b] => 'b"

defs
     (*defining the concrete constructors*)
  VAR_def  	"VAR(v) == In0(v)"
  CONST_def  	"CONST(v) == In1(In0(v))"
  COMB_def 	"COMB t u == In1(In1(t $ u))"

inductive "uterm(A)"
  intrs
    VAR_I	   "v:A ==> VAR(v) : uterm(A)"
    CONST_I  "c:A ==> CONST(c) : uterm(A)"
    COMB_I   "[| M:uterm(A);  N:uterm(A) |] ==> COMB M N : uterm(A)"

rules
    (*faking a type definition...*)
  Rep_uterm 		"Rep_uterm(xs): uterm(range(Leaf))"
  Rep_uterm_inverse 	"Abs_uterm(Rep_uterm(xs)) = xs"
  Abs_uterm_inverse 	"M: uterm(range(Leaf)) ==> Rep_uterm(Abs_uterm(M)) = M"

defs
     (*defining the abstract constructors*)
  Var_def  	"Var(v) == Abs_uterm(VAR(Leaf(v)))"
  Const_def  	"Const(c) == Abs_uterm(CONST(Leaf(c)))"
  Comb_def 	"Comb t u == Abs_uterm (COMB (Rep_uterm t) (Rep_uterm u))"

     (*uterm recursion*)
  UTerm_rec_def	
   "UTerm_rec M b c d == wfrec (trancl pred_sexp) M 
          (Case (%x g.b(x)) (Case (%y g. c(y)) (Split (%x y g. d x y (g x) (g y)))))"

  uterm_rec_def
   "uterm_rec t b c d == 
   UTerm_rec (Rep_uterm t) (%x.b(Inv Leaf x)) (%x.c(Inv Leaf x)) 
                           (%x y q r.d (Abs_uterm x) (Abs_uterm y) q r)"

end
