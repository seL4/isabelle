(*  Title:      CCL/Lazy/fix.thy
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1993  University of Cambridge

Tentative attempt at including fixed point induction.
Justified by Smith.
*)

Fix = Type + 

consts

  idgen      ::       "[i]=>i"
  INCL      :: "[i=>o]=>o"

rules

  idgen_def
  "idgen(f) == lam t. case(t,true,false,%x y.<f`x, f`y>,%u. lam x. f ` u(x))"

  INCL_def   "INCL(%x. P(x)) == (ALL f.(ALL n:Nat. P(f^n`bot)) --> P(fix(f)))"
  po_INCL    "INCL(%x. a(x) [= b(x))"
  INCL_subst "INCL(P) ==> INCL(%x. P((g::i=>i)(x)))"

end
