(*  Title:      FOL/ex/Nat.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Theory of the natural numbers: Peano's axioms, primitive recursion *}

theory Nat
imports FOL
begin

typedecl nat
arities nat :: "term"

consts
  0 :: nat    ("0")
  Suc :: "nat => nat"
  rec :: "[nat, 'a, [nat,'a]=>'a] => 'a"
  add :: "[nat, nat] => nat"    (infixl "+" 60)

axioms
  induct:      "[| P(0);  !!x. P(x) ==> P(Suc(x)) |]  ==> P(n)"
  Suc_inject:  "Suc(m)=Suc(n) ==> m=n"
  Suc_neq_0:   "Suc(m)=0      ==> R"
  rec_0:       "rec(0,a,f) = a"
  rec_Suc:     "rec(Suc(m), a, f) = f(m, rec(m,a,f))"
  add_def:     "m+n == rec(m, n, %x y. Suc(y))"

ML {* use_legacy_bindings (the_context ()) *}

end
