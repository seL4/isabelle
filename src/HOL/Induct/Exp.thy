(*  Title:      HOL/Induct/Exp
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Example of Mutual Induction via Iteratived Inductive Definitions: Expressions
*)

Exp = Com +

(** Evaluation of arithmetic expressions **)
consts  eval    :: "((exp*state) * (nat*state)) set"
       "-|->"   :: "[exp*state,nat*state] => bool"         (infixl 50)
translations
    "esig -|-> (n,s)" <= "(esig,n,s) : eval"
    "esig -|-> ns"    == "(esig,ns) : eval"
  
inductive eval
  intrs 
    N      "(N(n),s) -|-> (n,s)"

    X      "(X(x),s) -|-> (s(x),s)"

    Op     "[| (e0,s) -|-> (n0,s0);  (e1,s0)  -|-> (n1,s1) |] 
            ==> (Op f e0 e1, s) -|-> (f n0 n1, s1)"

    valOf  "[| (c,s) -[eval]-> s0;  (e,s0)  -|-> (n,s1) |] 
            ==> (VALOF c RESULTIS e, s) -|-> (n, s1)"

  monos "[exec_mono]"

end

