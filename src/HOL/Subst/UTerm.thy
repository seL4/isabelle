(*  ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header{*Simple Term Structure for Unification*}

theory UTerm
imports Main

begin

text{*Binary trees with leaves that are constants or variables.*}

datatype 'a uterm = Var 'a
                  | Const 'a
                  | Comb "'a uterm" "'a uterm"

consts
  vars_of  ::  "'a uterm => 'a set"
  "<:"     ::  "'a uterm => 'a uterm => bool"   (infixl 54) 
uterm_size ::  "'a uterm => nat"


primrec
  vars_of_Var:   "vars_of (Var v) = {v}"
  vars_of_Const: "vars_of (Const c) = {}"
  vars_of_Comb:  "vars_of (Comb M N) = (vars_of(M) Un vars_of(N))"


primrec
  occs_Var:   "u <: (Var v) = False"
  occs_Const: "u <: (Const c) = False"
  occs_Comb:  "u <: (Comb M N) = (u=M | u=N | u <: M | u <: N)"

primrec
  uterm_size_Var:   "uterm_size (Var v) = 0"
  uterm_size_Const: "uterm_size (Const c) = 0"
  uterm_size_Comb:  "uterm_size (Comb M N) = Suc(uterm_size M + uterm_size N)"


lemma vars_var_iff: "(v : vars_of(Var(w))) = (w=v)"
by auto

lemma vars_iff_occseq: "(x : vars_of(t)) = (Var(x) <: t | Var(x) = t)"
by (induct_tac "t", auto)


(* Not used, but perhaps useful in other proofs *)
lemma occs_vars_subset: "M<:N --> vars_of(M) <= vars_of(N)"
by (induct_tac "N", auto)


lemma monotone_vars_of: "vars_of M Un vars_of N <= (vars_of M Un A) Un (vars_of N Un B)"
by blast

lemma finite_vars_of: "finite(vars_of M)"
by (induct_tac "M", auto)


end
