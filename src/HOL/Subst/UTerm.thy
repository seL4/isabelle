(*  Title:      Subst/UTerm.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Simple term structure for unification.
Binary trees with leaves that are constants or variables.
*)

UTerm = Finite + 

datatype 'a uterm = Var ('a) 
                  | Const ('a)
                  | Comb ('a uterm) ('a uterm)

consts
  vars_of  ::  'a uterm => 'a set
  "<:"     ::  'a uterm => 'a uterm => bool   (infixl 54) 
uterm_size ::  'a uterm => nat


primrec vars_of   uterm
vars_of_Var   "vars_of (Var v) = {v}"
vars_of_Const "vars_of (Const c) = {}"
vars_of_Comb  "vars_of (Comb M N) = (vars_of(M) Un vars_of(N))"


primrec "op <:"   uterm
occs_Var   "u <: (Var v) = False"
occs_Const "u <: (Const c) = False"
occs_Comb  "u <: (Comb M N) = (u=M | u=N | u <: M | u <: N)"

primrec uterm_size  uterm
uterm_size_Var   "uterm_size (Var v) = 0"
uterm_size_Const "uterm_size (Const c) = 0"
uterm_size_Comb  "uterm_size (Comb M N) = Suc(uterm_size M + uterm_size N)"

end
