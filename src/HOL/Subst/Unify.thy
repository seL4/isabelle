(*  Title:      Subst/Unify
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Unification algorithm
*)

Unify = Unifier + WF_Rel + 

datatype 'a subst = Fail | Subst ('a list)

consts

   unifyRel :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"
   unify    :: "'a uterm * 'a uterm => ('a * 'a uterm) subst"

defs

  (*Termination relation for the Unify function:
    --either the set of variables decreases
    --or the first argument does (in fact, both do)
  *)
  unifyRel_def  "unifyRel == inv_image  (finite_psubset ** measure uterm_size)
                               (%(M,N). (vars_of M Un vars_of N, M))"

recdef unify "unifyRel"
  "unify(Const m, Const n)  = (if (m=n) then Subst[] else Fail)"
  "unify(Const m, Comb M N) = Fail"
  "unify(Const m, Var v)    = Subst[(v,Const m)]"
  "unify(Var v, M)          = (if (Var v <: M) then Fail else Subst[(v,M)])"
  "unify(Comb M N, Const x) = Fail"
  "unify(Comb M N, Var v)   = (if (Var v <: Comb M N) then Fail   
                               else Subst[(v,Comb M N)])"
  "unify(Comb M1 N1, Comb M2 N2) =   
      (case unify(M1,M2)  
        of Fail => Fail  
         | Subst theta => (case unify(N1 <| theta, N2 <| theta)  
                            of Fail => Fail  
                             | Subst sigma => Subst (theta <> sigma)))"
end
