(*  Title:      Subst/Unify
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Unification algorithm
*)

Unify = Unifier + Recdef + Option +

consts

   unifyRel :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"
   unify    :: "'a uterm * 'a uterm => ('a * 'a uterm) list option"

defs

  (*Termination relation for the Unify function:
    --either the set of variables decreases
    --or the first argument does (in fact, both do)
  *)
  unifyRel_def  "unifyRel == inv_image  (finite_psubset ** measure uterm_size)
                               (%(M,N). (vars_of M Un vars_of N, M))"

recdef unify "unifyRel"
  "unify(Const m, Const n)  = (if (m=n) then Some[] else None)"
  "unify(Const m, Comb M N) = None"
  "unify(Const m, Var v)    = Some[(v,Const m)]"
  "unify(Var v, M)          = (if (Var v <: M) then None else Some[(v,M)])"
  "unify(Comb M N, Const x) = None"
  "unify(Comb M N, Var v)   = (if (Var v <: Comb M N) then None   
                               else Some[(v,Comb M N)])"
  "unify(Comb M1 N1, Comb M2 N2) =   
      (case unify(M1,M2)  
        of None       => None  
         | Some theta => (case unify(N1 <| theta, N2 <| theta)  
                            of None       => None  
                             | Some sigma => Some (theta <> sigma)))"
end
