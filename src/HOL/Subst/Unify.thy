(*  Title:      Subst/Unify
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Unification algorithm
*)

Unify = Unifier + WF_Rel + 

datatype 'a subst = Fail | Subst ('a list)

consts

   uterm_less :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"
   unifyRel   :: "(('a uterm * 'a uterm) * ('a uterm * 'a uterm)) set"
   unify      :: "'a uterm * 'a uterm => ('a * 'a uterm) subst"

defs

  uterm_less_def "uterm_less == rprod (measure uterm_size) 
                                      (measure uterm_size)"
  
  (* Termination relation for the Unify function *)
  unifyRel_def  "unifyRel == inv_image  (finite_psubset ** uterm_less)
                               (%(x,y). (vars_of x Un vars_of y, (x,y)))"

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
