(*  Title:      Substitution.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Substitution = Redex +

consts
  lift_aux  :: i=> i
  lift          :: i=> i
  subst_aux :: i=> i
  "'/"          :: [i,i]=>i  (infixl 70)  (*subst*)

constdefs
  lift_rec      :: [i,i]=> i
    "lift_rec(r,k) == lift_aux(r)`k"

  subst_rec     :: [i,i,i]=> i
    "subst_rec(u,r,k) == subst_aux(r)`u`k"

translations
  "lift(r)"  == "lift_rec(r,0)"
  "u/v"      == "subst_rec(u,v,0)"
  

(** The clumsy _aux functions are required because other arguments vary
    in the recursive calls ***)

primrec
  "lift_aux(Var(i)) = (lam k:nat. if(i<k, Var(i), Var(succ(i))))"

  "lift_aux(Fun(t)) = (lam k:nat. Fun(lift_aux(t) ` succ(k)))"

  "lift_aux(App(b,f,a)) = (lam k:nat. App(b, lift_aux(f)`k, lift_aux(a)`k))"


  
primrec
(* subst_aux(u,Var(i),k)     = if k<i then Var(i-1)
                               else if k=i then u
                                    else Var(i)
   subst_aux(u,Fun(t),k)     = Fun(subst_aux(lift(u),t,succ(k)))
   subst_aux(u,App(b,f,a),k) = App(b,subst_aux(u,f,p),subst_aux(u,a,p))

*)

  "subst_aux(Var(i)) =
     (lam r:redexes. lam k:nat. if(k<i, Var(i #- 1),   
				   if(k=i, r, Var(i))))"
  "subst_aux(Fun(t)) =
     (lam r:redexes. lam k:nat. Fun(subst_rec(lift(r), t, succ(k))))"

  "subst_aux(App(b,f,a)) = 
     (lam r:redexes. lam k:nat. App(b, subst_rec(r,f,k), subst_rec(r,a,k)))"

end


