(*  Title:      ZF/Resid/Substitution.thy
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

  subst_rec     :: [i,i,i]=> i	(**NOTE THE ARGUMENT ORDER BELOW**)
    "subst_rec(u,r,k) == subst_aux(r)`u`k"

translations
  "lift(r)"  == "lift_rec(r,0)"
  "u/v"      == "subst_rec(u,v,0)"
  

(** The clumsy _aux functions are required because other arguments vary
    in the recursive calls ***)

primrec
  "lift_aux(Var(i)) = (\\<lambda>k \\<in> nat. if i<k then Var(i) else Var(succ(i)))"

  "lift_aux(Fun(t)) = (\\<lambda>k \\<in> nat. Fun(lift_aux(t) ` succ(k)))"

  "lift_aux(App(b,f,a)) = (\\<lambda>k \\<in> nat. App(b, lift_aux(f)`k, lift_aux(a)`k))"


  
primrec
  "subst_aux(Var(i)) =
     (\\<lambda>r \\<in> redexes. \\<lambda>k \\<in> nat. if k<i then Var(i #- 1) 
				else if k=i then r else Var(i))"
  "subst_aux(Fun(t)) =
     (\\<lambda>r \\<in> redexes. \\<lambda>k \\<in> nat. Fun(subst_aux(t) ` lift(r) ` succ(k)))"

  "subst_aux(App(b,f,a)) = 
     (\\<lambda>r \\<in> redexes. \\<lambda>k \\<in> nat. App(b, subst_aux(f)`r`k, subst_aux(a)`r`k))"

end


