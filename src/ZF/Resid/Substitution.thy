(*  Title: 	Substitution.thy
    ID:         $Id$
    Author: 	Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Substitution = SubUnion +

consts
  lift_rec	:: [i,i]=> i
  lift		:: i=>i
  subst_rec	:: [i,i,i]=> i
  "'/"          :: [i,i]=>i  (infixl 70)  (*subst*)
translations
  "lift(r)"  == "lift_rec(r,0)"
  "u/v" == "subst_rec(u,v,0)"
  
defs
  lift_rec_def	"lift_rec(r,kg) ==   
		     redex_rec(r,%i.(lam k:nat.if(i<k,Var(i),Var(succ(i)))), 
		                 %x m.(lam k:nat.Fun(m`(succ(k)))),   
		                 %b x y m p.lam k:nat.App(b,m`k,p`k))`kg"

  
(* subst_rec(u,Var(i),k)     = if k<i then Var(i-1)
                               else if k=i then u
                                    else Var(i)
   subst_rec(u,Fun(t),k)     = Fun(subst_rec(lift(u),t,succ(k)))
   subst_rec(u,App(b,f,a),k) = App(b,subst_rec(u,f,p),subst_rec(u,a,p))

*)
  subst_rec_def	"subst_rec(u,t,kg) ==   
		     redex_rec(t,   
		       %i.(lam r:redexes.lam k:nat.   
		              if(k<i,Var(i#-1),   
		                if(k=i,r,Var(i)))),   
		       %x m.(lam r:redexes.lam k:nat.   
                             Fun(m`(lift(r))`(succ(k)))),   
		       %b x y m p.lam r:redexes.lam k:nat.   
		              App(b,m`r`k,p`r`k))`u`kg"


end


