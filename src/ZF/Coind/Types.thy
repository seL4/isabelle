(*  Title:      ZF/Coind/Types.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory Types = Language:

consts
  Ty :: i               (* Datatype of types *)
  TyConst :: i          (* Abstract type of type constants *)

datatype
  "Ty" = t_const ("tc \<in> TyConst")
       | t_fun ("t1 \<in> Ty","t2 \<in> Ty")
  

(* Definition of type environments and associated operators *)

consts
  TyEnv :: i

datatype
  "TyEnv" = te_emp
          | te_owr ("te \<in> TyEnv","x \<in> ExVar","t \<in> Ty") 

consts
  te_dom :: "i => i"
  te_app :: "[i,i] => i"


primrec (*domain of the type environment*)
  "te_dom (te_emp) = 0"
  "te_dom (te_owr(te,x,v)) = te_dom(te) Un {x}"

primrec (*lookup up identifiers in the type environment*)
  "te_app (te_emp,x) = 0"
  "te_app (te_owr(te,y,t),x) = (if x=y then t else te_app(te,x))"

inductive_cases te_owrE [elim!]: "te_owr(te,f,t) \<in> TyEnv"

(*redundant??*)
lemma te_app_owr1: "te_app(te_owr(te,x,t),x) = t"
by simp

(*redundant??*)
lemma te_app_owr2: "x \<noteq> y ==> te_app(te_owr(te,x,t),y) = te_app(te,y)"
by auto

lemma te_app_owr [simp]:
     "te_app(te_owr(te,x,t),y) = (if x=y then t else te_app(te,y))"
by auto

lemma te_appI:
     "[| te \<in> TyEnv; x \<in> ExVar; x \<in> te_dom(te) |] ==> te_app(te,x) \<in> Ty"
apply (erule_tac P = "x \<in> te_dom (te) " in rev_mp)
apply (erule TyEnv.induct, auto)
done


















end
