(*  Title:      ZF/Coind/Static.thy
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory Static imports Values Types begin

(*** Basic correspondence relation -- not completely specified, as it is a
     parameter of the proof.  A concrete version could be defined inductively.
***)

axiomatization isof :: "[i,i] => o"
  where isof_app: "[|isof(c1,t_fun(t1,t2)); isof(c2,t1)|] ==> isof(c_app(c1,c2),t2)"

(*Its extension to environments*)

definition
  isofenv :: "[i,i] => o"  where
   "isofenv(ve,te) ==                
      ve_dom(ve) = te_dom(te) &            
      (\<forall>x \<in> ve_dom(ve).                          
        \<exists>c \<in> Const. ve_app(ve,x) = v_const(c) & isof(c,te_app(te,x)))"
  

(*** Elaboration ***)

consts  ElabRel :: i

inductive
  domains "ElabRel" \<subseteq> "TyEnv * Exp * Ty"
  intros
    constI [intro!]:
      "[| te \<in> TyEnv; c \<in> Const; t \<in> Ty; isof(c,t) |] ==>   
       <te,e_const(c),t> \<in> ElabRel"
    varI [intro!]:
      "[| te \<in> TyEnv; x \<in> ExVar; x \<in> te_dom(te) |] ==>   
       <te,e_var(x),te_app(te,x)> \<in> ElabRel"
    fnI [intro!]:
      "[| te \<in> TyEnv; x \<in> ExVar; e \<in> Exp; t1 \<in> Ty; t2 \<in> Ty;   
          <te_owr(te,x,t1),e,t2> \<in> ElabRel |] ==>   
       <te,e_fn(x,e),t_fun(t1,t2)> \<in> ElabRel"
    fixI [intro!]:
      "[| te \<in> TyEnv; f \<in> ExVar; x \<in> ExVar; t1 \<in> Ty; t2 \<in> Ty;   
          <te_owr(te_owr(te,f,t_fun(t1,t2)),x,t1),e,t2> \<in> ElabRel |] ==>   
       <te,e_fix(f,x,e),t_fun(t1,t2)> \<in> ElabRel"
    appI [intro]:
      "[| te \<in> TyEnv; e1 \<in> Exp; e2 \<in> Exp; t1 \<in> Ty; t2 \<in> Ty;   
          <te,e1,t_fun(t1,t2)> \<in> ElabRel;   
          <te,e2,t1> \<in> ElabRel |] ==> <te,e_app(e1,e2),t2> \<in> ElabRel"
  type_intros te_appI Exp.intros Ty.intros


inductive_cases
    elab_constE [elim!]: "<te,e_const(c),t> \<in> ElabRel"
  and elab_varE [elim!]: "<te,e_var(x),t> \<in> ElabRel"
  and elab_fnE [elim]:   "<te,e_fn(x,e),t> \<in> ElabRel"
  and elab_fixE [elim!]: "<te,e_fix(f,x,e),t> \<in> ElabRel"
  and elab_appE [elim]:  "<te,e_app(e1,e2),t> \<in> ElabRel"

declare ElabRel.dom_subset [THEN subsetD, dest]

end







