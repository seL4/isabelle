(*  Title:      Residuals.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF

*)

theory Residuals = Substitution:

consts
  Sres          :: "i"
  residuals     :: "[i,i,i]=>i"
  "|>"          :: "[i,i]=>i"     (infixl 70)

translations
  "residuals(u,v,w)"  == "<u,v,w> \<in> Sres"

inductive
  domains       "Sres" <= "redexes*redexes*redexes"
  intros
    Res_Var:    "n \<in> nat ==> residuals(Var(n),Var(n),Var(n))"
    Res_Fun:    "[|residuals(u,v,w)|]==>   
                     residuals(Fun(u),Fun(v),Fun(w))"
    Res_App:    "[|residuals(u1,v1,w1);   
                   residuals(u2,v2,w2); b \<in> bool|]==>   
                 residuals(App(b,u1,u2),App(0,v1,v2),App(b,w1,w2))"
    Res_redex:  "[|residuals(u1,v1,w1);   
                   residuals(u2,v2,w2); b \<in> bool|]==>   
                 residuals(App(b,Fun(u1),u2),App(1,Fun(v1),v2),w2/w1)"
  type_intros    subst_type nat_typechecks redexes.intros bool_typechecks

defs
  res_func_def:  "u |> v == THE w. residuals(u,v,w)"


(* ------------------------------------------------------------------------- *)
(*       Setting up rule lists                                               *)
(* ------------------------------------------------------------------------- *)

declare Sres.intros [intro]
declare Sreg.intros [intro]
declare subst_type [intro]

inductive_cases [elim!]:
  "residuals(Var(n),Var(n),v)"
  "residuals(Fun(t),Fun(u),v)"
  "residuals(App(b, u1, u2), App(0, v1, v2),v)"
  "residuals(App(b, u1, u2), App(1, Fun(v1), v2),v)"
  "residuals(Var(n),u,v)"
  "residuals(Fun(t),u,v)"
  "residuals(App(b, u1, u2), w,v)"
  "residuals(u,Var(n),v)"
  "residuals(u,Fun(t),v)"
  "residuals(w,App(b, u1, u2),v)"


inductive_cases [elim!]:
  "Var(n) <== u"
  "Fun(n) <== u"
  "u <== Fun(n)"
  "App(1,Fun(t),a) <== u"
  "App(0,t,a) <== u"

inductive_cases [elim!]:
  "Fun(t) \<in> redexes"

declare Sres.intros [simp]


(* ------------------------------------------------------------------------- *)
(*       residuals is a  partial function                                    *)
(* ------------------------------------------------------------------------- *)

lemma residuals_function [rule_format]:
     "residuals(u,v,w) ==> \<forall>w1. residuals(u,v,w1) --> w1 = w"
by (erule Sres.induct, force+)

lemma residuals_intro [rule_format]:
     "u~v ==> regular(v) --> (\<exists>w. residuals(u,v,w))"
by (erule Scomp.induct, force+)

lemma comp_resfuncD:
     "[| u~v;  regular(v) |] ==> residuals(u, v, THE w. residuals(u, v, w))"
apply (frule residuals_intro, assumption, clarify)
apply (subst the_equality)
apply (blast intro: residuals_function)+
done


(* ------------------------------------------------------------------------- *)
(*               Residual function                                           *)
(* ------------------------------------------------------------------------- *)

lemma res_Var [simp]: "n \<in> nat ==> Var(n) |> Var(n) = Var(n)"
by (unfold res_func_def, blast)

lemma res_Fun [simp]: 
    "[|s~t; regular(t)|]==> Fun(s) |> Fun(t) = Fun(s |> t)"
apply (unfold res_func_def)
apply (blast intro: comp_resfuncD residuals_function) 
done

lemma res_App [simp]: 
    "[|s~u; regular(u); t~v; regular(v); b \<in> bool|]
     ==> App(b,s,t) |> App(0,u,v) = App(b, s |> u, t |> v)"
apply (unfold res_func_def) 
apply (blast dest!: comp_resfuncD intro: residuals_function)
done

lemma res_redex [simp]: 
    "[|s~u; regular(u); t~v; regular(v); b \<in> bool|]
     ==> App(b,Fun(s),t) |> App(1,Fun(u),v) = (t |> v)/ (s |> u)"
apply (unfold res_func_def)
apply (blast elim!: redexes.free_elims dest!: comp_resfuncD 
             intro: residuals_function)
done

lemma resfunc_type [simp]:
     "[|s~t; regular(t)|]==> regular(t) --> s |> t \<in> redexes"
apply (erule Scomp.induct, auto)
apply (drule_tac psi = "Fun (?u) |> ?v \<in> redexes" in asm_rl)
apply auto
done

(* ------------------------------------------------------------------------- *)
(*     Commutation theorem                                                   *)
(* ------------------------------------------------------------------------- *)

lemma sub_comp [simp]: "u<==v ==> u~v"
by (erule Ssub.induct, simp_all)

lemma sub_preserve_reg [rule_format, simp]:
     "u<==v  ==> regular(v) --> regular(u)"
by (erule Ssub.induct, auto)

lemma residuals_lift_rec: "[|u~v; k \<in> nat|]==> regular(v)--> (\<forall>n \<in> nat.   
         lift_rec(u,n) |> lift_rec(v,n) = lift_rec(u |> v,n))"
apply (erule Scomp.induct, safe)
apply (simp_all add: lift_rec_Var subst_Var lift_subst)
apply (rotate_tac -2, simp)
done

lemma residuals_subst_rec:
     "u1~u2 ==>  \<forall>v1 v2. v1~v2 --> regular(v2) --> regular(u2) --> 
                  (\<forall>n \<in> nat. subst_rec(v1,u1,n) |> subst_rec(v2,u2,n) =  
                    subst_rec(v1 |> v2, u1 |> u2,n))"
apply (erule Scomp.induct, safe)
apply (simp_all add: lift_rec_Var subst_Var residuals_lift_rec)
apply (drule_tac psi = "\<forall>x.?P (x) " in asm_rl)
apply (simp add: substitution)
done


lemma commutation [simp]:
     "[|u1~u2; v1~v2; regular(u2); regular(v2)|]
      ==> (v1/u1) |> (v2/u2) = (v1 |> v2)/(u1 |> u2)"
by (simp add: residuals_subst_rec)


(* ------------------------------------------------------------------------- *)
(*     Residuals are comp and regular                                        *)
(* ------------------------------------------------------------------------- *)

lemma residuals_preserve_comp [rule_format, simp]:
     "u~v ==> \<forall>w. u~w --> v~w --> regular(w) --> (u|>w) ~ (v|>w)"
by (erule Scomp.induct, force+)

lemma residuals_preserve_reg [rule_format, simp]:
     "u~v ==> regular(u) --> regular(v) --> regular(u|>v)"
apply (erule Scomp.induct, auto)
apply (drule_tac psi = "regular (Fun (?u) |> ?v)" in asm_rl, force)+
done

(* ------------------------------------------------------------------------- *)
(*     Preservation lemma                                                    *)
(* ------------------------------------------------------------------------- *)

lemma union_preserve_comp: "u~v ==> v ~ (u un v)"
by (erule Scomp.induct, simp_all)

lemma preservation [rule_format]:
     "u ~ v ==> regular(v) --> u|>v = (u un v)|>v"
apply (erule Scomp.induct, safe)
apply (drule_tac [3] psi = "Fun (?u) |> ?v = ?w" in asm_rl)
apply (auto simp add: union_preserve_comp comp_sym_iff)
done


(**** And now the Cube ***)

declare sub_comp [THEN comp_sym, simp]

(* ------------------------------------------------------------------------- *)
(*         Prism theorem                                                     *)
(*         =============                                                     *)
(* ------------------------------------------------------------------------- *)

(* Having more assumptions than needed -- removed below  *)
lemma prism_l [rule_format]:
     "v<==u ==>  
       regular(u) --> (\<forall>w. w~v --> w~u -->   
                            w |> u = (w|>v) |> (u|>v))"
apply (erule Ssub.induct, force+)
done

lemma prism:
     "[|v <== u; regular(u); w~v|] ==> w |> u = (w|>v) |> (u|>v)"
apply (rule prism_l)
apply (rule_tac [4] comp_trans, auto)
done


(* ------------------------------------------------------------------------- *)
(*    Levy's Cube Lemma                                                      *)
(* ------------------------------------------------------------------------- *)

lemma cube: "[|u~v; regular(v); regular(u); w~u|]==>   
           (w|>u) |> (v|>u) = (w|>v) |> (u|>v)"
apply (subst preservation, assumption, assumption)
apply (subst preservation, erule comp_sym, assumption)
apply (subst prism [symmetric])
apply (simp add: union_r comp_sym_iff)
apply (simp add: union_preserve_regular comp_sym_iff)
apply (erule comp_trans, assumption)
apply (simp add: prism [symmetric] union_l union_preserve_regular 
                 comp_sym_iff union_sym)
done


(* ------------------------------------------------------------------------- *)
(*           paving theorem                                                  *)
(* ------------------------------------------------------------------------- *)

lemma paving: "[|w~u; w~v; regular(u); regular(v)|]==>  
           \<exists>uv vu. (w|>u) |> vu = (w|>v) |> uv & (w|>u)~vu & 
             regular(vu) & (w|>v)~uv & regular(uv) "
apply (subgoal_tac "u~v")
apply (safe intro!: exI)
apply (rule cube)
apply (simp_all add: comp_sym_iff)
apply (blast intro: residuals_preserve_comp comp_trans comp_sym)+
done


end

