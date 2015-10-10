(*  Title:      ZF/Resid/Residuals.thy
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
*)

theory Residuals imports Substitution begin

consts
  Sres          :: "i"

abbreviation
  "residuals(u,v,w) == <u,v,w> \<in> Sres"

inductive
  domains       "Sres" \<subseteq> "redexes*redexes*redexes"
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

definition
  res_func      :: "[i,i]=>i"     (infixl "|>" 70)  where
  "u |> v == THE w. residuals(u,v,w)"


subsection\<open>Setting up rule lists\<close>

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
  "Var(n) \<Longleftarrow> u"
  "Fun(n) \<Longleftarrow> u"
  "u \<Longleftarrow> Fun(n)"
  "App(1,Fun(t),a) \<Longleftarrow> u"
  "App(0,t,a) \<Longleftarrow> u"

inductive_cases [elim!]:
  "Fun(t) \<in> redexes"

declare Sres.intros [simp]

subsection\<open>residuals is a  partial function\<close>

lemma residuals_function [rule_format]:
     "residuals(u,v,w) ==> \<forall>w1. residuals(u,v,w1) \<longrightarrow> w1 = w"
by (erule Sres.induct, force+)

lemma residuals_intro [rule_format]:
     "u \<sim> v ==> regular(v) \<longrightarrow> (\<exists>w. residuals(u,v,w))"
by (erule Scomp.induct, force+)

lemma comp_resfuncD:
     "[| u \<sim> v;  regular(v) |] ==> residuals(u, v, THE w. residuals(u, v, w))"
apply (frule residuals_intro, assumption, clarify)
apply (subst the_equality)
apply (blast intro: residuals_function)+
done

subsection\<open>Residual function\<close>

lemma res_Var [simp]: "n \<in> nat ==> Var(n) |> Var(n) = Var(n)"
by (unfold res_func_def, blast)

lemma res_Fun [simp]: 
    "[|s \<sim> t; regular(t)|]==> Fun(s) |> Fun(t) = Fun(s |> t)"
apply (unfold res_func_def)
apply (blast intro: comp_resfuncD residuals_function) 
done

lemma res_App [simp]: 
    "[|s \<sim> u; regular(u); t \<sim> v; regular(v); b \<in> bool|]
     ==> App(b,s,t) |> App(0,u,v) = App(b, s |> u, t |> v)"
apply (unfold res_func_def) 
apply (blast dest!: comp_resfuncD intro: residuals_function)
done

lemma res_redex [simp]: 
    "[|s \<sim> u; regular(u); t \<sim> v; regular(v); b \<in> bool|]
     ==> App(b,Fun(s),t) |> App(1,Fun(u),v) = (t |> v)/ (s |> u)"
apply (unfold res_func_def)
apply (blast elim!: redexes.free_elims dest!: comp_resfuncD 
             intro: residuals_function)
done

lemma resfunc_type [simp]:
     "[|s \<sim> t; regular(t)|]==> regular(t) \<longrightarrow> s |> t \<in> redexes"
  by (erule Scomp.induct, auto)

subsection\<open>Commutation theorem\<close>

lemma sub_comp [simp]: "u \<Longleftarrow> v \<Longrightarrow> u \<sim> v"
by (erule Ssub.induct, simp_all)

lemma sub_preserve_reg [rule_format, simp]:
     "u \<Longleftarrow> v \<Longrightarrow> regular(v) \<longrightarrow> regular(u)"
by (erule Ssub.induct, auto)

lemma residuals_lift_rec: "[|u \<sim> v; k \<in> nat|]==> regular(v)\<longrightarrow> (\<forall>n \<in> nat.   
         lift_rec(u,n) |> lift_rec(v,n) = lift_rec(u |> v,n))"
apply (erule Scomp.induct, safe)
apply (simp_all add: lift_rec_Var subst_Var lift_subst)
done

lemma residuals_subst_rec:
     "u1 \<sim> u2 ==>  \<forall>v1 v2. v1 \<sim> v2 \<longrightarrow> regular(v2) \<longrightarrow> regular(u2) \<longrightarrow> 
                  (\<forall>n \<in> nat. subst_rec(v1,u1,n) |> subst_rec(v2,u2,n) =  
                    subst_rec(v1 |> v2, u1 |> u2,n))"
apply (erule Scomp.induct, safe)
apply (simp_all add: lift_rec_Var subst_Var residuals_lift_rec)
apply (drule_tac psi = "\<forall>x. P(x)" for P in asm_rl)
apply (simp add: substitution)
done


lemma commutation [simp]:
     "[|u1 \<sim> u2; v1 \<sim> v2; regular(u2); regular(v2)|]
      ==> (v1/u1) |> (v2/u2) = (v1 |> v2)/(u1 |> u2)"
by (simp add: residuals_subst_rec)


subsection\<open>Residuals are comp and regular\<close>

lemma residuals_preserve_comp [rule_format, simp]:
     "u \<sim> v ==> \<forall>w. u \<sim> w \<longrightarrow> v \<sim> w \<longrightarrow> regular(w) \<longrightarrow> (u|>w) \<sim> (v|>w)"
by (erule Scomp.induct, force+)

lemma residuals_preserve_reg [rule_format, simp]:
     "u \<sim> v ==> regular(u) \<longrightarrow> regular(v) \<longrightarrow> regular(u|>v)"
apply (erule Scomp.induct, auto)
done

subsection\<open>Preservation lemma\<close>

lemma union_preserve_comp: "u \<sim> v ==> v \<sim> (u \<squnion> v)"
by (erule Scomp.induct, simp_all)

lemma preservation [rule_format]:
     "u \<sim> v ==> regular(v) \<longrightarrow> u|>v = (u \<squnion> v)|>v"
apply (erule Scomp.induct, safe)
apply (drule_tac [3] psi = "Fun (u) |> v = w" for u v w in asm_rl)
apply (auto simp add: union_preserve_comp comp_sym_iff)
done


declare sub_comp [THEN comp_sym, simp]

subsection\<open>Prism theorem\<close>

(* Having more assumptions than needed -- removed below  *)
lemma prism_l [rule_format]:
     "v \<Longleftarrow> u \<Longrightarrow>  
       regular(u) \<longrightarrow> (\<forall>w. w \<sim> v \<longrightarrow> w \<sim> u \<longrightarrow>   
                            w |> u = (w|>v) |> (u|>v))"
by (erule Ssub.induct, force+)

lemma prism: "[|v \<Longleftarrow> u; regular(u); w \<sim> v|] ==> w |> u = (w|>v) |> (u|>v)"
apply (rule prism_l)
apply (rule_tac [4] comp_trans, auto)
done


subsection\<open>Levy's Cube Lemma\<close>

lemma cube: "[|u \<sim> v; regular(v); regular(u); w \<sim> u|]==>   
           (w|>u) |> (v|>u) = (w|>v) |> (u|>v)"
apply (subst preservation [of u], assumption, assumption)
apply (subst preservation [of v], erule comp_sym, assumption)
apply (subst prism [symmetric, of v])
apply (simp add: union_r comp_sym_iff)
apply (simp add: union_preserve_regular comp_sym_iff)
apply (erule comp_trans, assumption)
apply (simp add: prism [symmetric] union_l union_preserve_regular 
                 comp_sym_iff union_sym)
done


subsection\<open>paving theorem\<close>

lemma paving: "[|w \<sim> u; w \<sim> v; regular(u); regular(v)|]==>  
           \<exists>uv vu. (w|>u) |> vu = (w|>v) |> uv & (w|>u) \<sim> vu \<and>
             regular(vu) & (w|>v) \<sim> uv \<and> regular(uv)"
apply (subgoal_tac "u \<sim> v")
apply (safe intro!: exI)
apply (rule cube)
apply (simp_all add: comp_sym_iff)
apply (blast intro: residuals_preserve_comp comp_trans comp_sym)+
done


end

