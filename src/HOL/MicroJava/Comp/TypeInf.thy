(*  Title:      HOL/MicroJava/Comp/TypeInf.thy
    Author:     Martin Strecker
*)

(* Exact position in theory hierarchy still to be determined *)
theory TypeInf
imports "../J/WellType"
begin



(**********************************************************************)


(*** Inversion of typing rules -- to be moved into WellType.thy
     Also modify the wtpd_expr_\<dots> proofs in CorrComp.thy ***)

lemma NewC_invers:
  assumes "E\<turnstile>NewC C::T"
  shows "T = Class C \<and> is_class (prg E) C"
  using assms by cases auto

lemma Cast_invers:
  assumes "E\<turnstile>Cast D e::T"
  shows "\<exists>C. T = Class D \<and> E\<turnstile>e::C \<and> is_class (prg E) D \<and> prg E\<turnstile>C\<preceq>? Class D"
  using assms by cases auto

lemma Lit_invers:
  assumes "E\<turnstile>Lit x::T"
  shows "typeof (\<lambda>v. None) x = Some T"
  using assms by cases auto

lemma LAcc_invers:
  assumes "E\<turnstile>LAcc v::T"
  shows "localT E v = Some T \<and> is_type (prg E) T"
  using assms by cases auto

lemma BinOp_invers:
  assumes "E\<turnstile>BinOp bop e1 e2::T'"
  shows "\<exists>T. E\<turnstile>e1::T \<and> E\<turnstile>e2::T \<and>
            (if bop = Eq then T' = PrimT Boolean
                        else T' = T \<and> T = PrimT Integer)"
  using assms by cases auto

lemma LAss_invers:
  assumes  "E\<turnstile>v::=e::T'"
  shows "\<exists>T. v ~= This \<and> E\<turnstile>LAcc v::T \<and> E\<turnstile>e::T' \<and> prg E\<turnstile>T'\<preceq>T"
  using assms by cases auto

lemma FAcc_invers:
  assumes "E\<turnstile>{fd}a..fn::fT"
  shows "\<exists>C. E\<turnstile>a::Class C \<and> field (prg E,C) fn = Some (fd, fT)"
  using assms by cases auto

lemma FAss_invers:
  assumes "E\<turnstile>{fd}a..fn:=v::T'"
  shows "\<exists>T. E\<turnstile>{fd}a..fn::T \<and> E\<turnstile>v ::T' \<and> prg E\<turnstile>T'\<preceq>T"
  using assms by cases auto

lemma Call_invers:
  assumes "E\<turnstile>{C}a..mn({pTs'}ps)::rT"
  shows "\<exists>pTs md.
    E\<turnstile>a::Class C \<and> E\<turnstile>ps[::]pTs \<and> max_spec (prg E) C (mn, pTs) = {((md,rT),pTs')}"
  using assms by cases auto


lemma Nil_invers:
  assumes "E\<turnstile>[] [::] Ts"
  shows "Ts = []"
  using assms by cases auto

lemma Cons_invers:
  assumes "E\<turnstile>e#es[::]Ts"
  shows "\<exists>T Ts'. Ts = T#Ts' \<and> E \<turnstile>e::T \<and> E \<turnstile>es[::]Ts'"
  using assms by cases auto


lemma Expr_invers:
  assumes "E\<turnstile>Expr e\<surd>"
  shows "\<exists> T. E\<turnstile>e::T"
  using assms by cases auto

lemma Comp_invers:
  assumes "E\<turnstile>s1;; s2\<surd>"
  shows "E\<turnstile>s1\<surd> \<and> E\<turnstile>s2\<surd>"
  using assms by cases auto

lemma Cond_invers:
  assumes "E\<turnstile>If(e) s1 Else s2\<surd>"
  shows "E\<turnstile>e::PrimT Boolean \<and> E\<turnstile>s1\<surd> \<and> E\<turnstile>s2\<surd>"
  using assms by cases auto

lemma Loop_invers:
  assumes "E\<turnstile>While(e) s\<surd>"
  shows "E\<turnstile>e::PrimT Boolean \<and> E\<turnstile>s\<surd>"
  using assms by cases auto


(**********************************************************************)


declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

(* Uniqueness of types property *)

lemma uniqueness_of_types: "
  (\<forall> (E\<Colon>'a prog \<times> (vname \<Rightarrow> ty option)) T1 T2. 
  E\<turnstile>e :: T1 \<longrightarrow> E\<turnstile>e :: T2 \<longrightarrow> T1 = T2) \<and>
  (\<forall> (E\<Colon>'a prog \<times> (vname \<Rightarrow> ty option)) Ts1 Ts2. 
  E\<turnstile>es [::] Ts1 \<longrightarrow> E\<turnstile>es [::] Ts2 \<longrightarrow> Ts1 = Ts2)"
apply (rule compat_expr_expr_list.induct)

(* NewC *)
apply (intro strip)
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+

(* Cast *)
apply (intro strip) 
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+

(* Lit *)
apply (intro strip) 
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+

(* BinOp *)
apply (intro strip)
apply (rename_tac binop x2 x3 E T1 T2, case_tac binop)
(* Eq *)
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+
(* Add *)
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+

(* LAcc *)
apply (intro strip) 
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+

(* LAss *)
apply (intro strip) 
apply (erule ty_expr.cases) apply simp+
apply (erule ty_expr.cases) apply simp+


(* FAcc *)
apply (intro strip)
apply (drule FAcc_invers)+ apply (erule exE)+ 
  apply (subgoal_tac "C = Ca", simp) apply blast


(* FAss *)
apply (intro strip)
apply (drule FAss_invers)+ apply (erule exE)+ apply (erule conjE)+
apply (drule FAcc_invers)+ apply (erule exE)+ apply blast 


(* Call *)
apply (intro strip)
apply (drule Call_invers)+ apply (erule exE)+ apply (erule conjE)+
apply (subgoal_tac "pTs = pTsa", simp) apply blast

(* expression lists *)
apply (intro strip)
apply (erule ty_exprs.cases)+ apply simp+

apply (intro strip)
apply (erule ty_exprs.cases, simp)
apply (erule ty_exprs.cases, simp)
apply (subgoal_tac "e = ea", simp) apply simp
done


lemma uniqueness_of_types_expr [rule_format (no_asm)]: "
  (\<forall> E T1 T2. E\<turnstile>e :: T1 \<longrightarrow> E\<turnstile>e :: T2 \<longrightarrow> T1 = T2)"
by (rule uniqueness_of_types [THEN conjunct1])

lemma uniqueness_of_types_exprs [rule_format (no_asm)]: "
  (\<forall> E Ts1 Ts2. E\<turnstile>es [::] Ts1 \<longrightarrow> E\<turnstile>es [::] Ts2 \<longrightarrow> Ts1 = Ts2)"
by (rule uniqueness_of_types [THEN conjunct2])


  

definition inferred_tp :: "[java_mb env, expr] \<Rightarrow> ty" where
  "inferred_tp E e == (SOME T. E\<turnstile>e :: T)"

definition inferred_tps :: "[java_mb env, expr list] \<Rightarrow> ty list" where
  "inferred_tps E es == (SOME Ts. E\<turnstile>es [::] Ts)"

(* get inferred type(s) for well-typed term *)
lemma inferred_tp_wt: "E\<turnstile>e :: T \<Longrightarrow> (inferred_tp E e) = T"
by (auto simp: inferred_tp_def intro: uniqueness_of_types_expr)

lemma inferred_tps_wt: "E\<turnstile>es [::] Ts \<Longrightarrow> (inferred_tps E es) = Ts"
by (auto simp: inferred_tps_def intro: uniqueness_of_types_exprs)


end

