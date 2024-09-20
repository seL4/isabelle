(*  Title:      ZF/Finite.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

prove:  b \<in> Fin(A) \<Longrightarrow> inj(b,b) \<subseteq> surj(b,b)
*)

section\<open>Finite Powerset Operator and Finite Function Space\<close>

theory Finite imports Inductive Epsilon Nat begin

(*The natural numbers as a datatype*)
rep_datatype
  elimination    natE
  induction      nat_induct
  case_eqns      nat_case_0 nat_case_succ
  recursor_eqns  recursor_0 recursor_succ


consts
  Fin       :: "i\<Rightarrow>i"
  FiniteFun :: "[i,i]\<Rightarrow>i"  (\<open>(\<open>notation=\<open>infix -||>\<close>\<close>_ -||>/ _)\<close> [61, 60] 60)

inductive
  domains   "Fin(A)" \<subseteq> "Pow(A)"
  intros
    emptyI:  "0 \<in> Fin(A)"
    consI:   "\<lbrakk>a \<in> A;  b \<in> Fin(A)\<rbrakk> \<Longrightarrow> cons(a,b) \<in> Fin(A)"
  type_intros  empty_subsetI cons_subsetI PowI
  type_elims   PowD [elim_format]

inductive
  domains   "FiniteFun(A,B)" \<subseteq> "Fin(A*B)"
  intros
    emptyI:  "0 \<in> A -||> B"
    consI:   "\<lbrakk>a \<in> A;  b \<in> B;  h \<in> A -||> B;  a \<notin> domain(h)\<rbrakk>
              \<Longrightarrow> cons(\<langle>a,b\<rangle>,h) \<in> A -||> B"
  type_intros Fin.intros


subsection \<open>Finite Powerset Operator\<close>

lemma Fin_mono: "A<=B \<Longrightarrow> Fin(A) \<subseteq> Fin(B)"
  unfolding Fin.defs
apply (rule lfp_mono)
apply (rule Fin.bnd_mono)+
apply blast
done

(* @{term"A \<in> Fin(B) \<Longrightarrow> A \<subseteq> B"} *)
lemmas FinD = Fin.dom_subset [THEN subsetD, THEN PowD]

(** Induction on finite sets **)

(*Discharging @{term"x\<notin>y"} entails extra work*)
lemma Fin_induct [case_names 0 cons, induct set: Fin]:
    "\<lbrakk>b \<in> Fin(A);
        P(0);
        \<And>x y. \<lbrakk>x \<in> A;  y \<in> Fin(A);  x\<notin>y;  P(y)\<rbrakk> \<Longrightarrow> P(cons(x,y))
\<rbrakk> \<Longrightarrow> P(b)"
apply (erule Fin.induct, simp)
apply (case_tac "a \<in> b")
 apply (erule cons_absorb [THEN ssubst], assumption) (*backtracking!*)
apply simp
done


(** Simplification for Fin **)
declare Fin.intros [simp]

lemma Fin_0: "Fin(0) = {0}"
by (blast intro: Fin.emptyI dest: FinD)

(*The union of two finite sets is finite.*)
lemma Fin_UnI [simp]: "\<lbrakk>b \<in> Fin(A);  c \<in> Fin(A)\<rbrakk> \<Longrightarrow> b \<union> c \<in> Fin(A)"
apply (erule Fin_induct)
apply (simp_all add: Un_cons)
done


(*The union of a set of finite sets is finite.*)
lemma Fin_UnionI: "C \<in> Fin(Fin(A)) \<Longrightarrow> \<Union>(C) \<in> Fin(A)"
by (erule Fin_induct, simp_all)

(*Every subset of a finite set is finite.*)
lemma Fin_subset_lemma [rule_format]: "b \<in> Fin(A) \<Longrightarrow> \<forall>z. z<=b \<longrightarrow> z \<in> Fin(A)"
apply (erule Fin_induct)
apply (simp add: subset_empty_iff)
apply (simp add: subset_cons_iff distrib_simps, safe)
apply (erule_tac b = z in cons_Diff [THEN subst], simp)
done

lemma Fin_subset: "\<lbrakk>c<=b;  b \<in> Fin(A)\<rbrakk> \<Longrightarrow> c \<in> Fin(A)"
by (blast intro: Fin_subset_lemma)

lemma Fin_IntI1 [intro,simp]: "b \<in> Fin(A) \<Longrightarrow> b \<inter> c \<in> Fin(A)"
by (blast intro: Fin_subset)

lemma Fin_IntI2 [intro,simp]: "c \<in> Fin(A) \<Longrightarrow> b \<inter> c \<in> Fin(A)"
by (blast intro: Fin_subset)

lemma Fin_0_induct_lemma [rule_format]:
    "\<lbrakk>c \<in> Fin(A);  b \<in> Fin(A); P(b);
        \<And>x y. \<lbrakk>x \<in> A;  y \<in> Fin(A);  x \<in> y;  P(y)\<rbrakk> \<Longrightarrow> P(y-{x})
\<rbrakk> \<Longrightarrow> c<=b \<longrightarrow> P(b-c)"
apply (erule Fin_induct, simp)
apply (subst Diff_cons)
apply (simp add: cons_subset_iff Diff_subset [THEN Fin_subset])
done

lemma Fin_0_induct:
    "\<lbrakk>b \<in> Fin(A);
        P(b);
        \<And>x y. \<lbrakk>x \<in> A;  y \<in> Fin(A);  x \<in> y;  P(y)\<rbrakk> \<Longrightarrow> P(y-{x})
\<rbrakk> \<Longrightarrow> P(0)"
apply (rule Diff_cancel [THEN subst])
apply (blast intro: Fin_0_induct_lemma)
done

(*Functions from a finite ordinal*)
lemma nat_fun_subset_Fin: "n \<in> nat \<Longrightarrow> n->A \<subseteq> Fin(nat*A)"
apply (induct_tac "n")
apply (simp add: subset_iff)
apply (simp add: succ_def mem_not_refl [THEN cons_fun_eq])
apply (fast intro!: Fin.consI)
done


subsection\<open>Finite Function Space\<close>

lemma FiniteFun_mono:
    "\<lbrakk>A<=C;  B<=D\<rbrakk> \<Longrightarrow> A -||> B  \<subseteq>  C -||> D"
  unfolding FiniteFun.defs
apply (rule lfp_mono)
apply (rule FiniteFun.bnd_mono)+
apply (intro Fin_mono Sigma_mono basic_monos, assumption+)
done

lemma FiniteFun_mono1: "A<=B \<Longrightarrow> A -||> A  \<subseteq>  B -||> B"
by (blast dest: FiniteFun_mono)

lemma FiniteFun_is_fun: "h \<in> A -||>B \<Longrightarrow> h \<in> domain(h) -> B"
apply (erule FiniteFun.induct, simp)
apply (simp add: fun_extend3)
done

lemma FiniteFun_domain_Fin: "h \<in> A -||>B \<Longrightarrow> domain(h) \<in> Fin(A)"
by (erule FiniteFun.induct, simp, simp)

lemmas FiniteFun_apply_type = FiniteFun_is_fun [THEN apply_type]

(*Every subset of a finite function is a finite function.*)
lemma FiniteFun_subset_lemma [rule_format]:
     "b \<in> A-||>B \<Longrightarrow> \<forall>z. z<=b \<longrightarrow> z \<in> A-||>B"
apply (erule FiniteFun.induct)
apply (simp add: subset_empty_iff FiniteFun.intros)
apply (simp add: subset_cons_iff distrib_simps, safe)
apply (erule_tac b = z in cons_Diff [THEN subst])
apply (drule spec [THEN mp], assumption)
apply (fast intro!: FiniteFun.intros)
done

lemma FiniteFun_subset: "\<lbrakk>c<=b;  b \<in> A-||>B\<rbrakk> \<Longrightarrow> c \<in> A-||>B"
by (blast intro: FiniteFun_subset_lemma)

(** Some further results by Sidi O. Ehmety **)

lemma fun_FiniteFunI [rule_format]: "A \<in> Fin(X) \<Longrightarrow> \<forall>f. f \<in> A->B \<longrightarrow> f \<in> A-||>B"
apply (erule Fin.induct)
 apply (simp add: FiniteFun.intros, clarify)
apply (case_tac "a \<in> b")
 apply (simp add: cons_absorb)
apply (subgoal_tac "restrict (f,b) \<in> b -||> B")
 prefer 2 apply (blast intro: restrict_type2)
apply (subst fun_cons_restrict_eq, assumption)
apply (simp add: restrict_def lam_def)
apply (blast intro: apply_funtype FiniteFun.intros
                    FiniteFun_mono [THEN [2] rev_subsetD])
done

lemma lam_FiniteFun: "A \<in> Fin(X) \<Longrightarrow> (\<lambda>x\<in>A. b(x)) \<in> A -||> {b(x). x \<in> A}"
by (blast intro: fun_FiniteFunI lam_funtype)

lemma FiniteFun_Collect_iff:
     "f \<in> FiniteFun(A, {y \<in> B. P(y)})
      \<longleftrightarrow> f \<in> FiniteFun(A,B) \<and> (\<forall>x\<in>domain(f). P(f`x))"
apply auto
apply (blast intro: FiniteFun_mono [THEN [2] rev_subsetD])
apply (blast dest: Pair_mem_PiD FiniteFun_is_fun)
apply (rule_tac A1="domain(f)" in
       subset_refl [THEN [2] FiniteFun_mono, THEN subsetD])
 apply (fast dest: FiniteFun_domain_Fin Fin.dom_subset [THEN subsetD])
apply (rule fun_FiniteFunI)
apply (erule FiniteFun_domain_Fin)
apply (rule_tac B = "range (f) " in fun_weaken_type)
 apply (blast dest: FiniteFun_is_fun range_of_fun range_type apply_equality)+
done


subsection\<open>The Contents of a Singleton Set\<close>

definition
  contents :: "i\<Rightarrow>i"  where
   "contents(X) \<equiv> THE x. X = {x}"

lemma contents_eq [simp]: "contents ({x}) = x"
by (simp add: contents_def)

end
