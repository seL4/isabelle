(*  Title:      ZF/Finite.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

prove:  b \<in> Fin(A) ==> inj(b,b) \<subseteq> surj(b,b)
*)

header{*Finite Powerset Operator and Finite Function Space*}

theory Finite imports Inductive_ZF Epsilon Nat_ZF begin

(*The natural numbers as a datatype*)
rep_datatype
  elimination    natE
  induction      nat_induct
  case_eqns      nat_case_0 nat_case_succ
  recursor_eqns  recursor_0 recursor_succ


consts
  Fin       :: "i=>i"
  FiniteFun :: "[i,i]=>i"         ("(_ -||>/ _)" [61, 60] 60)

inductive
  domains   "Fin(A)" \<subseteq> "Pow(A)"
  intros
    emptyI:  "0 \<in> Fin(A)"
    consI:   "[| a \<in> A;  b \<in> Fin(A) |] ==> cons(a,b) \<in> Fin(A)"
  type_intros  empty_subsetI cons_subsetI PowI
  type_elims   PowD [elim_format]

inductive
  domains   "FiniteFun(A,B)" \<subseteq> "Fin(A*B)"
  intros
    emptyI:  "0 \<in> A -||> B"
    consI:   "[| a \<in> A;  b \<in> B;  h \<in> A -||> B;  a \<notin> domain(h) |]
              ==> cons(<a,b>,h) \<in> A -||> B"
  type_intros Fin.intros


subsection {* Finite Powerset Operator *}

lemma Fin_mono: "A<=B ==> Fin(A) \<subseteq> Fin(B)"
apply (unfold Fin.defs)
apply (rule lfp_mono)
apply (rule Fin.bnd_mono)+
apply blast
done

(* @{term"A \<in> Fin(B) ==> A \<subseteq> B"} *)
lemmas FinD = Fin.dom_subset [THEN subsetD, THEN PowD]

(** Induction on finite sets **)

(*Discharging @{term"x\<notin>y"} entails extra work*)
lemma Fin_induct [case_names 0 cons, induct set: Fin]:
    "[| b \<in> Fin(A);
        P(0);
        !!x y. [| x \<in> A;  y \<in> Fin(A);  x\<notin>y;  P(y) |] ==> P(cons(x,y))
     |] ==> P(b)"
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
lemma Fin_UnI [simp]: "[| b \<in> Fin(A);  c \<in> Fin(A) |] ==> b \<union> c \<in> Fin(A)"
apply (erule Fin_induct)
apply (simp_all add: Un_cons)
done


(*The union of a set of finite sets is finite.*)
lemma Fin_UnionI: "C \<in> Fin(Fin(A)) ==> \<Union>(C) \<in> Fin(A)"
by (erule Fin_induct, simp_all)

(*Every subset of a finite set is finite.*)
lemma Fin_subset_lemma [rule_format]: "b \<in> Fin(A) ==> \<forall>z. z<=b \<longrightarrow> z \<in> Fin(A)"
apply (erule Fin_induct)
apply (simp add: subset_empty_iff)
apply (simp add: subset_cons_iff distrib_simps, safe)
apply (erule_tac b = z in cons_Diff [THEN subst], simp)
done

lemma Fin_subset: "[| c<=b;  b \<in> Fin(A) |] ==> c \<in> Fin(A)"
by (blast intro: Fin_subset_lemma)

lemma Fin_IntI1 [intro,simp]: "b \<in> Fin(A) ==> b \<inter> c \<in> Fin(A)"
by (blast intro: Fin_subset)

lemma Fin_IntI2 [intro,simp]: "c \<in> Fin(A) ==> b \<inter> c \<in> Fin(A)"
by (blast intro: Fin_subset)

lemma Fin_0_induct_lemma [rule_format]:
    "[| c \<in> Fin(A);  b \<in> Fin(A); P(b);
        !!x y. [| x \<in> A;  y \<in> Fin(A);  x \<in> y;  P(y) |] ==> P(y-{x})
     |] ==> c<=b \<longrightarrow> P(b-c)"
apply (erule Fin_induct, simp)
apply (subst Diff_cons)
apply (simp add: cons_subset_iff Diff_subset [THEN Fin_subset])
done

lemma Fin_0_induct:
    "[| b \<in> Fin(A);
        P(b);
        !!x y. [| x \<in> A;  y \<in> Fin(A);  x \<in> y;  P(y) |] ==> P(y-{x})
     |] ==> P(0)"
apply (rule Diff_cancel [THEN subst])
apply (blast intro: Fin_0_induct_lemma)
done

(*Functions from a finite ordinal*)
lemma nat_fun_subset_Fin: "n \<in> nat ==> n->A \<subseteq> Fin(nat*A)"
apply (induct_tac "n")
apply (simp add: subset_iff)
apply (simp add: succ_def mem_not_refl [THEN cons_fun_eq])
apply (fast intro!: Fin.consI)
done


subsection{*Finite Function Space*}

lemma FiniteFun_mono:
    "[| A<=C;  B<=D |] ==> A -||> B  \<subseteq>  C -||> D"
apply (unfold FiniteFun.defs)
apply (rule lfp_mono)
apply (rule FiniteFun.bnd_mono)+
apply (intro Fin_mono Sigma_mono basic_monos, assumption+)
done

lemma FiniteFun_mono1: "A<=B ==> A -||> A  \<subseteq>  B -||> B"
by (blast dest: FiniteFun_mono)

lemma FiniteFun_is_fun: "h \<in> A -||>B ==> h \<in> domain(h) -> B"
apply (erule FiniteFun.induct, simp)
apply (simp add: fun_extend3)
done

lemma FiniteFun_domain_Fin: "h \<in> A -||>B ==> domain(h) \<in> Fin(A)"
by (erule FiniteFun.induct, simp, simp)

lemmas FiniteFun_apply_type = FiniteFun_is_fun [THEN apply_type]

(*Every subset of a finite function is a finite function.*)
lemma FiniteFun_subset_lemma [rule_format]:
     "b \<in> A-||>B ==> \<forall>z. z<=b \<longrightarrow> z \<in> A-||>B"
apply (erule FiniteFun.induct)
apply (simp add: subset_empty_iff FiniteFun.intros)
apply (simp add: subset_cons_iff distrib_simps, safe)
apply (erule_tac b = z in cons_Diff [THEN subst])
apply (drule spec [THEN mp], assumption)
apply (fast intro!: FiniteFun.intros)
done

lemma FiniteFun_subset: "[| c<=b;  b \<in> A-||>B |] ==> c \<in> A-||>B"
by (blast intro: FiniteFun_subset_lemma)

(** Some further results by Sidi O. Ehmety **)

lemma fun_FiniteFunI [rule_format]: "A \<in> Fin(X) ==> \<forall>f. f \<in> A->B \<longrightarrow> f \<in> A-||>B"
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

lemma lam_FiniteFun: "A \<in> Fin(X) ==> (\<lambda>x\<in>A. b(x)) \<in> A -||> {b(x). x \<in> A}"
by (blast intro: fun_FiniteFunI lam_funtype)

lemma FiniteFun_Collect_iff:
     "f \<in> FiniteFun(A, {y \<in> B. P(y)})
      \<longleftrightarrow> f \<in> FiniteFun(A,B) & (\<forall>x\<in>domain(f). P(f`x))"
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


subsection{*The Contents of a Singleton Set*}

definition
  contents :: "i=>i"  where
   "contents(X) == THE x. X = {x}"

lemma contents_eq [simp]: "contents ({x}) = x"
by (simp add: contents_def)

end
