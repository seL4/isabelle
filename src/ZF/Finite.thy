(*  Title:      ZF/Finite.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Finite powerset operator; finite function space

prove X:Fin(A) ==> |X| < nat

prove:  b: Fin(A) ==> inj(b,b) <= surj(b,b)
*)

theory Finite = Inductive + Epsilon + Nat:

(*The natural numbers as a datatype*)
rep_datatype
  elimination    natE
  induction	 nat_induct
  case_eqns	 nat_case_0 nat_case_succ
  recursor_eqns  recursor_0 recursor_succ


consts
  Fin       :: "i=>i"
  FiniteFun :: "[i,i]=>i"         ("(_ -||>/ _)" [61, 60] 60)

inductive
  domains   "Fin(A)" <= "Pow(A)"
  intros
    emptyI:  "0 : Fin(A)"
    consI:   "[| a: A;  b: Fin(A) |] ==> cons(a,b) : Fin(A)"
  type_intros  empty_subsetI cons_subsetI PowI
  type_elims   PowD [THEN revcut_rl]

inductive
  domains   "FiniteFun(A,B)" <= "Fin(A*B)"
  intros
    emptyI:  "0 : A -||> B"
    consI:   "[| a: A;  b: B;  h: A -||> B;  a ~: domain(h) |]
              ==> cons(<a,b>,h) : A -||> B"
  type_intros Fin.intros


subsection {* Finite powerset operator *}

lemma Fin_mono: "A<=B ==> Fin(A) <= Fin(B)"
apply (unfold Fin.defs)
apply (rule lfp_mono)
apply (rule Fin.bnd_mono)+
apply blast
done

(* A : Fin(B) ==> A <= B *)
lemmas FinD = Fin.dom_subset [THEN subsetD, THEN PowD, standard]

(** Induction on finite sets **)

(*Discharging x~:y entails extra work*)
lemma Fin_induct:
    "[| b: Fin(A);
        P(0);
        !!x y. [| x: A;  y: Fin(A);  x~:y;  P(y) |] ==> P(cons(x,y))
     |] ==> P(b)"
apply (erule Fin.induct, simp)
apply (case_tac "a:b")
 apply (erule cons_absorb [THEN ssubst], assumption) (*backtracking!*)
apply simp
done

(*fixed up for induct method*)
lemmas Fin_induct = Fin_induct [case_names 0 cons, induct set: Fin]


(** Simplification for Fin **)
declare Fin.intros [simp]

lemma Fin_0: "Fin(0) = {0}"
by (blast intro: Fin.emptyI dest: FinD)

(*The union of two finite sets is finite.*)
lemma Fin_UnI [simp]: "[| b: Fin(A);  c: Fin(A) |] ==> b Un c : Fin(A)"
apply (erule Fin_induct)
apply (simp_all add: Un_cons)
done


(*The union of a set of finite sets is finite.*)
lemma Fin_UnionI: "C : Fin(Fin(A)) ==> Union(C) : Fin(A)"
by (erule Fin_induct, simp_all)

(*Every subset of a finite set is finite.*)
lemma Fin_subset_lemma [rule_format]: "b: Fin(A) ==> \<forall>z. z<=b --> z: Fin(A)"
apply (erule Fin_induct)
apply (simp add: subset_empty_iff)
apply (simp add: subset_cons_iff distrib_simps, safe)
apply (erule_tac b = "z" in cons_Diff [THEN subst], simp)
done

lemma Fin_subset: "[| c<=b;  b: Fin(A) |] ==> c: Fin(A)"
by (blast intro: Fin_subset_lemma)

lemma Fin_IntI1 [intro,simp]: "b: Fin(A) ==> b Int c : Fin(A)"
by (blast intro: Fin_subset)

lemma Fin_IntI2 [intro,simp]: "c: Fin(A) ==> b Int c : Fin(A)"
by (blast intro: Fin_subset)

lemma Fin_0_induct_lemma [rule_format]:
    "[| c: Fin(A);  b: Fin(A); P(b);
        !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x})
     |] ==> c<=b --> P(b-c)"
apply (erule Fin_induct, simp)
apply (subst Diff_cons)
apply (simp add: cons_subset_iff Diff_subset [THEN Fin_subset])
done

lemma Fin_0_induct:
    "[| b: Fin(A);
        P(b);
        !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x})
     |] ==> P(0)"
apply (rule Diff_cancel [THEN subst])
apply (blast intro: Fin_0_induct_lemma) 
done

(*Functions from a finite ordinal*)
lemma nat_fun_subset_Fin: "n: nat ==> n->A <= Fin(nat*A)"
apply (induct_tac "n")
apply (simp add: subset_iff)
apply (simp add: succ_def mem_not_refl [THEN cons_fun_eq])
apply (fast intro!: Fin.consI)
done


(*** Finite function space ***)

lemma FiniteFun_mono:
    "[| A<=C;  B<=D |] ==> A -||> B  <=  C -||> D"
apply (unfold FiniteFun.defs)
apply (rule lfp_mono)
apply (rule FiniteFun.bnd_mono)+
apply (intro Fin_mono Sigma_mono basic_monos, assumption+)
done

lemma FiniteFun_mono1: "A<=B ==> A -||> A  <=  B -||> B"
by (blast dest: FiniteFun_mono)

lemma FiniteFun_is_fun: "h: A -||>B ==> h: domain(h) -> B"
apply (erule FiniteFun.induct, simp)
apply (simp add: fun_extend3)
done

lemma FiniteFun_domain_Fin: "h: A -||>B ==> domain(h) : Fin(A)"
apply (erule FiniteFun.induct, simp)
apply simp
done

lemmas FiniteFun_apply_type = FiniteFun_is_fun [THEN apply_type, standard]

(*Every subset of a finite function is a finite function.*)
lemma FiniteFun_subset_lemma [rule_format]:
     "b: A-||>B ==> ALL z. z<=b --> z: A-||>B"
apply (erule FiniteFun.induct)
apply (simp add: subset_empty_iff FiniteFun.intros)
apply (simp add: subset_cons_iff distrib_simps, safe)
apply (erule_tac b = "z" in cons_Diff [THEN subst])
apply (drule spec [THEN mp], assumption)
apply (fast intro!: FiniteFun.intros)
done

lemma FiniteFun_subset: "[| c<=b;  b: A-||>B |] ==> c: A-||>B"
by (blast intro: FiniteFun_subset_lemma)

(** Some further results by Sidi O. Ehmety **)

lemma fun_FiniteFunI [rule_format]: "A:Fin(X) ==> ALL f. f:A->B --> f:A-||>B"
apply (erule Fin.induct)
 apply (simp add: FiniteFun.intros)
apply clarify
apply (case_tac "a:b")
 apply (rotate_tac -1)
 apply (simp add: cons_absorb)
apply (subgoal_tac "restrict (f,b) : b -||> B")
 prefer 2 apply (blast intro: restrict_type2)
apply (subst fun_cons_restrict_eq, assumption)
apply (simp add: restrict_def lam_def)
apply (blast intro: apply_funtype FiniteFun.intros 
                    FiniteFun_mono [THEN [2] rev_subsetD])
done

lemma lam_FiniteFun: "A: Fin(X) ==> (lam x:A. b(x)) : A -||> {b(x). x:A}"
by (blast intro: fun_FiniteFunI lam_funtype)

lemma FiniteFun_Collect_iff:
     "f : FiniteFun(A, {y:B. P(y)})
      <-> f : FiniteFun(A,B) & (ALL x:domain(f). P(f`x))"
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

ML
{*
val Fin_intros = thms "Fin.intros";

val Fin_mono = thm "Fin_mono";
val FinD = thm "FinD";
val Fin_induct = thm "Fin_induct";
val Fin_UnI = thm "Fin_UnI";
val Fin_UnionI = thm "Fin_UnionI";
val Fin_subset = thm "Fin_subset";
val Fin_IntI1 = thm "Fin_IntI1";
val Fin_IntI2 = thm "Fin_IntI2";
val Fin_0_induct = thm "Fin_0_induct";
val nat_fun_subset_Fin = thm "nat_fun_subset_Fin";
val FiniteFun_mono = thm "FiniteFun_mono";
val FiniteFun_mono1 = thm "FiniteFun_mono1";
val FiniteFun_is_fun = thm "FiniteFun_is_fun";
val FiniteFun_domain_Fin = thm "FiniteFun_domain_Fin";
val FiniteFun_apply_type = thm "FiniteFun_apply_type";
val FiniteFun_subset = thm "FiniteFun_subset";
val fun_FiniteFunI = thm "fun_FiniteFunI";
val lam_FiniteFun = thm "lam_FiniteFun";
val FiniteFun_Collect_iff = thm "FiniteFun_Collect_iff";
*}

end
