(*  Title:      ZF/Constructible/Formula.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>First-Order Formulas and the Definition of the Class L\<close>

theory Formula imports ZF begin

subsection\<open>Internalized formulas of FOL\<close>

text\<open>De Bruijn representation.
  Unbound variables get their denotations from an environment.\<close>

consts   formula :: i
datatype
  "formula" = Member ("x \<in> nat", "y \<in> nat")
            | Equal  ("x \<in> nat", "y \<in> nat")
            | Nand ("p \<in> formula", "q \<in> formula")
            | Forall ("p \<in> formula")

declare formula.intros [TC]

definition
  Neg :: "i\<Rightarrow>i" where
  "Neg(p) \<equiv> Nand(p,p)"

definition
  And :: "[i,i]\<Rightarrow>i" where
  "And(p,q) \<equiv> Neg(Nand(p,q))"

definition
  Or :: "[i,i]\<Rightarrow>i" where
  "Or(p,q) \<equiv> Nand(Neg(p),Neg(q))"

definition
  Implies :: "[i,i]\<Rightarrow>i" where
  "Implies(p,q) \<equiv> Nand(p,Neg(q))"

definition
  Iff :: "[i,i]\<Rightarrow>i" where
  "Iff(p,q) \<equiv> And(Implies(p,q), Implies(q,p))"

definition
  Exists :: "i\<Rightarrow>i" where
  "Exists(p) \<equiv> Neg(Forall(Neg(p)))"

lemma Neg_type [TC]: "p \<in> formula \<Longrightarrow> Neg(p) \<in> formula"
by (simp add: Neg_def)

lemma And_type [TC]: "\<lbrakk>p \<in> formula; q \<in> formula\<rbrakk> \<Longrightarrow> And(p,q) \<in> formula"
by (simp add: And_def)

lemma Or_type [TC]: "\<lbrakk>p \<in> formula; q \<in> formula\<rbrakk> \<Longrightarrow> Or(p,q) \<in> formula"
by (simp add: Or_def)

lemma Implies_type [TC]:
     "\<lbrakk>p \<in> formula; q \<in> formula\<rbrakk> \<Longrightarrow> Implies(p,q) \<in> formula"
by (simp add: Implies_def)

lemma Iff_type [TC]:
     "\<lbrakk>p \<in> formula; q \<in> formula\<rbrakk> \<Longrightarrow> Iff(p,q) \<in> formula"
by (simp add: Iff_def)

lemma Exists_type [TC]: "p \<in> formula \<Longrightarrow> Exists(p) \<in> formula"
by (simp add: Exists_def)


consts   satisfies :: "[i,i]\<Rightarrow>i"
primrec (*explicit lambda is required because the environment varies*)
  "satisfies(A,Member(x,y)) =
      (\<lambda>env \<in> list(A). bool_of_o (nth(x,env) \<in> nth(y,env)))"

  "satisfies(A,Equal(x,y)) =
      (\<lambda>env \<in> list(A). bool_of_o (nth(x,env) = nth(y,env)))"

  "satisfies(A,Nand(p,q)) =
      (\<lambda>env \<in> list(A). not ((satisfies(A,p)`env) and (satisfies(A,q)`env)))"

  "satisfies(A,Forall(p)) =
      (\<lambda>env \<in> list(A). bool_of_o (\<forall>x\<in>A. satisfies(A,p) ` (Cons(x,env)) = 1))"


lemma satisfies_type: "p \<in> formula \<Longrightarrow> satisfies(A,p) \<in> list(A) -> bool"
by (induct set: formula) simp_all

abbreviation
  sats :: "[i,i,i] \<Rightarrow> o" where
  "sats(A,p,env) \<equiv> satisfies(A,p)`env = 1"

lemma sats_Member_iff [simp]:
  "env \<in> list(A) \<Longrightarrow> sats(A, Member(x,y), env) \<longleftrightarrow> nth(x,env) \<in> nth(y,env)"
by simp

lemma sats_Equal_iff [simp]:
  "env \<in> list(A) \<Longrightarrow> sats(A, Equal(x,y), env) \<longleftrightarrow> nth(x,env) = nth(y,env)"
by simp

lemma sats_Nand_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> (sats(A, Nand(p,q), env)) \<longleftrightarrow> \<not> (sats(A,p,env) \<and> sats(A,q,env))"
by (simp add: Bool.and_def Bool.not_def cond_def)

lemma sats_Forall_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> sats(A, Forall(p), env) \<longleftrightarrow> (\<forall>x\<in>A. sats(A, p, Cons(x,env)))"
by simp

declare satisfies.simps [simp del]

subsection\<open>Dividing line between primitive and derived connectives\<close>

lemma sats_Neg_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> sats(A, Neg(p), env) \<longleftrightarrow> \<not> sats(A,p,env)"
by (simp add: Neg_def)

lemma sats_And_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> (sats(A, And(p,q), env)) \<longleftrightarrow> sats(A,p,env) \<and> sats(A,q,env)"
by (simp add: And_def)

lemma sats_Or_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> (sats(A, Or(p,q), env)) \<longleftrightarrow> sats(A,p,env) | sats(A,q,env)"
by (simp add: Or_def)

lemma sats_Implies_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> (sats(A, Implies(p,q), env)) \<longleftrightarrow> (sats(A,p,env) \<longrightarrow> sats(A,q,env))"
by (simp add: Implies_def, blast)

lemma sats_Iff_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> (sats(A, Iff(p,q), env)) \<longleftrightarrow> (sats(A,p,env) \<longleftrightarrow> sats(A,q,env))"
by (simp add: Iff_def, blast)

lemma sats_Exists_iff [simp]:
  "env \<in> list(A)
   \<Longrightarrow> sats(A, Exists(p), env) \<longleftrightarrow> (\<exists>x\<in>A. sats(A, p, Cons(x,env)))"
by (simp add: Exists_def)


subsubsection\<open>Derived rules to help build up formulas\<close>

lemma mem_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (x\<in>y) \<longleftrightarrow> sats(A, Member(i,j), env)"
by (simp add: satisfies.simps)

lemma equal_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (x=y) \<longleftrightarrow> sats(A, Equal(i,j), env)"
by (simp add: satisfies.simps)

lemma not_iff_sats:
      "\<lbrakk>P \<longleftrightarrow> sats(A,p,env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (\<not>P) \<longleftrightarrow> sats(A, Neg(p), env)"
by simp

lemma conj_iff_sats:
      "\<lbrakk>P \<longleftrightarrow> sats(A,p,env); Q \<longleftrightarrow> sats(A,q,env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (P \<and> Q) \<longleftrightarrow> sats(A, And(p,q), env)"
by (simp)

lemma disj_iff_sats:
      "\<lbrakk>P \<longleftrightarrow> sats(A,p,env); Q \<longleftrightarrow> sats(A,q,env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (P | Q) \<longleftrightarrow> sats(A, Or(p,q), env)"
by (simp)

lemma iff_iff_sats:
      "\<lbrakk>P \<longleftrightarrow> sats(A,p,env); Q \<longleftrightarrow> sats(A,q,env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (P \<longleftrightarrow> Q) \<longleftrightarrow> sats(A, Iff(p,q), env)"
by (simp)

lemma imp_iff_sats:
      "\<lbrakk>P \<longleftrightarrow> sats(A,p,env); Q \<longleftrightarrow> sats(A,q,env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (P \<longrightarrow> Q) \<longleftrightarrow> sats(A, Implies(p,q), env)"
by (simp)

lemma ball_iff_sats:
      "\<lbrakk>\<And>x. x\<in>A \<Longrightarrow> P(x) \<longleftrightarrow> sats(A, p, Cons(x, env)); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (\<forall>x\<in>A. P(x)) \<longleftrightarrow> sats(A, Forall(p), env)"
by (simp)

lemma bex_iff_sats:
      "\<lbrakk>\<And>x. x\<in>A \<Longrightarrow> P(x) \<longleftrightarrow> sats(A, p, Cons(x, env)); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> (\<exists>x\<in>A. P(x)) \<longleftrightarrow> sats(A, Exists(p), env)"
by (simp)

lemmas FOL_iff_sats =
        mem_iff_sats equal_iff_sats not_iff_sats conj_iff_sats
        disj_iff_sats imp_iff_sats iff_iff_sats imp_iff_sats ball_iff_sats
        bex_iff_sats


subsection\<open>Arity of a Formula: Maximum Free de Bruijn Index\<close>

consts   arity :: "i\<Rightarrow>i"
primrec
  "arity(Member(x,y)) = succ(x) \<union> succ(y)"

  "arity(Equal(x,y)) = succ(x) \<union> succ(y)"

  "arity(Nand(p,q)) = arity(p) \<union> arity(q)"

  "arity(Forall(p)) = Arith.pred(arity(p))"


lemma arity_type [TC]: "p \<in> formula \<Longrightarrow> arity(p) \<in> nat"
by (induct_tac p, simp_all)

lemma arity_Neg [simp]: "arity(Neg(p)) = arity(p)"
by (simp add: Neg_def)

lemma arity_And [simp]: "arity(And(p,q)) = arity(p) \<union> arity(q)"
by (simp add: And_def)

lemma arity_Or [simp]: "arity(Or(p,q)) = arity(p) \<union> arity(q)"
by (simp add: Or_def)

lemma arity_Implies [simp]: "arity(Implies(p,q)) = arity(p) \<union> arity(q)"
by (simp add: Implies_def)

lemma arity_Iff [simp]: "arity(Iff(p,q)) = arity(p) \<union> arity(q)"
by (simp add: Iff_def, blast)

lemma arity_Exists [simp]: "arity(Exists(p)) = Arith.pred(arity(p))"
by (simp add: Exists_def)


lemma arity_sats_iff [rule_format]:
  "\<lbrakk>p \<in> formula; extra \<in> list(A)\<rbrakk>
   \<Longrightarrow> \<forall>env \<in> list(A).
           arity(p) \<le> length(env) \<longrightarrow>
           sats(A, p, env @ extra) \<longleftrightarrow> sats(A, p, env)"
apply (induct_tac p)
apply (simp_all add: Arith.pred_def nth_append Un_least_lt_iff nat_imp_quasinat
                split: split_nat_case, auto)
done

lemma arity_sats1_iff:
  "\<lbrakk>arity(p) \<le> succ(length(env)); p \<in> formula; x \<in> A; env \<in> list(A);
      extra \<in> list(A)\<rbrakk>
   \<Longrightarrow> sats(A, p, Cons(x, env @ extra)) \<longleftrightarrow> sats(A, p, Cons(x, env))"
apply (insert arity_sats_iff [of p extra A "Cons(x,env)"])
apply simp
done


subsection\<open>Renaming Some de Bruijn Variables\<close>

definition
  incr_var :: "[i,i]\<Rightarrow>i" where
  "incr_var(x,nq) \<equiv> if x<nq then x else succ(x)"

lemma incr_var_lt: "x<nq \<Longrightarrow> incr_var(x,nq) = x"
by (simp add: incr_var_def)

lemma incr_var_le: "nq\<le>x \<Longrightarrow> incr_var(x,nq) = succ(x)"
apply (simp add: incr_var_def)
apply (blast dest: lt_trans1)
done

consts   incr_bv :: "i\<Rightarrow>i"
primrec
  "incr_bv(Member(x,y)) =
      (\<lambda>nq \<in> nat. Member (incr_var(x,nq), incr_var(y,nq)))"

  "incr_bv(Equal(x,y)) =
      (\<lambda>nq \<in> nat. Equal (incr_var(x,nq), incr_var(y,nq)))"

  "incr_bv(Nand(p,q)) =
      (\<lambda>nq \<in> nat. Nand (incr_bv(p)`nq, incr_bv(q)`nq))"

  "incr_bv(Forall(p)) =
      (\<lambda>nq \<in> nat. Forall (incr_bv(p) ` succ(nq)))"


lemma [TC]: "x \<in> nat \<Longrightarrow> incr_var(x,nq) \<in> nat"
by (simp add: incr_var_def)

lemma incr_bv_type [TC]: "p \<in> formula \<Longrightarrow> incr_bv(p) \<in> nat -> formula"
by (induct_tac p, simp_all)

text\<open>Obviously, \<^term>\<open>DPow\<close> is closed under complements and finite
intersections and unions.  Needs an inductive lemma to allow two lists of
parameters to be combined.\<close>

lemma sats_incr_bv_iff [rule_format]:
  "\<lbrakk>p \<in> formula; env \<in> list(A); x \<in> A\<rbrakk>
   \<Longrightarrow> \<forall>bvs \<in> list(A).
           sats(A, incr_bv(p) ` length(bvs), bvs @ Cons(x,env)) \<longleftrightarrow>
           sats(A, p, bvs@env)"
apply (induct_tac p)
apply (simp_all add: incr_var_def nth_append succ_lt_iff length_type)
apply (auto simp add: diff_succ not_lt_iff_le)
done


(*the following two lemmas prevent huge case splits in arity_incr_bv_lemma*)
lemma incr_var_lemma:
     "\<lbrakk>x \<in> nat; y \<in> nat; nq \<le> x\<rbrakk>
      \<Longrightarrow> succ(x) \<union> incr_var(y,nq) = succ(x \<union> y)"
apply (simp add: incr_var_def Ord_Un_if, auto)
  apply (blast intro: leI)
 apply (simp add: not_lt_iff_le)
 apply (blast intro: le_anti_sym)
apply (blast dest: lt_trans2)
done

lemma incr_And_lemma:
     "y < x \<Longrightarrow> y \<union> succ(x) = succ(x \<union> y)"
apply (simp add: Ord_Un_if lt_Ord lt_Ord2 succ_lt_iff)
apply (blast dest: lt_asym)
done

lemma arity_incr_bv_lemma [rule_format]:
  "p \<in> formula
   \<Longrightarrow> \<forall>n \<in> nat. arity (incr_bv(p) ` n) =
                 (if n < arity(p) then succ(arity(p)) else arity(p))"
apply (induct_tac p)
apply (simp_all add: imp_disj not_lt_iff_le Un_least_lt_iff lt_Un_iff le_Un_iff
                     succ_Un_distrib [symmetric] incr_var_lt incr_var_le
                     Un_commute incr_var_lemma Arith.pred_def nat_imp_quasinat
            split: split_nat_case)
 txt\<open>the Forall case reduces to linear arithmetic\<close>
 prefer 2
 apply clarify
 apply (blast dest: lt_trans1)
txt\<open>left with the And case\<close>
apply safe
 apply (blast intro: incr_And_lemma lt_trans1)
apply (subst incr_And_lemma)
 apply (blast intro: lt_trans1)
apply (simp add: Un_commute)
done


subsection\<open>Renaming all but the First de Bruijn Variable\<close>

definition
  incr_bv1 :: "i \<Rightarrow> i" where
  "incr_bv1(p) \<equiv> incr_bv(p)`1"


lemma incr_bv1_type [TC]: "p \<in> formula \<Longrightarrow> incr_bv1(p) \<in> formula"
by (simp add: incr_bv1_def)

(*For renaming all but the bound variable at level 0*)
lemma sats_incr_bv1_iff:
  "\<lbrakk>p \<in> formula; env \<in> list(A); x \<in> A; y \<in> A\<rbrakk>
   \<Longrightarrow> sats(A, incr_bv1(p), Cons(x, Cons(y, env))) \<longleftrightarrow>
       sats(A, p, Cons(x,env))"
apply (insert sats_incr_bv_iff [of p env A y "Cons(x,Nil)"])
apply (simp add: incr_bv1_def)
done

lemma formula_add_params1 [rule_format]:
  "\<lbrakk>p \<in> formula; n \<in> nat; x \<in> A\<rbrakk>
   \<Longrightarrow> \<forall>bvs \<in> list(A). \<forall>env \<in> list(A).
          length(bvs) = n \<longrightarrow>
          sats(A, iterates(incr_bv1, n, p), Cons(x, bvs@env)) \<longleftrightarrow>
          sats(A, p, Cons(x,env))"
apply (induct_tac n, simp, clarify)
apply (erule list.cases)
apply (simp_all add: sats_incr_bv1_iff)
done


lemma arity_incr_bv1_eq:
  "p \<in> formula
   \<Longrightarrow> arity(incr_bv1(p)) =
        (if 1 < arity(p) then succ(arity(p)) else arity(p))"
apply (insert arity_incr_bv_lemma [of p 1])
apply (simp add: incr_bv1_def)
done

lemma arity_iterates_incr_bv1_eq:
  "\<lbrakk>p \<in> formula; n \<in> nat\<rbrakk>
   \<Longrightarrow> arity(incr_bv1^n(p)) =
         (if 1 < arity(p) then n #+ arity(p) else arity(p))"
apply (induct_tac n)
apply (simp_all add: arity_incr_bv1_eq)
apply (simp add: not_lt_iff_le)
apply (blast intro: le_trans add_le_self2 arity_type)
done



subsection\<open>Definable Powerset\<close>

text\<open>The definable powerset operation: Kunen's definition VI 1.1, page 165.\<close>
definition
  DPow :: "i \<Rightarrow> i" where
  "DPow(A) \<equiv> {X \<in> Pow(A).
               \<exists>env \<in> list(A). \<exists>p \<in> formula.
                 arity(p) \<le> succ(length(env)) \<and>
                 X = {x\<in>A. sats(A, p, Cons(x,env))}}"

lemma DPowI:
  "\<lbrakk>env \<in> list(A);  p \<in> formula;  arity(p) \<le> succ(length(env))\<rbrakk>
   \<Longrightarrow> {x\<in>A. sats(A, p, Cons(x,env))} \<in> DPow(A)"
by (simp add: DPow_def, blast)

text\<open>With this rule we can specify \<^term>\<open>p\<close> later.\<close>
lemma DPowI2 [rule_format]:
  "\<lbrakk>\<forall>x\<in>A. P(x) \<longleftrightarrow> sats(A, p, Cons(x,env));
     env \<in> list(A);  p \<in> formula;  arity(p) \<le> succ(length(env))\<rbrakk>
   \<Longrightarrow> {x\<in>A. P(x)} \<in> DPow(A)"
by (simp add: DPow_def, blast)

lemma DPowD:
  "X \<in> DPow(A)
   \<Longrightarrow> X \<subseteq> A \<and>
       (\<exists>env \<in> list(A).
        \<exists>p \<in> formula. arity(p) \<le> succ(length(env)) \<and>
                      X = {x\<in>A. sats(A, p, Cons(x,env))})"
by (simp add: DPow_def)

lemmas DPow_imp_subset = DPowD [THEN conjunct1]

(*Kunen's Lemma VI 1.2*)
lemma "\<lbrakk>p \<in> formula; env \<in> list(A); arity(p) \<le> succ(length(env))\<rbrakk>
       \<Longrightarrow> {x\<in>A. sats(A, p, Cons(x,env))} \<in> DPow(A)"
by (blast intro: DPowI)

lemma DPow_subset_Pow: "DPow(A) \<subseteq> Pow(A)"
by (simp add: DPow_def, blast)

lemma empty_in_DPow: "0 \<in> DPow(A)"
apply (simp add: DPow_def)
apply (rule_tac x=Nil in bexI)
 apply (rule_tac x="Neg(Equal(0,0))" in bexI)
  apply (auto simp add: Un_least_lt_iff)
done

lemma Compl_in_DPow: "X \<in> DPow(A) \<Longrightarrow> (A-X) \<in> DPow(A)"
apply (simp add: DPow_def, clarify, auto)
apply (rule bexI)
 apply (rule_tac x="Neg(p)" in bexI)
  apply auto
done

lemma Int_in_DPow: "\<lbrakk>X \<in> DPow(A); Y \<in> DPow(A)\<rbrakk> \<Longrightarrow> X \<inter> Y \<in> DPow(A)"
apply (simp add: DPow_def, auto)
apply (rename_tac envp p envq q)
apply (rule_tac x="envp@envq" in bexI)
 apply (rule_tac x="And(p, iterates(incr_bv1,length(envp),q))" in bexI)
  apply typecheck
apply (rule conjI)
(*finally check the arity!*)
 apply (simp add: arity_iterates_incr_bv1_eq Un_least_lt_iff)
 apply (force intro: add_le_self le_trans)
apply (simp add: arity_sats1_iff formula_add_params1, blast)
done

lemma Un_in_DPow: "\<lbrakk>X \<in> DPow(A); Y \<in> DPow(A)\<rbrakk> \<Longrightarrow> X \<union> Y \<in> DPow(A)"
apply (subgoal_tac "X \<union> Y = A - ((A-X) \<inter> (A-Y))")
apply (simp add: Int_in_DPow Compl_in_DPow)
apply (simp add: DPow_def, blast)
done

lemma singleton_in_DPow: "a \<in> A \<Longrightarrow> {a} \<in> DPow(A)"
apply (simp add: DPow_def)
apply (rule_tac x="Cons(a,Nil)" in bexI)
 apply (rule_tac x="Equal(0,1)" in bexI)
  apply typecheck
apply (force simp add: succ_Un_distrib [symmetric])
done

lemma cons_in_DPow: "\<lbrakk>a \<in> A; X \<in> DPow(A)\<rbrakk> \<Longrightarrow> cons(a,X) \<in> DPow(A)"
apply (rule cons_eq [THEN subst])
apply (blast intro: singleton_in_DPow Un_in_DPow)
done

(*Part of Lemma 1.3*)
lemma Fin_into_DPow: "X \<in> Fin(A) \<Longrightarrow> X \<in> DPow(A)"
apply (erule Fin.induct)
 apply (rule empty_in_DPow)
apply (blast intro: cons_in_DPow)
done

text\<open>\<^term>\<open>DPow\<close> is not monotonic.  For example, let \<^term>\<open>A\<close> be some
non-constructible set of natural numbers, and let \<^term>\<open>B\<close> be \<^term>\<open>nat\<close>.
Then \<^term>\<open>A<=B\<close> and obviously \<^term>\<open>A \<in> DPow(A)\<close> but \<^term>\<open>A \<notin>
DPow(B)\<close>.\<close>

(*This may be true but the proof looks difficult, requiring relativization
lemma DPow_insert: "DPow (cons(a,A)) = DPow(A) \<union> {cons(a,X) . X \<in> DPow(A)}"
apply (rule equalityI, safe)
oops
*)

lemma Finite_Pow_subset_Pow: "Finite(A) \<Longrightarrow> Pow(A) \<subseteq> DPow(A)"
by (blast intro: Fin_into_DPow Finite_into_Fin Fin_subset)

lemma Finite_DPow_eq_Pow: "Finite(A) \<Longrightarrow> DPow(A) = Pow(A)"
apply (rule equalityI)
apply (rule DPow_subset_Pow)
apply (erule Finite_Pow_subset_Pow)
done


subsection\<open>Internalized Formulas for the Ordinals\<close>

text\<open>The \<open>sats\<close> theorems below differ from the usual form in that they
include an element of absoluteness.  That is, they relate internalized
formulas to real concepts such as the subset relation, rather than to the
relativized concepts defined in theory \<open>Relative\<close>.  This lets us prove
the theorem as \<open>Ords_in_DPow\<close> without first having to instantiate the
locale \<open>M_trivial\<close>.  Note that the present theory does not even take
\<open>Relative\<close> as a parent.\<close>

subsubsection\<open>The subset relation\<close>

definition
  subset_fm :: "[i,i]\<Rightarrow>i" where
  "subset_fm(x,y) \<equiv> Forall(Implies(Member(0,succ(x)), Member(0,succ(y))))"

lemma subset_type [TC]: "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> subset_fm(x,y) \<in> formula"
by (simp add: subset_fm_def)

lemma arity_subset_fm [simp]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> arity(subset_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: subset_fm_def succ_Un_distrib [symmetric])

lemma sats_subset_fm [simp]:
   "\<lbrakk>x < length(env); y \<in> nat; env \<in> list(A); Transset(A)\<rbrakk>
    \<Longrightarrow> sats(A, subset_fm(x,y), env) \<longleftrightarrow> nth(x,env) \<subseteq> nth(y,env)"
apply (frule lt_length_in_nat, assumption)
apply (simp add: subset_fm_def Transset_def)
apply (blast intro: nth_type)
done

subsubsection\<open>Transitive sets\<close>

definition
  transset_fm :: "i\<Rightarrow>i" where
  "transset_fm(x) \<equiv> Forall(Implies(Member(0,succ(x)), subset_fm(0,succ(x))))"

lemma transset_type [TC]: "x \<in> nat \<Longrightarrow> transset_fm(x) \<in> formula"
by (simp add: transset_fm_def)

lemma arity_transset_fm [simp]:
     "x \<in> nat \<Longrightarrow> arity(transset_fm(x)) = succ(x)"
by (simp add: transset_fm_def succ_Un_distrib [symmetric])

lemma sats_transset_fm [simp]:
   "\<lbrakk>x < length(env); env \<in> list(A); Transset(A)\<rbrakk>
    \<Longrightarrow> sats(A, transset_fm(x), env) \<longleftrightarrow> Transset(nth(x,env))"
apply (frule lt_nat_in_nat, erule length_type)
apply (simp add: transset_fm_def Transset_def)
apply (blast intro: nth_type)
done

subsubsection\<open>Ordinals\<close>

definition
  ordinal_fm :: "i\<Rightarrow>i" where
  "ordinal_fm(x) \<equiv>
    And(transset_fm(x), Forall(Implies(Member(0,succ(x)), transset_fm(0))))"

lemma ordinal_type [TC]: "x \<in> nat \<Longrightarrow> ordinal_fm(x) \<in> formula"
by (simp add: ordinal_fm_def)

lemma arity_ordinal_fm [simp]:
     "x \<in> nat \<Longrightarrow> arity(ordinal_fm(x)) = succ(x)"
by (simp add: ordinal_fm_def succ_Un_distrib [symmetric])

lemma sats_ordinal_fm:
   "\<lbrakk>x < length(env); env \<in> list(A); Transset(A)\<rbrakk>
    \<Longrightarrow> sats(A, ordinal_fm(x), env) \<longleftrightarrow> Ord(nth(x,env))"
apply (frule lt_nat_in_nat, erule length_type)
apply (simp add: ordinal_fm_def Ord_def Transset_def)
apply (blast intro: nth_type)
done

text\<open>The subset consisting of the ordinals is definable.  Essential lemma for
\<open>Ord_in_Lset\<close>.  This result is the objective of the present subsection.\<close>
theorem Ords_in_DPow: "Transset(A) \<Longrightarrow> {x \<in> A. Ord(x)} \<in> DPow(A)"
apply (simp add: DPow_def Collect_subset)
apply (rule_tac x=Nil in bexI)
 apply (rule_tac x="ordinal_fm(0)" in bexI)
apply (simp_all add: sats_ordinal_fm)
done


subsection\<open>Constant Lset: Levels of the Constructible Universe\<close>

definition
  Lset :: "i\<Rightarrow>i" where
  "Lset(i) \<equiv> transrec(i, \<lambda>x f. \<Union>y\<in>x. DPow(f`y))"

definition
  L :: "i\<Rightarrow>o" where \<comment> \<open>Kunen's definition VI 1.5, page 167\<close>
  "L(x) \<equiv> \<exists>i. Ord(i) \<and> x \<in> Lset(i)"

text\<open>NOT SUITABLE FOR REWRITING -- RECURSIVE!\<close>
lemma Lset: "Lset(i) = (\<Union>j\<in>i. DPow(Lset(j)))"
by (subst Lset_def [THEN def_transrec], simp)

lemma LsetI: "\<lbrakk>y\<in>x; A \<in> DPow(Lset(y))\<rbrakk> \<Longrightarrow> A \<in> Lset(x)"
by (subst Lset, blast)

lemma LsetD: "A \<in> Lset(x) \<Longrightarrow> \<exists>y\<in>x. A \<in> DPow(Lset(y))"
apply (insert Lset [of x])
apply (blast intro: elim: equalityE)
done

subsubsection\<open>Transitivity\<close>

lemma elem_subset_in_DPow: "\<lbrakk>X \<in> A; X \<subseteq> A\<rbrakk> \<Longrightarrow> X \<in> DPow(A)"
apply (simp add: Transset_def DPow_def)
apply (rule_tac x="[X]" in bexI)
 apply (rule_tac x="Member(0,1)" in bexI)
  apply (auto simp add: Un_least_lt_iff)
done

lemma Transset_subset_DPow: "Transset(A) \<Longrightarrow> A \<subseteq> DPow(A)"
apply clarify
apply (simp add: Transset_def)
apply (blast intro: elem_subset_in_DPow)
done

lemma Transset_DPow: "Transset(A) \<Longrightarrow> Transset(DPow(A))"
apply (simp add: Transset_def)
apply (blast intro: elem_subset_in_DPow dest: DPowD)
done

text\<open>Kunen's VI 1.6 (a)\<close>
lemma Transset_Lset: "Transset(Lset(i))"
apply (rule_tac a=i in eps_induct)
apply (subst Lset)
apply (blast intro!: Transset_Union_family Transset_Un Transset_DPow)
done

lemma mem_Lset_imp_subset_Lset: "a \<in> Lset(i) \<Longrightarrow> a \<subseteq> Lset(i)"
apply (insert Transset_Lset)
apply (simp add: Transset_def)
done

subsubsection\<open>Monotonicity\<close>

text\<open>Kunen's VI 1.6 (b)\<close>
lemma Lset_mono [rule_format]:
     "\<forall>j. i<=j \<longrightarrow> Lset(i) \<subseteq> Lset(j)"
proof (induct i rule: eps_induct, intro allI impI)
  fix x j
  assume "\<forall>y\<in>x. \<forall>j. y \<subseteq> j \<longrightarrow> Lset(y) \<subseteq> Lset(j)"
     and "x \<subseteq> j"
  thus "Lset(x) \<subseteq> Lset(j)"
    by (force simp add: Lset [of x] Lset [of j])
qed

text\<open>This version lets us remove the premise \<^term>\<open>Ord(i)\<close> sometimes.\<close>
lemma Lset_mono_mem [rule_format]:
     "\<forall>j. i \<in> j \<longrightarrow> Lset(i) \<subseteq> Lset(j)"
proof (induct i rule: eps_induct, intro allI impI)
  fix x j
  assume "\<forall>y\<in>x. \<forall>j. y \<in> j \<longrightarrow> Lset(y) \<subseteq> Lset(j)"
     and "x \<in> j"
  thus "Lset(x) \<subseteq> Lset(j)"
    by (force simp add: Lset [of j]
              intro!: bexI intro: elem_subset_in_DPow dest: LsetD DPowD)
qed


text\<open>Useful with Reflection to bump up the ordinal\<close>
lemma subset_Lset_ltD: "\<lbrakk>A \<subseteq> Lset(i); i < j\<rbrakk> \<Longrightarrow> A \<subseteq> Lset(j)"
by (blast dest: ltD [THEN Lset_mono_mem])

subsubsection\<open>0, successor and limit equations for Lset\<close>

lemma Lset_0 [simp]: "Lset(0) = 0"
by (subst Lset, blast)

lemma Lset_succ_subset1: "DPow(Lset(i)) \<subseteq> Lset(succ(i))"
by (subst Lset, rule succI1 [THEN RepFunI, THEN Union_upper])

lemma Lset_succ_subset2: "Lset(succ(i)) \<subseteq> DPow(Lset(i))"
apply (subst Lset, rule UN_least)
apply (erule succE)
 apply blast
apply clarify
apply (rule elem_subset_in_DPow)
 apply (subst Lset)
 apply blast
apply (blast intro: dest: DPowD Lset_mono_mem)
done

lemma Lset_succ: "Lset(succ(i)) = DPow(Lset(i))"
by (intro equalityI Lset_succ_subset1 Lset_succ_subset2)

lemma Lset_Union [simp]: "Lset(\<Union>(X)) = (\<Union>y\<in>X. Lset(y))"
apply (subst Lset)
apply (rule equalityI)
 txt\<open>first inclusion\<close>
 apply (rule UN_least)
 apply (erule UnionE)
 apply (rule subset_trans)
  apply (erule_tac [2] UN_upper, subst Lset, erule UN_upper)
txt\<open>opposite inclusion\<close>
apply (rule UN_least)
apply (subst Lset, blast)
done

subsubsection\<open>Lset applied to Limit ordinals\<close>

lemma Limit_Lset_eq:
    "Limit(i) \<Longrightarrow> Lset(i) = (\<Union>y\<in>i. Lset(y))"
by (simp add: Lset_Union [symmetric] Limit_Union_eq)

lemma lt_LsetI: "\<lbrakk>a \<in> Lset(j);  j<i\<rbrakk> \<Longrightarrow> a \<in> Lset(i)"
by (blast dest: Lset_mono [OF le_imp_subset [OF leI]])

lemma Limit_LsetE:
    "\<lbrakk>a \<in> Lset(i);  \<not>R \<Longrightarrow> Limit(i);
        \<And>x. \<lbrakk>x<i;  a \<in> Lset(x)\<rbrakk> \<Longrightarrow> R
\<rbrakk> \<Longrightarrow> R"
apply (rule classical)
apply (rule Limit_Lset_eq [THEN equalityD1, THEN subsetD, THEN UN_E])
  prefer 2 apply assumption
 apply blast
apply (blast intro: ltI  Limit_is_Ord)
done

subsubsection\<open>Basic closure properties\<close>

lemma zero_in_Lset: "y \<in> x \<Longrightarrow> 0 \<in> Lset(x)"
by (subst Lset, blast intro: empty_in_DPow)

lemma notin_Lset: "x \<notin> Lset(x)"
apply (rule_tac a=x in eps_induct)
apply (subst Lset)
apply (blast dest: DPowD)
done


subsection\<open>Constructible Ordinals: Kunen's VI 1.9 (b)\<close>

lemma Ords_of_Lset_eq: "Ord(i) \<Longrightarrow> {x\<in>Lset(i). Ord(x)} = i"
apply (erule trans_induct3)
  apply (simp_all add: Lset_succ Limit_Lset_eq Limit_Union_eq)
txt\<open>The successor case remains.\<close>
apply (rule equalityI)
txt\<open>First inclusion\<close>
 apply clarify
 apply (erule Ord_linear_lt, assumption)
   apply (blast dest: DPow_imp_subset ltD notE [OF notin_Lset])
  apply blast
 apply (blast dest: ltD)
txt\<open>Opposite inclusion, \<^term>\<open>succ(x) \<subseteq> DPow(Lset(x)) \<inter> ON\<close>\<close>
apply auto
txt\<open>Key case:\<close>
  apply (erule subst, rule Ords_in_DPow [OF Transset_Lset])
 apply (blast intro: elem_subset_in_DPow dest: OrdmemD elim: equalityE)
apply (blast intro: Ord_in_Ord)
done


lemma Ord_subset_Lset: "Ord(i) \<Longrightarrow> i \<subseteq> Lset(i)"
by (subst Ords_of_Lset_eq [symmetric], assumption, fast)

lemma Ord_in_Lset: "Ord(i) \<Longrightarrow> i \<in> Lset(succ(i))"
apply (simp add: Lset_succ)
apply (subst Ords_of_Lset_eq [symmetric], assumption,
       rule Ords_in_DPow [OF Transset_Lset])
done

lemma Ord_in_L: "Ord(i) \<Longrightarrow> L(i)"
by (simp add: L_def, blast intro: Ord_in_Lset)

subsubsection\<open>Unions\<close>

lemma Union_in_Lset:
     "X \<in> Lset(i) \<Longrightarrow> \<Union>(X) \<in> Lset(succ(i))"
apply (insert Transset_Lset)
apply (rule LsetI [OF succI1])
apply (simp add: Transset_def DPow_def)
apply (intro conjI, blast)
txt\<open>Now to create the formula \<^term>\<open>\<exists>y. y \<in> X \<and> x \<in> y\<close>\<close>
apply (rule_tac x="Cons(X,Nil)" in bexI)
 apply (rule_tac x="Exists(And(Member(0,2), Member(1,0)))" in bexI)
  apply typecheck
apply (simp add: succ_Un_distrib [symmetric], blast)
done

theorem Union_in_L: "L(X) \<Longrightarrow> L(\<Union>(X))"
by (simp add: L_def, blast dest: Union_in_Lset)

subsubsection\<open>Finite sets and ordered pairs\<close>

lemma singleton_in_Lset: "a \<in> Lset(i) \<Longrightarrow> {a} \<in> Lset(succ(i))"
by (simp add: Lset_succ singleton_in_DPow)

lemma doubleton_in_Lset:
     "\<lbrakk>a \<in> Lset(i);  b \<in> Lset(i)\<rbrakk> \<Longrightarrow> {a,b} \<in> Lset(succ(i))"
by (simp add: Lset_succ empty_in_DPow cons_in_DPow)

lemma Pair_in_Lset:
    "\<lbrakk>a \<in> Lset(i);  b \<in> Lset(i); Ord(i)\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle> \<in> Lset(succ(succ(i)))"
apply (unfold Pair_def)
apply (blast intro: doubleton_in_Lset)
done

lemmas Lset_UnI1 = Un_upper1 [THEN Lset_mono [THEN subsetD]]
lemmas Lset_UnI2 = Un_upper2 [THEN Lset_mono [THEN subsetD]]

text\<open>Hard work is finding a single \<^term>\<open>j \<in> i\<close> such that \<^term>\<open>{a,b} \<subseteq> Lset(j)\<close>\<close>
lemma doubleton_in_LLimit:
    "\<lbrakk>a \<in> Lset(i);  b \<in> Lset(i);  Limit(i)\<rbrakk> \<Longrightarrow> {a,b} \<in> Lset(i)"
apply (erule Limit_LsetE, assumption)
apply (erule Limit_LsetE, assumption)
apply (blast intro: lt_LsetI [OF doubleton_in_Lset]
                    Lset_UnI1 Lset_UnI2 Limit_has_succ Un_least_lt)
done

theorem doubleton_in_L: "\<lbrakk>L(a); L(b)\<rbrakk> \<Longrightarrow> L({a, b})"
apply (simp add: L_def, clarify)
apply (drule Ord2_imp_greater_Limit, assumption)
apply (blast intro: lt_LsetI doubleton_in_LLimit Limit_is_Ord)
done

lemma Pair_in_LLimit:
    "\<lbrakk>a \<in> Lset(i);  b \<in> Lset(i);  Limit(i)\<rbrakk> \<Longrightarrow> \<langle>a,b\<rangle> \<in> Lset(i)"
txt\<open>Infer that a, b occur at ordinals x,xa < i.\<close>
apply (erule Limit_LsetE, assumption)
apply (erule Limit_LsetE, assumption)
txt\<open>Infer that \<^term>\<open>succ(succ(x \<union> xa)) < i\<close>\<close>
apply (blast intro: lt_Ord lt_LsetI [OF Pair_in_Lset]
                    Lset_UnI1 Lset_UnI2 Limit_has_succ Un_least_lt)
done



text\<open>The rank function for the constructible universe\<close>
definition
  lrank :: "i\<Rightarrow>i" where \<comment> \<open>Kunen's definition VI 1.7\<close>
  "lrank(x) \<equiv> \<mu> i. x \<in> Lset(succ(i))"

lemma L_I: "\<lbrakk>x \<in> Lset(i); Ord(i)\<rbrakk> \<Longrightarrow> L(x)"
by (simp add: L_def, blast)

lemma L_D: "L(x) \<Longrightarrow> \<exists>i. Ord(i) \<and> x \<in> Lset(i)"
by (simp add: L_def)

lemma Ord_lrank [simp]: "Ord(lrank(a))"
by (simp add: lrank_def)

lemma Lset_lrank_lt [rule_format]: "Ord(i) \<Longrightarrow> x \<in> Lset(i) \<longrightarrow> lrank(x) < i"
apply (erule trans_induct3)
  apply simp
 apply (simp only: lrank_def)
 apply (blast intro: Least_le)
apply (simp_all add: Limit_Lset_eq)
apply (blast intro: ltI Limit_is_Ord lt_trans)
done

text\<open>Kunen's VI 1.8.  The proof is much harder than the text would
suggest.  For a start, it needs the previous lemma, which is proved by
induction.\<close>
lemma Lset_iff_lrank_lt: "Ord(i) \<Longrightarrow> x \<in> Lset(i) \<longleftrightarrow> L(x) \<and> lrank(x) < i"
apply (simp add: L_def, auto)
 apply (blast intro: Lset_lrank_lt)
 apply (unfold lrank_def)
apply (drule succI1 [THEN Lset_mono_mem, THEN subsetD])
apply (drule_tac P="\<lambda>i. x \<in> Lset(succ(i))" in LeastI, assumption)
apply (blast intro!: le_imp_subset Lset_mono [THEN subsetD])
done

lemma Lset_succ_lrank_iff [simp]: "x \<in> Lset(succ(lrank(x))) \<longleftrightarrow> L(x)"
by (simp add: Lset_iff_lrank_lt)

text\<open>Kunen's VI 1.9 (a)\<close>
lemma lrank_of_Ord: "Ord(i) \<Longrightarrow> lrank(i) = i"
apply (unfold lrank_def)
apply (rule Least_equality)
  apply (erule Ord_in_Lset)
 apply assumption
apply (insert notin_Lset [of i])
apply (blast intro!: le_imp_subset Lset_mono [THEN subsetD])
done


text\<open>This is lrank(lrank(a)) = lrank(a)\<close>
declare Ord_lrank [THEN lrank_of_Ord, simp]

text\<open>Kunen's VI 1.10\<close>
lemma Lset_in_Lset_succ: "Lset(i) \<in> Lset(succ(i))"
apply (simp add: Lset_succ DPow_def)
apply (rule_tac x=Nil in bexI)
 apply (rule_tac x="Equal(0,0)" in bexI)
apply auto
done

lemma lrank_Lset: "Ord(i) \<Longrightarrow> lrank(Lset(i)) = i"
apply (unfold lrank_def)
apply (rule Least_equality)
  apply (rule Lset_in_Lset_succ)
 apply assumption
apply clarify
apply (subgoal_tac "Lset(succ(ia)) \<subseteq> Lset(i)")
 apply (blast dest: mem_irrefl)
apply (blast intro!: le_imp_subset Lset_mono)
done

text\<open>Kunen's VI 1.11\<close>
lemma Lset_subset_Vset: "Ord(i) \<Longrightarrow> Lset(i) \<subseteq> Vset(i)"
apply (erule trans_induct)
apply (subst Lset)
apply (subst Vset)
apply (rule UN_mono [OF subset_refl])
apply (rule subset_trans [OF DPow_subset_Pow])
apply (rule Pow_mono, blast)
done

text\<open>Kunen's VI 1.12\<close>
lemma Lset_subset_Vset': "i \<in> nat \<Longrightarrow> Lset(i) = Vset(i)"
apply (erule nat_induct)
 apply (simp add: Vfrom_0)
apply (simp add: Lset_succ Vset_succ Finite_Vset Finite_DPow_eq_Pow)
done

text\<open>Every set of constructible sets is included in some \<^term>\<open>Lset\<close>\<close>
lemma subset_Lset:
     "(\<forall>x\<in>A. L(x)) \<Longrightarrow> \<exists>i. Ord(i) \<and> A \<subseteq> Lset(i)"
by (rule_tac x = "\<Union>x\<in>A. succ(lrank(x))" in exI, force)

lemma subset_LsetE:
     "\<lbrakk>\<forall>x\<in>A. L(x);
        \<And>i. \<lbrakk>Ord(i); A \<subseteq> Lset(i)\<rbrakk> \<Longrightarrow> P\<rbrakk>
      \<Longrightarrow> P"
by (blast dest: subset_Lset)

subsubsection\<open>For L to satisfy the Powerset axiom\<close>

lemma LPow_env_typing:
    "\<lbrakk>y \<in> Lset(i); Ord(i); y \<subseteq> X\<rbrakk>
     \<Longrightarrow> \<exists>z \<in> Pow(X). y \<in> Lset(succ(lrank(z)))"
by (auto intro: L_I iff: Lset_succ_lrank_iff)

lemma LPow_in_Lset:
     "\<lbrakk>X \<in> Lset(i); Ord(i)\<rbrakk> \<Longrightarrow> \<exists>j. Ord(j) \<and> {y \<in> Pow(X). L(y)} \<in> Lset(j)"
apply (rule_tac x="succ(\<Union>y \<in> Pow(X). succ(lrank(y)))" in exI)
apply simp
apply (rule LsetI [OF succI1])
apply (simp add: DPow_def)
apply (intro conjI, clarify)
 apply (rule_tac a=x in UN_I, simp+)
txt\<open>Now to create the formula \<^term>\<open>y \<subseteq> X\<close>\<close>
apply (rule_tac x="Cons(X,Nil)" in bexI)
 apply (rule_tac x="subset_fm(0,1)" in bexI)
  apply typecheck
 apply (rule conjI)
apply (simp add: succ_Un_distrib [symmetric])
apply (rule equality_iffI)
apply (simp add: Transset_UN [OF Transset_Lset] LPow_env_typing)
apply (auto intro: L_I iff: Lset_succ_lrank_iff)
done

theorem LPow_in_L: "L(X) \<Longrightarrow> L({y \<in> Pow(X). L(y)})"
by (blast intro: L_I dest: L_D LPow_in_Lset)


subsection\<open>Eliminating \<^term>\<open>arity\<close> from the Definition of \<^term>\<open>Lset\<close>\<close>

lemma nth_zero_eq_0: "n \<in> nat \<Longrightarrow> nth(n,[0]) = 0"
by (induct_tac n, auto)

lemma sats_app_0_iff [rule_format]:
  "\<lbrakk>p \<in> formula; 0 \<in> A\<rbrakk>
   \<Longrightarrow> \<forall>env \<in> list(A). sats(A,p, env@[0]) \<longleftrightarrow> sats(A,p,env)"
apply (induct_tac p)
apply (simp_all del: app_Cons add: app_Cons [symmetric]
                add: nth_zero_eq_0 nth_append not_lt_iff_le nth_eq_0)
done

lemma sats_app_zeroes_iff:
  "\<lbrakk>p \<in> formula; 0 \<in> A; env \<in> list(A); n \<in> nat\<rbrakk>
   \<Longrightarrow> sats(A,p,env @ repeat(0,n)) \<longleftrightarrow> sats(A,p,env)"
apply (induct_tac n, simp)
apply (simp del: repeat.simps
            add: repeat_succ_app sats_app_0_iff app_assoc [symmetric])
done

lemma exists_bigger_env:
  "\<lbrakk>p \<in> formula; 0 \<in> A; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> \<exists>env' \<in> list(A). arity(p) \<le> succ(length(env')) \<and>
              (\<forall>a\<in>A. sats(A,p,Cons(a,env')) \<longleftrightarrow> sats(A,p,Cons(a,env)))"
apply (rule_tac x="env @ repeat(0,arity(p))" in bexI)
apply (simp del: app_Cons add: app_Cons [symmetric]
            add: length_repeat sats_app_zeroes_iff, typecheck)
done


text\<open>A simpler version of \<^term>\<open>DPow\<close>: no arity check!\<close>
definition
  DPow' :: "i \<Rightarrow> i" where
  "DPow'(A) \<equiv> {X \<in> Pow(A).
                \<exists>env \<in> list(A). \<exists>p \<in> formula.
                    X = {x\<in>A. sats(A, p, Cons(x,env))}}"

lemma DPow_subset_DPow': "DPow(A) \<subseteq> DPow'(A)"
by (simp add: DPow_def DPow'_def, blast)

lemma DPow'_0: "DPow'(0) = {0}"
by (auto simp add: DPow'_def)

lemma DPow'_subset_DPow: "0 \<in> A \<Longrightarrow> DPow'(A) \<subseteq> DPow(A)"
apply (auto simp add: DPow'_def DPow_def)
apply (frule exists_bigger_env, assumption+, force)
done

lemma DPow_eq_DPow': "Transset(A) \<Longrightarrow> DPow(A) = DPow'(A)"
apply (drule Transset_0_disj)
apply (erule disjE)
 apply (simp add: DPow'_0 Finite_DPow_eq_Pow)
apply (rule equalityI)
 apply (rule DPow_subset_DPow')
apply (erule DPow'_subset_DPow)
done

text\<open>And thus we can relativize \<^term>\<open>Lset\<close> without bothering with
      \<^term>\<open>arity\<close> and \<^term>\<open>length\<close>\<close>
lemma Lset_eq_transrec_DPow': "Lset(i) = transrec(i, \<lambda>x f. \<Union>y\<in>x. DPow'(f`y))"
apply (rule_tac a=i in eps_induct)
apply (subst Lset)
apply (subst transrec)
apply (simp only: DPow_eq_DPow' [OF Transset_Lset], simp)
done

text\<open>With this rule we can specify \<^term>\<open>p\<close> later and don't worry about
      arities at all!\<close>
lemma DPow_LsetI [rule_format]:
  "\<lbrakk>\<forall>x\<in>Lset(i). P(x) \<longleftrightarrow> sats(Lset(i), p, Cons(x,env));
     env \<in> list(Lset(i));  p \<in> formula\<rbrakk>
   \<Longrightarrow> {x\<in>Lset(i). P(x)} \<in> DPow(Lset(i))"
by (simp add: DPow_eq_DPow' [OF Transset_Lset] DPow'_def, blast)

end
