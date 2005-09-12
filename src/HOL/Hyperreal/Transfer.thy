(*  Title       : HOL/Hyperreal/Transfer.thy
    ID          : $Id$
    Author      : Brian Huffman
*)

header {* Transfer Principle *}

theory Transfer
imports StarType
uses ("transfer.ML")
begin

subsection {* Starting the transfer proof *}

text {*
  A transfer theorem asserts an equivalence @{prop "P \<equiv> P'"}
  between two related propositions. Proposition @{term P} may
  refer to constants having star types, like @{typ "'a star"}.
  Proposition @{term P'} is syntactically similar, but only
  refers to ordinary types (i.e. @{term P'} is the un-starred
  version of @{term P}).
*}

text {* This introduction rule starts each transfer proof. *}

lemma transfer_start:
  "P \<equiv> {n. Q} \<in> \<U> \<Longrightarrow> Trueprop P \<equiv> Trueprop Q"
by (subgoal_tac "P \<equiv> Q", simp, simp add: atomize_eq)

use "transfer.ML"
setup Transfer.setup

declare Ifun_defs [transfer_unfold]
declare Iset_of_def [transfer_unfold]

subsection {* Transfer introduction rules *}

text {*
  The proof of a transfer theorem is completely syntax-directed.
  At each step in the proof, the top-level connective determines
  which introduction rule to apply. Each argument to the top-level
  connective generates a new subgoal.
*}

text {*
  Subgoals in a transfer proof always have the form of an equivalence.
  The left side can be any term, and may contain references to star
  types. The form of the right side depends on its type. At type
  @{typ bool} it takes the form @{term "{n. P n} \<in> \<U>"}. At type
  @{typ "'a star"} it takes the form @{term "star_n (\<lambda>n. X n)"}. At type
  @{typ "'a star set"} it looks like @{term "Iset (star_n (\<lambda>n. A n))"}.
  And at type @{typ "'a star \<Rightarrow> 'b star"} it has the form
  @{term "Ifun (star_n (\<lambda>n. F n))"}.
*}

subsubsection {* Boolean operators *}

lemma transfer_not:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>\<rbrakk> \<Longrightarrow> \<not> p \<equiv> {n. \<not> P n} \<in> \<U>"
by (simp only: ultrafilter.Collect_not [OF ultrafilter_FUFNat])

lemma transfer_conj:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<and> q \<equiv> {n. P n \<and> Q n} \<in> \<U>"
by (simp only: filter.Collect_conj [OF filter_FUFNat])

lemma transfer_disj:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<or> q \<equiv> {n. P n \<or> Q n} \<in> \<U>"
by (simp only: ultrafilter.Collect_disj [OF ultrafilter_FUFNat])

lemma transfer_imp:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<longrightarrow> q \<equiv> {n. P n \<longrightarrow> Q n} \<in> \<U>"
by (simp only: imp_conv_disj transfer_disj transfer_not)

lemma transfer_iff:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p = q \<equiv> {n. P n = Q n} \<in> \<U>"
by (simp only: iff_conv_conj_imp transfer_conj transfer_imp)

lemma transfer_if_bool:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; x \<equiv> {n. X n} \<in> \<U>; y \<equiv> {n. Y n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> (if p then x else y) \<equiv> {n. if P n then X n else Y n} \<in> \<U>"
by (simp only: if_bool_eq_conj transfer_conj transfer_imp transfer_not)

subsubsection {* Equals, If *}

lemma transfer_eq:
  "\<lbrakk>x \<equiv> star_n X; y \<equiv> star_n Y\<rbrakk> \<Longrightarrow> x = y \<equiv> {n. X n = Y n} \<in> \<U>"
by (simp only: star_n_eq_iff)

lemma transfer_if:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; x \<equiv> star_n X; y \<equiv> star_n Y\<rbrakk>
    \<Longrightarrow> (if p then x else y) \<equiv> star_n (\<lambda>n. if P n then X n else Y n)"
apply (rule eq_reflection)
apply (auto simp add: star_n_eq_iff transfer_not elim!: ultra)
done

subsubsection {* Quantifiers *}

lemma transfer_ex:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>x::'a star. p x \<equiv> {n. \<exists>x. P n x} \<in> \<U>"
by (simp only: ex_star_eq filter.Collect_ex [OF filter_FUFNat])

lemma transfer_all:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<forall>x::'a star. p x \<equiv> {n. \<forall>x. P n x} \<in> \<U>"
by (simp only: all_star_eq ultrafilter.Collect_all [OF ultrafilter_FUFNat])

lemma transfer_ex1:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>!x. p x \<equiv> {n. \<exists>!x. P n x} \<in> \<U>"
by (simp only: Ex1_def transfer_ex transfer_conj
   transfer_all transfer_imp transfer_eq)

subsubsection {* Functions *}

lemma transfer_Ifun:
  "\<lbrakk>f \<equiv> star_n F; x \<equiv> star_n X\<rbrakk>
    \<Longrightarrow> f \<star> x \<equiv> star_n (\<lambda>n. F n (X n))"
by (simp only: Ifun_star_n)

lemma transfer_fun_eq:
  "\<lbrakk>\<And>X. f (star_n X) = g (star_n X) 
    \<equiv> {n. F n (X n) = G n (X n)} \<in> \<U>\<rbrakk>
      \<Longrightarrow> f = g \<equiv> {n. F n = G n} \<in> \<U>"
by (simp only: expand_fun_eq transfer_all)

subsubsection {* Sets *}

lemma transfer_Iset:
  "\<lbrakk>a \<equiv> star_n A\<rbrakk> \<Longrightarrow> Iset a \<equiv> Iset (star_n (\<lambda>n. A n))"
by simp

lemma transfer_Collect:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> Collect p \<equiv> Iset (star_n (\<lambda>n. Collect (P n)))"
by (simp add: atomize_eq expand_set_eq all_star_eq Iset_star_n)

lemma transfer_mem:
  "\<lbrakk>x \<equiv> star_n X; a \<equiv> Iset (star_n A)\<rbrakk>
    \<Longrightarrow> x \<in> a \<equiv> {n. X n \<in> A n} \<in> \<U>"
by (simp only: Iset_star_n)

lemma transfer_set_eq:
  "\<lbrakk>a \<equiv> Iset (star_n A); b \<equiv> Iset (star_n B)\<rbrakk>
    \<Longrightarrow> a = b \<equiv> {n. A n = B n} \<in> \<U>"
by (simp only: expand_set_eq transfer_all transfer_iff transfer_mem)

lemma transfer_ball:
  "\<lbrakk>a \<equiv> Iset (star_n A); \<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>a. p x \<equiv> {n. \<forall>x\<in>A n. P n x} \<in> \<U>"
by (simp only: Ball_def transfer_all transfer_imp transfer_mem)

lemma transfer_bex:
  "\<lbrakk>a \<equiv> Iset (star_n A); \<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>a. p x \<equiv> {n. \<exists>x\<in>A n. P n x} \<in> \<U>"
by (simp only: Bex_def transfer_ex transfer_conj transfer_mem)


subsubsection {* Miscellaneous *}

lemma transfer_unstar:
  "p \<equiv> star_n P \<Longrightarrow> unstar p \<equiv> {n. P n} \<in> \<U>"
by (simp only: unstar_star_n)

lemma transfer_star_of: "star_of x \<equiv> star_n (\<lambda>n. x)"
by (rule star_of_def)

lemma transfer_star_n: "star_n X \<equiv> star_n (\<lambda>n. X n)"
by (rule reflexive)

lemma transfer_bool: "p \<equiv> {n. p} \<in> \<U>"
by (simp add: atomize_eq)

lemmas transfer_intros [transfer_intro] =
  transfer_star_n
  transfer_star_of
  transfer_Ifun
  transfer_fun_eq

  transfer_not
  transfer_conj
  transfer_disj
  transfer_imp
  transfer_iff
  transfer_if_bool

  transfer_all
  transfer_ex

  transfer_unstar
  transfer_bool
  transfer_eq
  transfer_if

  transfer_set_eq
  transfer_Iset
  transfer_Collect
  transfer_mem
  transfer_ball
  transfer_bex

text {* Sample theorems *}

lemma Ifun_inject: "\<And>f g. (Ifun f = Ifun g) = (f = g)"
by transfer (rule refl)

lemma unstar_inject: "\<And>x y. (unstar x = unstar y) = (x = y)"
by transfer (rule refl)

lemma Iset_inject: "\<And>A B. (Iset A = Iset B) = (A = B)"
by transfer (rule refl)

end
