(*  Title       : HOL/Hyperreal/StarDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot and Brian Huffman
*)

header {* Construction of Star Types Using Ultrafilters *}

theory StarDef
imports Filter
uses ("transfer.ML")
begin

subsection {* A Free Ultrafilter over the Naturals *}

constdefs
  FreeUltrafilterNat :: "nat set set"  ("\<U>")
    "\<U> \<equiv> SOME U. freeultrafilter U"

lemma freeultrafilter_FUFNat: "freeultrafilter \<U>"
 apply (unfold FreeUltrafilterNat_def)
 apply (rule someI_ex)
 apply (rule freeultrafilter_Ex)
 apply (rule nat_infinite)
done

interpretation FUFNat: freeultrafilter [FreeUltrafilterNat]
by (cut_tac [!] freeultrafilter_FUFNat, simp_all add: freeultrafilter_def)

text {* This rule takes the place of the old ultra tactic *}

lemma ultra:
  "\<lbrakk>{n. P n} \<in> \<U>; {n. P n \<longrightarrow> Q n} \<in> \<U>\<rbrakk> \<Longrightarrow> {n. Q n} \<in> \<U>"
by (simp add: Collect_imp_eq FUFNat.F.Un_iff FUFNat.F.Compl_iff)


subsection {* Definition of @{text star} type constructor *}

constdefs
  starrel :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"
    "starrel \<equiv> {(X,Y). {n. X n = Y n} \<in> \<U>}"

typedef 'a star = "(UNIV :: (nat \<Rightarrow> 'a) set) // starrel"
by (auto intro: quotientI)

constdefs
  star_n :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a star"
  "star_n X \<equiv> Abs_star (starrel `` {X})"

theorem star_cases [case_names star_n, cases type: star]:
  "(\<And>X. x = star_n X \<Longrightarrow> P) \<Longrightarrow> P"
by (cases x, unfold star_n_def star_def, erule quotientE, fast)

lemma all_star_eq: "(\<forall>x. P x) = (\<forall>X. P (star_n X))"
by (auto, rule_tac x=x in star_cases, simp)

lemma ex_star_eq: "(\<exists>x. P x) = (\<exists>X. P (star_n X))"
by (auto, rule_tac x=x in star_cases, auto)

text {* Proving that @{term starrel} is an equivalence relation *}

lemma starrel_iff [iff]: "((X,Y) \<in> starrel) = ({n. X n = Y n} \<in> \<U>)"
by (simp add: starrel_def)

lemma equiv_starrel: "equiv UNIV starrel"
proof (rule equiv.intro)
  show "reflexive starrel" by (simp add: refl_def)
  show "sym starrel" by (simp add: sym_def eq_commute)
  show "trans starrel" by (auto intro: transI elim!: ultra)
qed

lemmas equiv_starrel_iff =
  eq_equiv_class_iff [OF equiv_starrel UNIV_I UNIV_I]

lemma starrel_in_star: "starrel``{x} \<in> star"
by (simp add: star_def quotientI)

lemma star_n_eq_iff: "(star_n X = star_n Y) = ({n. X n = Y n} \<in> \<U>)"
by (simp add: star_n_def Abs_star_inject starrel_in_star equiv_starrel_iff)


subsection {* Transfer principle *}

text {* This introduction rule starts each transfer proof. *}
lemma transfer_start:
  "P \<equiv> {n. Q} \<in> \<U> \<Longrightarrow> Trueprop P \<equiv> Trueprop Q"
by (subgoal_tac "P \<equiv> Q", simp, simp add: atomize_eq)

text {*Initialize transfer tactic.*}
use "transfer.ML"
setup Transfer.setup

text {* Transfer introduction rules. *}

lemma transfer_ex [transfer_intro]:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>x::'a star. p x \<equiv> {n. \<exists>x. P n x} \<in> \<U>"
by (simp only: ex_star_eq FUFNat.F.Collect_ex)

lemma transfer_all [transfer_intro]:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<forall>x::'a star. p x \<equiv> {n. \<forall>x. P n x} \<in> \<U>"
by (simp only: all_star_eq FUFNat.F.Collect_all)

lemma transfer_not [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>\<rbrakk> \<Longrightarrow> \<not> p \<equiv> {n. \<not> P n} \<in> \<U>"
by (simp only: FUFNat.F.Collect_not)

lemma transfer_conj [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<and> q \<equiv> {n. P n \<and> Q n} \<in> \<U>"
by (simp only: FUFNat.F.Collect_conj)

lemma transfer_disj [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<or> q \<equiv> {n. P n \<or> Q n} \<in> \<U>"
by (simp only: FUFNat.F.Collect_disj)

lemma transfer_imp [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<longrightarrow> q \<equiv> {n. P n \<longrightarrow> Q n} \<in> \<U>"
by (simp only: imp_conv_disj transfer_disj transfer_not)

lemma transfer_iff [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p = q \<equiv> {n. P n = Q n} \<in> \<U>"
by (simp only: iff_conv_conj_imp transfer_conj transfer_imp)

lemma transfer_if_bool [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; x \<equiv> {n. X n} \<in> \<U>; y \<equiv> {n. Y n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> (if p then x else y) \<equiv> {n. if P n then X n else Y n} \<in> \<U>"
by (simp only: if_bool_eq_conj transfer_conj transfer_imp transfer_not)

lemma transfer_eq [transfer_intro]:
  "\<lbrakk>x \<equiv> star_n X; y \<equiv> star_n Y\<rbrakk> \<Longrightarrow> x = y \<equiv> {n. X n = Y n} \<in> \<U>"
by (simp only: star_n_eq_iff)

lemma transfer_if [transfer_intro]:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; x \<equiv> star_n X; y \<equiv> star_n Y\<rbrakk>
    \<Longrightarrow> (if p then x else y) \<equiv> star_n (\<lambda>n. if P n then X n else Y n)"
apply (rule eq_reflection)
apply (auto simp add: star_n_eq_iff transfer_not elim!: ultra)
done

lemma transfer_fun_eq [transfer_intro]:
  "\<lbrakk>\<And>X. f (star_n X) = g (star_n X) 
    \<equiv> {n. F n (X n) = G n (X n)} \<in> \<U>\<rbrakk>
      \<Longrightarrow> f = g \<equiv> {n. F n = G n} \<in> \<U>"
by (simp only: expand_fun_eq transfer_all)

lemma transfer_star_n [transfer_intro]: "star_n X \<equiv> star_n (\<lambda>n. X n)"
by (rule reflexive)

lemma transfer_bool [transfer_intro]: "p \<equiv> {n. p} \<in> \<U>"
by (simp add: atomize_eq)


subsection {* Standard elements *}

constdefs
  star_of :: "'a \<Rightarrow> 'a star"
  "star_of x \<equiv> star_n (\<lambda>n. x)"

text {* Transfer tactic should remove occurrences of @{term star_of} *}
setup {* [Transfer.add_const "StarDef.star_of"] *}
declare star_of_def [transfer_intro]

lemma star_of_inject: "(star_of x = star_of y) = (x = y)"
by (transfer, rule refl)


subsection {* Internal functions *}

constdefs
  Ifun :: "('a \<Rightarrow> 'b) star \<Rightarrow> 'a star \<Rightarrow> 'b star" ("_ \<star> _" [300,301] 300)
  "Ifun f \<equiv> \<lambda>x. Abs_star
       (\<Union>F\<in>Rep_star f. \<Union>X\<in>Rep_star x. starrel``{\<lambda>n. F n (X n)})"

lemma Ifun_congruent2:
  "(\<lambda>F X. starrel``{\<lambda>n. F n (X n)}) respects2 starrel"
by (auto simp add: congruent2_def equiv_starrel_iff elim!: ultra)

lemma Ifun_star_n: "star_n F \<star> star_n X = star_n (\<lambda>n. F n (X n))"
by (simp add: Ifun_def star_n_def Abs_star_inverse starrel_in_star
    UN_equiv_class2 [OF equiv_starrel equiv_starrel Ifun_congruent2])

text {* Transfer tactic should remove occurrences of @{term Ifun} *}
setup {* [Transfer.add_const "StarDef.Ifun"] *}

lemma transfer_Ifun [transfer_intro]:
  "\<lbrakk>f \<equiv> star_n F; x \<equiv> star_n X\<rbrakk> \<Longrightarrow> f \<star> x \<equiv> star_n (\<lambda>n. F n (X n))"
by (simp only: Ifun_star_n)

lemma Ifun_star_of [simp]: "star_of f \<star> star_of x = star_of (f x)"
by (transfer, rule refl)

text {* Nonstandard extensions of functions *}

constdefs
  starfun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a star \<Rightarrow> 'b star)"
    ("*f* _" [80] 80)
  "starfun f \<equiv> \<lambda>x. star_of f \<star> x"

  starfun2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a star \<Rightarrow> 'b star \<Rightarrow> 'c star)"
    ("*f2* _" [80] 80)
  "starfun2 f \<equiv> \<lambda>x y. star_of f \<star> x \<star> y"

declare starfun_def [transfer_unfold]
declare starfun2_def [transfer_unfold]

lemma starfun_star_n: "( *f* f) (star_n X) = star_n (\<lambda>n. f (X n))"
by (simp only: starfun_def star_of_def Ifun_star_n)

lemma starfun2_star_n:
  "( *f2* f) (star_n X) (star_n Y) = star_n (\<lambda>n. f (X n) (Y n))"
by (simp only: starfun2_def star_of_def Ifun_star_n)

lemma starfun_star_of [simp]: "( *f* f) (star_of x) = star_of (f x)"
by (transfer, rule refl)

lemma starfun2_star_of [simp]: "( *f2* f) (star_of x) = *f* f x"
by (transfer, rule refl)


subsection {* Internal predicates *}

constdefs
  unstar :: "bool star \<Rightarrow> bool"
  "unstar b \<equiv> b = star_of True"

lemma unstar_star_n: "unstar (star_n P) = ({n. P n} \<in> \<U>)"
by (simp add: unstar_def star_of_def star_n_eq_iff)

lemma unstar_star_of [simp]: "unstar (star_of p) = p"
by (simp add: unstar_def star_of_inject)

text {* Transfer tactic should remove occurrences of @{term unstar} *}
setup {* [Transfer.add_const "StarDef.unstar"] *}

lemma transfer_unstar [transfer_intro]:
  "p \<equiv> star_n P \<Longrightarrow> unstar p \<equiv> {n. P n} \<in> \<U>"
by (simp only: unstar_star_n)

constdefs
  starP :: "('a \<Rightarrow> bool) \<Rightarrow> 'a star \<Rightarrow> bool"
    ("*p* _" [80] 80)
  "*p* P \<equiv> \<lambda>x. unstar (star_of P \<star> x)"

  starP2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a star \<Rightarrow> 'b star \<Rightarrow> bool"
    ("*p2* _" [80] 80)
  "*p2* P \<equiv> \<lambda>x y. unstar (star_of P \<star> x \<star> y)"

declare starP_def [transfer_unfold]
declare starP2_def [transfer_unfold]

lemma starP_star_n: "( *p* P) (star_n X) = ({n. P (X n)} \<in> \<U>)"
by (simp only: starP_def star_of_def Ifun_star_n unstar_star_n)

lemma starP2_star_n:
  "( *p2* P) (star_n X) (star_n Y) = ({n. P (X n) (Y n)} \<in> \<U>)"
by (simp only: starP2_def star_of_def Ifun_star_n unstar_star_n)

lemma starP_star_of [simp]: "( *p* P) (star_of x) = P x"
by (transfer, rule refl)

lemma starP2_star_of [simp]: "( *p2* P) (star_of x) = *p* P x"
by (transfer, rule refl)


subsection {* Internal sets *}

constdefs
  Iset :: "'a set star \<Rightarrow> 'a star set"
  "Iset A \<equiv> {x. ( *p2* op \<in>) x A}"

lemma Iset_star_n:
  "(star_n X \<in> Iset (star_n A)) = ({n. X n \<in> A n} \<in> \<U>)"
by (simp add: Iset_def starP2_star_n)

text {* Transfer tactic should remove occurrences of @{term Iset} *}
setup {* [Transfer.add_const "StarDef.Iset"] *}

lemma transfer_mem [transfer_intro]:
  "\<lbrakk>x \<equiv> star_n X; a \<equiv> Iset (star_n A)\<rbrakk>
    \<Longrightarrow> x \<in> a \<equiv> {n. X n \<in> A n} \<in> \<U>"
by (simp only: Iset_star_n)

lemma transfer_Collect [transfer_intro]:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> Collect p \<equiv> Iset (star_n (\<lambda>n. Collect (P n)))"
by (simp add: atomize_eq expand_set_eq all_star_eq Iset_star_n)

lemma transfer_set_eq [transfer_intro]:
  "\<lbrakk>a \<equiv> Iset (star_n A); b \<equiv> Iset (star_n B)\<rbrakk>
    \<Longrightarrow> a = b \<equiv> {n. A n = B n} \<in> \<U>"
by (simp only: expand_set_eq transfer_all transfer_iff transfer_mem)

lemma transfer_ball [transfer_intro]:
  "\<lbrakk>a \<equiv> Iset (star_n A); \<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>a. p x \<equiv> {n. \<forall>x\<in>A n. P n x} \<in> \<U>"
by (simp only: Ball_def transfer_all transfer_imp transfer_mem)

lemma transfer_bex [transfer_intro]:
  "\<lbrakk>a \<equiv> Iset (star_n A); \<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>a. p x \<equiv> {n. \<exists>x\<in>A n. P n x} \<in> \<U>"
by (simp only: Bex_def transfer_ex transfer_conj transfer_mem)

lemma transfer_Iset [transfer_intro]:
  "\<lbrakk>a \<equiv> star_n A\<rbrakk> \<Longrightarrow> Iset a \<equiv> Iset (star_n (\<lambda>n. A n))"
by simp

text {* Nonstandard extensions of sets. *}
constdefs
  starset :: "'a set \<Rightarrow> 'a star set" ("*s* _" [80] 80)
  "starset A \<equiv> Iset (star_of A)"

declare starset_def [transfer_unfold]

lemma starset_mem: "(star_of x \<in> *s* A) = (x \<in> A)"
by (transfer, rule refl)

lemma starset_UNIV: "*s* (UNIV::'a set) = (UNIV::'a star set)"
by (transfer UNIV_def, rule refl)

lemma starset_empty: "*s* {} = {}"
by (transfer empty_def, rule refl)

lemma starset_insert: "*s* (insert x A) = insert (star_of x) ( *s* A)"
by (transfer insert_def Un_def, rule refl)

lemma starset_Un: "*s* (A \<union> B) = *s* A \<union> *s* B"
by (transfer Un_def, rule refl)

lemma starset_Int: "*s* (A \<inter> B) = *s* A \<inter> *s* B"
by (transfer Int_def, rule refl)

lemma starset_Compl: "*s* -A = -( *s* A)"
by (transfer Compl_def, rule refl)

lemma starset_diff: "*s* (A - B) = *s* A - *s* B"
by (transfer set_diff_def, rule refl)

lemma starset_image: "*s* (f ` A) = ( *f* f) ` ( *s* A)"
by (transfer image_def, rule refl)

lemma starset_vimage: "*s* (f -` A) = ( *f* f) -` ( *s* A)"
by (transfer vimage_def, rule refl)

lemma starset_subset: "( *s* A \<subseteq> *s* B) = (A \<subseteq> B)"
by (transfer subset_def, rule refl)

lemma starset_eq: "( *s* A = *s* B) = (A = B)"
by (transfer, rule refl)

lemmas starset_simps [simp] =
  starset_mem     starset_UNIV
  starset_empty   starset_insert
  starset_Un      starset_Int
  starset_Compl   starset_diff
  starset_image   starset_vimage
  starset_subset  starset_eq

end
