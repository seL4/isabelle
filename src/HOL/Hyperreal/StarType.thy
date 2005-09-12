(*  Title       : HOL/Hyperreal/StarType.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot and Brian Huffman
*)

header {* Construction of Star Types Using Ultrafilters *}

theory StarType
imports Filter
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

lemmas ultrafilter_FUFNat =
  freeultrafilter_FUFNat [THEN freeultrafilter.ultrafilter]

lemmas filter_FUFNat =
  freeultrafilter_FUFNat [THEN freeultrafilter.filter]

lemmas FUFNat_empty [iff] =
  filter_FUFNat [THEN filter.empty]

lemmas FUFNat_UNIV [iff] =
  filter_FUFNat [THEN filter.UNIV]

text {* This rule takes the place of the old ultra tactic *}

lemma ultra:
  "\<lbrakk>{n. P n} \<in> \<U>; {n. P n \<longrightarrow> Q n} \<in> \<U>\<rbrakk> \<Longrightarrow> {n. Q n} \<in> \<U>"
by (simp add: Collect_imp_eq
    ultrafilter_FUFNat [THEN ultrafilter.Un_iff]
    ultrafilter_FUFNat [THEN ultrafilter.Compl_iff])


subsection {* Definition of @{text star} type constructor *}

constdefs
  starrel :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"
    "starrel \<equiv> {(X,Y). {n. X n = Y n} \<in> \<U>}"

typedef 'a star = "(UNIV :: (nat \<Rightarrow> 'a) set) // starrel"
by (auto intro: quotientI)

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
  -- {* @{term "(starrel `` {x} = starrel `` {y}) = ((x,y) \<in> starrel)"} *}

lemma starrel_in_star: "starrel``{x} \<in> star"
by (simp add: star_def starrel_def quotient_def, fast)

lemma eq_Abs_star:
  "(\<And>x. z = Abs_star (starrel``{x}) \<Longrightarrow> P) \<Longrightarrow> P"
 apply (rule_tac x=z in Abs_star_cases)
 apply (unfold star_def)
 apply (erule quotientE)
 apply simp
done


subsection {* Constructors for type @{typ "'a star"} *}

constdefs
  star_n :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a star"
  "star_n X \<equiv> Abs_star (starrel `` {X})"

  star_of :: "'a \<Rightarrow> 'a star"
  "star_of x \<equiv> star_n (\<lambda>n. x)"

theorem star_cases [case_names star_n, cases type: star]:
  "(\<And>X. x = star_n X \<Longrightarrow> P) \<Longrightarrow> P"
by (unfold star_n_def, rule eq_Abs_star[of x], blast)

lemma all_star_eq: "(\<forall>x. P x) = (\<forall>X. P (star_n X))"
by (auto, rule_tac x=x in star_cases, simp)

lemma ex_star_eq: "(\<exists>x. P x) = (\<exists>X. P (star_n X))"
by (auto, rule_tac x=x in star_cases, auto)

lemma star_n_eq_iff: "(star_n X = star_n Y) = ({n. X n = Y n} \<in> \<U>)"
 apply (unfold star_n_def)
 apply (simp add: Abs_star_inject starrel_in_star equiv_starrel_iff)
done

lemma star_of_inject: "(star_of x = star_of y) = (x = y)"
by (simp add: star_of_def star_n_eq_iff)


subsection {* Internal functions *}

constdefs
  Ifun :: "('a \<Rightarrow> 'b) star \<Rightarrow> 'a star \<Rightarrow> 'b star" ("_ \<star> _" [300,301] 300)
  "Ifun f \<equiv> \<lambda>x. Abs_star
       (\<Union>F\<in>Rep_star f. \<Union>X\<in>Rep_star x. starrel``{\<lambda>n. F n (X n)})"

lemma Ifun_star_n: "star_n F \<star> star_n X = star_n (\<lambda>n. F n (X n))"
 apply (unfold Ifun_def star_n_def)
 apply (simp add: Abs_star_inverse starrel_in_star)
 apply (rule_tac f=Abs_star in arg_cong)
 apply safe
  apply (erule ultra)+
  apply simp
 apply force
done

lemma Ifun [simp]: "star_of f \<star> star_of x = star_of (f x)"
by (simp only: star_of_def Ifun_star_n)


subsection {* Testing lifted booleans *}

constdefs
  unstar :: "bool star \<Rightarrow> bool"
  "unstar b \<equiv> b = star_of True"

lemma unstar_star_n: "unstar (star_n P) = ({n. P n} \<in> \<U>)"
by (simp add: unstar_def star_of_def star_n_eq_iff)

lemma unstar [simp]: "unstar (star_of p) = p"
by (simp add: unstar_def star_of_inject)


subsection {* Internal functions and predicates *}

constdefs
  Ifun_of :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a star \<Rightarrow> 'b star)"
  "Ifun_of f \<equiv> Ifun (star_of f)"

  Ifun2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) star \<Rightarrow> ('a star \<Rightarrow> 'b star \<Rightarrow> 'c star)"
  "Ifun2 f \<equiv> \<lambda>x y. f \<star> x \<star> y"

  Ifun2_of :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a star \<Rightarrow> 'b star \<Rightarrow> 'c star)"
  "Ifun2_of f \<equiv> \<lambda>x y. star_of f \<star> x \<star> y"

  Ipred :: "('a \<Rightarrow> bool) star \<Rightarrow> ('a star \<Rightarrow> bool)"
  "Ipred P \<equiv> \<lambda>x. unstar (P \<star> x)"

  Ipred_of :: "('a \<Rightarrow> bool) \<Rightarrow> ('a star \<Rightarrow> bool)"
  "Ipred_of P \<equiv> \<lambda>x. unstar (star_of P \<star> x)"

  Ipred2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) star \<Rightarrow> ('a star \<Rightarrow> 'b star \<Rightarrow> bool)"
  "Ipred2 P \<equiv> \<lambda>x y. unstar (P \<star> x \<star> y)"

  Ipred2_of :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a star \<Rightarrow> 'b star \<Rightarrow> bool)"
  "Ipred2_of P \<equiv> \<lambda>x y. unstar (star_of P \<star> x \<star> y)"

lemmas Ifun_defs =
  Ifun_of_def Ifun2_def Ifun2_of_def
  Ipred_def Ipred_of_def Ipred2_def Ipred2_of_def

lemma Ifun_of [simp]:
  "Ifun_of f (star_of x) = star_of (f x)"
by (simp only: Ifun_of_def Ifun)

lemma Ifun2_of [simp]:
  "Ifun2_of f (star_of x) (star_of y) = star_of (f x y)"
by (simp only: Ifun2_of_def Ifun)

lemma Ipred_of [simp]:
  "Ipred_of P (star_of x) = P x"
by (simp only: Ipred_of_def Ifun unstar)

lemma Ipred2_of [simp]:
  "Ipred2_of P (star_of x) (star_of y) = P x y"
by (simp only: Ipred2_of_def Ifun unstar)


subsection {* Internal sets *}

constdefs
  Iset :: "'a set star \<Rightarrow> 'a star set"
  "Iset A \<equiv> {x. Ipred2_of (op \<in>) x A}"

  Iset_of :: "'a set \<Rightarrow> 'a star set"
  "Iset_of A \<equiv> Iset (star_of A)"

lemma Iset_star_n:
  "(star_n X \<in> Iset (star_n A)) = ({n. X n \<in> A n} \<in> \<U>)"
by (simp add: Iset_def Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)



end
