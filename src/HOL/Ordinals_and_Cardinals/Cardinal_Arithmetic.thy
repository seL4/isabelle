(*  Title:      HOL/Ordinals_and_Cardinals/Cardinal_Arithmetic.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Cardinal arithmetic.
*)

header {* Cardinal Arithmetic  *}

theory Cardinal_Arithmetic
imports Cardinal_Order_Relation_Base
begin

text {*
  The following collection of lemmas should be seen as an user interface to the HOL Theory
  of cardinals. It is not expected to be complete in any sense, since its
  development was driven by demand arising from the development of the (co)datatype package.
*}

(*library candidate*)
lemma dir_image: "\<lbrakk>\<And>x y. (f x = f y) = (x = y); Card_order r\<rbrakk> \<Longrightarrow> r =o dir_image r f"
by (rule dir_image_ordIso) (auto simp add: inj_on_def card_order_on_def)

(*should supersede a weaker lemma from the library*)
lemma dir_image_Field: "Field (dir_image r f) = f ` Field r"
unfolding dir_image_def Field_def Range_def Domain_def by fastforce

lemma card_order_dir_image:
  assumes bij: "bij f" and co: "card_order r"
  shows "card_order (dir_image r f)"
proof -
  from assms have "Field (dir_image r f) = UNIV"
    using card_order_on_Card_order[of UNIV r] unfolding bij_def dir_image_Field by auto
  moreover from bij have "\<And>x y. (f x = f y) = (x = y)" unfolding bij_def inj_on_def by auto
  with co have "Card_order (dir_image r f)"
    using card_order_on_Card_order[of UNIV r] Card_order_ordIso2[OF _ dir_image] by blast
  ultimately show ?thesis by auto
qed

(*library candidate*)
lemma ordIso_refl: "Card_order r \<Longrightarrow> r =o r"
by (rule card_order_on_ordIso)

(*library candidate*)
lemma ordLeq_refl: "Card_order r \<Longrightarrow> r \<le>o r"
by (rule ordIso_imp_ordLeq, rule card_order_on_ordIso)

(*library candidate*)
lemma card_of_ordIso_subst: "A = B \<Longrightarrow> |A| =o |B|"
by (simp only: ordIso_refl card_of_Card_order)

(*library candidate*)
lemma card_of_Times_Plus_distrib:
  "|A <*> (B <+> C)| =o |A <*> B <+> A <*> C|" (is "|?RHS| =o |?LHS|")
proof -
  let ?f = "\<lambda>(a, bc). case bc of Inl b \<Rightarrow> Inl (a, b) | Inr c \<Rightarrow> Inr (a, c)"
  have "bij_betw ?f ?RHS ?LHS" unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso by blast
qed

(*library candidate*)
lemma Field_card_order: "card_order r \<Longrightarrow> Field r = UNIV"
using card_order_on_Card_order[of UNIV r] by simp

subsection {* Zero *}

definition czero where
  "czero = card_of {}"

lemma czero_ordIso:
  "czero =o czero"
using card_of_empty_ordIso by (simp add: czero_def)

lemma card_of_ordIso_czero_iff_empty:
  "|A| =o (czero :: 'a rel) \<longleftrightarrow> A = ({} :: 'a set)"
unfolding czero_def by (rule iffI[OF card_of_empty2]) (auto simp: card_of_refl)

(* A "not czero" Cardinal predicate *)
abbreviation Cnotzero where
  "Cnotzero (r :: 'a rel) \<equiv> \<not>(r =o (czero :: 'a rel)) \<and> Card_order r"

(*helper*)
lemma Cnotzero_imp_not_empty: "Cnotzero r \<Longrightarrow> Field r \<noteq> {}"
by (metis Card_order_iff_ordIso_card_of czero_def)

lemma czeroI:
  "\<lbrakk>Card_order r; Field r = {}\<rbrakk> \<Longrightarrow> r =o czero"
using Cnotzero_imp_not_empty ordIso_transitive[OF _ czero_ordIso] by blast

lemma czeroE:
  "r =o czero \<Longrightarrow> Field r = {}"
unfolding czero_def
by (drule card_of_cong) (simp only: Field_card_of card_of_empty2)

lemma Cnotzero_mono:
  "\<lbrakk>Cnotzero r; Card_order q; r \<le>o q\<rbrakk> \<Longrightarrow> Cnotzero q"
apply (rule ccontr)
apply auto
apply (drule czeroE)
apply (erule notE)
apply (erule czeroI)
apply (drule card_of_mono2)
apply (simp only: card_of_empty3)
done

subsection {* Infinite cardinals *}

definition cinfinite where
  "cinfinite r = infinite (Field r)"

abbreviation Cinfinite where
  "Cinfinite r \<equiv> cinfinite r \<and> Card_order r"

lemma natLeq_ordLeq_cinfinite:
  assumes inf: "Cinfinite r"
  shows "natLeq \<le>o r"
proof -
  from inf have "natLeq \<le>o |Field r|" by (simp add: cinfinite_def infinite_iff_natLeq_ordLeq)
  also from inf have "|Field r| =o r" by (simp add: card_of_unique ordIso_symmetric)
  finally show ?thesis .
qed

lemma cinfinite_not_czero: "cinfinite r \<Longrightarrow> \<not> (r =o (czero :: 'a rel))"
unfolding cinfinite_def by (metis czeroE finite.emptyI)

lemma Cinfinite_Cnotzero: "Cinfinite r \<Longrightarrow> Cnotzero r"
by (metis cinfinite_not_czero)

lemma Cinfinite_cong: "\<lbrakk>r1 =o r2; Cinfinite r1\<rbrakk> \<Longrightarrow> Cinfinite r2"
by (metis Card_order_ordIso2 card_of_mono2 card_of_ordLeq_infinite cinfinite_def ordIso_iff_ordLeq)

lemma cinfinite_mono: "\<lbrakk>r1 \<le>o r2; cinfinite r1\<rbrakk> \<Longrightarrow> cinfinite r2"
by (metis card_of_mono2 card_of_ordLeq_infinite cinfinite_def)


subsection {* Binary sum *}

definition csum (infixr "+c" 65) where
  "r1 +c r2 \<equiv> |Field r1 <+> Field r2|"

lemma Card_order_csum:
  "Card_order (r1 +c r2)"
unfolding csum_def by (simp add: card_of_Card_order)

lemma csum_Cnotzero1:
  "Cnotzero r1 \<Longrightarrow> Cnotzero (r1 +c r2)"
unfolding csum_def
by (metis Cnotzero_imp_not_empty Field_card_of Plus_eq_empty_conv card_of_card_order_on czeroE)

lemma csum_Cnotzero2:
  "Cnotzero r2 \<Longrightarrow> Cnotzero (r1 +c r2)"
unfolding csum_def
by (metis Cnotzero_imp_not_empty Field_card_of Plus_eq_empty_conv card_of_card_order_on czeroE)

lemma card_order_csum:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 +c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" using assms card_order_on_Card_order by auto
  thus ?thesis unfolding csum_def by (auto simp: card_of_card_order_on)
qed

lemma cinfinite_csum:
  "cinfinite r1 \<or> cinfinite r2 \<Longrightarrow> cinfinite (r1 +c r2)"
unfolding cinfinite_def csum_def by (auto simp: Field_card_of)

lemma Cinfinite_csum:
  "Cinfinite r1 \<or> Cinfinite r2 \<Longrightarrow> Cinfinite (r1 +c r2)"
unfolding cinfinite_def csum_def by (metis Field_card_of card_of_Card_order finite_Plus_iff)

lemma Cinfinite_csum_strong:
  "\<lbrakk>Cinfinite r1; Cinfinite r2\<rbrakk> \<Longrightarrow> Cinfinite (r1 +c r2)"
by (metis Cinfinite_csum)

lemma Cinfinite_csum1:
  "Cinfinite r1 \<Longrightarrow> Cinfinite (r1 +c r2)"
unfolding cinfinite_def csum_def by (metis Field_card_of card_of_Card_order finite_Plus_iff)

lemma csum_cong: "\<lbrakk>p1 =o r1; p2 =o r2\<rbrakk> \<Longrightarrow> p1 +c p2 =o r1 +c r2"
by (simp only: csum_def ordIso_Plus_cong)

lemma csum_cong1: "p1 =o r1 \<Longrightarrow> p1 +c q =o r1 +c q"
by (simp only: csum_def ordIso_Plus_cong1)

lemma csum_cong2: "p2 =o r2 \<Longrightarrow> q +c p2 =o q +c r2"
by (simp only: csum_def ordIso_Plus_cong2)

lemma csum_mono: "\<lbrakk>p1 \<le>o r1; p2 \<le>o r2\<rbrakk> \<Longrightarrow> p1 +c p2 \<le>o r1 +c r2"
by (simp only: csum_def ordLeq_Plus_mono)

lemma csum_mono1: "p1 \<le>o r1 \<Longrightarrow> p1 +c q \<le>o r1 +c q"
by (simp only: csum_def ordLeq_Plus_mono1)

lemma csum_mono2: "p2 \<le>o r2 \<Longrightarrow> q +c p2 \<le>o q +c r2"
by (simp only: csum_def ordLeq_Plus_mono2)

lemma ordLeq_csum1: "Card_order p1 \<Longrightarrow> p1 \<le>o p1 +c p2"
by (simp only: csum_def Card_order_Plus1)

lemma ordLeq_csum2: "Card_order p2 \<Longrightarrow> p2 \<le>o p1 +c p2"
by (simp only: csum_def Card_order_Plus2)

lemma csum_com: "p1 +c p2 =o p2 +c p1"
by (simp only: csum_def card_of_Plus_commute)

lemma csum_assoc: "(p1 +c p2) +c p3 =o p1 +c p2 +c p3"
by (simp only: csum_def Field_card_of card_of_Plus_assoc)

lemma Plus_csum: "|A <+> B| =o |A| +c |B|"
by (simp only: csum_def Field_card_of card_of_refl)

lemma Un_csum: "|A \<union> B| \<le>o |A| +c |B|"
using ordLeq_ordIso_trans[OF card_of_Un_Plus_ordLeq Plus_csum] by blast


subsection {* One *}

definition cone where
  "cone = card_of {()}"

lemma Card_order_cone: "Card_order cone"
unfolding cone_def by (rule card_of_Card_order)

lemma single_cone:
  "|{x}| =o cone"
proof -
  let ?f = "\<lambda>x. ()"
  have "bij_betw ?f {x} {()}" unfolding bij_betw_def by auto
  thus ?thesis unfolding cone_def using card_of_ordIso by blast
qed

lemma cone_not_czero: "\<not> (cone =o czero)"
unfolding czero_def cone_def by (metis empty_not_insert card_of_empty3[of "{()}"] ordIso_iff_ordLeq)

lemma cone_Cnotzero: "Cnotzero cone"
by (simp add: cone_not_czero Card_order_cone)

lemma cone_ordLeq_Cnotzero: "Cnotzero r \<Longrightarrow> cone \<le>o r"
unfolding cone_def by (metis Card_order_singl_ordLeq czeroI)


subsection{* Two *}

definition ctwo where
  "ctwo = |UNIV :: bool set|"

lemma Card_order_ctwo: "Card_order ctwo"
unfolding ctwo_def by (rule card_of_Card_order)

lemma cone_ordLeq_ctwo: "cone \<le>o ctwo"
unfolding cone_def ctwo_def card_of_ordLeq[symmetric] by auto

lemma ctwo_not_czero: "\<not> (ctwo =o czero)"
using card_of_empty3[of "UNIV :: bool set"] ordIso_iff_ordLeq
unfolding czero_def ctwo_def by (metis UNIV_not_empty)

lemma ctwo_Cnotzero: "Cnotzero ctwo"
by (simp add: ctwo_not_czero Card_order_ctwo)


subsection {* Family sum *}

definition Csum where
  "Csum r rs \<equiv> |SIGMA i : Field r. Field (rs i)|"

(* Similar setup to the one for SIGMA from theory Big_Operators: *)
syntax "_Csum" ::
  "pttrn => ('a * 'a) set => 'b * 'b set => (('a * 'b) * ('a * 'b)) set"
  ("(3CSUM _:_. _)" [0, 51, 10] 10)

translations
  "CSUM i:r. rs" == "CONST Csum r (%i. rs)"

lemma SIGMA_CSUM: "|SIGMA i : I. As i| = (CSUM i : |I|. |As i| )"
by (auto simp: Csum_def Field_card_of)

(* NB: Always, under the cardinal operator,
operations on sets are reduced automatically to operations on cardinals.
This should make cardinal reasoning more direct and natural.  *)


subsection {* Product *}

definition cprod (infixr "*c" 80) where
  "r1 *c r2 = |Field r1 <*> Field r2|"

lemma Times_cprod: "|A \<times> B| =o |A| *c |B|"
by (simp only: cprod_def Field_card_of card_of_refl)

lemma card_order_cprod:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 *c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" using assms card_order_on_Card_order by auto
  thus ?thesis by (auto simp: cprod_def card_of_card_order_on)
qed

lemma Card_order_cprod: "Card_order (r1 *c r2)"
by (simp only: cprod_def Field_card_of card_of_card_order_on)

lemma cprod_cong2: "p2 =o r2 \<Longrightarrow> q *c p2 =o q *c r2"
by (simp only: cprod_def ordIso_Times_cong2)

lemma cprod_mono1: "p1 \<le>o r1 \<Longrightarrow> p1 *c q \<le>o r1 *c q"
by (simp only: cprod_def ordLeq_Times_mono1)

lemma cprod_mono2: "p2 \<le>o r2 \<Longrightarrow> q *c p2 \<le>o q *c r2"
by (simp only: cprod_def ordLeq_Times_mono2)

lemma ordLeq_cprod1: "\<lbrakk>Card_order p1; Cnotzero p2\<rbrakk> \<Longrightarrow> p1 \<le>o p1 *c p2"
unfolding cprod_def by (metis Card_order_Times1 czeroI)

lemma ordLeq_cprod2: "\<lbrakk>Cnotzero p1; Card_order p2\<rbrakk> \<Longrightarrow> p2 \<le>o p1 *c p2"
unfolding cprod_def by (metis Card_order_Times2 czeroI)

lemma cinfinite_cprod: "\<lbrakk>cinfinite r1; cinfinite r2\<rbrakk> \<Longrightarrow> cinfinite (r1 *c r2)"
by (simp add: cinfinite_def cprod_def Field_card_of infinite_cartesian_product)

lemma cinfinite_cprod2: "\<lbrakk>Cnotzero r1; Cinfinite r2\<rbrakk> \<Longrightarrow> cinfinite (r1 *c r2)"
by (metis cinfinite_mono ordLeq_cprod2)

lemma Cinfinite_cprod2: "\<lbrakk>Cnotzero r1; Cinfinite r2\<rbrakk> \<Longrightarrow> Cinfinite (r1 *c r2)"
by (blast intro: cinfinite_cprod2 Card_order_cprod)

lemma cprod_com: "p1 *c p2 =o p2 *c p1"
by (simp only: cprod_def card_of_Times_commute)

lemma card_of_Csum_Times:
  "\<forall>i \<in> I. |A i| \<le>o |B| \<Longrightarrow> (CSUM i : |I|. |A i| ) \<le>o |I| *c |B|"
by (simp only: Csum_def cprod_def Field_card_of card_of_Sigma_Times)

lemma card_of_Csum_Times':
  assumes "Card_order r" "\<forall>i \<in> I. |A i| \<le>o r"
  shows "(CSUM i : |I|. |A i| ) \<le>o |I| *c r"
proof -
  from assms(1) have *: "r =o |Field r|" by (simp add: card_of_unique)
  with assms(2) have "\<forall>i \<in> I. |A i| \<le>o |Field r|" by (blast intro: ordLeq_ordIso_trans)
  hence "(CSUM i : |I|. |A i| ) \<le>o |I| *c |Field r|" by (simp only: card_of_Csum_Times)
  also from * have "|I| *c |Field r| \<le>o |I| *c r"
    by (simp only: Field_card_of card_of_refl cprod_def ordIso_imp_ordLeq)
  finally show ?thesis .
qed

lemma cprod_csum_distrib1: "r1 *c r2 +c r1 *c r3 =o r1 *c (r2 +c r3)"
unfolding csum_def cprod_def by (simp add: Field_card_of card_of_Times_Plus_distrib ordIso_symmetric)

lemma csum_absorb2': "\<lbrakk>Card_order r2; r1 \<le>o r2; cinfinite r1 \<or> cinfinite r2\<rbrakk> \<Longrightarrow> r1 +c r2 =o r2"
unfolding csum_def by (metis Card_order_Plus_infinite cinfinite_def cinfinite_mono)

lemma csum_absorb1':
  assumes card: "Card_order r2"
  and r12: "r1 \<le>o r2" and cr12: "cinfinite r1 \<or> cinfinite r2"
  shows "r2 +c r1 =o r2"
by (rule ordIso_transitive, rule csum_com, rule csum_absorb2', (simp only: assms)+)

lemma csum_absorb1: "\<lbrakk>Cinfinite r2; r1 \<le>o r2\<rbrakk> \<Longrightarrow> r2 +c r1 =o r2"
by (rule csum_absorb1') auto

lemma cprod_infinite1': "\<lbrakk>Cinfinite r; Cnotzero p; p \<le>o r\<rbrakk> \<Longrightarrow> r *c p =o r"
unfolding cinfinite_def cprod_def
by (rule Card_order_Times_infinite[THEN conjunct1]) (blast intro: czeroI)+

lemma cprod_infinite: "Cinfinite r \<Longrightarrow> r *c r =o r"
using cprod_infinite1' Cinfinite_Cnotzero ordLeq_refl by blast


subsection {* Exponentiation *}

definition cexp (infixr "^c" 80) where
  "r1 ^c r2 \<equiv> |Func (Field r2) (Field r1)|"

definition ccexp (infixr "^^c" 80) where
  "r1 ^^c r2 \<equiv> |Pfunc (Field r2) (Field r1)|"

lemma cexp_ordLeq_ccexp: "r1 ^c r2 \<le>o r1 ^^c r2"
unfolding cexp_def ccexp_def by (rule card_of_mono1) (rule Func_Pfunc)

lemma card_order_ccexp:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 ^^c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" using assms card_order_on_Card_order by auto
  thus ?thesis unfolding ccexp_def Pfunc_def
    by (auto simp: card_of_card_order_on split: option.split)
qed

lemma Card_order_cexp: "Card_order (r1 ^c r2)"
unfolding cexp_def by (rule card_of_Card_order)

lemma cexp_mono':
  assumes 1: "p1 \<le>o r1" and 2: "p2 \<le>o r2"
  and n1: "Field p1 \<noteq> {} \<or> cone \<le>o r1 ^c r2"
  and n2: "Field p2 = {} \<Longrightarrow> Field r2 = {}"
  shows "p1 ^c p2 \<le>o r1 ^c r2"
proof(cases "Field p1 = {}")
  case True
  hence "|Field (p1 ^c p2)| \<le>o cone"
    unfolding czero_def cone_def cexp_def Field_card_of
    by (cases "Field p2 = {}", auto intro: card_of_ordLeqI2 simp: Func_empty)
       (metis Func_is_emp card_of_empty ex_in_conv)
  hence "p1 ^c p2 \<le>o cone" by (simp add: Field_card_of cexp_def)
  thus ?thesis using True n1 ordLeq_transitive by auto
next
  case False
  have 1: "|Field p1| \<le>o |Field r1|" and 2: "|Field p2| \<le>o |Field r2|"
    using 1 2 by (auto simp: card_of_mono2)
  obtain f1 where f1: "f1 ` Field r1 = Field p1"
    using 1 unfolding card_of_ordLeq2[OF False, symmetric] by auto
  obtain f2 where f2: "inj_on f2 (Field p2)" "f2 ` Field p2 \<subseteq> Field r2"
    using 2 unfolding card_of_ordLeq[symmetric] by blast
  have 0: "Func_map (Field p2) f1 f2 ` (Field (r1 ^c r2)) = Field (p1 ^c p2)"
    unfolding cexp_def Field_card_of using Func_map_surj[OF f1 f2 n2, symmetric] .
  have 00: "Field (p1 ^c p2) \<noteq> {}" unfolding cexp_def Field_card_of Func_is_emp
    using False by simp
  show ?thesis
    using 0 card_of_ordLeq2[OF 00] unfolding cexp_def Field_card_of by blast
qed

lemma cexp_mono:
  assumes 1: "p1 \<le>o r1" and 2: "p2 \<le>o r2"
  and n1: "Cnotzero p1 \<or> cone \<le>o r1 ^c r2"
  and n2: "p2 =o czero \<Longrightarrow> r2 =o czero" and card: "Card_order p2"
  shows "p1 ^c p2 \<le>o r1 ^c r2"
proof (rule cexp_mono'[OF 1 2])
  show "Field p1 \<noteq> {} \<or> cone \<le>o r1 ^c r2"
  proof (cases "Cnotzero p1")
    case True show ?thesis using Cnotzero_imp_not_empty[OF True] by (rule disjI1)
  next
    case False with n1 show ?thesis by blast
  qed
qed (rule czeroI[OF card, THEN n2, THEN czeroE])

lemma cexp_mono1:
  assumes 1: "p1 \<le>o r1"
  and n1: "Cnotzero p1 \<or> cone \<le>o r1 ^c q" and q: "Card_order q"
  shows "p1 ^c q \<le>o r1 ^c q"
using ordLeq_refl[OF q] by (rule cexp_mono[OF 1 _ n1]) (auto simp: q)

lemma cexp_mono1_Cnotzero: "\<lbrakk>p1 \<le>o r1; Cnotzero p1; Card_order q\<rbrakk> \<Longrightarrow> p1 ^c q \<le>o r1 ^c q"
by (simp add: cexp_mono1)

lemma cexp_mono1_cone_ordLeq: "\<lbrakk>p1 \<le>o r1; cone \<le>o r1 ^c q; Card_order q\<rbrakk> \<Longrightarrow> p1 ^c q \<le>o r1 ^c q"
using assms by (simp add: cexp_mono1)

lemma cexp_mono2':
  assumes 2: "p2 \<le>o r2" and q: "Card_order q"
  and n1: "Field q \<noteq> {} \<or> cone \<le>o q ^c r2"
  and n2: "Field p2 = {} \<Longrightarrow> Field r2 = {}"
  shows "q ^c p2 \<le>o q ^c r2"
using ordLeq_refl[OF q] by (rule cexp_mono'[OF _ 2 n1 n2]) auto

lemma cexp_mono2:
  assumes 2: "p2 \<le>o r2" and q: "Card_order q"
  and n1: "Cnotzero q \<or> cone \<le>o q ^c r2"
  and n2: "p2 =o czero \<Longrightarrow> r2 =o czero" and card: "Card_order p2"
  shows "q ^c p2 \<le>o q ^c r2"
using ordLeq_refl[OF q] by (rule cexp_mono[OF _ 2 n1 n2 card]) auto

lemma cexp_mono2_Cnotzero:
  assumes "p2 \<le>o r2" "Cnotzero q" and n2: "Cnotzero p2"
  shows "q ^c p2 \<le>o q ^c r2"
proof (rule cexp_mono)
  assume *: "p2 =o czero"
  have False using n2 czeroI czeroE[OF *] by blast
  thus "r2 =o czero" by blast
qed (auto simp add: assms ordLeq_refl)

lemma cexp_cong:
  assumes 1: "p1 =o r1" and 2: "p2 =o r2"
  and p1: "Cnotzero p1 \<or> cone \<le>o r1 ^c r2" and Cr: "Card_order r2"
  and r1: "Cnotzero r1 \<or> cone \<le>o p1 ^c p2" and Cp: "Card_order p2"
  shows "p1 ^c p2 =o r1 ^c r2"
proof -
  obtain f where "bij_betw f (Field p2) (Field r2)"
    using 2 card_of_ordIso[of "Field p2" "Field r2"] card_of_cong by auto
  hence 0: "Field p2 = {} \<longleftrightarrow> Field r2 = {}" unfolding bij_betw_def by auto
  have r: "p2 =o czero \<Longrightarrow> r2 =o czero"
    and p: "r2 =o czero \<Longrightarrow> p2 =o czero"
     using 0 Cr Cp czeroE czeroI by auto
  show ?thesis using 0 1 2 unfolding ordIso_iff_ordLeq
    using r p cexp_mono[OF _ _ p1 _ Cp] cexp_mono[OF _ _ r1 _ Cr]
    by blast
qed

lemma cexp_cong1:
  assumes 1: "p1 =o r1" and q: "Card_order q"
  and p1: "Cnotzero p1 \<or> cone \<le>o r1 ^c q"
  and r1: "Cnotzero r1 \<or> cone \<le>o p1 ^c q"
  shows "p1 ^c q =o r1 ^c q"
by (rule cexp_cong[OF 1 _ p1 q r1 q]) (rule ordIso_refl[OF q])

lemma cexp_cong1_Cnotzero:
  assumes "p1 =o r1" "Card_order q" "Cnotzero p1" "Cnotzero r1"
  shows "p1 ^c q =o r1 ^c q"
by (rule cexp_cong1, auto simp add: assms)

lemma cexp_cong2:
  assumes 2: "p2 =o r2" and q: "Card_order q"
  and p: "Card_order p2" and r: "Card_order r2"
  shows "Cnotzero q \<or> (cone \<le>o q ^c p2 \<and> cone \<le>o q ^c r2) \<Longrightarrow>
    q ^c p2 =o q ^c r2"
by (rule cexp_cong[OF _ 2]) (auto simp only: ordIso_refl q p r)

lemma cexp_cong2_Cnotzero:
  assumes 2: "p2 =o r2" and q: "Cnotzero q"
  and p: "Card_order p2"
  shows "q ^c p2 =o q ^c r2"
by (rule cexp_cong[OF _ 2]) (auto simp only: ordIso_refl Card_order_ordIso2[OF p 2] q p)

lemma cexp_czero: "r ^c czero =o cone"
unfolding cexp_def czero_def Field_card_of Func_empty by (rule single_cone)

lemma cexp_cone:
  assumes "Card_order r"
  shows "r ^c cone =o r"
proof -
  have "r ^c cone =o |Field r|"
    unfolding cexp_def cone_def Field_card_of Func_empty
      card_of_ordIso[symmetric] bij_betw_def Func_def inj_on_def image_def
    by (rule exI[of _ "\<lambda>f. case f () of Some a \<Rightarrow> a"]) auto
  also have "|Field r| =o r" by (rule card_of_Field_ordIso[OF assms])
  finally show ?thesis .
qed

lemma cexp_cprod:
  assumes r1: "Cnotzero r1"
  shows "(r1 ^c r2) ^c r3 =o r1 ^c (r2 *c r3)" (is "?L =o ?R")
proof -
  have "?L =o r1 ^c (r3 *c r2)"
    unfolding cprod_def cexp_def Field_card_of
    using card_of_Func_Times by(rule ordIso_symmetric)
  also have "r1 ^c (r3 *c r2) =o ?R"
    apply(rule cexp_cong2) using cprod_com r1 by (auto simp: Card_order_cprod)
  finally show ?thesis .
qed

lemma cexp_cprod_ordLeq:
  assumes r1: "Cnotzero r1" and r2: "Cinfinite r2"
  and r3: "Cnotzero r3" "r3 \<le>o r2"
  shows "(r1 ^c r2) ^c r3 =o r1 ^c r2" (is "?L =o ?R")
proof-
  have "?L =o r1 ^c (r2 *c r3)" using cexp_cprod[OF r1] .
  also have "r1 ^c (r2 *c r3) =o ?R"
  apply(rule cexp_cong2)
  apply(rule cprod_infinite1'[OF r2 r3]) using r1 r2 by (fastforce simp: Card_order_cprod)+
  finally show ?thesis .
qed

lemma Cnotzero_UNIV: "Cnotzero |UNIV|"
by (auto simp: card_of_Card_order card_of_ordIso_czero_iff_empty)

lemma Pow_cexp_ctwo:
  "|Pow A| =o ctwo ^c |A|"
unfolding ctwo_def cexp_def Field_card_of by (rule card_of_Pow_Func)

lemma ordLess_ctwo_cexp:
  assumes "Card_order r"
  shows "r <o ctwo ^c r"
proof -
  have "r <o |Pow (Field r)|" using assms by (rule Card_order_Pow)
  also have "|Pow (Field r)| =o ctwo ^c r"
    unfolding ctwo_def cexp_def Field_card_of by (rule card_of_Pow_Func)
  finally show ?thesis .
qed

lemma ordLeq_cexp1:
  assumes "Cnotzero r" "Card_order q"
  shows "q \<le>o q ^c r"
proof (cases "q =o (czero :: 'a rel)")
  case True thus ?thesis by (simp only: card_of_empty cexp_def czero_def ordIso_ordLeq_trans)
next
  case False
  thus ?thesis
    apply -
    apply (rule ordIso_ordLeq_trans)
    apply (rule ordIso_symmetric)
    apply (rule cexp_cone)
    apply (rule assms(2))
    apply (rule cexp_mono2)
    apply (rule cone_ordLeq_Cnotzero)
    apply (rule assms(1))
    apply (rule assms(2))
    apply (rule disjI1)
    apply (rule conjI)
    apply (rule notI)
    apply (erule notE)
    apply (rule ordIso_transitive)
    apply assumption
    apply (rule czero_ordIso)
    apply (rule assms(2))
    apply (rule notE)
    apply (rule cone_not_czero)
    apply assumption
    apply (rule Card_order_cone)
  done
qed

lemma ordLeq_cexp2:
  assumes "ctwo \<le>o q" "Card_order r"
  shows "r \<le>o q ^c r"
proof (cases "r =o (czero :: 'a rel)")
  case True thus ?thesis by (simp only: card_of_empty cexp_def czero_def ordIso_ordLeq_trans)
next
  case False thus ?thesis
    apply -
    apply (rule ordLess_imp_ordLeq)
    apply (rule ordLess_ordLeq_trans)
    apply (rule ordLess_ctwo_cexp)
    apply (rule assms(2))
    apply (rule cexp_mono1)
    apply (rule assms(1))
    apply (rule disjI1)
    apply (rule ctwo_Cnotzero)
    apply (rule assms(2))
  done
qed

lemma Cnotzero_cexp:
  assumes "Cnotzero q" "Card_order r"
  shows "Cnotzero (q ^c r)"
proof (cases "r =o czero")
  case False thus ?thesis
    apply -
    apply (rule Cnotzero_mono)
    apply (rule assms(1))
    apply (rule Card_order_cexp)
    apply (rule ordLeq_cexp1)
    apply (rule conjI)
    apply (rule notI)
    apply (erule notE)
    apply (rule ordIso_transitive)
    apply assumption
    apply (rule czero_ordIso)
    apply (rule assms(2))
    apply (rule conjunct2)
    apply (rule assms(1))
  done
next
  case True thus ?thesis
    apply -
    apply (rule Cnotzero_mono)
    apply (rule cone_Cnotzero)
    apply (rule Card_order_cexp)
    apply (rule ordIso_imp_ordLeq)
    apply (rule ordIso_symmetric)
    apply (rule ordIso_transitive)
    apply (rule cexp_cong2)
    apply assumption
    apply (rule conjunct2)
    apply (rule assms(1))
    apply (rule assms(2))
    apply (simp only: card_of_Card_order czero_def)
    apply (rule disjI1)
    apply (rule assms(1))
    apply (rule cexp_czero)
  done
qed

lemma Cinfinite_ctwo_cexp:
  "Cinfinite r \<Longrightarrow> Cinfinite (ctwo ^c r)"
unfolding ctwo_def cexp_def cinfinite_def Field_card_of
by (rule conjI, rule infinite_Func, auto, rule card_of_card_order_on)

lemma cinfinite_cexp: "\<lbrakk>ctwo \<le>o q; Cinfinite r\<rbrakk> \<Longrightarrow> cinfinite (q ^c r)"
by (metis assms cinfinite_mono ordLeq_cexp2)

lemma cinfinite_ccexp: "\<lbrakk>ctwo \<le>o q; Cinfinite r\<rbrakk> \<Longrightarrow> cinfinite (q ^^c r)"
by (rule cinfinite_mono[OF cexp_ordLeq_ccexp cinfinite_cexp])

lemma Cinfinite_cexp:
  "\<lbrakk>ctwo \<le>o q; Cinfinite r\<rbrakk> \<Longrightarrow> Cinfinite (q ^c r)"
by (simp add: cinfinite_cexp Card_order_cexp)

lemma ctwo_ordLess_natLeq:
  "ctwo <o natLeq"
unfolding ctwo_def using finite_iff_ordLess_natLeq finite_UNIV by fast

lemma ctwo_ordLess_Cinfinite: "Cinfinite r \<Longrightarrow> ctwo <o r"
by (metis ctwo_ordLess_natLeq natLeq_ordLeq_cinfinite ordLess_ordLeq_trans)

lemma ctwo_ordLeq_Cinfinite:
  assumes "Cinfinite r"
  shows "ctwo \<le>o r"
by (rule ordLess_imp_ordLeq[OF ctwo_ordLess_Cinfinite[OF assms]])

lemma Cinfinite_ordLess_cexp:
  assumes r: "Cinfinite r"
  shows "r <o r ^c r"
proof -
  have "r <o ctwo ^c r" using r by (simp only: ordLess_ctwo_cexp)
  also have "ctwo ^c r \<le>o r ^c r"
    by (rule cexp_mono1[OF ctwo_ordLeq_Cinfinite]) (auto simp: r ctwo_not_czero Card_order_ctwo)
  finally show ?thesis .
qed

lemma infinite_ordLeq_cexp:
  assumes "Cinfinite r"
  shows "r \<le>o r ^c r"
by (rule ordLess_imp_ordLeq[OF Cinfinite_ordLess_cexp[OF assms]])

lemma cone_ordLeq_iff_Field:
  assumes "cone \<le>o r"
  shows "Field r \<noteq> {}"
proof (rule ccontr)
  assume "\<not> Field r \<noteq> {}"
  hence "Field r = {}" by simp
  thus False using card_of_empty3
    card_of_mono2[OF assms] Cnotzero_imp_not_empty[OF cone_Cnotzero] by auto
qed

lemma cone_ordLeq_cexp: "cone \<le>o r1 \<Longrightarrow> cone \<le>o r1 ^c r2"
by (simp add: cexp_def cone_def Func_non_emp card_of_singl_ordLeq cone_ordLeq_iff_Field)

lemma Card_order_czero: "Card_order czero"
by (simp only: card_of_Card_order czero_def)

lemma cexp_mono2'':
  assumes 2: "p2 \<le>o r2"
  and n1: "Cnotzero q"
  and n2: "Card_order p2"
  shows "q ^c p2 \<le>o q ^c r2"
proof (cases "p2 =o (czero :: 'a rel)")
  case True
  hence "q ^c p2 =o q ^c (czero :: 'a rel)" using n1 n2 cexp_cong2 Card_order_czero by blast
  also have "q ^c (czero :: 'a rel) =o cone" using cexp_czero by blast
  also have "cone \<le>o q ^c r2" using cone_ordLeq_cexp cone_ordLeq_Cnotzero n1 by blast
  finally show ?thesis .
next
  case False thus ?thesis using assms cexp_mono2' czeroI by metis
qed

lemma Un_Cinfinite_bound: "\<lbrakk>|A| \<le>o r; |B| \<le>o r; Cinfinite r\<rbrakk> \<Longrightarrow> |A \<union> B| \<le>o r"
by (auto simp add: cinfinite_def card_of_Un_ordLeq_infinite_Field)

lemma UNION_Cinfinite_bound: "\<lbrakk>|I| \<le>o r; \<forall>i \<in> I. |A i| \<le>o r; Cinfinite r\<rbrakk> \<Longrightarrow> |\<Union>i \<in> I. A i| \<le>o r"
by (auto simp add: card_of_UNION_ordLeq_infinite_Field cinfinite_def)

lemma csum_cinfinite_bound:
  assumes "p \<le>o r" "q \<le>o r" "Card_order p" "Card_order q" "Cinfinite r"
  shows "p +c q \<le>o r"
proof -
  from assms(1-4) have "|Field p| \<le>o r" "|Field q| \<le>o r"
    unfolding card_order_on_def using card_of_least ordLeq_transitive by blast+
  with assms show ?thesis unfolding cinfinite_def csum_def
    by (blast intro: card_of_Plus_ordLeq_infinite_Field)
qed

lemma csum_cexp: "\<lbrakk>Cinfinite r1; Cinfinite r2; Card_order q; ctwo \<le>o q\<rbrakk> \<Longrightarrow>
  q ^c r1 +c q ^c r2 \<le>o q ^c (r1 +c r2)"
apply (rule csum_cinfinite_bound)
apply (rule cexp_mono2)
apply (rule ordLeq_csum1)
apply (erule conjunct2)
apply assumption
apply (rule disjI2)
apply (rule ordLeq_transitive)
apply (rule cone_ordLeq_ctwo)
apply (rule ordLeq_transitive)
apply assumption
apply (rule ordLeq_cexp1)
apply (rule Cinfinite_Cnotzero)
apply (rule Cinfinite_csum)
apply (rule disjI1)
apply assumption
apply assumption
apply (rule notE)
apply (rule cinfinite_not_czero[of r1])
apply (erule conjunct1)
apply assumption
apply (erule conjunct2)
apply (rule cexp_mono2)
apply (rule ordLeq_csum2)
apply (erule conjunct2)
apply assumption
apply (rule disjI2)
apply (rule ordLeq_transitive)
apply (rule cone_ordLeq_ctwo)
apply (rule ordLeq_transitive)
apply assumption
apply (rule ordLeq_cexp1)
apply (rule Cinfinite_Cnotzero)
apply (rule Cinfinite_csum)
apply (rule disjI1)
apply assumption
apply assumption
apply (rule notE)
apply (rule cinfinite_not_czero[of r2])
apply (erule conjunct1)
apply assumption
apply (erule conjunct2)
apply (rule Card_order_cexp)
apply (rule Card_order_cexp)
apply (rule Cinfinite_cexp)
apply assumption
apply (rule Cinfinite_csum)
by (rule disjI1)

lemma csum_cexp': "\<lbrakk>Cinfinite r; Card_order q; ctwo \<le>o q\<rbrakk> \<Longrightarrow> q +c r \<le>o q ^c r"
apply (rule csum_cinfinite_bound)
    apply (metis Cinfinite_Cnotzero ordLeq_cexp1)
   apply (metis ordLeq_cexp2)
  apply blast+
by (metis Cinfinite_cexp)

lemma cprod_cinfinite_bound:
  assumes "p \<le>o r" "q \<le>o r" "Card_order p" "Card_order q" "Cinfinite r"
  shows "p *c q \<le>o r"
proof -
  from assms(1-4) have "|Field p| \<le>o r" "|Field q| \<le>o r"
    unfolding card_order_on_def using card_of_least ordLeq_transitive by blast+
  with assms show ?thesis unfolding cinfinite_def cprod_def
    by (blast intro: card_of_Times_ordLeq_infinite_Field)
qed

lemma cprod_csum_cexp:
  "r1 *c r2 \<le>o (r1 +c r2) ^c ctwo"
unfolding cprod_def csum_def cexp_def ctwo_def Field_card_of
proof -
  let ?f = "\<lambda>(a, b). %x. if x then Some (Inl a) else Some (Inr b)"
  have "inj_on ?f (Field r1 \<times> Field r2)" (is "inj_on _ ?LHS")
    by (auto simp: inj_on_def fun_eq_iff split: bool.split)
  moreover
  have "?f ` ?LHS \<subseteq> Func (UNIV :: bool set) (Field r1 <+> Field r2)" (is "_ \<subseteq> ?RHS")
    by (auto simp: Func_def)
  ultimately show "|?LHS| \<le>o |?RHS|" using card_of_ordLeq by blast
qed

lemma card_of_Sigma_ordLeq_Cinfinite:
  "\<lbrakk>Cinfinite r; |I| \<le>o r; \<forall>i \<in> I. |A i| \<le>o r\<rbrakk> \<Longrightarrow> |SIGMA i : I. A i| \<le>o r"
unfolding cinfinite_def by (blast intro: card_of_Sigma_ordLeq_infinite_Field)


(* cardSuc *)

lemma Cinfinite_cardSuc: "Cinfinite r \<Longrightarrow> Cinfinite (cardSuc r)"
by (simp add: cinfinite_def cardSuc_Card_order cardSuc_finite)

lemma cardSuc_UNION_Cinfinite:
  assumes "Cinfinite r" "relChain (cardSuc r) As" "B \<le> (UN i : Field (cardSuc r). As i)" "|B| <=o r"
  shows "EX i : Field (cardSuc r). B \<le> As i"
using cardSuc_UNION assms unfolding cinfinite_def by blast

subsection {* Powerset *}

definition cpow where "cpow r = |Pow (Field r)|"

lemma card_order_cpow: "card_order r \<Longrightarrow> card_order (cpow r)"
by (simp only: cpow_def Field_card_order Pow_UNIV card_of_card_order_on)

lemma cpow_greater_eq: "Card_order r \<Longrightarrow> r \<le>o cpow r"
by (rule ordLess_imp_ordLeq) (simp only: cpow_def Card_order_Pow)

lemma Card_order_cpow: "Card_order (cpow r)"
unfolding cpow_def by (rule card_of_Card_order)

lemma Cinfinite_cpow: "Cinfinite r \<Longrightarrow> Cinfinite (cpow r)"
unfolding cpow_def cinfinite_def by (metis Field_card_of card_of_Card_order infinite_Pow)

lemma cardSuc_ordLeq_cpow: "Card_order r \<Longrightarrow> cardSuc r \<le>o cpow r"
unfolding cpow_def by (metis Card_order_Pow cardSuc_ordLess_ordLeq card_of_Card_order)

lemma cpow_cexp_ctwo: "cpow r =o ctwo ^c r"
unfolding cpow_def ctwo_def cexp_def Field_card_of by (rule card_of_Pow_Func)

subsection {* Lists *}

definition clists where "clists r = |lists (Field r)|"

lemma clists_Cinfinite: "Cinfinite r \<Longrightarrow> clists r =o r"
unfolding cinfinite_def clists_def by (blast intro: Card_order_lists_infinite)

lemma Card_order_clists: "Card_order (clists r)"
unfolding clists_def by (rule card_of_Card_order)

lemma Cnotzero_clists: "Cnotzero (clists r)"
by (simp add: clists_def card_of_ordIso_czero_iff_empty lists_not_empty) (rule card_of_Card_order)

end
