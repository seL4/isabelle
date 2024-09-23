(*  Title:      HOL/BNF_Cardinal_Arithmetic.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Cardinal arithmetic as needed by bounded natural functors.
*)

section \<open>Cardinal Arithmetic as Needed by Bounded Natural Functors\<close>

theory BNF_Cardinal_Arithmetic
  imports BNF_Cardinal_Order_Relation
begin

lemma dir_image: "\<lbrakk>\<And>x y. (f x = f y) = (x = y); Card_order r\<rbrakk> \<Longrightarrow> r =o dir_image r f"
  by (rule dir_image_ordIso) (auto simp add: inj_on_def card_order_on_def)

lemma card_order_dir_image:
  assumes bij: "bij f" and co: "card_order r"
  shows "card_order (dir_image r f)"
proof -
  have "Field (dir_image r f) = UNIV"
    using assms card_order_on_Card_order[of UNIV r] 
    unfolding bij_def dir_image_Field by auto
  moreover from bij have "\<And>x y. (f x = f y) = (x = y)" 
    unfolding bij_def inj_on_def by auto
  with co have "Card_order (dir_image r f)"
    using card_order_on_Card_order Card_order_ordIso2[OF _ dir_image] by blast
  ultimately show ?thesis by auto
qed

lemma ordIso_refl: "Card_order r \<Longrightarrow> r =o r"
  by (rule card_order_on_ordIso)

lemma ordLeq_refl: "Card_order r \<Longrightarrow> r \<le>o r"
  by (rule ordIso_imp_ordLeq, rule card_order_on_ordIso)

lemma card_of_ordIso_subst: "A = B \<Longrightarrow> |A| =o |B|"
  by (simp only: ordIso_refl card_of_Card_order)

lemma Field_card_order: "card_order r \<Longrightarrow> Field r = UNIV"
  using card_order_on_Card_order[of UNIV r] by simp


subsection \<open>Zero\<close>

definition czero where
  "czero = card_of {}"

lemma czero_ordIso: "czero =o czero"
  using card_of_empty_ordIso by (simp add: czero_def)

lemma card_of_ordIso_czero_iff_empty:
  "|A| =o (czero :: 'b rel) \<longleftrightarrow> A = ({} :: 'a set)"
  unfolding czero_def by (rule iffI[OF card_of_empty2]) (auto simp: card_of_refl card_of_empty_ordIso)

(* A "not czero" Cardinal predicate *)
abbreviation Cnotzero where
  "Cnotzero (r :: 'a rel) \<equiv> \<not>(r =o (czero :: 'a rel)) \<and> Card_order r"

(*helper*)
lemma Cnotzero_imp_not_empty: "Cnotzero r \<Longrightarrow> Field r \<noteq> {}"
  unfolding Card_order_iff_ordIso_card_of czero_def by force

lemma czeroI:
  "\<lbrakk>Card_order r; Field r = {}\<rbrakk> \<Longrightarrow> r =o czero"
  using Cnotzero_imp_not_empty ordIso_transitive[OF _ czero_ordIso] by blast

lemma czeroE:
  "r =o czero \<Longrightarrow> Field r = {}"
  unfolding czero_def
  by (drule card_of_cong) (simp only: Field_card_of card_of_empty2)

lemma Cnotzero_mono:
  "\<lbrakk>Cnotzero r; Card_order q; r \<le>o q\<rbrakk> \<Longrightarrow> Cnotzero q"
    by (force intro: czeroI dest: card_of_mono2 card_of_empty3 czeroE)

subsection \<open>(In)finite cardinals\<close>

definition cinfinite where
  "cinfinite r \<equiv> (\<not> finite (Field r))"

abbreviation Cinfinite where
  "Cinfinite r \<equiv> cinfinite r \<and> Card_order r"

definition cfinite where
  "cfinite r = finite (Field r)"

abbreviation Cfinite where
  "Cfinite r \<equiv> cfinite r \<and> Card_order r"

lemma Cfinite_ordLess_Cinfinite: "\<lbrakk>Cfinite r; Cinfinite s\<rbrakk> \<Longrightarrow> r <o s"
  unfolding cfinite_def cinfinite_def
  by (blast intro: finite_ordLess_infinite card_order_on_well_order_on)

lemmas natLeq_card_order = natLeq_Card_order[unfolded Field_natLeq]

lemma natLeq_cinfinite: "cinfinite natLeq"
  unfolding cinfinite_def Field_natLeq by (rule infinite_UNIV_nat)

lemma natLeq_Cinfinite: "Cinfinite natLeq"
  using natLeq_cinfinite natLeq_Card_order by simp

lemma natLeq_ordLeq_cinfinite:
  assumes inf: "Cinfinite r"
  shows "natLeq \<le>o r"
proof -
  from inf have "natLeq \<le>o |Field r|" unfolding cinfinite_def
    using infinite_iff_natLeq_ordLeq by blast
  also from inf have "|Field r| =o r" by (simp add: card_of_unique ordIso_symmetric)
  finally show ?thesis .
qed

lemma cinfinite_not_czero: "cinfinite r \<Longrightarrow> \<not> (r =o (czero :: 'a rel))"
  unfolding cinfinite_def by (cases "Field r = {}") (auto dest: czeroE)

lemma Cinfinite_Cnotzero: "Cinfinite r \<Longrightarrow> Cnotzero r"
  using cinfinite_not_czero by auto

lemma Cinfinite_cong: "\<lbrakk>r1 =o r2; Cinfinite r1\<rbrakk> \<Longrightarrow> Cinfinite r2"
  using Card_order_ordIso2[of r1 r2] unfolding cinfinite_def ordIso_iff_ordLeq
  by (auto dest: card_of_ordLeq_infinite[OF card_of_mono2])

lemma cinfinite_mono: "\<lbrakk>r1 \<le>o r2; cinfinite r1\<rbrakk> \<Longrightarrow> cinfinite r2"
  unfolding cinfinite_def by (auto dest: card_of_ordLeq_infinite[OF card_of_mono2])

lemma regularCard_ordIso:
  assumes  "k =o k'" and "Cinfinite k" and "regularCard k"
  shows "regularCard k'"
proof-
  have "stable k" using assms cinfinite_def regularCard_stable by blast
  hence "stable k'" using assms stable_ordIso1 ordIso_symmetric by blast
  thus ?thesis using assms cinfinite_def stable_regularCard Cinfinite_cong by blast
qed

corollary card_of_UNION_ordLess_infinite_Field_regularCard:
  assumes "regularCard r" and "Cinfinite r" and "|I| <o r" and "\<forall>i \<in> I. |A i| <o r"
  shows "|\<Union>i \<in> I. A i| <o r"
  using card_of_UNION_ordLess_infinite_Field regularCard_stable assms cinfinite_def by blast

subsection \<open>Binary sum\<close>

definition csum (infixr \<open>+c\<close> 65) 
    where "r1 +c r2 \<equiv> |Field r1 <+> Field r2|"

lemma Field_csum: "Field (r +c s) = Inl ` Field r \<union> Inr ` Field s"
  unfolding csum_def Field_card_of by auto

lemma Card_order_csum: "Card_order (r1 +c r2)"
  unfolding csum_def by (simp add: card_of_Card_order)

lemma csum_Cnotzero1: "Cnotzero r1 \<Longrightarrow> Cnotzero (r1 +c r2)"
  using Cnotzero_imp_not_empty 
  by (auto intro: card_of_Card_order simp: csum_def card_of_ordIso_czero_iff_empty)

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
  using card_of_Card_order 
  by (auto simp: cinfinite_def csum_def Field_card_of)

lemma Cinfinite_csum1: "Cinfinite r1 \<Longrightarrow> Cinfinite (r1 +c r2)"
  by (blast intro!: Cinfinite_csum elim: )

lemma Cinfinite_csum_weak:
  "\<lbrakk>Cinfinite r1; Cinfinite r2\<rbrakk> \<Longrightarrow> Cinfinite (r1 +c r2)"
by (erule Cinfinite_csum1)

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

lemma Cfinite_csum: "\<lbrakk>Cfinite r; Cfinite s\<rbrakk> \<Longrightarrow> Cfinite (r +c s)"
  unfolding cfinite_def csum_def Field_card_of using card_of_card_order_on by simp

lemma csum_csum: "(r1 +c r2) +c (r3 +c r4) =o (r1 +c r3) +c (r2 +c r4)"
proof -
  have "(r1 +c r2) +c (r3 +c r4) =o r1 +c r2 +c (r3 +c r4)"
    by (rule csum_assoc)
  also have "r1 +c r2 +c (r3 +c r4) =o r1 +c (r2 +c r3) +c r4"
    by (intro csum_assoc csum_cong2 ordIso_symmetric)
  also have "r1 +c (r2 +c r3) +c r4 =o r1 +c (r3 +c r2) +c r4"
    by (intro csum_com csum_cong1 csum_cong2)
  also have "r1 +c (r3 +c r2) +c r4 =o r1 +c r3 +c r2 +c r4"
    by (intro csum_assoc csum_cong2 ordIso_symmetric)
  also have "r1 +c r3 +c r2 +c r4 =o (r1 +c r3) +c (r2 +c r4)"
    by (intro csum_assoc ordIso_symmetric)
  finally show ?thesis .
qed

lemma Plus_csum: "|A <+> B| =o |A| +c |B|"
  by (simp only: csum_def Field_card_of card_of_refl)

lemma Un_csum: "|A \<union> B| \<le>o |A| +c |B|"
  using ordLeq_ordIso_trans[OF card_of_Un_Plus_ordLeq Plus_csum] by blast

subsection \<open>One\<close>

definition cone where
  "cone = card_of {()}"

lemma Card_order_cone: "Card_order cone"
  unfolding cone_def by (rule card_of_Card_order)

lemma Cfinite_cone: "Cfinite cone"
  unfolding cfinite_def by (simp add: Card_order_cone)

lemma cone_not_czero: "\<not> (cone =o czero)"
  unfolding czero_def cone_def ordIso_iff_ordLeq 
  using card_of_empty3 empty_not_insert by blast

lemma cone_ordLeq_Cnotzero: "Cnotzero r \<Longrightarrow> cone \<le>o r"
  unfolding cone_def by (rule Card_order_singl_ordLeq) (auto intro: czeroI)


subsection \<open>Two\<close>

definition ctwo where
  "ctwo = |UNIV :: bool set|"

lemma Card_order_ctwo: "Card_order ctwo"
  unfolding ctwo_def by (rule card_of_Card_order)

lemma ctwo_not_czero: "\<not> (ctwo =o czero)"
  using card_of_empty3[of "UNIV :: bool set"] ordIso_iff_ordLeq
  unfolding czero_def ctwo_def using UNIV_not_empty by auto

lemma ctwo_Cnotzero: "Cnotzero ctwo"
  by (simp add: ctwo_not_czero Card_order_ctwo)


subsection \<open>Family sum\<close>

definition Csum where
  "Csum r rs \<equiv> |SIGMA i : Field r. Field (rs i)|"

(* Similar setup to the one for SIGMA from theory Big_Operators: *)
syntax "_Csum" ::
  "pttrn => ('a * 'a) set => 'b * 'b set => (('a * 'b) * ('a * 'b)) set"
  (\<open>(\<open>indent=3 notation=\<open>binder CSUM\<close>\<close>CSUM _:_. _)\<close> [0, 51, 10] 10)

syntax_consts
  "_Csum" == Csum

translations
  "CSUM i:r. rs" == "CONST Csum r (%i. rs)"

lemma SIGMA_CSUM: "|SIGMA i : I. As i| = (CSUM i : |I|. |As i| )"
  by (auto simp: Csum_def Field_card_of)

(* NB: Always, under the cardinal operator,
operations on sets are reduced automatically to operations on cardinals.
This should make cardinal reasoning more direct and natural.  *)


subsection \<open>Product\<close>

definition cprod (infixr \<open>*c\<close> 80) where
  "r1 *c r2 = |Field r1 \<times> Field r2|"

lemma card_order_cprod:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 *c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" 
    using assms card_order_on_Card_order by auto
  thus ?thesis by (auto simp: cprod_def card_of_card_order_on)
qed

lemma Card_order_cprod: "Card_order (r1 *c r2)"
  by (simp only: cprod_def Field_card_of card_of_card_order_on)

lemma cprod_mono1: "p1 \<le>o r1 \<Longrightarrow> p1 *c q \<le>o r1 *c q"
  by (simp only: cprod_def ordLeq_Times_mono1)

lemma cprod_mono2: "p2 \<le>o r2 \<Longrightarrow> q *c p2 \<le>o q *c r2"
  by (simp only: cprod_def ordLeq_Times_mono2)

lemma cprod_mono: "\<lbrakk>p1 \<le>o r1; p2 \<le>o r2\<rbrakk> \<Longrightarrow> p1 *c p2 \<le>o r1 *c r2"
  by (rule ordLeq_transitive[OF cprod_mono1 cprod_mono2])

lemma ordLeq_cprod2: "\<lbrakk>Cnotzero p1; Card_order p2\<rbrakk> \<Longrightarrow> p2 \<le>o p1 *c p2"
  unfolding cprod_def by (rule Card_order_Times2) (auto intro: czeroI)

lemma cinfinite_cprod: "\<lbrakk>cinfinite r1; cinfinite r2\<rbrakk> \<Longrightarrow> cinfinite (r1 *c r2)"
  by (simp add: cinfinite_def cprod_def Field_card_of infinite_cartesian_product)

lemma cinfinite_cprod2: "\<lbrakk>Cnotzero r1; Cinfinite r2\<rbrakk> \<Longrightarrow> cinfinite (r1 *c r2)"
  by (rule cinfinite_mono) (auto intro: ordLeq_cprod2)

lemma Cinfinite_cprod2: "\<lbrakk>Cnotzero r1; Cinfinite r2\<rbrakk> \<Longrightarrow> Cinfinite (r1 *c r2)"
  by (blast intro: cinfinite_cprod2 Card_order_cprod)

lemma cprod_cong: "\<lbrakk>p1 =o r1; p2 =o r2\<rbrakk> \<Longrightarrow> p1 *c p2 =o r1 *c r2"
  unfolding ordIso_iff_ordLeq by (blast intro: cprod_mono)

lemma cprod_cong1: "\<lbrakk>p1 =o r1\<rbrakk> \<Longrightarrow> p1 *c p2 =o r1 *c p2"
  unfolding ordIso_iff_ordLeq by (blast intro: cprod_mono1)

lemma cprod_cong2: "p2 =o r2 \<Longrightarrow> q *c p2 =o q *c r2"
  unfolding ordIso_iff_ordLeq by (blast intro: cprod_mono2)

lemma cprod_com: "p1 *c p2 =o p2 *c p1"
  by (simp only: cprod_def card_of_Times_commute)

lemma card_of_Csum_Times:
  "\<forall>i \<in> I. |A i| \<le>o |B| \<Longrightarrow> (CSUM i : |I|. |A i| ) \<le>o |I| *c |B|"
  by (simp only: Csum_def cprod_def Field_card_of card_of_Sigma_mono1)

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
  unfolding csum_def 
  using Card_order_Plus_infinite
  by (fastforce simp: cinfinite_def dest: cinfinite_mono)

lemma csum_absorb1':
  assumes card: "Card_order r2"
    and r12: "r1 \<le>o r2" and cr12: "cinfinite r1 \<or> cinfinite r2"
  shows "r2 +c r1 =o r2"
proof -
  have "r1 +c r2 =o r2"
    by (simp add: csum_absorb2' assms)
  then show ?thesis
    by (blast intro: ordIso_transitive csum_com)
qed

lemma csum_absorb1: "\<lbrakk>Cinfinite r2; r1 \<le>o r2\<rbrakk> \<Longrightarrow> r2 +c r1 =o r2"
  by (rule csum_absorb1') auto

lemma csum_absorb2: "\<lbrakk>Cinfinite r2 ; r1 \<le>o r2\<rbrakk> \<Longrightarrow> r1 +c r2 =o r2"
  using ordIso_transitive csum_com csum_absorb1 by blast

lemma regularCard_csum:
  assumes "Cinfinite r" "Cinfinite s" "regularCard r" "regularCard s"
  shows "regularCard (r +c s)"
proof (cases "r \<le>o s")
  case True
  then show ?thesis using regularCard_ordIso[of s] csum_absorb2'[THEN ordIso_symmetric] assms by auto
next
  case False
  have "Well_order s" "Well_order r" using assms card_order_on_well_order_on by auto
  then have "s \<le>o r" using not_ordLeq_iff_ordLess False ordLess_imp_ordLeq by auto
  then show ?thesis using regularCard_ordIso[of r] csum_absorb1'[THEN ordIso_symmetric] assms by auto
qed

lemma csum_mono_strict:
  assumes Card_order: "Card_order r" "Card_order q"
    and Cinfinite: "Cinfinite r'" "Cinfinite q'"
    and less: "r <o r'" "q <o q'"
  shows "r +c q <o r' +c q'"
proof -
  have Well_order: "Well_order r" "Well_order q" "Well_order r'" "Well_order q'"
    using card_order_on_well_order_on Card_order Cinfinite by auto
  show ?thesis
  proof (cases "Cinfinite r")
    case outer: True
    then show ?thesis
    proof (cases "Cinfinite q")
      case inner: True
      then show ?thesis
      proof (cases "r \<le>o q")
        case True
        then have "r +c q =o q" using csum_absorb2 inner by blast
        then show ?thesis
          using ordIso_ordLess_trans ordLess_ordLeq_trans less Cinfinite ordLeq_csum2 by blast
      next
        case False
        then have "q \<le>o r" using not_ordLeq_iff_ordLess Well_order ordLess_imp_ordLeq by blast
        then have "r +c q =o r" using csum_absorb1 outer by blast
        then show ?thesis
          using ordIso_ordLess_trans ordLess_ordLeq_trans less Cinfinite ordLeq_csum1 by blast
      qed
    next
      case False
      then have "Cfinite q" using Card_order cinfinite_def cfinite_def by blast
      then have "q \<le>o r" using finite_ordLess_infinite cfinite_def cinfinite_def outer
          Well_order ordLess_imp_ordLeq by blast
      then have "r +c q =o r" by (rule csum_absorb1[OF outer])
      then show ?thesis using ordIso_ordLess_trans ordLess_ordLeq_trans less ordLeq_csum1 Cinfinite by blast
    qed
  next
    case False
    then have outer: "Cfinite r" using Card_order cinfinite_def cfinite_def by blast
    then show ?thesis
    proof (cases "Cinfinite q")
      case True
      then have "r \<le>o q" using finite_ordLess_infinite cinfinite_def cfinite_def outer Well_order
          ordLess_imp_ordLeq by blast
      then have "r +c q =o q" by (rule csum_absorb2[OF True])
      then show ?thesis using ordIso_ordLess_trans ordLess_ordLeq_trans less ordLeq_csum2 Cinfinite by blast
    next
      case False
      then have "Cfinite q" using Card_order cinfinite_def cfinite_def by blast
      then have "Cfinite (r +c q)" using Cfinite_csum outer by blast
      moreover have "Cinfinite (r' +c q')" using Cinfinite_csum1 Cinfinite by blast
      ultimately show ?thesis using Cfinite_ordLess_Cinfinite by blast
    qed
  qed
qed

subsection \<open>Exponentiation\<close>

definition cexp (infixr \<open>^c\<close> 90) where
  "r1 ^c r2 \<equiv> |Func (Field r2) (Field r1)|"

lemma Card_order_cexp: "Card_order (r1 ^c r2)"
  unfolding cexp_def by (rule card_of_Card_order)

lemma cexp_mono':
  assumes 1: "p1 \<le>o r1" and 2: "p2 \<le>o r2"
    and n: "Field p2 = {} \<Longrightarrow> Field r2 = {}"
  shows "p1 ^c p2 \<le>o r1 ^c r2"
proof(cases "Field p1 = {}")
  case True
  hence "Field p2 \<noteq> {} \<Longrightarrow> Func (Field p2) {} = {}" unfolding Func_is_emp by simp
  with True have "|Field |Func (Field p2) (Field p1)|| \<le>o cone"
    unfolding cone_def Field_card_of
    by (cases "Field p2 = {}", auto intro: surj_imp_ordLeq simp: Func_empty)
  hence "|Func (Field p2) (Field p1)| \<le>o cone" by (simp add: Field_card_of cexp_def)
  hence "p1 ^c p2 \<le>o cone" unfolding cexp_def .
  thus ?thesis
  proof (cases "Field p2 = {}")
    case True
    with n have "Field r2 = {}" .
    hence "cone \<le>o r1 ^c r2" unfolding cone_def cexp_def Func_def
      by (auto intro: card_of_ordLeqI[where f="\<lambda>_ _. undefined"])
    thus ?thesis using \<open>p1 ^c p2 \<le>o cone\<close> ordLeq_transitive by auto
  next
    case False with True have "|Field (p1 ^c p2)| =o czero"
      unfolding card_of_ordIso_czero_iff_empty cexp_def Field_card_of Func_def by auto
    thus ?thesis unfolding cexp_def card_of_ordIso_czero_iff_empty Field_card_of
      by (simp add: card_of_empty)
  qed
next
  case False
  have 1: "|Field p1| \<le>o |Field r1|" and 2: "|Field p2| \<le>o |Field r2|"
    using 1 2 by (auto simp: card_of_mono2)
  obtain f1 where f1: "f1 ` Field r1 = Field p1"
    using 1 unfolding card_of_ordLeq2[OF False, symmetric] by auto
  obtain f2 where f2: "inj_on f2 (Field p2)" "f2 ` Field p2 \<subseteq> Field r2"
    using 2 unfolding card_of_ordLeq[symmetric] by blast
  have 0: "Func_map (Field p2) f1 f2 ` (Field (r1 ^c r2)) = Field (p1 ^c p2)"
    unfolding cexp_def Field_card_of using Func_map_surj[OF f1 f2 n, symmetric] .
  have 00: "Field (p1 ^c p2) \<noteq> {}" unfolding cexp_def Field_card_of Func_is_emp
    using False by simp
  show ?thesis
    using 0 card_of_ordLeq2[OF 00] unfolding cexp_def Field_card_of by blast
qed

lemma cexp_mono:
  assumes 1: "p1 \<le>o r1" and 2: "p2 \<le>o r2"
    and n: "p2 =o czero \<Longrightarrow> r2 =o czero" and card: "Card_order p2"
  shows "p1 ^c p2 \<le>o r1 ^c r2"
  by (rule cexp_mono'[OF 1 2 czeroE[OF n[OF czeroI[OF card]]]])

lemma cexp_mono1:
  assumes 1: "p1 \<le>o r1" and q: "Card_order q"
  shows "p1 ^c q \<le>o r1 ^c q"
  using ordLeq_refl[OF q] by (rule cexp_mono[OF 1]) (auto simp: q)

lemma cexp_mono2':
  assumes 2: "p2 \<le>o r2" and q: "Card_order q"
    and n: "Field p2 = {} \<Longrightarrow> Field r2 = {}"
  shows "q ^c p2 \<le>o q ^c r2"
  using ordLeq_refl[OF q] by (rule cexp_mono'[OF _ 2 n]) auto

lemma cexp_mono2:
  assumes 2: "p2 \<le>o r2" and q: "Card_order q"
    and n: "p2 =o czero \<Longrightarrow> r2 =o czero" and card: "Card_order p2"
  shows "q ^c p2 \<le>o q ^c r2"
  using ordLeq_refl[OF q] by (rule cexp_mono[OF _ 2 n card]) auto

lemma cexp_mono2_Cnotzero:
  assumes "p2 \<le>o r2" "Card_order q" "Cnotzero p2"
  shows "q ^c p2 \<le>o q ^c r2"
  using assms(3) czeroI by (blast intro: cexp_mono2'[OF assms(1,2)])

lemma cexp_cong:
  assumes 1: "p1 =o r1" and 2: "p2 =o r2"
    and Cr: "Card_order r2"
    and Cp: "Card_order p2"
  shows "p1 ^c p2 =o r1 ^c r2"
proof -
  obtain f where "bij_betw f (Field p2) (Field r2)"
    using 2 card_of_ordIso[of "Field p2" "Field r2"] card_of_cong by auto
  hence 0: "Field p2 = {} \<longleftrightarrow> Field r2 = {}" unfolding bij_betw_def by auto
  have r: "p2 =o czero \<Longrightarrow> r2 =o czero"
    and p: "r2 =o czero \<Longrightarrow> p2 =o czero"
    using 0 Cr Cp czeroE czeroI by auto
  show ?thesis using 0 1 2 unfolding ordIso_iff_ordLeq
    using r p cexp_mono[OF _ _ _ Cp] cexp_mono[OF _ _ _ Cr] by blast
qed

lemma cexp_cong1:
  assumes 1: "p1 =o r1" and q: "Card_order q"
  shows "p1 ^c q =o r1 ^c q"
  by (rule cexp_cong[OF 1 _ q q]) (rule ordIso_refl[OF q])

lemma cexp_cong2:
  assumes 2: "p2 =o r2" and q: "Card_order q" and p: "Card_order p2"
  shows "q ^c p2 =o q ^c r2"
  by (rule cexp_cong[OF _ 2]) (auto simp only: ordIso_refl Card_order_ordIso2[OF p 2] q p)

lemma cexp_cone:
  assumes "Card_order r"
  shows "r ^c cone =o r"
proof -
  have "r ^c cone =o |Field r|"
    unfolding cexp_def cone_def Field_card_of Func_empty
      card_of_ordIso[symmetric] bij_betw_def Func_def inj_on_def image_def
    by (rule exI[of _ "\<lambda>f. f ()"]) auto
  also have "|Field r| =o r" by (rule card_of_Field_ordIso[OF assms])
  finally show ?thesis .
qed

lemma cexp_cprod:
  assumes r1: "Card_order r1"
  shows "(r1 ^c r2) ^c r3 =o r1 ^c (r2 *c r3)" (is "?L =o ?R")
proof -
  have "?L =o r1 ^c (r3 *c r2)"
    unfolding cprod_def cexp_def Field_card_of
    using card_of_Func_Times by(rule ordIso_symmetric)
  also have "r1 ^c (r3 *c r2) =o ?R"
    using cprod_com r1 by (intro cexp_cong2, auto simp: Card_order_cprod)
  finally show ?thesis .
qed

lemma cprod_infinite1': "\<lbrakk>Cinfinite r; Cnotzero p; p \<le>o r\<rbrakk> \<Longrightarrow> r *c p =o r"
  unfolding cinfinite_def cprod_def
  by (rule Card_order_Times_infinite[THEN conjunct1]) (blast intro: czeroI)+

lemma cprod_infinite: "Cinfinite r \<Longrightarrow> r *c r =o r"
  using cprod_infinite1' Cinfinite_Cnotzero ordLeq_refl by blast

lemma cexp_cprod_ordLeq:
  assumes r1: "Card_order r1" and r2: "Cinfinite r2"
    and r3: "Cnotzero r3" "r3 \<le>o r2"
  shows "(r1 ^c r2) ^c r3 =o r1 ^c r2" (is "?L =o ?R")
proof-
  have "?L =o r1 ^c (r2 *c r3)" using cexp_cprod[OF r1] .
  also have "r1 ^c (r2 *c r3) =o ?R"
    using assms by (fastforce simp: Card_order_cprod intro: cprod_infinite1' cexp_cong2)
  finally show ?thesis .
qed

lemma Cnotzero_UNIV: "Cnotzero |UNIV|"
  by (auto simp: card_of_Card_order card_of_ordIso_czero_iff_empty)

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
  have "q =o q ^c cone"
    by (blast intro: assms ordIso_symmetric cexp_cone)
  also have "q ^c cone \<le>o q ^c r"
    using assms
    by (intro cexp_mono2) (simp_all add: cone_ordLeq_Cnotzero cone_not_czero Card_order_cone)
  finally show ?thesis .
qed

lemma ordLeq_cexp2:
  assumes "ctwo \<le>o q" "Card_order r"
  shows "r \<le>o q ^c r"
proof (cases "r =o (czero :: 'a rel)")
  case True thus ?thesis by (simp only: card_of_empty cexp_def czero_def ordIso_ordLeq_trans)
next
  case False 
  have "r <o ctwo ^c r"
    by (blast intro: assms ordLess_ctwo_cexp) 
  also have "ctwo ^c r \<le>o q ^c r"
    by (blast intro: assms cexp_mono1)
  finally show ?thesis by (rule ordLess_imp_ordLeq)
qed

lemma cinfinite_cexp: "\<lbrakk>ctwo \<le>o q; Cinfinite r\<rbrakk> \<Longrightarrow> cinfinite (q ^c r)"
  by (rule cinfinite_mono[OF ordLeq_cexp2]) simp_all

lemma Cinfinite_cexp:
  "\<lbrakk>ctwo \<le>o q; Cinfinite r\<rbrakk> \<Longrightarrow> Cinfinite (q ^c r)"
  by (simp add: cinfinite_cexp Card_order_cexp)

lemma card_order_cexp:
  assumes "card_order r1" "card_order r2"
  shows "card_order (r1 ^c r2)"
proof -
  have "Field r1 = UNIV" "Field r2 = UNIV" using assms card_order_on_Card_order by auto
  thus ?thesis unfolding cexp_def Func_def using card_of_card_order_on by simp
qed

lemma ctwo_ordLess_natLeq: "ctwo <o natLeq"
  unfolding ctwo_def using finite_UNIV natLeq_cinfinite natLeq_Card_order
  by (intro Cfinite_ordLess_Cinfinite) (auto simp: cfinite_def card_of_Card_order)

lemma ctwo_ordLess_Cinfinite: "Cinfinite r \<Longrightarrow> ctwo <o r"
  by (rule ordLess_ordLeq_trans[OF ctwo_ordLess_natLeq natLeq_ordLeq_cinfinite])

lemma ctwo_ordLeq_Cinfinite:
  assumes "Cinfinite r"
  shows "ctwo \<le>o r"
  by (rule ordLess_imp_ordLeq[OF ctwo_ordLess_Cinfinite[OF assms]])

lemma Un_Cinfinite_bound: "\<lbrakk>|A| \<le>o r; |B| \<le>o r; Cinfinite r\<rbrakk> \<Longrightarrow> |A \<union> B| \<le>o r"
  by (auto simp add: cinfinite_def card_of_Un_ordLeq_infinite_Field)

lemma Un_Cinfinite_bound_strict: "\<lbrakk>|A| <o r; |B| <o r; Cinfinite r\<rbrakk> \<Longrightarrow> |A \<union> B| <o r"
  by (auto simp add: cinfinite_def card_of_Un_ordLess_infinite_Field)

lemma UNION_Cinfinite_bound: "\<lbrakk>|I| \<le>o r; \<forall>i \<in> I. |A i| \<le>o r; Cinfinite r\<rbrakk> \<Longrightarrow> |\<Union>i \<in> I. A i| \<le>o r"
  by (auto simp add: card_of_UNION_ordLeq_infinite_Field cinfinite_def)

lemma csum_cinfinite_bound:
  assumes "p \<le>o r" "q \<le>o r" "Card_order p" "Card_order q" "Cinfinite r"
  shows "p +c q \<le>o r"
proof -
  have "|Field p| \<le>o r" "|Field q| \<le>o r"
    using assms card_of_least ordLeq_transitive unfolding card_order_on_def by blast+
  with assms show ?thesis unfolding cinfinite_def csum_def
    by (blast intro: card_of_Plus_ordLeq_infinite_Field)
qed

lemma cprod_cinfinite_bound:
  assumes "p \<le>o r" "q \<le>o r" "Card_order p" "Card_order q" "Cinfinite r"
  shows "p *c q \<le>o r"
proof -
  from assms(1-4) have "|Field p| \<le>o r" "|Field q| \<le>o r"
    unfolding card_order_on_def using card_of_least ordLeq_transitive by blast+
  with assms show ?thesis unfolding cinfinite_def cprod_def
    by (blast intro: card_of_Times_ordLeq_infinite_Field)
qed

lemma cprod_infinite2': "\<lbrakk>Cnotzero r1; Cinfinite r2; r1 \<le>o r2\<rbrakk> \<Longrightarrow> r1 *c r2 =o r2"
  unfolding ordIso_iff_ordLeq
  by (intro conjI cprod_cinfinite_bound ordLeq_cprod2 ordLeq_refl)
    (auto dest!: ordIso_imp_ordLeq not_ordLeq_ordLess simp: czero_def Card_order_empty)

lemma regularCard_cprod:
  assumes "Cinfinite r" "Cinfinite s" "regularCard r" "regularCard s"
  shows "regularCard (r *c s)"
proof (cases "r \<le>o s")
  case True
  with assms Cinfinite_Cnotzero show ?thesis
    by (force intro: regularCard_ordIso ordIso_symmetric[OF cprod_infinite2'])
next
  case False
  have "Well_order r" "Well_order s" using assms card_order_on_well_order_on by auto
  then have "s \<le>o r" using not_ordLeq_iff_ordLess ordLess_imp_ordLeq False by blast
  with assms Cinfinite_Cnotzero show ?thesis
    by (force intro: regularCard_ordIso ordIso_symmetric[OF cprod_infinite1'])
qed

lemma cprod_csum_cexp:
  "r1 *c r2 \<le>o (r1 +c r2) ^c ctwo"
  unfolding cprod_def csum_def cexp_def ctwo_def Field_card_of
proof -
  let ?f = "\<lambda>(a, b). %x. if x then Inl a else Inr b"
  have "inj_on ?f (Field r1 \<times> Field r2)" (is "inj_on _ ?LHS")
    by (auto simp: inj_on_def fun_eq_iff split: bool.split)
  moreover
  have "?f ` ?LHS \<subseteq> Func (UNIV :: bool set) (Field r1 <+> Field r2)" (is "_ \<subseteq> ?RHS")
    by (auto simp: Func_def)
  ultimately show "|?LHS| \<le>o |?RHS|" using card_of_ordLeq by blast
qed

lemma Cfinite_cprod_Cinfinite: "\<lbrakk>Cfinite r; Cinfinite s\<rbrakk> \<Longrightarrow> r *c s \<le>o s"
  by (intro cprod_cinfinite_bound)
    (auto intro: ordLeq_refl ordLess_imp_ordLeq[OF Cfinite_ordLess_Cinfinite])

lemma cprod_cexp: "(r *c s) ^c t =o r ^c t *c s ^c t"
  unfolding cprod_def cexp_def Field_card_of by (rule Func_Times_Range)

lemma cprod_cexp_csum_cexp_Cinfinite:
  assumes t: "Cinfinite t"
  shows "(r *c s) ^c t \<le>o (r +c s) ^c t"
proof -
  have "(r *c s) ^c t \<le>o ((r +c s) ^c ctwo) ^c t"
    by (rule cexp_mono1[OF cprod_csum_cexp conjunct2[OF t]])
  also have "((r +c s) ^c ctwo) ^c t =o (r +c s) ^c (ctwo *c t)"
    by (rule cexp_cprod[OF Card_order_csum])
  also have "(r +c s) ^c (ctwo *c t) =o (r +c s) ^c (t *c ctwo)"
    by (rule cexp_cong2[OF cprod_com Card_order_csum Card_order_cprod])
  also have "(r +c s) ^c (t *c ctwo) =o ((r +c s) ^c t) ^c ctwo"
    by (rule ordIso_symmetric[OF cexp_cprod[OF Card_order_csum]])
  also have "((r +c s) ^c t) ^c ctwo =o (r +c s) ^c t"
    by (rule cexp_cprod_ordLeq[OF Card_order_csum t ctwo_Cnotzero ctwo_ordLeq_Cinfinite[OF t]])
  finally show ?thesis .
qed

lemma Cfinite_cexp_Cinfinite:
  assumes s: "Cfinite s" and t: "Cinfinite t"
  shows "s ^c t \<le>o ctwo ^c t"
proof (cases "s \<le>o ctwo")
  case True thus ?thesis using t by (blast intro: cexp_mono1)
next
  case False
  hence "ctwo \<le>o s" using ordLeq_total[of s ctwo] Card_order_ctwo s
    by (auto intro: card_order_on_well_order_on)
  hence "Cnotzero s" using Cnotzero_mono[OF ctwo_Cnotzero] s by blast
  hence st: "Cnotzero (s *c t)" by (intro Cinfinite_Cnotzero[OF Cinfinite_cprod2]) (auto simp: t)
  have "s ^c t \<le>o (ctwo ^c s) ^c t"
    using assms by (blast intro: cexp_mono1 ordLess_imp_ordLeq[OF ordLess_ctwo_cexp])
  also have "(ctwo ^c s) ^c t =o ctwo ^c (s *c t)"
    by (blast intro: Card_order_ctwo cexp_cprod)
  also have "ctwo ^c (s *c t) \<le>o ctwo ^c t"
    using assms st by (intro cexp_mono2_Cnotzero Cfinite_cprod_Cinfinite Card_order_ctwo)
  finally show ?thesis .
qed

lemma csum_Cfinite_cexp_Cinfinite:
  assumes r: "Card_order r" and s: "Cfinite s" and t: "Cinfinite t"
  shows "(r +c s) ^c t \<le>o (r +c ctwo) ^c t"
proof (cases "Cinfinite r")
  case True
  hence "r +c s =o r" by (intro csum_absorb1 ordLess_imp_ordLeq[OF Cfinite_ordLess_Cinfinite] s)
  hence "(r +c s) ^c t =o r ^c t" using t by (blast intro: cexp_cong1)
  also have "r ^c t \<le>o (r +c ctwo) ^c t" using t by (blast intro: cexp_mono1 ordLeq_csum1 r)
  finally show ?thesis .
next
  case False
  with r have "Cfinite r" unfolding cinfinite_def cfinite_def by auto
  hence "Cfinite (r +c s)" by (intro Cfinite_csum s)
  hence "(r +c s) ^c t \<le>o ctwo ^c t" by (intro Cfinite_cexp_Cinfinite t)
  also have "ctwo ^c t \<le>o (r +c ctwo) ^c t" using t
    by (blast intro: cexp_mono1 ordLeq_csum2 Card_order_ctwo)
  finally show ?thesis .
qed

(* cardSuc *)

lemma Cinfinite_cardSuc: "Cinfinite r \<Longrightarrow> Cinfinite (cardSuc r)"
  by (simp add: cinfinite_def cardSuc_Card_order cardSuc_finite)

lemma cardSuc_UNION_Cinfinite:
  assumes "Cinfinite r" "relChain (cardSuc r) As" "B \<le> (\<Union>i \<in> Field (cardSuc r). As i)" "|B| <=o r"
  shows "\<exists>i \<in> Field (cardSuc r). B \<le> As i"
  using cardSuc_UNION assms unfolding cinfinite_def by blast

lemma Cinfinite_card_suc: "\<lbrakk> Cinfinite r ; card_order r \<rbrakk> \<Longrightarrow> Cinfinite (card_suc r)"
  using Cinfinite_cong[OF cardSuc_ordIso_card_suc Cinfinite_cardSuc] .

lemma card_suc_least: "\<lbrakk>card_order r; Card_order s; r <o s\<rbrakk> \<Longrightarrow> card_suc r \<le>o s"
  by (rule ordIso_ordLeq_trans[OF ordIso_symmetric[OF cardSuc_ordIso_card_suc]])
    (auto intro!: cardSuc_least simp: card_order_on_Card_order)

lemma regularCard_cardSuc: "Cinfinite k \<Longrightarrow> regularCard (cardSuc k)"
  by (rule infinite_cardSuc_regularCard) (auto simp: cinfinite_def)

lemma regularCard_card_suc: "card_order r \<Longrightarrow> Cinfinite r \<Longrightarrow> regularCard (card_suc r)"
  using cardSuc_ordIso_card_suc Cinfinite_cardSuc regularCard_cardSuc regularCard_ordIso
  by blast

end
