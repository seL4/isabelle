(*  Title:      HOL/Cardinals/Cardinal_Order_Relation.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Cardinal-order relations.
*)

header {* Cardinal-Order Relations *}

theory Cardinal_Order_Relation
imports Cardinal_Order_Relation_Base Constructions_on_Wellorders
begin

declare
  card_order_on_well_order_on[simp]
  card_of_card_order_on[simp]
  card_of_well_order_on[simp]
  Field_card_of[simp]
  card_of_Card_order[simp]
  card_of_Well_order[simp]
  card_of_least[simp]
  card_of_unique[simp]
  card_of_mono1[simp]
  card_of_mono2[simp]
  card_of_cong[simp]
  card_of_Field_ordLess[simp]
  card_of_Field_ordIso[simp]
  card_of_underS[simp]
  ordLess_Field[simp]
  card_of_empty[simp]
  card_of_empty1[simp]
  card_of_image[simp]
  card_of_singl_ordLeq[simp]
  Card_order_singl_ordLeq[simp]
  card_of_Pow[simp]
  Card_order_Pow[simp]
  card_of_set_type[simp]
  card_of_Plus1[simp]
  Card_order_Plus1[simp]
  card_of_Plus2[simp]
  Card_order_Plus2[simp]
  card_of_Plus_mono1[simp]
  card_of_Plus_mono2[simp]
  card_of_Plus_mono[simp]
  card_of_Plus_cong2[simp]
  card_of_Plus_cong[simp]
  card_of_Un1[simp]
  card_of_diff[simp]
  card_of_Un_Plus_ordLeq[simp]
  card_of_Times1[simp]
  card_of_Times2[simp]
  card_of_Times3[simp]
  card_of_Times_mono1[simp]
  card_of_Times_mono2[simp]
  card_of_Times_cong1[simp]
  card_of_Times_cong2[simp]
  card_of_ordIso_finite[simp]
  finite_ordLess_infinite2[simp]
  card_of_Times_same_infinite[simp]
  card_of_Times_infinite_simps[simp]
  card_of_Plus_infinite1[simp]
  card_of_Plus_infinite2[simp]
  card_of_Plus_ordLess_infinite[simp]
  card_of_Plus_ordLess_infinite_Field[simp]
  card_of_lists_infinite[simp]
  infinite_cartesian_product[simp]
  cardSuc_Card_order[simp]
  cardSuc_greater[simp]
  cardSuc_ordLeq[simp]
  cardSuc_ordLeq_ordLess[simp]
  cardSuc_mono_ordLeq[simp]
  cardSuc_invar_ordIso[simp]
  card_of_cardSuc_finite[simp]
  cardSuc_finite[simp]
  card_of_Plus_ordLeq_infinite_Field[simp]
  curr_in[intro, simp]
  Func_empty[simp]
  Func_map_empty[simp]
  Func_is_emp[simp]


subsection {* Cardinal of a set *}

lemma card_of_inj_rel: assumes INJ: "!! x y y'. \<lbrakk>(x,y) : R; (x,y') : R\<rbrakk> \<Longrightarrow> y = y'"
shows "|{y. EX x. (x,y) : R}| <=o |{x. EX y. (x,y) : R}|"
proof-
  let ?Y = "{y. EX x. (x,y) : R}"  let ?X = "{x. EX y. (x,y) : R}"
  let ?f = "% y. SOME x. (x,y) : R"
  have "?f ` ?Y <= ?X" using someI by force (* FIXME: takes a bit long *)
  moreover have "inj_on ?f ?Y"
  unfolding inj_on_def proof(auto)
    fix y1 x1 y2 x2
    assume *: "(x1, y1) \<in> R" "(x2, y2) \<in> R" and **: "?f y1 = ?f y2"
    hence "(?f y1,y1) : R" using someI[of "% x. (x,y1) : R"] by auto
    moreover have "(?f y2,y2) : R" using * someI[of "% x. (x,y2) : R"] by auto
    ultimately show "y1 = y2" using ** INJ by auto
  qed
  ultimately show "|?Y| <=o |?X|" using card_of_ordLeq by blast
qed

lemma card_of_unique2: "\<lbrakk>card_order_on B r; bij_betw f A B\<rbrakk> \<Longrightarrow> r =o |A|"
using card_of_ordIso card_of_unique ordIso_equivalence by blast

lemma internalize_card_of_ordLess:
"( |A| <o r) = (\<exists>B < Field r. |A| =o |B| \<and> |B| <o r)"
proof
  assume "|A| <o r"
  then obtain p where 1: "Field p < Field r \<and> |A| =o p \<and> p <o r"
  using internalize_ordLess[of "|A|" r] by blast
  hence "Card_order p" using card_of_Card_order Card_order_ordIso2 by blast
  hence "|Field p| =o p" using card_of_Field_ordIso by blast
  hence "|A| =o |Field p| \<and> |Field p| <o r"
  using 1 ordIso_equivalence ordIso_ordLess_trans by blast
  thus "\<exists>B < Field r. |A| =o |B| \<and> |B| <o r" using 1 by blast
next
  assume "\<exists>B < Field r. |A| =o |B| \<and> |B| <o r"
  thus "|A| <o r" using ordIso_ordLess_trans by blast
qed

lemma internalize_card_of_ordLess2:
"( |A| <o |C| ) = (\<exists>B < C. |A| =o |B| \<and> |B| <o |C| )"
using internalize_card_of_ordLess[of "A" "|C|"] Field_card_of[of C] by auto

lemma Card_order_omax:
assumes "finite R" and "R \<noteq> {}" and "\<forall>r\<in>R. Card_order r"
shows "Card_order (omax R)"
proof-
  have "\<forall>r\<in>R. Well_order r"
  using assms unfolding card_order_on_def by simp
  thus ?thesis using assms apply - apply(drule omax_in) by auto
qed

lemma Card_order_omax2:
assumes "finite I" and "I \<noteq> {}"
shows "Card_order (omax {|A i| | i. i \<in> I})"
proof-
  let ?R = "{|A i| | i. i \<in> I}"
  have "finite ?R" and "?R \<noteq> {}" using assms by auto
  moreover have "\<forall>r\<in>?R. Card_order r"
  using card_of_Card_order by auto
  ultimately show ?thesis by(rule Card_order_omax)
qed


subsection {* Cardinals versus set operations on arbitrary sets *}

lemma subset_ordLeq_strict:
assumes "A \<le> B" and "|A| <o |B|"
shows "A < B"
proof-
  {assume "\<not>(A < B)"
   hence "A = B" using assms(1) by blast
   hence False using assms(2) not_ordLess_ordIso card_of_refl by blast
  }
  thus ?thesis by blast
qed

corollary subset_ordLeq_diff:
assumes "A \<le> B" and "|A| <o |B|"
shows "B - A \<noteq> {}"
using assms subset_ordLeq_strict by blast

lemma card_of_empty4:
"|{}::'b set| <o |A::'a set| = (A \<noteq> {})"
proof(intro iffI notI)
  assume *: "|{}::'b set| <o |A|" and "A = {}"
  hence "|A| =o |{}::'b set|"
  using card_of_ordIso unfolding bij_betw_def inj_on_def by blast
  hence "|{}::'b set| =o |A|" using ordIso_symmetric by blast
  with * show False using not_ordLess_ordIso[of "|{}::'b set|" "|A|"] by blast
next
  assume "A \<noteq> {}"
  hence "(\<not> (\<exists>f. inj_on f A \<and> f ` A \<subseteq> {}))"
  unfolding inj_on_def by blast
  thus "| {} | <o | A |"
  using card_of_ordLess by blast
qed

lemma card_of_empty5:
"|A| <o |B| \<Longrightarrow> B \<noteq> {}"
using card_of_empty not_ordLess_ordLeq by blast

lemma Well_order_card_of_empty:
"Well_order r \<Longrightarrow> |{}| \<le>o r" by simp

lemma card_of_UNIV[simp]:
"|A :: 'a set| \<le>o |UNIV :: 'a set|"
using card_of_mono1[of A] by simp

lemma card_of_UNIV2[simp]:
"Card_order r \<Longrightarrow> (r :: 'a rel) \<le>o |UNIV :: 'a set|"
using card_of_UNIV[of "Field r"] card_of_Field_ordIso
      ordIso_symmetric ordIso_ordLeq_trans by blast

lemma card_of_Pow_mono[simp]:
assumes "|A| \<le>o |B|"
shows "|Pow A| \<le>o |Pow B|"
proof-
  obtain f where "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A B] by auto
  hence "inj_on (image f) (Pow A) \<and> (image f) ` (Pow A) \<le> (Pow B)"
  by (auto simp add: inj_on_image_Pow image_Pow_mono)
  thus ?thesis using card_of_ordLeq[of "Pow A"] by metis
qed

lemma ordIso_Pow_mono[simp]:
assumes "r \<le>o r'"
shows "|Pow(Field r)| \<le>o |Pow(Field r')|"
using assms card_of_mono2 card_of_Pow_mono by blast

lemma card_of_Pow_cong[simp]:
assumes "|A| =o |B|"
shows "|Pow A| =o |Pow B|"
proof-
  obtain f where "bij_betw f A B"
  using assms card_of_ordIso[of A B] by auto
  hence "bij_betw (image f) (Pow A) (Pow B)"
  by (auto simp add: bij_betw_image_Pow)
  thus ?thesis using card_of_ordIso[of "Pow A"] by auto
qed

lemma ordIso_Pow_cong[simp]:
assumes "r =o r'"
shows "|Pow(Field r)| =o |Pow(Field r')|"
using assms card_of_cong card_of_Pow_cong by blast

corollary Card_order_Plus_empty1:
"Card_order r \<Longrightarrow> r =o |(Field r) <+> {}|"
using card_of_Plus_empty1 card_of_Field_ordIso ordIso_equivalence by blast

corollary Card_order_Plus_empty2:
"Card_order r \<Longrightarrow> r =o |{} <+> (Field r)|"
using card_of_Plus_empty2 card_of_Field_ordIso ordIso_equivalence by blast

lemma Card_order_Un1:
shows "Card_order r \<Longrightarrow> |Field r| \<le>o |(Field r) \<union> B| "
using card_of_Un1 card_of_Field_ordIso ordIso_symmetric ordIso_ordLeq_trans by auto

lemma card_of_Un2[simp]:
shows "|A| \<le>o |B \<union> A|"
using inj_on_id[of A] card_of_ordLeq[of A _] by fastforce

lemma Card_order_Un2:
shows "Card_order r \<Longrightarrow> |Field r| \<le>o |A \<union> (Field r)| "
using card_of_Un2 card_of_Field_ordIso ordIso_symmetric ordIso_ordLeq_trans by auto

lemma Un_Plus_bij_betw:
assumes "A Int B = {}"
shows "\<exists>f. bij_betw f (A \<union> B) (A <+> B)"
proof-
  let ?f = "\<lambda> c. if c \<in> A then Inl c else Inr c"
  have "bij_betw ?f (A \<union> B) (A <+> B)"
  using assms by(unfold bij_betw_def inj_on_def, auto)
  thus ?thesis by blast
qed

lemma card_of_Un_Plus_ordIso:
assumes "A Int B = {}"
shows "|A \<union> B| =o |A <+> B|"
using assms card_of_ordIso[of "A \<union> B"] Un_Plus_bij_betw[of A B] by auto

lemma card_of_Un_Plus_ordIso1:
"|A \<union> B| =o |A <+> (B - A)|"
using card_of_Un_Plus_ordIso[of A "B - A"] by auto

lemma card_of_Un_Plus_ordIso2:
"|A \<union> B| =o |(A - B) <+> B|"
using card_of_Un_Plus_ordIso[of "A - B" B] by auto

lemma card_of_Times_singl1: "|A| =o |A \<times> {b}|"
proof-
  have "bij_betw fst (A \<times> {b}) A" unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed

corollary Card_order_Times_singl1:
"Card_order r \<Longrightarrow> r =o |(Field r) \<times> {b}|"
using card_of_Times_singl1[of _ b] card_of_Field_ordIso ordIso_equivalence by blast

lemma card_of_Times_singl2: "|A| =o |{b} \<times> A|"
proof-
  have "bij_betw snd ({b} \<times> A) A" unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed

corollary Card_order_Times_singl2:
"Card_order r \<Longrightarrow> r =o |{a} \<times> (Field r)|"
using card_of_Times_singl2[of _ a] card_of_Field_ordIso ordIso_equivalence by blast

lemma card_of_Times_assoc: "|(A \<times> B) \<times> C| =o |A \<times> B \<times> C|"
proof -
  let ?f = "\<lambda>((a,b),c). (a,(b,c))"
  have "A \<times> B \<times> C \<subseteq> ?f ` ((A \<times> B) \<times> C)"
  proof
    fix x assume "x \<in> A \<times> B \<times> C"
    then obtain a b c where *: "a \<in> A" "b \<in> B" "c \<in> C" "x = (a, b, c)" by blast
    let ?x = "((a, b), c)"
    from * have "?x \<in> (A \<times> B) \<times> C" "x = ?f ?x" by auto
    thus "x \<in> ?f ` ((A \<times> B) \<times> C)" by blast
  qed
  hence "bij_betw ?f ((A \<times> B) \<times> C) (A \<times> B \<times> C)"
  unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed

corollary Card_order_Times3:
"Card_order r \<Longrightarrow> |Field r| \<le>o |(Field r) \<times> (Field r)|"
using card_of_Times3 card_of_Field_ordIso
      ordIso_ordLeq_trans ordIso_symmetric by blast

lemma card_of_Times_mono[simp]:
assumes "|A| \<le>o |B|" and "|C| \<le>o |D|"
shows "|A \<times> C| \<le>o |B \<times> D|"
using assms card_of_Times_mono1[of A B C] card_of_Times_mono2[of C D B]
      ordLeq_transitive[of "|A \<times> C|"] by blast

corollary ordLeq_Times_mono:
assumes "r \<le>o r'" and "p \<le>o p'"
shows "|(Field r) \<times> (Field p)| \<le>o |(Field r') \<times> (Field p')|"
using assms card_of_mono2[of r r'] card_of_mono2[of p p'] card_of_Times_mono by blast

corollary ordIso_Times_cong1[simp]:
assumes "r =o r'"
shows "|(Field r) \<times> C| =o |(Field r') \<times> C|"
using assms card_of_cong card_of_Times_cong1 by blast

lemma card_of_Times_cong[simp]:
assumes "|A| =o |B|" and "|C| =o |D|"
shows "|A \<times> C| =o |B \<times> D|"
using assms
by (auto simp add: ordIso_iff_ordLeq)

corollary ordIso_Times_cong:
assumes "r =o r'" and "p =o p'"
shows "|(Field r) \<times> (Field p)| =o |(Field r') \<times> (Field p')|"
using assms card_of_cong[of r r'] card_of_cong[of p p'] card_of_Times_cong by blast

lemma card_of_Sigma_mono2:
assumes "inj_on f (I::'i set)" and "f ` I \<le> (J::'j set)"
shows "|SIGMA i : I. (A::'j \<Rightarrow> 'a set) (f i)| \<le>o |SIGMA j : J. A j|"
proof-
  let ?LEFT = "SIGMA i : I. A (f i)"
  let ?RIGHT = "SIGMA j : J. A j"
  obtain u where u_def: "u = (\<lambda>(i::'i,a::'a). (f i,a))" by blast
  have "inj_on u ?LEFT \<and> u `?LEFT \<le> ?RIGHT"
  using assms unfolding u_def inj_on_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed

lemma card_of_Sigma_mono:
assumes INJ: "inj_on f I" and IM: "f ` I \<le> J" and
        LEQ: "\<forall>j \<in> J. |A j| \<le>o |B j|"
shows "|SIGMA i : I. A (f i)| \<le>o |SIGMA j : J. B j|"
proof-
  have "\<forall>i \<in> I. |A(f i)| \<le>o |B(f i)|"
  using IM LEQ by blast
  hence "|SIGMA i : I. A (f i)| \<le>o |SIGMA i : I. B (f i)|"
  using card_of_Sigma_mono1[of I] by metis
  moreover have "|SIGMA i : I. B (f i)| \<le>o |SIGMA j : J. B j|"
  using INJ IM card_of_Sigma_mono2 by blast
  ultimately show ?thesis using ordLeq_transitive by blast
qed


lemma ordLeq_Sigma_mono1:
assumes "\<forall>i \<in> I. p i \<le>o r i"
shows "|SIGMA i : I. Field(p i)| \<le>o |SIGMA i : I. Field(r i)|"
using assms by (auto simp add: card_of_Sigma_mono1)


lemma ordLeq_Sigma_mono:
assumes "inj_on f I" and "f ` I \<le> J" and
        "\<forall>j \<in> J. p j \<le>o r j"
shows "|SIGMA i : I. Field(p(f i))| \<le>o |SIGMA j : J. Field(r j)|"
using assms card_of_mono2 card_of_Sigma_mono
      [of f I J "\<lambda> i. Field(p i)" "\<lambda> j. Field(r j)"] by metis


lemma card_of_Sigma_cong1:
assumes "\<forall>i \<in> I. |A i| =o |B i|"
shows "|SIGMA i : I. A i| =o |SIGMA i : I. B i|"
using assms by (auto simp add: card_of_Sigma_mono1 ordIso_iff_ordLeq)


lemma card_of_Sigma_cong2:
assumes "bij_betw f (I::'i set) (J::'j set)"
shows "|SIGMA i : I. (A::'j \<Rightarrow> 'a set) (f i)| =o |SIGMA j : J. A j|"
proof-
  let ?LEFT = "SIGMA i : I. A (f i)"
  let ?RIGHT = "SIGMA j : J. A j"
  obtain u where u_def: "u = (\<lambda>(i::'i,a::'a). (f i,a))" by blast
  have "bij_betw u ?LEFT ?RIGHT"
  using assms unfolding u_def bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Sigma_cong:
assumes BIJ: "bij_betw f I J" and
        ISO: "\<forall>j \<in> J. |A j| =o |B j|"
shows "|SIGMA i : I. A (f i)| =o |SIGMA j : J. B j|"
proof-
  have "\<forall>i \<in> I. |A(f i)| =o |B(f i)|"
  using ISO BIJ unfolding bij_betw_def by blast
  hence "|SIGMA i : I. A (f i)| =o |SIGMA i : I. B (f i)|"
  using card_of_Sigma_cong1 by metis
  moreover have "|SIGMA i : I. B (f i)| =o |SIGMA j : J. B j|"
  using BIJ card_of_Sigma_cong2 by blast
  ultimately show ?thesis using ordIso_transitive by blast
qed

lemma ordIso_Sigma_cong1:
assumes "\<forall>i \<in> I. p i =o r i"
shows "|SIGMA i : I. Field(p i)| =o |SIGMA i : I. Field(r i)|"
using assms by (auto simp add: card_of_Sigma_cong1)

lemma ordLeq_Sigma_cong:
assumes "bij_betw f I J" and
        "\<forall>j \<in> J. p j =o r j"
shows "|SIGMA i : I. Field(p(f i))| =o |SIGMA j : J. Field(r j)|"
using assms card_of_cong card_of_Sigma_cong
      [of f I J "\<lambda> j. Field(p j)" "\<lambda> j. Field(r j)"] by blast

corollary ordLeq_Sigma_Times:
"\<forall>i \<in> I. p i \<le>o r \<Longrightarrow> |SIGMA i : I. Field (p i)| \<le>o |I \<times> (Field r)|"
by (auto simp add: card_of_Sigma_Times)

lemma card_of_UNION_Sigma2:
assumes
"!! i j. \<lbrakk>{i,j} <= I; i ~= j\<rbrakk> \<Longrightarrow> A i Int A j = {}"
shows
"|\<Union>i\<in>I. A i| =o |Sigma I A|"
proof-
  let ?L = "\<Union>i\<in>I. A i"  let ?R = "Sigma I A"
  have "|?L| <=o |?R|" using card_of_UNION_Sigma .
  moreover have "|?R| <=o |?L|"
  proof-
    have "inj_on snd ?R"
    unfolding inj_on_def using assms by auto
    moreover have "snd ` ?R <= ?L" by auto
    ultimately show ?thesis using card_of_ordLeq by blast
  qed
  ultimately show ?thesis by(simp add: ordIso_iff_ordLeq)
qed

corollary Plus_into_Times:
assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and
        B2: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B"
shows "\<exists>f. inj_on f (A <+> B) \<and> f ` (A <+> B) \<le> A \<times> B"
using assms by (auto simp add: card_of_Plus_Times card_of_ordLeq)

corollary Plus_into_Times_types:
assumes A2: "(a1::'a) \<noteq> a2" and  B2: "(b1::'b) \<noteq> b2"
shows "\<exists>(f::'a + 'b \<Rightarrow> 'a * 'b). inj f"
using assms Plus_into_Times[of a1 a2 UNIV b1 b2 UNIV]
by auto

corollary Times_same_infinite_bij_betw:
assumes "infinite A"
shows "\<exists>f. bij_betw f (A \<times> A) A"
using assms by (auto simp add: card_of_ordIso)

corollary Times_same_infinite_bij_betw_types:
assumes INF: "infinite(UNIV::'a set)"
shows "\<exists>(f::('a * 'a) => 'a). bij f"
using assms Times_same_infinite_bij_betw[of "UNIV::'a set"]
by auto

corollary Times_infinite_bij_betw:
assumes INF: "infinite A" and NE: "B \<noteq> {}" and INJ: "inj_on g B \<and> g ` B \<le> A"
shows "(\<exists>f. bij_betw f (A \<times> B) A) \<and> (\<exists>h. bij_betw h (B \<times> A) A)"
proof-
  have "|B| \<le>o |A|" using INJ card_of_ordLeq by blast
  thus ?thesis using INF NE
  by (auto simp add: card_of_ordIso card_of_Times_infinite)
qed

corollary Times_infinite_bij_betw_types:
assumes INF: "infinite(UNIV::'a set)" and
        BIJ: "inj(g::'b \<Rightarrow> 'a)"
shows "(\<exists>(f::('b * 'a) => 'a). bij f) \<and> (\<exists>(h::('a * 'b) => 'a). bij h)"
using assms Times_infinite_bij_betw[of "UNIV::'a set" "UNIV::'b set" g]
by auto

lemma card_of_Times_ordLeq_infinite:
"\<lbrakk>infinite C; |A| \<le>o |C|; |B| \<le>o |C|\<rbrakk>
 \<Longrightarrow> |A <*> B| \<le>o |C|"
by(simp add: card_of_Sigma_ordLeq_infinite)

corollary Plus_infinite_bij_betw:
assumes INF: "infinite A" and INJ: "inj_on g B \<and> g ` B \<le> A"
shows "(\<exists>f. bij_betw f (A <+> B) A) \<and> (\<exists>h. bij_betw h (B <+> A) A)"
proof-
  have "|B| \<le>o |A|" using INJ card_of_ordLeq by blast
  thus ?thesis using INF
  by (auto simp add: card_of_ordIso)
qed

corollary Plus_infinite_bij_betw_types:
assumes INF: "infinite(UNIV::'a set)" and
        BIJ: "inj(g::'b \<Rightarrow> 'a)"
shows "(\<exists>(f::('b + 'a) => 'a). bij f) \<and> (\<exists>(h::('a + 'b) => 'a). bij h)"
using assms Plus_infinite_bij_betw[of "UNIV::'a set" g "UNIV::'b set"]
by auto

lemma card_of_Un_infinite_simps[simp]:
"\<lbrakk>infinite A; |B| \<le>o |A| \<rbrakk> \<Longrightarrow> |A \<union> B| =o |A|"
"\<lbrakk>infinite A; |B| \<le>o |A| \<rbrakk> \<Longrightarrow> |B \<union> A| =o |A|"
using card_of_Un_infinite by auto

corollary Card_order_Un_infinite:
assumes INF: "infinite(Field r)" and CARD: "Card_order r" and
        LEQ: "p \<le>o r"
shows "| (Field r) \<union> (Field p) | =o r \<and> | (Field p) \<union> (Field r) | =o r"
proof-
  have "| Field r \<union> Field p | =o | Field r | \<and>
        | Field p \<union> Field r | =o | Field r |"
  using assms by (auto simp add: card_of_Un_infinite)
  thus ?thesis
  using assms card_of_Field_ordIso[of r]
        ordIso_transitive[of "|Field r \<union> Field p|"]
        ordIso_transitive[of _ "|Field r|"] by blast
qed

corollary subset_ordLeq_diff_infinite:
assumes INF: "infinite B" and SUB: "A \<le> B" and LESS: "|A| <o |B|"
shows "infinite (B - A)"
using assms card_of_Un_diff_infinite card_of_ordIso_finite by blast

lemma card_of_Times_ordLess_infinite[simp]:
assumes INF: "infinite C" and
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A \<times> B| <o |C|"
proof(cases "A = {} \<or> B = {}")
  assume Case1: "A = {} \<or> B = {}"
  hence "A \<times> B = {}" by blast
  moreover have "C \<noteq> {}" using
  LESS1 card_of_empty5 by blast
  ultimately show ?thesis by(auto simp add:  card_of_empty4)
next
  assume Case2: "\<not>(A = {} \<or> B = {})"
  {assume *: "|C| \<le>o |A \<times> B|"
   hence "infinite (A \<times> B)" using INF card_of_ordLeq_finite by blast
   hence 1: "infinite A \<or> infinite B" using finite_cartesian_product by blast
   {assume Case21: "|A| \<le>o |B|"
    hence "infinite B" using 1 card_of_ordLeq_finite by blast
    hence "|A \<times> B| =o |B|" using Case2 Case21
    by (auto simp add: card_of_Times_infinite)
    hence False using LESS2 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   moreover
   {assume Case22: "|B| \<le>o |A|"
    hence "infinite A" using 1 card_of_ordLeq_finite by blast
    hence "|A \<times> B| =o |A|" using Case2 Case22
    by (auto simp add: card_of_Times_infinite)
    hence False using LESS1 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   ultimately have False using ordLeq_total card_of_Well_order[of A]
   card_of_Well_order[of B] by blast
  }
  thus ?thesis using ordLess_or_ordLeq[of "|A \<times> B|" "|C|"]
  card_of_Well_order[of "A \<times> B"] card_of_Well_order[of "C"] by auto
qed

lemma card_of_Times_ordLess_infinite_Field[simp]:
assumes INF: "infinite (Field r)" and r: "Card_order r" and
        LESS1: "|A| <o r" and LESS2: "|B| <o r"
shows "|A \<times> B| <o r"
proof-
  let ?C  = "Field r"
  have 1: "r =o |?C| \<and> |?C| =o r" using r card_of_Field_ordIso
  ordIso_symmetric by blast
  hence "|A| <o |?C|"  "|B| <o |?C|"
  using LESS1 LESS2 ordLess_ordIso_trans by blast+
  hence  "|A <*> B| <o |?C|" using INF
  card_of_Times_ordLess_infinite by blast
  thus ?thesis using 1 ordLess_ordIso_trans by blast
qed

lemma card_of_Un_ordLess_infinite[simp]:
assumes INF: "infinite C" and
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A \<union> B| <o |C|"
using assms card_of_Plus_ordLess_infinite card_of_Un_Plus_ordLeq
      ordLeq_ordLess_trans by blast

lemma card_of_Un_ordLess_infinite_Field[simp]:
assumes INF: "infinite (Field r)" and r: "Card_order r" and
        LESS1: "|A| <o r" and LESS2: "|B| <o r"
shows "|A Un B| <o r"
proof-
  let ?C  = "Field r"
  have 1: "r =o |?C| \<and> |?C| =o r" using r card_of_Field_ordIso
  ordIso_symmetric by blast
  hence "|A| <o |?C|"  "|B| <o |?C|"
  using LESS1 LESS2 ordLess_ordIso_trans by blast+
  hence  "|A Un B| <o |?C|" using INF
  card_of_Un_ordLess_infinite by blast
  thus ?thesis using 1 ordLess_ordIso_trans by blast
qed

lemma card_of_Un_singl_ordLess_infinite1:
assumes "infinite B" and "|A| <o |B|"
shows "|{a} Un A| <o |B|"
proof-
  have "|{a}| <o |B|" using assms by auto
  thus ?thesis using assms card_of_Un_ordLess_infinite[of B] by fastforce
qed

lemma card_of_Un_singl_ordLess_infinite:
assumes "infinite B"
shows "( |A| <o |B| ) = ( |{a} Un A| <o |B| )"
using assms card_of_Un_singl_ordLess_infinite1[of B A]
proof(auto)
  assume "|insert a A| <o |B|"
  moreover have "|A| <=o |insert a A|" using card_of_mono1[of A] by blast
  ultimately show "|A| <o |B|" using ordLeq_ordLess_trans by blast
qed


subsection {* Cardinals versus lists  *}

lemma Card_order_lists: "Card_order r \<Longrightarrow> r \<le>o |lists(Field r) |"
using card_of_lists card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast

lemma Union_set_lists:
"Union(set ` (lists A)) = A"
unfolding lists_def2 proof(auto)
  fix a assume "a \<in> A"
  hence "set [a] \<le> A \<and> a \<in> set [a]" by auto
  thus "\<exists>l. set l \<le> A \<and> a \<in> set l" by blast
qed

lemma inj_on_map_lists:
assumes "inj_on f A"
shows "inj_on (map f) (lists A)"
using assms Union_set_lists[of A] inj_on_mapI[of f "lists A"] by auto

lemma map_lists_mono:
assumes "f ` A \<le> B"
shows "(map f) ` (lists A) \<le> lists B"
using assms unfolding lists_def2 by (auto, blast) (* lethal combination of methods :)  *)

lemma map_lists_surjective:
assumes "f ` A = B"
shows "(map f) ` (lists A) = lists B"
using assms unfolding lists_def2
proof (auto, blast)
  fix l' assume *: "set l' \<le> f ` A"
  have "set l' \<le> f ` A \<longrightarrow> l' \<in> map f ` {l. set l \<le> A}"
  proof(induct l', auto)
    fix l a
    assume "a \<in> A" and "set l \<le> A" and
           IH: "f ` (set l) \<le> f ` A"
    hence "set (a # l) \<le> A" by auto
    hence "map f (a # l) \<in> map f ` {l. set l \<le> A}" by blast
    thus "f a # map f l \<in> map f ` {l. set l \<le> A}" by auto
  qed
  thus "l' \<in> map f ` {l. set l \<le> A}" using * by auto
qed

lemma bij_betw_map_lists:
assumes "bij_betw f A B"
shows "bij_betw (map f) (lists A) (lists B)"
using assms unfolding bij_betw_def
by(auto simp add: inj_on_map_lists map_lists_surjective)

lemma card_of_lists_mono[simp]:
assumes "|A| \<le>o |B|"
shows "|lists A| \<le>o |lists B|"
proof-
  obtain f where "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A B] by auto
  hence "inj_on (map f) (lists A) \<and> (map f) ` (lists A) \<le> (lists B)"
  by (auto simp add: inj_on_map_lists map_lists_mono)
  thus ?thesis using card_of_ordLeq[of "lists A"] by metis
qed

lemma ordIso_lists_mono:
assumes "r \<le>o r'"
shows "|lists(Field r)| \<le>o |lists(Field r')|"
using assms card_of_mono2 card_of_lists_mono by blast

lemma card_of_lists_cong[simp]:
assumes "|A| =o |B|"
shows "|lists A| =o |lists B|"
proof-
  obtain f where "bij_betw f A B"
  using assms card_of_ordIso[of A B] by auto
  hence "bij_betw (map f) (lists A) (lists B)"
  by (auto simp add: bij_betw_map_lists)
  thus ?thesis using card_of_ordIso[of "lists A"] by auto
qed

lemma ordIso_lists_cong:
assumes "r =o r'"
shows "|lists(Field r)| =o |lists(Field r')|"
using assms card_of_cong card_of_lists_cong by blast

corollary lists_infinite_bij_betw:
assumes "infinite A"
shows "\<exists>f. bij_betw f (lists A) A"
using assms card_of_lists_infinite card_of_ordIso by blast

corollary lists_infinite_bij_betw_types:
assumes "infinite(UNIV :: 'a set)"
shows "\<exists>(f::'a list \<Rightarrow> 'a). bij f"
using assms assms lists_infinite_bij_betw[of "UNIV::'a set"]
using lists_UNIV by auto


subsection {* Cardinals versus the set-of-finite-sets operator  *}

definition Fpow :: "'a set \<Rightarrow> 'a set set"
where "Fpow A \<equiv> {X. X \<le> A \<and> finite X}"

lemma Fpow_mono: "A \<le> B \<Longrightarrow> Fpow A \<le> Fpow B"
unfolding Fpow_def by auto

lemma empty_in_Fpow: "{} \<in> Fpow A"
unfolding Fpow_def by auto

lemma Fpow_not_empty: "Fpow A \<noteq> {}"
using empty_in_Fpow by blast

lemma Fpow_subset_Pow: "Fpow A \<le> Pow A"
unfolding Fpow_def by auto

lemma card_of_Fpow[simp]: "|A| \<le>o |Fpow A|"
proof-
  let ?h = "\<lambda> a. {a}"
  have "inj_on ?h A \<and> ?h ` A \<le> Fpow A"
  unfolding inj_on_def Fpow_def by auto
  thus ?thesis using card_of_ordLeq by metis
qed

lemma Card_order_Fpow: "Card_order r \<Longrightarrow> r \<le>o |Fpow(Field r) |"
using card_of_Fpow card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast

lemma Fpow_Pow_finite: "Fpow A = Pow A Int {A. finite A}"
unfolding Fpow_def Pow_def by blast

lemma inj_on_image_Fpow:
assumes "inj_on f A"
shows "inj_on (image f) (Fpow A)"
using assms Fpow_subset_Pow[of A] subset_inj_on[of "image f" "Pow A"]
      inj_on_image_Pow by blast

lemma image_Fpow_mono:
assumes "f ` A \<le> B"
shows "(image f) ` (Fpow A) \<le> Fpow B"
using assms by(unfold Fpow_def, auto)

lemma image_Fpow_surjective:
assumes "f ` A = B"
shows "(image f) ` (Fpow A) = Fpow B"
using assms proof(unfold Fpow_def, auto)
  fix Y assume *: "Y \<le> f ` A" and **: "finite Y"
  hence "\<forall>b \<in> Y. \<exists>a. a \<in> A \<and> f a = b" by auto
  with bchoice[of Y "\<lambda>b a. a \<in> A \<and> f a = b"]
  obtain g where 1: "\<forall>b \<in> Y. g b \<in> A \<and> f(g b) = b" by blast
  obtain X where X_def: "X = g ` Y" by blast
  have "f ` X = Y \<and> X \<le> A \<and> finite X"
  by(unfold X_def, force simp add: ** 1)
  thus "Y \<in> (image f) ` {X. X \<le> A \<and> finite X}" by auto
qed

lemma bij_betw_image_Fpow:
assumes "bij_betw f A B"
shows "bij_betw (image f) (Fpow A) (Fpow B)"
using assms unfolding bij_betw_def
by (auto simp add: inj_on_image_Fpow image_Fpow_surjective)

lemma card_of_Fpow_mono[simp]:
assumes "|A| \<le>o |B|"
shows "|Fpow A| \<le>o |Fpow B|"
proof-
  obtain f where "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A B] by auto
  hence "inj_on (image f) (Fpow A) \<and> (image f) ` (Fpow A) \<le> (Fpow B)"
  by (auto simp add: inj_on_image_Fpow image_Fpow_mono)
  thus ?thesis using card_of_ordLeq[of "Fpow A"] by auto
qed

lemma ordIso_Fpow_mono:
assumes "r \<le>o r'"
shows "|Fpow(Field r)| \<le>o |Fpow(Field r')|"
using assms card_of_mono2 card_of_Fpow_mono by blast

lemma card_of_Fpow_cong[simp]:
assumes "|A| =o |B|"
shows "|Fpow A| =o |Fpow B|"
proof-
  obtain f where "bij_betw f A B"
  using assms card_of_ordIso[of A B] by auto
  hence "bij_betw (image f) (Fpow A) (Fpow B)"
  by (auto simp add: bij_betw_image_Fpow)
  thus ?thesis using card_of_ordIso[of "Fpow A"] by auto
qed

lemma ordIso_Fpow_cong:
assumes "r =o r'"
shows "|Fpow(Field r)| =o |Fpow(Field r')|"
using assms card_of_cong card_of_Fpow_cong by blast

lemma card_of_Fpow_lists: "|Fpow A| \<le>o |lists A|"
proof-
  have "set ` (lists A) = Fpow A"
  unfolding lists_def2 Fpow_def using finite_list finite_set by blast
  thus ?thesis using card_of_ordLeq2[of "Fpow A"] Fpow_not_empty[of A] by blast
qed

lemma card_of_Fpow_infinite[simp]:
assumes "infinite A"
shows "|Fpow A| =o |A|"
using assms card_of_Fpow_lists card_of_lists_infinite card_of_Fpow
      ordLeq_ordIso_trans ordIso_iff_ordLeq by blast

corollary Fpow_infinite_bij_betw:
assumes "infinite A"
shows "\<exists>f. bij_betw f (Fpow A) A"
using assms card_of_Fpow_infinite card_of_ordIso by blast


subsection {* The cardinal $\omega$ and the finite cardinals  *}

subsubsection {* First as well-orders *}

lemma Field_natLess: "Field natLess = (UNIV::nat set)"
by(unfold Field_def, auto)

lemma natLeq_ofilter_less: "ofilter natLeq {0 ..< n}"
by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def,
   simp add:  Field_natLeq, unfold rel.under_def, auto)

lemma natLeq_ofilter_leq: "ofilter natLeq {0 .. n}"
by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def,
   simp add:  Field_natLeq, unfold rel.under_def, auto)

lemma natLeq_ofilter_iff:
"ofilter natLeq A = (A = UNIV \<or> (\<exists>n. A = {0 ..< n}))"
proof(rule iffI)
  assume "ofilter natLeq A"
  hence "\<forall>m n. n \<in> A \<and> m \<le> n \<longrightarrow> m \<in> A"
  by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def rel.under_def)
  thus "A = UNIV \<or> (\<exists>n. A = {0 ..< n})" using closed_nat_set_iff by blast
next
  assume "A = UNIV \<or> (\<exists>n. A = {0 ..< n})"
  thus "ofilter natLeq A"
  by(auto simp add: natLeq_ofilter_less natLeq_UNIV_ofilter)
qed

lemma natLeq_under_leq: "under natLeq n = {0 .. n}"
unfolding rel.under_def by auto

corollary natLeq_on_ofilter:
"ofilter(natLeq_on n) {0 ..< n}"
by (auto simp add: natLeq_on_ofilter_less_eq)

lemma natLeq_on_ofilter_less:
"n < m \<Longrightarrow> ofilter (natLeq_on m) {0 .. n}"
by(auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def,
   simp add: Field_natLeq_on, unfold rel.under_def, auto)

lemma natLeq_on_ordLess_natLeq: "natLeq_on n <o natLeq"
using Field_natLeq Field_natLeq_on[of n] nat_infinite
      finite_ordLess_infinite[of "natLeq_on n" natLeq]
      natLeq_Well_order natLeq_on_Well_order[of n] by auto

lemma natLeq_on_injective:
"natLeq_on m = natLeq_on n \<Longrightarrow> m = n"
using Field_natLeq_on[of m] Field_natLeq_on[of n]
      atLeastLessThan_injective[of m n] by auto

lemma natLeq_on_injective_ordIso:
"(natLeq_on m =o natLeq_on n) = (m = n)"
proof(auto simp add: natLeq_on_Well_order ordIso_reflexive)
  assume "natLeq_on m =o natLeq_on n"
  then obtain f where "bij_betw f {0..<m} {0..<n}"
  using Field_natLeq_on assms unfolding ordIso_def iso_def[abs_def] by auto
  thus "m = n" using atLeastLessThan_injective2 by blast
qed


subsubsection {* Then as cardinals *}

lemma ordIso_natLeq_infinite1:
"|A| =o natLeq \<Longrightarrow> infinite A"
using ordIso_symmetric ordIso_imp_ordLeq infinite_iff_natLeq_ordLeq by blast

lemma ordIso_natLeq_infinite2:
"natLeq =o |A| \<Longrightarrow> infinite A"
using ordIso_imp_ordLeq infinite_iff_natLeq_ordLeq by blast

lemma ordLeq_natLeq_on_imp_finite:
assumes "|A| \<le>o natLeq_on n"
shows "finite A"
proof-
  have "|A| \<le>o |{0 ..< n}|"
  using assms card_of_less ordIso_symmetric ordLeq_ordIso_trans by blast
  thus ?thesis by (auto simp add: card_of_ordLeq_finite)
qed


subsubsection {* "Backwards compatibility" with the numeric cardinal operator for finite sets *}

lemma finite_card_of_iff_card:
assumes FIN: "finite A" and FIN': "finite B"
shows "( |A| =o |B| ) = (card A = card B)"
using assms card_of_ordIso[of A B] bij_betw_iff_card[of A B] by blast

lemma finite_card_of_iff_card3:
assumes FIN: "finite A" and FIN': "finite B"
shows "( |A| <o |B| ) = (card A < card B)"
proof-
  have "( |A| <o |B| ) = (~ ( |B| \<le>o |A| ))" by simp
  also have "... = (~ (card B \<le> card A))"
  using assms by(simp add: finite_card_of_iff_card2)
  also have "... = (card A < card B)" by auto
  finally show ?thesis .
qed

lemma card_Field_natLeq_on:
"card(Field(natLeq_on n)) = n"
using Field_natLeq_on card_atLeastLessThan by auto


subsection {* The successor of a cardinal *}

lemma embed_implies_ordIso_Restr:
assumes WELL: "Well_order r" and WELL': "Well_order r'" and EMB: "embed r' r f"
shows "r' =o Restr r (f ` (Field r'))"
using assms embed_implies_iso_Restr Well_order_Restr unfolding ordIso_def by blast

lemma cardSuc_Well_order[simp]:
"Card_order r \<Longrightarrow> Well_order(cardSuc r)"
using cardSuc_Card_order unfolding card_order_on_def by blast

lemma Field_cardSuc_not_empty:
assumes "Card_order r"
shows "Field (cardSuc r) \<noteq> {}"
proof
  assume "Field(cardSuc r) = {}"
  hence "|Field(cardSuc r)| \<le>o r" using assms Card_order_empty[of r] by auto
  hence "cardSuc r \<le>o r" using assms card_of_Field_ordIso
  cardSuc_Card_order ordIso_symmetric ordIso_ordLeq_trans by blast
  thus False using cardSuc_greater not_ordLess_ordLeq assms by blast
qed

lemma cardSuc_mono_ordLess[simp]:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(cardSuc r <o cardSuc r') = (r <o r')"
proof-
  have 0: "Well_order r \<and> Well_order r' \<and> Well_order(cardSuc r) \<and> Well_order(cardSuc r')"
  using assms by auto
  thus ?thesis
  using not_ordLeq_iff_ordLess not_ordLeq_iff_ordLess[of r r']
  using cardSuc_mono_ordLeq[of r' r] assms by blast
qed

lemma card_of_Plus_ordLeq_infinite[simp]:
assumes C: "infinite C" and A: "|A| \<le>o |C|" and B: "|B| \<le>o |C|"
shows "|A <+> B| \<le>o |C|"
proof-
  let ?r = "cardSuc |C|"
  have "Card_order ?r \<and> infinite (Field ?r)" using assms by simp
  moreover have "|A| <o ?r" and "|B| <o ?r" using A B by auto
  ultimately have "|A <+> B| <o ?r"
  using card_of_Plus_ordLess_infinite_Field by blast
  thus ?thesis using C by simp
qed

lemma card_of_Un_ordLeq_infinite[simp]:
assumes C: "infinite C" and A: "|A| \<le>o |C|" and B: "|B| \<le>o |C|"
shows "|A Un B| \<le>o |C|"
using assms card_of_Plus_ordLeq_infinite card_of_Un_Plus_ordLeq
ordLeq_transitive by metis


subsection {* Others *}

lemma under_mono[simp]:
assumes "Well_order r" and "(i,j) \<in> r"
shows "under r i \<subseteq> under r j"
using assms unfolding rel.under_def order_on_defs
trans_def by blast

lemma underS_under:
assumes "i \<in> Field r"
shows "underS r i = under r i - {i}"
using assms unfolding rel.underS_def rel.under_def by auto

lemma relChain_under:
assumes "Well_order r"
shows "relChain r (\<lambda> i. under r i)"
using assms unfolding relChain_def by auto

lemma infinite_card_of_diff_singl:
assumes "infinite A"
shows "|A - {a}| =o |A|"
by (metis assms card_of_infinite_diff_finitte finite.emptyI finite_insert)

lemma card_of_vimage:
assumes "B \<subseteq> range f"
shows "|B| \<le>o |f -` B|"
apply(rule surj_imp_ordLeq[of _ f])
using assms by (metis Int_absorb2 image_vimage_eq order_refl)

lemma surj_card_of_vimage:
assumes "surj f"
shows "|B| \<le>o |f -` B|"
by (metis assms card_of_vimage subset_UNIV)

(* bounded powerset *)
definition Bpow where
"Bpow r A \<equiv> {X . X \<subseteq> A \<and> |X| \<le>o r}"

lemma Bpow_empty[simp]:
assumes "Card_order r"
shows "Bpow r {} = {{}}"
using assms unfolding Bpow_def by auto

lemma singl_in_Bpow:
assumes rc: "Card_order r"
and r: "Field r \<noteq> {}" and a: "a \<in> A"
shows "{a} \<in> Bpow r A"
proof-
  have "|{a}| \<le>o r" using r rc by auto
  thus ?thesis unfolding Bpow_def using a by auto
qed

lemma ordLeq_card_Bpow:
assumes rc: "Card_order r" and r: "Field r \<noteq> {}"
shows "|A| \<le>o |Bpow r A|"
proof-
  have "inj_on (\<lambda> a. {a}) A" unfolding inj_on_def by auto
  moreover have "(\<lambda> a. {a}) ` A \<subseteq> Bpow r A"
  using singl_in_Bpow[OF assms] by auto
  ultimately show ?thesis unfolding card_of_ordLeq[symmetric] by blast
qed

lemma infinite_Bpow:
assumes rc: "Card_order r" and r: "Field r \<noteq> {}"
and A: "infinite A"
shows "infinite (Bpow r A)"
using ordLeq_card_Bpow[OF rc r]
by (metis A card_of_ordLeq_infinite)

lemma Bpow_ordLeq_Func_Field:
assumes rc: "Card_order r" and r: "Field r \<noteq> {}" and A: "infinite A"
shows "|Bpow r A| \<le>o |Func (Field r) A|"
proof-
  let ?F = "\<lambda> f. {x | x a. f a = Some x}"
  {fix X assume "X \<in> Bpow r A - {{}}"
   hence XA: "X \<subseteq> A" and "|X| \<le>o r"
   and X: "X \<noteq> {}" unfolding Bpow_def by auto
   hence "|X| \<le>o |Field r|" by (metis Field_card_of card_of_mono2)
   then obtain F where 1: "X = F ` (Field r)"
   using card_of_ordLeq2[OF X] by metis
   def f \<equiv> "\<lambda> i. if i \<in> Field r then Some (F i) else None"
   have "\<exists> f \<in> Func (Field r) A. X = ?F f"
   apply (intro bexI[of _ f]) using 1 XA unfolding Func_def f_def by auto
  }
  hence "Bpow r A - {{}} \<subseteq> ?F ` (Func (Field r) A)" by auto
  hence "|Bpow r A - {{}}| \<le>o |Func (Field r) A|"
  by (rule surj_imp_ordLeq)
  moreover
  {have 2: "infinite (Bpow r A)" using infinite_Bpow[OF rc r A] .
   have "|Bpow r A| =o |Bpow r A - {{}}|"
   using card_of_infinite_diff_finitte
   by (metis Pow_empty 2 finite_Pow_iff infinite_imp_nonempty ordIso_symmetric)
  }
  ultimately show ?thesis by (metis ordIso_ordLeq_trans)
qed

lemma Func_emp2[simp]: "A \<noteq> {} \<Longrightarrow> Func A {} = {}" by auto

lemma empty_in_Func[simp]:
"B \<noteq> {} \<Longrightarrow> empty \<in> Func {} B"
unfolding Func_def by auto

lemma Func_mono[simp]:
assumes "B1 \<subseteq> B2"
shows "Func A B1 \<subseteq> Func A B2"
using assms unfolding Func_def by force

lemma Pfunc_mono[simp]:
assumes "A1 \<subseteq> A2" and "B1 \<subseteq> B2"
shows "Pfunc A B1 \<subseteq> Pfunc A B2"
using assms in_mono unfolding Pfunc_def apply safe
apply(case_tac "x a", auto)
by (metis in_mono option.simps(5))

lemma card_of_Func_UNIV_UNIV:
"|Func (UNIV::'a set) (UNIV::'b set)| =o |UNIV::('a \<Rightarrow> 'b) set|"
using card_of_Func_UNIV[of "UNIV::'b set"] by auto

end
