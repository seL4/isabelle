(*  Title:      HOL/Cardinals/Cardinal_Order_Relation.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Cardinal-order relations.
*)

header {* Cardinal-Order Relations *}

theory Cardinal_Order_Relation
imports BNF_Cardinal_Order_Relation Constructions_on_Wellorders
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
  card_of_Plus1[simp]
  Card_order_Plus1[simp]
  card_of_Plus2[simp]
  Card_order_Plus2[simp]
  card_of_Plus_mono1[simp]
  card_of_Plus_mono2[simp]
  card_of_Plus_mono[simp]
  card_of_Plus_cong2[simp]
  card_of_Plus_cong[simp]
  card_of_Un_Plus_ordLeq[simp]
  card_of_Times1[simp]
  card_of_Times2[simp]
  card_of_Times3[simp]
  card_of_Times_mono1[simp]
  card_of_Times_mono2[simp]
  card_of_ordIso_finite[simp]
  card_of_Times_same_infinite[simp]
  card_of_Times_infinite_simps[simp]
  card_of_Plus_infinite1[simp]
  card_of_Plus_infinite2[simp]
  card_of_Plus_ordLess_infinite[simp]
  card_of_Plus_ordLess_infinite_Field[simp]
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


subsection {* Cardinal of a set *}

lemma card_of_inj_rel: assumes INJ: "!! x y y'. \<lbrakk>(x,y) : R; (x,y') : R\<rbrakk> \<Longrightarrow> y = y'"
shows "|{y. EX x. (x,y) : R}| <=o |{x. EX y. (x,y) : R}|"
proof-
  let ?Y = "{y. EX x. (x,y) : R}"  let ?X = "{x. EX y. (x,y) : R}"
  let ?f = "% y. SOME x. (x,y) : R"
  have "?f ` ?Y <= ?X" by (auto dest: someI)
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

lemma card_of_set_type[simp]: "|UNIV::'a set| <o |UNIV::'a set set|"
using card_of_Pow[of "UNIV::'a set"] by simp

lemma card_of_Un1[simp]:
shows "|A| \<le>o |A \<union> B| "
using inj_on_id[of A] card_of_ordLeq[of A _] by fastforce

lemma card_of_diff[simp]:
shows "|A - B| \<le>o |A|"
using inj_on_id[of "A - B"] card_of_ordLeq[of "A - B" _] by fastforce

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
  by (rule card_of_Times3)

lemma card_of_Times_cong1[simp]:
assumes "|A| =o |B|"
shows "|A \<times> C| =o |B \<times> C|"
using assms by (simp add: ordIso_iff_ordLeq)

lemma card_of_Times_cong2[simp]:
assumes "|A| =o |B|"
shows "|C \<times> A| =o |C \<times> B|"
using assms by (simp add: ordIso_iff_ordLeq)

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

corollary ordIso_Times_cong2:
assumes "r =o r'"
shows "|A \<times> (Field r)| =o |A \<times> (Field r')|"
using assms card_of_cong card_of_Times_cong2 by blast

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
  hence "|SIGMA i : I. A (f i)| =o |SIGMA i : I. B (f i)|" by (rule card_of_Sigma_cong1)
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
assumes "\<not>finite A"
shows "\<exists>f. bij_betw f (A \<times> A) A"
using assms by (auto simp add: card_of_ordIso)

corollary Times_same_infinite_bij_betw_types:
assumes INF: "\<not>finite(UNIV::'a set)"
shows "\<exists>(f::('a * 'a) => 'a). bij f"
using assms Times_same_infinite_bij_betw[of "UNIV::'a set"]
by auto

corollary Times_infinite_bij_betw:
assumes INF: "\<not>finite A" and NE: "B \<noteq> {}" and INJ: "inj_on g B \<and> g ` B \<le> A"
shows "(\<exists>f. bij_betw f (A \<times> B) A) \<and> (\<exists>h. bij_betw h (B \<times> A) A)"
proof-
  have "|B| \<le>o |A|" using INJ card_of_ordLeq by blast
  thus ?thesis using INF NE
  by (auto simp add: card_of_ordIso card_of_Times_infinite)
qed

corollary Times_infinite_bij_betw_types:
assumes INF: "\<not>finite(UNIV::'a set)" and
        BIJ: "inj(g::'b \<Rightarrow> 'a)"
shows "(\<exists>(f::('b * 'a) => 'a). bij f) \<and> (\<exists>(h::('a * 'b) => 'a). bij h)"
using assms Times_infinite_bij_betw[of "UNIV::'a set" "UNIV::'b set" g]
by auto

lemma card_of_Times_ordLeq_infinite:
"\<lbrakk>\<not>finite C; |A| \<le>o |C|; |B| \<le>o |C|\<rbrakk>
 \<Longrightarrow> |A <*> B| \<le>o |C|"
by(simp add: card_of_Sigma_ordLeq_infinite)

corollary Plus_infinite_bij_betw:
assumes INF: "\<not>finite A" and INJ: "inj_on g B \<and> g ` B \<le> A"
shows "(\<exists>f. bij_betw f (A <+> B) A) \<and> (\<exists>h. bij_betw h (B <+> A) A)"
proof-
  have "|B| \<le>o |A|" using INJ card_of_ordLeq by blast
  thus ?thesis using INF
  by (auto simp add: card_of_ordIso)
qed

corollary Plus_infinite_bij_betw_types:
assumes INF: "\<not>finite(UNIV::'a set)" and
        BIJ: "inj(g::'b \<Rightarrow> 'a)"
shows "(\<exists>(f::('b + 'a) => 'a). bij f) \<and> (\<exists>(h::('a + 'b) => 'a). bij h)"
using assms Plus_infinite_bij_betw[of "UNIV::'a set" g "UNIV::'b set"]
by auto

lemma card_of_Un_infinite:
assumes INF: "\<not>finite A" and LEQ: "|B| \<le>o |A|"
shows "|A \<union> B| =o |A| \<and> |B \<union> A| =o |A|"
proof-
  have "|A \<union> B| \<le>o |A <+> B|" by (rule card_of_Un_Plus_ordLeq)
  moreover have "|A <+> B| =o |A|"
  using assms by (metis card_of_Plus_infinite)
  ultimately have "|A \<union> B| \<le>o |A|" using ordLeq_ordIso_trans by blast
  hence "|A \<union> B| =o |A|" using card_of_Un1 ordIso_iff_ordLeq by blast
  thus ?thesis using Un_commute[of B A] by auto
qed

lemma card_of_Un_infinite_simps[simp]:
"\<lbrakk>\<not>finite A; |B| \<le>o |A| \<rbrakk> \<Longrightarrow> |A \<union> B| =o |A|"
"\<lbrakk>\<not>finite A; |B| \<le>o |A| \<rbrakk> \<Longrightarrow> |B \<union> A| =o |A|"
using card_of_Un_infinite by auto

lemma card_of_Un_diff_infinite:
assumes INF: "\<not>finite A" and LESS: "|B| <o |A|"
shows "|A - B| =o |A|"
proof-
  obtain C where C_def: "C = A - B" by blast
  have "|A \<union> B| =o |A|"
  using assms ordLeq_iff_ordLess_or_ordIso card_of_Un_infinite by blast
  moreover have "C \<union> B = A \<union> B" unfolding C_def by auto
  ultimately have 1: "|C \<union> B| =o |A|" by auto
  (*  *)
  {assume *: "|C| \<le>o |B|"
   moreover
   {assume **: "finite B"
    hence "finite C"
    using card_of_ordLeq_finite * by blast
    hence False using ** INF card_of_ordIso_finite 1 by blast
   }
   hence "\<not>finite B" by auto
   ultimately have False
   using card_of_Un_infinite 1 ordIso_equivalence(1,3) LESS not_ordLess_ordIso by metis
  }
  hence 2: "|B| \<le>o |C|" using card_of_Well_order ordLeq_total by blast
  {assume *: "finite C"
    hence "finite B" using card_of_ordLeq_finite 2 by blast
    hence False using * INF card_of_ordIso_finite 1 by blast
  }
  hence "\<not>finite C" by auto
  hence "|C| =o |A|"
  using  card_of_Un_infinite 1 2 ordIso_equivalence(1,3) by metis
  thus ?thesis unfolding C_def .
qed

corollary Card_order_Un_infinite:
assumes INF: "\<not>finite(Field r)" and CARD: "Card_order r" and
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
assumes INF: "\<not>finite B" and SUB: "A \<le> B" and LESS: "|A| <o |B|"
shows "\<not>finite (B - A)"
using assms card_of_Un_diff_infinite card_of_ordIso_finite by blast

lemma card_of_Times_ordLess_infinite[simp]:
assumes INF: "\<not>finite C" and
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
   hence "\<not>finite (A \<times> B)" using INF card_of_ordLeq_finite by blast
   hence 1: "\<not>finite A \<or> \<not>finite B" using finite_cartesian_product by blast
   {assume Case21: "|A| \<le>o |B|"
    hence "\<not>finite B" using 1 card_of_ordLeq_finite by blast
    hence "|A \<times> B| =o |B|" using Case2 Case21
    by (auto simp add: card_of_Times_infinite)
    hence False using LESS2 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   moreover
   {assume Case22: "|B| \<le>o |A|"
    hence "\<not>finite A" using 1 card_of_ordLeq_finite by blast
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
assumes INF: "\<not>finite (Field r)" and r: "Card_order r" and
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
assumes INF: "\<not>finite C" and
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A \<union> B| <o |C|"
using assms card_of_Plus_ordLess_infinite card_of_Un_Plus_ordLeq
      ordLeq_ordLess_trans by blast

lemma card_of_Un_ordLess_infinite_Field[simp]:
assumes INF: "\<not>finite (Field r)" and r: "Card_order r" and
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


subsection {* Cardinals versus set operations involving infinite sets *}

lemma finite_iff_cardOf_nat:
"finite A = ( |A| <o |UNIV :: nat set| )"
using infinite_iff_card_of_nat[of A]
not_ordLeq_iff_ordLess[of "|A|" "|UNIV :: nat set|"]
by fastforce

lemma finite_ordLess_infinite2[simp]:
assumes "finite A" and "\<not>finite B"
shows "|A| <o |B|"
using assms
finite_ordLess_infinite[of "|A|" "|B|"]
card_of_Well_order[of A] card_of_Well_order[of B]
Field_card_of[of A] Field_card_of[of B] by auto

lemma infinite_card_of_insert:
assumes "\<not>finite A"
shows "|insert a A| =o |A|"
proof-
  have iA: "insert a A = A \<union> {a}" by simp
  show ?thesis
  using infinite_imp_bij_betw2[OF assms] unfolding iA
  by (metis bij_betw_inv card_of_ordIso)
qed

lemma card_of_Un_singl_ordLess_infinite1:
assumes "\<not>finite B" and "|A| <o |B|"
shows "|{a} Un A| <o |B|"
proof-
  have "|{a}| <o |B|" using assms by auto
  thus ?thesis using assms card_of_Un_ordLess_infinite[of B] by blast
qed

lemma card_of_Un_singl_ordLess_infinite:
assumes "\<not>finite B"
shows "( |A| <o |B| ) = ( |{a} Un A| <o |B| )"
using assms card_of_Un_singl_ordLess_infinite1[of B A]
proof(auto)
  assume "|insert a A| <o |B|"
  moreover have "|A| <=o |insert a A|" using card_of_mono1[of A "insert a A"] by blast
  ultimately show "|A| <o |B|" using ordLeq_ordLess_trans by blast
qed


subsection {* Cardinals versus lists *}

text{* The next is an auxiliary operator, which shall be used for inductive
proofs of facts concerning the cardinality of @{text "List"} : *}

definition nlists :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set"
where "nlists A n \<equiv> {l. set l \<le> A \<and> length l = n}"

lemma lists_def2: "lists A = {l. set l \<le> A}"
using in_listsI by blast

lemma lists_UNION_nlists: "lists A = (\<Union> n. nlists A n)"
unfolding lists_def2 nlists_def by blast

lemma card_of_lists: "|A| \<le>o |lists A|"
proof-
  let ?h = "\<lambda> a. [a]"
  have "inj_on ?h A \<and> ?h ` A \<le> lists A"
  unfolding inj_on_def lists_def2 by auto
  thus ?thesis by (metis card_of_ordLeq)
qed

lemma nlists_0: "nlists A 0 = {[]}"
unfolding nlists_def by auto

lemma nlists_not_empty:
assumes "A \<noteq> {}"
shows "nlists A n \<noteq> {}"
proof(induct n, simp add: nlists_0)
  fix n assume "nlists A n \<noteq> {}"
  then obtain a and l where "a \<in> A \<and> l \<in> nlists A n" using assms by auto
  hence "a # l \<in> nlists A (Suc n)" unfolding nlists_def by auto
  thus "nlists A (Suc n) \<noteq> {}" by auto
qed

lemma Nil_in_lists: "[] \<in> lists A"
unfolding lists_def2 by auto

lemma lists_not_empty: "lists A \<noteq> {}"
using Nil_in_lists by blast

lemma card_of_nlists_Succ: "|nlists A (Suc n)| =o |A \<times> (nlists A n)|"
proof-
  let ?B = "A \<times> (nlists A n)"   let ?h = "\<lambda>(a,l). a # l"
  have "inj_on ?h ?B \<and> ?h ` ?B \<le> nlists A (Suc n)"
  unfolding inj_on_def nlists_def by auto
  moreover have "nlists A (Suc n) \<le> ?h ` ?B"
  proof(auto)
    fix l assume "l \<in> nlists A (Suc n)"
    hence 1: "length l = Suc n \<and> set l \<le> A" unfolding nlists_def by auto
    then obtain a and l' where 2: "l = a # l'" by (auto simp: length_Suc_conv)
    hence "a \<in> A \<and> set l' \<le> A \<and> length l' = n" using 1 by auto
    thus "l \<in> ?h ` ?B"  using 2 unfolding nlists_def by auto
  qed
  ultimately have "bij_betw ?h ?B (nlists A (Suc n))"
  unfolding bij_betw_def by auto
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed

lemma card_of_nlists_infinite:
assumes "\<not>finite A"
shows "|nlists A n| \<le>o |A|"
proof(induct n)
  have "A \<noteq> {}" using assms by auto
  thus "|nlists A 0| \<le>o |A|" by (simp add: nlists_0)
next
  fix n assume IH: "|nlists A n| \<le>o |A|"
  have "|nlists A (Suc n)| =o |A \<times> (nlists A n)|"
  using card_of_nlists_Succ by blast
  moreover
  {have "nlists A n \<noteq> {}" using assms nlists_not_empty[of A] by blast
   hence "|A \<times> (nlists A n)| =o |A|"
   using assms IH by (auto simp add: card_of_Times_infinite)
  }
  ultimately show "|nlists A (Suc n)| \<le>o |A|"
  using ordIso_transitive ordIso_iff_ordLeq by blast
qed

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

lemma card_of_lists_infinite[simp]:
assumes "\<not>finite A"
shows "|lists A| =o |A|"
proof-
  have "|lists A| \<le>o |A|" unfolding lists_UNION_nlists
  by (rule card_of_UNION_ordLeq_infinite[OF assms _ ballI[OF card_of_nlists_infinite[OF assms]]])
    (metis infinite_iff_card_of_nat assms)
  thus ?thesis using card_of_lists ordIso_iff_ordLeq by blast
qed

lemma Card_order_lists_infinite:
assumes "Card_order r" and "\<not>finite(Field r)"
shows "|lists(Field r)| =o r"
using assms card_of_lists_infinite card_of_Field_ordIso ordIso_transitive by blast

lemma ordIso_lists_cong:
assumes "r =o r'"
shows "|lists(Field r)| =o |lists(Field r')|"
using assms card_of_cong card_of_lists_cong by blast

corollary lists_infinite_bij_betw:
assumes "\<not>finite A"
shows "\<exists>f. bij_betw f (lists A) A"
using assms card_of_lists_infinite card_of_ordIso by blast

corollary lists_infinite_bij_betw_types:
assumes "\<not>finite(UNIV :: 'a set)"
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
assumes "\<not>finite A"
shows "|Fpow A| =o |A|"
using assms card_of_Fpow_lists card_of_lists_infinite card_of_Fpow
      ordLeq_ordIso_trans ordIso_iff_ordLeq by blast

corollary Fpow_infinite_bij_betw:
assumes "\<not>finite A"
shows "\<exists>f. bij_betw f (Fpow A) A"
using assms card_of_Fpow_infinite card_of_ordIso by blast


subsection {* The cardinal $\omega$ and the finite cardinals  *}

subsubsection {* First as well-orders *}

lemma Field_natLess: "Field natLess = (UNIV::nat set)"
by(unfold Field_def, auto)

lemma natLeq_well_order_on: "well_order_on UNIV natLeq"
using natLeq_Well_order Field_natLeq by auto

lemma natLeq_wo_rel: "wo_rel natLeq"
unfolding wo_rel_def using natLeq_Well_order .

lemma natLeq_ofilter_less: "ofilter natLeq {0 ..< n}"
by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def,
   simp add: Field_natLeq, unfold under_def, auto)

lemma natLeq_ofilter_leq: "ofilter natLeq {0 .. n}"
by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def,
   simp add: Field_natLeq, unfold under_def, auto)

lemma natLeq_UNIV_ofilter: "wo_rel.ofilter natLeq UNIV"
using natLeq_wo_rel Field_natLeq wo_rel.Field_ofilter[of natLeq] by auto

lemma closed_nat_set_iff:
assumes "\<forall>(m::nat) n. n \<in> A \<and> m \<le> n \<longrightarrow> m \<in> A"
shows "A = UNIV \<or> (\<exists>n. A = {0 ..< n})"
proof-
  {assume "A \<noteq> UNIV" hence "\<exists>n. n \<notin> A" by blast
   moreover obtain n where n_def: "n = (LEAST n. n \<notin> A)" by blast
   ultimately have 1: "n \<notin> A \<and> (\<forall>m. m < n \<longrightarrow> m \<in> A)"
   using LeastI_ex[of "\<lambda> n. n \<notin> A"] n_def Least_le[of "\<lambda> n. n \<notin> A"] by fastforce
   have "A = {0 ..< n}"
   proof(auto simp add: 1)
     fix m assume *: "m \<in> A"
     {assume "n \<le> m" with assms * have "n \<in> A" by blast
      hence False using 1 by auto
     }
     thus "m < n" by fastforce
   qed
   hence "\<exists>n. A = {0 ..< n}" by blast
  }
  thus ?thesis by blast
qed

lemma natLeq_ofilter_iff:
"ofilter natLeq A = (A = UNIV \<or> (\<exists>n. A = {0 ..< n}))"
proof(rule iffI)
  assume "ofilter natLeq A"
  hence "\<forall>m n. n \<in> A \<and> m \<le> n \<longrightarrow> m \<in> A"
  by(auto simp add: natLeq_wo_rel wo_rel.ofilter_def under_def)
  thus "A = UNIV \<or> (\<exists>n. A = {0 ..< n})" using closed_nat_set_iff by blast
next
  assume "A = UNIV \<or> (\<exists>n. A = {0 ..< n})"
  thus "ofilter natLeq A"
  by(auto simp add: natLeq_ofilter_less natLeq_UNIV_ofilter)
qed

lemma natLeq_under_leq: "under natLeq n = {0 .. n}"
unfolding under_def by auto

lemma natLeq_on_ofilter_less_eq:
"n \<le> m \<Longrightarrow> wo_rel.ofilter (natLeq_on m) {0 ..< n}"
apply (auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def)
apply (simp add: Field_natLeq_on)
by (auto simp add: under_def)

lemma natLeq_on_ofilter_iff:
"wo_rel.ofilter (natLeq_on m) A = (\<exists>n \<le> m. A = {0 ..< n})"
proof(rule iffI)
  assume *: "wo_rel.ofilter (natLeq_on m) A"
  hence 1: "A \<le> {0..<m}"
  by (auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def under_def Field_natLeq_on)
  hence "\<forall>n1 n2. n2 \<in> A \<and> n1 \<le> n2 \<longrightarrow> n1 \<in> A"
  using * by(fastforce simp add: natLeq_on_wo_rel wo_rel.ofilter_def under_def)
  hence "A = UNIV \<or> (\<exists>n. A = {0 ..< n})" using closed_nat_set_iff by blast
  thus "\<exists>n \<le> m. A = {0 ..< n}" using 1 atLeastLessThan_less_eq by blast
next
  assume "(\<exists>n\<le>m. A = {0 ..< n})"
  thus "wo_rel.ofilter (natLeq_on m) A" by (auto simp add: natLeq_on_ofilter_less_eq)
qed

corollary natLeq_on_ofilter:
"ofilter(natLeq_on n) {0 ..< n}"
by (auto simp add: natLeq_on_ofilter_less_eq)

lemma natLeq_on_ofilter_less:
"n < m \<Longrightarrow> ofilter (natLeq_on m) {0 .. n}"
by(auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def,
   simp add: Field_natLeq_on, unfold under_def, auto)

lemma natLeq_on_ordLess_natLeq: "natLeq_on n <o natLeq"
using Field_natLeq Field_natLeq_on[of n]
      finite_ordLess_infinite[of "natLeq_on n" natLeq]
      natLeq_Well_order natLeq_on_Well_order[of n] by auto

lemma natLeq_on_injective:
"natLeq_on m = natLeq_on n \<Longrightarrow> m = n"
using Field_natLeq_on[of m] Field_natLeq_on[of n]
      atLeastLessThan_injective[of m n, unfolded atLeastLessThan_def] by blast

lemma natLeq_on_injective_ordIso:
"(natLeq_on m =o natLeq_on n) = (m = n)"
proof(auto simp add: natLeq_on_Well_order ordIso_reflexive)
  assume "natLeq_on m =o natLeq_on n"
  then obtain f where "bij_betw f {x. x<m} {x. x<n}"
  using Field_natLeq_on assms unfolding ordIso_def iso_def[abs_def] by auto
  thus "m = n" using atLeastLessThan_injective2[of f m n]
    unfolding atLeast_0 atLeastLessThan_def lessThan_def Int_UNIV_left by blast
qed


subsubsection {* Then as cardinals *}

lemma ordIso_natLeq_infinite1:
"|A| =o natLeq \<Longrightarrow> \<not>finite A"
using ordIso_symmetric ordIso_imp_ordLeq infinite_iff_natLeq_ordLeq by blast

lemma ordIso_natLeq_infinite2:
"natLeq =o |A| \<Longrightarrow> \<not>finite A"
using ordIso_imp_ordLeq infinite_iff_natLeq_ordLeq by blast


lemma ordIso_natLeq_on_imp_finite:
"|A| =o natLeq_on n \<Longrightarrow> finite A"
unfolding ordIso_def iso_def[abs_def]
by (auto simp: Field_natLeq_on bij_betw_finite)


lemma natLeq_on_Card_order: "Card_order (natLeq_on n)"
proof(unfold card_order_on_def,
      auto simp add: natLeq_on_Well_order, simp add: Field_natLeq_on)
  fix r assume "well_order_on {x. x < n} r"
  thus "natLeq_on n \<le>o r"
  using finite_atLeastLessThan natLeq_on_well_order_on
        finite_well_order_on_ordIso ordIso_iff_ordLeq by blast
qed


corollary card_of_Field_natLeq_on:
"|Field (natLeq_on n)| =o natLeq_on n"
using Field_natLeq_on natLeq_on_Card_order
      Card_order_iff_ordIso_card_of[of "natLeq_on n"]
      ordIso_symmetric[of "natLeq_on n"] by blast


corollary card_of_less:
"|{0 ..< n}| =o natLeq_on n"
using Field_natLeq_on card_of_Field_natLeq_on
unfolding atLeast_0 atLeastLessThan_def lessThan_def Int_UNIV_left by auto


lemma natLeq_on_ordLeq_less_eq:
"((natLeq_on m) \<le>o (natLeq_on n)) = (m \<le> n)"
proof
  assume "natLeq_on m \<le>o natLeq_on n"
  then obtain f where "inj_on f {x. x < m} \<and> f ` {x. x < m} \<le> {x. x < n}"
  unfolding ordLeq_def using
    embed_inj_on[OF natLeq_on_Well_order[of m], of "natLeq_on n", unfolded Field_natLeq_on]
     embed_Field[OF natLeq_on_Well_order[of m], of "natLeq_on n", unfolded Field_natLeq_on] by blast
  thus "m \<le> n" using atLeastLessThan_less_eq2
    unfolding atLeast_0 atLeastLessThan_def lessThan_def Int_UNIV_left by blast
next
  assume "m \<le> n"
  hence "inj_on id {0..<m} \<and> id ` {0..<m} \<le> {0..<n}" unfolding inj_on_def by auto
  hence "|{0..<m}| \<le>o |{0..<n}|" using card_of_ordLeq by blast
  thus "natLeq_on m \<le>o natLeq_on n"
  using card_of_less ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric by blast
qed


lemma natLeq_on_ordLeq_less:
"((natLeq_on m) <o (natLeq_on n)) = (m < n)"
using not_ordLeq_iff_ordLess[OF natLeq_on_Well_order natLeq_on_Well_order, of n m]
   natLeq_on_ordLeq_less_eq[of n m] by linarith

lemma ordLeq_natLeq_on_imp_finite:
assumes "|A| \<le>o natLeq_on n"
shows "finite A"
proof-
  have "|A| \<le>o |{0 ..< n}|"
  using assms card_of_less ordIso_symmetric ordLeq_ordIso_trans by blast
  thus ?thesis by (auto simp add: card_of_ordLeq_finite)
qed


subsubsection {* "Backward compatibility" with the numeric cardinal operator for finite sets *}

lemma finite_card_of_iff_card2:
assumes FIN: "finite A" and FIN': "finite B"
shows "( |A| \<le>o |B| ) = (card A \<le> card B)"
using assms card_of_ordLeq[of A B] inj_on_iff_card_le[of A B] by blast

lemma finite_imp_card_of_natLeq_on:
assumes "finite A"
shows "|A| =o natLeq_on (card A)"
proof-
  obtain h where "bij_betw h A {0 ..< card A}"
  using assms ex_bij_betw_finite_nat by blast
  thus ?thesis using card_of_ordIso card_of_less ordIso_equivalence by blast
qed

lemma finite_iff_card_of_natLeq_on:
"finite A = (\<exists>n. |A| =o natLeq_on n)"
using finite_imp_card_of_natLeq_on[of A]
by(auto simp add: ordIso_natLeq_on_imp_finite)


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

lemma cardSuc_natLeq_on_Suc:
"cardSuc(natLeq_on n) =o natLeq_on(Suc n)"
proof-
  obtain r r' p where r_def: "r = natLeq_on n" and
                      r'_def: "r' = cardSuc(natLeq_on n)"  and
                      p_def: "p = natLeq_on(Suc n)" by blast
  (* Preliminary facts:  *)
  have CARD: "Card_order r \<and> Card_order r' \<and> Card_order p" unfolding r_def r'_def p_def
  using cardSuc_ordLess_ordLeq natLeq_on_Card_order cardSuc_Card_order by blast
  hence WELL: "Well_order r \<and> Well_order r' \<and>  Well_order p"
  unfolding card_order_on_def by force
  have FIELD: "Field r = {0..<n} \<and> Field p = {0..<(Suc n)}"
  unfolding r_def p_def Field_natLeq_on atLeast_0 atLeastLessThan_def lessThan_def by simp
  hence FIN: "finite (Field r)" by force
  have "r <o r'" using CARD unfolding r_def r'_def using cardSuc_greater by blast
  hence "|Field r| <o r'" using CARD card_of_Field_ordIso ordIso_ordLess_trans by blast
  hence LESS: "|Field r| <o |Field r'|"
  using CARD card_of_Field_ordIso ordLess_ordIso_trans ordIso_symmetric by blast
  (* Main proof: *)
  have "r' \<le>o p" using CARD unfolding r_def r'_def p_def
  using natLeq_on_ordLeq_less cardSuc_ordLess_ordLeq by blast
  moreover have "p \<le>o r'"
  proof-
    {assume "r' <o p"
     then obtain f where 0: "embedS r' p f" unfolding ordLess_def by force
     let ?q = "Restr p (f ` Field r')"
     have 1: "embed r' p f" using 0 unfolding embedS_def by force
     hence 2: "f ` Field r' < {0..<(Suc n)}"
     using WELL FIELD 0 by (auto simp add: embedS_iff)
     have "wo_rel.ofilter p (f ` Field r')" using embed_Field_ofilter 1 WELL by blast
     then obtain m where "m \<le> Suc n" and 3: "f ` (Field r') = {0..<m}"
     unfolding p_def by (auto simp add: natLeq_on_ofilter_iff)
     hence 4: "m \<le> n" using 2 by force
     (*  *)
     have "bij_betw f (Field r') (f ` (Field r'))"
     using WELL embed_inj_on[OF _ 1] unfolding bij_betw_def by blast
     moreover have "finite(f ` (Field r'))" using 3 finite_atLeastLessThan[of 0 m] by force
     ultimately have 5: "finite (Field r') \<and> card(Field r') = card (f ` (Field r'))"
     using bij_betw_same_card bij_betw_finite by metis
     hence "card(Field r') \<le> card(Field r)" using 3 4 FIELD by force
     hence "|Field r'| \<le>o |Field r|" using FIN 5 finite_card_of_iff_card2 by blast
     hence False using LESS not_ordLess_ordLeq by auto
    }
    thus ?thesis using WELL CARD by fastforce
  qed
  ultimately show ?thesis using ordIso_iff_ordLeq unfolding r'_def p_def by blast
qed

lemma card_of_Plus_ordLeq_infinite[simp]:
assumes C: "\<not>finite C" and A: "|A| \<le>o |C|" and B: "|B| \<le>o |C|"
shows "|A <+> B| \<le>o |C|"
proof-
  let ?r = "cardSuc |C|"
  have "Card_order ?r \<and> \<not>finite (Field ?r)" using assms by simp
  moreover have "|A| <o ?r" and "|B| <o ?r" using A B by auto
  ultimately have "|A <+> B| <o ?r"
  using card_of_Plus_ordLess_infinite_Field by blast
  thus ?thesis using C by simp
qed

lemma card_of_Un_ordLeq_infinite[simp]:
assumes C: "\<not>finite C" and A: "|A| \<le>o |C|" and B: "|B| \<le>o |C|"
shows "|A Un B| \<le>o |C|"
using assms card_of_Plus_ordLeq_infinite card_of_Un_Plus_ordLeq
ordLeq_transitive by metis


subsection {* Others *}

lemma under_mono[simp]:
assumes "Well_order r" and "(i,j) \<in> r"
shows "under r i \<subseteq> under r j"
using assms unfolding under_def order_on_defs
trans_def by blast

lemma underS_under:
assumes "i \<in> Field r"
shows "underS r i = under r i - {i}"
using assms unfolding underS_def under_def by auto

lemma relChain_under:
assumes "Well_order r"
shows "relChain r (\<lambda> i. under r i)"
using assms unfolding relChain_def by auto

lemma card_of_infinite_diff_finite:
assumes "\<not>finite A" and "finite B"
shows "|A - B| =o |A|"
by (metis assms card_of_Un_diff_infinite finite_ordLess_infinite2)

lemma infinite_card_of_diff_singl:
assumes "\<not>finite A"
shows "|A - {a}| =o |A|"
by (metis assms card_of_infinite_diff_finite finite.emptyI finite_insert)

lemma card_of_vimage:
assumes "B \<subseteq> range f"
shows "|B| \<le>o |f -` B|"
apply(rule surj_imp_ordLeq[of _ f])
using assms by (metis Int_absorb2 image_vimage_eq order_refl)

lemma surj_card_of_vimage:
assumes "surj f"
shows "|B| \<le>o |f -` B|"
by (metis assms card_of_vimage subset_UNIV)

lemma infinite_Pow:
assumes "\<not> finite A"
shows "\<not> finite (Pow A)"
proof-
  have "|A| \<le>o |Pow A|" by (metis card_of_Pow ordLess_imp_ordLeq)
  thus ?thesis by (metis assms finite_Pow_iff)
qed

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
and A: "\<not>finite A"
shows "\<not>finite (Bpow r A)"
using ordLeq_card_Bpow[OF rc r]
by (metis A card_of_ordLeq_infinite)

definition Func_option where
 "Func_option A B \<equiv>
  {f. (\<forall> a. f a \<noteq> None \<longleftrightarrow> a \<in> A) \<and> (\<forall> a \<in> A. case f a of Some b \<Rightarrow> b \<in> B |None \<Rightarrow> True)}"

lemma card_of_Func_option_Func:
"|Func_option A B| =o |Func A B|"
proof (rule ordIso_symmetric, unfold card_of_ordIso[symmetric], intro exI)
  let ?F = "\<lambda> f a. if a \<in> A then Some (f a) else None"
  show "bij_betw ?F (Func A B) (Func_option A B)"
  unfolding bij_betw_def unfolding inj_on_def proof(intro conjI ballI impI)
    fix f g assume f: "f \<in> Func A B" and g: "g \<in> Func A B" and eq: "?F f = ?F g"
    show "f = g"
    proof(rule ext)
      fix a
      show "f a = g a"
      proof(cases "a \<in> A")
        case True
        have "Some (f a) = ?F f a" using True by auto
        also have "... = ?F g a" using eq unfolding fun_eq_iff by(rule allE)
        also have "... = Some (g a)" using True by auto
        finally have "Some (f a) = Some (g a)" .
        thus ?thesis by simp
      qed(insert f g, unfold Func_def, auto)
    qed
  next
    show "?F ` Func A B = Func_option A B"
    proof safe
      fix f assume f: "f \<in> Func_option A B"
      def g \<equiv> "\<lambda> a. case f a of Some b \<Rightarrow> b | None \<Rightarrow> undefined"
      have "g \<in> Func A B"
      using f unfolding g_def Func_def Func_option_def by force+
      moreover have "f = ?F g"
      proof(rule ext)
        fix a show "f a = ?F g a"
        using f unfolding Func_option_def g_def by (cases "a \<in> A") force+
      qed
      ultimately show "f \<in> ?F ` (Func A B)" by blast
    qed(unfold Func_def Func_option_def, auto)
  qed
qed

(* partial-function space: *)
definition Pfunc where
"Pfunc A B \<equiv>
 {f. (\<forall>a. f a \<noteq> None \<longrightarrow> a \<in> A) \<and>
     (\<forall>a. case f a of None \<Rightarrow> True | Some b \<Rightarrow> b \<in> B)}"

lemma Func_Pfunc:
"Func_option A B \<subseteq> Pfunc A B"
unfolding Func_option_def Pfunc_def by auto

lemma Pfunc_Func_option:
"Pfunc A B = (\<Union> A' \<in> Pow A. Func_option A' B)"
proof safe
  fix f assume f: "f \<in> Pfunc A B"
  show "f \<in> (\<Union>A'\<in>Pow A. Func_option A' B)"
  proof (intro UN_I)
    let ?A' = "{a. f a \<noteq> None}"
    show "?A' \<in> Pow A" using f unfolding Pow_def Pfunc_def by auto
    show "f \<in> Func_option ?A' B" using f unfolding Func_option_def Pfunc_def by auto
  qed
next
  fix f A' assume "f \<in> Func_option A' B" and "A' \<subseteq> A"
  thus "f \<in> Pfunc A B" unfolding Func_option_def Pfunc_def by auto
qed

lemma card_of_Func_mono:
fixes A1 A2 :: "'a set" and B :: "'b set"
assumes A12: "A1 \<subseteq> A2" and B: "B \<noteq> {}"
shows "|Func A1 B| \<le>o |Func A2 B|"
proof-
  obtain bb where bb: "bb \<in> B" using B by auto
  def F \<equiv> "\<lambda> (f1::'a \<Rightarrow> 'b) a. if a \<in> A2 then (if a \<in> A1 then f1 a else bb)
                                                else undefined"
  show ?thesis unfolding card_of_ordLeq[symmetric] proof(intro exI[of _ F] conjI)
    show "inj_on F (Func A1 B)" unfolding inj_on_def proof safe
      fix f g assume f: "f \<in> Func A1 B" and g: "g \<in> Func A1 B" and eq: "F f = F g"
      show "f = g"
      proof(rule ext)
        fix a show "f a = g a"
        proof(cases "a \<in> A1")
          case True
          thus ?thesis using eq A12 unfolding F_def fun_eq_iff
          by (elim allE[of _ a]) auto
        qed(insert f g, unfold Func_def, fastforce)
      qed
    qed
  qed(insert bb, unfold Func_def F_def, force)
qed

lemma card_of_Func_option_mono:
fixes A1 A2 :: "'a set" and B :: "'b set"
assumes A12: "A1 \<subseteq> A2" and B: "B \<noteq> {}"
shows "|Func_option A1 B| \<le>o |Func_option A2 B|"
by (metis card_of_Func_mono[OF A12 B] card_of_Func_option_Func
  ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric)

lemma card_of_Pfunc_Pow_Func_option:
assumes "B \<noteq> {}"
shows "|Pfunc A B| \<le>o |Pow A <*> Func_option A B|"
proof-
  have "|Pfunc A B| =o |\<Union> A' \<in> Pow A. Func_option A' B|" (is "_ =o ?K")
    unfolding Pfunc_Func_option by(rule card_of_refl)
  also have "?K \<le>o |Sigma (Pow A) (\<lambda> A'. Func_option A' B)|" using card_of_UNION_Sigma .
  also have "|Sigma (Pow A) (\<lambda> A'. Func_option A' B)| \<le>o |Pow A <*> Func_option A B|"
    apply(rule card_of_Sigma_mono1) using card_of_Func_option_mono[OF _ assms] by auto
  finally show ?thesis .
qed

lemma Bpow_ordLeq_Func_Field:
assumes rc: "Card_order r" and r: "Field r \<noteq> {}" and A: "\<not>finite A"
shows "|Bpow r A| \<le>o |Func (Field r) A|"
proof-
  let ?F = "\<lambda> f. {x | x a. f a = x \<and> a \<in> Field r}"
  {fix X assume "X \<in> Bpow r A - {{}}"
   hence XA: "X \<subseteq> A" and "|X| \<le>o r"
   and X: "X \<noteq> {}" unfolding Bpow_def by auto
   hence "|X| \<le>o |Field r|" by (metis Field_card_of card_of_mono2)
   then obtain F where 1: "X = F ` (Field r)"
   using card_of_ordLeq2[OF X] by metis
   def f \<equiv> "\<lambda> i. if i \<in> Field r then F i else undefined"
   have "\<exists> f \<in> Func (Field r) A. X = ?F f"
   apply (intro bexI[of _ f]) using 1 XA unfolding Func_def f_def by auto
  }
  hence "Bpow r A - {{}} \<subseteq> ?F ` (Func (Field r) A)" by auto
  hence "|Bpow r A - {{}}| \<le>o |Func (Field r) A|"
  by (rule surj_imp_ordLeq)
  moreover
  {have 2: "\<not>finite (Bpow r A)" using infinite_Bpow[OF rc r A] .
   have "|Bpow r A| =o |Bpow r A - {{}}|"
     by (metis 2 infinite_card_of_diff_singl ordIso_symmetric)
  }
  ultimately show ?thesis by (metis ordIso_ordLeq_trans)
qed

lemma empty_in_Func[simp]:
"B \<noteq> {} \<Longrightarrow> (\<lambda>x. undefined) \<in> Func {} B"
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

lemma ordLeq_Func:
assumes "{b1,b2} \<subseteq> B" "b1 \<noteq> b2"
shows "|A| \<le>o |Func A B|"
unfolding card_of_ordLeq[symmetric] proof(intro exI conjI)
  let ?F = "\<lambda> aa a. if a \<in> A then (if a = aa then b1 else b2) else undefined"
  show "inj_on ?F A" using assms unfolding inj_on_def fun_eq_iff by auto
  show "?F ` A \<subseteq> Func A B" using assms unfolding Func_def by auto
qed

lemma infinite_Func:
assumes A: "\<not>finite A" and B: "{b1,b2} \<subseteq> B" "b1 \<noteq> b2"
shows "\<not>finite (Func A B)"
using ordLeq_Func[OF B] by (metis A card_of_ordLeq_finite)

section {* Infinite cardinals are limit ordinals *}

lemma card_order_infinite_isLimOrd:
assumes c: "Card_order r" and i: "\<not>finite (Field r)"
shows "isLimOrd r"
proof-
  have 0: "wo_rel r" and 00: "Well_order r"
  using c unfolding card_order_on_def wo_rel_def by auto
  hence rr: "Refl r" by (metis wo_rel.REFL)
  show ?thesis unfolding wo_rel.isLimOrd_def[OF 0] wo_rel.isSuccOrd_def[OF 0] proof safe
    fix j assume j: "j \<in> Field r" and jm: "\<forall>i\<in>Field r. (i, j) \<in> r"
    def p \<equiv> "Restr r (Field r - {j})"
    have fp: "Field p = Field r - {j}"
    unfolding p_def apply(rule Refl_Field_Restr2[OF rr]) by auto
    have of: "ofilter r (Field p)" unfolding wo_rel.ofilter_def[OF 0] proof safe
      fix a x assume a: "a \<in> Field p" and "x \<in> under r a"
      hence x: "(x,a) \<in> r" "x \<in> Field r" unfolding under_def Field_def by auto
      moreover have a: "a \<noteq> j" "a \<in> Field r" "(a,j) \<in> r" using a jm  unfolding fp by auto
      ultimately have "x \<noteq> j" using j jm  by (metis 0 wo_rel.max2_def wo_rel.max2_equals1)
      thus "x \<in> Field p" using x unfolding fp by auto
    qed(unfold p_def Field_def, auto)
    have "p <o r" using j ofilter_ordLess[OF 00 of] unfolding fp p_def[symmetric] by auto
    hence 2: "|Field p| <o r" using c by (metis BNF_Cardinal_Order_Relation.ordLess_Field)
    have "|Field p| =o |Field r|" unfolding fp using i by (metis infinite_card_of_diff_singl)
    also have "|Field r| =o r"
    using c by (metis card_of_unique ordIso_symmetric)
    finally have "|Field p| =o r" .
    with 2 show False by (metis not_ordLess_ordIso)
  qed
qed

lemma insert_Chain:
assumes "Refl r" "C \<in> Chains r" and "i \<in> Field r" and "\<And>j. j \<in> C \<Longrightarrow> (j,i) \<in> r \<or> (i,j) \<in> r"
shows "insert i C \<in> Chains r"
using assms unfolding Chains_def by (auto dest: refl_onD)

lemma Collect_insert: "{R j |j. j \<in> insert j1 J} = insert (R j1) {R j |j. j \<in> J}"
by auto

lemma Field_init_seg_of[simp]:
"Field init_seg_of = UNIV"
unfolding Field_def init_seg_of_def by auto

lemma refl_init_seg_of[intro, simp]: "refl init_seg_of"
unfolding refl_on_def Field_def by auto

lemma regularCard_all_ex:
assumes r: "Card_order r"   "regularCard r"
and As: "\<And> i j b. b \<in> B \<Longrightarrow> (i,j) \<in> r \<Longrightarrow> P i b \<Longrightarrow> P j b"
and Bsub: "\<forall> b \<in> B. \<exists> i \<in> Field r. P i b"
and cardB: "|B| <o r"
shows "\<exists> i \<in> Field r. \<forall> b \<in> B. P i b"
proof-
  let ?As = "\<lambda>i. {b \<in> B. P i b}"
  have "EX i : Field r. B \<le> ?As i"
  apply(rule regularCard_UNION) using assms unfolding relChain_def by auto
  thus ?thesis by auto
qed

lemma relChain_stabilize:
assumes rc: "relChain r As" and AsB: "(\<Union> i \<in> Field r. As i) \<subseteq> B" and Br: "|B| <o r"
and ir: "\<not>finite (Field r)" and cr: "Card_order r"
shows "\<exists> i \<in> Field r. As (succ r i) = As i"
proof(rule ccontr, auto)
  have 0: "wo_rel r" and 00: "Well_order r"
  unfolding wo_rel_def by (metis card_order_on_well_order_on cr)+
  have L: "isLimOrd r" using ir cr by (metis card_order_infinite_isLimOrd)
  have AsBs: "(\<Union> i \<in> Field r. As (succ r i)) \<subseteq> B"
  using AsB L apply safe by (metis "0" UN_I set_mp wo_rel.isLimOrd_succ)
  assume As_s: "\<forall>i\<in>Field r. As (succ r i) \<noteq> As i"
  have 1: "\<forall>i j. (i,j) \<in> r \<and> i \<noteq> j \<longrightarrow> As i \<subset> As j"
  proof safe
    fix i j assume 1: "(i, j) \<in> r" "i \<noteq> j" and Asij: "As i = As j"
    hence rij: "(succ r i, j) \<in> r" by (metis "0" wo_rel.succ_smallest)
    hence "As (succ r i) \<subseteq> As j" using rc unfolding relChain_def by auto
    moreover
    {have "(i,succ r i) \<in> r" apply(rule wo_rel.succ_in[OF 0])
     using 1 unfolding aboveS_def by auto
     hence "As i \<subset> As (succ r i)" using As_s rc rij unfolding relChain_def Field_def by auto
    }
    ultimately show False unfolding Asij by auto
  qed (insert rc, unfold relChain_def, auto)
  hence "\<forall> i \<in> Field r. \<exists> a. a \<in> As (succ r i) - As i"
  using wo_rel.succ_in[OF 0] AsB
  by(metis 0 card_order_infinite_isLimOrd cr ir psubset_imp_ex_mem
            wo_rel.isLimOrd_aboveS wo_rel.succ_diff)
  then obtain f where f: "\<forall> i \<in> Field r. f i \<in> As (succ r i) - As i" by metis
  have "inj_on f (Field r)" unfolding inj_on_def proof safe
    fix i j assume ij: "i \<in> Field r" "j \<in> Field r" and fij: "f i = f j"
    show "i = j"
    proof(cases rule: wo_rel.cases_Total3[OF 0], safe)
      assume "(i, j) \<in> r" and ijd: "i \<noteq> j"
      hence rij: "(succ r i, j) \<in> r" by (metis "0" wo_rel.succ_smallest)
      hence "As (succ r i) \<subseteq> As j" using rc unfolding relChain_def by auto
      thus "i = j" using ij ijd fij f by auto
    next
      assume "(j, i) \<in> r" and ijd: "i \<noteq> j"
      hence rij: "(succ r j, i) \<in> r" by (metis "0" wo_rel.succ_smallest)
      hence "As (succ r j) \<subseteq> As i" using rc unfolding relChain_def by auto
      thus "j = i" using ij ijd fij f by fastforce
    qed(insert ij, auto)
  qed
  moreover have "f ` (Field r) \<subseteq> B" using f AsBs by auto
  moreover have "|B| <o |Field r|" using Br cr by (metis card_of_unique ordLess_ordIso_trans)
  ultimately show False unfolding card_of_ordLess[symmetric] by auto
qed

section {* Regular vs. Stable Cardinals *}

definition stable :: "'a rel \<Rightarrow> bool"
where
"stable r \<equiv> \<forall>(A::'a set) (F :: 'a \<Rightarrow> 'a set).
               |A| <o r \<and> (\<forall>a \<in> A. |F a| <o r)
               \<longrightarrow> |SIGMA a : A. F a| <o r"

lemma regularCard_stable:
assumes cr: "Card_order r" and ir: "\<not>finite (Field r)" and reg: "regularCard r"
shows "stable r"
unfolding stable_def proof safe
  fix A :: "'a set" and F :: "'a \<Rightarrow> 'a set" assume A: "|A| <o r" and F: "\<forall>a\<in>A. |F a| <o r"
  {assume "r \<le>o |Sigma A F|"
   hence "|Field r| \<le>o |Sigma A F|" using card_of_Field_ordIso[OF cr]
   by (metis Field_card_of card_of_cong ordLeq_iff_ordLess_or_ordIso ordLeq_ordLess_trans)
   moreover have Fi: "Field r \<noteq> {}" using ir by auto
   ultimately obtain f where f: "f ` Sigma A F = Field r" using card_of_ordLeq2 by metis
   have r: "wo_rel r" using cr unfolding card_order_on_def wo_rel_def by auto
   {fix a assume a: "a \<in> A"
    def L \<equiv> "{(a,u) | u. u \<in> F a}"
    have fL: "f ` L \<subseteq> Field r" using f a unfolding L_def by auto
    have "|L| =o |F a|" unfolding L_def card_of_ordIso[symmetric]
    apply(rule exI[of _ snd]) unfolding bij_betw_def inj_on_def by (auto simp: image_def)
    hence "|L| <o r" using F a ordIso_ordLess_trans[of "|L|" "|F a|"] unfolding L_def by auto
    hence "|f ` L| <o r" using ordLeq_ordLess_trans[OF card_of_image, of "L"] unfolding L_def by auto
    hence "\<not> cofinal (f ` L) r" using reg fL unfolding regularCard_def by (metis not_ordLess_ordIso)
    then obtain k where k: "k \<in> Field r" and "\<forall> l \<in> L. \<not> (f l \<noteq> k \<and> (k, f l) \<in> r)"
    unfolding cofinal_def image_def by auto
    hence "\<exists> k \<in> Field r. \<forall> l \<in> L. (f l, k) \<in> r" using r by (metis fL image_subset_iff wo_rel.in_notinI)
    hence "\<exists> k \<in> Field r. \<forall> u \<in> F a. (f (a,u), k) \<in> r" unfolding L_def by auto
   }
   then obtain gg where gg: "\<forall> a \<in> A. \<forall> u \<in> F a. (f (a,u), gg a) \<in> r" by metis
   obtain j0 where j0: "j0 \<in> Field r" using Fi by auto
   def g \<equiv> "\<lambda> a. if F a \<noteq> {} then gg a else j0"
   have g: "\<forall> a \<in> A. \<forall> u \<in> F a. (f (a,u),g a) \<in> r" using gg unfolding g_def by auto
   hence 1: "Field r \<subseteq> (\<Union> a \<in> A. under r (g a))"
   using f[symmetric] unfolding under_def image_def by auto
   have gA: "g ` A \<subseteq> Field r" using gg j0 unfolding Field_def g_def by auto
   moreover have "cofinal (g ` A) r" unfolding cofinal_def proof safe
     fix i assume "i \<in> Field r"
     then obtain j where ij: "(i,j) \<in> r" "i \<noteq> j" using cr ir by (metis infinite_Card_order_limit)
     hence "j \<in> Field r" by (metis card_order_on_def cr well_order_on_domain)
     then obtain a where a: "a \<in> A" and j: "(j, g a) \<in> r" using 1 unfolding under_def by auto
     hence "(i, g a) \<in> r" using ij wo_rel.TRANS[OF r] unfolding trans_def by blast
     moreover have "i \<noteq> g a"
     using ij j r unfolding wo_rel_def unfolding well_order_on_def linear_order_on_def
     partial_order_on_def antisym_def by auto
     ultimately show "\<exists>j\<in>g ` A. i \<noteq> j \<and> (i, j) \<in> r" using a by auto
   qed
   ultimately have "|g ` A| =o r" using reg unfolding regularCard_def by auto
   moreover have "|g ` A| \<le>o |A|" by (metis card_of_image)
   ultimately have False using A by (metis not_ordLess_ordIso ordLeq_ordLess_trans)
  }
  thus "|Sigma A F| <o r"
  using cr not_ordLess_iff_ordLeq by (metis card_of_Well_order card_order_on_well_order_on)
qed

lemma stable_regularCard:
assumes cr: "Card_order r" and ir: "\<not>finite (Field r)" and st: "stable r"
shows "regularCard r"
unfolding regularCard_def proof safe
  fix K assume K: "K \<subseteq> Field r" and cof: "cofinal K r"
  have "|K| \<le>o r" using K by (metis card_of_Field_ordIso card_of_mono1 cr ordLeq_ordIso_trans)
  moreover
  {assume Kr: "|K| <o r"
   then obtain f where "\<forall> a \<in> Field r. f a \<in> K \<and> a \<noteq> f a \<and> (a, f a) \<in> r"
   using cof unfolding cofinal_def by metis
   hence "Field r \<subseteq> (\<Union> a \<in> K. underS r a)" unfolding underS_def by auto
   hence "r \<le>o |\<Union> a \<in> K. underS r a|" using cr
   by (metis Card_order_iff_ordLeq_card_of card_of_mono1 ordLeq_transitive)
   also have "|\<Union> a \<in> K. underS r a| \<le>o |SIGMA a: K. underS r a|" by (rule card_of_UNION_Sigma)
   also
   {have "\<forall> a \<in> K. |underS r a| <o r" using K by (metis card_of_underS cr subsetD)
    hence "|SIGMA a: K. underS r a| <o r" using st Kr unfolding stable_def by auto
   }
   finally have "r <o r" .
   hence False by (metis ordLess_irreflexive)
  }
  ultimately show "|K| =o r" by (metis ordLeq_iff_ordLess_or_ordIso)
qed

(* Note that below the types of A and F are now unconstrained: *)
lemma stable_elim:
assumes ST: "stable r" and A_LESS: "|A| <o r" and
        F_LESS: "\<And> a. a \<in> A \<Longrightarrow> |F a| <o r"
shows "|SIGMA a : A. F a| <o r"
proof-
  obtain A' where 1: "A' < Field r \<and> |A'| <o r" and 2: " |A| =o |A'|"
  using internalize_card_of_ordLess[of A r] A_LESS by blast
  then obtain G where 3: "bij_betw G A' A"
  using card_of_ordIso  ordIso_symmetric by blast
  (*  *)
  {fix a assume "a \<in> A"
   hence "\<exists>B'. B' \<le> Field r \<and> |F a| =o |B'| \<and> |B'| <o r"
   using internalize_card_of_ordLess[of "F a" r] F_LESS by blast
  }
  then obtain F' where
  temp: "\<forall>a \<in> A. F' a \<le> Field r \<and> |F a| =o |F' a| \<and> |F' a| <o r"
  using bchoice[of A "\<lambda> a B'. B' \<le> Field r \<and> |F a| =o |B'| \<and> |B'| <o r"] by blast
  hence 4: "\<forall>a \<in> A. F' a \<le> Field r \<and> |F' a| <o r" by auto
  have 5: "\<forall>a \<in> A. |F' a| =o |F a|" using temp ordIso_symmetric by auto
  (*  *)
  have "\<forall>a' \<in> A'. F'(G a') \<le> Field r \<and> |F'(G a')| <o r"
  using 3 4 bij_betw_ball[of G A' A] by auto
  hence "|SIGMA a' : A'. F'(G a')| <o r"
  using ST 1 unfolding stable_def by auto
  moreover have "|SIGMA a' : A'. F'(G a')| =o |SIGMA a : A. F a|"
  using card_of_Sigma_cong[of G A' A F' F] 5 3 by blast
  ultimately show ?thesis using ordIso_symmetric ordIso_ordLess_trans by blast
qed

lemma stable_natLeq: "stable natLeq"
proof(unfold stable_def, safe)
  fix A :: "'a set" and F :: "'a \<Rightarrow> 'a set"
  assume "|A| <o natLeq" and "\<forall>a\<in>A. |F a| <o natLeq"
  hence "finite A \<and> (\<forall>a \<in> A. finite(F a))"
  by (auto simp add: finite_iff_ordLess_natLeq)
  hence "finite(Sigma A F)" by (simp only: finite_SigmaI[of A F])
  thus "|Sigma A F | <o natLeq"
  by (auto simp add: finite_iff_ordLess_natLeq)
qed

corollary regularCard_natLeq: "regularCard natLeq"
using stable_regularCard[OF natLeq_Card_order _ stable_natLeq] Field_natLeq by simp

lemma stable_cardSuc:
assumes CARD: "Card_order r" and INF: "\<not>finite (Field r)"
shows "stable(cardSuc r)"
using infinite_cardSuc_regularCard regularCard_stable
by (metis CARD INF cardSuc_Card_order cardSuc_finite)

lemma stable_UNION:
assumes ST: "stable r" and A_LESS: "|A| <o r" and
        F_LESS: "\<And> a. a \<in> A \<Longrightarrow> |F a| <o r"
shows "|\<Union> a \<in> A. F a| <o r"
proof-
  have "|\<Union> a \<in> A. F a| \<le>o |SIGMA a : A. F a|"
  using card_of_UNION_Sigma by blast
  thus ?thesis using assms stable_elim ordLeq_ordLess_trans by blast
qed

lemma stable_ordIso1:
assumes ST: "stable r" and ISO: "r' =o r"
shows "stable r'"
proof(unfold stable_def, auto)
  fix A::"'b set" and F::"'b \<Rightarrow> 'b set"
  assume "|A| <o r'" and "\<forall>a \<in> A. |F a| <o r'"
  hence "( |A| <o r) \<and> (\<forall>a \<in> A. |F a| <o r)"
  using ISO ordLess_ordIso_trans by blast
  hence "|SIGMA a : A. F a| <o r" using assms stable_elim by blast
  thus "|SIGMA a : A. F a| <o r'"
  using ISO ordIso_symmetric ordLess_ordIso_trans by blast
qed

lemma stable_ordIso2:
assumes ST: "stable r" and ISO: "r =o r'"
shows "stable r'"
using assms stable_ordIso1 ordIso_symmetric by blast

lemma stable_ordIso:
assumes "r =o r'"
shows "stable r = stable r'"
using assms stable_ordIso1 stable_ordIso2 by blast

lemma stable_nat: "stable |UNIV::nat set|"
using stable_natLeq card_of_nat stable_ordIso by auto

text{* Below, the type of "A" is not important -- we just had to choose an appropriate
   type to make "A" possible. What is important is that arbitrarily large
   infinite sets of stable cardinality exist. *}

lemma infinite_stable_exists:
assumes CARD: "\<forall>r \<in> R. Card_order (r::'a rel)"
shows "\<exists>(A :: (nat + 'a set)set).
          \<not>finite A \<and> stable |A| \<and> (\<forall>r \<in> R. r <o |A| )"
proof-
  have "\<exists>(A :: (nat + 'a set)set).
          \<not>finite A \<and> stable |A| \<and> |UNIV::'a set| <o |A|"
  proof(cases "finite (UNIV::'a set)")
    assume Case1: "finite (UNIV::'a set)"
    let ?B = "UNIV::nat set"
    have "\<not>finite(?B <+> {})" using finite_Plus_iff by blast
    moreover
    have "stable |?B|" using stable_natLeq card_of_nat stable_ordIso1 by blast
    hence "stable |?B <+> {}|" using stable_ordIso card_of_Plus_empty1 by blast
    moreover
    have "\<not>finite(Field |?B| ) \<and> finite(Field |UNIV::'a set| )" using Case1 by simp
    hence "|UNIV::'a set| <o |?B|" by (simp add: finite_ordLess_infinite)
    hence "|UNIV::'a set| <o |?B <+> {}|" using card_of_Plus_empty1 ordLess_ordIso_trans by blast
    ultimately show ?thesis by blast
  next
    assume Case1: "\<not>finite (UNIV::'a set)"
    hence *: "\<not>finite(Field |UNIV::'a set| )" by simp
    let ?B = "Field(cardSuc |UNIV::'a set| )"
    have 0: "|?B| =o |{} <+> ?B|" using card_of_Plus_empty2 by blast
    have 1: "\<not>finite ?B" using Case1 card_of_cardSuc_finite by blast
    hence 2: "\<not>finite({} <+> ?B)" using 0 card_of_ordIso_finite by blast
    have "|?B| =o cardSuc |UNIV::'a set|"
    using card_of_Card_order cardSuc_Card_order card_of_Field_ordIso by blast
    moreover have "stable(cardSuc |UNIV::'a set| )"
    using stable_cardSuc * card_of_Card_order by blast
    ultimately have "stable |?B|" using stable_ordIso by blast
    hence 3: "stable |{} <+> ?B|" using stable_ordIso 0 by blast
    have "|UNIV::'a set| <o cardSuc |UNIV::'a set|"
    using card_of_Card_order cardSuc_greater by blast
    moreover have "|?B| =o  cardSuc |UNIV::'a set|"
    using card_of_Card_order cardSuc_Card_order  card_of_Field_ordIso by blast
    ultimately have "|UNIV::'a set| <o |?B|"
    using ordIso_symmetric ordLess_ordIso_trans by blast
    hence "|UNIV::'a set| <o |{} <+> ?B|" using 0 ordLess_ordIso_trans by blast
    thus ?thesis using 2 3 by blast
  qed
  thus ?thesis using CARD card_of_UNIV2 ordLeq_ordLess_trans by blast
qed

corollary infinite_regularCard_exists:
assumes CARD: "\<forall>r \<in> R. Card_order (r::'a rel)"
shows "\<exists>(A :: (nat + 'a set)set).
          \<not>finite A \<and> regularCard |A| \<and> (\<forall>r \<in> R. r <o |A| )"
using infinite_stable_exists[OF CARD] stable_regularCard by (metis Field_card_of card_of_card_order_on)

end
