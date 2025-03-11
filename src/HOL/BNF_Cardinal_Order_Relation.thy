(*  Title:      HOL/BNF_Cardinal_Order_Relation.thy
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jan van Brügge, TU Muenchen
    Copyright   2012, 2022

Cardinal-order relations as needed by bounded natural functors.
*)

section \<open>Cardinal-Order Relations as Needed by Bounded Natural Functors\<close>

theory BNF_Cardinal_Order_Relation
  imports Zorn BNF_Wellorder_Constructions
begin

text\<open>In this section, we define cardinal-order relations to be minim well-orders
on their field.  Then we define the cardinal of a set to be {\em some} cardinal-order
relation on that set, which will be unique up to order isomorphism.  Then we study
the connection between cardinals and:
\begin{itemize}
\item standard set-theoretic constructions: products,
sums, unions, lists, powersets, set-of finite sets operator;
\item finiteness and infiniteness (in particular, with the numeric cardinal operator
for finite sets, \<open>card\<close>, from the theory \<open>Finite_Sets.thy\<close>).
\end{itemize}
%
On the way, we define the canonical $\omega$ cardinal and finite cardinals.  We also
define (again, up to order isomorphism) the successor of a cardinal, and show that
any cardinal admits a successor.

Main results of this section are the existence of cardinal relations and the
facts that, in the presence of infiniteness,
most of the standard set-theoretic constructions (except for the powerset)
{\em do not increase cardinality}.  In particular, e.g., the set of words/lists over
any infinite set has the same cardinality (hence, is in bijection) with that set.
\<close>


subsection \<open>Cardinal orders\<close>

text\<open>A cardinal order in our setting shall be a well-order {\em minim} w.r.t. the
order-embedding relation, \<open>\<le>o\<close> (which is the same as being {\em minimal} w.r.t. the
strict order-embedding relation, \<open><o\<close>), among all the well-orders on its field.\<close>

definition card_order_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where
    "card_order_on A r \<equiv> well_order_on A r \<and> (\<forall>r'. well_order_on A r' \<longrightarrow> r \<le>o r')"

abbreviation "Card_order r \<equiv> card_order_on (Field r) r"
abbreviation "card_order r \<equiv> card_order_on UNIV r"

lemma card_order_on_well_order_on:
  assumes "card_order_on A r"
  shows "well_order_on A r"
  using assms unfolding card_order_on_def by simp

lemma card_order_on_Card_order:
  "card_order_on A r \<Longrightarrow> A = Field r \<and> Card_order r"
  unfolding card_order_on_def using well_order_on_Field by blast

text\<open>The existence of a cardinal relation on any given set (which will mean
that any set has a cardinal) follows from two facts:
\begin{itemize}
\item Zermelo's theorem (proved in \<open>Zorn.thy\<close> as theorem \<open>well_order_on\<close>),
which states that on any given set there exists a well-order;
\item The well-founded-ness of \<open><o\<close>, ensuring that then there exists a minimal
such well-order, i.e., a cardinal order.
\end{itemize}
\<close>

theorem card_order_on: "\<exists>r. card_order_on A r"
proof -
  define R where "R \<equiv> {r. well_order_on A r}" 
  have "R \<noteq> {} \<and> (\<forall>r \<in> R. Well_order r)"
    using well_order_on[of A] R_def well_order_on_Well_order by blast
  with exists_minim_Well_order[of R] show ?thesis  
    by (auto simp: R_def card_order_on_def)
qed

lemma card_order_on_ordIso:
  assumes CO: "card_order_on A r" and CO': "card_order_on A r'"
  shows "r =o r'"
  using assms unfolding card_order_on_def
  using ordIso_iff_ordLeq by blast

lemma Card_order_ordIso:
  assumes CO: "Card_order r" and ISO: "r' =o r"
  shows "Card_order r'"
  using ISO unfolding ordIso_def
proof(unfold card_order_on_def, auto)
  fix p' assume "well_order_on (Field r') p'"
  hence 0: "Well_order p' \<and> Field p' = Field r'"
    using well_order_on_Well_order by blast
  obtain f where 1: "iso r' r f" and 2: "Well_order r \<and> Well_order r'"
    using ISO unfolding ordIso_def by auto
  hence 3: "inj_on f (Field r') \<and> f ` (Field r') = Field r"
    by (auto simp add: iso_iff embed_inj_on)
  let ?p = "dir_image p' f"
  have 4: "p' =o ?p \<and> Well_order ?p"
    using 0 2 3 by (auto simp add: dir_image_ordIso Well_order_dir_image)
  moreover have "Field ?p = Field r"
    using 0 3 by (auto simp add: dir_image_Field)
  ultimately have "well_order_on (Field r) ?p" by auto
  hence "r \<le>o ?p" using CO unfolding card_order_on_def by auto
  thus "r' \<le>o p'"
    using ISO 4 ordLeq_ordIso_trans ordIso_ordLeq_trans ordIso_symmetric by blast
qed

lemma Card_order_ordIso2:
  assumes CO: "Card_order r" and ISO: "r =o r'"
  shows "Card_order r'"
  using assms Card_order_ordIso ordIso_symmetric by blast


subsection \<open>Cardinal of a set\<close>

text\<open>We define the cardinal of set to be {\em some} cardinal order on that set.
We shall prove that this notion is unique up to order isomorphism, meaning
that order isomorphism shall be the true identity of cardinals.\<close>

definition card_of :: "'a set \<Rightarrow> 'a rel" (\<open>(\<open>open_block notation=\<open>mixfix card_of\<close>\<close>|_|)\<close>)
  where "card_of A = (SOME r. card_order_on A r)"

lemma card_of_card_order_on: "card_order_on A |A|"
  unfolding card_of_def by (auto simp add: card_order_on someI_ex)

lemma card_of_well_order_on: "well_order_on A |A|"
  using card_of_card_order_on card_order_on_def by blast

lemma Field_card_of: "Field |A| = A"
  using card_of_card_order_on[of A] unfolding card_order_on_def
  using well_order_on_Field by blast

lemma card_of_Card_order: "Card_order |A|"
  by (simp only: card_of_card_order_on Field_card_of)

corollary ordIso_card_of_imp_Card_order:
  "r =o |A| \<Longrightarrow> Card_order r"
  using card_of_Card_order Card_order_ordIso by blast

lemma card_of_Well_order: "Well_order |A|"
  using card_of_Card_order unfolding card_order_on_def by auto

lemma card_of_refl: "|A| =o |A|"
  using card_of_Well_order ordIso_reflexive by blast

lemma card_of_least: "well_order_on A r \<Longrightarrow> |A| \<le>o r"
  using card_of_card_order_on unfolding card_order_on_def by blast

lemma card_of_ordIso:
  "(\<exists>f. bij_betw f A B) = ( |A| =o |B| )"
proof(auto)
  fix f assume *: "bij_betw f A B"
  then obtain r where "well_order_on B r \<and> |A| =o r"
    using Well_order_iso_copy card_of_well_order_on by blast
  hence "|B| \<le>o |A|" using card_of_least
      ordLeq_ordIso_trans ordIso_symmetric by blast
  moreover
  {let ?g = "inv_into A f"
    have "bij_betw ?g B A" using * bij_betw_inv_into by blast
    then obtain r where "well_order_on A r \<and> |B| =o r"
      using Well_order_iso_copy card_of_well_order_on by blast
    hence "|A| \<le>o |B|" 
      using card_of_least ordLeq_ordIso_trans ordIso_symmetric by blast
  }
  ultimately show "|A| =o |B|" using ordIso_iff_ordLeq by blast
next
  assume "|A| =o |B|"
  then obtain f where "iso ( |A| ) ( |B| ) f"
    unfolding ordIso_def by auto
  hence "bij_betw f A B" unfolding iso_def Field_card_of by simp
  thus "\<exists>f. bij_betw f A B" by auto
qed

lemma card_of_ordLeq:
  "(\<exists>f. inj_on f A \<and> f ` A \<le> B) = ( |A| \<le>o |B| )"
proof(auto)
  fix f assume *: "inj_on f A" and **: "f ` A \<le> B"
  {assume "|B| <o |A|"
    hence "|B| \<le>o |A|" using ordLeq_iff_ordLess_or_ordIso by blast
    then obtain g where "embed ( |B| ) ( |A| ) g"
      unfolding ordLeq_def by auto
    hence 1: "inj_on g B \<and> g ` B \<le> A" using embed_inj_on[of "|B|" "|A|" "g"]
        card_of_Well_order[of "B"] Field_card_of[of "B"] Field_card_of[of "A"]
        embed_Field[of "|B|" "|A|" g] by auto
    obtain h where "bij_betw h A B"
      using * ** 1 Schroeder_Bernstein[of f] by fastforce
    hence "|A| \<le>o |B|" using card_of_ordIso ordIso_iff_ordLeq by auto
  }
  thus "|A| \<le>o |B|" using ordLess_or_ordLeq[of "|B|" "|A|"]
    by (auto simp: card_of_Well_order)
next
  assume *: "|A| \<le>o |B|"
  obtain f where "embed |A| |B| f"
    using * unfolding ordLeq_def by auto
  hence "inj_on f A \<and> f ` A \<le> B" 
    using embed_inj_on[of "|A|" "|B|"] card_of_Well_order embed_Field[of "|A|" "|B|"]
    by (auto simp: Field_card_of)
  thus "\<exists>f. inj_on f A \<and> f ` A \<le> B" by auto
qed

lemma card_of_ordLeq2:
  "A \<noteq> {} \<Longrightarrow> (\<exists>g. g ` B = A) = ( |A| \<le>o |B| )"
  using card_of_ordLeq[of A B] inj_on_iff_surj[of A B] by auto

lemma card_of_ordLess:
  "(\<not>(\<exists>f. inj_on f A \<and> f ` A \<le> B)) = ( |B| <o |A| )"
proof -
  have "(\<not>(\<exists>f. inj_on f A \<and> f ` A \<le> B)) = (\<not> |A| \<le>o |B| )"
    using card_of_ordLeq by blast
  also have "\<dots> = ( |B| <o |A| )"
    using  not_ordLeq_iff_ordLess by (auto intro: card_of_Well_order)
  finally show ?thesis .
qed

lemma card_of_ordLess2:
  "B \<noteq> {} \<Longrightarrow> (\<not>(\<exists>f. f ` A = B)) = ( |A| <o |B| )"
  using card_of_ordLess[of B A] inj_on_iff_surj[of B A] by auto

lemma card_of_ordIsoI:
  assumes "bij_betw f A B"
  shows "|A| =o |B|"
  using assms unfolding card_of_ordIso[symmetric] by auto

lemma card_of_ordLeqI:
  assumes "inj_on f A" and "\<And> a. a \<in> A \<Longrightarrow> f a \<in> B"
  shows "|A| \<le>o |B|"
  using assms unfolding card_of_ordLeq[symmetric] by auto

lemma card_of_unique:
  "card_order_on A r \<Longrightarrow> r =o |A|"
  by (simp only: card_order_on_ordIso card_of_card_order_on)

lemma card_of_mono1:
  "A \<le> B \<Longrightarrow> |A| \<le>o |B|"
  using inj_on_id[of A] card_of_ordLeq[of A B] by fastforce

lemma card_of_mono2:
  assumes "r \<le>o r'"
  shows "|Field r| \<le>o |Field r'|"
proof -
  obtain f where
    1: "well_order_on (Field r) r \<and> well_order_on (Field r) r \<and> embed r r' f"
    using assms unfolding ordLeq_def
    by (auto simp add: well_order_on_Well_order)
  hence "inj_on f (Field r) \<and> f ` (Field r) \<le> Field r'"
    by (auto simp add: embed_inj_on embed_Field)
  thus "|Field r| \<le>o |Field r'|" using card_of_ordLeq by blast
qed

lemma card_of_cong: "r =o r' \<Longrightarrow> |Field r| =o |Field r'|"
  by (simp add: ordIso_iff_ordLeq card_of_mono2)

lemma card_of_Field_ordIso:
  assumes "Card_order r"
  shows "|Field r| =o r"
proof -
  have "card_order_on (Field r) r"
    using assms card_order_on_Card_order by blast
  moreover have "card_order_on (Field r) |Field r|"
    using card_of_card_order_on by blast
  ultimately show ?thesis using card_order_on_ordIso by blast
qed

lemma Card_order_iff_ordIso_card_of:
  "Card_order r = (r =o |Field r| )"
  using ordIso_card_of_imp_Card_order card_of_Field_ordIso ordIso_symmetric by blast

lemma Card_order_iff_ordLeq_card_of:
  "Card_order r = (r \<le>o |Field r| )"
proof -
  have "Card_order r = (r =o |Field r| )"
    unfolding Card_order_iff_ordIso_card_of by simp
  also have "\<dots> = (r \<le>o |Field r| \<and> |Field r| \<le>o r)"
    unfolding ordIso_iff_ordLeq by simp
  also have "\<dots> = (r \<le>o |Field r| )"
    using card_of_least
    by (auto simp: card_of_least ordLeq_Well_order_simp)
  finally show ?thesis .
qed

lemma Card_order_iff_Restr_underS:
  assumes "Well_order r"
  shows "Card_order r = (\<forall>a \<in> Field r. Restr r (underS r a) <o |Field r| )"
  using assms ordLeq_iff_ordLess_Restr card_of_Well_order
  unfolding Card_order_iff_ordLeq_card_of  by blast

lemma card_of_underS:
  assumes r: "Card_order r" and a: "a \<in> Field r"
  shows "|underS r a| <o r"
proof -
  let ?A = "underS r a"  let ?r' = "Restr r ?A"
  have 1: "Well_order r"
    using r unfolding card_order_on_def by simp
  have "Well_order ?r'" using 1 Well_order_Restr by auto
  with card_of_card_order_on have "|Field ?r'| \<le>o ?r'"
    unfolding card_order_on_def by auto
  moreover have "Field ?r' = ?A"
    using 1 wo_rel.underS_ofilter Field_Restr_ofilter
    unfolding wo_rel_def by fastforce
  ultimately have "|?A| \<le>o ?r'" by simp
  also have "?r' <o |Field r|"
    using 1 a r Card_order_iff_Restr_underS by blast
  also have "|Field r| =o r"
    using r ordIso_symmetric unfolding Card_order_iff_ordIso_card_of by auto
  finally show ?thesis .
qed

lemma ordLess_Field:
  assumes "r <o r'"
  shows "|Field r| <o r'"
proof -
  have "well_order_on (Field r) r" using assms unfolding ordLess_def
    by (auto simp add: well_order_on_Well_order)
  hence "|Field r| \<le>o r" using card_of_least by blast
  thus ?thesis using assms ordLeq_ordLess_trans by blast
qed

lemma internalize_card_of_ordLeq:
  "( |A| \<le>o r) = (\<exists>B \<le> Field r. |A| =o |B| \<and> |B| \<le>o r)"
proof
  assume "|A| \<le>o r"
  then obtain p where 1: "Field p \<le> Field r \<and> |A| =o p \<and> p \<le>o r"
    using internalize_ordLeq[of "|A|" r] by blast
  hence "Card_order p" using card_of_Card_order Card_order_ordIso2 by blast
  hence "|Field p| =o p" using card_of_Field_ordIso by blast
  hence "|A| =o |Field p| \<and> |Field p| \<le>o r"
    using 1 ordIso_equivalence ordIso_ordLeq_trans by blast
  thus "\<exists>B \<le> Field r. |A| =o |B| \<and> |B| \<le>o r" using 1 by blast
next
  assume "\<exists>B \<le> Field r. |A| =o |B| \<and> |B| \<le>o r"
  thus "|A| \<le>o r" using ordIso_ordLeq_trans by blast
qed

lemma internalize_card_of_ordLeq2:
  "( |A| \<le>o |C| ) = (\<exists>B \<le> C. |A| =o |B| \<and> |B| \<le>o |C| )"
  using internalize_card_of_ordLeq[of "A" "|C|"] Field_card_of[of C] by auto


subsection \<open>Cardinals versus set operations on arbitrary sets\<close>

text\<open>Here we embark in a long journey of simple results showing
that the standard set-theoretic operations are well-behaved w.r.t. the notion of
cardinal -- essentially, this means that they preserve the ``cardinal identity"
\<open>=o\<close> and are monotonic w.r.t. \<open>\<le>o\<close>.
\<close>

lemma card_of_empty: "|{}| \<le>o |A|"
  using card_of_ordLeq inj_on_id by blast

lemma card_of_empty1:
  assumes "Well_order r \<or> Card_order r"
  shows "|{}| \<le>o r"
proof -
  have "Well_order r" using assms unfolding card_order_on_def by auto
  hence "|Field r| \<le>o r"
    using assms card_of_least by blast
  moreover have "|{}| \<le>o |Field r|" by (simp add: card_of_empty)
  ultimately show ?thesis using ordLeq_transitive by blast
qed

corollary Card_order_empty:
  "Card_order r \<Longrightarrow> |{}| \<le>o r" by (simp add: card_of_empty1)

lemma card_of_empty2:
  assumes "|A| =o |{}|"
  shows "A = {}"
  using assms card_of_ordIso[of A] bij_betw_empty2 by blast

lemma card_of_empty3:
  assumes "|A| \<le>o |{}|"
  shows "A = {}"
  using assms
  by (simp add: ordIso_iff_ordLeq card_of_empty1 card_of_empty2
      ordLeq_Well_order_simp)

lemma card_of_empty_ordIso:
  "|{}::'a set| =o |{}::'b set|"
  using card_of_ordIso unfolding bij_betw_def inj_on_def by blast

lemma card_of_image:
  "|f ` A| \<le>o |A|"
proof(cases "A = {}")
  case False
  hence "f ` A \<noteq> {}" by auto
  thus ?thesis
    using card_of_ordLeq2[of "f ` A" A] by auto
qed (simp add: card_of_empty)

lemma surj_imp_ordLeq:
  assumes "B \<subseteq> f ` A"
  shows "|B| \<le>o |A|"
proof -
  have "|B| \<le>o |f ` A|" using assms card_of_mono1 by auto
  thus ?thesis using card_of_image ordLeq_transitive by blast
qed

lemma card_of_singl_ordLeq:
  assumes "A \<noteq> {}"
  shows "|{b}| \<le>o |A|"
proof -
  obtain a where *: "a \<in> A" using assms by auto
  let ?h = "\<lambda> b'::'b. if b' = b then a else undefined"
  have "inj_on ?h {b} \<and> ?h ` {b} \<le> A"
    using * unfolding inj_on_def by auto
  thus ?thesis unfolding card_of_ordLeq[symmetric] by (intro exI)
qed

corollary Card_order_singl_ordLeq:
  "\<lbrakk>Card_order r; Field r \<noteq> {}\<rbrakk> \<Longrightarrow> |{b}| \<le>o r"
  using card_of_singl_ordLeq[of "Field r" b]
    card_of_Field_ordIso[of r] ordLeq_ordIso_trans by blast

lemma card_of_Pow: "|A| <o |Pow A|"
  using card_of_ordLess2[of "Pow A" A]  Cantors_theorem[of A]
    Pow_not_empty[of A] by auto

corollary Card_order_Pow:
  "Card_order r \<Longrightarrow> r <o |Pow(Field r)|"
  using card_of_Pow card_of_Field_ordIso ordIso_ordLess_trans ordIso_symmetric by blast

lemma card_of_Plus1: "|A| \<le>o |A <+> B|" and card_of_Plus2: "|B| \<le>o |A <+> B|"
  using card_of_ordLeq by force+

corollary Card_order_Plus1:
  "Card_order r \<Longrightarrow> r \<le>o |(Field r) <+> B|"
  using card_of_Plus1 card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast

corollary Card_order_Plus2:
  "Card_order r \<Longrightarrow> r \<le>o |A <+> (Field r)|"
  using card_of_Plus2 card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast

lemma card_of_Plus_empty1: "|A| =o |A <+> {}|"
proof -
  have "bij_betw Inl A (A <+> {})" unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by auto
qed

lemma card_of_Plus_empty2: "|A| =o |{} <+> A|"
proof -
  have "bij_betw Inr A ({} <+> A)" unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by auto
qed

lemma card_of_Plus_commute: "|A <+> B| =o |B <+> A|"
proof -
  let ?f = "\<lambda>c. case c of Inl a \<Rightarrow> Inr a | Inr b \<Rightarrow> Inl b"
  have "bij_betw ?f (A <+> B) (B <+> A)"
    unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Plus_assoc:
  fixes A :: "'a set" and B :: "'b set" and C :: "'c set"
  shows "|(A <+> B) <+> C| =o |A <+> B <+> C|"
proof -
  define f :: "('a + 'b) + 'c \<Rightarrow> 'a + 'b + 'c"
    where [abs_def]: "f k =
      (case k of
        Inl ab \<Rightarrow>
          (case ab of
            Inl a \<Rightarrow> Inl a
          | Inr b \<Rightarrow> Inr (Inl b))
      | Inr c \<Rightarrow> Inr (Inr c))"
    for k
  have "A <+> B <+> C \<subseteq> f ` ((A <+> B) <+> C)"
  proof
    fix x assume x: "x \<in> A <+> B <+> C"
    show "x \<in> f ` ((A <+> B) <+> C)"
    proof(cases x)
      case (Inl a)
      hence "a \<in> A" "x = f (Inl (Inl a))"
        using x unfolding f_def by auto
      thus ?thesis by auto
    next
      case (Inr bc) with x show ?thesis 
        by (cases bc) (force simp: f_def)+
    qed
  qed
  hence "bij_betw f ((A <+> B) <+> C) (A <+> B <+> C)"
    unfolding bij_betw_def inj_on_def f_def by fastforce
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Plus_mono1:
  assumes "|A| \<le>o |B|"
  shows "|A <+> C| \<le>o |B <+> C|"
proof -
  obtain f where f: "inj_on f A \<and> f ` A \<le> B"
    using assms card_of_ordLeq[of A] by fastforce
  define g where "g \<equiv> \<lambda>d. case d of Inl a \<Rightarrow> Inl(f a) | Inr (c::'c) \<Rightarrow> Inr c" 
  have "inj_on g (A <+> C) \<and> g ` (A <+> C) \<le> (B <+> C)"
    using f unfolding inj_on_def g_def by force
  thus ?thesis using card_of_ordLeq by blast
qed

corollary ordLeq_Plus_mono1:
  assumes "r \<le>o r'"
  shows "|(Field r) <+> C| \<le>o |(Field r') <+> C|"
  using assms card_of_mono2 card_of_Plus_mono1 by blast

lemma card_of_Plus_mono2:
  assumes "|A| \<le>o |B|"
  shows "|C <+> A| \<le>o |C <+> B|"
  using card_of_Plus_mono1[OF assms]
  by (blast intro: card_of_Plus_commute ordIso_ordLeq_trans ordLeq_ordIso_trans)

corollary ordLeq_Plus_mono2:
  assumes "r \<le>o r'"
  shows "|A <+> (Field r)| \<le>o |A <+> (Field r')|"
  using assms card_of_mono2 card_of_Plus_mono2 by blast

lemma card_of_Plus_mono:
  assumes "|A| \<le>o |B|" and "|C| \<le>o |D|"
  shows "|A <+> C| \<le>o |B <+> D|"
  using assms card_of_Plus_mono1[of A B C] card_of_Plus_mono2[of C D B]
    ordLeq_transitive by blast

corollary ordLeq_Plus_mono:
  assumes "r \<le>o r'" and "p \<le>o p'"
  shows "|(Field r) <+> (Field p)| \<le>o |(Field r') <+> (Field p')|"
  using assms card_of_mono2[of r r'] card_of_mono2[of p p'] card_of_Plus_mono by blast

lemma card_of_Plus_cong1:
  assumes "|A| =o |B|"
  shows "|A <+> C| =o |B <+> C|"
  using assms by (simp add: ordIso_iff_ordLeq card_of_Plus_mono1)

corollary ordIso_Plus_cong1:
  assumes "r =o r'"
  shows "|(Field r) <+> C| =o |(Field r') <+> C|"
  using assms card_of_cong card_of_Plus_cong1 by blast

lemma card_of_Plus_cong2:
  assumes "|A| =o |B|"
  shows "|C <+> A| =o |C <+> B|"
  using assms by (simp add: ordIso_iff_ordLeq card_of_Plus_mono2)

corollary ordIso_Plus_cong2:
  assumes "r =o r'"
  shows "|A <+> (Field r)| =o |A <+> (Field r')|"
  using assms card_of_cong card_of_Plus_cong2 by blast

lemma card_of_Plus_cong:
  assumes "|A| =o |B|" and "|C| =o |D|"
  shows "|A <+> C| =o |B <+> D|"
  using assms by (simp add: ordIso_iff_ordLeq card_of_Plus_mono)

corollary ordIso_Plus_cong:
  assumes "r =o r'" and "p =o p'"
  shows "|(Field r) <+> (Field p)| =o |(Field r') <+> (Field p')|"
  using assms card_of_cong[of r r'] card_of_cong[of p p'] card_of_Plus_cong by blast

lemma card_of_Un_Plus_ordLeq:
  "|A \<union> B| \<le>o |A <+> B|"
proof -
  let ?f = "\<lambda> c. if c \<in> A then Inl c else Inr c"
  have "inj_on ?f (A \<union> B) \<and> ?f ` (A \<union> B) \<le> A <+> B"
    unfolding inj_on_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed

lemma card_of_Times1:
  assumes "A \<noteq> {}"
  shows "|B| \<le>o |B \<times> A|"
proof(cases "B = {}")
  case False
  have "fst `(B \<times> A) = B" using assms by auto
  thus ?thesis using inj_on_iff_surj[of B "B \<times> A"]
      card_of_ordLeq False by blast
qed (simp add: card_of_empty)

lemma card_of_Times_commute: "|A \<times> B| =o |B \<times> A|"
proof -
  have "bij_betw (\<lambda>(a,b). (b,a)) (A \<times> B) (B \<times> A)"
    unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Times2:
  assumes "A \<noteq> {}"   shows "|B| \<le>o |A \<times> B|"
  using assms card_of_Times1[of A B] card_of_Times_commute[of B A]
    ordLeq_ordIso_trans by blast

corollary Card_order_Times1:
  "\<lbrakk>Card_order r; B \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o |(Field r) \<times> B|"
  using card_of_Times1[of B] card_of_Field_ordIso
    ordIso_ordLeq_trans ordIso_symmetric by blast

corollary Card_order_Times2:
  "\<lbrakk>Card_order r; A \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o |A \<times> (Field r)|"
  using card_of_Times2[of A] card_of_Field_ordIso
    ordIso_ordLeq_trans ordIso_symmetric by blast

lemma card_of_Times3: "|A| \<le>o |A \<times> A|"
  using card_of_Times1[of A]
  by(cases "A = {}", simp add: card_of_empty)

lemma card_of_Plus_Times_bool: "|A <+> A| =o |A \<times> (UNIV::bool set)|"
proof -
  let ?f = "\<lambda>c::'a + 'a. case c of Inl a \<Rightarrow> (a,True)
                                  |Inr a \<Rightarrow> (a,False)"
  have "bij_betw ?f (A <+> A) (A \<times> (UNIV::bool set))"
  proof -
    have "\<And>c1 c2. ?f c1 = ?f c2 \<Longrightarrow> c1 = c2" 
      by (force split: sum.split_asm)
    moreover
    have "\<And>c. c \<in> A <+> A \<Longrightarrow> ?f c \<in> A \<times> (UNIV::bool set)"
      by (force split: sum.split_asm)
    moreover
    {fix a bl assume "(a,bl) \<in> A \<times> (UNIV::bool set)"
      hence "(a,bl) \<in> ?f ` ( A <+> A)"
      by (cases bl) (force split: sum.split_asm)+
    }
    ultimately show ?thesis unfolding bij_betw_def inj_on_def by auto
  qed
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Times_mono1:
  assumes "|A| \<le>o |B|"
  shows "|A \<times> C| \<le>o |B \<times> C|"
proof -
  obtain f where f: "inj_on f A \<and> f ` A \<le> B"
    using assms card_of_ordLeq[of A] by fastforce
  define g where "g \<equiv> (\<lambda>(a,c::'c). (f a,c))" 
  have "inj_on g (A \<times> C) \<and> g ` (A \<times> C) \<le> (B \<times> C)"
    using f unfolding inj_on_def using g_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed

corollary ordLeq_Times_mono1:
  assumes "r \<le>o r'"
  shows "|(Field r) \<times> C| \<le>o |(Field r') \<times> C|"
  using assms card_of_mono2 card_of_Times_mono1 by blast

lemma card_of_Times_mono2:
  assumes "|A| \<le>o |B|"
  shows "|C \<times> A| \<le>o |C \<times> B|"
  using assms card_of_Times_mono1[of A B C]
  by (blast intro: card_of_Times_commute ordIso_ordLeq_trans ordLeq_ordIso_trans)

corollary ordLeq_Times_mono2:
  assumes "r \<le>o r'"
  shows "|A \<times> (Field r)| \<le>o |A \<times> (Field r')|"
  using assms card_of_mono2 card_of_Times_mono2 by blast

lemma card_of_Sigma_mono1:
  assumes "\<forall>i \<in> I. |A i| \<le>o |B i|"
  shows "|SIGMA i : I. A i| \<le>o |SIGMA i : I. B i|"
proof -
  have "\<forall>i. i \<in> I \<longrightarrow> (\<exists>f. inj_on f (A i) \<and> f ` (A i) \<le> B i)"
    using assms by (auto simp add: card_of_ordLeq)
  with choice[of "\<lambda> i f. i \<in> I \<longrightarrow> inj_on f (A i) \<and> f ` (A i) \<le> B i"]
  obtain F where F: "\<forall>i \<in> I. inj_on (F i) (A i) \<and> (F i) ` (A i) \<le> B i"
    by atomize_elim (auto intro: bchoice)
  define g where "g \<equiv> (\<lambda>(i,a::'b). (i,F i a))" 
  have "inj_on g (Sigma I A) \<and> g ` (Sigma I A) \<le> (Sigma I B)"
    using F unfolding inj_on_def using g_def by force
  thus ?thesis using card_of_ordLeq by blast
qed

lemma card_of_UNION_Sigma:
  "|\<Union>i \<in> I. A i| \<le>o |SIGMA i : I. A i|"
  using Ex_inj_on_UNION_Sigma [of A I] card_of_ordLeq by blast

lemma card_of_bool:
  assumes "a1 \<noteq> a2"
  shows "|UNIV::bool set| =o |{a1,a2}|"
proof -
  let ?f = "\<lambda> bl. if bl then a1 else a2"
  have "bij_betw ?f UNIV {a1,a2}"
  proof -
    have "\<And>bl1 bl2. ?f bl1 = ?f bl2 \<Longrightarrow> bl1 = bl2"
      using assms by (force split: if_split_asm)
    moreover
    have "\<And>bl. ?f bl \<in> {a1,a2}"
      using assms by (force split: if_split_asm)
    ultimately show ?thesis unfolding bij_betw_def inj_on_def by force
  qed
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Plus_Times_aux:
  assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and
    LEQ: "|A| \<le>o |B|"
  shows "|A <+> B| \<le>o |A \<times> B|"
proof -
  have 1: "|UNIV::bool set| \<le>o |A|"
    using A2 card_of_mono1[of "{a1,a2}"] card_of_bool[of a1 a2]
    by (blast intro: ordIso_ordLeq_trans)
  have "|A <+> B| \<le>o |B <+> B|"
    using LEQ card_of_Plus_mono1 by blast
  moreover have "|B <+> B| =o |B \<times> (UNIV::bool set)|"
    using card_of_Plus_Times_bool by blast
  moreover have "|B \<times> (UNIV::bool set)| \<le>o |B \<times> A|"
    using 1 by (simp add: card_of_Times_mono2)
  moreover have " |B \<times> A| =o |A \<times> B|"
    using card_of_Times_commute by blast
  ultimately show "|A <+> B| \<le>o |A \<times> B|"
    by (blast intro: ordLeq_transitive dest: ordLeq_ordIso_trans)
qed

lemma card_of_Plus_Times:
  assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and B2: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B"
  shows "|A <+> B| \<le>o |A \<times> B|"
proof -
  {assume "|A| \<le>o |B|"
    hence ?thesis using assms by (auto simp add: card_of_Plus_Times_aux)
  }
  moreover
  {assume "|B| \<le>o |A|"
    hence "|B <+> A| \<le>o |B \<times> A|"
      using assms by (auto simp add: card_of_Plus_Times_aux)
    hence ?thesis
      using card_of_Plus_commute card_of_Times_commute
        ordIso_ordLeq_trans ordLeq_ordIso_trans by blast
  }
  ultimately show ?thesis
    using card_of_Well_order[of A] card_of_Well_order[of B]
      ordLeq_total[of "|A|"] by blast
qed

lemma card_of_Times_Plus_distrib:
  "|A \<times> (B <+> C)| =o |A \<times> B <+> A \<times> C|" (is "|?RHS| =o |?LHS|")
proof -
  let ?f = "\<lambda>(a, bc). case bc of Inl b \<Rightarrow> Inl (a, b) | Inr c \<Rightarrow> Inr (a, c)"
  have "bij_betw ?f ?RHS ?LHS" unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_ordLeq_finite:
  assumes "|A| \<le>o |B|" and "finite B"
  shows "finite A"
  using assms unfolding ordLeq_def
  using embed_inj_on[of "|A|" "|B|"]  embed_Field[of "|A|" "|B|"]
    Field_card_of[of "A"] Field_card_of[of "B"] inj_on_finite[of _ "A" "B"] by fastforce

lemma card_of_ordLeq_infinite:
  assumes "|A| \<le>o |B|" and "\<not> finite A"
  shows "\<not> finite B"
  using assms card_of_ordLeq_finite by auto

lemma card_of_ordIso_finite:
  assumes "|A| =o |B|"
  shows "finite A = finite B"
  using assms unfolding ordIso_def iso_def[abs_def]
  by (auto simp: bij_betw_finite Field_card_of)

lemma card_of_ordIso_finite_Field:
  assumes "Card_order r" and "r =o |A|"
  shows "finite(Field r) = finite A"
  using assms card_of_Field_ordIso card_of_ordIso_finite ordIso_equivalence by blast


subsection \<open>Cardinals versus set operations involving infinite sets\<close>

text\<open>Here we show that, for infinite sets, most set-theoretic constructions
do not increase the cardinality.  The cornerstone for this is
theorem \<open>Card_order_Times_same_infinite\<close>, which states that self-product
does not increase cardinality -- the proof of this fact adapts a standard
set-theoretic argument, as presented, e.g., in the proof of theorem 1.5.11
at page 47 in \<^cite>\<open>"card-book"\<close>. Then everything else follows fairly easily.\<close>

lemma infinite_iff_card_of_nat:
  "\<not> finite A \<longleftrightarrow> ( |UNIV::nat set| \<le>o |A| )"
  unfolding infinite_iff_countable_subset card_of_ordLeq ..

text\<open>The next two results correspond to the ZF fact that all infinite cardinals are
limit ordinals:\<close>

lemma Card_order_infinite_not_under:
  assumes CARD: "Card_order r" and INF: "\<not>finite (Field r)"
  shows "\<not> (\<exists>a. Field r = under r a)"
proof(auto)
  have 0: "Well_order r \<and> wo_rel r \<and> Refl r"
    using CARD unfolding wo_rel_def card_order_on_def order_on_defs by auto
  fix a assume *: "Field r = under r a"
  show False
  proof(cases "a \<in> Field r")
    assume Case1: "a \<notin> Field r"
    hence "under r a = {}" unfolding Field_def under_def by auto
    thus False using INF *  by auto
  next
    let ?r' = "Restr r (underS r a)"
    assume Case2: "a \<in> Field r"
    hence 1: "under r a = underS r a \<union> {a} \<and> a \<notin> underS r a"
      using 0 Refl_under_underS[of r a] underS_notIn[of a r] by blast
    have 2: "wo_rel.ofilter r (underS r a) \<and> underS r a < Field r"
      using 0 wo_rel.underS_ofilter * 1 Case2 by fast
    hence "?r' <o r" using 0 using ofilter_ordLess by blast
    moreover
    have "Field ?r' = underS r a \<and> Well_order ?r'"
      using  2 0 Field_Restr_ofilter[of r] Well_order_Restr[of r] by blast
    ultimately have "|underS r a| <o r" using ordLess_Field[of ?r'] by auto
    moreover have "|under r a| =o r" using * CARD card_of_Field_ordIso[of r] by auto
    ultimately have "|underS r a| <o |under r a|"
      using ordIso_symmetric ordLess_ordIso_trans by blast
    moreover
    {have "\<exists>f. bij_betw f (under r a) (underS r a)"
        using infinite_imp_bij_betw[of "Field r" a] INF * 1 by auto
      hence "|under r a| =o |underS r a|" using card_of_ordIso by blast
    }
    ultimately show False using not_ordLess_ordIso ordIso_symmetric by blast
  qed
qed

lemma infinite_Card_order_limit:
  assumes r: "Card_order r" and "\<not>finite (Field r)"
    and a: "a \<in> Field r"
  shows "\<exists>b \<in> Field r. a \<noteq> b \<and> (a,b) \<in> r"
proof -
  have "Field r \<noteq> under r a"
    using assms Card_order_infinite_not_under by blast
  moreover have "under r a \<le> Field r"
    using under_Field .
  ultimately obtain b where b: "b \<in> Field r \<and> \<not> (b,a) \<in> r"
    unfolding under_def by blast
  moreover have ba: "b \<noteq> a"
    using b r unfolding card_order_on_def well_order_on_def
      linear_order_on_def partial_order_on_def preorder_on_def refl_on_def by auto
  ultimately have "(a,b) \<in> r"
    using a r unfolding card_order_on_def well_order_on_def linear_order_on_def
      total_on_def by blast
  thus ?thesis using b ba by auto
qed

theorem Card_order_Times_same_infinite:
  assumes CO: "Card_order r" and INF: "\<not>finite(Field r)"
  shows "|Field r \<times> Field r| \<le>o r"
proof -
  define phi where 
    "phi \<equiv> \<lambda>r::'a rel. Card_order r \<and> \<not>finite(Field r) \<and> \<not> |Field r \<times> Field r| \<le>o r"
  have temp1: "\<forall>r. phi r \<longrightarrow> Well_order r"
    unfolding phi_def card_order_on_def by auto
  have Ft: "\<not>(\<exists>r. phi r)"
  proof
    assume "\<exists>r. phi r"
    hence "{r. phi r} \<noteq> {} \<and> {r. phi r} \<le> {r. Well_order r}"
      using temp1 by auto
    then obtain r where 1: "phi r" and 2: "\<forall>r'. phi r' \<longrightarrow> r \<le>o r'" and
      3: "Card_order r \<and> Well_order r"
      using exists_minim_Well_order[of "{r. phi r}"] temp1 phi_def by blast
    let ?A = "Field r"  let ?r' = "bsqr r"
    have 4: "Well_order ?r' \<and> Field ?r' = ?A \<times> ?A \<and> |?A| =o r"
      using 3 bsqr_Well_order Field_bsqr card_of_Field_ordIso by blast
    have 5: "Card_order |?A \<times> ?A| \<and> Well_order |?A \<times> ?A|"
      using card_of_Card_order card_of_Well_order by blast
        (*  *)
    have "r <o |?A \<times> ?A|"
      using 1 3 5 ordLess_or_ordLeq unfolding phi_def by blast
    moreover have "|?A \<times> ?A| \<le>o ?r'"
      using card_of_least[of "?A \<times> ?A"] 4 by auto
    ultimately have "r <o ?r'" using ordLess_ordLeq_trans by auto
    then obtain f where 6: "embed r ?r' f" and 7: "\<not> bij_betw f ?A (?A \<times> ?A)"
      unfolding ordLess_def embedS_def[abs_def]
      by (auto simp add: Field_bsqr)
    let ?B = "f ` ?A"
    have "|?A| =o |?B|"
      using 3 6 embed_inj_on inj_on_imp_bij_betw card_of_ordIso by blast
    hence 8: "r =o |?B|" using 4 ordIso_transitive ordIso_symmetric by blast
        (*  *)
    have "wo_rel.ofilter ?r' ?B"
      using 6 embed_Field_ofilter 3 4 by blast
    hence "wo_rel.ofilter ?r' ?B \<and> ?B \<noteq> ?A \<times> ?A \<and> ?B \<noteq> Field ?r'"
      using 7 unfolding bij_betw_def using 6 3 embed_inj_on 4 by auto
    hence temp2: "wo_rel.ofilter ?r' ?B \<and> ?B < ?A \<times> ?A"
      using 4 wo_rel_def[of ?r'] wo_rel.ofilter_def[of ?r' ?B] by blast
    have "\<not> (\<exists>a. Field r = under r a)"
      using 1 unfolding phi_def using Card_order_infinite_not_under[of r] by auto
    then obtain A1 where temp3: "wo_rel.ofilter r A1 \<and> A1 < ?A" and 9: "?B \<le> A1 \<times> A1"
      using temp2 3 bsqr_ofilter[of r ?B] by blast
    hence "|?B| \<le>o |A1 \<times> A1|" using card_of_mono1 by blast
    hence 10: "r \<le>o |A1 \<times> A1|" using 8 ordIso_ordLeq_trans by blast
    let ?r1 = "Restr r A1"
    have "?r1 <o r" using temp3 ofilter_ordLess 3 by blast
    moreover
    {have "well_order_on A1 ?r1" using 3 temp3 well_order_on_Restr by blast
      hence "|A1| \<le>o ?r1" using 3 Well_order_Restr card_of_least by blast
    }
    ultimately have 11: "|A1| <o r" using ordLeq_ordLess_trans by blast
        (*  *)
    have "\<not> finite (Field r)" using 1 unfolding phi_def by simp
    hence "\<not> finite ?B" using 8 3 card_of_ordIso_finite_Field[of r ?B] by blast
    hence "\<not> finite A1" using 9 finite_cartesian_product finite_subset by blast
    moreover have temp4: "Field |A1| = A1 \<and> Well_order |A1| \<and> Card_order |A1|"
      using card_of_Card_order[of A1] card_of_Well_order[of A1]
      by (simp add: Field_card_of)
    moreover have "\<not> r \<le>o | A1 |"
      using temp4 11 3 using not_ordLeq_iff_ordLess by blast
    ultimately have "\<not> finite(Field |A1| ) \<and> Card_order |A1| \<and> \<not> r \<le>o | A1 |"
      by (simp add: card_of_card_order_on)
    hence "|Field |A1| \<times> Field |A1| | \<le>o |A1|"
      using 2 unfolding phi_def by blast
    hence "|A1 \<times> A1 | \<le>o |A1|" using temp4 by auto
    hence "r \<le>o |A1|" using 10 ordLeq_transitive by blast
    thus False using 11 not_ordLess_ordLeq by auto
  qed
  thus ?thesis using assms unfolding phi_def by blast
qed

corollary card_of_Times_same_infinite:
  assumes "\<not>finite A"
  shows "|A \<times> A| =o |A|"
proof -
  let ?r = "|A|"
  have "Field ?r = A \<and> Card_order ?r"
    using Field_card_of card_of_Card_order[of A] by fastforce
  hence "|A \<times> A| \<le>o |A|"
    using Card_order_Times_same_infinite[of ?r] assms by auto
  thus ?thesis using card_of_Times3 ordIso_iff_ordLeq by blast
qed

lemma card_of_Times_infinite:
  assumes INF: "\<not>finite A" and NE: "B \<noteq> {}" and LEQ: "|B| \<le>o |A|"
  shows "|A \<times> B| =o |A| \<and> |B \<times> A| =o |A|"
proof -
  have "|A| \<le>o |A \<times> B| \<and> |A| \<le>o |B \<times> A|"
    using assms by (simp add: card_of_Times1 card_of_Times2)
  moreover
  {have "|A \<times> B| \<le>o |A \<times> A| \<and> |B \<times> A| \<le>o |A \<times> A|"
      using LEQ card_of_Times_mono1 card_of_Times_mono2 by blast
    moreover have "|A \<times> A| =o |A|" using INF card_of_Times_same_infinite by blast
    ultimately have "|A \<times> B| \<le>o |A| \<and> |B \<times> A| \<le>o |A|"
      using ordLeq_ordIso_trans[of "|A \<times> B|"] ordLeq_ordIso_trans[of "|B \<times> A|"] by auto
  }
  ultimately show ?thesis by (simp add: ordIso_iff_ordLeq)
qed

corollary Card_order_Times_infinite:
  assumes INF: "\<not>finite(Field r)" and CARD: "Card_order r" and
    NE: "Field p \<noteq> {}" and LEQ: "p \<le>o r"
  shows "| (Field r) \<times> (Field p) | =o r \<and> | (Field p) \<times> (Field r) | =o r"
proof -
  have "|Field r \<times> Field p| =o |Field r| \<and> |Field p \<times> Field r| =o |Field r|"
    using assms by (simp add: card_of_Times_infinite card_of_mono2)
  thus ?thesis
    using assms card_of_Field_ordIso by (blast intro: ordIso_transitive)
qed

lemma card_of_Sigma_ordLeq_infinite:
  assumes INF: "\<not>finite B" and
    LEQ_I: "|I| \<le>o |B|" and LEQ: "\<forall>i \<in> I. |A i| \<le>o |B|"
  shows "|SIGMA i : I. A i| \<le>o |B|"
proof(cases "I = {}")
  case False
  have "|SIGMA i : I. A i| \<le>o |I \<times> B|"
    using card_of_Sigma_mono1[OF LEQ] by blast
  moreover have "|I \<times> B| =o |B|"
    using INF False LEQ_I by (auto simp add: card_of_Times_infinite)
  ultimately show ?thesis using ordLeq_ordIso_trans by blast
qed (simp add: card_of_empty)

lemma card_of_Sigma_ordLeq_infinite_Field:
  assumes INF: "\<not>finite (Field r)" and r: "Card_order r" and
    LEQ_I: "|I| \<le>o r" and LEQ: "\<forall>i \<in> I. |A i| \<le>o r"
  shows "|SIGMA i : I. A i| \<le>o r"
proof -
  let ?B  = "Field r"
  have 1: "r =o |?B| \<and> |?B| =o r" 
    using r card_of_Field_ordIso ordIso_symmetric by blast
  hence "|I| \<le>o |?B|"  "\<forall>i \<in> I. |A i| \<le>o |?B|"
    using LEQ_I LEQ ordLeq_ordIso_trans by blast+
  hence  "|SIGMA i : I. A i| \<le>o |?B|" using INF LEQ
      card_of_Sigma_ordLeq_infinite by blast
  thus ?thesis using 1 ordLeq_ordIso_trans by blast
qed

lemma card_of_Times_ordLeq_infinite_Field:
  "\<lbrakk>\<not>finite (Field r); |A| \<le>o r; |B| \<le>o r; Card_order r\<rbrakk> \<Longrightarrow> |A \<times> B| \<le>o r"
  by(simp add: card_of_Sigma_ordLeq_infinite_Field)

lemma card_of_Times_infinite_simps:
  "\<lbrakk>\<not>finite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |A \<times> B| =o |A|"
  "\<lbrakk>\<not>finite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |A| =o |A \<times> B|"
  "\<lbrakk>\<not>finite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |B \<times> A| =o |A|"
  "\<lbrakk>\<not>finite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |A| =o |B \<times> A|"
  by (auto simp add: card_of_Times_infinite ordIso_symmetric)

lemma card_of_UNION_ordLeq_infinite:
  assumes INF: "\<not>finite B" and LEQ_I: "|I| \<le>o |B|" and LEQ: "\<forall>i \<in> I. |A i| \<le>o |B|"
  shows "|\<Union>i \<in> I. A i| \<le>o |B|"
proof(cases "I = {}")
  case False
  have "|\<Union>i \<in> I. A i| \<le>o |SIGMA i : I. A i|"
    using card_of_UNION_Sigma by blast
  moreover have "|SIGMA i : I. A i| \<le>o |B|"
    using assms card_of_Sigma_ordLeq_infinite by blast
  ultimately show ?thesis using ordLeq_transitive by blast
qed (simp add: card_of_empty)

corollary card_of_UNION_ordLeq_infinite_Field:
  assumes INF: "\<not>finite (Field r)" and r: "Card_order r" and
    LEQ_I: "|I| \<le>o r" and LEQ: "\<forall>i \<in> I. |A i| \<le>o r"
  shows "|\<Union>i \<in> I. A i| \<le>o r"
proof -
  let ?B  = "Field r"
  have 1: "r =o |?B| \<and> |?B| =o r" 
    using r card_of_Field_ordIso ordIso_symmetric by blast
  hence "|I| \<le>o |?B|"  "\<forall>i \<in> I. |A i| \<le>o |?B|"
    using LEQ_I LEQ ordLeq_ordIso_trans by blast+
  hence  "|\<Union>i \<in> I. A i| \<le>o |?B|" using INF LEQ
      card_of_UNION_ordLeq_infinite by blast
  thus ?thesis using 1 ordLeq_ordIso_trans by blast
qed

lemma card_of_Plus_infinite1:
  assumes INF: "\<not>finite A" and LEQ: "|B| \<le>o |A|"
  shows "|A <+> B| =o |A|"
proof(cases "B = {}")
  case True
  then show ?thesis
    by (simp add: card_of_Plus_empty1 card_of_Plus_empty2 ordIso_symmetric)
next
  case False
  let ?Inl = "Inl::'a \<Rightarrow> 'a + 'b"  let ?Inr = "Inr::'b \<Rightarrow> 'a + 'b"
  assume *: "B \<noteq> {}"
  then obtain b1 where 1: "b1 \<in> B" by blast
  show ?thesis
  proof(cases "B = {b1}")
    case True
    have 2: "bij_betw ?Inl A ((?Inl ` A))"
      unfolding bij_betw_def inj_on_def by auto
    hence 3: "\<not>finite (?Inl ` A)"
      using INF bij_betw_finite[of ?Inl A] by blast
    let ?A' = "?Inl ` A \<union> {?Inr b1}"
    obtain g where "bij_betw g (?Inl ` A) ?A'"
      using 3 infinite_imp_bij_betw2[of "?Inl ` A"] by auto
    moreover have "?A' = A <+> B" using True by blast
    ultimately have "bij_betw g (?Inl ` A) (A <+> B)" by simp
    hence "bij_betw (g \<circ> ?Inl) A (A <+> B)"
      using 2 by (auto simp add: bij_betw_trans)
    thus ?thesis using card_of_ordIso ordIso_symmetric by blast
  next
    case False
    with * 1 obtain b2 where 3: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B" by fastforce
    obtain f where "inj_on f B \<and> f ` B \<le> A"
      using LEQ card_of_ordLeq[of B] by fastforce
    with 3 have "f b1 \<noteq> f b2 \<and> {f b1, f b2} \<le> A"
      unfolding inj_on_def by auto
    with 3 have "|A <+> B| \<le>o |A \<times> B|"
      by (auto simp add: card_of_Plus_Times)
    moreover have "|A \<times> B| =o |A|"
      using assms * by (simp add: card_of_Times_infinite_simps)
    ultimately have "|A <+> B| \<le>o |A|" using ordLeq_ordIso_trans by blast
    thus ?thesis using card_of_Plus1 ordIso_iff_ordLeq by blast
  qed
qed

lemma card_of_Plus_infinite2:
  assumes INF: "\<not>finite A" and LEQ: "|B| \<le>o |A|"
  shows "|B <+> A| =o |A|"
  using assms card_of_Plus_commute card_of_Plus_infinite1
    ordIso_equivalence by blast

lemma card_of_Plus_infinite:
  assumes INF: "\<not>finite A" and LEQ: "|B| \<le>o |A|"
  shows "|A <+> B| =o |A| \<and> |B <+> A| =o |A|"
  using assms by (auto simp: card_of_Plus_infinite1 card_of_Plus_infinite2)

corollary Card_order_Plus_infinite:
  assumes INF: "\<not>finite(Field r)" and CARD: "Card_order r" and
    LEQ: "p \<le>o r"
  shows "| (Field r) <+> (Field p) | =o r \<and> | (Field p) <+> (Field r) | =o r"
proof -
  have "| Field r <+> Field p | =o | Field r | \<and>
        | Field p <+> Field r | =o | Field r |"
    using assms by (simp add: card_of_Plus_infinite card_of_mono2)
  thus ?thesis
    using assms card_of_Field_ordIso by (blast intro: ordIso_transitive)

qed


subsection \<open>The cardinal $\omega$ and the finite cardinals\<close>

text\<open>The cardinal $\omega$, of natural numbers, shall be the standard non-strict
order relation on
\<open>nat\<close>, that we abbreviate by \<open>natLeq\<close>.  The finite cardinals
shall be the restrictions of these relations to the numbers smaller than
fixed numbers \<open>n\<close>, that we abbreviate by \<open>natLeq_on n\<close>.\<close>

definition "(natLeq::(nat * nat) set) \<equiv> {(x,y). x \<le> y}"
definition "(natLess::(nat * nat) set) \<equiv> {(x,y). x < y}"

abbreviation natLeq_on :: "nat \<Rightarrow> (nat * nat) set"
  where "natLeq_on n \<equiv> {(x,y). x < n \<and> y < n \<and> x \<le> y}"

lemma infinite_cartesian_product:
  assumes "\<not>finite A" "\<not>finite B"
  shows "\<not>finite (A \<times> B)"
using assms finite_cartesian_productD2 by auto


subsubsection \<open>First as well-orders\<close>

lemma Field_natLeq: "Field natLeq = (UNIV::nat set)"
  by(unfold Field_def natLeq_def, auto)

lemma natLeq_Refl: "Refl natLeq"
  unfolding refl_on_def Field_def natLeq_def by auto

lemma natLeq_trans: "trans natLeq"
  unfolding trans_def natLeq_def by auto

lemma natLeq_Preorder: "Preorder natLeq"
  unfolding preorder_on_def
proof (intro conjI)
  show "natLeq \<subseteq> Field natLeq \<times> Field natLeq"
    unfolding natLeq_def Field_def by blast
next
  show "Refl natLeq"
    using natLeq_Refl .
next
  show "trans natLeq"
    using natLeq_trans .
qed

lemma natLeq_antisym: "antisym natLeq"
  unfolding antisym_def natLeq_def by auto

lemma natLeq_Partial_order: "Partial_order natLeq"
  unfolding partial_order_on_def
  by (auto simp add: natLeq_Preorder natLeq_antisym)

lemma natLeq_Total: "Total natLeq"
  unfolding total_on_def natLeq_def by auto

lemma natLeq_Linear_order: "Linear_order natLeq"
  unfolding linear_order_on_def
  by (auto simp add: natLeq_Partial_order natLeq_Total)

lemma natLeq_natLess_Id: "natLess = natLeq - Id"
  unfolding natLeq_def natLess_def by auto

lemma natLeq_Well_order: "Well_order natLeq"
  unfolding well_order_on_def
  using natLeq_Linear_order wf_less natLeq_natLess_Id natLeq_def natLess_def by auto

lemma Field_natLeq_on: "Field (natLeq_on n) = {x. x < n}"
  unfolding Field_def by auto

lemma natLeq_underS_less: "underS natLeq n = {x. x < n}"
  unfolding underS_def natLeq_def by auto

lemma Restr_natLeq: "Restr natLeq {x. x < n} = natLeq_on n"
  unfolding natLeq_def by force

lemma Restr_natLeq2:
  "Restr natLeq (underS natLeq n) = natLeq_on n"
  by (auto simp add: Restr_natLeq natLeq_underS_less)

lemma natLeq_on_Well_order: "Well_order(natLeq_on n)"
  using Restr_natLeq[of n] natLeq_Well_order
    Well_order_Restr[of natLeq "{x. x < n}"] by auto

corollary natLeq_on_well_order_on: "well_order_on {x. x < n} (natLeq_on n)"
  using natLeq_on_Well_order Field_natLeq_on by auto

lemma natLeq_on_wo_rel: "wo_rel(natLeq_on n)"
  unfolding wo_rel_def using natLeq_on_Well_order .


subsubsection \<open>Then as cardinals\<close>

lemma natLeq_Card_order: "Card_order natLeq"
proof -
  have "natLeq_on n <o |UNIV::nat set|" for n
  proof -
    have "finite(Field (natLeq_on n))" by (auto simp: Field_def)
    moreover have "\<not>finite(UNIV::nat set)" by auto
    ultimately show ?thesis
      using finite_ordLess_infinite[of "natLeq_on n" "|UNIV::nat set|"]
        card_of_Well_order[of "UNIV::nat set"] natLeq_on_Well_order
      by (force simp add: Field_card_of)
  qed
  then show ?thesis
    apply (simp add: natLeq_Well_order Card_order_iff_Restr_underS Restr_natLeq2)
    apply (force simp add: Field_natLeq)
    done
qed

corollary card_of_Field_natLeq:
  "|Field natLeq| =o natLeq"
  using Field_natLeq natLeq_Card_order Card_order_iff_ordIso_card_of[of natLeq]
    ordIso_symmetric[of natLeq] by blast

corollary card_of_nat:
  "|UNIV::nat set| =o natLeq"
  using Field_natLeq card_of_Field_natLeq by auto

corollary infinite_iff_natLeq_ordLeq:
  "\<not>finite A = ( natLeq \<le>o |A| )"
  using infinite_iff_card_of_nat[of A] card_of_nat
    ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric by blast

corollary finite_iff_ordLess_natLeq:
  "finite A = ( |A| <o natLeq)"
  using infinite_iff_natLeq_ordLeq not_ordLeq_iff_ordLess
    card_of_Well_order natLeq_Well_order by blast


subsection \<open>The successor of a cardinal\<close>

text\<open>First we define \<open>isCardSuc r r'\<close>, the notion of \<open>r'\<close>
being a successor cardinal of \<open>r\<close>. Although the definition does
not require \<open>r\<close> to be a cardinal, only this case will be meaningful.\<close>

definition isCardSuc :: "'a rel \<Rightarrow> 'a set rel \<Rightarrow> bool"
  where
    "isCardSuc r r' \<equiv>
         Card_order r' \<and> r <o r' \<and>
         (\<forall>(r''::'a set rel). Card_order r'' \<and> r <o r'' \<longrightarrow> r' \<le>o r'')"

text\<open>Now we introduce the cardinal-successor operator \<open>cardSuc\<close>,
by picking {\em some} cardinal-order relation fulfilling \<open>isCardSuc\<close>.
Again, the picked item shall be proved unique up to order-isomorphism.\<close>

definition cardSuc :: "'a rel \<Rightarrow> 'a set rel"
  where "cardSuc r \<equiv> SOME r'. isCardSuc r r'"

lemma exists_minim_Card_order:
  "\<lbrakk>R \<noteq> {}; \<forall>r \<in> R. Card_order r\<rbrakk> \<Longrightarrow> \<exists>r \<in> R. \<forall>r' \<in> R. r \<le>o r'"
  unfolding card_order_on_def using exists_minim_Well_order by blast

lemma exists_isCardSuc:
  assumes "Card_order r"
  shows "\<exists>r'. isCardSuc r r'"
proof -
  let ?R = "{(r'::'a set rel). Card_order r' \<and> r <o r'}"
  have "|Pow(Field r)| \<in> ?R \<and> (\<forall>r \<in> ?R. Card_order r)" using assms
    by (simp add: card_of_Card_order Card_order_Pow)
  then obtain r where "r \<in> ?R \<and> (\<forall>r' \<in> ?R. r \<le>o r')"
    using exists_minim_Card_order[of ?R] by blast
  thus ?thesis unfolding isCardSuc_def by auto
qed

lemma cardSuc_isCardSuc:
  assumes "Card_order r"
  shows "isCardSuc r (cardSuc r)"
  unfolding cardSuc_def using assms
  by (simp add: exists_isCardSuc someI_ex)

lemma cardSuc_Card_order:
  "Card_order r \<Longrightarrow> Card_order(cardSuc r)"
  using cardSuc_isCardSuc unfolding isCardSuc_def by blast

lemma cardSuc_greater:
  "Card_order r \<Longrightarrow> r <o cardSuc r"
  using cardSuc_isCardSuc unfolding isCardSuc_def by blast

lemma cardSuc_ordLeq:
  "Card_order r \<Longrightarrow> r \<le>o cardSuc r"
  using cardSuc_greater ordLeq_iff_ordLess_or_ordIso by blast

text\<open>The minimality property of \<open>cardSuc\<close> originally present in its definition
is local to the type \<open>'a set rel\<close>, i.e., that of \<open>cardSuc r\<close>:\<close>

lemma cardSuc_least_aux:
  "\<lbrakk>Card_order (r::'a rel); Card_order (r'::'a set rel); r <o r'\<rbrakk> \<Longrightarrow> cardSuc r \<le>o r'"
  using cardSuc_isCardSuc unfolding isCardSuc_def by blast

text\<open>But from this we can infer general minimality:\<close>

lemma cardSuc_least:
  assumes CARD: "Card_order r" and CARD': "Card_order r'" and LESS: "r <o r'"
  shows "cardSuc r \<le>o r'"
proof -
  let ?p = "cardSuc r"
  have 0: "Well_order ?p \<and> Well_order r'"
    using assms cardSuc_Card_order unfolding card_order_on_def by blast
  { assume "r' <o ?p"
    then obtain r'' where 1: "Field r'' < Field ?p" and 2: "r' =o r'' \<and> r'' <o ?p"
      using internalize_ordLess[of r' ?p] by blast
        (*  *)
    have "Card_order r''" using CARD' Card_order_ordIso2 2 by blast
    moreover have "r <o r''" using LESS 2 ordLess_ordIso_trans by blast
    ultimately have "?p \<le>o r''" using cardSuc_least_aux CARD by blast
    hence False using 2 not_ordLess_ordLeq by blast
  }
  thus ?thesis using 0 ordLess_or_ordLeq by blast
qed

lemma cardSuc_ordLess_ordLeq:
  assumes CARD: "Card_order r" and CARD': "Card_order r'"
  shows "(r <o r') = (cardSuc r \<le>o r')"
proof 
  show "cardSuc r \<le>o r' \<Longrightarrow> r <o r'"
    using assms cardSuc_greater ordLess_ordLeq_trans by blast
qed (auto simp add: assms cardSuc_least)

lemma cardSuc_ordLeq_ordLess:
  assumes CARD: "Card_order r" and CARD': "Card_order r'"
  shows "(r' <o cardSuc r) = (r' \<le>o r)"
proof -
  have "Well_order r \<and> Well_order r'"
    using assms unfolding card_order_on_def by auto
  moreover have "Well_order(cardSuc r)"
    using assms cardSuc_Card_order card_order_on_def by blast
  ultimately show ?thesis
    using assms cardSuc_ordLess_ordLeq by (blast dest: not_ordLeq_iff_ordLess)
qed

lemma cardSuc_mono_ordLeq:
  assumes CARD: "Card_order r" and CARD': "Card_order r'"
  shows "(cardSuc r \<le>o cardSuc r') = (r \<le>o r')"
  using assms cardSuc_ordLeq_ordLess cardSuc_ordLess_ordLeq cardSuc_Card_order by blast

lemma cardSuc_invar_ordIso:
  assumes CARD: "Card_order r" and CARD': "Card_order r'"
  shows "(cardSuc r =o cardSuc r') = (r =o r')"
proof -
  have 0: "Well_order r \<and> Well_order r' \<and> Well_order(cardSuc r) \<and> Well_order(cardSuc r')"
    using assms by (simp add: card_order_on_well_order_on cardSuc_Card_order)
  thus ?thesis
    using ordIso_iff_ordLeq[of r r'] ordIso_iff_ordLeq
    using cardSuc_mono_ordLeq[of r r'] cardSuc_mono_ordLeq[of r' r] assms by blast
qed

lemma card_of_cardSuc_finite:
  "finite(Field(cardSuc |A| )) = finite A"
proof
  assume *: "finite (Field (cardSuc |A| ))"
  have 0: "|Field(cardSuc |A| )| =o cardSuc |A|"
    using card_of_Card_order cardSuc_Card_order card_of_Field_ordIso by blast
  hence "|A| \<le>o |Field(cardSuc |A| )|"
    using card_of_Card_order[of A] cardSuc_ordLeq[of "|A|"] ordIso_symmetric
      ordLeq_ordIso_trans by blast
  thus "finite A" using * card_of_ordLeq_finite by blast
next
  assume "finite A"
  then have "finite ( Field |Pow A| )" unfolding Field_card_of by simp
  moreover
  have "cardSuc |A| \<le>o |Pow A|"
    by (rule iffD1[OF cardSuc_ordLess_ordLeq card_of_Pow]) (simp_all add: card_of_Card_order)
  ultimately show "finite (Field (cardSuc |A| ))"
    by (blast intro: card_of_ordLeq_finite card_of_mono2)
qed

lemma cardSuc_finite:
  assumes "Card_order r"
  shows "finite (Field (cardSuc r)) = finite (Field r)"
proof -
  let ?A = "Field r"
  have "|?A| =o r" using assms by (simp add: card_of_Field_ordIso)
  hence "cardSuc |?A| =o cardSuc r" using assms
    by (simp add: card_of_Card_order cardSuc_invar_ordIso)
  moreover have "|Field (cardSuc |?A| ) | =o cardSuc |?A|"
    by (simp add: card_of_card_order_on Field_card_of card_of_Field_ordIso cardSuc_Card_order)
  moreover
  { have "|Field (cardSuc r) | =o cardSuc r"
      using assms by (simp add: card_of_Field_ordIso cardSuc_Card_order)
    hence "cardSuc r =o |Field (cardSuc r) |"
      using ordIso_symmetric by blast
  }
  ultimately have "|Field (cardSuc |?A| ) | =o |Field (cardSuc r) |"
    using ordIso_transitive by blast
  hence "finite (Field (cardSuc |?A| )) = finite (Field (cardSuc r))"
    using card_of_ordIso_finite by blast
  thus ?thesis by (simp only: card_of_cardSuc_finite)
qed

lemma Field_cardSuc_not_empty:
  assumes "Card_order r"
  shows "Field (cardSuc r) \<noteq> {}"
proof
  assume "Field(cardSuc r) = {}"
  then have "|Field(cardSuc r)| \<le>o r" using assms Card_order_empty[of r] by auto
  then have "cardSuc r \<le>o r" using assms card_of_Field_ordIso
      cardSuc_Card_order ordIso_symmetric ordIso_ordLeq_trans by blast
  then show False using cardSuc_greater not_ordLess_ordLeq assms by blast
qed

typedef 'a suc = "Field (cardSuc |UNIV :: 'a set| )"
  using Field_cardSuc_not_empty card_of_Card_order by blast

definition card_suc :: "'a rel \<Rightarrow> 'a suc rel" where
  "card_suc \<equiv> \<lambda>_. map_prod Abs_suc Abs_suc ` cardSuc |UNIV :: 'a set|"

lemma Field_card_suc: "Field (card_suc r) = UNIV"
proof -
  let ?r = "cardSuc |UNIV|"
  let ?ar = "\<lambda>x. Abs_suc (Rep_suc x)"
  have 1: "\<And>P. (\<forall>x\<in>Field ?r. P x) = (\<forall>x. P (Rep_suc x))" using Rep_suc_induct Rep_suc by blast
  have 2: "\<And>P. (\<exists>x\<in>Field ?r. P x) = (\<exists>x. P (Rep_suc x))" using Rep_suc_cases Rep_suc by blast
  have 3: "\<And>A a b. (a, b) \<in> A \<Longrightarrow> (Abs_suc a, Abs_suc b) \<in> map_prod Abs_suc Abs_suc ` A" unfolding map_prod_def by auto
  have "\<forall>x\<in>Field ?r. (\<exists>b\<in>Field ?r. (x, b) \<in> ?r) \<or> (\<exists>a\<in>Field ?r. (a, x) \<in> ?r)"
    unfolding Field_def Range.simps Domain.simps Un_iff by blast
  then have "\<forall>x. (\<exists>b. (Rep_suc x, Rep_suc b) \<in> ?r) \<or> (\<exists>a. (Rep_suc a, Rep_suc x) \<in> ?r)" unfolding 1 2 .
  then have "\<forall>x. (\<exists>b. (?ar x, ?ar b) \<in> map_prod Abs_suc Abs_suc ` ?r) \<or> (\<exists>a. (?ar a, ?ar x) \<in> map_prod Abs_suc Abs_suc ` ?r)" using 3 by fast
  then have "\<forall>x. (\<exists>b. (x, b) \<in> card_suc r) \<or> (\<exists>a. (a, x) \<in> card_suc r)" unfolding card_suc_def Rep_suc_inverse .
  then show ?thesis unfolding Field_def Domain.simps Range.simps set_eq_iff Un_iff eqTrueI[OF UNIV_I] ex_simps simp_thms .
qed

lemma card_suc_alt: "card_suc r = dir_image (cardSuc |UNIV :: 'a set| ) Abs_suc"
  unfolding card_suc_def dir_image_def by auto

lemma cardSuc_Well_order: "Card_order r \<Longrightarrow> Well_order(cardSuc r)"
  using cardSuc_Card_order unfolding card_order_on_def by blast

lemma cardSuc_ordIso_card_suc:
  assumes "card_order r"
  shows "cardSuc r =o card_suc (r :: 'a rel)"
proof -
  have "cardSuc (r :: 'a rel) =o cardSuc |UNIV :: 'a set|"
    using cardSuc_invar_ordIso[THEN iffD2, OF _ card_of_Card_order card_of_unique[OF assms]] assms
    by (simp add: card_order_on_Card_order)
  also have "cardSuc |UNIV :: 'a set| =o card_suc (r :: 'a rel)"
    unfolding card_suc_alt
    by (rule dir_image_ordIso) (simp_all add: inj_on_def Abs_suc_inject cardSuc_Well_order card_of_Card_order)
  finally show ?thesis .
qed

lemma Card_order_card_suc: "card_order r \<Longrightarrow> Card_order (card_suc r)"
  using cardSuc_Card_order[THEN Card_order_ordIso2[OF _ cardSuc_ordIso_card_suc]] card_order_on_Card_order by blast

lemma card_order_card_suc: "card_order r \<Longrightarrow> card_order (card_suc r)"
  using Card_order_card_suc arg_cong2[OF Field_card_suc refl, of "card_order_on"] by blast

lemma card_suc_greater: "card_order r \<Longrightarrow> r <o card_suc r"
  using ordLess_ordIso_trans[OF cardSuc_greater cardSuc_ordIso_card_suc] card_order_on_Card_order by blast

lemma card_of_Plus_ordLess_infinite:
  assumes INF: "\<not>finite C" and LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
  shows "|A <+> B| <o |C|"
proof(cases "A = {} \<or> B = {}")
  case True
  hence "|A| =o |A <+> B| \<or> |B| =o |A <+> B|"
    using card_of_Plus_empty1 card_of_Plus_empty2 by blast
  hence "|A <+> B| =o |A| \<or> |A <+> B| =o |B|"
    using ordIso_symmetric[of "|A|"] ordIso_symmetric[of "|B|"] by blast
  thus ?thesis using LESS1 LESS2
      ordIso_ordLess_trans[of "|A <+> B|" "|A|"]
      ordIso_ordLess_trans[of "|A <+> B|" "|B|"] by blast
next
  case False
  have False if "|C| \<le>o |A <+> B|"
  proof -
    have \<section>: "\<not>finite A \<or> \<not>finite B" 
      using that INF card_of_ordLeq_finite finite_Plus by blast
    consider  "|A| \<le>o |B|" | "|B| \<le>o |A|"
      using ordLeq_total [OF card_of_Well_order card_of_Well_order] by blast
    then show False
    proof cases
      case 1
      hence "\<not>finite B" using \<section> card_of_ordLeq_finite by blast
      hence "|A <+> B| =o |B|" using False 1
        by (auto simp add: card_of_Plus_infinite)
      thus False using LESS2 not_ordLess_ordLeq that ordLeq_ordIso_trans by blast
    next
      case 2
      hence "\<not>finite A" using \<section> card_of_ordLeq_finite by blast
      hence "|A <+> B| =o |A|" using False 2
        by (auto simp add: card_of_Plus_infinite)
      thus False using LESS1 not_ordLess_ordLeq that ordLeq_ordIso_trans by blast
    qed
  qed
  thus ?thesis 
    using ordLess_or_ordLeq[of "|A <+> B|" "|C|"] 
          card_of_Well_order[of "A <+> B"] card_of_Well_order[of "C"] by auto
qed

lemma card_of_Plus_ordLess_infinite_Field:
  assumes INF: "\<not>finite (Field r)" and r: "Card_order r" and
    LESS1: "|A| <o r" and LESS2: "|B| <o r"
  shows "|A <+> B| <o r"
proof -
  let ?C  = "Field r"
  have 1: "r =o |?C| \<and> |?C| =o r" 
    using r card_of_Field_ordIso ordIso_symmetric by blast
  hence "|A| <o |?C|"  "|B| <o |?C|"
    using LESS1 LESS2 ordLess_ordIso_trans by blast+
  hence  "|A <+> B| <o |?C|" using INF
      card_of_Plus_ordLess_infinite by blast
  thus ?thesis using 1 ordLess_ordIso_trans by blast
qed

lemma card_of_Plus_ordLeq_infinite_Field:
  assumes r: "\<not>finite (Field r)" and A: "|A| \<le>o r" and B: "|B| \<le>o r"
    and c: "Card_order r"
  shows "|A <+> B| \<le>o r"
proof -
  let ?r' = "cardSuc r"
  have "Card_order ?r' \<and> \<not>finite (Field ?r')" using assms
    by (simp add: cardSuc_Card_order cardSuc_finite)
  moreover have "|A| <o ?r'" and "|B| <o ?r'" using A B c
    by (auto simp: card_of_card_order_on Field_card_of cardSuc_ordLeq_ordLess)
  ultimately have "|A <+> B| <o ?r'"
    using card_of_Plus_ordLess_infinite_Field by blast
  thus ?thesis using c r
    by (simp add: card_of_card_order_on Field_card_of cardSuc_ordLeq_ordLess)
qed

lemma card_of_Un_ordLeq_infinite_Field:
  assumes C: "\<not>finite (Field r)" and A: "|A| \<le>o r" and B: "|B| \<le>o r"
    and "Card_order r"
  shows "|A Un B| \<le>o r"
  using assms card_of_Plus_ordLeq_infinite_Field card_of_Un_Plus_ordLeq
    ordLeq_transitive by fast

lemma card_of_Un_ordLess_infinite:
  assumes INF: "\<not>finite C" and
    LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
  shows "|A \<union> B| <o |C|"
  using assms card_of_Plus_ordLess_infinite card_of_Un_Plus_ordLeq
    ordLeq_ordLess_trans by blast

lemma card_of_Un_ordLess_infinite_Field:
  assumes INF: "\<not>finite (Field r)" and r: "Card_order r" and
    LESS1: "|A| <o r" and LESS2: "|B| <o r"
  shows "|A Un B| <o r"
proof -
  let ?C  = "Field r"
  have 1: "r =o |?C| \<and> |?C| =o r" using r card_of_Field_ordIso
      ordIso_symmetric by blast
  hence "|A| <o |?C|"  "|B| <o |?C|"
    using LESS1 LESS2 ordLess_ordIso_trans by blast+
  hence  "|A Un B| <o |?C|" using INF
      card_of_Un_ordLess_infinite by blast
  thus ?thesis using 1 ordLess_ordIso_trans by blast
qed

subsection \<open>Regular cardinals\<close>

definition cofinal where
  "cofinal A r \<equiv> \<forall>a \<in> Field r. \<exists>b \<in> A. a \<noteq> b \<and> (a,b) \<in> r"

definition regularCard where
  "regularCard r \<equiv> \<forall>K. K \<le> Field r \<and> cofinal K r \<longrightarrow> |K| =o r"

definition relChain where
  "relChain r As \<equiv> \<forall>i j. (i,j) \<in> r \<longrightarrow> As i \<le> As j"

lemma regularCard_UNION:
  assumes r: "Card_order r"   "regularCard r"
    and As: "relChain r As"
    and Bsub: "B \<le> (\<Union>i \<in> Field r. As i)"
    and cardB: "|B| <o r"
  shows "\<exists>i \<in> Field r. B \<le> As i"
proof -
  let ?phi = "\<lambda>b j. j \<in> Field r \<and> b \<in> As j"
  have "\<forall>b\<in>B. \<exists>j. ?phi b j" using Bsub by blast
  then obtain f where f: "\<And>b. b \<in> B \<Longrightarrow> ?phi b (f b)"
    using bchoice[of B ?phi] by blast
  let ?K = "f ` B"
  {assume 1: "\<And>i. i \<in> Field r \<Longrightarrow> \<not> B \<le> As i"
    have 2: "cofinal ?K r"
      unfolding cofinal_def 
    proof (intro strip)
      fix i assume i: "i \<in> Field r"
      with 1 obtain b where b: "b \<in> B \<and> b \<notin> As i" by blast
      hence "i \<noteq> f b \<and> \<not> (f b,i) \<in> r"
        using As f unfolding relChain_def by auto
      hence "i \<noteq> f b \<and> (i, f b) \<in> r" using r
        unfolding card_order_on_def well_order_on_def linear_order_on_def
          total_on_def using i f b by auto
      with b show "\<exists>b \<in> f`B. i \<noteq> b \<and> (i,b) \<in> r" by blast
    qed
    moreover have "?K \<le> Field r" using f by blast
    ultimately have "|?K| =o r" using 2 r unfolding regularCard_def by blast
    moreover
    have "|?K| <o r" using cardB ordLeq_ordLess_trans card_of_image by blast
    ultimately have False using not_ordLess_ordIso by blast
  }
  thus ?thesis by blast
qed

lemma infinite_cardSuc_regularCard:
  assumes r_inf: "\<not>finite (Field r)" and r_card: "Card_order r"
  shows "regularCard (cardSuc r)"
proof -
  let ?r' = "cardSuc r"
  have r': "Card_order ?r'" "\<And>p. Card_order p \<longrightarrow> (p \<le>o r) = (p <o ?r')"
    using r_card by (auto simp: cardSuc_Card_order cardSuc_ordLeq_ordLess)
  show ?thesis
    unfolding regularCard_def proof auto
    fix K assume 1: "K \<le> Field ?r'" and 2: "cofinal K ?r'"
    hence "|K| \<le>o |Field ?r'|" by (simp only: card_of_mono1)
    also have 22: "|Field ?r'| =o ?r'"
      using r' by (simp add: card_of_Field_ordIso[of ?r'])
    finally have "|K| \<le>o ?r'" .
    moreover
    { let ?L = "\<Union> j \<in> K. underS ?r' j"
      let ?J = "Field r"
      have rJ: "r =o |?J|"
        using r_card card_of_Field_ordIso ordIso_symmetric by blast
      assume "|K| <o ?r'"
      hence "|K| \<le>o r" using r' card_of_Card_order[of K] by blast
      hence "|K| \<le>o |?J|" using rJ ordLeq_ordIso_trans by blast
      moreover
      {have "\<forall>j\<in>K. |underS ?r' j| <o ?r'"
          using r' 1 by (auto simp: card_of_underS)
        hence "\<forall>j\<in>K. |underS ?r' j| \<le>o r"
          using r' card_of_Card_order by blast
        hence "\<forall>j\<in>K. |underS ?r' j| \<le>o |?J|"
          using rJ ordLeq_ordIso_trans by blast
      }
      ultimately have "|?L| \<le>o |?J|"
        using r_inf card_of_UNION_ordLeq_infinite by blast
      hence "|?L| \<le>o r" using rJ ordIso_symmetric ordLeq_ordIso_trans by blast
      hence "|?L| <o ?r'" using r' card_of_Card_order by blast
      moreover
      {
        have "Field ?r' \<le> ?L"
          using 2 unfolding underS_def cofinal_def by auto
        hence "|Field ?r'| \<le>o |?L|" by (simp add: card_of_mono1)
        hence "?r' \<le>o |?L|"
          using 22 ordIso_ordLeq_trans ordIso_symmetric by blast
      }
      ultimately have "|?L| <o |?L|" using ordLess_ordLeq_trans by blast
      hence False using ordLess_irreflexive by blast
    }
    ultimately show "|K| =o ?r'"
      unfolding ordLeq_iff_ordLess_or_ordIso by blast
  qed
qed

lemma cardSuc_UNION:
  assumes r: "Card_order r" and "\<not>finite (Field r)"
    and As: "relChain (cardSuc r) As"
    and Bsub: "B \<le> (\<Union> i \<in> Field (cardSuc r). As i)"
    and cardB: "|B| \<le>o r"
  shows "\<exists>i \<in> Field (cardSuc r). B \<le> As i"
proof -
  let ?r' = "cardSuc r"
  have "Card_order ?r' \<and> |B| <o ?r'"
    using r cardB cardSuc_ordLeq_ordLess cardSuc_Card_order
      card_of_Card_order by blast
  moreover have "regularCard ?r'"
    using assms by(simp add: infinite_cardSuc_regularCard)
  ultimately show ?thesis
    using As Bsub cardB regularCard_UNION by blast
qed


subsection \<open>Others\<close>

lemma card_of_Func_Times:
  "|Func (A \<times> B) C| =o |Func A (Func B C)|"
  unfolding card_of_ordIso[symmetric]
  using bij_betw_curr by blast

lemma card_of_Pow_Func:
  "|Pow A| =o |Func A (UNIV::bool set)|"
proof -
  define F where [abs_def]: "F A' a \<equiv>
    (if a \<in> A then (if a \<in> A' then True else False) else undefined)" for A' a
  have "bij_betw F (Pow A) (Func A (UNIV::bool set))"
    unfolding bij_betw_def inj_on_def proof (intro ballI impI conjI)
    fix A1 A2 assume "A1 \<in> Pow A" "A2 \<in> Pow A" "F A1 = F A2"
    thus "A1 = A2" unfolding F_def Pow_def fun_eq_iff by (auto split: if_split_asm)
  next
    show "F ` Pow A = Func A UNIV"
    proof safe
      fix f assume f: "f \<in> Func A (UNIV::bool set)"
      show "f \<in> F ` Pow A" 
        unfolding image_iff 
      proof
        show "f = F {a \<in> A. f a = True}"
          using f unfolding Func_def F_def by force
      qed auto
    qed(unfold Func_def F_def, auto)
  qed
  thus ?thesis unfolding card_of_ordIso[symmetric] by blast
qed

lemma card_of_Func_UNIV:
  "|Func (UNIV::'a set) (B::'b set)| =o |{f::'a \<Rightarrow> 'b. range f \<subseteq> B}|"
proof -
  let ?F = "\<lambda> f (a::'a). ((f a)::'b)"
  have "bij_betw ?F {f. range f \<subseteq> B} (Func UNIV B)"
    unfolding bij_betw_def inj_on_def 
  proof safe
    fix h :: "'a \<Rightarrow> 'b" assume h: "h \<in> Func UNIV B"
    then obtain f where f: "\<forall> a. h a = f a" by blast
    hence "range f \<subseteq> B" using h unfolding Func_def by auto
    thus "h \<in> (\<lambda>f a. f a) ` {f. range f \<subseteq> B}" using f by auto
  qed(unfold Func_def fun_eq_iff, auto)
  then show ?thesis
    by (blast intro: ordIso_symmetric card_of_ordIsoI)
qed

lemma Func_Times_Range:
  "|Func A (B \<times> C)| =o |Func A B \<times> Func A C|" (is "|?LHS| =o |?RHS|")
proof -
  let ?F = "\<lambda>fg. (\<lambda>x. if x \<in> A then fst (fg x) else undefined,
                  \<lambda>x. if x \<in> A then snd (fg x) else undefined)"
  let ?G = "\<lambda>(f, g) x. if x \<in> A then (f x, g x) else undefined"
  have "bij_betw ?F ?LHS ?RHS" unfolding bij_betw_def inj_on_def
  proof (intro conjI impI ballI equalityI subsetI)
    fix f g assume *: "f \<in> Func A (B \<times> C)" "g \<in> Func A (B \<times> C)" "?F f = ?F g"
    show "f = g"
    proof
      fix x from * have "fst (f x) = fst (g x) \<and> snd (f x) = snd (g x)"
        by (cases "x \<in> A") (auto simp: Func_def fun_eq_iff split: if_splits)
      then show "f x = g x" by (subst (1 2) surjective_pairing) simp
    qed
  next
    fix fg assume "fg \<in> Func A B \<times> Func A C"
    thus "fg \<in> ?F ` Func A (B \<times> C)"
      by (intro image_eqI[of _ _ "?G fg"]) (auto simp: Func_def)
  qed (auto simp: Func_def fun_eq_iff)
  thus ?thesis using card_of_ordIso by blast
qed

subsection \<open>Regular vs. stable cardinals\<close>

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
    hence "|Field r| \<le>o |Sigma A F|" using card_of_Field_ordIso[OF cr] ordIso_ordLeq_trans by blast
    moreover have Fi: "Field r \<noteq> {}" using ir by auto
    ultimately have "\<exists>f. f ` Sigma A F = Field r" using card_of_ordLeq2[OF Fi] by blast
    then obtain f where f: "f ` Sigma A F = Field r" by blast
    have r: "wo_rel r" using cr unfolding card_order_on_def wo_rel_def by auto
    {fix a assume a: "a \<in> A"
      define L where "L = {(a,u) | u. u \<in> F a}"
      have fL: "f ` L \<subseteq> Field r" using f a unfolding L_def by auto
      have "bij_betw snd {(a, u) |u. u \<in> F a} (F a)"
        unfolding bij_betw_def inj_on_def by (auto simp: image_def)
      then have "|L| =o |F a|" unfolding L_def card_of_ordIso[symmetric] by blast
      hence "|L| <o r" using F a ordIso_ordLess_trans[of "|L|" "|F a|"] unfolding L_def by auto
      hence "|f ` L| <o r" using ordLeq_ordLess_trans[OF card_of_image, of "L"] unfolding L_def by auto
      hence "\<not> cofinal (f ` L) r" using reg fL unfolding regularCard_def
        by (force simp add: dest: not_ordLess_ordIso)
      then obtain k where k: "k \<in> Field r" and "\<forall> l \<in> L. \<not> (f l \<noteq> k \<and> (k, f l) \<in> r)"
        unfolding cofinal_def image_def by auto
      hence "\<exists> k \<in> Field r. \<forall> l \<in> L. (f l, k) \<in> r"
        using wo_rel.in_notinI[OF r _ _ \<open>k \<in> Field r\<close>] fL unfolding image_subset_iff by fast
      hence "\<exists> k \<in> Field r. \<forall> u \<in> F a. (f (a,u), k) \<in> r" unfolding L_def by auto
    }
    then have x: "\<And>a. a\<in>A \<Longrightarrow> \<exists>k. k \<in> Field r \<and> (\<forall>u\<in>F a. (f (a, u), k) \<in> r)" by blast
    obtain gg where "\<And>a. a\<in>A \<Longrightarrow> gg a = (SOME k. k \<in> Field r \<and> (\<forall>u\<in>F a. (f (a, u), k) \<in> r))" by simp
    then have gg: "\<forall>a\<in>A. \<forall>u\<in>F a. (f (a, u), gg a) \<in> r" using someI_ex[OF x] by auto
    obtain j0 where j0: "j0 \<in> Field r" using Fi by auto
    define g where [abs_def]: "g a = (if F a \<noteq> {} then gg a else j0)" for a
    have g: "\<forall> a \<in> A. \<forall> u \<in> F a. (f (a,u),g a) \<in> r" using gg unfolding g_def by auto
    hence 1: "Field r \<subseteq> (\<Union>a \<in> A. under r (g a))"
      using f[symmetric] unfolding under_def image_def by auto
    have gA: "g ` A \<subseteq> Field r" using gg j0 unfolding Field_def g_def by auto
    moreover have "cofinal (g ` A) r" unfolding cofinal_def 
    proof safe
      fix i assume "i \<in> Field r"
      then obtain j where ij: "(i,j) \<in> r" "i \<noteq> j" using cr ir infinite_Card_order_limit by fast
      hence "j \<in> Field r" using card_order_on_def cr well_order_on_domain by fast
      then obtain a where a: "a \<in> A" and j: "(j, g a) \<in> r" 
        using 1 unfolding under_def by auto
      hence "(i, g a) \<in> r" using ij wo_rel.TRANS[OF r] unfolding trans_def by blast
      moreover have "i \<noteq> g a"
        using ij j r unfolding wo_rel_def unfolding well_order_on_def linear_order_on_def
          partial_order_on_def antisym_def by auto
      ultimately show "\<exists>j\<in>g ` A. i \<noteq> j \<and> (i, j) \<in> r" using a by auto
    qed
    ultimately have "|g ` A| =o r" using reg unfolding regularCard_def by auto
    moreover have "|g ` A| \<le>o |A|" using card_of_image by blast
    ultimately have False using A using not_ordLess_ordIso ordLeq_ordLess_trans by blast
  }
  thus "|Sigma A F| <o r"
    using cr not_ordLess_iff_ordLeq using card_of_Well_order card_order_on_well_order_on by blast
qed

lemma stable_regularCard:
  assumes cr: "Card_order r" and ir: "\<not>finite (Field r)" and st: "stable r"
  shows "regularCard r"
  unfolding regularCard_def proof safe
  fix K assume K: "K \<subseteq> Field r" and cof: "cofinal K r"
  have "|K| \<le>o r" using K card_of_Field_ordIso card_of_mono1 cr ordLeq_ordIso_trans by blast
  moreover
  {assume Kr: "|K| <o r"
    have x: "\<And>a. a \<in> Field r \<Longrightarrow> \<exists>b. b \<in> K \<and> a \<noteq> b \<and> (a, b) \<in> r" using cof unfolding cofinal_def by blast
    then obtain f where "\<And>a. a \<in> Field r \<Longrightarrow> f a = (SOME b. b \<in> K \<and> a \<noteq> b \<and> (a, b) \<in> r)" by simp
    then have "\<forall>a\<in>Field r. f a \<in> K \<and> a \<noteq> f a \<and> (a, f a) \<in> r" using someI_ex[OF x] by simp
    hence "Field r \<subseteq> (\<Union>a \<in> K. underS r a)" unfolding underS_def by auto
    hence "r \<le>o |\<Union>a \<in> K. underS r a|"
      using cr Card_order_iff_ordLeq_card_of card_of_mono1 ordLeq_transitive by blast
    also have "|\<Union>a \<in> K. underS r a| \<le>o |SIGMA a: K. underS r a|" by (rule card_of_UNION_Sigma)
    also
    {have "\<forall> a \<in> K. |underS r a| <o r" using K card_of_underS[OF cr] subsetD by auto
      hence "|SIGMA a: K. underS r a| <o r" using st Kr unfolding stable_def by auto
    }
    finally have "r <o r" .
    hence False using ordLess_irreflexive by blast
  }
  ultimately show "|K| =o r" using ordLeq_iff_ordLess_or_ordIso by blast
qed

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

lemma card_of_Sigma_cong1:
  assumes "\<forall>i \<in> I. |A i| =o |B i|"
  shows "|SIGMA i : I. A i| =o |SIGMA i : I. B i|"
  using assms by (auto simp add: card_of_Sigma_mono1 ordIso_iff_ordLeq)

lemma card_of_Sigma_cong2:
  assumes "bij_betw f (I::'i set) (J::'j set)"
  shows "|SIGMA i : I. (A::'j \<Rightarrow> 'a set) (f i)| =o |SIGMA j : J. A j|"
proof -
  let ?LEFT = "SIGMA i : I. A (f i)"
  let ?RIGHT = "SIGMA j : J. A j"
  define u where "u \<equiv> \<lambda>(i::'i,a::'a). (f i,a)"
  have "bij_betw u ?LEFT ?RIGHT"
    using assms unfolding u_def bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed

lemma card_of_Sigma_cong:
  assumes BIJ: "bij_betw f I J" and ISO: "\<forall>j \<in> J. |A j| =o |B j|"
  shows "|SIGMA i : I. A (f i)| =o |SIGMA j : J. B j|"
proof -
  have "\<forall>i \<in> I. |A(f i)| =o |B(f i)|"
    using ISO BIJ unfolding bij_betw_def by blast
  hence "|SIGMA i : I. A (f i)| =o |SIGMA i : I. B (f i)|" by (rule card_of_Sigma_cong1)
  moreover have "|SIGMA i : I. B (f i)| =o |SIGMA j : J. B j|"
    using BIJ card_of_Sigma_cong2 by blast
  ultimately show ?thesis using ordIso_transitive by blast
qed

(* Note that below the types of A and F are now unconstrained: *)
lemma stable_elim:
  assumes ST: "stable r" and A_LESS: "|A| <o r" and
    F_LESS: "\<And> a. a \<in> A \<Longrightarrow> |F a| <o r"
  shows "|SIGMA a : A. F a| <o r"
proof -
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

lemma stable_UNION:
  assumes "stable r" and "|A| <o r" and "\<And> a. a \<in> A \<Longrightarrow> |F a| <o r"
  shows "|\<Union>a \<in> A. F a| <o r"
  using assms card_of_UNION_Sigma stable_elim ordLeq_ordLess_trans by blast

corollary card_of_UNION_ordLess_infinite:
  assumes "stable |B|" and "|I| <o |B|" and "\<forall>i \<in> I. |A i| <o |B|"
  shows "|\<Union>i \<in> I. A i| <o |B|"
  using assms stable_UNION by blast

corollary card_of_UNION_ordLess_infinite_Field:
  assumes ST: "stable r" and r: "Card_order r" and
    LEQ_I: "|I| <o r" and LEQ: "\<forall>i \<in> I. |A i| <o r"
  shows "|\<Union>i \<in> I. A i| <o r"
proof -
  let ?B  = "Field r"
  have 1: "r =o |?B| \<and> |?B| =o r" using r card_of_Field_ordIso
      ordIso_symmetric by blast
  hence "|I| <o |?B|"  "\<forall>i \<in> I. |A i| <o |?B|"
    using LEQ_I LEQ ordLess_ordIso_trans by blast+
  moreover have "stable |?B|" using stable_ordIso1 ST 1 by blast
  ultimately have  "|\<Union>i \<in> I. A i| <o |?B|" using LEQ
      card_of_UNION_ordLess_infinite by blast
  thus ?thesis using 1 ordLess_ordIso_trans by blast
qed

end
