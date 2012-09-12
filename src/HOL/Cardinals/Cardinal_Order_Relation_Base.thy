(*  Title:      HOL/Cardinals/Cardinal_Order_Relation_Base.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Cardinal-order relations (base).
*)

header {* Cardinal-Order Relations (Base)  *}

theory Cardinal_Order_Relation_Base
imports Constructions_on_Wellorders_Base
begin


text{* In this section, we define cardinal-order relations to be minim well-orders
on their field.  Then we define the cardinal of a set to be {\em some} cardinal-order
relation on that set, which will be unique up to order isomorphism.  Then we study
the connection between cardinals and:
\begin{itemize}
\item standard set-theoretic constructions: products,
sums, unions, lists, powersets, set-of finite sets operator;
\item finiteness and infiniteness (in particular, with the numeric cardinal operator
for finite sets, @{text "card"}, from the theory @{text "Finite_Sets.thy"}).
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
*}


subsection {* Cardinal orders *}


text{* A cardinal order in our setting shall be a well-order {\em minim} w.r.t. the
order-embedding relation, @{text "\<le>o"} (which is the same as being {\em minimal} w.r.t. the
strict order-embedding relation, @{text "<o"}), among all the well-orders on its field.  *}

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
unfolding card_order_on_def using rel.well_order_on_Field by blast


text{* The existence of a cardinal relation on any given set (which will mean
that any set has a cardinal) follows from two facts:
\begin{itemize}
\item Zermelo's theorem (proved in @{text "Zorn.thy"} as theorem @{text "well_order_on"}),
which states that on any given set there exists a well-order;
\item The well-founded-ness of @{text "<o"}, ensuring that then there exists a minimal
such well-order, i.e., a cardinal order.
\end{itemize}
*}


theorem card_order_on: "\<exists>r. card_order_on A r"
proof-
  obtain R where R_def: "R = {r. well_order_on A r}" by blast
  have 1: "R \<noteq> {} \<and> (\<forall>r \<in> R. Well_order r)"
  using well_order_on[of A] R_def rel.well_order_on_Well_order by blast
  hence "\<exists>r \<in> R. \<forall>r' \<in> R. r \<le>o r'"
  using  exists_minim_Well_order[of R] by auto
  thus ?thesis using R_def unfolding card_order_on_def by auto
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
  using rel.well_order_on_Well_order by blast
  obtain f where 1: "iso r' r f" and 2: "Well_order r \<and> Well_order r'"
  using ISO unfolding ordIso_def by auto
  hence 3: "inj_on f (Field r') \<and> f ` (Field r') = Field r"
  by (auto simp add: iso_iff embed_inj_on)
  let ?p = "dir_image p' f"
  have 4: "p' =o ?p \<and> Well_order ?p"
  using 0 2 3 by (auto simp add: dir_image_ordIso Well_order_dir_image)
  moreover have "Field ?p =  Field r"
  using 0 3 by (auto simp add: dir_image_Field2 order_on_defs)
  ultimately have "well_order_on (Field r) ?p" by auto
  hence "r \<le>o ?p" using CO unfolding card_order_on_def by auto
  thus "r' \<le>o p'"
  using ISO 4 ordLeq_ordIso_trans ordIso_ordLeq_trans ordIso_symmetric by blast
qed


lemma Card_order_ordIso2:
assumes CO: "Card_order r" and ISO: "r =o r'"
shows "Card_order r'"
using assms Card_order_ordIso ordIso_symmetric by blast


subsection {* Cardinal of a set *}


text{* We define the cardinal of set to be {\em some} cardinal order on that set.
We shall prove that this notion is unique up to order isomorphism, meaning
that order isomorphism shall be the true identity of cardinals.  *}


definition card_of :: "'a set \<Rightarrow> 'a rel" ("|_|" )
where "card_of A = (SOME r. card_order_on A r)"


lemma card_of_card_order_on: "card_order_on A |A|"
unfolding card_of_def by (auto simp add: card_order_on someI_ex)


lemma card_of_well_order_on: "well_order_on A |A|"
using card_of_card_order_on card_order_on_def by blast


lemma Field_card_of: "Field |A| = A"
using card_of_card_order_on[of A] unfolding card_order_on_def
using rel.well_order_on_Field by blast


lemma card_of_Card_order: "Card_order |A|"
by (simp only: card_of_card_order_on Field_card_of)


corollary ordIso_card_of_imp_Card_order:
"r =o |A| \<Longrightarrow> Card_order r"
using card_of_Card_order Card_order_ordIso by blast


lemma card_of_Well_order: "Well_order |A|"
using card_of_Card_order unfolding  card_order_on_def by auto


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
   hence "|A| \<le>o |B|" using card_of_least
   ordLeq_ordIso_trans ordIso_symmetric by blast
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
   using * ** 1 Cantor_Bernstein[of f] by fastforce
   hence "|A| =o |B|" using card_of_ordIso by blast
   hence "|A| \<le>o |B|" using ordIso_iff_ordLeq by auto
  }
  thus "|A| \<le>o |B|" using ordLess_or_ordLeq[of "|B|" "|A|"]
  by (auto simp: card_of_Well_order)
next
  assume *: "|A| \<le>o |B|"
  obtain f where "embed ( |A| ) ( |B| ) f"
  using * unfolding ordLeq_def by auto
  hence "inj_on f A \<and> f ` A \<le> B" using embed_inj_on[of "|A|" "|B|" f]
  card_of_Well_order[of "A"] Field_card_of[of "A"] Field_card_of[of "B"]
  embed_Field[of "|A|" "|B|" f] by auto
  thus "\<exists>f. inj_on f A \<and> f ` A \<le> B" by auto
qed


lemma card_of_ordLeq2:
"A \<noteq> {} \<Longrightarrow> (\<exists>g. g ` B = A) = ( |A| \<le>o |B| )"
using card_of_ordLeq[of A B] inj_on_iff_surj[of A B] by auto


lemma card_of_ordLess:
"(\<not>(\<exists>f. inj_on f A \<and> f ` A \<le> B)) = ( |B| <o |A| )"
proof-
  have "(\<not>(\<exists>f. inj_on f A \<and> f ` A \<le> B)) = (\<not> |A| \<le>o |B| )"
  using card_of_ordLeq by blast
  also have "\<dots> = ( |B| <o |A| )"
  using card_of_Well_order[of A] card_of_Well_order[of B]
        not_ordLeq_iff_ordLess by blast
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
proof-
  obtain f where
  1: "well_order_on (Field r) r \<and> well_order_on (Field r) r \<and> embed r r' f"
  using assms unfolding ordLeq_def
  by (auto simp add: rel.well_order_on_Well_order)
  hence "inj_on f (Field r) \<and> f ` (Field r) \<le> Field r'"
  by (auto simp add: embed_inj_on embed_Field)
  thus "|Field r| \<le>o |Field r'|" using card_of_ordLeq by blast
qed


lemma card_of_cong: "r =o r' \<Longrightarrow> |Field r| =o |Field r'|"
by (simp add: ordIso_iff_ordLeq card_of_mono2)


lemma card_of_Field_ordLess: "Well_order r \<Longrightarrow> |Field r| \<le>o r"
using card_of_least card_of_well_order_on rel.well_order_on_Well_order by blast


lemma card_of_Field_ordIso:
assumes "Card_order r"
shows "|Field r| =o r"
proof-
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
proof-
  have "Card_order r = (r =o |Field r| )"
  unfolding Card_order_iff_ordIso_card_of by simp
  also have "... = (r \<le>o |Field r| \<and> |Field r| \<le>o r)"
  unfolding ordIso_iff_ordLeq by simp
  also have "... = (r \<le>o |Field r| )"
  using card_of_Field_ordLess
  by (auto simp: card_of_Field_ordLess ordLeq_Well_order_simp)
  finally show ?thesis .
qed


lemma Card_order_iff_Restr_underS:
assumes "Well_order r"
shows "Card_order r = (\<forall>a \<in> Field r. Restr r (rel.underS r a) <o |Field r| )"
using assms unfolding Card_order_iff_ordLeq_card_of
using ordLeq_iff_ordLess_Restr card_of_Well_order by blast


lemma card_of_underS:
assumes r: "Card_order r" and a: "a : Field r"
shows "|rel.underS r a| <o r"
proof-
  let ?A = "rel.underS r a"  let ?r' = "Restr r ?A"
  have 1: "Well_order r"
  using r unfolding card_order_on_def by simp
  have "Well_order ?r'" using 1 Well_order_Restr by auto
  moreover have "card_order_on (Field ?r') |Field ?r'|"
  using card_of_card_order_on .
  ultimately have "|Field ?r'| \<le>o ?r'"
  unfolding card_order_on_def by simp
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
proof-
  have "well_order_on (Field r) r" using assms unfolding ordLess_def
  by (auto simp add: rel.well_order_on_Well_order)
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



subsection {* Cardinals versus set operations on arbitrary sets *}


text{* Here we embark in a long journey of simple results showing
that the standard set-theoretic operations are well-behaved w.r.t. the notion of
cardinal -- essentially, this means that they preserve the ``cardinal identity"
@{text "=o"} and are monotonic w.r.t. @{text "\<le>o"}.
*}


lemma card_of_empty: "|{}| \<le>o |A|"
using card_of_ordLeq inj_on_id by blast


lemma card_of_empty1:
assumes "Well_order r \<or> Card_order r"
shows "|{}| \<le>o r"
proof-
  have "Well_order r" using assms unfolding card_order_on_def by auto
  hence "|Field r| <=o r"
  using assms card_of_Field_ordLess by blast
  moreover have "|{}| \<le>o |Field r|" by (simp add: card_of_empty)
  ultimately show ?thesis using ordLeq_transitive by blast
qed


corollary Card_order_empty:
"Card_order r \<Longrightarrow> |{}| \<le>o r" by (simp add: card_of_empty1)


lemma card_of_empty2:
assumes LEQ: "|A| =o |{}|"
shows "A = {}"
using assms card_of_ordIso[of A] bij_betw_empty2 by blast


lemma card_of_empty3:
assumes LEQ: "|A| \<le>o |{}|"
shows "A = {}"
using assms
by (simp add: ordIso_iff_ordLeq card_of_empty1 card_of_empty2
              ordLeq_Well_order_simp)


lemma card_of_empty_ordIso:
"|{}::'a set| =o |{}::'b set|"
using card_of_ordIso unfolding bij_betw_def inj_on_def by blast


lemma card_of_image:
"|f ` A| <=o |A|"
proof(cases "A = {}", simp add: card_of_empty)
  assume "A ~= {}"
  hence "f ` A ~= {}" by auto
  thus "|f ` A| \<le>o |A|"
  using card_of_ordLeq2[of "f ` A" A] by auto
qed


lemma surj_imp_ordLeq:
assumes "B <= f ` A"
shows "|B| <=o |A|"
proof-
  have "|B| <=o |f ` A|" using assms card_of_mono1 by auto
  thus ?thesis using card_of_image ordLeq_transitive by blast
qed


lemma card_of_ordLeqI2:
assumes "B \<subseteq> f ` A"
shows "|B| \<le>o |A|"
using assms by (metis surj_imp_ordLeq)


lemma card_of_singl_ordLeq:
assumes "A \<noteq> {}"
shows "|{b}| \<le>o |A|"
proof-
  obtain a where *: "a \<in> A" using assms by auto
  let ?h = "\<lambda> b'::'b. if b' = b then a else undefined"
  have "inj_on ?h {b} \<and> ?h ` {b} \<le> A"
  using * unfolding inj_on_def by auto
  thus ?thesis using card_of_ordLeq by blast
qed


corollary Card_order_singl_ordLeq:
"\<lbrakk>Card_order r; Field r \<noteq> {}\<rbrakk> \<Longrightarrow> |{b}| \<le>o r"
using card_of_singl_ordLeq[of "Field r" b]
      card_of_Field_ordIso[of r] ordLeq_ordIso_trans by blast


lemma card_of_Pow: "|A| <o |Pow A|"
using card_of_ordLess2[of "Pow A" A]  Cantors_paradox[of A]
      Pow_not_empty[of A] by auto


lemma infinite_Pow:
assumes "infinite A"
shows "infinite (Pow A)"
proof-
  have "|A| \<le>o |Pow A|" by (metis card_of_Pow ordLess_imp_ordLeq)
  thus ?thesis by (metis assms finite_Pow_iff)
qed


corollary Card_order_Pow:
"Card_order r \<Longrightarrow> r <o |Pow(Field r)|"
using card_of_Pow card_of_Field_ordIso ordIso_ordLess_trans ordIso_symmetric by blast


corollary card_of_set_type: "|UNIV::'a set| <o |UNIV::'a set set|"
using card_of_Pow[of "UNIV::'a set"] by simp


lemma card_of_Plus1: "|A| \<le>o |A <+> B|"
proof-
  have "Inl ` A \<le> A <+> B" by auto
  thus ?thesis using inj_Inl[of A] card_of_ordLeq by blast
qed


corollary Card_order_Plus1:
"Card_order r \<Longrightarrow> r \<le>o |(Field r) <+> B|"
using card_of_Plus1 card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Plus2: "|B| \<le>o |A <+> B|"
proof-
  have "Inr ` B \<le> A <+> B" by auto
  thus ?thesis using inj_Inr[of B] card_of_ordLeq by blast
qed


corollary Card_order_Plus2:
"Card_order r \<Longrightarrow> r \<le>o |A <+> (Field r)|"
using card_of_Plus2 card_of_Field_ordIso ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Plus_empty1: "|A| =o |A <+> {}|"
proof-
  have "bij_betw Inl A (A <+> {})" unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by auto
qed


lemma card_of_Plus_empty2: "|A| =o |{} <+> A|"
proof-
  have "bij_betw Inr A ({} <+> A)" unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by auto
qed


lemma card_of_Plus_commute: "|A <+> B| =o |B <+> A|"
proof-
  let ?f = "\<lambda>(c::'a + 'b). case c of Inl a \<Rightarrow> Inr a
                                   | Inr b \<Rightarrow> Inl b"
  have "bij_betw ?f (A <+> B) (B <+> A)"
  unfolding bij_betw_def inj_on_def by force
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Plus_assoc:
fixes A :: "'a set" and B :: "'b set" and C :: "'c set"
shows "|(A <+> B) <+> C| =o |A <+> B <+> C|"
proof -
  def f \<equiv> "\<lambda>(k::('a + 'b) + 'c).
  case k of Inl ab \<Rightarrow> (case ab of Inl a \<Rightarrow> Inl a
                                 |Inr b \<Rightarrow> Inr (Inl b))
           |Inr c \<Rightarrow> Inr (Inr c)"
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
      case (Inr bc) note 1 = Inr show ?thesis
      proof(cases bc)
        case (Inl b)
        hence "b \<in> B" "x = f (Inl (Inr b))"
        using x 1 unfolding f_def by auto
        thus ?thesis by auto
      next
        case (Inr c)
        hence "c \<in> C" "x = f (Inr c)"
        using x 1 unfolding f_def by auto
        thus ?thesis by auto
      qed
    qed
  qed
  hence "bij_betw f ((A <+> B) <+> C) (A <+> B <+> C)"
  unfolding bij_betw_def inj_on_def f_def by auto
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Plus_mono1:
assumes "|A| \<le>o |B|"
shows "|A <+> C| \<le>o |B <+> C|"
proof-
  obtain f where 1: "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A] by fastforce
  obtain g where g_def:
  "g = (\<lambda>d. case d of Inl a \<Rightarrow> Inl(f a) | Inr (c::'c) \<Rightarrow> Inr c)" by blast
  have "inj_on g (A <+> C) \<and> g ` (A <+> C) \<le> (B <+> C)"
  proof-
    {fix d1 and d2 assume "d1 \<in> A <+> C \<and> d2 \<in> A <+> C" and
                          "g d1 = g d2"
     hence "d1 = d2" using 1 unfolding inj_on_def
     by(case_tac d1, case_tac d2, auto simp add: g_def)
    }
    moreover
    {fix d assume "d \<in> A <+> C"
     hence "g d \<in> B <+> C"  using 1
     by(case_tac d, auto simp add: g_def)
    }
    ultimately show ?thesis unfolding inj_on_def by auto
  qed
  thus ?thesis using card_of_ordLeq by metis
qed


corollary ordLeq_Plus_mono1:
assumes "r \<le>o r'"
shows "|(Field r) <+> C| \<le>o |(Field r') <+> C|"
using assms card_of_mono2 card_of_Plus_mono1 by blast


lemma card_of_Plus_mono2:
assumes "|A| \<le>o |B|"
shows "|C <+> A| \<le>o |C <+> B|"
using assms card_of_Plus_mono1[of A B C]
      card_of_Plus_commute[of C A]  card_of_Plus_commute[of B C]
      ordIso_ordLeq_trans[of "|C <+> A|"] ordLeq_ordIso_trans[of "|C <+> A|"]
by blast


corollary ordLeq_Plus_mono2:
assumes "r \<le>o r'"
shows "|A <+> (Field r)| \<le>o |A <+> (Field r')|"
using assms card_of_mono2 card_of_Plus_mono2 by blast


lemma card_of_Plus_mono:
assumes "|A| \<le>o |B|" and "|C| \<le>o |D|"
shows "|A <+> C| \<le>o |B <+> D|"
using assms card_of_Plus_mono1[of A B C] card_of_Plus_mono2[of C D B]
      ordLeq_transitive[of "|A <+> C|"] by blast


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


lemma card_of_Un1:
shows "|A| \<le>o |A \<union> B| "
using inj_on_id[of A] card_of_ordLeq[of A _] by fastforce


lemma card_of_diff:
shows "|A - B| \<le>o |A|"
using inj_on_id[of "A - B"] card_of_ordLeq[of "A - B" _] by fastforce


lemma card_of_Un_Plus_ordLeq:
"|A \<union> B| \<le>o |A <+> B|"
proof-
   let ?f = "\<lambda> c. if c \<in> A then Inl c else Inr c"
   have "inj_on ?f (A \<union> B) \<and> ?f ` (A \<union> B) \<le> A <+> B"
   unfolding inj_on_def by auto
   thus ?thesis using card_of_ordLeq by blast
qed


lemma card_of_Times1:
assumes "A \<noteq> {}"
shows "|B| \<le>o |B \<times> A|"
proof(cases "B = {}", simp add: card_of_empty)
  assume *: "B \<noteq> {}"
  have "fst `(B \<times> A) = B" unfolding image_def using assms by auto
  thus ?thesis using inj_on_iff_surj[of B "B \<times> A"]
                     card_of_ordLeq[of B "B \<times> A"] * by blast
qed


corollary Card_order_Times1:
"\<lbrakk>Card_order r; B \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o |(Field r) \<times> B|"
using card_of_Times1[of B] card_of_Field_ordIso
      ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Times_commute: "|A \<times> B| =o |B \<times> A|"
proof-
  let ?f = "\<lambda>(a::'a,b::'b). (b,a)"
  have "bij_betw ?f (A \<times> B) (B \<times> A)"
  unfolding bij_betw_def inj_on_def by auto
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Times2:
assumes "A \<noteq> {}"   shows "|B| \<le>o |A \<times> B|"
using assms card_of_Times1[of A B] card_of_Times_commute[of B A]
      ordLeq_ordIso_trans by blast


corollary Card_order_Times2:
"\<lbrakk>Card_order r; A \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o |A \<times> (Field r)|"
using card_of_Times2[of A] card_of_Field_ordIso
      ordIso_ordLeq_trans ordIso_symmetric by blast


lemma card_of_Times3: "|A| \<le>o |A \<times> A|"
using card_of_Times1[of A]
by(cases "A = {}", simp add: card_of_empty, blast)


lemma card_of_Plus_Times_bool: "|A <+> A| =o |A \<times> (UNIV::bool set)|"
proof-
  let ?f = "\<lambda>c::'a + 'a. case c of Inl a \<Rightarrow> (a,True)
                                  |Inr a \<Rightarrow> (a,False)"
  have "bij_betw ?f (A <+> A) (A \<times> (UNIV::bool set))"
  proof-
    {fix  c1 and c2 assume "?f c1 = ?f c2"
     hence "c1 = c2"
     by(case_tac "c1", case_tac "c2", auto, case_tac "c2", auto)
    }
    moreover
    {fix c assume "c \<in> A <+> A"
     hence "?f c \<in> A \<times> (UNIV::bool set)"
     by(case_tac c, auto)
    }
    moreover
    {fix a bl assume *: "(a,bl) \<in> A \<times> (UNIV::bool set)"
     have "(a,bl) \<in> ?f ` ( A <+> A)"
     proof(cases bl)
       assume bl hence "?f(Inl a) = (a,bl)" by auto
       thus ?thesis using * by force
     next
       assume "\<not> bl" hence "?f(Inr a) = (a,bl)" by auto
       thus ?thesis using * by force
     qed
    }
    ultimately show ?thesis unfolding bij_betw_def inj_on_def by auto
  qed
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Times_mono1:
assumes "|A| \<le>o |B|"
shows "|A \<times> C| \<le>o |B \<times> C|"
proof-
  obtain f where 1: "inj_on f A \<and> f ` A \<le> B"
  using assms card_of_ordLeq[of A] by fastforce
  obtain g where g_def:
  "g = (\<lambda>(a,c::'c). (f a,c))" by blast
  have "inj_on g (A \<times> C) \<and> g ` (A \<times> C) \<le> (B \<times> C)"
  using 1 unfolding inj_on_def using g_def by auto
  thus ?thesis using card_of_ordLeq by metis
qed


corollary ordLeq_Times_mono1:
assumes "r \<le>o r'"
shows "|(Field r) \<times> C| \<le>o |(Field r') \<times> C|"
using assms card_of_mono2 card_of_Times_mono1 by blast


lemma card_of_Times_mono2:
assumes "|A| \<le>o |B|"
shows "|C \<times> A| \<le>o |C \<times> B|"
using assms card_of_Times_mono1[of A B C]
      card_of_Times_commute[of C A]  card_of_Times_commute[of B C]
      ordIso_ordLeq_trans[of "|C \<times> A|"] ordLeq_ordIso_trans[of "|C \<times> A|"]
by blast


corollary ordLeq_Times_mono2:
assumes "r \<le>o r'"
shows "|A \<times> (Field r)| \<le>o |A \<times> (Field r')|"
using assms card_of_mono2 card_of_Times_mono2 by blast


lemma card_of_Times_cong1:
assumes "|A| =o |B|"
shows "|A \<times> C| =o |B \<times> C|"
using assms by (simp add: ordIso_iff_ordLeq card_of_Times_mono1)


lemma card_of_Times_cong2:
assumes "|A| =o |B|"
shows "|C \<times> A| =o |C \<times> B|"
using assms by (simp add: ordIso_iff_ordLeq card_of_Times_mono2)


corollary ordIso_Times_cong2:
assumes "r =o r'"
shows "|A \<times> (Field r)| =o |A \<times> (Field r')|"
using assms card_of_cong card_of_Times_cong2 by blast


lemma card_of_Sigma_mono1:
assumes "\<forall>i \<in> I. |A i| \<le>o |B i|"
shows "|SIGMA i : I. A i| \<le>o |SIGMA i : I. B i|"
proof-
  have "\<forall>i. i \<in> I \<longrightarrow> (\<exists>f. inj_on f (A i) \<and> f ` (A i) \<le> B i)"
  using assms by (auto simp add: card_of_ordLeq)
  with choice[of "\<lambda> i f. i \<in> I \<longrightarrow> inj_on f (A i) \<and> f ` (A i) \<le> B i"]
  obtain F where 1: "\<forall>i \<in> I. inj_on (F i) (A i) \<and> (F i) ` (A i) \<le> B i" by fastforce
  obtain g where g_def: "g = (\<lambda>(i,a::'b). (i,F i a))" by blast
  have "inj_on g (Sigma I A) \<and> g ` (Sigma I A) \<le> (Sigma I B)"
  using 1 unfolding inj_on_def using g_def by force
  thus ?thesis using card_of_ordLeq by metis
qed


corollary card_of_Sigma_Times:
"\<forall>i \<in> I. |A i| \<le>o |B| \<Longrightarrow> |SIGMA i : I. A i| \<le>o |I \<times> B|"
using card_of_Sigma_mono1[of I A "\<lambda>i. B"] .


lemma card_of_UNION_Sigma:
"|\<Union>i \<in> I. A i| \<le>o |SIGMA i : I. A i|"
using Ex_inj_on_UNION_Sigma[of I A] card_of_ordLeq by metis


lemma card_of_bool:
assumes "a1 \<noteq> a2"
shows "|UNIV::bool set| =o |{a1,a2}|"
proof-
  let ?f = "\<lambda> bl. case bl of True \<Rightarrow> a1 | False \<Rightarrow> a2"
  have "bij_betw ?f UNIV {a1,a2}"
  proof-
    {fix bl1 and bl2 assume "?f  bl1 = ?f bl2"
     hence "bl1 = bl2" using assms by (case_tac bl1, case_tac bl2, auto)
    }
    moreover
    {fix bl have "?f bl \<in> {a1,a2}" by (case_tac bl, auto)
    }
    moreover
    {fix a assume *: "a \<in> {a1,a2}"
     have "a \<in> ?f ` UNIV"
     proof(cases "a = a1")
       assume "a = a1"
       hence "?f True = a" by auto  thus ?thesis by blast
     next
       assume "a \<noteq> a1" hence "a = a2" using * by auto
       hence "?f False = a" by auto  thus ?thesis by blast
     qed
    }
    ultimately show ?thesis unfolding bij_betw_def inj_on_def
    by (metis image_subsetI order_eq_iff subsetI)
  qed
  thus ?thesis using card_of_ordIso by blast
qed


lemma card_of_Plus_Times_aux:
assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and
        LEQ: "|A| \<le>o |B|"
shows "|A <+> B| \<le>o |A \<times> B|"
proof-
  have 1: "|UNIV::bool set| \<le>o |A|"
  using A2 card_of_mono1[of "{a1,a2}"] card_of_bool[of a1 a2]
        ordIso_ordLeq_trans[of "|UNIV::bool set|"] by metis
  (*  *)
  have "|A <+> B| \<le>o |B <+> B|"
  using LEQ card_of_Plus_mono1 by blast
  moreover have "|B <+> B| =o |B \<times> (UNIV::bool set)|"
  using card_of_Plus_Times_bool by blast
  moreover have "|B \<times> (UNIV::bool set)| \<le>o |B \<times> A|"
  using 1 by (simp add: card_of_Times_mono2)
  moreover have " |B \<times> A| =o |A \<times> B|"
  using card_of_Times_commute by blast
  ultimately show "|A <+> B| \<le>o |A \<times> B|"
  using ordLeq_ordIso_trans[of "|A <+> B|" "|B <+> B|" "|B \<times> (UNIV::bool set)|"]
        ordLeq_transitive[of "|A <+> B|" "|B \<times> (UNIV::bool set)|" "|B \<times> A|"]
        ordLeq_ordIso_trans[of "|A <+> B|" "|B \<times> A|" "|A \<times> B|"]
  by blast
qed


lemma card_of_Plus_Times:
assumes A2: "a1 \<noteq> a2 \<and> {a1,a2} \<le> A" and
        B2: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B"
shows "|A <+> B| \<le>o |A \<times> B|"
proof-
  {assume "|A| \<le>o |B|"
   hence ?thesis using assms by (auto simp add: card_of_Plus_Times_aux)
  }
  moreover
  {assume "|B| \<le>o |A|"
   hence "|B <+> A| \<le>o |B \<times> A|"
   using assms by (auto simp add: card_of_Plus_Times_aux)
   hence ?thesis
   using card_of_Plus_commute card_of_Times_commute
         ordIso_ordLeq_trans ordLeq_ordIso_trans by metis
  }
  ultimately show ?thesis
  using card_of_Well_order[of A] card_of_Well_order[of B]
        ordLeq_total[of "|A|"] by metis
qed


lemma card_of_ordLeq_finite:
assumes "|A| \<le>o |B|" and "finite B"
shows "finite A"
using assms unfolding ordLeq_def
using embed_inj_on[of "|A|" "|B|"]  embed_Field[of "|A|" "|B|"]
      Field_card_of[of "A"] Field_card_of[of "B"] inj_on_finite[of _ "A" "B"] by fastforce


lemma card_of_ordLeq_infinite:
assumes "|A| \<le>o |B|" and "infinite A"
shows "infinite B"
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


subsection {* Cardinals versus set operations involving infinite sets *}


text{* Here we show that, for infinite sets, most set-theoretic constructions
do not increase the cardinality.  The cornerstone for this is
theorem @{text "Card_order_Times_same_infinite"}, which states that self-product
does not increase cardinality -- the proof of this fact adapts a standard
set-theoretic argument, as presented, e.g., in the proof of theorem 1.5.11
at page 47 in \cite{card-book}. Then everything else follows fairly easily.  *}


lemma infinite_iff_card_of_nat:
"infinite A = ( |UNIV::nat set| \<le>o |A| )"
by (auto simp add: infinite_iff_countable_subset card_of_ordLeq)


lemma finite_iff_cardOf_nat:
"finite A = ( |A| <o |UNIV :: nat set| )"
using infinite_iff_card_of_nat[of A]
not_ordLeq_iff_ordLess[of "|A|" "|UNIV :: nat set|"]
by (fastforce simp: card_of_Well_order)

lemma finite_ordLess_infinite2:
assumes "finite A" and "infinite B"
shows "|A| <o |B|"
using assms
finite_ordLess_infinite[of "|A|" "|B|"]
card_of_Well_order[of A] card_of_Well_order[of B]
Field_card_of[of A] Field_card_of[of B] by auto


text{* The next two results correspond to the ZF fact that all infinite cardinals are
limit ordinals: *}

lemma Card_order_infinite_not_under:
assumes CARD: "Card_order r" and INF: "infinite (Field r)"
shows "\<not> (\<exists>a. Field r = rel.under r a)"
proof(auto)
  have 0: "Well_order r \<and> wo_rel r \<and> Refl r"
  using CARD unfolding wo_rel_def card_order_on_def order_on_defs by auto
  fix a assume *: "Field r = rel.under r a"
  show False
  proof(cases "a \<in> Field r")
    assume Case1: "a \<notin> Field r"
    hence "rel.under r a = {}" unfolding Field_def rel.under_def by auto
    thus False using INF *  by auto
  next
    let ?r' = "Restr r (rel.underS r a)"
    assume Case2: "a \<in> Field r"
    hence 1: "rel.under r a = rel.underS r a \<union> {a} \<and> a \<notin> rel.underS r a"
    using 0 rel.Refl_under_underS rel.underS_notIn by fastforce
    have 2: "wo_rel.ofilter r (rel.underS r a) \<and> rel.underS r a < Field r"
    using 0 wo_rel.underS_ofilter * 1 Case2 by auto
    hence "?r' <o r" using 0 using ofilter_ordLess by blast
    moreover
    have "Field ?r' = rel.underS r a \<and> Well_order ?r'"
    using  2 0 Field_Restr_ofilter[of r] Well_order_Restr[of r] by blast
    ultimately have "|rel.underS r a| <o r" using ordLess_Field[of ?r'] by auto
    moreover have "|rel.under r a| =o r" using * CARD card_of_Field_ordIso[of r] by auto
    ultimately have "|rel.underS r a| <o |rel.under r a|"
    using ordIso_symmetric ordLess_ordIso_trans by blast
    moreover
    {have "\<exists>f. bij_betw f (rel.under r a) (rel.underS r a)"
     using infinite_imp_bij_betw[of "Field r" a] INF * 1 by auto
     hence "|rel.under r a| =o |rel.underS r a|" using card_of_ordIso by blast
    }
    ultimately show False using not_ordLess_ordIso ordIso_symmetric by blast
  qed
qed


lemma infinite_Card_order_limit:
assumes r: "Card_order r" and "infinite (Field r)"
and a: "a : Field r"
shows "EX b : Field r. a \<noteq> b \<and> (a,b) : r"
proof-
  have "Field r \<noteq> rel.under r a"
  using assms Card_order_infinite_not_under by blast
  moreover have "rel.under r a \<le> Field r"
  using rel.under_Field .
  ultimately have "rel.under r a < Field r" by blast
  then obtain b where 1: "b : Field r \<and> ~ (b,a) : r"
  unfolding rel.under_def by blast
  moreover have ba: "b \<noteq> a"
  using 1 r unfolding card_order_on_def well_order_on_def
  linear_order_on_def partial_order_on_def preorder_on_def refl_on_def by auto
  ultimately have "(a,b) : r"
  using a r unfolding card_order_on_def well_order_on_def linear_order_on_def
  total_on_def by blast
  thus ?thesis using 1 ba by auto
qed


theorem Card_order_Times_same_infinite:
assumes CO: "Card_order r" and INF: "infinite(Field r)"
shows "|Field r \<times> Field r| \<le>o r"
proof-
  obtain phi where phi_def:
  "phi = (\<lambda>r::'a rel. Card_order r \<and> infinite(Field r) \<and>
                      \<not> |Field r \<times> Field r| \<le>o r )" by blast
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
    have "\<not> (\<exists>a. Field r = rel.under r a)"
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
    have "infinite (Field r)" using 1 unfolding phi_def by simp
    hence "infinite ?B" using 8 3 card_of_ordIso_finite_Field[of r ?B] by blast
    hence "infinite A1" using 9 infinite_super finite_cartesian_product by blast
    moreover have temp4: "Field |A1| = A1 \<and> Well_order |A1| \<and> Card_order |A1|"
    using card_of_Card_order[of A1] card_of_Well_order[of A1]
    by (simp add: Field_card_of)
    moreover have "\<not> r \<le>o | A1 |"
    using temp4 11 3 using not_ordLeq_iff_ordLess by blast
    ultimately have "infinite(Field |A1| ) \<and> Card_order |A1| \<and> \<not> r \<le>o | A1 |"
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
assumes "infinite A"
shows "|A \<times> A| =o |A|"
proof-
  let ?r = "|A|"
  have "Field ?r = A \<and> Card_order ?r"
  using Field_card_of card_of_Card_order[of A] by fastforce
  hence "|A \<times> A| \<le>o |A|"
  using Card_order_Times_same_infinite[of ?r] assms by auto
  thus ?thesis using card_of_Times3 ordIso_iff_ordLeq by blast
qed


lemma card_of_Times_infinite:
assumes INF: "infinite A" and NE: "B \<noteq> {}" and LEQ: "|B| \<le>o |A|"
shows "|A \<times> B| =o |A| \<and> |B \<times> A| =o |A|"
proof-
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


corollary card_of_Times_infinite_simps:
"\<lbrakk>infinite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |A \<times> B| =o |A|"
"\<lbrakk>infinite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |A| =o |A \<times> B|"
"\<lbrakk>infinite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |B \<times> A| =o |A|"
"\<lbrakk>infinite A; B \<noteq> {}; |B| \<le>o |A|\<rbrakk> \<Longrightarrow> |A| =o |B \<times> A|"
by (auto simp add: card_of_Times_infinite ordIso_symmetric)


corollary Card_order_Times_infinite:
assumes INF: "infinite(Field r)" and CARD: "Card_order r" and
        NE: "Field p \<noteq> {}" and LEQ: "p \<le>o r"
shows "| (Field r) \<times> (Field p) | =o r \<and> | (Field p) \<times> (Field r) | =o r"
proof-
  have "|Field r \<times> Field p| =o |Field r| \<and> |Field p \<times> Field r| =o |Field r|"
  using assms by (simp add: card_of_Times_infinite card_of_mono2)
  thus ?thesis
  using assms card_of_Field_ordIso[of r]
        ordIso_transitive[of "|Field r \<times> Field p|"]
        ordIso_transitive[of _ "|Field r|"] by blast
qed


lemma card_of_Sigma_ordLeq_infinite:
assumes INF: "infinite B" and
        LEQ_I: "|I| \<le>o |B|" and LEQ: "\<forall>i \<in> I. |A i| \<le>o |B|"
shows "|SIGMA i : I. A i| \<le>o |B|"
proof(cases "I = {}", simp add: card_of_empty)
  assume *: "I \<noteq> {}"
  have "|SIGMA i : I. A i| \<le>o |I \<times> B|"
  using LEQ card_of_Sigma_Times by blast
  moreover have "|I \<times> B| =o |B|"
  using INF * LEQ_I by (auto simp add: card_of_Times_infinite)
  ultimately show ?thesis using ordLeq_ordIso_trans by blast
qed


lemma card_of_Sigma_ordLeq_infinite_Field:
assumes INF: "infinite (Field r)" and r: "Card_order r" and
        LEQ_I: "|I| \<le>o r" and LEQ: "\<forall>i \<in> I. |A i| \<le>o r"
shows "|SIGMA i : I. A i| \<le>o r"
proof-
  let ?B  = "Field r"
  have 1: "r =o |?B| \<and> |?B| =o r" using r card_of_Field_ordIso
  ordIso_symmetric by blast
  hence "|I| \<le>o |?B|"  "\<forall>i \<in> I. |A i| \<le>o |?B|"
  using LEQ_I LEQ ordLeq_ordIso_trans by blast+
  hence  "|SIGMA i : I. A i| \<le>o |?B|" using INF LEQ
  card_of_Sigma_ordLeq_infinite by blast
  thus ?thesis using 1 ordLeq_ordIso_trans by blast
qed


lemma card_of_Times_ordLeq_infinite_Field:
"\<lbrakk>infinite (Field r); |A| \<le>o r; |B| \<le>o r; Card_order r\<rbrakk>
 \<Longrightarrow> |A <*> B| \<le>o r"
by(simp add: card_of_Sigma_ordLeq_infinite_Field)


lemma card_of_UNION_ordLeq_infinite:
assumes INF: "infinite B" and
        LEQ_I: "|I| \<le>o |B|" and LEQ: "\<forall>i \<in> I. |A i| \<le>o |B|"
shows "|\<Union> i \<in> I. A i| \<le>o |B|"
proof(cases "I = {}", simp add: card_of_empty)
  assume *: "I \<noteq> {}"
  have "|\<Union> i \<in> I. A i| \<le>o |SIGMA i : I. A i|"
  using card_of_UNION_Sigma by blast
  moreover have "|SIGMA i : I. A i| \<le>o |B|"
  using assms card_of_Sigma_ordLeq_infinite by blast
  ultimately show ?thesis using ordLeq_transitive by blast
qed


corollary card_of_UNION_ordLeq_infinite_Field:
assumes INF: "infinite (Field r)" and r: "Card_order r" and
        LEQ_I: "|I| \<le>o r" and LEQ: "\<forall>i \<in> I. |A i| \<le>o r"
shows "|\<Union> i \<in> I. A i| \<le>o r"
proof-
  let ?B  = "Field r"
  have 1: "r =o |?B| \<and> |?B| =o r" using r card_of_Field_ordIso
  ordIso_symmetric by blast
  hence "|I| \<le>o |?B|"  "\<forall>i \<in> I. |A i| \<le>o |?B|"
  using LEQ_I LEQ ordLeq_ordIso_trans by blast+
  hence  "|\<Union> i \<in> I. A i| \<le>o |?B|" using INF LEQ
  card_of_UNION_ordLeq_infinite by blast
  thus ?thesis using 1 ordLeq_ordIso_trans by blast
qed


lemma card_of_Plus_infinite1:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|A <+> B| =o |A|"
proof(cases "B = {}", simp add: card_of_Plus_empty1 card_of_Plus_empty2 ordIso_symmetric)
  let ?Inl = "Inl::'a \<Rightarrow> 'a + 'b"  let ?Inr = "Inr::'b \<Rightarrow> 'a + 'b"
  assume *: "B \<noteq> {}"
  then obtain b1 where 1: "b1 \<in> B" by blast
  show ?thesis
  proof(cases "B = {b1}")
    assume Case1: "B = {b1}"
    have 2: "bij_betw ?Inl A ((?Inl ` A))"
    unfolding bij_betw_def inj_on_def by auto
    hence 3: "infinite (?Inl ` A)"
    using INF bij_betw_finite[of ?Inl A] by blast
    let ?A' = "?Inl ` A \<union> {?Inr b1}"
    obtain g where "bij_betw g (?Inl ` A) ?A'"
    using 3 infinite_imp_bij_betw2[of "?Inl ` A"] by auto
    moreover have "?A' = A <+> B" using Case1 by blast
    ultimately have "bij_betw g (?Inl ` A) (A <+> B)" by simp
    hence "bij_betw (g o ?Inl) A (A <+> B)"
    using 2 by (auto simp add: bij_betw_trans)
    thus ?thesis using card_of_ordIso ordIso_symmetric by blast
  next
    assume Case2: "B \<noteq> {b1}"
    with * 1 obtain b2 where 3: "b1 \<noteq> b2 \<and> {b1,b2} \<le> B" by fastforce
    obtain f where "inj_on f B \<and> f ` B \<le> A"
    using LEQ card_of_ordLeq[of B] by fastforce
    with 3 have "f b1 \<noteq> f b2 \<and> {f b1, f b2} \<le> A"
    unfolding inj_on_def by auto
    with 3 have "|A <+> B| \<le>o |A \<times> B|"
    by (auto simp add: card_of_Plus_Times)
    moreover have "|A \<times> B| =o |A|"
    using assms * by (simp add: card_of_Times_infinite_simps)
    ultimately have "|A <+> B| \<le>o |A|" using ordLeq_ordIso_trans by metis
    thus ?thesis using card_of_Plus1 ordIso_iff_ordLeq by blast
  qed
qed


lemma card_of_Plus_infinite2:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|B <+> A| =o |A|"
using assms card_of_Plus_commute card_of_Plus_infinite1
ordIso_equivalence by blast


lemma card_of_Plus_infinite:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|A <+> B| =o |A| \<and> |B <+> A| =o |A|"
using assms by (auto simp: card_of_Plus_infinite1 card_of_Plus_infinite2)


corollary Card_order_Plus_infinite:
assumes INF: "infinite(Field r)" and CARD: "Card_order r" and
        LEQ: "p \<le>o r"
shows "| (Field r) <+> (Field p) | =o r \<and> | (Field p) <+> (Field r) | =o r"
proof-
  have "| Field r <+> Field p | =o | Field r | \<and>
        | Field p <+> Field r | =o | Field r |"
  using assms by (simp add: card_of_Plus_infinite card_of_mono2)
  thus ?thesis
  using assms card_of_Field_ordIso[of r]
        ordIso_transitive[of "|Field r <+> Field p|"]
        ordIso_transitive[of _ "|Field r|"] by blast
qed


lemma card_of_Un_infinite:
assumes INF: "infinite A" and LEQ: "|B| \<le>o |A|"
shows "|A \<union> B| =o |A| \<and> |B \<union> A| =o |A|"
proof-
  have "|A \<union> B| \<le>o |A <+> B|" by (rule card_of_Un_Plus_ordLeq)
  moreover have "|A <+> B| =o |A|"
  using assms by (metis card_of_Plus_infinite)
  ultimately have "|A \<union> B| \<le>o |A|" using ordLeq_ordIso_trans by blast
  hence "|A \<union> B| =o |A|" using card_of_Un1 ordIso_iff_ordLeq by blast
  thus ?thesis using Un_commute[of B A] by auto
qed


lemma card_of_Un_diff_infinite:
assumes INF: "infinite A" and LESS: "|B| <o |A|"
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
   hence "infinite B" by auto
   ultimately have False
   using card_of_Un_infinite 1 ordIso_equivalence(1,3) LESS not_ordLess_ordIso by metis
  }
  hence 2: "|B| \<le>o |C|" using card_of_Well_order ordLeq_total by blast
  {assume *: "finite C"
    hence "finite B" using card_of_ordLeq_finite 2 by blast
    hence False using * INF card_of_ordIso_finite 1 by blast
  }
  hence "infinite C" by auto
  hence "|C| =o |A|"
  using  card_of_Un_infinite 1 2 ordIso_equivalence(1,3) by metis
  thus ?thesis unfolding C_def .
qed


lemma card_of_Plus_ordLess_infinite:
assumes INF: "infinite C" and
        LESS1: "|A| <o |C|" and LESS2: "|B| <o |C|"
shows "|A <+> B| <o |C|"
proof(cases "A = {} \<or> B = {}")
  assume Case1: "A = {} \<or> B = {}"
  hence "|A| =o |A <+> B| \<or> |B| =o |A <+> B|"
  using card_of_Plus_empty1 card_of_Plus_empty2 by blast
  hence "|A <+> B| =o |A| \<or> |A <+> B| =o |B|"
  using ordIso_symmetric[of "|A|"] ordIso_symmetric[of "|B|"] by blast
  thus ?thesis using LESS1 LESS2
       ordIso_ordLess_trans[of "|A <+> B|" "|A|"]
       ordIso_ordLess_trans[of "|A <+> B|" "|B|"] by blast
next
  assume Case2: "\<not>(A = {} \<or> B = {})"
  {assume *: "|C| \<le>o |A <+> B|"
   hence "infinite (A <+> B)" using INF card_of_ordLeq_finite by blast
   hence 1: "infinite A \<or> infinite B" using finite_Plus by blast
   {assume Case21: "|A| \<le>o |B|"
    hence "infinite B" using 1 card_of_ordLeq_finite by blast
    hence "|A <+> B| =o |B|" using Case2 Case21
    by (auto simp add: card_of_Plus_infinite)
    hence False using LESS2 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   moreover
   {assume Case22: "|B| \<le>o |A|"
    hence "infinite A" using 1 card_of_ordLeq_finite by blast
    hence "|A <+> B| =o |A|" using Case2 Case22
    by (auto simp add: card_of_Plus_infinite)
    hence False using LESS1 not_ordLess_ordLeq * ordLeq_ordIso_trans by blast
   }
   ultimately have False using ordLeq_total card_of_Well_order[of A]
   card_of_Well_order[of B] by blast
  }
  thus ?thesis using ordLess_or_ordLeq[of "|A <+> B|" "|C|"]
  card_of_Well_order[of "A <+> B"] card_of_Well_order[of "C"] by auto
qed


lemma card_of_Plus_ordLess_infinite_Field:
assumes INF: "infinite (Field r)" and r: "Card_order r" and
        LESS1: "|A| <o r" and LESS2: "|B| <o r"
shows "|A <+> B| <o r"
proof-
  let ?C  = "Field r"
  have 1: "r =o |?C| \<and> |?C| =o r" using r card_of_Field_ordIso
  ordIso_symmetric by blast
  hence "|A| <o |?C|"  "|B| <o |?C|"
  using LESS1 LESS2 ordLess_ordIso_trans by blast+
  hence  "|A <+> B| <o |?C|" using INF
  card_of_Plus_ordLess_infinite by blast
  thus ?thesis using 1 ordLess_ordIso_trans by blast
qed


lemma infinite_card_of_insert:
assumes "infinite A"
shows "|insert a A| =o |A|"
proof-
  have iA: "insert a A = A \<union> {a}" by simp
  show ?thesis
  using infinite_imp_bij_betw2[OF assms] unfolding iA
  by (metis bij_betw_inv card_of_ordIso)
qed


subsection {* Cardinals versus lists  *}


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
assumes "infinite A"
shows "|nlists A n| \<le>o |A|"
proof(induct n)
  have "A \<noteq> {}" using assms by auto
  thus "|nlists A 0| \<le>o |A|" by (simp add: nlists_0 card_of_singl_ordLeq)
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


lemma card_of_lists_infinite:
assumes "infinite A"
shows "|lists A| =o |A|"
proof-
  have "|lists A| \<le>o |A|"
  using assms
  by (auto simp add: lists_UNION_nlists card_of_UNION_ordLeq_infinite
                     infinite_iff_card_of_nat card_of_nlists_infinite)
  thus ?thesis using card_of_lists ordIso_iff_ordLeq by blast
qed


lemma Card_order_lists_infinite:
assumes "Card_order r" and "infinite(Field r)"
shows "|lists(Field r)| =o r"
using assms card_of_lists_infinite card_of_Field_ordIso ordIso_transitive by blast



subsection {* The cardinal $\omega$ and the finite cardinals  *}


text{* The cardinal $\omega$, of natural numbers, shall be the standard non-strict
order relation on
@{text "nat"}, that we abbreviate by @{text "natLeq"}.  The finite cardinals
shall be the restrictions of these relations to the numbers smaller than
fixed numbers @{text "n"}, that we abbreviate by @{text "natLeq_on n"}.  *}

abbreviation "(natLeq::(nat * nat) set) \<equiv> {(x,y). x \<le> y}"
abbreviation "(natLess::(nat * nat) set) \<equiv> {(x,y). x < y}"

abbreviation natLeq_on :: "nat \<Rightarrow> (nat * nat) set"
where "natLeq_on n \<equiv> {(x,y). x < n \<and> y < n \<and> x \<le> y}"

lemma infinite_cartesian_product:
assumes "infinite A" "infinite B"
shows "infinite (A \<times> B)"
proof
  assume "finite (A \<times> B)"
  from assms(1) have "A \<noteq> {}" by auto
  with `finite (A \<times> B)` have "finite B" using finite_cartesian_productD2 by auto
  with assms(2) show False by simp
qed



subsubsection {* First as well-orders *}


lemma Field_natLeq: "Field natLeq = (UNIV::nat set)"
by(unfold Field_def, auto)


lemma natLeq_Refl: "Refl natLeq"
unfolding refl_on_def Field_def by auto


lemma natLeq_trans: "trans natLeq"
unfolding trans_def by auto


lemma natLeq_Preorder: "Preorder natLeq"
unfolding preorder_on_def
by (auto simp add: natLeq_Refl natLeq_trans)


lemma natLeq_antisym: "antisym natLeq"
unfolding antisym_def by auto


lemma natLeq_Partial_order: "Partial_order natLeq"
unfolding partial_order_on_def
by (auto simp add: natLeq_Preorder natLeq_antisym)


lemma natLeq_Total: "Total natLeq"
unfolding total_on_def by auto


lemma natLeq_Linear_order: "Linear_order natLeq"
unfolding linear_order_on_def
by (auto simp add: natLeq_Partial_order natLeq_Total)


lemma natLeq_natLess_Id: "natLess = natLeq - Id"
by auto


lemma natLeq_Well_order: "Well_order natLeq"
unfolding well_order_on_def
using natLeq_Linear_order wf_less natLeq_natLess_Id by auto


corollary natLeq_well_order_on: "well_order_on UNIV natLeq"
using natLeq_Well_order Field_natLeq by auto


lemma natLeq_wo_rel: "wo_rel natLeq"
unfolding wo_rel_def using natLeq_Well_order .


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


lemma Field_natLeq_on: "Field (natLeq_on n) = {0 ..< n}"
unfolding Field_def by auto


lemma natLeq_underS_less: "rel.underS natLeq n = {0 ..< n}"
unfolding rel.underS_def by auto


lemma Restr_natLeq: "Restr natLeq {0 ..< n} = natLeq_on n"
by auto


lemma Restr_natLeq2:
"Restr natLeq (rel.underS natLeq n) = natLeq_on n"
by (auto simp add: Restr_natLeq natLeq_underS_less)


lemma natLeq_on_Well_order: "Well_order(natLeq_on n)"
using Restr_natLeq[of n] natLeq_Well_order
      Well_order_Restr[of natLeq "{0..<n}"] by auto


corollary natLeq_on_well_order_on: "well_order_on {0 ..< n} (natLeq_on n)"
using natLeq_on_Well_order Field_natLeq_on by auto


lemma natLeq_on_wo_rel: "wo_rel(natLeq_on n)"
unfolding wo_rel_def using natLeq_on_Well_order .


lemma natLeq_on_ofilter_less_eq:
"n \<le> m \<Longrightarrow> wo_rel.ofilter (natLeq_on m) {0 ..< n}"
by (auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def,
    simp add: Field_natLeq_on, unfold rel.under_def, auto)


lemma natLeq_on_ofilter_iff:
"wo_rel.ofilter (natLeq_on m) A = (\<exists>n \<le> m. A = {0 ..< n})"
proof(rule iffI)
  assume *: "wo_rel.ofilter (natLeq_on m) A"
  hence 1: "A \<le> {0..<m}"
  by (auto simp add: natLeq_on_wo_rel wo_rel.ofilter_def rel.under_def Field_natLeq_on)
  hence "\<forall>n1 n2. n2 \<in> A \<and> n1 \<le> n2 \<longrightarrow> n1 \<in> A"
  using * by(fastforce simp add: natLeq_on_wo_rel wo_rel.ofilter_def rel.under_def)
  hence "A = UNIV \<or> (\<exists>n. A = {0 ..< n})" using closed_nat_set_iff by blast
  thus "\<exists>n \<le> m. A = {0 ..< n}" using 1 atLeastLessThan_less_eq by blast
next
  assume "(\<exists>n\<le>m. A = {0 ..< n})"
  thus "wo_rel.ofilter (natLeq_on m) A" by (auto simp add: natLeq_on_ofilter_less_eq)
qed



subsubsection {* Then as cardinals *}


lemma natLeq_Card_order: "Card_order natLeq"
proof(auto simp add: natLeq_Well_order
      Card_order_iff_Restr_underS Restr_natLeq2, simp add:  Field_natLeq)
  fix n have "finite(Field (natLeq_on n))"
  unfolding Field_natLeq_on by auto
  moreover have "infinite(UNIV::nat set)" by auto
  ultimately show "natLeq_on n <o |UNIV::nat set|"
  using finite_ordLess_infinite[of "natLeq_on n" "|UNIV::nat set|"]
        Field_card_of[of "UNIV::nat set"]
        card_of_Well_order[of "UNIV::nat set"] natLeq_on_Well_order[of n] by auto
qed


corollary card_of_Field_natLeq:
"|Field natLeq| =o natLeq"
using Field_natLeq natLeq_Card_order Card_order_iff_ordIso_card_of[of natLeq]
      ordIso_symmetric[of natLeq] by blast


corollary card_of_nat:
"|UNIV::nat set| =o natLeq"
using Field_natLeq card_of_Field_natLeq by auto


corollary infinite_iff_natLeq_ordLeq:
"infinite A = ( natLeq \<le>o |A| )"
using infinite_iff_card_of_nat[of A] card_of_nat
      ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric by blast


corollary finite_iff_ordLess_natLeq:
"finite A = ( |A| <o natLeq)"
using infinite_iff_natLeq_ordLeq not_ordLeq_iff_ordLess
      card_of_Well_order natLeq_Well_order by blast


lemma ordIso_natLeq_on_imp_finite:
"|A| =o natLeq_on n \<Longrightarrow> finite A"
unfolding ordIso_def iso_def[abs_def]
by (auto simp: Field_natLeq_on bij_betw_finite Field_card_of)


lemma natLeq_on_Card_order: "Card_order (natLeq_on n)"
proof(unfold card_order_on_def,
      auto simp add: natLeq_on_Well_order, simp add: Field_natLeq_on)
  fix r assume "well_order_on {0..<n} r"
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
using Field_natLeq_on card_of_Field_natLeq_on by auto


lemma natLeq_on_ordLeq_less_eq:
"((natLeq_on m) \<le>o (natLeq_on n)) = (m \<le> n)"
proof
  assume "natLeq_on m \<le>o natLeq_on n"
  then obtain f where "inj_on f {0..<m} \<and> f ` {0..<m} \<le> {0..<n}"
  using Field_natLeq_on[of m] Field_natLeq_on[of n]
  unfolding ordLeq_def using embed_inj_on[of "natLeq_on m"  "natLeq_on n"]
  embed_Field[of "natLeq_on m" "natLeq_on n"] using natLeq_on_Well_order[of m] by fastforce
  thus "m \<le> n" using atLeastLessThan_less_eq2 by blast
next
  assume "m \<le> n"
  hence "inj_on id {0..<m} \<and> id ` {0..<m} \<le> {0..<n}" unfolding inj_on_def by auto
  hence "|{0..<m}| \<le>o |{0..<n}|" using card_of_ordLeq by blast
  thus "natLeq_on m \<le>o natLeq_on n"
  using card_of_less ordIso_ordLeq_trans ordLeq_ordIso_trans ordIso_symmetric by blast
qed


lemma natLeq_on_ordLeq_less:
"((natLeq_on m) <o (natLeq_on n)) = (m < n)"
using not_ordLeq_iff_ordLess[of "natLeq_on m" "natLeq_on n"]
natLeq_on_Well_order natLeq_on_ordLeq_less_eq by auto



subsubsection {* "Backwards compatibility" with the numeric cardinal operator for finite sets *}


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



subsection {* The successor of a cardinal *}


text{* First we define @{text "isCardSuc r r'"}, the notion of @{text "r'"}
being a successor cardinal of @{text "r"}. Although the definition does
not require @{text "r"} to be a cardinal, only this case will be meaningful.  *}


definition isCardSuc :: "'a rel \<Rightarrow> 'a set rel \<Rightarrow> bool"
where
"isCardSuc r r' \<equiv>
 Card_order r' \<and> r <o r' \<and>
 (\<forall>(r''::'a set rel). Card_order r'' \<and> r <o r'' \<longrightarrow> r' \<le>o r'')"


text{* Now we introduce the cardinal-successor operator @{text "cardSuc"},
by picking {\em some} cardinal-order relation fulfilling @{text "isCardSuc"}.
Again, the picked item shall be proved unique up to order-isomorphism. *}


definition cardSuc :: "'a rel \<Rightarrow> 'a set rel"
where
"cardSuc r \<equiv> SOME r'. isCardSuc r r'"


lemma exists_minim_Card_order:
"\<lbrakk>R \<noteq> {}; \<forall>r \<in> R. Card_order r\<rbrakk> \<Longrightarrow> \<exists>r \<in> R. \<forall>r' \<in> R. r \<le>o r'"
unfolding card_order_on_def using exists_minim_Well_order by blast


lemma exists_isCardSuc:
assumes "Card_order r"
shows "\<exists>r'. isCardSuc r r'"
proof-
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


text{* The minimality property of @{text "cardSuc"} originally present in its definition
is local to the type @{text "'a set rel"}, i.e., that of @{text "cardSuc r"}:  *}

lemma cardSuc_least_aux:
"\<lbrakk>Card_order (r::'a rel); Card_order (r'::'a set rel); r <o r'\<rbrakk> \<Longrightarrow> cardSuc r \<le>o r'"
using cardSuc_isCardSuc unfolding isCardSuc_def by blast


text{* But from this we can infer general minimality: *}

lemma cardSuc_least:
assumes CARD: "Card_order r" and CARD': "Card_order r'" and LESS: "r <o r'"
shows "cardSuc r \<le>o r'"
proof-
  let ?p = "cardSuc r"
  have 0: "Well_order ?p \<and> Well_order r'"
  using assms cardSuc_Card_order unfolding card_order_on_def by blast
  {assume "r' <o ?p"
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
proof(auto simp add: assms cardSuc_least)
  assume "cardSuc r \<le>o r'"
  thus "r <o r'" using assms cardSuc_greater ordLess_ordLeq_trans by blast
qed


lemma cardSuc_ordLeq_ordLess:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(r' <o cardSuc r) = (r' \<le>o r)"
proof-
  have "Well_order r \<and> Well_order r'"
  using assms unfolding card_order_on_def by auto
  moreover have "Well_order(cardSuc r)"
  using assms cardSuc_Card_order card_order_on_def by blast
  ultimately show ?thesis
  using assms cardSuc_ordLess_ordLeq[of r r']
  not_ordLeq_iff_ordLess[of r r'] not_ordLeq_iff_ordLess[of r' "cardSuc r"] by blast
qed


lemma cardSuc_mono_ordLeq:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(cardSuc r \<le>o cardSuc r') = (r \<le>o r')"
using assms cardSuc_ordLeq_ordLess cardSuc_ordLess_ordLeq cardSuc_Card_order by blast


lemma cardSuc_invar_ordIso:
assumes CARD: "Card_order r" and CARD': "Card_order r'"
shows "(cardSuc r =o cardSuc r') = (r =o r')"
proof-
  have 0: "Well_order r \<and> Well_order r' \<and> Well_order(cardSuc r) \<and> Well_order(cardSuc r')"
  using assms by (simp add: card_order_on_well_order_on cardSuc_Card_order)
  thus ?thesis
  using ordIso_iff_ordLeq[of r r'] ordIso_iff_ordLeq
  using cardSuc_mono_ordLeq[of r r'] cardSuc_mono_ordLeq[of r' r] assms by blast
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
  unfolding r_def p_def Field_natLeq_on by simp
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
     using 1 WELL embed_inj_on unfolding bij_betw_def by force
     moreover have "finite(f ` (Field r'))" using 3 finite_atLeastLessThan[of 0 m] by force
     ultimately have 5: "finite (Field r') \<and> card(Field r') = card (f ` (Field r'))"
     using bij_betw_same_card bij_betw_finite by metis
     hence "card(Field r') \<le> card(Field r)" using 3 4 FIELD by force
     hence "|Field r'| \<le>o |Field r|" using FIN 5 finite_card_of_iff_card2 by blast
     hence False using LESS not_ordLess_ordLeq by auto
    }
    thus ?thesis using WELL CARD by (fastforce simp: not_ordLess_iff_ordLeq)
  qed
  ultimately show ?thesis using ordIso_iff_ordLeq unfolding r'_def p_def by blast
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
  then obtain n where "|A| =o natLeq_on n" using finite_iff_card_of_natLeq_on by blast
  hence "cardSuc |A| =o cardSuc(natLeq_on n)"
  using card_of_Card_order cardSuc_invar_ordIso natLeq_on_Card_order by blast
  hence "cardSuc |A| =o natLeq_on(Suc n)"
  using cardSuc_natLeq_on_Suc ordIso_transitive by blast
  hence "cardSuc |A| =o |{0..<(Suc n)}|" using card_of_less ordIso_equivalence by blast
  moreover have "|Field (cardSuc |A| ) | =o cardSuc |A|"
  using card_of_Field_ordIso cardSuc_Card_order card_of_Card_order by blast
  ultimately have "|Field (cardSuc |A| ) | =o |{0..<(Suc n)}|"
  using ordIso_equivalence by blast
  thus "finite (Field (cardSuc |A| ))"
  using card_of_ordIso_finite finite_atLeastLessThan by blast
qed


lemma cardSuc_finite:
assumes "Card_order r"
shows "finite (Field (cardSuc r)) = finite (Field r)"
proof-
  let ?A = "Field r"
  have "|?A| =o r" using assms by (simp add: card_of_Field_ordIso)
  hence "cardSuc |?A| =o cardSuc r" using assms
  by (simp add: card_of_Card_order cardSuc_invar_ordIso)
  moreover have "|Field (cardSuc |?A| ) | =o cardSuc |?A|"
  by (simp add: card_of_card_order_on Field_card_of card_of_Field_ordIso cardSuc_Card_order)
  moreover
  {have "|Field (cardSuc r) | =o cardSuc r"
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


lemma card_of_Plus_ordLeq_infinite_Field:
assumes r: "infinite (Field r)" and A: "|A| \<le>o r" and B: "|B| \<le>o r"
and c: "Card_order r"
shows "|A <+> B| \<le>o r"
proof-
  let ?r' = "cardSuc r"
  have "Card_order ?r' \<and> infinite (Field ?r')" using assms
  by (simp add: cardSuc_Card_order cardSuc_finite)
  moreover have "|A| <o ?r'" and "|B| <o ?r'" using A B c
  by (auto simp: card_of_card_order_on Field_card_of cardSuc_ordLeq_ordLess)
  ultimately have "|A <+> B| <o ?r'"
  using card_of_Plus_ordLess_infinite_Field by blast
  thus ?thesis using c r
  by (simp add: card_of_card_order_on Field_card_of cardSuc_ordLeq_ordLess)
qed


lemma card_of_Un_ordLeq_infinite_Field:
assumes C: "infinite (Field r)" and A: "|A| \<le>o r" and B: "|B| \<le>o r"
and "Card_order r"
shows "|A Un B| \<le>o r"
using assms card_of_Plus_ordLeq_infinite_Field card_of_Un_Plus_ordLeq
ordLeq_transitive by blast



subsection {* Regular cardinals *}


definition cofinal where
"cofinal A r \<equiv>
 ALL a : Field r. EX b : A. a \<noteq> b \<and> (a,b) : r"


definition regular where
"regular r \<equiv>
 ALL K. K \<le> Field r \<and> cofinal K r \<longrightarrow> |K| =o r"


definition relChain where
"relChain r As \<equiv>
 ALL i j. (i,j) \<in> r \<longrightarrow> As i \<le> As j"

lemma regular_UNION:
assumes r: "Card_order r"   "regular r"
and As: "relChain r As"
and Bsub: "B \<le> (UN i : Field r. As i)"
and cardB: "|B| <o r"
shows "EX i : Field r. B \<le> As i"
proof-
  let ?phi = "%b j. j : Field r \<and> b : As j"
  have "ALL b : B. EX j. ?phi b j" using Bsub by blast
  then obtain f where f: "!! b. b : B \<Longrightarrow> ?phi b (f b)"
  using bchoice[of B ?phi] by blast
  let ?K = "f ` B"
  {assume 1: "!! i. i : Field r \<Longrightarrow> ~ B \<le> As i"
   have 2: "cofinal ?K r"
   unfolding cofinal_def proof auto
     fix i assume i: "i : Field r"
     with 1 obtain b where b: "b : B \<and> b \<notin> As i" by blast
     hence "i \<noteq> f b \<and> ~ (f b,i) : r"
     using As f unfolding relChain_def by auto
     hence "i \<noteq> f b \<and> (i, f b) : r" using r
     unfolding card_order_on_def well_order_on_def linear_order_on_def
     total_on_def using i f b by auto
     with b show "\<exists>b\<in>B. i \<noteq> f b \<and> (i, f b) \<in> r" by blast
   qed
   moreover have "?K \<le> Field r" using f by blast
   ultimately have "|?K| =o r" using 2 r unfolding regular_def by blast
   moreover
   {
    have "|?K| <=o |B|" using card_of_image .
    hence "|?K| <o r" using cardB ordLeq_ordLess_trans by blast
   }
   ultimately have False using not_ordLess_ordIso by blast
  }
  thus ?thesis by blast
qed


lemma infinite_cardSuc_regular:
assumes r_inf: "infinite (Field r)" and r_card: "Card_order r"
shows "regular (cardSuc r)"
proof-
  let ?r' = "cardSuc r"
  have r': "Card_order ?r'"
  "!! p. Card_order p \<longrightarrow> (p \<le>o r) = (p <o ?r')"
  using r_card by (auto simp: cardSuc_Card_order cardSuc_ordLeq_ordLess)
  show ?thesis
  unfolding regular_def proof auto
    fix K assume 1: "K \<le> Field ?r'" and 2: "cofinal K ?r'"
    hence "|K| \<le>o |Field ?r'|" by (simp only: card_of_mono1)
    also have 22: "|Field ?r'| =o ?r'"
    using r' by (simp add: card_of_Field_ordIso[of ?r'])
    finally have "|K| \<le>o ?r'" .
    moreover
    {let ?L = "UN j : K. rel.underS ?r' j"
     let ?J = "Field r"
     have rJ: "r =o |?J|"
     using r_card card_of_Field_ordIso ordIso_symmetric by blast
     assume "|K| <o ?r'"
     hence "|K| <=o r" using r' card_of_Card_order[of K] by blast
     hence "|K| \<le>o |?J|" using rJ ordLeq_ordIso_trans by blast
     moreover
     {have "ALL j : K. |rel.underS ?r' j| <o ?r'"
      using r' 1 by (auto simp: card_of_underS)
      hence "ALL j : K. |rel.underS ?r' j| \<le>o r"
      using r' card_of_Card_order by blast
      hence "ALL j : K. |rel.underS ?r' j| \<le>o |?J|"
      using rJ ordLeq_ordIso_trans by blast
     }
     ultimately have "|?L| \<le>o |?J|"
     using r_inf card_of_UNION_ordLeq_infinite by blast
     hence "|?L| \<le>o r" using rJ ordIso_symmetric ordLeq_ordIso_trans by blast
     hence "|?L| <o ?r'" using r' card_of_Card_order by blast
     moreover
     {
      have "Field ?r' \<le> ?L"
      using 2 unfolding rel.underS_def cofinal_def by auto
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
assumes r: "Card_order r" and "infinite (Field r)"
and As: "relChain (cardSuc r) As"
and Bsub: "B \<le> (UN i : Field (cardSuc r). As i)"
and cardB: "|B| <=o r"
shows "EX i : Field (cardSuc r). B \<le> As i"
proof-
  let ?r' = "cardSuc r"
  have "Card_order ?r' \<and> |B| <o ?r'"
  using r cardB cardSuc_ordLeq_ordLess cardSuc_Card_order
  card_of_Card_order by blast
  moreover have "regular ?r'"
  using assms by(simp add: infinite_cardSuc_regular)
  ultimately show ?thesis
  using As Bsub cardB regular_UNION by blast
qed


subsection {* Others *}

(* FIXME: finitte ~> finite? *)
lemma card_of_infinite_diff_finitte:
assumes "infinite A" and "finite B"
shows "|A - B| =o |A|"
by (metis assms card_of_Un_diff_infinite finite_ordLess_infinite2)

(* function space *)
definition Func where
"Func A B \<equiv>
 {f. (\<forall> a. f a \<noteq> None \<longleftrightarrow> a \<in> A) \<and> (\<forall> a \<in> A. case f a of Some b \<Rightarrow> b \<in> B |None \<Rightarrow> True)}"

lemma Func_empty:
"Func {} B = {empty}"
unfolding Func_def by auto

lemma Func_elim:
assumes "g \<in> Func A B" and "a \<in> A"
shows "\<exists> b. b \<in> B \<and> g a = Some b"
using assms unfolding Func_def by (cases "g a") force+

definition curr where
"curr A f \<equiv> \<lambda> a. if a \<in> A then Some (\<lambda> b. f (a,b)) else None"

lemma curr_in:
assumes f: "f \<in> Func (A <*> B) C"
shows "curr A f \<in> Func A (Func B C)"
using assms unfolding curr_def Func_def by auto

lemma curr_inj:
assumes "f1 \<in> Func (A <*> B) C" and "f2 \<in> Func (A <*> B) C"
shows "curr A f1 = curr A f2 \<longleftrightarrow> f1 = f2"
proof safe
  assume c: "curr A f1 = curr A f2"
  show "f1 = f2"
  proof (rule ext, clarify)
    fix a b show "f1 (a, b) = f2 (a, b)"
    proof (cases "(a,b) \<in> A <*> B")
      case False
      thus ?thesis using assms unfolding Func_def
      apply(cases "f1 (a,b)") apply(cases "f2 (a,b)", fastforce, fastforce)
      apply(cases "f2 (a,b)") by auto
    next
      case True hence a: "a \<in> A" and b: "b \<in> B" by auto
      thus ?thesis
      using c unfolding curr_def fun_eq_iff
      apply(elim allE[of _ a]) apply simp unfolding fun_eq_iff by auto
    qed
  qed
qed

lemma curr_surj:
assumes "g \<in> Func A (Func B C)"
shows "\<exists> f \<in> Func (A <*> B) C. curr A f = g"
proof
  let ?f = "\<lambda> ab. case g (fst ab) of None \<Rightarrow> None | Some g1 \<Rightarrow> g1 (snd ab)"
  show "curr A ?f = g"
  proof (rule ext)
    fix a show "curr A ?f a = g a"
    proof (cases "a \<in> A")
      case False
      hence "g a = None" using assms unfolding Func_def by auto
      thus ?thesis unfolding curr_def using False by simp
    next
      case True
      obtain g1 where "g1 \<in> Func B C" and "g a = Some g1"
      using assms using Func_elim[OF assms True] by blast
      thus ?thesis using True unfolding curr_def by auto
    qed
  qed
  show "?f \<in> Func (A <*> B) C"
  unfolding Func_def mem_Collect_eq proof(intro conjI allI ballI)
    fix ab show "?f ab \<noteq> None \<longleftrightarrow> ab \<in> A \<times> B"
    proof(cases "g (fst ab)")
      case None
      hence "fst ab \<notin> A" using assms unfolding Func_def by force
      thus ?thesis using None by auto
    next
      case (Some g1)
      hence fst: "fst ab \<in> A" and g1: "g1 \<in> Func B C"
      using assms unfolding Func_def[of A] by force+
      hence "?f ab \<noteq> None \<longleftrightarrow> g1 (snd ab) \<noteq> None" using Some by auto
      also have "... \<longleftrightarrow> snd ab \<in> B" using g1 unfolding Func_def by auto
      also have "... \<longleftrightarrow> ab \<in> A \<times> B" using fst by (cases ab, auto)
      finally show ?thesis .
    qed
  next
    fix ab assume ab: "ab \<in> A \<times> B"
    hence "fst ab \<in> A" and "snd ab \<in> B" by(cases ab, auto)
    then obtain g1 where "g1 \<in> Func B C" and "g (fst ab) = Some g1"
    using assms using Func_elim[OF assms] by blast
    thus "case ?f ab of Some c \<Rightarrow> c \<in> C |None \<Rightarrow> True"
    unfolding Func_def by auto
  qed
qed

(* FIXME: betwe ~> betw? *)
lemma bij_betwe_curr:
"bij_betw (curr A) (Func (A <*> B) C) (Func A (Func B C))"
unfolding bij_betw_def inj_on_def image_def
using curr_in curr_inj curr_surj by blast

lemma card_of_Func_Times:
"|Func (A <*> B) C| =o |Func A (Func B C)|"
unfolding card_of_ordIso[symmetric]
using bij_betwe_curr by blast

definition Func_map where
"Func_map B2 f1 f2 g b2 \<equiv>
 if b2 \<in> B2 then case g (f2 b2) of None \<Rightarrow> None | Some a1 \<Rightarrow> Some (f1 a1)
            else None"

lemma Func_map:
assumes g: "g \<in> Func A2 A1" and f1: "f1 ` A1 \<subseteq> B1" and f2: "f2 ` B2 \<subseteq> A2"
shows "Func_map B2 f1 f2 g \<in> Func B2 B1"
unfolding Func_def mem_Collect_eq proof(intro conjI allI ballI)
  fix b2 show "Func_map B2 f1 f2 g b2 \<noteq> None \<longleftrightarrow> b2 \<in> B2"
  proof(cases "b2 \<in> B2")
    case True
    hence "f2 b2 \<in> A2" using f2 by auto
    then obtain a1 where "g (f2 b2) = Some a1" and "a1 \<in> A1"
    using g unfolding Func_def by(cases "g (f2 b2)", fastforce+)
    thus ?thesis unfolding Func_map_def using True by auto
  qed(unfold Func_map_def, auto)
next
  fix b2 assume b2: "b2 \<in> B2"
  hence "f2 b2 \<in> A2" using f2 by auto
  then obtain a1 where "g (f2 b2) = Some a1" and "a1 \<in> A1"
  using g unfolding Func_def by(cases "g (f2 b2)", fastforce+)
  thus "case Func_map B2 f1 f2 g b2 of None \<Rightarrow> True | Some b1 \<Rightarrow> b1 \<in> B1"
  unfolding Func_map_def using b2 f1 by auto
qed

lemma Func_map_empty:
"Func_map B2 f1 f2 empty = empty"
unfolding Func_map_def[abs_def] by (rule ext, auto)

lemma Func_non_emp:
assumes "B \<noteq> {}"
shows "Func A B \<noteq> {}"
proof-
  obtain b where b: "b \<in> B" using assms by auto
  hence "(\<lambda> a. if a \<in> A then Some b else None) \<in> Func A B"
  unfolding Func_def by auto
  thus ?thesis by blast
qed

lemma Func_is_emp:
"Func A B = {} \<longleftrightarrow> A \<noteq> {} \<and> B = {}" (is "?L \<longleftrightarrow> ?R")
proof
  assume L: ?L
  moreover {assume "A = {}" hence False using L Func_empty by auto}
  moreover {assume "B \<noteq> {}" hence False using L Func_non_emp by metis}
  ultimately show ?R by blast
next
  assume R: ?R
  moreover
  {fix f assume "f \<in> Func A B"
   moreover obtain a where "a \<in> A" using R by blast
   ultimately obtain b where "b \<in> B" unfolding Func_def by(cases "f a", force+)
   with R have False by auto
  }
  thus ?L by blast
qed

lemma Func_map_surj:
assumes B1: "f1 ` A1 = B1" and A2: "inj_on f2 B2" "f2 ` B2 \<subseteq> A2"
and B2A2: "B2 = {} \<Longrightarrow> A2 = {}"
shows "Func B2 B1 = Func_map B2 f1 f2 ` Func A2 A1"
proof(cases "B2 = {}")
  case True
  thus ?thesis using B2A2 by (auto simp: Func_empty Func_map_empty)
next
  case False note B2 = False
  show ?thesis
proof safe
  fix h assume h: "h \<in> Func B2 B1"
  def j1 \<equiv> "inv_into A1 f1"
  have "\<forall> a2 \<in> f2 ` B2. \<exists> b2. b2 \<in> B2 \<and> f2 b2 = a2" by blast
  then obtain k where k: "\<forall> a2 \<in> f2 ` B2. k a2 \<in> B2 \<and> f2 (k a2) = a2" by metis
  {fix b2 assume b2: "b2 \<in> B2"
   hence "f2 (k (f2 b2)) = f2 b2" using k A2(2) by auto
   moreover have "k (f2 b2) \<in> B2" using b2 A2(2) k by auto
   ultimately have "k (f2 b2) = b2" using b2 A2(1) unfolding inj_on_def by blast
  } note kk = this
  obtain b22 where b22: "b22 \<in> B2" using B2 by auto
  def j2 \<equiv> "\<lambda> a2. if a2 \<in> f2 ` B2 then k a2 else b22"
  have j2A2: "j2 ` A2 \<subseteq> B2" unfolding j2_def using k b22 by auto
  have j2: "\<And> b2. b2 \<in> B2 \<Longrightarrow> j2 (f2 b2) = b2"
  using kk unfolding j2_def by auto
  def g \<equiv> "Func_map A2 j1 j2 h"
  have "Func_map B2 f1 f2 g = h"
  proof (rule ext)
    fix b2 show "Func_map B2 f1 f2 g b2 = h b2"
    proof(cases "b2 \<in> B2")
      case True
      show ?thesis
      proof (cases "h b2")
        case (Some b1)
        hence b1: "b1 \<in> f1 ` A1" using True h unfolding B1 Func_def by auto
        show ?thesis
        using Some True A2 f_inv_into_f[OF b1]
        unfolding g_def Func_map_def j1_def j2[OF True] by auto
      qed(insert A2 True j2[OF True], unfold g_def Func_map_def, auto)
    qed(insert h, unfold Func_def Func_map_def, auto)
  qed
  moreover have "g \<in> Func A2 A1" unfolding g_def apply(rule Func_map[OF h])
  using inv_into_into j2A2 B1 A2 inv_into_into
  unfolding j1_def image_def by(force, force)
  ultimately show "h \<in> Func_map B2 f1 f2 ` Func A2 A1"
  unfolding Func_map_def[abs_def] unfolding image_def by auto
qed(insert B1 Func_map[OF _ _ A2(2)], auto)
qed

(* partial-function space: *)
definition Pfunc where
"Pfunc A B \<equiv>
 {f. (\<forall>a. f a \<noteq> None \<longrightarrow> a \<in> A) \<and>
     (\<forall>a. case f a of None \<Rightarrow> True | Some b \<Rightarrow> b \<in> B)}"

lemma Func_Pfunc:
"Func A B \<subseteq> Pfunc A B"
unfolding Func_def Pfunc_def by auto

lemma Pfunc_Func:
"Pfunc A B = (\<Union> A' \<in> Pow A. Func A' B)"
proof safe
  fix f assume f: "f \<in> Pfunc A B"
  show "f \<in> (\<Union>A'\<in>Pow A. Func A' B)"
  proof (intro UN_I)
    let ?A' = "{a. f a \<noteq> None}"
    show "?A' \<in> Pow A" using f unfolding Pow_def Pfunc_def by auto
    show "f \<in> Func ?A' B" using f unfolding Func_def Pfunc_def by auto
  qed
next
  fix f A' assume "f \<in> Func A' B" and "A' \<subseteq> A"
  thus "f \<in> Pfunc A B" unfolding Func_def Pfunc_def by auto
qed

lemma card_of_Pow_Func:
"|Pow A| =o |Func A (UNIV::bool set)|"
proof-
  def F \<equiv> "\<lambda> A' a. if a \<in> A then (if a \<in> A' then Some True else Some False)
                            else None"
  have "bij_betw F (Pow A) (Func A (UNIV::bool set))"
  unfolding bij_betw_def inj_on_def proof (intro ballI impI conjI)
    fix A1 A2 assume A1: "A1 \<in> Pow A" and A2: "A2 \<in> Pow A" and eq: "F A1 = F A2"
    show "A1 = A2"
    proof-
      {fix a
       have "a \<in> A1 \<longleftrightarrow> F A1 a = Some True" using A1 unfolding F_def Pow_def by auto
       also have "... \<longleftrightarrow> F A2 a = Some True" unfolding eq ..
       also have "... \<longleftrightarrow> a \<in> A2" using A2 unfolding F_def Pow_def by auto
       finally have "a \<in> A1 \<longleftrightarrow> a \<in> A2" .
      }
      thus ?thesis by auto
    qed
  next
    show "F ` Pow A = Func A UNIV"
    proof safe
      fix f assume f: "f \<in> Func A (UNIV::bool set)"
      show "f \<in> F ` Pow A" unfolding image_def mem_Collect_eq proof(intro bexI)
        let ?A1 = "{a \<in> A. f a = Some True}"
        show "f = F ?A1" unfolding F_def apply(rule ext)
        using f unfolding Func_def mem_Collect_eq by (auto,force)
      qed auto
    qed(unfold Func_def mem_Collect_eq F_def, auto)
  qed
  thus ?thesis unfolding card_of_ordIso[symmetric] by blast
qed

lemma card_of_Func_mono:
fixes A1 A2 :: "'a set" and B :: "'b set"
assumes A12: "A1 \<subseteq> A2" and B: "B \<noteq> {}"
shows "|Func A1 B| \<le>o |Func A2 B|"
proof-
  obtain bb where bb: "bb \<in> B" using B by auto
  def F \<equiv> "\<lambda> (f1::'a \<Rightarrow> 'b option) a. if a \<in> A2 then (if a \<in> A1 then f1 a else Some bb)
                                                else None"
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

lemma card_of_Pfunc_Pow_Func:
assumes "B \<noteq> {}"
shows "|Pfunc A B| \<le>o |Pow A <*> Func A B|"
proof-
  have "|Pfunc A B| =o |\<Union> A' \<in> Pow A. Func A' B|" (is "_ =o ?K")
  unfolding Pfunc_Func by(rule card_of_refl)
  also have "?K \<le>o |Sigma (Pow A) (\<lambda> A'. Func A' B)|" using card_of_UNION_Sigma .
  also have "|Sigma (Pow A) (\<lambda> A'. Func A' B)| \<le>o |Pow A <*> Func A B|"
  apply(rule card_of_Sigma_mono1) using card_of_Func_mono[OF _ assms] by auto
  finally show ?thesis .
qed

lemma ordLeq_Func:
assumes "{b1,b2} \<subseteq> B" "b1 \<noteq> b2"
shows "|A| \<le>o |Func A B|"
unfolding card_of_ordLeq[symmetric] proof(intro exI conjI)
  let ?F = "\<lambda> aa a. if a \<in> A then (if a = aa then Some b1 else Some b2)
                             else None"
  show "inj_on ?F A" using assms unfolding inj_on_def fun_eq_iff by auto
  show "?F ` A \<subseteq> Func A B" using assms unfolding Func_def apply auto
  by (metis option.simps(3))
qed

lemma infinite_Func:
assumes A: "infinite A" and B: "{b1,b2} \<subseteq> B" "b1 \<noteq> b2"
shows "infinite (Func A B)"
using ordLeq_Func[OF B] by (metis A card_of_ordLeq_finite)

(* alternative function space avoiding the option type, with undefined instead of None *)
definition Ffunc where
"Ffunc A B = {f . (\<forall> a \<in> A. f a \<in> B) \<and> (\<forall> a. a \<notin> A \<longrightarrow> f a = undefined)}"

lemma card_of_Func_Ffunc:
"|Ffunc A B| =o |Func A B|"
unfolding card_of_ordIso[symmetric] proof
  let ?F = "\<lambda> f a. if a \<in> A then Some (f a) else None"
  show "bij_betw ?F (Ffunc A B) (Func A B)"
  unfolding bij_betw_def unfolding inj_on_def proof(intro conjI ballI impI)
    fix f g assume f: "f \<in> Ffunc A B" and g: "g \<in> Ffunc A B" and eq: "?F f = ?F g"
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
      qed(insert f g, unfold Ffunc_def, auto)
    qed
  next
    show "?F ` Ffunc A B = Func A B"
    proof safe
      fix f assume f: "f \<in> Func A B"
      def g \<equiv> "\<lambda> a. case f a of Some b \<Rightarrow> b | None \<Rightarrow> undefined"
      have "g \<in> Ffunc A B"
      using f unfolding g_def Func_def Ffunc_def by force+
      moreover have "f = ?F g"
      proof(rule ext)
        fix a show "f a = ?F g a"
        using f unfolding Func_def g_def by (cases "a \<in> A") force+
      qed
      ultimately show "f \<in> ?F ` (Ffunc A B)" by blast
    qed(unfold Ffunc_def Func_def, auto)
  qed
qed

lemma card_of_Func_UNIV:
"|Func (UNIV::'a set) (B::'b set)| =o |{f::'a \<Rightarrow> 'b. range f \<subseteq> B}|"
apply(rule ordIso_symmetric) proof(intro card_of_ordIsoI)
  let ?F = "\<lambda> f (a::'a). Some ((f a)::'b)"
  show "bij_betw ?F {f. range f \<subseteq> B} (Func UNIV B)"
  unfolding bij_betw_def inj_on_def proof safe
    fix h :: "'a \<Rightarrow> 'b option" assume h: "h \<in> Func UNIV B"
    hence "\<forall> a. \<exists> b. h a = Some b" unfolding Func_def by auto
    then obtain f where f: "\<forall> a. h a = Some (f a)" by metis
    hence "range f \<subseteq> B" using h unfolding Func_def by auto
    thus "h \<in> (\<lambda>f a. Some (f a)) ` {f. range f \<subseteq> B}" using f unfolding image_def by auto
  qed(unfold Func_def fun_eq_iff, auto)
qed

end
