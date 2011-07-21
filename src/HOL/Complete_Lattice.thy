(*  Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel; Florian Haftmann, TU Muenchen *)

header {* Complete lattices, with special focus on sets *}

theory Complete_Lattice
imports Set
begin

notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  top ("\<top>") and
  bot ("\<bottom>")


subsection {* Syntactic infimum and supremum operations *}

class Inf =
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)

class Sup =
  fixes Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)

subsection {* Abstract complete lattices *}

class complete_lattice = bounded_lattice + Inf + Sup +
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> x"
     and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>A \<sqsubseteq> z"
begin

lemma dual_complete_lattice:
  "class.complete_lattice Sup Inf (op \<ge>) (op >) sup inf \<top> \<bottom>"
  by (auto intro!: class.complete_lattice.intro dual_bounded_lattice)
    (unfold_locales, (fact bot_least top_greatest
        Sup_upper Sup_least Inf_lower Inf_greatest)+)

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<sqsubseteq> a}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<sqsubseteq> b}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Inf_empty [simp]:
  "\<Sqinter>{} = \<top>"
  by (auto intro: antisym Inf_greatest)

lemma Sup_empty [simp]:
  "\<Squnion>{} = \<bottom>"
  by (auto intro: antisym Sup_least)

lemma Inf_UNIV [simp]:
  "\<Sqinter>UNIV = \<bottom>"
  by (simp add: Sup_Inf Sup_empty [symmetric])

lemma Sup_UNIV [simp]:
  "\<Squnion>UNIV = \<top>"
  by (simp add: Inf_Sup Inf_empty [symmetric])

lemma Inf_insert: "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
  by (auto intro: le_infI le_infI1 le_infI2 antisym Inf_greatest Inf_lower)

lemma Sup_insert: "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
  by (auto intro: le_supI le_supI1 le_supI2 antisym Sup_least Sup_upper)

lemma Inf_singleton [simp]:
  "\<Sqinter>{a} = a"
  by (auto intro: antisym Inf_lower Inf_greatest)

lemma Sup_singleton [simp]:
  "\<Squnion>{a} = a"
  by (auto intro: antisym Sup_upper Sup_least)

lemma Inf_binary:
  "\<Sqinter>{a, b} = a \<sqinter> b"
  by (simp add: Inf_insert)

lemma Sup_binary:
  "\<Squnion>{a, b} = a \<squnion> b"
  by (simp add: Sup_insert)

lemma le_Inf_iff: "b \<sqsubseteq> \<Sqinter>A \<longleftrightarrow> (\<forall>a\<in>A. b \<sqsubseteq> a)"
  by (auto intro: Inf_greatest dest: Inf_lower)

lemma Sup_le_iff: "\<Squnion>A \<sqsubseteq> b \<longleftrightarrow> (\<forall>a\<in>A. a \<sqsubseteq> b)"
  by (auto intro: Sup_least dest: Sup_upper)

lemma Inf_superset_mono: "B \<subseteq> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> \<Sqinter>B"
  by (auto intro: Inf_greatest Inf_lower)

lemma Sup_subset_mono: "A \<subseteq> B \<Longrightarrow> \<Squnion>A \<sqsubseteq> \<Squnion>B"
  by (auto intro: Sup_least Sup_upper)

lemma Inf_mono:
  assumes "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<sqsubseteq> b"
  shows "\<Sqinter>A \<sqsubseteq> \<Sqinter>B"
proof (rule Inf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<sqsubseteq> b" by blast
  from `a \<in> A` have "\<Sqinter>A \<sqsubseteq> a" by (rule Inf_lower)
  with `a \<sqsubseteq> b` show "\<Sqinter>A \<sqsubseteq> b" by auto
qed

lemma Sup_mono:
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<sqsubseteq> b"
  shows "\<Squnion>A \<sqsubseteq> \<Squnion>B"
proof (rule Sup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<sqsubseteq> b" by blast
  from `b \<in> B` have "b \<sqsubseteq> \<Squnion>B" by (rule Sup_upper)
  with `a \<sqsubseteq> b` show "a \<sqsubseteq> \<Squnion>B" by auto
qed

lemma Sup_upper2: "u \<in> A \<Longrightarrow> v \<sqsubseteq> u \<Longrightarrow> v \<sqsubseteq> \<Squnion>A"
  using Sup_upper [of u A] by auto

lemma Inf_lower2: "u \<in> A \<Longrightarrow> u \<sqsubseteq> v \<Longrightarrow> \<Sqinter>A \<sqsubseteq> v"
  using Inf_lower [of u A] by auto

lemma Inf_less_eq:
  assumes "\<And>v. v \<in> A \<Longrightarrow> v \<sqsubseteq> u"
    and "A \<noteq> {}"
  shows "\<Sqinter>A \<sqsubseteq> u"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "v \<sqsubseteq> u" by blast
  ultimately show ?thesis by (rule Inf_lower2)
qed

lemma less_eq_Sup:
  assumes "\<And>v. v \<in> A \<Longrightarrow> u \<sqsubseteq> v"
    and "A \<noteq> {}"
  shows "u \<sqsubseteq> \<Squnion>A"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "u \<sqsubseteq> v" by blast
  ultimately show ?thesis by (rule Sup_upper2)
qed

lemma less_eq_Inf_inter: "\<Sqinter>A \<squnion> \<Sqinter>B \<sqsubseteq> \<Sqinter>(A \<inter> B)"
  by (auto intro: Inf_greatest Inf_lower)

lemma Sup_inter_less_eq: "\<Squnion>(A \<inter> B) \<sqsubseteq> \<Squnion>A \<sqinter> \<Squnion>B "
  by (auto intro: Sup_least Sup_upper)

lemma Inf_union_distrib: "\<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
  by (rule antisym) (auto intro: Inf_greatest Inf_lower le_infI1 le_infI2)

lemma Sup_union_distrib: "\<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
  by (rule antisym) (auto intro: Sup_least Sup_upper le_supI1 le_supI2)

lemma Inf_top_conv [no_atp]:
  "\<Sqinter>A = \<top> \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)"
  "\<top> = \<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)"
proof -
  show "\<Sqinter>A = \<top> \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)"
  proof
    assume "\<forall>x\<in>A. x = \<top>"
    then have "A = {} \<or> A = {\<top>}" by auto
    then show "\<Sqinter>A = \<top>" by auto
  next
    assume "\<Sqinter>A = \<top>"
    show "\<forall>x\<in>A. x = \<top>"
    proof (rule ccontr)
      assume "\<not> (\<forall>x\<in>A. x = \<top>)"
      then obtain x where "x \<in> A" and "x \<noteq> \<top>" by blast
      then obtain B where "A = insert x B" by blast
      with `\<Sqinter>A = \<top>` `x \<noteq> \<top>` show False by (simp add: Inf_insert)
    qed
  qed
  then show "\<top> = \<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)" by auto
qed

lemma Sup_bot_conv [no_atp]:
  "\<Squnion>A = \<bottom> \<longleftrightarrow> (\<forall>x\<in>A. x = \<bottom>)" (is ?P)
  "\<bottom> = \<Squnion>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<bottom>)" (is ?Q)
proof -
  interpret dual: complete_lattice Sup Inf "op \<ge>" "op >" sup inf \<top> \<bottom>
    by (fact dual_complete_lattice)
  from dual.Inf_top_conv show ?P and ?Q by simp_all
qed

definition INFI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  INF_def: "INFI A f = \<Sqinter> (f ` A)"

definition SUPR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  SUP_def: "SUPR A f = \<Squnion> (f ` A)"

text {*
  Note: must use names @{const INFI} and @{const SUPR} here instead of
  @{text INF} and @{text SUP} to allow the following syntax coexist
  with the plain constant names.
*}

end

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3INF _:_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3SUP _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI CONST UNIV (%x. B)"
  "INF x. B"     == "INF x:CONST UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR CONST UNIV (%x. B)"
  "SUP x. B"     == "SUP x:CONST UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax INFI} @{syntax_const "_INF"},
    Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax SUPR} @{syntax_const "_SUP"}]
*} -- {* to avoid eta-contraction of body *}

context complete_lattice
begin

lemma INF_empty: "(\<Sqinter>x\<in>{}. f x) = \<top>"
  by (simp add: INF_def)

lemma SUP_empty: "(\<Squnion>x\<in>{}. f x) = \<bottom>"
  by (simp add: SUP_def)

lemma INF_insert: "(\<Sqinter>x\<in>insert a A. f x) = f a \<sqinter> INFI A f"
  by (simp add: INF_def Inf_insert)

lemma SUP_insert: "(\<Squnion>x\<in>insert a A. f x) = f a \<squnion> SUPR A f"
  by (simp add: SUP_def Sup_insert)

lemma INF_leI: "i \<in> A \<Longrightarrow> (\<Sqinter>i\<in>A. f i) \<sqsubseteq> f i"
  by (auto simp add: INF_def intro: Inf_lower)

lemma le_SUP_I: "i \<in> A \<Longrightarrow> f i \<sqsubseteq> (\<Squnion>i\<in>A. f i)"
  by (auto simp add: SUP_def intro: Sup_upper)

lemma INF_leI2: "i \<in> A \<Longrightarrow> f i \<sqsubseteq> u \<Longrightarrow> (\<Sqinter>i\<in>A. f i) \<sqsubseteq> u"
  using INF_leI [of i A f] by auto

lemma le_SUP_I2: "i \<in> A \<Longrightarrow> u \<sqsubseteq> f i \<Longrightarrow> u \<sqsubseteq> (\<Squnion>i\<in>A. f i)"
  using le_SUP_I [of i A f] by auto

lemma le_INF_I: "(\<And>i. i \<in> A \<Longrightarrow> u \<sqsubseteq> f i) \<Longrightarrow> u \<sqsubseteq> (\<Sqinter>i\<in>A. f i)"
  by (auto simp add: INF_def intro: Inf_greatest)

lemma SUP_leI: "(\<And>i. i \<in> A \<Longrightarrow> f i \<sqsubseteq> u) \<Longrightarrow> (\<Squnion>i\<in>A. f i) \<sqsubseteq> u"
  by (auto simp add: SUP_def intro: Sup_least)

lemma le_INF_iff: "u \<sqsubseteq> (\<Sqinter>i\<in>A. f i) \<longleftrightarrow> (\<forall>i \<in> A. u \<sqsubseteq> f i)"
  by (auto simp add: INF_def le_Inf_iff)

lemma SUP_le_iff: "(\<Squnion>i\<in>A. f i) \<sqsubseteq> u \<longleftrightarrow> (\<forall>i \<in> A. f i \<sqsubseteq> u)"
  by (auto simp add: SUP_def Sup_le_iff)

lemma INF_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter>i\<in>A. f) = f"
  by (auto intro: antisym INF_leI le_INF_I)

lemma SUP_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion>i\<in>A. f) = f"
  by (auto intro: antisym SUP_leI le_SUP_I)

lemma INF_top: "(\<Sqinter>x\<in>A. \<top>) = \<top>"
  by (cases "A = {}") (simp_all add: INF_empty)

lemma SUP_bot: "(\<Squnion>x\<in>A. \<bottom>) = \<bottom>"
  by (cases "A = {}") (simp_all add: SUP_empty)

lemma INF_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Sqinter>x\<in>A. C x) = (\<Sqinter>x\<in>B. D x)"
  by (simp add: INF_def image_def)

lemma SUP_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Squnion>x\<in>A. C x) = (\<Squnion>x\<in>B. D x)"
  by (simp add: SUP_def image_def)

lemma INF_mono:
  "(\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Sqinter>n\<in>A. f n) \<sqsubseteq> (\<Sqinter>n\<in>B. g n)"
  by (force intro!: Inf_mono simp: INF_def)

lemma SUP_mono:
  "(\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Squnion>n\<in>A. f n) \<sqsubseteq> (\<Squnion>n\<in>B. g n)"
  by (force intro!: Sup_mono simp: SUP_def)

lemma INF_superset_mono:
  "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<sqsubseteq> g x) \<Longrightarrow> (\<Sqinter>x\<in>A. f x) \<sqsubseteq> (\<Sqinter>x\<in>B. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (blast intro: INF_mono dest: subsetD)

lemma SUP_subset_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<sqsubseteq> g x) \<Longrightarrow> (\<Squnion>x\<in>A. f x) \<sqsubseteq> (\<Squnion>x\<in>B. g x)"
  by (blast intro: SUP_mono dest: subsetD)

lemma INF_commute: "(\<Sqinter>i\<in>A. \<Sqinter>j\<in>B. f i j) = (\<Sqinter>j\<in>B. \<Sqinter>i\<in>A. f i j)"
  by (iprover intro: INF_leI le_INF_I order_trans antisym)

lemma SUP_commute: "(\<Squnion>i\<in>A. \<Squnion>j\<in>B. f i j) = (\<Squnion>j\<in>B. \<Squnion>i\<in>A. f i j)"
  by (iprover intro: SUP_leI le_SUP_I order_trans antisym)

lemma INF_absorb:
  assumes "k \<in> I"
  shows "A k \<sqinter> (\<Sqinter>i\<in>I. A i) = (\<Sqinter>i\<in>I. A i)"
proof -
  from assms obtain J where "I = insert k J" by blast
  then show ?thesis by (simp add: INF_insert)
qed

lemma SUP_absorb:
  assumes "k \<in> I"
  shows "A k \<squnion> (\<Squnion>i\<in>I. A i) = (\<Squnion>i\<in>I. A i)"
proof -
  from assms obtain J where "I = insert k J" by blast
  then show ?thesis by (simp add: SUP_insert)
qed

lemma INF_union:
  "(\<Sqinter>i \<in> A \<union> B. M i) = (\<Sqinter>i \<in> A. M i) \<sqinter> (\<Sqinter>i\<in>B. M i)"
  by (auto intro!: antisym INF_mono intro: le_infI1 le_infI2 le_INF_I INF_leI)

lemma SUP_union:
  "(\<Squnion>i \<in> A \<union> B. M i) = (\<Squnion>i \<in> A. M i) \<squnion> (\<Squnion>i\<in>B. M i)"
  by (auto intro!: antisym SUP_mono intro: le_supI1 le_supI2 SUP_leI le_SUP_I)

lemma INF_constant:
  "(\<Sqinter>y\<in>A. c) = (if A = {} then \<top> else c)"
  by (simp add: INF_empty)

lemma SUP_constant:
  "(\<Squnion>y\<in>A. c) = (if A = {} then \<bottom> else c)"
  by (simp add: SUP_empty)

lemma INF_eq:
  "(\<Sqinter>x\<in>A. B x) = \<Sqinter>({Y. \<exists>x\<in>A. Y = B x})"
  by (simp add: INF_def image_def)

lemma SUP_eq:
  "(\<Squnion>x\<in>A. B x) = \<Squnion>({Y. \<exists>x\<in>A. Y = B x})"
  by (simp add: SUP_def image_def)

lemma INF_top_conv:
 "\<top> = (\<Sqinter>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = \<top>)"
 "(\<Sqinter>x\<in>A. B x) = \<top> \<longleftrightarrow> (\<forall>x\<in>A. B x = \<top>)"
  by (auto simp add: INF_def Inf_top_conv)

lemma SUP_bot_conv:
 "\<bottom> = (\<Squnion>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = \<bottom>)"
 "(\<Squnion>x\<in>A. B x) = \<bottom> \<longleftrightarrow> (\<forall>x\<in>A. B x = \<bottom>)"
  by (auto simp add: SUP_def Sup_bot_conv)

lemma INF_UNIV_range:
  "(\<Sqinter>x. f x) = \<Sqinter>range f"
  by (fact INF_def)

lemma SUP_UNIV_range:
  "(\<Squnion>x. f x) = \<Squnion>range f"
  by (fact SUP_def)

lemma INF_UNIV_bool_expand:
  "(\<Sqinter>b. A b) = A True \<sqinter> A False"
  by (simp add: UNIV_bool INF_empty INF_insert inf_commute)

lemma SUP_UNIV_bool_expand:
  "(\<Squnion>b. A b) = A True \<squnion> A False"
  by (simp add: UNIV_bool SUP_empty SUP_insert sup_commute)

end

class complete_boolean_algebra = boolean_algebra + complete_lattice
begin

lemma uminus_Inf:
  "- (\<Sqinter>A) = \<Squnion>(uminus ` A)"
proof (rule antisym)
  show "- \<Sqinter>A \<le> \<Squnion>(uminus ` A)"
    by (rule compl_le_swap2, rule Inf_greatest, rule compl_le_swap2, rule Sup_upper) simp
  show "\<Squnion>(uminus ` A) \<le> - \<Sqinter>A"
    by (rule Sup_least, rule compl_le_swap1, rule Inf_lower) auto
qed

lemma uminus_Sup:
  "- (\<Squnion>A) = \<Sqinter>(uminus ` A)"
proof -
  have "\<Squnion>A = - \<Sqinter>(uminus ` A)" by (simp add: image_image uminus_Inf)
  then show ?thesis by simp
qed
  
lemma uminus_INF: "- (\<Sqinter>x\<in>A. B x) = (\<Squnion>x\<in>A. - B x)"
  by (simp add: INF_def SUP_def uminus_Inf image_image)

lemma uminus_SUP: "- (\<Squnion>x\<in>A. B x) = (\<Sqinter>x\<in>A. - B x)"
  by (simp add: INF_def SUP_def uminus_Sup image_image)

end

class complete_linorder = linorder + complete_lattice
begin

lemma Inf_less_iff:
  "\<Sqinter>S \<sqsubset> a \<longleftrightarrow> (\<exists>x\<in>S. x \<sqsubset> a)"
  unfolding not_le [symmetric] le_Inf_iff by auto

lemma less_Sup_iff:
  "a \<sqsubset> \<Squnion>S \<longleftrightarrow> (\<exists>x\<in>S. a \<sqsubset> x)"
  unfolding not_le [symmetric] Sup_le_iff by auto

lemma INF_less_iff:
  "(\<Sqinter>i\<in>A. f i) \<sqsubset> a \<longleftrightarrow> (\<exists>x\<in>A. f x \<sqsubset> a)"
  unfolding INF_def Inf_less_iff by auto

lemma less_SUP_iff:
  "a \<sqsubset> (\<Squnion>i\<in>A. f i) \<longleftrightarrow> (\<exists>x\<in>A. a \<sqsubset> f x)"
  unfolding SUP_def less_Sup_iff by auto

end


subsection {* @{typ bool} and @{typ "_ \<Rightarrow> _"} as complete lattice *}

instantiation bool :: complete_boolean_algebra
begin

definition
  "\<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x)"

definition
  "\<Squnion>A \<longleftrightarrow> (\<exists>x\<in>A. x)"

instance proof
qed (auto simp add: Inf_bool_def Sup_bool_def)

end

lemma INF_bool_eq [simp]:
  "INFI = Ball"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(\<Sqinter>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P x)"
    by (auto simp add: Ball_def INF_def Inf_bool_def)
qed

lemma SUP_bool_eq [simp]:
  "SUPR = Bex"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(\<Squnion>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>A. P x)"
    by (auto simp add: Bex_def SUP_def Sup_bool_def)
qed

instantiation "fun" :: (type, complete_lattice) complete_lattice
begin

definition
  "\<Sqinter>A = (\<lambda>x. \<Sqinter>{y. \<exists>f\<in>A. y = f x})"

lemma Inf_apply:
  "(\<Sqinter>A) x = \<Sqinter>{y. \<exists>f\<in>A. y = f x}"
  by (simp add: Inf_fun_def)

definition
  "\<Squnion>A = (\<lambda>x. \<Squnion>{y. \<exists>f\<in>A. y = f x})"

lemma Sup_apply:
  "(\<Squnion>A) x = \<Squnion>{y. \<exists>f\<in>A. y = f x}"
  by (simp add: Sup_fun_def)

instance proof
qed (auto simp add: le_fun_def Inf_apply Sup_apply
  intro: Inf_lower Sup_upper Inf_greatest Sup_least)

end

lemma INF_apply:
  "(\<Sqinter>y\<in>A. f y) x = (\<Sqinter>y\<in>A. f y x)"
  by (auto intro: arg_cong [of _ _ Inf] simp add: INF_def Inf_apply)

lemma SUP_apply:
  "(\<Squnion>y\<in>A. f y) x = (\<Squnion>y\<in>A. f y x)"
  by (auto intro: arg_cong [of _ _ Sup] simp add: SUP_def Sup_apply)

instance "fun" :: (type, complete_boolean_algebra) complete_boolean_algebra ..


subsection {* Inter *}

abbreviation Inter :: "'a set set \<Rightarrow> 'a set" where
  "Inter S \<equiv> \<Sqinter>S"
  
notation (xsymbols)
  Inter  ("\<Inter>_" [90] 90)

lemma Inter_eq:
  "\<Inter>A = {x. \<forall>B \<in> A. x \<in> B}"
proof (rule set_eqI)
  fix x
  have "(\<forall>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<forall>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Inter>A \<longleftrightarrow> x \<in> {x. \<forall>B \<in> A. x \<in> B}"
    by (simp add: Inf_fun_def Inf_bool_def) (simp add: mem_def)
qed

lemma Inter_iff [simp,no_atp]: "A \<in> \<Inter>C \<longleftrightarrow> (\<forall>X\<in>C. A \<in> X)"
  by (unfold Inter_eq) blast

lemma InterI [intro!]: "(\<And>X. X \<in> C \<Longrightarrow> A \<in> X) \<Longrightarrow> A \<in> \<Inter>C"
  by (simp add: Inter_eq)

text {*
  \medskip A ``destruct'' rule -- every @{term X} in @{term C}
  contains @{term A} as an element, but @{prop "A \<in> X"} can hold when
  @{prop "X \<in> C"} does not!  This rule is analogous to @{text spec}.
*}

lemma InterD [elim, Pure.elim]: "A \<in> \<Inter>C \<Longrightarrow> X \<in> C \<Longrightarrow> A \<in> X"
  by auto

lemma InterE [elim]: "A \<in> \<Inter>C \<Longrightarrow> (X \<notin> C \<Longrightarrow> R) \<Longrightarrow> (A \<in> X \<Longrightarrow> R) \<Longrightarrow> R"
  -- {* ``Classical'' elimination rule -- does not require proving
    @{prop "X \<in> C"}. *}
  by (unfold Inter_eq) blast

lemma Inter_lower: "B \<in> A \<Longrightarrow> \<Inter>A \<subseteq> B"
  by (fact Inf_lower)

lemma Inter_subset:
  "(\<And>X. X \<in> A \<Longrightarrow> X \<subseteq> B) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter>A \<subseteq> B"
  by (fact Inf_less_eq)

lemma Inter_greatest: "(\<And>X. X \<in> A \<Longrightarrow> C \<subseteq> X) \<Longrightarrow> C \<subseteq> Inter A"
  by (fact Inf_greatest)

lemma Int_eq_Inter: "A \<inter> B = \<Inter>{A, B}"
  by (fact Inf_binary [symmetric])

lemma Inter_empty [simp]: "\<Inter>{} = UNIV"
  by (fact Inf_empty)

lemma Inter_UNIV [simp]: "\<Inter>UNIV = {}"
  by (fact Inf_UNIV)

lemma Inter_insert [simp]: "\<Inter>(insert a B) = a \<inter> \<Inter>B"
  by (fact Inf_insert)

lemma Inter_Un_subset: "\<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by (fact less_eq_Inf_inter)

lemma Inter_Un_distrib: "\<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by (fact Inf_union_distrib)

lemma Inter_UNIV_conv [simp, no_atp]:
  "\<Inter>A = UNIV \<longleftrightarrow> (\<forall>x\<in>A. x = UNIV)"
  "UNIV = \<Inter>A \<longleftrightarrow> (\<forall>x\<in>A. x = UNIV)"
  by (fact Inf_top_conv)+

lemma Inter_anti_mono: "B \<subseteq> A \<Longrightarrow> \<Inter>A \<subseteq> \<Inter>B"
  by (fact Inf_superset_mono)


subsection {* Intersections of families *}

abbreviation INTER :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "INTER \<equiv> INFI"

text {*
  Note: must use name @{const INTER} here instead of @{text INT}
  to allow the following syntax coexist with the plain constant name.
*}

syntax
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3INT _./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3INT _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>_./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 0, 10] 10)

syntax (latex output)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

translations
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "CONST INTER CONST UNIV (%x. B)"
  "INT x. B"    == "INT x:CONST UNIV. B"
  "INT x:A. B"  == "CONST INTER A (%x. B)"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax INTER} @{syntax_const "_INTER"}]
*} -- {* to avoid eta-contraction of body *}

lemma INTER_eq_Inter_image:
  "(\<Inter>x\<in>A. B x) = \<Inter>(B`A)"
  by (fact INF_def)
  
lemma Inter_def:
  "\<Inter>S = (\<Inter>x\<in>S. x)"
  by (simp add: INTER_eq_Inter_image image_def)

lemma INTER_def:
  "(\<Inter>x\<in>A. B x) = {y. \<forall>x\<in>A. y \<in> B x}"
  by (auto simp add: INTER_eq_Inter_image Inter_eq)

lemma Inter_image_eq [simp]:
  "\<Inter>(B`A) = (\<Inter>x\<in>A. B x)"
  by (rule sym) (fact INF_def)

lemma INT_iff [simp]: "b \<in> (\<Inter>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. b \<in> B x)"
  by (unfold INTER_def) blast

lemma INT_I [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> b \<in> B x) \<Longrightarrow> b \<in> (\<Inter>x\<in>A. B x)"
  by (unfold INTER_def) blast

lemma INT_D [elim, Pure.elim]: "b \<in> (\<Inter>x\<in>A. B x) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B a"
  by auto

lemma INT_E [elim]: "b \<in> (\<Inter>x\<in>A. B x) \<Longrightarrow> (b \<in> B a \<Longrightarrow> R) \<Longrightarrow> (a \<notin> A \<Longrightarrow> R) \<Longrightarrow> R"
  -- {* "Classical" elimination -- by the Excluded Middle on @{prop "a\<in>A"}. *}
  by (unfold INTER_def) blast

lemma INT_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Inter>x\<in>A. C x) = (\<Inter>x\<in>B. D x)"
  by (fact INF_cong)

lemma Collect_ball_eq: "{x. \<forall>y\<in>A. P x y} = (\<Inter>y\<in>A. {x. P x y})"
  by blast

lemma Collect_all_eq: "{x. \<forall>y. P x y} = (\<Inter>y. {x. P x y})"
  by blast

lemma INT_lower: "a \<in> A \<Longrightarrow> (\<Inter>x\<in>A. B x) \<subseteq> B a"
  by (fact INF_leI)

lemma INT_greatest: "(\<And>x. x \<in> A \<Longrightarrow> C \<subseteq> B x) \<Longrightarrow> C \<subseteq> (\<Inter>x\<in>A. B x)"
  by (fact le_INF_I)

lemma INT_empty [simp]: "(\<Inter>x\<in>{}. B x) = UNIV"
  by (fact INF_empty)

lemma INT_absorb: "k \<in> I \<Longrightarrow> A k \<inter> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. A i)"
  by (fact INF_absorb)

lemma INT_subset_iff: "B \<subseteq> (\<Inter>i\<in>I. A i) \<longleftrightarrow> (\<forall>i\<in>I. B \<subseteq> A i)"
  by (fact le_INF_iff)

lemma INT_insert [simp]: "(\<Inter>x \<in> insert a A. B x) = B a \<inter> INTER A B"
  by (fact INF_insert)

lemma INT_Un: "(\<Inter>i \<in> A \<union> B. M i) = (\<Inter>i \<in> A. M i) \<inter> (\<Inter>i\<in>B. M i)"
  by (fact INF_union)

lemma INT_insert_distrib:
  "u \<in> A \<Longrightarrow> (\<Inter>x\<in>A. insert a (B x)) = insert a (\<Inter>x\<in>A. B x)"
  by blast

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A = {} then UNIV else c)"
  by (fact INF_constant)

lemma INT_eq: "(\<Inter>x\<in>A. B x) = \<Inter>({Y. \<exists>x\<in>A. Y = B x})"
  -- {* Look: it has an \emph{existential} quantifier *}
  by (fact INF_eq)

lemma INTER_UNIV_conv [simp]:
 "(UNIV = (\<Inter>x\<in>A. B x)) = (\<forall>x\<in>A. B x = UNIV)"
 "((\<Inter>x\<in>A. B x) = UNIV) = (\<forall>x\<in>A. B x = UNIV)"
  by (fact INF_top_conv)+

lemma INT_bool_eq: "(\<Inter>b. A b) = A True \<inter> A False"
  by (fact INF_UNIV_bool_expand)

lemma INT_anti_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> (\<Inter>x\<in>B. f x) \<subseteq> (\<Inter>x\<in>A. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (fact INF_superset_mono)

lemma Pow_INT_eq: "Pow (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. Pow (B x))"
  by blast

lemma vimage_INT: "f -` (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. f -` B x)"
  by blast


subsection {* Union *}

abbreviation Union :: "'a set set \<Rightarrow> 'a set" where
  "Union S \<equiv> \<Squnion>S"

notation (xsymbols)
  Union  ("\<Union>_" [90] 90)

lemma Union_eq:
  "\<Union>A = {x. \<exists>B \<in> A. x \<in> B}"
proof (rule set_eqI)
  fix x
  have "(\<exists>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<exists>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Union>A \<longleftrightarrow> x \<in> {x. \<exists>B\<in>A. x \<in> B}"
    by (simp add: Sup_fun_def Sup_bool_def) (simp add: mem_def)
qed

lemma Union_iff [simp, no_atp]:
  "A \<in> \<Union>C \<longleftrightarrow> (\<exists>X\<in>C. A\<in>X)"
  by (unfold Union_eq) blast

lemma UnionI [intro]:
  "X \<in> C \<Longrightarrow> A \<in> X \<Longrightarrow> A \<in> \<Union>C"
  -- {* The order of the premises presupposes that @{term C} is rigid;
    @{term A} may be flexible. *}
  by auto

lemma UnionE [elim!]:
  "A \<in> \<Union>C \<Longrightarrow> (\<And>X. A \<in> X \<Longrightarrow> X \<in> C \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma Union_upper: "B \<in> A \<Longrightarrow> B \<subseteq> \<Union>A"
  by (fact Sup_upper)

lemma Union_least: "(\<And>X. X \<in> A \<Longrightarrow> X \<subseteq> C) \<Longrightarrow> \<Union>A \<subseteq> C"
  by (fact Sup_least)

lemma Un_eq_Union: "A \<union> B = \<Union>{A, B}"
  by blast

lemma Union_empty [simp]: "\<Union>{} = {}"
  by (fact Sup_empty)

lemma Union_UNIV [simp]: "\<Union>UNIV = UNIV"
  by (fact Sup_UNIV)

lemma Union_insert [simp]: "\<Union>insert a B = a \<union> \<Union>B"
  by (fact Sup_insert)

lemma Union_Un_distrib [simp]: "\<Union>(A \<union> B) = \<Union>A \<union> \<Union>B"
  by (fact Sup_union_distrib)

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by (fact Sup_inter_less_eq)

lemma Union_empty_conv [simp,no_atp]: "(\<Union>A = {}) \<longleftrightarrow> (\<forall>x\<in>A. x = {})"
  by (fact Sup_bot_conv)

lemma empty_Union_conv [simp,no_atp]: "({} = \<Union>A) \<longleftrightarrow> (\<forall>x\<in>A. x = {})"
  by (fact Sup_bot_conv)

lemma Union_disjoint: "(\<Union>C \<inter> A = {}) \<longleftrightarrow> (\<forall>B\<in>C. B \<inter> A = {})" -- "FIXME generalize"
  by blast

lemma subset_Pow_Union: "A \<subseteq> Pow (\<Union>A)"
  by blast

lemma Union_Pow_eq [simp]: "\<Union>(Pow A) = A"
  by blast

lemma Union_mono: "A \<subseteq> B \<Longrightarrow> \<Union>A \<subseteq> \<Union>B"
  by (fact Sup_subset_mono)


subsection {* Unions of families *}

abbreviation UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "UNION \<equiv> SUPR"

text {*
  Note: must use name @{const UNION} here instead of @{text UN}
  to allow the following syntax coexist with the plain constant name.
*}

syntax
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3UN _./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3UN _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)

syntax (latex output)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

translations
  "UN x y. B"   == "UN x. UN y. B"
  "UN x. B"     == "CONST UNION CONST UNIV (%x. B)"
  "UN x. B"     == "UN x:CONST UNIV. B"
  "UN x:A. B"   == "CONST UNION A (%x. B)"

text {*
  Note the difference between ordinary xsymbol syntax of indexed
  unions and intersections (e.g.\ @{text"\<Union>a\<^isub>1\<in>A\<^isub>1. B"})
  and their \LaTeX\ rendition: @{term"\<Union>a\<^isub>1\<in>A\<^isub>1. B"}. The
  former does not make the index expression a subscript of the
  union/intersection symbol because this leads to problems with nested
  subscripts in Proof General.
*}

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax UNION} @{syntax_const "_UNION"}]
*} -- {* to avoid eta-contraction of body *}

lemma UNION_eq_Union_image:
  "(\<Union>x\<in>A. B x) = \<Union>(B ` A)"
  by (fact SUP_def)

lemma Union_def:
  "\<Union>S = (\<Union>x\<in>S. x)"
  by (simp add: UNION_eq_Union_image image_def)

lemma UNION_def [no_atp]:
  "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
  by (auto simp add: UNION_eq_Union_image Union_eq)
  
lemma Union_image_eq [simp]:
  "\<Union>(B ` A) = (\<Union>x\<in>A. B x)"
  by (rule sym) (fact UNION_eq_Union_image)
  
lemma UN_iff [simp]: "(b \<in> (\<Union>x\<in>A. B x)) = (\<exists>x\<in>A. b \<in> B x)"
  by (unfold UNION_def) blast

lemma UN_I [intro]: "a \<in> A \<Longrightarrow> b \<in> B a \<Longrightarrow> b \<in> (\<Union>x\<in>A. B x)"
  -- {* The order of the premises presupposes that @{term A} is rigid;
    @{term b} may be flexible. *}
  by auto

lemma UN_E [elim!]: "b \<in> (\<Union>x\<in>A. B x) \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> b \<in> B x \<Longrightarrow> R) \<Longrightarrow> R"
  by (unfold UNION_def) blast

lemma UN_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Union>x\<in>A. C x) = (\<Union>x\<in>B. D x)"
  by (fact SUP_cong)

lemma strong_UN_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B =simp=> C x = D x) \<Longrightarrow> (\<Union>x\<in>A. C x) = (\<Union>x\<in>B. D x)"
  by (unfold simp_implies_def) (fact UN_cong)

lemma image_eq_UN: "f ` A = (\<Union>x\<in>A. {f x})"
  by blast

lemma UN_upper: "a \<in> A \<Longrightarrow> B a \<subseteq> (\<Union>x\<in>A. B x)"
  by (fact le_SUP_I)

lemma UN_least: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C) \<Longrightarrow> (\<Union>x\<in>A. B x) \<subseteq> C"
  by (fact SUP_leI)

lemma Collect_bex_eq [no_atp]: "{x. \<exists>y\<in>A. P x y} = (\<Union>y\<in>A. {x. P x y})"
  by blast

lemma UN_insert_distrib: "u \<in> A \<Longrightarrow> (\<Union>x\<in>A. insert a (B x)) = insert a (\<Union>x\<in>A. B x)"
  by blast

lemma UN_empty [simp, no_atp]: "(\<Union>x\<in>{}. B x) = {}"
  by (fact SUP_empty)

lemma UN_empty2 [simp]: "(\<Union>x\<in>A. {}) = {}"
  by (fact SUP_bot)

lemma UN_singleton [simp]: "(\<Union>x\<in>A. {x}) = A"
  by blast

lemma UN_absorb: "k \<in> I \<Longrightarrow> A k \<union> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. A i)"
  by (fact SUP_absorb)

lemma UN_insert [simp]: "(\<Union>x\<in>insert a A. B x) = B a \<union> UNION A B"
  by (fact SUP_insert)

lemma UN_Un[simp]: "(\<Union>i \<in> A \<union> B. M i) = (\<Union>i\<in>A. M i) \<union> (\<Union>i\<in>B. M i)"
  by (fact SUP_union)

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B y). C x) = (\<Union>y\<in>A. \<Union>x\<in>B y. C x)" -- "FIXME generalize"
  by blast

lemma UN_subset_iff: "((\<Union>i\<in>I. A i) \<subseteq> B) = (\<forall>i\<in>I. A i \<subseteq> B)"
  by (fact SUP_le_iff)

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A = {} then {} else c)"
  by (fact SUP_constant)

lemma UN_eq: "(\<Union>x\<in>A. B x) = \<Union>({Y. \<exists>x\<in>A. Y = B x})"
  by (fact SUP_eq)

lemma image_Union: "f ` \<Union>S = (\<Union>x\<in>S. f ` x)" -- "FIXME generalize"
  by blast

lemma UNION_empty_conv[simp]:
  "{} = (\<Union>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = {})"
  "(\<Union>x\<in>A. B x) = {} \<longleftrightarrow> (\<forall>x\<in>A. B x = {})"
  by (fact SUP_bot_conv)+

lemma Collect_ex_eq [no_atp]: "{x. \<exists>y. P x y} = (\<Union>y. {x. P x y})"
  by blast

lemma ball_UN: "(\<forall>z \<in> UNION A B. P z) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>z \<in> B x. P z)"
  by blast

lemma bex_UN: "(\<exists>z \<in> UNION A B. P z) \<longleftrightarrow> (\<exists>x\<in>A. \<exists>z\<in>B x. P z)"
  by blast

lemma Un_eq_UN: "A \<union> B = (\<Union>b. if b then A else B)"
  by (auto simp add: split_if_mem2)

lemma UN_bool_eq: "(\<Union>b. A b) = (A True \<union> A False)"
  by (fact SUP_UNIV_bool_expand)

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow (B x)) \<subseteq> Pow (\<Union>x\<in>A. B x)"
  by blast

lemma UN_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow>
    (\<Union>x\<in>A. f x) \<subseteq> (\<Union>x\<in>B. g x)"
  by (fact SUP_subset_mono)

lemma vimage_Union: "f -` (\<Union>A) = (\<Union>X\<in>A. f -` X)"
  by blast

lemma vimage_UN: "f -` (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. f -` B x)"
  by blast

lemma vimage_eq_UN: "f -` B = (\<Union>y\<in>B. f -` {y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma image_UN: "f ` UNION A B = (\<Union>x\<in>A. f ` B x)"
  by blast


subsection {* Distributive laws *}

lemma Int_Union: "A \<inter> \<Union>B = (\<Union>C\<in>B. A \<inter> C)"
  by blast

lemma Int_Union2: "\<Union>B \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
  by blast

lemma Un_Union_image: "(\<Union>x\<in>C. A x \<union> B x) = \<Union>(A ` C) \<union> \<Union>(B ` C)"
  -- {* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: *}
  -- {* Union of a family of unions *}
  by blast

lemma UN_Un_distrib: "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Un_Inter: "A \<union> \<Inter>B = (\<Inter>C\<in>B. A \<union> C)"
  by blast

lemma Int_Inter_image: "(\<Inter>x\<in>C. A x \<inter> B x) = \<Inter>(A ` C) \<inter> \<Inter>(B ` C)"
  by blast

lemma INT_Int_distrib: "(\<Inter>i\<in>I. A i \<inter> B i) = (\<Inter>i\<in>I. A i) \<inter> (\<Inter>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Int_UN_distrib: "B \<inter> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. B \<inter> A i)"
  -- {* Halmos, Naive Set Theory, page 35. *}
  by blast

lemma Un_INT_distrib: "B \<union> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. B \<union> A i)"
  by blast

lemma Int_UN_distrib2: "(\<Union>i\<in>I. A i) \<inter> (\<Union>j\<in>J. B j) = (\<Union>i\<in>I. \<Union>j\<in>J. A i \<inter> B j)"
  by blast

lemma Un_INT_distrib2: "(\<Inter>i\<in>I. A i) \<union> (\<Inter>j\<in>J. B j) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A i \<union> B j)"
  by blast


subsection {* Complement *}

lemma Compl_INT [simp]: "- (\<Inter>x\<in>A. B x) = (\<Union>x\<in>A. -B x)"
  by (fact uminus_INF)

lemma Compl_UN [simp]: "- (\<Union>x\<in>A. B x) = (\<Inter>x\<in>A. -B x)"
  by (fact uminus_SUP)


subsection {* Miniscoping and maxiscoping *}

text {* \medskip Miniscoping: pushing in quantifiers and big Unions
           and Intersections. *}

lemma UN_simps [simp]:
  "\<And>a B C. (\<Union>x\<in>C. insert a (B x)) = (if C={} then {} else insert a (\<Union>x\<in>C. B x))"
  "\<And>A B C. (\<Union>x\<in>C. A x \<union>  B) = ((if C={} then {} else (\<Union>x\<in>C. A x) \<union> B))"
  "\<And>A B C. (\<Union>x\<in>C. A \<union> B x) = ((if C={} then {} else A \<union> (\<Union>x\<in>C. B x)))"
  "\<And>A B C. (\<Union>x\<in>C. A x \<inter> B) = ((\<Union>x\<in>C. A x) \<inter>B)"
  "\<And>A B C. (\<Union>x\<in>C. A \<inter> B x) = (A \<inter>(\<Union>x\<in>C. B x))"
  "\<And>A B C. (\<Union>x\<in>C. A x - B) = ((\<Union>x\<in>C. A x) - B)"
  "\<And>A B C. (\<Union>x\<in>C. A - B x) = (A - (\<Inter>x\<in>C. B x))"
  "\<And>A B. (\<Union>x\<in>\<Union>A. B x) = (\<Union>y\<in>A. \<Union>x\<in>y. B x)"
  "\<And>A B C. (\<Union>z\<in>UNION A B. C z) = (\<Union>x\<in>A. \<Union>z\<in>B x. C z)"
  "\<And>A B f. (\<Union>x\<in>f`A. B x) = (\<Union>a\<in>A. B (f a))"
  by auto

lemma INT_simps [simp]:
  "\<And>A B C. (\<Inter>x\<in>C. A x \<inter> B) = (if C={} then UNIV else (\<Inter>x\<in>C. A x) \<inter>B)"
  "\<And>A B C. (\<Inter>x\<in>C. A \<inter> B x) = (if C={} then UNIV else A \<inter>(\<Inter>x\<in>C. B x))"
  "\<And>A B C. (\<Inter>x\<in>C. A x - B) = (if C={} then UNIV else (\<Inter>x\<in>C. A x) - B)"
  "\<And>A B C. (\<Inter>x\<in>C. A - B x) = (if C={} then UNIV else A - (\<Union>x\<in>C. B x))"
  "\<And>a B C. (\<Inter>x\<in>C. insert a (B x)) = insert a (\<Inter>x\<in>C. B x)"
  "\<And>A B C. (\<Inter>x\<in>C. A x \<union> B) = ((\<Inter>x\<in>C. A x) \<union> B)"
  "\<And>A B C. (\<Inter>x\<in>C. A \<union> B x) = (A \<union> (\<Inter>x\<in>C. B x))"
  "\<And>A B. (\<Inter>x\<in>\<Union>A. B x) = (\<Inter>y\<in>A. \<Inter>x\<in>y. B x)"
  "\<And>A B C. (\<Inter>z\<in>UNION A B. C z) = (\<Inter>x\<in>A. \<Inter>z\<in>B x. C z)"
  "\<And>A B f. (\<Inter>x\<in>f`A. B x) = (\<Inter>a\<in>A. B (f a))"
  by auto

lemma ball_simps [simp,no_atp]:
  "\<And>A P Q. (\<forall>x\<in>A. P x \<or> Q) \<longleftrightarrow> ((\<forall>x\<in>A. P x) \<or> Q)"
  "\<And>A P Q. (\<forall>x\<in>A. P \<or> Q x) \<longleftrightarrow> (P \<or> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P x \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<longrightarrow> Q)"
  "\<And>P. (\<forall>x\<in>{}. P x) \<longleftrightarrow> True"
  "\<And>P. (\<forall>x\<in>UNIV. P x) \<longleftrightarrow> (\<forall>x. P x)"
  "\<And>a B P. (\<forall>x\<in>insert a B. P x) \<longleftrightarrow> (P a \<and> (\<forall>x\<in>B. P x))"
  "\<And>A P. (\<forall>x\<in>\<Union>A. P x) \<longleftrightarrow> (\<forall>y\<in>A. \<forall>x\<in>y. P x)"
  "\<And>A B P. (\<forall>x\<in> UNION A B. P x) = (\<forall>a\<in>A. \<forall>x\<in> B a. P x)"
  "\<And>P Q. (\<forall>x\<in>Collect Q. P x) \<longleftrightarrow> (\<forall>x. Q x \<longrightarrow> P x)"
  "\<And>A P f. (\<forall>x\<in>f`A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P (f x))"
  "\<And>A P. (\<not> (\<forall>x\<in>A. P x)) \<longleftrightarrow> (\<exists>x\<in>A. \<not> P x)"
  by auto

lemma bex_simps [simp,no_atp]:
  "\<And>A P Q. (\<exists>x\<in>A. P x \<and> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<and> Q)"
  "\<And>A P Q. (\<exists>x\<in>A. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x\<in>A. Q x))"
  "\<And>P. (\<exists>x\<in>{}. P x) \<longleftrightarrow> False"
  "\<And>P. (\<exists>x\<in>UNIV. P x) \<longleftrightarrow> (\<exists>x. P x)"
  "\<And>a B P. (\<exists>x\<in>insert a B. P x) \<longleftrightarrow> (P a | (\<exists>x\<in>B. P x))"
  "\<And>A P. (\<exists>x\<in>\<Union>A. P x) \<longleftrightarrow> (\<exists>y\<in>A. \<exists>x\<in>y. P x)"
  "\<And>A B P. (\<exists>x\<in>UNION A B. P x) \<longleftrightarrow> (\<exists>a\<in>A. \<exists>x\<in>B a. P x)"
  "\<And>P Q. (\<exists>x\<in>Collect Q. P x) \<longleftrightarrow> (\<exists>x. Q x \<and> P x)"
  "\<And>A P f. (\<exists>x\<in>f`A. P x) \<longleftrightarrow> (\<exists>x\<in>A. P (f x))"
  "\<And>A P. (\<not>(\<exists>x\<in>A. P x)) \<longleftrightarrow> (\<forall>x\<in>A. \<not> P x)"
  by auto

text {* \medskip Maxiscoping: pulling out big Unions and Intersections. *}

lemma UN_extend_simps:
  "\<And>a B C. insert a (\<Union>x\<in>C. B x) = (if C={} then {a} else (\<Union>x\<in>C. insert a (B x)))"
  "\<And>A B C. (\<Union>x\<in>C. A x) \<union>  B  = (if C={} then B else (\<Union>x\<in>C. A x \<union>  B))"
  "\<And>A B C. A \<union> (\<Union>x\<in>C. B x) = (if C={} then A else (\<Union>x\<in>C. A \<union> B x))"
  "\<And>A B C. ((\<Union>x\<in>C. A x) \<inter> B) = (\<Union>x\<in>C. A x \<inter> B)"
  "\<And>A B C. (A \<inter> (\<Union>x\<in>C. B x)) = (\<Union>x\<in>C. A \<inter> B x)"
  "\<And>A B C. ((\<Union>x\<in>C. A x) - B) = (\<Union>x\<in>C. A x - B)"
  "\<And>A B C. (A - (\<Inter>x\<in>C. B x)) = (\<Union>x\<in>C. A - B x)"
  "\<And>A B. (\<Union>y\<in>A. \<Union>x\<in>y. B x) = (\<Union>x\<in>\<Union>A. B x)"
  "\<And>A B C. (\<Union>x\<in>A. \<Union>z\<in>B x. C z) = (\<Union>z\<in>UNION A B. C z)"
  "\<And>A B f. (\<Union>a\<in>A. B (f a)) = (\<Union>x\<in>f`A. B x)"
  by auto

lemma INT_extend_simps:
  "\<And>A B C. (\<Inter>x\<in>C. A x) \<inter> B = (if C={} then B else (\<Inter>x\<in>C. A x \<inter> B))"
  "\<And>A B C. A \<inter> (\<Inter>x\<in>C. B x) = (if C={} then A else (\<Inter>x\<in>C. A \<inter> B x))"
  "\<And>A B C. (\<Inter>x\<in>C. A x) - B = (if C={} then UNIV - B else (\<Inter>x\<in>C. A x - B))"
  "\<And>A B C. A - (\<Union>x\<in>C. B x) = (if C={} then A else (\<Inter>x\<in>C. A - B x))"
  "\<And>a B C. insert a (\<Inter>x\<in>C. B x) = (\<Inter>x\<in>C. insert a (B x))"
  "\<And>A B C. ((\<Inter>x\<in>C. A x) \<union> B) = (\<Inter>x\<in>C. A x \<union> B)"
  "\<And>A B C. A \<union> (\<Inter>x\<in>C. B x) = (\<Inter>x\<in>C. A \<union> B x)"
  "\<And>A B. (\<Inter>y\<in>A. \<Inter>x\<in>y. B x) = (\<Inter>x\<in>\<Union>A. B x)"
  "\<And>A B C. (\<Inter>x\<in>A. \<Inter>z\<in>B x. C z) = (\<Inter>z\<in>UNION A B. C z)"
  "\<And>A B f. (\<Inter>a\<in>A. B (f a)) = (\<Inter>x\<in>f`A. B x)"
  by auto


text {* Legacy names *}

lemmas (in complete_lattice) INFI_def = INF_def
lemmas (in complete_lattice) SUPR_def = SUP_def
lemmas (in complete_lattice) le_SUPI = le_SUP_I
lemmas (in complete_lattice) le_SUPI2 = le_SUP_I2
lemmas (in complete_lattice) le_INFI = le_INF_I

lemma (in complete_lattice) INF_subset:
  "B \<subseteq> A \<Longrightarrow> INFI A f \<sqsubseteq> INFI B f"
  by (rule INF_superset_mono) auto

lemmas INFI_apply = INF_apply
lemmas SUPR_apply = SUP_apply

text {* Finally *}

no_notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

lemmas mem_simps =
  insert_iff empty_iff Un_iff Int_iff Compl_iff Diff_iff
  mem_Collect_eq UN_iff Union_iff INT_iff Inter_iff
  -- {* Each of these has ALREADY been added @{text "[simp]"} above. *}

end
