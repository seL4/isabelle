(*  Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel; Florian Haftmann, TU Muenchen *)

header {* Complete lattices, with special focus on sets *}

theory Complete_Lattice
imports Set
begin

notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)


subsection {* Abstract complete lattices *}

class complete_lattice = lattice + bot + top +
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)
    and Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> x"
     and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>A \<sqsubseteq> z"
begin

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<le> a}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<le> b}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Inf_Univ: "\<Sqinter>UNIV = \<Squnion>{}"
  unfolding Sup_Inf by auto

lemma Sup_Univ: "\<Squnion>UNIV = \<Sqinter>{}"
  unfolding Inf_Sup by auto

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

lemma Inf_insert_simp:
  "\<Sqinter>insert a A = (if A = {} then a else a \<sqinter> \<Sqinter>A)"
  by (cases "A = {}") (simp_all, simp add: Inf_insert)

lemma Sup_insert_simp:
  "\<Squnion>insert a A = (if A = {} then a else a \<squnion> \<Squnion>A)"
  by (cases "A = {}") (simp_all, simp add: Sup_insert)

lemma Inf_binary:
  "\<Sqinter>{a, b} = a \<sqinter> b"
  by (auto simp add: Inf_insert_simp)

lemma Sup_binary:
  "\<Squnion>{a, b} = a \<squnion> b"
  by (auto simp add: Sup_insert_simp)

lemma bot_def:
  "bot = \<Squnion>{}"
  by (auto intro: antisym Sup_least)

lemma top_def:
  "top = \<Sqinter>{}"
  by (auto intro: antisym Inf_greatest)

lemma sup_bot [simp]:
  "x \<squnion> bot = x"
  using bot_least [of x] by (simp add: le_iff_sup sup_commute)

lemma inf_top [simp]:
  "x \<sqinter> top = x"
  using top_greatest [of x] by (simp add: le_iff_inf inf_commute)

definition SUPR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "SUPR A f = \<Squnion> (f ` A)"

definition INFI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "INFI A f = \<Sqinter> (f ` A)"

end

syntax
  "_SUP1"     :: "pttrns => 'b => 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn => 'a set => 'b => 'b"  ("(3SUP _:_./ _)" [0, 10] 10)
  "_INF1"     :: "pttrns => 'b => 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn => 'a set => 'b => 'b"  ("(3INF _:_./ _)" [0, 10] 10)

translations
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR CONST UNIV (%x. B)"
  "SUP x. B"     == "SUP x:CONST UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI CONST UNIV (%x. B)"
  "INF x. B"     == "INF x:CONST UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax SUPR} "_SUP",
Syntax.preserve_binder_abs2_tr' @{const_syntax INFI} "_INF"
] *} -- {* to avoid eta-contraction of body *}

context complete_lattice
begin

lemma le_SUPI: "i : A \<Longrightarrow> M i \<le> (SUP i:A. M i)"
  by (auto simp add: SUPR_def intro: Sup_upper)

lemma SUP_leI: "(\<And>i. i : A \<Longrightarrow> M i \<le> u) \<Longrightarrow> (SUP i:A. M i) \<le> u"
  by (auto simp add: SUPR_def intro: Sup_least)

lemma INF_leI: "i : A \<Longrightarrow> (INF i:A. M i) \<le> M i"
  by (auto simp add: INFI_def intro: Inf_lower)

lemma le_INFI: "(\<And>i. i : A \<Longrightarrow> u \<le> M i) \<Longrightarrow> u \<le> (INF i:A. M i)"
  by (auto simp add: INFI_def intro: Inf_greatest)

lemma SUP_const[simp]: "A \<noteq> {} \<Longrightarrow> (SUP i:A. M) = M"
  by (auto intro: antisym SUP_leI le_SUPI)

lemma INF_const[simp]: "A \<noteq> {} \<Longrightarrow> (INF i:A. M) = M"
  by (auto intro: antisym INF_leI le_INFI)

end


subsection {* @{typ bool} and @{typ "_ \<Rightarrow> _"} as complete lattice *}

instantiation bool :: complete_lattice
begin

definition
  Inf_bool_def: "\<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x)"

definition
  Sup_bool_def: "\<Squnion>A \<longleftrightarrow> (\<exists>x\<in>A. x)"

instance proof
qed (auto simp add: Inf_bool_def Sup_bool_def le_bool_def)

end

lemma Inf_empty_bool [simp]:
  "\<Sqinter>{}"
  unfolding Inf_bool_def by auto

lemma not_Sup_empty_bool [simp]:
  "\<not> \<Squnion>{}"
  unfolding Sup_bool_def by auto

lemma INFI_bool_eq:
  "INFI = Ball"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(INF x:A. P x) \<longleftrightarrow> (\<forall>x \<in> A. P x)"
    by (auto simp add: Ball_def INFI_def Inf_bool_def)
qed

lemma SUPR_bool_eq:
  "SUPR = Bex"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(SUP x:A. P x) \<longleftrightarrow> (\<exists>x \<in> A. P x)"
    by (auto simp add: Bex_def SUPR_def Sup_bool_def)
qed

instantiation "fun" :: (type, complete_lattice) complete_lattice
begin

definition
  Inf_fun_def [code del]: "\<Sqinter>A = (\<lambda>x. \<Sqinter>{y. \<exists>f\<in>A. y = f x})"

definition
  Sup_fun_def [code del]: "\<Squnion>A = (\<lambda>x. \<Squnion>{y. \<exists>f\<in>A. y = f x})"

instance proof
qed (auto simp add: Inf_fun_def Sup_fun_def le_fun_def
  intro: Inf_lower Sup_upper Inf_greatest Sup_least)

end

lemma Inf_empty_fun:
  "\<Sqinter>{} = (\<lambda>_. \<Sqinter>{})"
  by (simp add: Inf_fun_def)

lemma Sup_empty_fun:
  "\<Squnion>{} = (\<lambda>_. \<Squnion>{})"
  by (simp add: Sup_fun_def)


subsection {* Union *}

definition Union :: "'a set set \<Rightarrow> 'a set" where
  Sup_set_eq [symmetric]: "Union S = \<Squnion>S"

notation (xsymbols)
  Union  ("\<Union>_" [90] 90)

lemma Union_eq:
  "\<Union>A = {x. \<exists>B \<in> A. x \<in> B}"
proof (rule set_ext)
  fix x
  have "(\<exists>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<exists>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Union>A \<longleftrightarrow> x \<in> {x. \<exists>B\<in>A. x \<in> B}"
    by (simp add: Sup_set_eq [symmetric] Sup_fun_def Sup_bool_def) (simp add: mem_def)
qed

lemma Union_iff [simp, noatp]:
  "A \<in> \<Union>C \<longleftrightarrow> (\<exists>X\<in>C. A\<in>X)"
  by (unfold Union_eq) blast

lemma UnionI [intro]:
  "X \<in> C \<Longrightarrow> A \<in> X \<Longrightarrow> A \<in> \<Union>C"
  -- {* The order of the premises presupposes that @{term C} is rigid;
    @{term A} may be flexible. *}
  by auto

lemma UnionE [elim!]:
  "A \<in> \<Union>C \<Longrightarrow> (\<And>X. A\<in>X \<Longrightarrow> X\<in>C \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma Union_upper: "B \<in> A ==> B \<subseteq> Union A"
  by (iprover intro: subsetI UnionI)

lemma Union_least: "(!!X. X \<in> A ==> X \<subseteq> C) ==> Union A \<subseteq> C"
  by (iprover intro: subsetI elim: UnionE dest: subsetD)

lemma Un_eq_Union: "A \<union> B = \<Union>{A, B}"
  by blast

lemma Union_empty [simp]: "Union({}) = {}"
  by blast

lemma Union_UNIV [simp]: "Union UNIV = UNIV"
  by blast

lemma Union_insert [simp]: "Union (insert a B) = a \<union> \<Union>B"
  by blast

lemma Union_Un_distrib [simp]: "\<Union>(A Un B) = \<Union>A \<union> \<Union>B"
  by blast

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by blast

lemma Union_empty_conv [simp,noatp]: "(\<Union>A = {}) = (\<forall>x\<in>A. x = {})"
  by blast

lemma empty_Union_conv [simp,noatp]: "({} = \<Union>A) = (\<forall>x\<in>A. x = {})"
  by blast

lemma Union_disjoint: "(\<Union>C \<inter> A = {}) = (\<forall>B\<in>C. B \<inter> A = {})"
  by blast

lemma subset_Pow_Union: "A \<subseteq> Pow (\<Union>A)"
  by blast

lemma Union_Pow_eq [simp]: "\<Union>(Pow A) = A"
  by blast

lemma Union_mono: "A \<subseteq> B ==> \<Union>A \<subseteq> \<Union>B"
  by blast


subsection {* Unions of families *}

definition UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  SUPR_set_eq [symmetric]: "UNION S f = (SUP x:S. f x)"

syntax
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3UN _./ _)" [0, 10] 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3UN _:_./ _)" [0, 10] 10)

syntax (xsymbols)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" [0, 10] 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 10] 10)

syntax (latex output)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 10] 10)

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

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax UNION} "@UNION"
] *} -- {* to avoid eta-contraction of body *}

lemma UNION_eq_Union_image:
  "(\<Union>x\<in>A. B x) = \<Union>(B`A)"
  by (simp add: SUPR_def SUPR_set_eq [symmetric] Sup_set_eq)

lemma Union_def:
  "\<Union>S = (\<Union>x\<in>S. x)"
  by (simp add: UNION_eq_Union_image image_def)

lemma UNION_def [noatp]:
  "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
  by (auto simp add: UNION_eq_Union_image Union_eq)
  
lemma Union_image_eq [simp]:
  "\<Union>(B`A) = (\<Union>x\<in>A. B x)"
  by (rule sym) (fact UNION_eq_Union_image)
  
lemma UN_iff [simp]: "(b: (UN x:A. B x)) = (EX x:A. b: B x)"
  by (unfold UNION_def) blast

lemma UN_I [intro]: "a:A ==> b: B a ==> b: (UN x:A. B x)"
  -- {* The order of the premises presupposes that @{term A} is rigid;
    @{term b} may be flexible. *}
  by auto

lemma UN_E [elim!]: "b : (UN x:A. B x) ==> (!!x. x:A ==> b: B x ==> R) ==> R"
  by (unfold UNION_def) blast

lemma UN_cong [cong]:
    "A = B ==> (!!x. x:B ==> C x = D x) ==> (UN x:A. C x) = (UN x:B. D x)"
  by (simp add: UNION_def)

lemma strong_UN_cong:
    "A = B ==> (!!x. x:B =simp=> C x = D x) ==> (UN x:A. C x) = (UN x:B. D x)"
  by (simp add: UNION_def simp_implies_def)

lemma image_eq_UN: "f`A = (UN x:A. {f x})"
  by blast

lemma UN_upper: "a \<in> A ==> B a \<subseteq> (\<Union>x\<in>A. B x)"
  by blast

lemma UN_least: "(!!x. x \<in> A ==> B x \<subseteq> C) ==> (\<Union>x\<in>A. B x) \<subseteq> C"
  by (iprover intro: subsetI elim: UN_E dest: subsetD)

lemma Collect_bex_eq [noatp]: "{x. \<exists>y\<in>A. P x y} = (\<Union>y\<in>A. {x. P x y})"
  by blast

lemma UN_insert_distrib: "u \<in> A ==> (\<Union>x\<in>A. insert a (B x)) = insert a (\<Union>x\<in>A. B x)"
  by blast

lemma UN_empty [simp,noatp]: "(\<Union>x\<in>{}. B x) = {}"
  by blast

lemma UN_empty2 [simp]: "(\<Union>x\<in>A. {}) = {}"
  by blast

lemma UN_singleton [simp]: "(\<Union>x\<in>A. {x}) = A"
  by blast

lemma UN_absorb: "k \<in> I ==> A k \<union> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. A i)"
  by auto

lemma UN_insert [simp]: "(\<Union>x\<in>insert a A. B x) = B a \<union> UNION A B"
  by blast

lemma UN_Un[simp]: "(\<Union>i \<in> A \<union> B. M i) = (\<Union>i\<in>A. M i) \<union> (\<Union>i\<in>B. M i)"
  by blast

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B y). C x) = (\<Union>y\<in>A. \<Union>x\<in>B y. C x)"
  by blast

lemma UN_subset_iff: "((\<Union>i\<in>I. A i) \<subseteq> B) = (\<forall>i\<in>I. A i \<subseteq> B)"
  by blast

lemma image_Union: "f ` \<Union>S = (\<Union>x\<in>S. f ` x)"
  by blast

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A = {} then {} else c)"
  by auto

lemma UN_eq: "(\<Union>x\<in>A. B x) = \<Union>({Y. \<exists>x\<in>A. Y = B x})"
  by blast

lemma UNION_empty_conv[simp]:
  "({} = (UN x:A. B x)) = (\<forall>x\<in>A. B x = {})"
  "((UN x:A. B x) = {}) = (\<forall>x\<in>A. B x = {})"
by blast+

lemma Collect_ex_eq [noatp]: "{x. \<exists>y. P x y} = (\<Union>y. {x. P x y})"
  by blast

lemma ball_UN: "(\<forall>z \<in> UNION A B. P z) = (\<forall>x\<in>A. \<forall>z \<in> B x. P z)"
  by blast

lemma bex_UN: "(\<exists>z \<in> UNION A B. P z) = (\<exists>x\<in>A. \<exists>z\<in>B x. P z)"
  by blast

lemma Un_eq_UN: "A \<union> B = (\<Union>b. if b then A else B)"
  by (auto simp add: split_if_mem2)

lemma UN_bool_eq: "(\<Union>b::bool. A b) = (A True \<union> A False)"
  by (auto intro: bool_contrapos)

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow (B x)) \<subseteq> Pow (\<Union>x\<in>A. B x)"
  by blast

lemma UN_mono:
  "A \<subseteq> B ==> (!!x. x \<in> A ==> f x \<subseteq> g x) ==>
    (\<Union>x\<in>A. f x) \<subseteq> (\<Union>x\<in>B. g x)"
  by (blast dest: subsetD)

lemma vimage_Union: "f -` (Union A) = (UN X:A. f -` X)"
  by blast

lemma vimage_UN: "f-`(UN x:A. B x) = (UN x:A. f -` B x)"
  by blast

lemma vimage_eq_UN: "f-`B = (UN y: B. f-`{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma image_UN: "(f ` (UNION A B)) = (UN x:A.(f ` (B x)))"
by blast


subsection {* Inter *}

definition Inter :: "'a set set \<Rightarrow> 'a set" where
  Inf_set_eq [symmetric]: "Inter S = \<Sqinter>S"
  
notation (xsymbols)
  Inter  ("\<Inter>_" [90] 90)

lemma Inter_eq [code del]:
  "\<Inter>A = {x. \<forall>B \<in> A. x \<in> B}"
proof (rule set_ext)
  fix x
  have "(\<forall>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<forall>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Inter>A \<longleftrightarrow> x \<in> {x. \<forall>B \<in> A. x \<in> B}"
    by (simp add: Inf_fun_def Inf_bool_def Inf_set_eq [symmetric]) (simp add: mem_def)
qed

lemma Inter_iff [simp,noatp]: "(A : Inter C) = (ALL X:C. A:X)"
  by (unfold Inter_eq) blast

lemma InterI [intro!]: "(!!X. X:C ==> A:X) ==> A : Inter C"
  by (simp add: Inter_eq)

text {*
  \medskip A ``destruct'' rule -- every @{term X} in @{term C}
  contains @{term A} as an element, but @{prop "A:X"} can hold when
  @{prop "X:C"} does not!  This rule is analogous to @{text spec}.
*}

lemma InterD [elim]: "A : Inter C ==> X:C ==> A:X"
  by auto

lemma InterE [elim]: "A : Inter C ==> (X~:C ==> R) ==> (A:X ==> R) ==> R"
  -- {* ``Classical'' elimination rule -- does not require proving
    @{prop "X:C"}. *}
  by (unfold Inter_eq) blast

lemma Inter_lower: "B \<in> A ==> Inter A \<subseteq> B"
  by blast

lemma Inter_subset:
  "[| !!X. X \<in> A ==> X \<subseteq> B; A ~= {} |] ==> \<Inter>A \<subseteq> B"
  by blast

lemma Inter_greatest: "(!!X. X \<in> A ==> C \<subseteq> X) ==> C \<subseteq> Inter A"
  by (iprover intro: InterI subsetI dest: subsetD)

lemma Int_eq_Inter: "A \<inter> B = \<Inter>{A, B}"
  by blast

lemma Inter_empty [simp]: "\<Inter>{} = UNIV"
  by blast

lemma Inter_UNIV [simp]: "\<Inter>UNIV = {}"
  by blast

lemma Inter_insert [simp]: "\<Inter>(insert a B) = a \<inter> \<Inter>B"
  by blast

lemma Inter_Un_subset: "\<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by blast

lemma Inter_Un_distrib: "\<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by blast

lemma Inter_UNIV_conv [simp,noatp]:
  "(\<Inter>A = UNIV) = (\<forall>x\<in>A. x = UNIV)"
  "(UNIV = \<Inter>A) = (\<forall>x\<in>A. x = UNIV)"
  by blast+

lemma Inter_anti_mono: "B \<subseteq> A ==> \<Inter>A \<subseteq> \<Inter>B"
  by blast


subsection {* Intersections of families *}

definition INTER :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  INFI_set_eq [symmetric]: "INTER S f = (INF x:S. f x)"

syntax
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3INT _./ _)" [0, 10] 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3INT _:_./ _)" [0, 10] 10)

syntax (xsymbols)
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>_./ _)" [0, 10] 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 10] 10)

syntax (latex output)
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 10] 10)

translations
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "CONST INTER CONST UNIV (%x. B)"
  "INT x. B"    == "INT x:CONST UNIV. B"
  "INT x:A. B"  == "CONST INTER A (%x. B)"

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax INTER} "@INTER"
] *} -- {* to avoid eta-contraction of body *}

lemma INTER_eq_Inter_image:
  "(\<Inter>x\<in>A. B x) = \<Inter>(B`A)"
  by (simp add: INFI_def INFI_set_eq [symmetric] Inf_set_eq)
  
lemma Inter_def:
  "\<Inter>S = (\<Inter>x\<in>S. x)"
  by (simp add: INTER_eq_Inter_image image_def)

lemma INTER_def:
  "(\<Inter>x\<in>A. B x) = {y. \<forall>x\<in>A. y \<in> B x}"
  by (auto simp add: INTER_eq_Inter_image Inter_eq)

lemma Inter_image_eq [simp]:
  "\<Inter>(B`A) = (\<Inter>x\<in>A. B x)"
  by (rule sym) (fact INTER_eq_Inter_image)

lemma INT_iff [simp]: "(b: (INT x:A. B x)) = (ALL x:A. b: B x)"
  by (unfold INTER_def) blast

lemma INT_I [intro!]: "(!!x. x:A ==> b: B x) ==> b : (INT x:A. B x)"
  by (unfold INTER_def) blast

lemma INT_D [elim]: "b : (INT x:A. B x) ==> a:A ==> b: B a"
  by auto

lemma INT_E [elim]: "b : (INT x:A. B x) ==> (b: B a ==> R) ==> (a~:A ==> R) ==> R"
  -- {* "Classical" elimination -- by the Excluded Middle on @{prop "a:A"}. *}
  by (unfold INTER_def) blast

lemma INT_cong [cong]:
    "A = B ==> (!!x. x:B ==> C x = D x) ==> (INT x:A. C x) = (INT x:B. D x)"
  by (simp add: INTER_def)

lemma Collect_ball_eq: "{x. \<forall>y\<in>A. P x y} = (\<Inter>y\<in>A. {x. P x y})"
  by blast

lemma Collect_all_eq: "{x. \<forall>y. P x y} = (\<Inter>y. {x. P x y})"
  by blast

lemma INT_lower: "a \<in> A ==> (\<Inter>x\<in>A. B x) \<subseteq> B a"
  by blast

lemma INT_greatest: "(!!x. x \<in> A ==> C \<subseteq> B x) ==> C \<subseteq> (\<Inter>x\<in>A. B x)"
  by (iprover intro: INT_I subsetI dest: subsetD)

lemma INT_empty [simp]: "(\<Inter>x\<in>{}. B x) = UNIV"
  by blast

lemma INT_absorb: "k \<in> I ==> A k \<inter> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. A i)"
  by blast

lemma INT_subset_iff: "(B \<subseteq> (\<Inter>i\<in>I. A i)) = (\<forall>i\<in>I. B \<subseteq> A i)"
  by blast

lemma INT_insert [simp]: "(\<Inter>x \<in> insert a A. B x) = B a \<inter> INTER A B"
  by blast

lemma INT_Un: "(\<Inter>i \<in> A \<union> B. M i) = (\<Inter>i \<in> A. M i) \<inter> (\<Inter>i\<in>B. M i)"
  by blast

lemma INT_insert_distrib:
    "u \<in> A ==> (\<Inter>x\<in>A. insert a (B x)) = insert a (\<Inter>x\<in>A. B x)"
  by blast

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A = {} then UNIV else c)"
  by auto

lemma INT_eq: "(\<Inter>x\<in>A. B x) = \<Inter>({Y. \<exists>x\<in>A. Y = B x})"
  -- {* Look: it has an \emph{existential} quantifier *}
  by blast

lemma INTER_UNIV_conv[simp]:
 "(UNIV = (INT x:A. B x)) = (\<forall>x\<in>A. B x = UNIV)"
 "((INT x:A. B x) = UNIV) = (\<forall>x\<in>A. B x = UNIV)"
by blast+

lemma INT_bool_eq: "(\<Inter>b::bool. A b) = (A True \<inter> A False)"
  by (auto intro: bool_induct)

lemma Pow_INT_eq: "Pow (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. Pow (B x))"
  by blast

lemma INT_anti_mono:
  "B \<subseteq> A ==> (!!x. x \<in> A ==> f x \<subseteq> g x) ==>
    (\<Inter>x\<in>A. f x) \<subseteq> (\<Inter>x\<in>A. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (blast dest: subsetD)

lemma vimage_INT: "f-`(INT x:A. B x) = (INT x:A. f -` B x)"
  by blast


subsection {* Distributive laws *}

lemma Int_Union: "A \<inter> \<Union>B = (\<Union>C\<in>B. A \<inter> C)"
  by blast

lemma Int_Union2: "\<Union>B \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
  by blast

lemma Un_Union_image: "(\<Union>x\<in>C. A x \<union> B x) = \<Union>(A`C) \<union> \<Union>(B`C)"
  -- {* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: *}
  -- {* Union of a family of unions *}
  by blast

lemma UN_Un_distrib: "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Un_Inter: "A \<union> \<Inter>B = (\<Inter>C\<in>B. A \<union> C)"
  by blast

lemma Int_Inter_image: "(\<Inter>x\<in>C. A x \<inter> B x) = \<Inter>(A`C) \<inter> \<Inter>(B`C)"
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

lemma Compl_UN [simp]: "-(\<Union>x\<in>A. B x) = (\<Inter>x\<in>A. -B x)"
  by blast

lemma Compl_INT [simp]: "-(\<Inter>x\<in>A. B x) = (\<Union>x\<in>A. -B x)"
  by blast


subsection {* Miniscoping and maxiscoping *}

text {* \medskip Miniscoping: pushing in quantifiers and big Unions
           and Intersections. *}

lemma UN_simps [simp]:
  "!!a B C. (UN x:C. insert a (B x)) = (if C={} then {} else insert a (UN x:C. B x))"
  "!!A B C. (UN x:C. A x Un B)   = ((if C={} then {} else (UN x:C. A x) Un B))"
  "!!A B C. (UN x:C. A Un B x)   = ((if C={} then {} else A Un (UN x:C. B x)))"
  "!!A B C. (UN x:C. A x Int B)  = ((UN x:C. A x) Int B)"
  "!!A B C. (UN x:C. A Int B x)  = (A Int (UN x:C. B x))"
  "!!A B C. (UN x:C. A x - B)    = ((UN x:C. A x) - B)"
  "!!A B C. (UN x:C. A - B x)    = (A - (INT x:C. B x))"
  "!!A B. (UN x: Union A. B x) = (UN y:A. UN x:y. B x)"
  "!!A B C. (UN z: UNION A B. C z) = (UN  x:A. UN z: B(x). C z)"
  "!!A B f. (UN x:f`A. B x)     = (UN a:A. B (f a))"
  by auto

lemma INT_simps [simp]:
  "!!A B C. (INT x:C. A x Int B) = (if C={} then UNIV else (INT x:C. A x) Int B)"
  "!!A B C. (INT x:C. A Int B x) = (if C={} then UNIV else A Int (INT x:C. B x))"
  "!!A B C. (INT x:C. A x - B)   = (if C={} then UNIV else (INT x:C. A x) - B)"
  "!!A B C. (INT x:C. A - B x)   = (if C={} then UNIV else A - (UN x:C. B x))"
  "!!a B C. (INT x:C. insert a (B x)) = insert a (INT x:C. B x)"
  "!!A B C. (INT x:C. A x Un B)  = ((INT x:C. A x) Un B)"
  "!!A B C. (INT x:C. A Un B x)  = (A Un (INT x:C. B x))"
  "!!A B. (INT x: Union A. B x) = (INT y:A. INT x:y. B x)"
  "!!A B C. (INT z: UNION A B. C z) = (INT x:A. INT z: B(x). C z)"
  "!!A B f. (INT x:f`A. B x)    = (INT a:A. B (f a))"
  by auto

lemma ball_simps [simp,noatp]:
  "!!A P Q. (ALL x:A. P x | Q) = ((ALL x:A. P x) | Q)"
  "!!A P Q. (ALL x:A. P | Q x) = (P | (ALL x:A. Q x))"
  "!!A P Q. (ALL x:A. P --> Q x) = (P --> (ALL x:A. Q x))"
  "!!A P Q. (ALL x:A. P x --> Q) = ((EX x:A. P x) --> Q)"
  "!!P. (ALL x:{}. P x) = True"
  "!!P. (ALL x:UNIV. P x) = (ALL x. P x)"
  "!!a B P. (ALL x:insert a B. P x) = (P a & (ALL x:B. P x))"
  "!!A P. (ALL x:Union A. P x) = (ALL y:A. ALL x:y. P x)"
  "!!A B P. (ALL x: UNION A B. P x) = (ALL a:A. ALL x: B a. P x)"
  "!!P Q. (ALL x:Collect Q. P x) = (ALL x. Q x --> P x)"
  "!!A P f. (ALL x:f`A. P x) = (ALL x:A. P (f x))"
  "!!A P. (~(ALL x:A. P x)) = (EX x:A. ~P x)"
  by auto

lemma bex_simps [simp,noatp]:
  "!!A P Q. (EX x:A. P x & Q) = ((EX x:A. P x) & Q)"
  "!!A P Q. (EX x:A. P & Q x) = (P & (EX x:A. Q x))"
  "!!P. (EX x:{}. P x) = False"
  "!!P. (EX x:UNIV. P x) = (EX x. P x)"
  "!!a B P. (EX x:insert a B. P x) = (P(a) | (EX x:B. P x))"
  "!!A P. (EX x:Union A. P x) = (EX y:A. EX x:y. P x)"
  "!!A B P. (EX x: UNION A B. P x) = (EX a:A. EX x:B a. P x)"
  "!!P Q. (EX x:Collect Q. P x) = (EX x. Q x & P x)"
  "!!A P f. (EX x:f`A. P x) = (EX x:A. P (f x))"
  "!!A P. (~(EX x:A. P x)) = (ALL x:A. ~P x)"
  by auto

lemma ball_conj_distrib:
  "(ALL x:A. P x & Q x) = ((ALL x:A. P x) & (ALL x:A. Q x))"
  by blast

lemma bex_disj_distrib:
  "(EX x:A. P x | Q x) = ((EX x:A. P x) | (EX x:A. Q x))"
  by blast


text {* \medskip Maxiscoping: pulling out big Unions and Intersections. *}

lemma UN_extend_simps:
  "!!a B C. insert a (UN x:C. B x) = (if C={} then {a} else (UN x:C. insert a (B x)))"
  "!!A B C. (UN x:C. A x) Un B    = (if C={} then B else (UN x:C. A x Un B))"
  "!!A B C. A Un (UN x:C. B x)   = (if C={} then A else (UN x:C. A Un B x))"
  "!!A B C. ((UN x:C. A x) Int B) = (UN x:C. A x Int B)"
  "!!A B C. (A Int (UN x:C. B x)) = (UN x:C. A Int B x)"
  "!!A B C. ((UN x:C. A x) - B) = (UN x:C. A x - B)"
  "!!A B C. (A - (INT x:C. B x)) = (UN x:C. A - B x)"
  "!!A B. (UN y:A. UN x:y. B x) = (UN x: Union A. B x)"
  "!!A B C. (UN  x:A. UN z: B(x). C z) = (UN z: UNION A B. C z)"
  "!!A B f. (UN a:A. B (f a)) = (UN x:f`A. B x)"
  by auto

lemma INT_extend_simps:
  "!!A B C. (INT x:C. A x) Int B = (if C={} then B else (INT x:C. A x Int B))"
  "!!A B C. A Int (INT x:C. B x) = (if C={} then A else (INT x:C. A Int B x))"
  "!!A B C. (INT x:C. A x) - B   = (if C={} then UNIV-B else (INT x:C. A x - B))"
  "!!A B C. A - (UN x:C. B x)   = (if C={} then A else (INT x:C. A - B x))"
  "!!a B C. insert a (INT x:C. B x) = (INT x:C. insert a (B x))"
  "!!A B C. ((INT x:C. A x) Un B)  = (INT x:C. A x Un B)"
  "!!A B C. A Un (INT x:C. B x)  = (INT x:C. A Un B x)"
  "!!A B. (INT y:A. INT x:y. B x) = (INT x: Union A. B x)"
  "!!A B C. (INT x:A. INT z: B(x). C z) = (INT z: UNION A B. C z)"
  "!!A B f. (INT a:A. B (f a))    = (INT x:f`A. B x)"
  by auto


no_notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

lemmas mem_simps =
  insert_iff empty_iff Un_iff Int_iff Compl_iff Diff_iff
  mem_Collect_eq UN_iff Union_iff INT_iff Inter_iff
  -- {* Each of these has ALREADY been added @{text "[simp]"} above. *}

end
