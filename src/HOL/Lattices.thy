(*  Title:      HOL/Lattices.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* Abstract lattices *}

theory Lattices
imports Orderings
begin

subsection{* Lattices *}

class lower_semilattice = order +
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes inf_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
  and inf_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
  and inf_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"

class upper_semilattice = order +
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
  assumes sup_ge1 [simp]: "x \<sqsubseteq> x \<squnion> y"
  and sup_ge2 [simp]: "y \<sqsubseteq> x \<squnion> y"
  and sup_least: "y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<squnion> z \<sqsubseteq> x"

class lattice = lower_semilattice + upper_semilattice

subsubsection{* Intro and elim rules*}

context lower_semilattice
begin

lemmas antisym_intro [intro!] = antisym
lemmas (in -) [rule del] = antisym_intro

lemma le_infI1[intro]:
  assumes "a \<sqsubseteq> x"
  shows "a \<sqinter> b \<sqsubseteq> x"
proof (rule order_trans)
  show "a \<sqinter> b \<sqsubseteq> a" and "a \<sqsubseteq> x" using assms by simp
qed
lemmas (in -) [rule del] = le_infI1

lemma le_infI2[intro]:
  assumes "b \<sqsubseteq> x"
  shows "a \<sqinter> b \<sqsubseteq> x"
proof (rule order_trans)
  show "a \<sqinter> b \<sqsubseteq> b" and "b \<sqsubseteq> x" using assms by simp
qed
lemmas (in -) [rule del] = le_infI2

lemma le_infI[intro!]: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<sqinter> b"
by(blast intro: inf_greatest)
lemmas (in -) [rule del] = le_infI

lemma le_infE [elim!]: "x \<sqsubseteq> a \<sqinter> b \<Longrightarrow> (x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans)
lemmas (in -) [rule del] = le_infE

lemma le_inf_iff [simp]:
 "x \<sqsubseteq> y \<sqinter> z = (x \<sqsubseteq> y \<and> x \<sqsubseteq> z)"
by blast

lemma le_iff_inf: "(x \<sqsubseteq> y) = (x \<sqinter> y = x)"
by(blast dest:eq_iff[THEN iffD1])

end

lemma mono_inf: "mono f \<Longrightarrow> f (inf A B) \<le> inf (f A) (f B)"
  by (auto simp add: mono_def)


context upper_semilattice
begin

lemmas antisym_intro [intro!] = antisym
lemmas (in -) [rule del] = antisym_intro

lemma le_supI1[intro]: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto
lemmas (in -) [rule del] = le_supI1

lemma le_supI2[intro]: "x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto 
lemmas (in -) [rule del] = le_supI2

lemma le_supI[intro!]: "a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> a \<squnion> b \<sqsubseteq> x"
by(blast intro: sup_least)
lemmas (in -) [rule del] = le_supI

lemma le_supE[elim!]: "a \<squnion> b \<sqsubseteq> x \<Longrightarrow> (a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans)
lemmas (in -) [rule del] = le_supE


lemma ge_sup_conv[simp]:
 "x \<squnion> y \<sqsubseteq> z = (x \<sqsubseteq> z \<and> y \<sqsubseteq> z)"
by blast

lemma le_iff_sup: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
by(blast dest:eq_iff[THEN iffD1])

end

lemma mono_sup: "mono f \<Longrightarrow> sup (f A) (f B) \<le> f (sup A B)"
  by (auto simp add: mono_def)


subsubsection{* Equational laws *}


context lower_semilattice
begin

lemma inf_commute: "(x \<sqinter> y) = (y \<sqinter> x)"
by blast

lemma inf_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
by blast

lemma inf_idem[simp]: "x \<sqinter> x = x"
by blast

lemma inf_left_idem[simp]: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
by blast

lemma inf_absorb1: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
by blast

lemma inf_absorb2: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
by blast

lemma inf_left_commute: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)"
by blast

lemmas inf_ACI = inf_commute inf_assoc inf_left_commute inf_left_idem

end


context upper_semilattice
begin

lemma sup_commute: "(x \<squnion> y) = (y \<squnion> x)"
by blast

lemma sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
by blast

lemma sup_idem[simp]: "x \<squnion> x = x"
by blast

lemma sup_left_idem[simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
by blast

lemma sup_absorb1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
by blast

lemma sup_absorb2: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
by blast

lemma sup_left_commute: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
by blast

lemmas sup_ACI = sup_commute sup_assoc sup_left_commute sup_left_idem

end

context lattice
begin

lemma inf_sup_absorb: "x \<sqinter> (x \<squnion> y) = x"
by(blast intro: antisym inf_le1 inf_greatest sup_ge1)

lemma sup_inf_absorb: "x \<squnion> (x \<sqinter> y) = x"
by(blast intro: antisym sup_ge1 sup_least inf_le1)

lemmas ACI = inf_ACI sup_ACI

lemmas inf_sup_ord = inf_le1 inf_le2 sup_ge1 sup_ge2

text{* Towards distributivity *}

lemma distrib_sup_le: "x \<squnion> (y \<sqinter> z) \<sqsubseteq> (x \<squnion> y) \<sqinter> (x \<squnion> z)"
by blast

lemma distrib_inf_le: "(x \<sqinter> y) \<squnion> (x \<sqinter> z) \<sqsubseteq> x \<sqinter> (y \<squnion> z)"
by blast


text{* If you have one of them, you have them all. *}

lemma distrib_imp1:
assumes D: "!!x y z. x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
shows "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof-
  have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)" by(simp add:sup_inf_absorb)
  also have "\<dots> = x \<squnion> (z \<sqinter> (x \<squnion> y))" by(simp add:D inf_commute sup_assoc)
  also have "\<dots> = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)"
    by(simp add:inf_sup_absorb inf_commute)
  also have "\<dots> = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by(simp add:D)
  finally show ?thesis .
qed

lemma distrib_imp2:
assumes D: "!!x y z. x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
shows "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
proof-
  have "x \<sqinter> (y \<squnion> z) = (x \<sqinter> (x \<squnion> z)) \<sqinter> (y \<squnion> z)" by(simp add:inf_sup_absorb)
  also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))" by(simp add:D sup_commute inf_assoc)
  also have "\<dots> = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)"
    by(simp add:sup_inf_absorb sup_commute)
  also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by(simp add:D)
  finally show ?thesis .
qed

(* seems unused *)
lemma modular_le: "x \<sqsubseteq> z \<Longrightarrow> x \<squnion> (y \<sqinter> z) \<sqsubseteq> (x \<squnion> y) \<sqinter> z"
by blast

end


subsection {* Distributive lattices *}

class distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

context distrib_lattice
begin

lemma sup_inf_distrib2:
 "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
by(simp add:ACI sup_inf_distrib1)

lemma inf_sup_distrib1:
 "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
by(rule distrib_imp2[OF sup_inf_distrib1])

lemma inf_sup_distrib2:
 "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
by(simp add:ACI inf_sup_distrib1)

lemmas distrib =
  sup_inf_distrib1 sup_inf_distrib2 inf_sup_distrib1 inf_sup_distrib2

end


subsection {* Uniqueness of inf and sup *}

lemma (in lower_semilattice) inf_unique:
  fixes f (infixl "\<triangle>" 70)
  assumes le1: "\<And>x y. x \<triangle> y \<le> x" and le2: "\<And>x y. x \<triangle> y \<le> y"
  and greatest: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<triangle> z"
  shows "x \<sqinter> y = x \<triangle> y"
proof (rule antisym)
  show "x \<triangle> y \<le> x \<sqinter> y" by (rule le_infI) (rule le1, rule le2)
next
  have leI: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<triangle> z" by (blast intro: greatest)
  show "x \<sqinter> y \<le> x \<triangle> y" by (rule leI) simp_all
qed

lemma (in upper_semilattice) sup_unique:
  fixes f (infixl "\<nabla>" 70)
  assumes ge1 [simp]: "\<And>x y. x \<le> x \<nabla> y" and ge2: "\<And>x y. y \<le> x \<nabla> y"
  and least: "\<And>x y z. y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<nabla> z \<le> x"
  shows "x \<squnion> y = x \<nabla> y"
proof (rule antisym)
  show "x \<squnion> y \<le> x \<nabla> y" by (rule le_supI) (rule ge1, rule ge2)
next
  have leI: "\<And>x y z. x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x \<nabla> y \<le> z" by (blast intro: least)
  show "x \<nabla> y \<le> x \<squnion> y" by (rule leI) simp_all
qed
  

subsection {* @{const min}/@{const max} on linear orders as
  special case of @{const inf}/@{const sup} *}

lemma (in linorder) distrib_lattice_min_max:
  "distrib_lattice (op \<le>) (op <) min max"
proof unfold_locales
  have aux: "\<And>x y \<Colon> 'a. x < y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp add: less_le antisym)
  fix x y z
  show "max x (min y z) = min (max x y) (max x z)"
  unfolding min_def max_def
  by auto
qed (auto simp add: min_def max_def not_le less_imp_le)

interpretation min_max:
  distrib_lattice ["op \<le> \<Colon> 'a\<Colon>linorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" min max]
  by (rule distrib_lattice_min_max)

lemma inf_min: "inf = (min \<Colon> 'a\<Colon>{lower_semilattice, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (rule ext)+ auto

lemma sup_max: "sup = (max \<Colon> 'a\<Colon>{upper_semilattice, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (rule ext)+ auto

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2
 
lemmas max_ac = min_max.sup_assoc min_max.sup_commute
  mk_left_commute [of max, OF min_max.sup_assoc min_max.sup_commute]

lemmas min_ac = min_max.inf_assoc min_max.inf_commute
  mk_left_commute [of min, OF min_max.inf_assoc min_max.inf_commute]

text {*
  Now we have inherited antisymmetry as an intro-rule on all
  linear orders. This is a problem because it applies to bool, which is
  undesirable.
*}

lemmas [rule del] = min_max.antisym_intro min_max.le_infI min_max.le_supI
  min_max.le_supE min_max.le_infE min_max.le_supI1 min_max.le_supI2
  min_max.le_infI1 min_max.le_infI2


subsection {* Complete lattices *}

class complete_lattice = lattice +
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)
    and Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> x"
     and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>A \<sqsubseteq> z"
begin

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<le> a}"
  by (auto intro: Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<le> b}"
  by (auto intro: Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Inf_Univ: "\<Sqinter>UNIV = \<Squnion>{}"
  unfolding Sup_Inf by auto

lemma Sup_Univ: "\<Squnion>UNIV = \<Sqinter>{}"
  unfolding Inf_Sup by auto

lemma Inf_insert: "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
  apply (rule antisym)
  apply (rule le_infI)
  apply (rule Inf_lower)
  apply simp
  apply (rule Inf_greatest)
  apply (rule Inf_lower)
  apply simp
  apply (rule Inf_greatest)
  apply (erule insertE)
  apply (rule le_infI1)
  apply simp
  apply (rule le_infI2)
  apply (erule Inf_lower)
  done

lemma Sup_insert: "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
  apply (rule antisym)
  apply (rule Sup_least)
  apply (erule insertE)
  apply (rule le_supI1)
  apply simp
  apply (rule le_supI2)
  apply (erule Sup_upper)
  apply (rule le_supI)
  apply (rule Sup_upper)
  apply simp
  apply (rule Sup_least)
  apply (rule Sup_upper)
  apply simp
  done

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
  by (simp add: Inf_insert_simp)

lemma Sup_binary:
  "\<Squnion>{a, b} = a \<squnion> b"
  by (simp add: Sup_insert_simp)

definition
  top :: 'a
where
  "top = Inf {}"

definition
  bot :: 'a
where
  "bot = Sup {}"

lemma top_greatest [simp]: "x \<le> top"
  by (unfold top_def, rule Inf_greatest, simp)

lemma bot_least [simp]: "bot \<le> x"
  by (unfold bot_def, rule Sup_least, simp)

definition
  SUPR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "SUPR A f == Sup (f ` A)"

definition
  INFI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "INFI A f == Inf (f ` A)"

end

syntax
  "_SUP1"     :: "pttrns => 'b => 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn => 'a set => 'b => 'b"  ("(3SUP _:_./ _)" [0, 10] 10)
  "_INF1"     :: "pttrns => 'b => 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn => 'a set => 'b => 'b"  ("(3INF _:_./ _)" [0, 10] 10)

translations
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR UNIV (%x. B)"
  "SUP x. B"     == "SUP x:UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI UNIV (%x. B)"
  "INF x. B"     == "INF x:UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"

(* To avoid eta-contraction of body: *)
print_translation {*
let
  fun btr' syn (A :: Abs abs :: ts) =
    let val (x,t) = atomic_abs_tr' abs
    in list_comb (Syntax.const syn $ x $ A $ t, ts) end
  val const_syntax_name = Sign.const_syntax_name @{theory} o fst o dest_Const
in
[(const_syntax_name @{term SUPR}, btr' "_SUP"),(const_syntax_name @{term "INFI"}, btr' "_INF")]
end
*}

lemma le_SUPI: "i : A \<Longrightarrow> M i \<le> (SUP i:A. M i)"
  by (auto simp add: SUPR_def intro: Sup_upper)

lemma SUP_leI: "(\<And>i. i : A \<Longrightarrow> M i \<le> u) \<Longrightarrow> (SUP i:A. M i) \<le> u"
  by (auto simp add: SUPR_def intro: Sup_least)

lemma INF_leI: "i : A \<Longrightarrow> (INF i:A. M i) \<le> M i"
  by (auto simp add: INFI_def intro: Inf_lower)

lemma le_INFI: "(\<And>i. i : A \<Longrightarrow> u \<le> M i) \<Longrightarrow> u \<le> (INF i:A. M i)"
  by (auto simp add: INFI_def intro: Inf_greatest)

lemma SUP_const[simp]: "A \<noteq> {} \<Longrightarrow> (SUP i:A. M) = M"
  by (auto intro: order_antisym SUP_leI le_SUPI)

lemma INF_const[simp]: "A \<noteq> {} \<Longrightarrow> (INF i:A. M) = M"
  by (auto intro: order_antisym INF_leI le_INFI)


subsection {* Bool as lattice *}

instance bool :: distrib_lattice
  inf_bool_eq: "inf P Q \<equiv> P \<and> Q"
  sup_bool_eq: "sup P Q \<equiv> P \<or> Q"
  by intro_classes (auto simp add: inf_bool_eq sup_bool_eq le_bool_def)

instance bool :: complete_lattice
  Inf_bool_def: "Inf A \<equiv> \<forall>x\<in>A. x"
  Sup_bool_def: "Sup A \<equiv> \<exists>x\<in>A. x"
  by intro_classes (auto simp add: Inf_bool_def Sup_bool_def le_bool_def)

lemma Inf_empty_bool [simp]:
  "Inf {}"
  unfolding Inf_bool_def by auto

lemma not_Sup_empty_bool [simp]:
  "\<not> Sup {}"
  unfolding Sup_bool_def by auto

lemma top_bool_eq: "top = True"
  by (iprover intro!: order_antisym le_boolI top_greatest)

lemma bot_bool_eq: "bot = False"
  by (iprover intro!: order_antisym le_boolI bot_least)


subsection {* Set as lattice *}

instance set :: (type) distrib_lattice
  inf_set_eq: "inf A B \<equiv> A \<inter> B"
  sup_set_eq: "sup A B \<equiv> A \<union> B"
  by intro_classes (auto simp add: inf_set_eq sup_set_eq)

lemmas [code func del] = inf_set_eq sup_set_eq

lemma mono_Int: "mono f \<Longrightarrow> f (A \<inter> B) \<subseteq> f A \<inter> f B"
  apply (fold inf_set_eq sup_set_eq)
  apply (erule mono_inf)
  done

lemma mono_Un: "mono f \<Longrightarrow> f A \<union> f B \<subseteq> f (A \<union> B)"
  apply (fold inf_set_eq sup_set_eq)
  apply (erule mono_sup)
  done

instance set :: (type) complete_lattice
  Inf_set_def: "Inf S \<equiv> \<Inter>S"
  Sup_set_def: "Sup S \<equiv> \<Union>S"
  by intro_classes (auto simp add: Inf_set_def Sup_set_def)

lemmas [code func del] = Inf_set_def Sup_set_def

lemma top_set_eq: "top = UNIV"
  by (iprover intro!: subset_antisym subset_UNIV top_greatest)

lemma bot_set_eq: "bot = {}"
  by (iprover intro!: subset_antisym empty_subsetI bot_least)


subsection {* Fun as lattice *}

instance "fun" :: (type, lattice) lattice
  inf_fun_eq: "inf f g \<equiv> (\<lambda>x. inf (f x) (g x))"
  sup_fun_eq: "sup f g \<equiv> (\<lambda>x. sup (f x) (g x))"
apply intro_classes
unfolding inf_fun_eq sup_fun_eq
apply (auto intro: le_funI)
apply (rule le_funI)
apply (auto dest: le_funD)
apply (rule le_funI)
apply (auto dest: le_funD)
done

lemmas [code func del] = inf_fun_eq sup_fun_eq

instance "fun" :: (type, distrib_lattice) distrib_lattice
  by default (auto simp add: inf_fun_eq sup_fun_eq sup_inf_distrib1)

instance "fun" :: (type, complete_lattice) complete_lattice
  Inf_fun_def: "Inf A \<equiv> (\<lambda>x. Inf {y. \<exists>f\<in>A. y = f x})"
  Sup_fun_def: "Sup A \<equiv> (\<lambda>x. Sup {y. \<exists>f\<in>A. y = f x})"
  by intro_classes
    (auto simp add: Inf_fun_def Sup_fun_def le_fun_def
      intro: Inf_lower Sup_upper Inf_greatest Sup_least)

lemmas [code func del] = Inf_fun_def Sup_fun_def

lemma Inf_empty_fun:
  "Inf {} = (\<lambda>_. Inf {})"
  by rule (auto simp add: Inf_fun_def)

lemma Sup_empty_fun:
  "Sup {} = (\<lambda>_. Sup {})"
  by rule (auto simp add: Sup_fun_def)

lemma top_fun_eq: "top = (\<lambda>x. top)"
  by (iprover intro!: order_antisym le_funI top_greatest)

lemma bot_fun_eq: "bot = (\<lambda>x. bot)"
  by (iprover intro!: order_antisym le_funI bot_least)


text {* redundant bindings *}

lemmas inf_aci = inf_ACI
lemmas sup_aci = sup_ACI

no_notation
  inf (infixl "\<sqinter>" 70)

no_notation
  sup (infixl "\<squnion>" 65)

no_notation
  Inf ("\<Sqinter>_" [900] 900)

no_notation
  Sup ("\<Squnion>_" [900] 900)

end
