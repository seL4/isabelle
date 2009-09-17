(*  Title:      HOL/Lattices.thy
    Author:     Tobias Nipkow
*)

header {* Abstract lattices *}

theory Lattices
imports Orderings
begin

subsection {* Lattices *}

notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less  (infix "\<sqsubset>" 50) and
  top ("\<top>") and
  bot ("\<bottom>")

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
begin

text {* Dual lattice *}

lemma dual_semilattice:
  "lower_semilattice (op \<ge>) (op >) sup"
by (rule lower_semilattice.intro, rule dual_order)
  (unfold_locales, simp_all add: sup_least)

end

class lattice = lower_semilattice + upper_semilattice


subsubsection {* Intro and elim rules*}

context lower_semilattice
begin

lemma le_infI1:
  "a \<sqsubseteq> x \<Longrightarrow> a \<sqinter> b \<sqsubseteq> x"
  by (rule order_trans) auto

lemma le_infI2:
  "b \<sqsubseteq> x \<Longrightarrow> a \<sqinter> b \<sqsubseteq> x"
  by (rule order_trans) auto

lemma le_infI: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<sqinter> b"
  by (blast intro: inf_greatest)

lemma le_infE: "x \<sqsubseteq> a \<sqinter> b \<Longrightarrow> (x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans le_infI1 le_infI2)

lemma le_inf_iff [simp]:
  "x \<sqsubseteq> y \<sqinter> z \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<sqsubseteq> z"
  by (blast intro: le_infI elim: le_infE)

lemma le_iff_inf:
  "x \<sqsubseteq> y \<longleftrightarrow> x \<sqinter> y = x"
  by (auto intro: le_infI1 antisym dest: eq_iff [THEN iffD1])

lemma mono_inf:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>lower_semilattice"
  shows "mono f \<Longrightarrow> f (A \<sqinter> B) \<le> f A \<sqinter> f B"
  by (auto simp add: mono_def intro: Lattices.inf_greatest)

end

context upper_semilattice
begin

lemma le_supI1:
  "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto

lemma le_supI2:
  "x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto 

lemma le_supI:
  "a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> a \<squnion> b \<sqsubseteq> x"
  by (blast intro: sup_least)

lemma le_supE:
  "a \<squnion> b \<sqsubseteq> x \<Longrightarrow> (a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: le_supI1 le_supI2 order_trans)

lemma le_sup_iff [simp]:
  "x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  by (blast intro: le_supI elim: le_supE)

lemma le_iff_sup:
  "x \<sqsubseteq> y \<longleftrightarrow> x \<squnion> y = y"
  by (auto intro: le_supI2 antisym dest: eq_iff [THEN iffD1])

lemma mono_sup:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>upper_semilattice"
  shows "mono f \<Longrightarrow> f A \<squnion> f B \<le> f (A \<squnion> B)"
  by (auto simp add: mono_def intro: Lattices.sup_least)

end


subsubsection {* Equational laws *}

context lower_semilattice
begin

lemma inf_commute: "(x \<sqinter> y) = (y \<sqinter> x)"
  by (rule antisym) auto

lemma inf_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  by (rule antisym) (auto intro: le_infI1 le_infI2)

lemma inf_idem[simp]: "x \<sqinter> x = x"
  by (rule antisym) auto

lemma inf_left_idem[simp]: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
  by (rule antisym) (auto intro: le_infI2)

lemma inf_absorb1[simp]: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
  by (rule antisym) auto

lemma inf_absorb2[simp]: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
  by (rule antisym) auto

lemma inf_left_commute: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)"
  by (rule mk_left_commute [of inf]) (fact inf_assoc inf_commute)+
  
lemmas inf_aci = inf_commute inf_assoc inf_left_commute inf_left_idem

end

context upper_semilattice
begin

lemma sup_commute: "(x \<squnion> y) = (y \<squnion> x)"
  by (rule antisym) auto

lemma sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  by (rule antisym) (auto intro: le_supI1 le_supI2)

lemma sup_idem[simp]: "x \<squnion> x = x"
  by (rule antisym) auto

lemma sup_left_idem[simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
  by (rule antisym) (auto intro: le_supI2)

lemma sup_absorb1[simp]: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  by (rule antisym) auto

lemma sup_absorb2[simp]: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  by (rule antisym) auto

lemma sup_left_commute: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
  by (rule mk_left_commute [of sup]) (fact sup_assoc sup_commute)+

lemmas sup_aci = sup_commute sup_assoc sup_left_commute sup_left_idem

end

context lattice
begin

lemma dual_lattice:
  "lattice (op \<ge>) (op >) sup inf"
  by (rule lattice.intro, rule dual_semilattice, rule upper_semilattice.intro, rule dual_order)
    (unfold_locales, auto)

lemma inf_sup_absorb: "x \<sqinter> (x \<squnion> y) = x"
  by (blast intro: antisym inf_le1 inf_greatest sup_ge1)

lemma sup_inf_absorb: "x \<squnion> (x \<sqinter> y) = x"
  by (blast intro: antisym sup_ge1 sup_least inf_le1)

lemmas inf_sup_aci = inf_aci sup_aci

lemmas inf_sup_ord = inf_le1 inf_le2 sup_ge1 sup_ge2

text{* Towards distributivity *}

lemma distrib_sup_le: "x \<squnion> (y \<sqinter> z) \<sqsubseteq> (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  by (auto intro: le_infI1 le_infI2 le_supI1 le_supI2)

lemma distrib_inf_le: "(x \<sqinter> y) \<squnion> (x \<sqinter> z) \<sqsubseteq> x \<sqinter> (y \<squnion> z)"
  by (auto intro: le_infI1 le_infI2 le_supI1 le_supI2)

text{* If you have one of them, you have them all. *}

lemma distrib_imp1:
assumes D: "!!x y z. x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
shows "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof-
  have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)" by(simp add:sup_inf_absorb)
  also have "\<dots> = x \<squnion> (z \<sqinter> (x \<squnion> y))" by(simp add:D inf_commute sup_assoc del:sup_absorb1)
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
  also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))" by(simp add:D sup_commute inf_assoc del:inf_absorb1)
  also have "\<dots> = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)"
    by(simp add:sup_inf_absorb sup_commute)
  also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by(simp add:D)
  finally show ?thesis .
qed

end

subsubsection {* Strict order *}

context lower_semilattice
begin

lemma less_infI1:
  "a \<sqsubset> x \<Longrightarrow> a \<sqinter> b \<sqsubset> x"
  by (auto simp add: less_le intro: le_infI1)

lemma less_infI2:
  "b \<sqsubset> x \<Longrightarrow> a \<sqinter> b \<sqsubset> x"
  by (auto simp add: less_le intro: le_infI2)

end

context upper_semilattice
begin

lemma less_supI1:
  "x < a \<Longrightarrow> x < a \<squnion> b"
proof -
  interpret dual: lower_semilattice "op \<ge>" "op >" sup
    by (fact dual_semilattice)
  assume "x < a"
  then show "x < a \<squnion> b"
    by (fact dual.less_infI1)
qed

lemma less_supI2:
  "x < b \<Longrightarrow> x < a \<squnion> b"
proof -
  interpret dual: lower_semilattice "op \<ge>" "op >" sup
    by (fact dual_semilattice)
  assume "x < b"
  then show "x < a \<squnion> b"
    by (fact dual.less_infI2)
qed

end


subsection {* Distributive lattices *}

class distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

context distrib_lattice
begin

lemma sup_inf_distrib2:
 "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
by(simp add: inf_sup_aci sup_inf_distrib1)

lemma inf_sup_distrib1:
 "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
by(rule distrib_imp2[OF sup_inf_distrib1])

lemma inf_sup_distrib2:
 "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
by(simp add: inf_sup_aci inf_sup_distrib1)

lemma dual_distrib_lattice:
  "distrib_lattice (op \<ge>) (op >) sup inf"
  by (rule distrib_lattice.intro, rule dual_lattice)
    (unfold_locales, fact inf_sup_distrib1)

lemmas distrib =
  sup_inf_distrib1 sup_inf_distrib2 inf_sup_distrib1 inf_sup_distrib2

end


subsection {* Boolean algebras *}

class boolean_algebra = distrib_lattice + top + bot + minus + uminus +
  assumes inf_compl_bot: "x \<sqinter> - x = bot"
    and sup_compl_top: "x \<squnion> - x = top"
  assumes diff_eq: "x - y = x \<sqinter> - y"
begin

lemma dual_boolean_algebra:
  "boolean_algebra (\<lambda>x y. x \<squnion> - y) uminus (op \<ge>) (op >) (op \<squnion>) (op \<sqinter>) top bot"
  by (rule boolean_algebra.intro, rule dual_distrib_lattice)
    (unfold_locales,
      auto simp add: inf_compl_bot sup_compl_top diff_eq less_le_not_le)

lemma compl_inf_bot:
  "- x \<sqinter> x = bot"
  by (simp add: inf_commute inf_compl_bot)

lemma compl_sup_top:
  "- x \<squnion> x = top"
  by (simp add: sup_commute sup_compl_top)

lemma inf_bot_left [simp]:
  "bot \<sqinter> x = bot"
  by (rule inf_absorb1) simp

lemma inf_bot_right [simp]:
  "x \<sqinter> bot = bot"
  by (rule inf_absorb2) simp

lemma sup_top_left [simp]:
  "top \<squnion> x = top"
  by (rule sup_absorb1) simp

lemma sup_top_right [simp]:
  "x \<squnion> top = top"
  by (rule sup_absorb2) simp

lemma inf_top_left [simp]:
  "top \<sqinter> x = x"
  by (rule inf_absorb2) simp

lemma inf_top_right [simp]:
  "x \<sqinter> top = x"
  by (rule inf_absorb1) simp

lemma sup_bot_left [simp]:
  "bot \<squnion> x = x"
  by (rule sup_absorb2) simp

lemma sup_bot_right [simp]:
  "x \<squnion> bot = x"
  by (rule sup_absorb1) simp

lemma inf_eq_top_eq1:
  assumes "A \<sqinter> B = \<top>"
  shows "A = \<top>"
proof (cases "B = \<top>")
  case True with assms show ?thesis by simp
next
  case False with top_greatest have "B < \<top>" by (auto intro: neq_le_trans)
  then have "A \<sqinter> B < \<top>" by (rule less_infI2)
  with assms show ?thesis by simp
qed

lemma inf_eq_top_eq2:
  assumes "A \<sqinter> B = \<top>"
  shows "B = \<top>"
  by (rule inf_eq_top_eq1, unfold inf_commute [of B]) (fact assms)

lemma sup_eq_bot_eq1:
  assumes "A \<squnion> B = \<bottom>"
  shows "A = \<bottom>"
proof -
  interpret dual: boolean_algebra "\<lambda>x y. x \<squnion> - y" uminus "op \<ge>" "op >" "op \<squnion>" "op \<sqinter>" top bot
    by (rule dual_boolean_algebra)
  from dual.inf_eq_top_eq1 assms show ?thesis .
qed

lemma sup_eq_bot_eq2:
  assumes "A \<squnion> B = \<bottom>"
  shows "B = \<bottom>"
proof -
  interpret dual: boolean_algebra "\<lambda>x y. x \<squnion> - y" uminus "op \<ge>" "op >" "op \<squnion>" "op \<sqinter>" top bot
    by (rule dual_boolean_algebra)
  from dual.inf_eq_top_eq2 assms show ?thesis .
qed

lemma compl_unique:
  assumes "x \<sqinter> y = bot"
    and "x \<squnion> y = top"
  shows "- x = y"
proof -
  have "(x \<sqinter> - x) \<squnion> (- x \<sqinter> y) = (x \<sqinter> y) \<squnion> (- x \<sqinter> y)"
    using inf_compl_bot assms(1) by simp
  then have "(- x \<sqinter> x) \<squnion> (- x \<sqinter> y) = (y \<sqinter> x) \<squnion> (y \<sqinter> - x)"
    by (simp add: inf_commute)
  then have "- x \<sqinter> (x \<squnion> y) = y \<sqinter> (x \<squnion> - x)"
    by (simp add: inf_sup_distrib1)
  then have "- x \<sqinter> top = y \<sqinter> top"
    using sup_compl_top assms(2) by simp
  then show "- x = y" by (simp add: inf_top_right)
qed

lemma double_compl [simp]:
  "- (- x) = x"
  using compl_inf_bot compl_sup_top by (rule compl_unique)

lemma compl_eq_compl_iff [simp]:
  "- x = - y \<longleftrightarrow> x = y"
proof
  assume "- x = - y"
  then have "- x \<sqinter> y = bot"
    and "- x \<squnion> y = top"
    by (simp_all add: compl_inf_bot compl_sup_top)
  then have "- (- x) = y" by (rule compl_unique)
  then show "x = y" by simp
next
  assume "x = y"
  then show "- x = - y" by simp
qed

lemma compl_bot_eq [simp]:
  "- bot = top"
proof -
  from sup_compl_top have "bot \<squnion> - bot = top" .
  then show ?thesis by simp
qed

lemma compl_top_eq [simp]:
  "- top = bot"
proof -
  from inf_compl_bot have "top \<sqinter> - top = bot" .
  then show ?thesis by simp
qed

lemma compl_inf [simp]:
  "- (x \<sqinter> y) = - x \<squnion> - y"
proof (rule compl_unique)
  have "(x \<sqinter> y) \<sqinter> (- x \<squnion> - y) = ((x \<sqinter> y) \<sqinter> - x) \<squnion> ((x \<sqinter> y) \<sqinter> - y)"
    by (rule inf_sup_distrib1)
  also have "... = (y \<sqinter> (x \<sqinter> - x)) \<squnion> (x \<sqinter> (y \<sqinter> - y))"
    by (simp only: inf_commute inf_assoc inf_left_commute)
  finally show "(x \<sqinter> y) \<sqinter> (- x \<squnion> - y) = bot"
    by (simp add: inf_compl_bot)
next
  have "(x \<sqinter> y) \<squnion> (- x \<squnion> - y) = (x \<squnion> (- x \<squnion> - y)) \<sqinter> (y \<squnion> (- x \<squnion> - y))"
    by (rule sup_inf_distrib2)
  also have "... = (- y \<squnion> (x \<squnion> - x)) \<sqinter> (- x \<squnion> (y \<squnion> - y))"
    by (simp only: sup_commute sup_assoc sup_left_commute)
  finally show "(x \<sqinter> y) \<squnion> (- x \<squnion> - y) = top"
    by (simp add: sup_compl_top)
qed

lemma compl_sup [simp]:
  "- (x \<squnion> y) = - x \<sqinter> - y"
proof -
  interpret boolean_algebra "\<lambda>x y. x \<squnion> - y" uminus "op \<ge>" "op >" "op \<squnion>" "op \<sqinter>" top bot
    by (rule dual_boolean_algebra)
  then show ?thesis by simp
qed

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

sublocale linorder < min_max!: distrib_lattice less_eq less min max
proof
  fix x y z
  show "max x (min y z) = min (max x y) (max x z)"
    by (auto simp add: min_def max_def)
qed (auto simp add: min_def max_def not_le less_imp_le)

lemma inf_min: "inf = (min \<Colon> 'a\<Colon>{lower_semilattice, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (rule ext)+ (auto intro: antisym)

lemma sup_max: "sup = (max \<Colon> 'a\<Colon>{upper_semilattice, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (rule ext)+ (auto intro: antisym)

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2
 
lemmas max_ac = min_max.sup_assoc min_max.sup_commute
  mk_left_commute [of max, OF min_max.sup_assoc min_max.sup_commute]

lemmas min_ac = min_max.inf_assoc min_max.inf_commute
  mk_left_commute [of min, OF min_max.inf_assoc min_max.inf_commute]


subsection {* Bool as lattice *}

instantiation bool :: boolean_algebra
begin

definition
  bool_Compl_def: "uminus = Not"

definition
  bool_diff_def: "A - B \<longleftrightarrow> A \<and> \<not> B"

definition
  inf_bool_eq: "P \<sqinter> Q \<longleftrightarrow> P \<and> Q"

definition
  sup_bool_eq: "P \<squnion> Q \<longleftrightarrow> P \<or> Q"

instance proof
qed (simp_all add: inf_bool_eq sup_bool_eq le_bool_def
  bot_bool_eq top_bool_eq bool_Compl_def bool_diff_def, auto)

end


subsection {* Fun as lattice *}

instantiation "fun" :: (type, lattice) lattice
begin

definition
  inf_fun_eq [code del]: "f \<sqinter> g = (\<lambda>x. f x \<sqinter> g x)"

definition
  sup_fun_eq [code del]: "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"

instance
apply intro_classes
unfolding inf_fun_eq sup_fun_eq
apply (auto intro: le_funI)
apply (rule le_funI)
apply (auto dest: le_funD)
apply (rule le_funI)
apply (auto dest: le_funD)
done

end

instance "fun" :: (type, distrib_lattice) distrib_lattice
proof
qed (auto simp add: inf_fun_eq sup_fun_eq sup_inf_distrib1)

instantiation "fun" :: (type, uminus) uminus
begin

definition
  fun_Compl_def: "- A = (\<lambda>x. - A x)"

instance ..

end

instantiation "fun" :: (type, minus) minus
begin

definition
  fun_diff_def: "A - B = (\<lambda>x. A x - B x)"

instance ..

end

instance "fun" :: (type, boolean_algebra) boolean_algebra
proof
qed (simp_all add: inf_fun_eq sup_fun_eq bot_fun_eq top_fun_eq fun_Compl_def fun_diff_def
  inf_compl_bot sup_compl_top diff_eq)


no_notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  top ("\<top>") and
  bot ("\<bottom>")

end
