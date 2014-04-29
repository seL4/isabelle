(*  Title:      HOL/Library/Finite_Lattice.thy
    Author:     Alessandro Coglio
*)

theory Finite_Lattice
imports Product_Order
begin

text {* A non-empty finite lattice is a complete lattice.
Since types are never empty in Isabelle/HOL,
a type of classes @{class finite} and @{class lattice}
should also have class @{class complete_lattice}.
A type class is defined
that extends classes @{class finite} and @{class lattice}
with the operators @{const bot}, @{const top}, @{const Inf}, and @{const Sup},
along with assumptions that define these operators
in terms of the ones of classes @{class finite} and @{class lattice}.
The resulting class is a subclass of @{class complete_lattice}. *}

class finite_lattice_complete = finite + lattice + bot + top + Inf + Sup +
  assumes bot_def: "bot = Inf_fin UNIV"
  assumes top_def: "top = Sup_fin UNIV"
  assumes Inf_def: "Inf A = Finite_Set.fold inf top A"
  assumes Sup_def: "Sup A = Finite_Set.fold sup bot A"

text {* The definitional assumptions
on the operators @{const bot} and @{const top}
of class @{class finite_lattice_complete}
ensure that they yield bottom and top. *}

lemma finite_lattice_complete_bot_least: "(bot::'a::finite_lattice_complete) \<le> x"
  by (auto simp: bot_def intro: Inf_fin.coboundedI)

instance finite_lattice_complete \<subseteq> order_bot
  by default (auto simp: finite_lattice_complete_bot_least)

lemma finite_lattice_complete_top_greatest: "(top::'a::finite_lattice_complete) \<ge> x"
  by (auto simp: top_def Sup_fin.coboundedI)

instance finite_lattice_complete \<subseteq> order_top
  by default (auto simp: finite_lattice_complete_top_greatest)

instance finite_lattice_complete \<subseteq> bounded_lattice ..

text {* The definitional assumptions
on the operators @{const Inf} and @{const Sup}
of class @{class finite_lattice_complete}
ensure that they yield infimum and supremum. *}

lemma finite_lattice_complete_Inf_empty: "Inf {} = (top :: 'a::finite_lattice_complete)"
  by (simp add: Inf_def)

lemma finite_lattice_complete_Sup_empty: "Sup {} = (bot :: 'a::finite_lattice_complete)"
  by (simp add: Sup_def)

lemma finite_lattice_complete_Inf_insert:
  fixes A :: "'a::finite_lattice_complete set"
  shows "Inf (insert x A) = inf x (Inf A)"
proof -
  interpret comp_fun_idem "inf :: 'a \<Rightarrow> _"
    by (fact comp_fun_idem_inf)
  show ?thesis by (simp add: Inf_def)
qed

lemma finite_lattice_complete_Sup_insert:
  fixes A :: "'a::finite_lattice_complete set"
  shows "Sup (insert x A) = sup x (Sup A)"
proof -
  interpret comp_fun_idem "sup :: 'a \<Rightarrow> _"
    by (fact comp_fun_idem_sup)
  show ?thesis by (simp add: Sup_def)
qed

lemma finite_lattice_complete_Inf_lower:
  "(x::'a::finite_lattice_complete) \<in> A \<Longrightarrow> Inf A \<le> x"
  using finite [of A]
  by (induct A) (auto simp add: finite_lattice_complete_Inf_insert intro: le_infI2)

lemma finite_lattice_complete_Inf_greatest:
  "\<forall>x::'a::finite_lattice_complete \<in> A. z \<le> x \<Longrightarrow> z \<le> Inf A"
  using finite [of A]
  by (induct A) (auto simp add: finite_lattice_complete_Inf_empty finite_lattice_complete_Inf_insert)

lemma finite_lattice_complete_Sup_upper:
  "(x::'a::finite_lattice_complete) \<in> A \<Longrightarrow> Sup A \<ge> x"
  using finite [of A]
  by (induct A) (auto simp add: finite_lattice_complete_Sup_insert intro: le_supI2)

lemma finite_lattice_complete_Sup_least:
  "\<forall>x::'a::finite_lattice_complete \<in> A. z \<ge> x \<Longrightarrow> z \<ge> Sup A"
  using finite [of A]
  by (induct A) (auto simp add: finite_lattice_complete_Sup_empty finite_lattice_complete_Sup_insert)

instance finite_lattice_complete \<subseteq> complete_lattice
proof
qed (auto simp:
  finite_lattice_complete_Inf_lower
  finite_lattice_complete_Inf_greatest
  finite_lattice_complete_Sup_upper
  finite_lattice_complete_Sup_least
  finite_lattice_complete_Inf_empty
  finite_lattice_complete_Sup_empty)

text {* The product of two finite lattices is already a finite lattice. *}

lemma finite_bot_prod:
  "(bot :: ('a::finite_lattice_complete \<times> 'b::finite_lattice_complete)) =
    Inf_fin UNIV"
  by (metis Inf_fin.coboundedI UNIV_I bot.extremum_uniqueI finite_UNIV)

lemma finite_top_prod:
  "(top :: ('a::finite_lattice_complete \<times> 'b::finite_lattice_complete)) =
    Sup_fin UNIV"
  by (metis Sup_fin.coboundedI UNIV_I top.extremum_uniqueI finite_UNIV)

lemma finite_Inf_prod:
  "Inf(A :: ('a::finite_lattice_complete \<times> 'b::finite_lattice_complete) set) =
    Finite_Set.fold inf top A"
  by (metis Inf_fold_inf finite_code)

lemma finite_Sup_prod:
  "Sup (A :: ('a::finite_lattice_complete \<times> 'b::finite_lattice_complete) set) =
    Finite_Set.fold sup bot A"
  by (metis Sup_fold_sup finite_code)

instance prod :: (finite_lattice_complete, finite_lattice_complete) finite_lattice_complete
  by default (auto simp: finite_bot_prod finite_top_prod finite_Inf_prod finite_Sup_prod)

text {* Functions with a finite domain and with a finite lattice as codomain
already form a finite lattice. *}

lemma finite_bot_fun: "(bot :: ('a::finite \<Rightarrow> 'b::finite_lattice_complete)) = Inf_fin UNIV"
  by (metis Inf_UNIV Inf_fin_Inf empty_not_UNIV finite_code)

lemma finite_top_fun: "(top :: ('a::finite \<Rightarrow> 'b::finite_lattice_complete)) = Sup_fin UNIV"
  by (metis Sup_UNIV Sup_fin_Sup empty_not_UNIV finite_code)

lemma finite_Inf_fun:
  "Inf (A::('a::finite \<Rightarrow> 'b::finite_lattice_complete) set) =
    Finite_Set.fold inf top A"
  by (metis Inf_fold_inf finite_code)

lemma finite_Sup_fun:
  "Sup (A::('a::finite \<Rightarrow> 'b::finite_lattice_complete) set) =
    Finite_Set.fold sup bot A"
  by (metis Sup_fold_sup finite_code)

instance "fun" :: (finite, finite_lattice_complete) finite_lattice_complete
  by default (auto simp: finite_bot_fun finite_top_fun finite_Inf_fun finite_Sup_fun)


subsection {* Finite Distributive Lattices *}

text {* A finite distributive lattice is a complete lattice
whose @{const inf} and @{const sup} operators
distribute over @{const Sup} and @{const Inf}. *}

class finite_distrib_lattice_complete =
  distrib_lattice + finite_lattice_complete

lemma finite_distrib_lattice_complete_sup_Inf:
  "sup (x::'a::finite_distrib_lattice_complete) (Inf A) = (INF y:A. sup x y)"
  using finite
  by (induct A rule: finite_induct) (simp_all add: sup_inf_distrib1)

lemma finite_distrib_lattice_complete_inf_Sup:
  "inf (x::'a::finite_distrib_lattice_complete) (Sup A) = (SUP y:A. inf x y)"
  apply (rule finite_induct)
  apply (metis finite_code)
  apply (metis SUP_empty Sup_empty inf_bot_right)
  apply (metis SUP_insert Sup_insert inf_sup_distrib1)
  done

instance finite_distrib_lattice_complete \<subseteq> complete_distrib_lattice
proof
qed (auto simp:
  finite_distrib_lattice_complete_sup_Inf
  finite_distrib_lattice_complete_inf_Sup)

text {* The product of two finite distributive lattices
is already a finite distributive lattice. *}

instance prod ::
  (finite_distrib_lattice_complete, finite_distrib_lattice_complete)
  finite_distrib_lattice_complete
  ..

text {* Functions with a finite domain
and with a finite distributive lattice as codomain
already form a finite distributive lattice. *}

instance "fun" ::
  (finite, finite_distrib_lattice_complete) finite_distrib_lattice_complete
  ..


subsection {* Linear Orders *}

text {* A linear order is a distributive lattice.
A type class is defined
that extends class @{class linorder}
with the operators @{const inf} and @{const sup},
along with assumptions that define these operators
in terms of the ones of class @{class linorder}.
The resulting class is a subclass of @{class distrib_lattice}. *}

class linorder_lattice = linorder + inf + sup +
  assumes inf_def: "inf x y = (if x \<le> y then x else y)"
  assumes sup_def: "sup x y = (if x \<ge> y then x else y)"

text {* The definitional assumptions
on the operators @{const inf} and @{const sup}
of class @{class linorder_lattice}
ensure that they yield infimum and supremum
and that they distribute over each other. *}

lemma linorder_lattice_inf_le1: "inf (x::'a::linorder_lattice) y \<le> x"
  unfolding inf_def by (metis (full_types) linorder_linear)

lemma linorder_lattice_inf_le2: "inf (x::'a::linorder_lattice) y \<le> y"
  unfolding inf_def by (metis (full_types) linorder_linear)

lemma linorder_lattice_inf_greatest:
  "(x::'a::linorder_lattice) \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
  unfolding inf_def by (metis (full_types))

lemma linorder_lattice_sup_ge1: "sup (x::'a::linorder_lattice) y \<ge> x"
  unfolding sup_def by (metis (full_types) linorder_linear)

lemma linorder_lattice_sup_ge2: "sup (x::'a::linorder_lattice) y \<ge> y"
  unfolding sup_def by (metis (full_types) linorder_linear)

lemma linorder_lattice_sup_least:
  "(x::'a::linorder_lattice) \<ge> y \<Longrightarrow> x \<ge> z \<Longrightarrow> x \<ge> sup y z"
  by (auto simp: sup_def)

lemma linorder_lattice_sup_inf_distrib1:
  "sup (x::'a::linorder_lattice) (inf y z) = inf (sup x y) (sup x z)"
  by (auto simp: inf_def sup_def)

instance linorder_lattice \<subseteq> distrib_lattice
proof
qed (auto simp:
  linorder_lattice_inf_le1
  linorder_lattice_inf_le2
  linorder_lattice_inf_greatest
  linorder_lattice_sup_ge1
  linorder_lattice_sup_ge2
  linorder_lattice_sup_least
  linorder_lattice_sup_inf_distrib1)


subsection {* Finite Linear Orders *}

text {* A (non-empty) finite linear order is a complete linear order. *}

class finite_linorder_complete = linorder_lattice + finite_lattice_complete

instance finite_linorder_complete \<subseteq> complete_linorder ..

text {* A (non-empty) finite linear order is a complete lattice
whose @{const inf} and @{const sup} operators
distribute over @{const Sup} and @{const Inf}. *}

instance finite_linorder_complete \<subseteq> finite_distrib_lattice_complete ..

end

