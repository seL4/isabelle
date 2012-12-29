(* Author: Alessandro Coglio *)

theory Finite_Lattice
imports Product_Lattice
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
The resulting class is a subclass of @{class complete_lattice}.
Classes @{class bot} and @{class top} already include assumptions that suffice
to define the operators @{const bot} and @{const top} (as proved below),
and so no explicit assumptions on these two operators are needed
in the following type class.%
\footnote{The Isabelle/HOL library does not provide
syntactic classes for the operators @{const bot} and @{const top}.} *}

class finite_lattice_complete = finite + lattice + bot + top + Inf + Sup +
assumes Inf_def: "Inf A = Finite_Set.fold inf top A"
assumes Sup_def: "Sup A = Finite_Set.fold sup bot A"
-- "No explicit assumptions on @{const bot} or @{const top}."

instance finite_lattice_complete \<subseteq> bounded_lattice ..
-- "This subclass relation eases the proof of the next two lemmas."

lemma finite_lattice_complete_bot_def:
  "(bot::'a::finite_lattice_complete) = \<Sqinter>\<^bsub>fin\<^esub>UNIV"
by (metis finite_UNIV sup_Inf_absorb sup_bot_left iso_tuple_UNIV_I)
-- "Derived definition of @{const bot}."

lemma finite_lattice_complete_top_def:
  "(top::'a::finite_lattice_complete) = \<Squnion>\<^bsub>fin\<^esub>UNIV"
by (metis finite_UNIV inf_Sup_absorb inf_top_left iso_tuple_UNIV_I)
-- "Derived definition of @{const top}."

text {* The definitional assumptions
on the operators @{const Inf} and @{const Sup}
of class @{class finite_lattice_complete}
ensure that they yield infimum and supremum,
as required for a complete lattice. *}

lemma finite_lattice_complete_Inf_lower:
  "(x::'a::finite_lattice_complete) \<in> A \<Longrightarrow> Inf A \<le> x"
unfolding Inf_def by (metis finite_code le_inf_iff fold_inf_le_inf)

lemma finite_lattice_complete_Inf_greatest:
  "\<forall>x::'a::finite_lattice_complete \<in> A. z \<le> x \<Longrightarrow> z \<le> Inf A"
unfolding Inf_def by (metis finite_code inf_le_fold_inf inf_top_right)

lemma finite_lattice_complete_Sup_upper:
  "(x::'a::finite_lattice_complete) \<in> A \<Longrightarrow> Sup A \<ge> x"
unfolding Sup_def by (metis finite_code le_sup_iff sup_le_fold_sup)

lemma finite_lattice_complete_Sup_least:
  "\<forall>x::'a::finite_lattice_complete \<in> A. z \<ge> x \<Longrightarrow> z \<ge> Sup A"
unfolding Sup_def by (metis finite_code fold_sup_le_sup sup_bot_right)

instance finite_lattice_complete \<subseteq> complete_lattice
proof
qed (auto simp:
 finite_lattice_complete_Inf_lower
 finite_lattice_complete_Inf_greatest
 finite_lattice_complete_Sup_upper
 finite_lattice_complete_Sup_least)


text {* The product of two finite lattices is already a finite lattice. *}

lemma finite_Inf_prod:
  "Inf(A::('a::finite_lattice_complete \<times> 'b::finite_lattice_complete) set) =
  Finite_Set.fold inf top A"
by (metis Inf_fold_inf finite_code)

lemma finite_Sup_prod:
  "Sup (A::('a::finite_lattice_complete \<times> 'b::finite_lattice_complete) set) =
  Finite_Set.fold sup bot A"
by (metis Sup_fold_sup finite_code)

instance prod ::
  (finite_lattice_complete, finite_lattice_complete) finite_lattice_complete
proof qed (auto simp: finite_Inf_prod finite_Sup_prod)

text {* Functions with a finite domain and with a finite lattice as codomain
already form a finite lattice. *}

lemma finite_Inf_fun:
  "Inf (A::('a::finite \<Rightarrow> 'b::finite_lattice_complete) set) =
  Finite_Set.fold inf top A"
by (metis Inf_fold_inf finite_code)

lemma finite_Sup_fun:
  "Sup (A::('a::finite \<Rightarrow> 'b::finite_lattice_complete) set) =
  Finite_Set.fold sup bot A"
by (metis Sup_fold_sup finite_code)

instance "fun" :: (finite, finite_lattice_complete) finite_lattice_complete
proof qed (auto simp: finite_Inf_fun finite_Sup_fun)


subsection {* Finite Distributive Lattices *}

text {* A finite distributive lattice is a complete lattice
whose @{const inf} and @{const sup} operators
distribute over @{const Sup} and @{const Inf}. *}

class finite_distrib_lattice_complete =
  distrib_lattice + finite_lattice_complete

lemma finite_distrib_lattice_complete_sup_Inf:
  "sup (x::'a::finite_distrib_lattice_complete) (Inf A) = (INF y:A. sup x y)"
apply (rule finite_induct)
apply (metis finite_code)
apply (metis INF_empty Inf_empty sup_top_right)
apply (metis INF_insert Inf_insert sup_inf_distrib1)
done

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
Since in Isabelle/HOL
a subclass must have all the parameters of its superclasses,
class @{class linorder} cannot be a subclass of @{class distrib_lattice}.
So class @{class linorder} is extended with
the operators @{const inf} and @{const sup},
along with assumptions that define these operators
in terms of the ones of class @{class linorder}.
The resulting class is a subclass of @{class distrib_lattice}. *}

class linorder_lattice = linorder + inf + sup +
assumes inf_def: "inf x y = (if x \<le> y then x else y)"
assumes sup_def: "sup x y = (if x \<ge> y then x else y)"

text {* The definitional assumptions
on the operators @{const inf} and @{const sup}
of class @{class linorder_lattice}
ensure that they yield infimum and supremum,
and that they distribute over each other,
as required for a distributive lattice. *}

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
