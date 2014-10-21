(*  Title:      HOL/Hahn_Banach/Function_Order.thy
    Author:     Gertrud Bauer, TU Munich
*)

header \<open>An order on functions\<close>

theory Function_Order
imports Subspace Linearform
begin

subsection \<open>The graph of a function\<close>

text \<open>
  We define the \emph{graph} of a (real) function @{text f} with
  domain @{text F} as the set
  \begin{center}
  @{text "{(x, f x). x \<in> F}"}
  \end{center}
  So we are modeling partial functions by specifying the domain and
  the mapping function. We use the term ``function'' also for its
  graph.
\<close>

type_synonym 'a graph = "('a \<times> real) set"

definition graph :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a graph"
  where "graph F f = {(x, f x) | x. x \<in> F}"

lemma graphI [intro]: "x \<in> F \<Longrightarrow> (x, f x) \<in> graph F f"
  unfolding graph_def by blast

lemma graphI2 [intro?]: "x \<in> F \<Longrightarrow> \<exists>t \<in> graph F f. t = (x, f x)"
  unfolding graph_def by blast

lemma graphE [elim?]:
  assumes "(x, y) \<in> graph F f"
  obtains "x \<in> F" and "y = f x"
  using assms unfolding graph_def by blast


subsection \<open>Functions ordered by domain extension\<close>

text \<open>
  A function @{text h'} is an extension of @{text h}, iff the graph of
  @{text h} is a subset of the graph of @{text h'}.
\<close>

lemma graph_extI:
  "(\<And>x. x \<in> H \<Longrightarrow> h x = h' x) \<Longrightarrow> H \<subseteq> H'
    \<Longrightarrow> graph H h \<subseteq> graph H' h'"
  unfolding graph_def by blast

lemma graph_extD1 [dest?]: "graph H h \<subseteq> graph H' h' \<Longrightarrow> x \<in> H \<Longrightarrow> h x = h' x"
  unfolding graph_def by blast

lemma graph_extD2 [dest?]: "graph H h \<subseteq> graph H' h' \<Longrightarrow> H \<subseteq> H'"
  unfolding graph_def by blast


subsection \<open>Domain and function of a graph\<close>

text \<open>
  The inverse functions to @{text graph} are @{text domain} and @{text
  funct}.
\<close>

definition domain :: "'a graph \<Rightarrow> 'a set"
  where "domain g = {x. \<exists>y. (x, y) \<in> g}"

definition funct :: "'a graph \<Rightarrow> ('a \<Rightarrow> real)"
  where "funct g = (\<lambda>x. (SOME y. (x, y) \<in> g))"

text \<open>
  The following lemma states that @{text g} is the graph of a function
  if the relation induced by @{text g} is unique.
\<close>

lemma graph_domain_funct:
  assumes uniq: "\<And>x y z. (x, y) \<in> g \<Longrightarrow> (x, z) \<in> g \<Longrightarrow> z = y"
  shows "graph (domain g) (funct g) = g"
  unfolding domain_def funct_def graph_def
proof auto  (* FIXME !? *)
  fix a b assume g: "(a, b) \<in> g"
  from g show "(a, SOME y. (a, y) \<in> g) \<in> g" by (rule someI2)
  from g show "\<exists>y. (a, y) \<in> g" ..
  from g show "b = (SOME y. (a, y) \<in> g)"
  proof (rule some_equality [symmetric])
    fix y assume "(a, y) \<in> g"
    with g show "y = b" by (rule uniq)
  qed
qed


subsection \<open>Norm-preserving extensions of a function\<close>

text \<open>
  Given a linear form @{text f} on the space @{text F} and a seminorm
  @{text p} on @{text E}. The set of all linear extensions of @{text
  f}, to superspaces @{text H} of @{text F}, which are bounded by
  @{text p}, is defined as follows.
\<close>

definition
  norm_pres_extensions ::
    "'a::{plus, minus, uminus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real)
      \<Rightarrow> 'a graph set"
where
  "norm_pres_extensions E p F f
    = {g. \<exists>H h. g = graph H h
        \<and> linearform H h
        \<and> H \<unlhd> E
        \<and> F \<unlhd> H
        \<and> graph F f \<subseteq> graph H h
        \<and> (\<forall>x \<in> H. h x \<le> p x)}"

lemma norm_pres_extensionE [elim]:
  assumes "g \<in> norm_pres_extensions E p F f"
  obtains H h
    where "g = graph H h"
    and "linearform H h"
    and "H \<unlhd> E"
    and "F \<unlhd> H"
    and "graph F f \<subseteq> graph H h"
    and "\<forall>x \<in> H. h x \<le> p x"
  using assms unfolding norm_pres_extensions_def by blast

lemma norm_pres_extensionI2 [intro]:
  "linearform H h \<Longrightarrow> H \<unlhd> E \<Longrightarrow> F \<unlhd> H
    \<Longrightarrow> graph F f \<subseteq> graph H h \<Longrightarrow> \<forall>x \<in> H. h x \<le> p x
    \<Longrightarrow> graph H h \<in> norm_pres_extensions E p F f"
  unfolding norm_pres_extensions_def by blast

lemma norm_pres_extensionI:  (* FIXME ? *)
  "\<exists>H h. g = graph H h
    \<and> linearform H h
    \<and> H \<unlhd> E
    \<and> F \<unlhd> H
    \<and> graph F f \<subseteq> graph H h
    \<and> (\<forall>x \<in> H. h x \<le> p x) \<Longrightarrow> g \<in> norm_pres_extensions E p F f"
  unfolding norm_pres_extensions_def by blast

end
