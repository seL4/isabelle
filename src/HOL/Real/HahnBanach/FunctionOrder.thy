(*  Title:      HOL/Real/HahnBanach/FunctionOrder.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* An order on functions *}

theory FunctionOrder = Subspace + Linearform:

subsection {* The graph of a function *}

text {*
  We define the \emph{graph} of a (real) function @{text f} with
  domain @{text F} as the set
  \begin{center}
  @{text "{(x, f x). x \<in> F}"}
  \end{center}
  So we are modeling partial functions by specifying the domain and
  the mapping function. We use the term ``function'' also for its
  graph.
*}

types 'a graph = "('a \<times> real) set"

constdefs
  graph :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a graph"
  "graph F f \<equiv> {(x, f x) | x. x \<in> F}"

lemma graphI [intro]: "x \<in> F \<Longrightarrow> (x, f x) \<in> graph F f"
  by (unfold graph_def) blast

lemma graphI2 [intro?]: "x \<in> F \<Longrightarrow> \<exists>t \<in> graph F f. t = (x, f x)"
  by (unfold graph_def) blast

lemma graphE [elim?]:
    "(x, y) \<in> graph F f \<Longrightarrow> (x \<in> F \<Longrightarrow> y = f x \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold graph_def) blast


subsection {* Functions ordered by domain extension *}

text {*
  A function @{text h'} is an extension of @{text h}, iff the graph of
  @{text h} is a subset of the graph of @{text h'}.
*}

lemma graph_extI:
  "(\<And>x. x \<in> H \<Longrightarrow> h x = h' x) \<Longrightarrow> H \<subseteq> H'
    \<Longrightarrow> graph H h \<subseteq> graph H' h'"
  by (unfold graph_def) blast

lemma graph_extD1 [dest?]:
  "graph H h \<subseteq> graph H' h' \<Longrightarrow> x \<in> H \<Longrightarrow> h x = h' x"
  by (unfold graph_def) blast

lemma graph_extD2 [dest?]:
  "graph H h \<subseteq> graph H' h' \<Longrightarrow> H \<subseteq> H'"
  by (unfold graph_def) blast


subsection {* Domain and function of a graph *}

text {*
  The inverse functions to @{text graph} are @{text domain} and @{text
  funct}.
*}

constdefs
  "domain" :: "'a graph \<Rightarrow> 'a set"
  "domain g \<equiv> {x. \<exists>y. (x, y) \<in> g}"

  funct :: "'a graph \<Rightarrow> ('a \<Rightarrow> real)"
  "funct g \<equiv> \<lambda>x. (SOME y. (x, y) \<in> g)"

text {*
  The following lemma states that @{text g} is the graph of a function
  if the relation induced by @{text g} is unique.
*}

lemma graph_domain_funct:
  assumes uniq: "\<And>x y z. (x, y) \<in> g \<Longrightarrow> (x, z) \<in> g \<Longrightarrow> z = y"
  shows "graph (domain g) (funct g) = g"
proof (unfold domain_def funct_def graph_def, auto)  (* FIXME !? *)
  fix a b assume "(a, b) \<in> g"
  show "(a, SOME y. (a, y) \<in> g) \<in> g" by (rule someI2)
  show "\<exists>y. (a, y) \<in> g" ..
  show "b = (SOME y. (a, y) \<in> g)"
  proof (rule some_equality [symmetric])
    fix y assume "(a, y) \<in> g"
    show "y = b" by (rule uniq)
  qed
qed


subsection {* Norm-preserving extensions of a function *}

text {*
  Given a linear form @{text f} on the space @{text F} and a seminorm
  @{text p} on @{text E}. The set of all linear extensions of @{text
  f}, to superspaces @{text H} of @{text F}, which are bounded by
  @{text p}, is defined as follows.
*}

constdefs
  norm_pres_extensions ::
    "'a::{plus, minus, zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real)
      \<Rightarrow> 'a graph set"
    "norm_pres_extensions E p F f
      \<equiv> {g. \<exists>H h. g = graph H h
          \<and> linearform H h
          \<and> H \<unlhd> E
          \<and> F \<unlhd> H
          \<and> graph F f \<subseteq> graph H h
          \<and> (\<forall>x \<in> H. h x \<le> p x)}"

lemma norm_pres_extensionE [elim]:
  "g \<in> norm_pres_extensions E p F f
  \<Longrightarrow> (\<And>H h. g = graph H h \<Longrightarrow> linearform H h
        \<Longrightarrow> H \<unlhd> E \<Longrightarrow> F \<unlhd> H \<Longrightarrow> graph F f \<subseteq> graph H h
        \<Longrightarrow> \<forall>x \<in> H. h x \<le> p x \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold norm_pres_extensions_def) blast

lemma norm_pres_extensionI2 [intro]:
  "linearform H h \<Longrightarrow> H \<unlhd> E \<Longrightarrow> F \<unlhd> H
    \<Longrightarrow> graph F f \<subseteq> graph H h \<Longrightarrow> \<forall>x \<in> H. h x \<le> p x
    \<Longrightarrow> graph H h \<in> norm_pres_extensions E p F f"
  by (unfold norm_pres_extensions_def) blast

lemma norm_pres_extensionI:  (* FIXME ? *)
  "\<exists>H h. g = graph H h
    \<and> linearform H h
    \<and> H \<unlhd> E
    \<and> F \<unlhd> H
    \<and> graph F f \<subseteq> graph H h
    \<and> (\<forall>x \<in> H. h x \<le> p x) \<Longrightarrow> g \<in> norm_pres_extensions E p F f"
  by (unfold norm_pres_extensions_def) blast

end
