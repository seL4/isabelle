(*:maxLineLen=78:*)

theory Local_Theory
imports Base
begin

chapter \<open>Local theory specifications \label{ch:local-theory}\<close>

text \<open>
  A \<^emph>\<open>local theory\<close> combines aspects of both theory and proof context (cf.\
  \secref{sec:context}), such that definitional specifications may be given
  relatively to parameters and assumptions. A local theory is represented as a
  regular proof context, augmented by administrative data about the \<^emph>\<open>target
  context\<close>.

  The target is usually derived from the background theory by adding local
  \<open>\<FIX>\<close> and \<open>\<ASSUME>\<close> elements, plus suitable modifications of
  non-logical context data (e.g.\ a special type-checking discipline). Once
  initialized, the target is ready to absorb definitional primitives:
  \<open>\<DEFINE>\<close> for terms and \<open>\<NOTE>\<close> for theorems. Such definitions may get
  transformed in a target-specific way, but the programming interface hides
  such details.

  Isabelle/Pure provides target mechanisms for locales, type-classes,
  type-class instantiations, and general overloading. In principle, users can
  implement new targets as well, but this rather arcane discipline is beyond
  the scope of this manual. In contrast, implementing derived definitional
  packages to be used within a local theory context is quite easy: the
  interfaces are even simpler and more abstract than the underlying primitives
  for raw theories.

  Many definitional packages for local theories are available in Isabelle.
  Although a few old packages only work for global theories, the standard way
  of implementing definitional packages in Isabelle is via the local theory
  interface.
\<close>


section \<open>Definitional elements\<close>

text \<open>
  There are separate elements \<open>\<DEFINE> c \<equiv> t\<close> for terms, and \<open>\<NOTE> b =
  thm\<close> for theorems. Types are treated implicitly, according to Hindley-Milner
  discipline (cf.\ \secref{sec:variables}). These definitional primitives
  essentially act like \<open>let\<close>-bindings within a local context that may already
  contain earlier \<open>let\<close>-bindings and some initial \<open>\<lambda>\<close>-bindings. Thus we gain
  \<^emph>\<open>dependent definitions\<close> that are relative to an initial axiomatic context.
  The following diagram illustrates this idea of axiomatic elements versus
  definitional elements:

  \begin{center}
  \begin{tabular}{|l|l|l|}
  \hline
  & \<open>\<lambda>\<close>-binding & \<open>let\<close>-binding \\
  \hline
  types & fixed \<open>\<alpha>\<close> & arbitrary \<open>\<beta>\<close> \\
  terms & \<open>\<FIX> x :: \<tau>\<close> & \<open>\<DEFINE> c \<equiv> t\<close> \\
  theorems & \<open>\<ASSUME> a: A\<close> & \<open>\<NOTE> b = \<^BG>B\<^EN>\<close> \\
  \hline
  \end{tabular}
  \end{center}

  A user package merely needs to produce suitable \<open>\<DEFINE>\<close> and \<open>\<NOTE>\<close>
  elements according to the application. For example, a package for inductive
  definitions might first \<open>\<DEFINE>\<close> a certain predicate as some fixed-point
  construction, then \<open>\<NOTE>\<close> a proven result about monotonicity of the
  functor involved here, and then produce further derived concepts via
  additional \<open>\<DEFINE>\<close> and \<open>\<NOTE>\<close> elements.

  The cumulative sequence of \<open>\<DEFINE>\<close> and \<open>\<NOTE>\<close> produced at package
  runtime is managed by the local theory infrastructure by means of an
  \<^emph>\<open>auxiliary context\<close>. Thus the system holds up the impression of working
  within a fully abstract situation with hypothetical entities: \<open>\<DEFINE> c \<equiv>
  t\<close> always results in a literal fact \<open>\<^BG>c \<equiv> t\<^EN>\<close>, where \<open>c\<close> is a
  fixed variable \<open>c\<close>. The details about global constants, name spaces etc. are
  handled internally.

  So the general structure of a local theory is a sandwich of three layers:

  \begin{center}
  \framebox{\quad auxiliary context \quad\framebox{\quad target context \quad\framebox{\quad background theory\quad}}}
  \end{center}

  When a definitional package is finished, the auxiliary context is reset to
  the target context. The target now holds definitions for terms and theorems
  that stem from the hypothetical \<open>\<DEFINE>\<close> and \<open>\<NOTE>\<close> elements,
  transformed by the particular target policy (see @{cite \<open>\S4--5\<close>
  "Haftmann-Wenzel:2009"} for details).
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type local_theory: Proof.context} \\
  @{index_ML Named_Target.init: "string list -> string -> theory -> local_theory"} \\[1ex]
  @{index_ML Local_Theory.define: "(binding * mixfix) * (Attrib.binding * term) ->
    local_theory -> (term * (string * thm)) * local_theory"} \\
  @{index_ML Local_Theory.note: "Attrib.binding * thm list ->
    local_theory -> (string * thm list) * local_theory"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>local_theory\<close> represents local theories. Although this is
  merely an alias for \<^ML_type>\<open>Proof.context\<close>, it is semantically a subtype
  of the same: a \<^ML_type>\<open>local_theory\<close> holds target information as special
  context data. Subtyping means that any value \<open>lthy:\<close>~\<^ML_type>\<open>local_theory\<close>
  can be also used with operations on expecting a regular \<open>ctxt:\<close>~\<^ML_type>\<open>Proof.context\<close>.

  \<^descr> \<^ML>\<open>Named_Target.init\<close>~\<open>includes name thy\<close> initializes a local theory
  derived from the given background theory. An empty name refers to a \<^emph>\<open>global
  theory\<close> context, and a non-empty name refers to a @{command locale} or
  @{command class} context (a fully-qualified internal name is expected here).
  This is useful for experimentation --- normally the Isar toplevel already
  takes care to initialize the local theory context.

  \<^descr> \<^ML>\<open>Local_Theory.define\<close>~\<open>((b, mx), (a, rhs)) lthy\<close> defines a local
  entity according to the specification that is given relatively to the
  current \<open>lthy\<close> context. In particular the term of the RHS may refer to
  earlier local entities from the auxiliary context, or hypothetical
  parameters from the target context. The result is the newly defined term
  (which is always a fixed variable with exactly the same name as specified
  for the LHS), together with an equational theorem that states the definition
  as a hypothetical fact.

  Unless an explicit name binding is given for the RHS, the resulting fact
  will be called \<open>b_def\<close>. Any given attributes are applied to that same fact
  --- immediately in the auxiliary context \<^emph>\<open>and\<close> in any transformed versions
  stemming from target-specific policies or any later interpretations of
  results from the target context (think of @{command locale} and @{command
  interpretation}, for example). This means that attributes should be usually
  plain declarations such as @{attribute simp}, while non-trivial rules like
  @{attribute simplified} are better avoided.

  \<^descr> \<^ML>\<open>Local_Theory.note\<close>~\<open>(a, ths) lthy\<close> is analogous to \<^ML>\<open>Local_Theory.define\<close>, but defines facts instead of terms. There is also a
  slightly more general variant \<^ML>\<open>Local_Theory.notes\<close> that defines several
  facts (with attribute expressions) simultaneously.

  This is essentially the internal version of the @{command lemmas} command,
  or @{command declare} if an empty name binding is given.
\<close>


section \<open>Morphisms and declarations \label{sec:morphisms}\<close>

text \<open>
  %FIXME

  See also @{cite "Chaieb-Wenzel:2007"}.
\<close>

end
