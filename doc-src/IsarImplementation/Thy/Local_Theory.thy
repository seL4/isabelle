theory Local_Theory
imports Base
begin

chapter {* Local theory specifications \label{ch:local-theory} *}

text {*
  A \emph{local theory} combines aspects of both theory and proof
  context (cf.\ \secref{sec:context}), such that definitional
  specifications may be given relatively to parameters and
  assumptions.  A local theory is represented as a regular proof
  context, augmented by administrative data about the \emph{target
  context}.

  The target is usually derived from the background theory by adding
  local @{text "\<FIX>"} and @{text "\<ASSUME>"} elements, plus
  suitable modifications of non-logical context data (e.g.\ a special
  type-checking discipline).  Once initialized, the target is ready to
  absorb definitional primitives: @{text "\<DEFINE>"} for terms and
  @{text "\<NOTE>"} for theorems.  Such definitions may get
  transformed in a target-specific way, but the programming interface
  hides such details.

  Isabelle/Pure provides target mechanisms for locales, type-classes,
  type-class instantiations, and general overloading.  In principle,
  users can implement new targets as well, but this rather arcane
  discipline is beyond the scope of this manual.  In contrast,
  implementing derived definitional packages to be used within a local
  theory context is quite easy: the interfaces are even simpler and
  more abstract than the underlying primitives for raw theories.

  Many definitional packages for local theories are available in
  Isabelle.  Although a few old packages only work for global
  theories, the standard way of implementing definitional packages in
  Isabelle is via the local theory interface.
*}


section {* Definitional elements *}

text {*
  There are separate elements @{text "\<DEFINE> c \<equiv> t"} for terms, and
  @{text "\<NOTE> b = thm"} for theorems.  Types are treated
  implicitly, according to Hindley-Milner discipline (cf.\
  \secref{sec:variables}).  These definitional primitives essentially
  act like @{text "let"}-bindings within a local context that may
  already contain earlier @{text "let"}-bindings and some initial
  @{text "\<lambda>"}-bindings.  Thus we gain \emph{dependent definitions}
  that are relative to an initial axiomatic context.  The following
  diagram illustrates this idea of axiomatic elements versus
  definitional elements:

  \begin{center}
  \begin{tabular}{|l|l|l|}
  \hline
  & @{text "\<lambda>"}-binding & @{text "let"}-binding \\
  \hline
  types & fixed @{text "\<alpha>"} & arbitrary @{text "\<beta>"} \\
  terms & @{text "\<FIX> x :: \<tau>"} & @{text "\<DEFINE> c \<equiv> t"} \\
  theorems & @{text "\<ASSUME> a: A"} & @{text "\<NOTE> b = \<^BG>B\<^EN>"} \\
  \hline
  \end{tabular}
  \end{center}

  A user package merely needs to produce suitable @{text "\<DEFINE>"}
  and @{text "\<NOTE>"} elements according to the application.  For
  example, a package for inductive definitions might first @{text
  "\<DEFINE>"} a certain predicate as some fixed-point construction,
  then @{text "\<NOTE>"} a proven result about monotonicity of the
  functor involved here, and then produce further derived concepts via
  additional @{text "\<DEFINE>"} and @{text "\<NOTE>"} elements.

  The cumulative sequence of @{text "\<DEFINE>"} and @{text "\<NOTE>"}
  produced at package runtime is managed by the local theory
  infrastructure by means of an \emph{auxiliary context}.  Thus the
  system holds up the impression of working within a fully abstract
  situation with hypothetical entities: @{text "\<DEFINE> c \<equiv> t"}
  always results in a literal fact @{text "\<^BG>c \<equiv> t\<^EN>"}, where
  @{text "c"} is a fixed variable @{text "c"}.  The details about
  global constants, name spaces etc. are handled internally.

  So the general structure of a local theory is a sandwich of three
  layers:

  \begin{center}
  \framebox{\quad auxiliary context \quad\framebox{\quad target context \quad\framebox{\quad background theory\quad}}}
  \end{center}

  When a definitional package is finished, the auxiliary context is
  reset to the target context.  The target now holds definitions for
  terms and theorems that stem from the hypothetical @{text
  "\<DEFINE>"} and @{text "\<NOTE>"} elements, transformed by the
  particular target policy (see \cite[\S4--5]{Haftmann-Wenzel:2009}
  for details).  *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type local_theory: Proof.context} \\
  @{index_ML Named_Target.init: "(local_theory -> local_theory) ->
    string -> theory -> local_theory"} \\[1ex]
  @{index_ML Local_Theory.define: "(binding * mixfix) * (Attrib.binding * term) ->
    local_theory -> (term * (string * thm)) * local_theory"} \\
  @{index_ML Local_Theory.note: "Attrib.binding * thm list ->
    local_theory -> (string * thm list) * local_theory"} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type local_theory} represents local theories.
  Although this is merely an alias for @{ML_type Proof.context}, it is
  semantically a subtype of the same: a @{ML_type local_theory} holds
  target information as special context data.  Subtyping means that
  any value @{text "lthy:"}~@{ML_type local_theory} can be also used
  with operations on expecting a regular @{text "ctxt:"}~@{ML_type
  Proof.context}.

  \item @{ML Named_Target.init}~@{text "before_exit name thy"}
  initializes a local theory derived from the given background theory.
  An empty name refers to a \emph{global theory} context, and a
  non-empty name refers to a @{command locale} or @{command class}
  context (a fully-qualified internal name is expected here).  This is
  useful for experimentation --- normally the Isar toplevel already
  takes care to initialize the local theory context.  The given @{text
  "before_exit"} function is invoked before leaving the context; in
  most situations plain identity @{ML I} is sufficient.

  \item @{ML Local_Theory.define}~@{text "((b, mx), (a, rhs))
  lthy"} defines a local entity according to the specification that is
  given relatively to the current @{text "lthy"} context.  In
  particular the term of the RHS may refer to earlier local entities
  from the auxiliary context, or hypothetical parameters from the
  target context.  The result is the newly defined term (which is
  always a fixed variable with exactly the same name as specified for
  the LHS), together with an equational theorem that states the
  definition as a hypothetical fact.

  Unless an explicit name binding is given for the RHS, the resulting
  fact will be called @{text "b_def"}.  Any given attributes are
  applied to that same fact --- immediately in the auxiliary context
  \emph{and} in any transformed versions stemming from target-specific
  policies or any later interpretations of results from the target
  context (think of @{command locale} and @{command interpretation},
  for example).  This means that attributes should be usually plain
  declarations such as @{attribute simp}, while non-trivial rules like
  @{attribute simplified} are better avoided.

  \item @{ML Local_Theory.note}~@{text "(a, ths) lthy"} is
  analogous to @{ML Local_Theory.define}, but defines facts instead of
  terms.  There is also a slightly more general variant @{ML
  Local_Theory.notes} that defines several facts (with attribute
  expressions) simultaneously.

  This is essentially the internal version of the @{command lemmas}
  command, or @{command declare} if an empty name binding is given.

  \end{description}
*}


section {* Morphisms and declarations \label{sec:morphisms} *}

text {* FIXME

  \medskip See also \cite{Chaieb-Wenzel:2007}.
*}

end
