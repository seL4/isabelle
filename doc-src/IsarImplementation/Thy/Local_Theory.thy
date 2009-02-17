theory Local_Theory
imports Base
begin

chapter {* Local theory specifications *}

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
  theory context is quite easy: the interfaces are simpler and more
  abstract than the underlying primitives for raw theories.

  Many definitional packages for local theories are available in
  Isabelle/Pure and Isabelle/HOL.  Even though a few old packages that
  only work for global theories might still persists, the local theory
  interface is already the standard way of implementing definitional
  packages in Isabelle.
*}


section {* Definitional elements *}

text {*
  There are separate definitional elements @{text "\<DEFINE> c \<equiv> t"}
  for terms, and @{text "\<NOTE> b = thm"} for theorems.  Types are
  treated implicitly, according to Hindley-Milner discipline (cf.\
  \secref{sec:variables}).  These definitional primitives essentially
  act like @{text "let"}-bindings within a local context that may
  already contain some @{text "\<lambda>"}-bindings.  Thus we gain
  \emph{dependent definitions}, relatively to an initial axiomatic
  context.  The following diagram illustrates this idea of axiomatic
  elements versus definitional elements:

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
  prove the monotonicity of the functor involved here and @{text
  "\<NOTE>"} the result, and then produce further derived concepts via
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

  \noindent When a definitional package is finished, the auxiliary
  context will be reset to the target context.  The target now holds
  definitions for terms and theorems that stem from the hypothetical
  @{text "\<DEFINE>"} and @{text "\<NOTE>"} elements, transformed by
  the particular target policy (see \cite[\S4-5]{Haftmann-Wenzel:2009}
  for details).
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML LocalTheory.define: "string ->
    (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory"} \\
  @{index_ML LocalTheory.note: "string ->
    Attrib.binding * thm list -> local_theory ->
    (string * thm list) * local_theory"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML LocalTheory.define}~@{text FIXME}

  \item @{ML LocalTheory.note}~@{text FIXME}

  \end{description}
*}


section {* Morphisms and declarations *}

text FIXME

end
