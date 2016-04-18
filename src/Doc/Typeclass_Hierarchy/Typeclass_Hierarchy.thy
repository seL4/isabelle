theory Typeclass_Hierarchy
imports Setup
begin

section \<open>Introduction\<close>

text \<open>
  The {Isabelle/HOL} type-class hierarchy entered the stage
  in a quite ancient era -- first related \emph{NEWS} entries date
  back to release {Isabelle99-1}.  Since then, there have been
  ongoing modifications and additions, leading to ({Isabelle2016})
  more than 180 type-classes.  This sheer complexity makes access
  and understanding of that type-class hierarchy difficult and
  involved, let alone maintenance.

  The purpose of this primer is to shed some light on this,
  not only on the mere ingredients, but also on the design
  principles which have evolved and proven useful over time.
\<close>

section \<open>Foundations\<close>

subsection \<open>Locales and type classes\<close>

text \<open>
  Some familiarity with the Isabelle module system is assumed:
  defining locales and type-classes, interpreting locales and
  instantiating type-classes, adding relationships between
  locales (@{command sublocale}) and type-classes
  (@{command subclass}).  Handy introductions are the
  respective tutorials \cite{isabelle-locale}
  \cite{isabelle-classes}.
\<close>

subsection \<open>Strengths and restrictions of type classes\<close>

text \<open>
  The primary motivation for using type classes in {Isabelle/HOL}
  always have been numerical types, which form an inclusion chain:
  
  \begin{center}
    @{typ nat} @{text \<sqsubset>} @{typ int} @{text \<sqsubset>} @{typ rat}
      @{text \<sqsubset>} @{typ real} @{text \<sqsubset>} @{typ complex}
  \end{center}

  \noindent The inclusion @{text \<sqsubset>} means that any value of the numerical
  type to the left hand side mathematically can be transferred
  to the numerical type on the right hand side.

  How to accomplish this given the quite restrictive type system
  of {Isabelle/HOL}?  Paulson \cite{paulson-numerical} explains
  that each numerical type has some characteristic properties
  which define an characteristic algebraic structure;  @{text \<sqsubset>}
  then corresponds to specialization of the corresponding
  characteristic algebraic structures.  These algebraic structures
  are expressed using algebraic type classes and embeddings
  of numerical types into them:

  \begin{center}\begin{tabular}{lccc}
    @{term of_nat} @{text "::"}  & @{typ nat}  & @{text \<Rightarrow>} & @{typ [source] "'a::semiring_1"} \\
                                 & @{text \<sqinter>}   &            & @{text \<up>} \\
    @{term of_int} @{text "::"}  & @{typ int}  & @{text \<Rightarrow>} & @{typ [source] "'a::ring_1"} \\
                                 & @{text \<sqinter>}   &            & @{text \<up>} \\
    @{term of_rat} @{text "::"}  & @{typ rat}  & @{text \<Rightarrow>} & @{typ [source] "'a::field_char_0"} \\
                                 & @{text \<sqinter>}   &            & @{text \<up>} \\
    @{term of_real} @{text "::"} & @{typ real} & @{text \<Rightarrow>} & @{typ [source] "'a::real_algebra_1"} \\
                                 & @{text \<sqinter>} \\
                                 & @{typ complex}
  \end{tabular}\end{center}

  \noindent @{text "d \<leftarrow> c"} means that @{text c} is subclass of @{text d}.
  Hence each characteristic embedding @{text of_num} can transform
  any value of type @{text num} to any numerical type further
  up in the inclusion chain.

  This canonical example exhibits key strengths of type classes:

    \<^item> Sharing of operations and facts among different
      types, hence also sharing of notation and names: there
      is only one plus operation using infix syntax @{text "+"},
      only one zero written @{text 0}, and neutrality
      (@{thm add_0_left [all, no_vars]} and
      @{thm add_0_right [all, no_vars]})
      is referred to
      uniformly by names @{fact add_0_left} and @{fact add_0_right}.

    \<^item> Proof tool setups are shared implicitly:
      @{fact add_0} and @{fact add_0_right} are simplification
      rules by default.

    \<^item> Hence existing proofs about particular numerical
      types are often easy to generalize to algebraic structures,
      given that they do not depend on specific properties of
      those numerical types.

  Considerable restrictions include:

    \<^item> Type class operations are restricted to one
      type parameter; this is insufficient e.g. for expressing
      a unified power operation adequately (see \secref{sec:power}).

    \<^item> Parameters are fixed over the whole type class
      hierarchy and cannot be refined in specific situations:
      think of integral domains with a predicate @{term is_unit};
      for natural numbers, this degenerates to the much simpler
      @{term [source] "HOL.equal (1::nat)"} but facts
      refer to @{term is_unit} nonetheless.

    \<^item> Type classes are not apt for meta-theory.  There
      is no practically usable way to express that the units
      of an integral domain form a multiplicative group using
      type classes.  But see session @{text "HOL-Algebra"}
      which provides locales with an explicit carrier.
\<close>


subsection \<open>Navigating the hierarchy\<close>

text \<open>
  An indispensable tool to inspect the class hierarchy is
  @{command class_deps} which displays the graph of classes,
  optionally showing the logical content for each class also.
  Optional parameters restrict the graph to a particular segment
  which is useful to get a graspable view.  See
  the Isar reference manual \cite{isabelle-isar-ref} for details.
\<close>


section \<open>The hierarchy\<close>

subsection \<open>Syntactic type classes\<close>

text \<open>
  At the top of the hierarchy there are a couple of syntactic type
  classes, ie. classes with operations but with no axioms,
  most notably:

    \<^item> @{class plus} with @{term [source] "(a::'a::plus) + b"}

    \<^item> @{class zero} with @{term [source] "0::'a::zero"}

    \<^item> @{class times} with @{term [source] "(a::'a::times) * b"}

    \<^item> @{class one} with @{term [source] "1::'a::one"}

  \noindent Before the introduction of the @{command class} statement in
  Isabelle \cite{Haftmann-Wenzel:2006:classes} it was impossible
  to define operations with associated axioms in the same class,
  hence there were always pairs of syntactic and logical type
  classes.  This restriction is lifted nowadays, but there are
  still reasons to maintain syntactic type classes:

    \<^item> Syntactic type classes allow generic notation to be used
      regardless of a particular logical interpretation; e.g.
      although multiplication @{text "*"} is usually associative,
      there are examples where it is not (e.g. octonions), and
      leaving @{text "*"} without axioms allows to re-use this
      syntax by means of type class instantiation also for such
      exotic examples.

    \<^item> Type classes might share operations but not necessarily
      axioms on them, e.g. @{term gcd} (see \secref{sec:gcd}).
      Hence their common base is a syntactic type class.

  \noindent However syntactic type classes should only be used with striking
  cause.  Otherwise there is risk for confusion if the notation
  suggests properties which do not hold without particular
  constraints.  This can be illustrated using numerals
  (see \secref{sec:numerals}):  @{lemma "2 + 2 = 4" by simp} is
  provable without further ado, and this also meets the typical
  expectation towards a numeral notation;  in more ancient releases
  numerals were purely syntactic and @{prop "2 + 2 = 4"} was
  not provable without particular type constraints.
\<close>

end
