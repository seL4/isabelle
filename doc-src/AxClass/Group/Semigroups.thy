
header {* Semigroups *}

theory Semigroups = Main:

text {*
 \medskip\noindent An axiomatic type class is simply a class of types
 that all meet certain properties, which are also called \emph{class
 axioms}. Thus, type classes may be also understood as type predicates
 --- i.e.\ abstractions over a single type argument @{typ 'a}.  Class
 axioms typically contain polymorphic constants that depend on this
 type @{typ 'a}.  These \emph{characteristic constants} behave like
 operations associated with the ``carrier'' type @{typ 'a}.

 We illustrate these basic concepts by the following formulation of
 semigroups.
*}

consts
  times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<odot>" 70)
axclass semigroup < "term"
  assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"

text {*
 \noindent Above we have first declared a polymorphic constant @{text
 "\<odot> \<Colon> 'a \<Rightarrow> 'a \<Rightarrow> 'a"} and then defined the class @{text semigroup} of
 all types @{text \<tau>} such that @{text "\<odot> \<Colon> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>"} is indeed an
 associative operator.  The @{text assoc} axiom contains exactly one
 type variable, which is invisible in the above presentation, though.
 Also note that free term variables (like @{term x}, @{term y}, @{term
 z}) are allowed for user convenience --- conceptually all of these
 are bound by outermost universal quantifiers.

 \medskip In general, type classes may be used to describe
 \emph{structures} with exactly one carrier @{typ 'a} and a fixed
 \emph{signature}.  Different signatures require different classes.
 Below, class @{text plus_semigroup} represents semigroups of the form
 @{text "(\<tau>, \<oplus>)"}, while the original @{text semigroup} would
 correspond to semigroups @{text "(\<tau>, \<odot>)"}.
*}

consts
  plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<oplus>" 70)
axclass plus_semigroup < "term"
  assoc: "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"

text {*
 \noindent Even if classes @{text plus_semigroup} and @{text
 semigroup} both represent semigroups in a sense, they are certainly
 not quite the same.
*}

end