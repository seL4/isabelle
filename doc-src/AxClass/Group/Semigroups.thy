
header {* Semigroups *}

theory Semigroups = Main:

text {*
 \medskip\noindent An axiomatic type class is simply a class of types
 that all meet certain properties, which are also called \emph{class
 axioms}. Thus, type classes may be also understood as type predicates
 --- i.e.\ abstractions over a single type argument $\alpha$.  Class
 axioms typically contain polymorphic constants that depend on this
 type $\alpha$.  These \emph{characteristic constants} behave like
 operations associated with the ``carrier'' type $\alpha$.

 We illustrate these basic concepts by the following formulation of
 semigroups.
*}

consts
  times :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Otimes>" 70)
axclass
  semigroup < "term"
  assoc: "(x \<Otimes> y) \<Otimes> z = x \<Otimes> (y \<Otimes> z)"

text {*
 \noindent Above we have first declared a polymorphic constant $\TIMES
 :: \alpha \To \alpha \To \alpha$ and then defined the class
 $semigroup$ of all types $\tau$ such that $\TIMES :: \tau \To \tau
 \To \tau$ is indeed an associative operator.  The $assoc$ axiom
 contains exactly one type variable, which is invisible in the above
 presentation, though.  Also note that free term variables (like $x$,
 $y$, $z$) are allowed for user convenience --- conceptually all of
 these are bound by outermost universal quantifiers.

 \medskip In general, type classes may be used to describe
 \emph{structures} with exactly one carrier $\alpha$ and a fixed
 \emph{signature}.  Different signatures require different classes.
 Below, class $plus_semigroup$ represents semigroups of the form
 $(\tau, \PLUS^\tau)$, while the original $semigroup$ would correspond
 to semigroups $(\tau, \TIMES^\tau)$.
*}

consts
  plus :: "'a \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\<Oplus>" 70)
axclass
  plus_semigroup < "term"
  assoc: "(x \<Oplus> y) \<Oplus> z = x \<Oplus> (y \<Oplus> z)"

text {*
 \noindent Even if classes $plus_semigroup$ and $semigroup$ both
 represent semigroups in a sense, they are certainly not quite the
 same.
*}

end