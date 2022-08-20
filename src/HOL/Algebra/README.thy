theory README imports Main
begin

section \<open>Algebra --- Classical Algebra, using Explicit Structures and Locales\<close>

text \<open>
  This directory contains proofs in classical algebra. It is intended as a
  base for any algebraic development in Isabelle. Emphasis is on reusability.
  This is achieved by modelling algebraic structures as first-class citizens
  of the logic (not axiomatic type classes, say). The library is expected to
  grow in future releases of Isabelle. Contributions are welcome.
\<close>

subsection \<open>GroupTheory, including Sylow's Theorem\<close>

text \<open>
  These proofs are mainly by Florian Kammüller. (Later, Larry Paulson
  simplified some of the proofs.) These theories were indeed the original
  motivation for locales.

  Here is an outline of the directory's contents:

  \<^item> Theory \<^file>\<open>Group.thy\<close> defines semigroups, monoids, groups, commutative
    monoids, commutative groups, homomorphisms and the subgroup relation. It
    also defines the product of two groups (This theory was reimplemented by
    Clemens Ballarin).

  \<^item> Theory \<^file>\<open>FiniteProduct.thy\<close> extends commutative groups by a product
    operator for finite sets (provided by Clemens Ballarin).

  \<^item> Theory \<^file>\<open>Coset.thy\<close> defines the factorization of a group and shows that
    the factorization a normal subgroup is a group.

  \<^item> Theory \<^file>\<open>Bij.thy\<close> defines bijections over sets and operations on them and
    shows that they are a group. It shows that automorphisms form a group.

  \<^item> Theory \<^file>\<open>Exponent.thy\<close> the combinatorial argument underlying Sylow's
    first theorem.

  \<^item> Theory \<^file>\<open>Sylow.thy\<close> contains a proof of the first Sylow theorem.
\<close>


subsection \<open>Rings and Polynomials\<close>

text \<open>
  \<^item> Theory \<^file>\<open>Ring.thy\<close> defines Abelian monoids and groups. The difference to
    commutative structures is merely notational: the binary operation is
    addition rather than multiplication. Commutative rings are obtained by
    inheriting properties from Abelian groups and commutative monoids. Further
    structures in the algebraic hierarchy of rings: integral domain.

  \<^item> Theory \<^file>\<open>Module.thy\<close> introduces the notion of a R-left-module over an
    Abelian group, where R is a ring.

  \<^item> Theory \<^file>\<open>UnivPoly.thy\<close> constructs univariate polynomials over rings and
    integral domains. Degree function. Universal Property.
\<close>


subsection \<open>Development of Polynomials using Type Classes\<close>

text \<open>
  A development of univariate polynomials for HOL's ring classes is available
  at \<^file>\<open>~~/src/HOL/Computational_Algebra/Polynomial.thy\<close>.

  [Jacobson1985] Nathan Jacobson, Basic Algebra I, Freeman, 1985.

  [Ballarin1999] Clemens Ballarin, Computer Algebra and Theorem Proving,
  Author's PhD thesis, 1999. Also University of Cambridge, Computer Laboratory
  Technical Report number 473.
\<close>

end
