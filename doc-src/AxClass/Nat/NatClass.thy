
header {* Defining natural numbers in FOL \label{sec:ex-natclass} *}

theory NatClass = FOL:

text {*
 \medskip\noindent Axiomatic type classes abstract over exactly one
 type argument. Thus, any \emph{axiomatic} theory extension where each
 axiom refers to at most one type variable, may be trivially turned
 into a \emph{definitional} one.

 We illustrate this with the natural numbers in
 Isabelle/FOL.\footnote{See also
 \url{http://isabelle.in.tum.de/library/FOL/ex/NatClass.html}}
*}

consts
  zero :: 'a    ("\<zero>")
  Suc :: "'a \<Rightarrow> 'a"
  rec :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a"

axclass nat \<subseteq> "term"
  induct: "P(\<zero>) \<Longrightarrow> (\<And>x. P(x) \<Longrightarrow> P(Suc(x))) \<Longrightarrow> P(n)"
  Suc_inject: "Suc(m) = Suc(n) \<Longrightarrow> m = n"
  Suc_neq_0: "Suc(m) = \<zero> \<Longrightarrow> R"
  rec_0: "rec(\<zero>, a, f) = a"
  rec_Suc: "rec(Suc(m), a, f) = f(m, rec(m, a, f))"

constdefs
  add :: "'a::nat \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "+" 60)
  "m + n \<equiv> rec(m, n, \<lambda>x y. Suc(y))"

text {*
 This is an abstract version of the plain @{text Nat} theory in
 FOL.\footnote{See
 \url{http://isabelle.in.tum.de/library/FOL/ex/Nat.html}} Basically,
 we have just replaced all occurrences of type @{text nat} by @{typ
 'a} and used the natural number axioms to define class @{text nat}.
 There is only a minor snag, that the original recursion operator
 @{term rec} had to be made monomorphic.

 Thus class @{text nat} contains exactly those types @{text \<tau>} that
 are isomorphic to ``the'' natural numbers (with signature @{term
 \<zero>}, @{term Suc}, @{term rec}).

 \medskip What we have done here can be also viewed as \emph{type
 specification}.  Of course, it still remains open if there is some
 type at all that meets the class axioms.  Now a very nice property of
 axiomatic type classes is that abstract reasoning is always possible
 --- independent of satisfiability.  The meta-logic won't break, even
 if some classes (or general sorts) turns out to be empty later ---
 ``inconsistent'' class definitions may be useless, but do not cause
 any harm.

 Theorems of the abstract natural numbers may be derived in the same
 way as for the concrete version.  The original proof scripts may be
 re-used with some trivial changes only (mostly adding some type
 constraints).
*}

end