(*  Title:      HOL/Algebras.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Generic algebraic structures and operations *}

theory Algebras
imports HOL
begin

text {*
  These locales provide basic structures for interpretation into
  bigger structures;  extensions require careful thinking, otherwise
  undesired effects may occur due to interpretation.
*}

ML {*
structure Ac_Simps = Named_Thms(
  val name = "ac_simps"
  val description = "associativity and commutativity simplification rules"
)
*}

setup Ac_Simps.setup

locale semigroup =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
  assumes assoc [ac_simps]: "a * b * c = a * (b * c)"

locale abel_semigroup = semigroup +
  assumes commute [ac_simps]: "a * b = b * a"
begin

lemma left_commute [ac_simps]:
  "b * (a * c) = a * (b * c)"
proof -
  have "(b * a) * c = (a * b) * c"
    by (simp only: commute)
  then show ?thesis
    by (simp only: assoc)
qed

end

locale semilattice = abel_semigroup +
  assumes idem [simp]: "a * a = a"
begin

lemma left_idem [simp]:
  "a * (a * b) = a * b"
  by (simp add: assoc [symmetric])

end

end