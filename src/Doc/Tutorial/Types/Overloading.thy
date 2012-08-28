(*<*)theory Overloading imports Main Setup begin

hide_class (open) plus (*>*)

text {* Type classes allow \emph{overloading}; thus a constant may
have multiple definitions at non-overlapping types. *}

subsubsection {* Overloading *}

text {* We can introduce a binary infix addition operator @{text "\<otimes>"}
for arbitrary types by means of a type class: *}

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70)

text {* \noindent This introduces a new class @{class [source] plus},
along with a constant @{const [source] plus} with nice infix syntax.
@{const [source] plus} is also named \emph{class operation}.  The type
of @{const [source] plus} carries a class constraint @{typ [source] "'a
:: plus"} on its type variable, meaning that only types of class
@{class [source] plus} can be instantiated for @{typ [source] "'a"}.
To breathe life into @{class [source] plus} we need to declare a type
to be an \bfindex{instance} of @{class [source] plus}: *}

instantiation nat :: plus
begin

text {* \noindent Command \isacommand{instantiation} opens a local
theory context.  Here we can now instantiate @{const [source] plus} on
@{typ nat}: *}

primrec plus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "(0::nat) \<oplus> n = n"
  | "Suc m \<oplus> n = Suc (m \<oplus> n)"

text {* \noindent Note that the name @{const [source] plus} carries a
suffix @{text "_nat"}; by default, the local name of a class operation
@{text f} to be instantiated on type constructor @{text \<kappa>} is mangled
as @{text f_\<kappa>}.  In case of uncertainty, these names may be inspected
using the @{command "print_context"} command or the corresponding
ProofGeneral button.

Although class @{class [source] plus} has no axioms, the instantiation must be
formally concluded by a (trivial) instantiation proof ``..'': *}

instance ..

text {* \noindent More interesting \isacommand{instance} proofs will
arise below.

The instantiation is finished by an explicit *}

end

text {* \noindent From now on, terms like @{term "Suc (m \<oplus> 2)"} are
legal. *}

instantiation prod :: (plus, plus) plus
begin

text {* \noindent Here we instantiate the product type @{type prod} to
class @{class [source] plus}, given that its type arguments are of
class @{class [source] plus}: *}

fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "(x, y) \<oplus> (w, z) = (x \<oplus> w, y \<oplus> z)"

text {* \noindent Obviously, overloaded specifications may include
recursion over the syntactic structure of types. *}

instance ..

end

text {* \noindent This way we have encoded the canonical lifting of
binary operations to products by means of type classes. *}

(*<*)end(*>*)
