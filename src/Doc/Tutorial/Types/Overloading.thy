(*<*)theory Overloading imports "../Setup" begin

hide_class (open) plus (*>*)

text \<open>Type classes allow \emph{overloading}; thus a constant may
have multiple definitions at non-overlapping types.\<close>

subsubsection \<open>Overloading\<close>

text \<open>We can introduce a binary infix addition operator \<open>\<oplus>\<close>
for arbitrary types by means of a type class:\<close>

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70)

text \<open>\noindent This introduces a new class @{class [source] plus},
along with a constant @{const [source] plus} with nice infix syntax.
@{const [source] plus} is also named \emph{class operation}.  The type
of @{const [source] plus} carries a class constraint @{typ [source] "'a
:: plus"} on its type variable, meaning that only types of class
@{class [source] plus} can be instantiated for @{typ [source] "'a"}.
To breathe life into @{class [source] plus} we need to declare a type
to be an \bfindex{instance} of @{class [source] plus}:\<close>

instantiation nat :: plus
begin

text \<open>\noindent Command \isacommand{instantiation} opens a local
theory context.  Here we can now instantiate @{const [source] plus} on
\<^typ>\<open>nat\<close>:\<close>

primrec plus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "(0::nat) \<oplus> n = n"
  | "Suc m \<oplus> n = Suc (m \<oplus> n)"

text \<open>\noindent Note that the name @{const [source] plus} carries a
suffix \<open>_nat\<close>; by default, the local name of a class operation
\<open>f\<close> to be instantiated on type constructor \<open>\<kappa>\<close> is mangled
as \<open>f_\<kappa>\<close>.  In case of uncertainty, these names may be inspected
using the @{command "print_context"} command.

Although class @{class [source] plus} has no axioms, the instantiation must be
formally concluded by a (trivial) instantiation proof ``..'':\<close>

instance ..

text \<open>\noindent More interesting \isacommand{instance} proofs will
arise below.

The instantiation is finished by an explicit\<close>

end

text \<open>\noindent From now on, terms like \<^term>\<open>Suc (m \<oplus> 2)\<close> are
legal.\<close>

instantiation prod :: (plus, plus) plus
begin

text \<open>\noindent Here we instantiate the product type \<^type>\<open>prod\<close> to
class @{class [source] plus}, given that its type arguments are of
class @{class [source] plus}:\<close>

fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "(x, y) \<oplus> (w, z) = (x \<oplus> w, y \<oplus> z)"

text \<open>\noindent Obviously, overloaded specifications may include
recursion over the syntactic structure of types.\<close>

instance ..

end

text \<open>\noindent This way we have encoded the canonical lifting of
binary operations to products by means of type classes.\<close>

(*<*)end(*>*)
