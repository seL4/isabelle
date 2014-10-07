(*  Title:      HOL/ex/ML.thy
    Author:     Makarius
*)

header \<open>Isabelle/ML basics\<close>

theory "ML"
imports Main
begin

section \<open>ML expressions\<close>

text \<open>
  The Isabelle command 'ML' allows to embed Isabelle/ML source into the formal
  text. It is type-checked, compiled, and run within that environment.

  Note that side-effects should be avoided, unless the intention is to change
  global parameters of the run-time environment (rare).

  ML top-level bindings are managed within the theory context.
\<close>

ML \<open>1 + 1\<close>

ML \<open>val a = 1\<close>
ML \<open>val b = 1\<close>
ML \<open>val c = a + b\<close>


section \<open>Antiquotations\<close>

text \<open>There are some language extensions (via antiquotations), as explained in
  the ``Isabelle/Isar implementation manual'', chapter 0.\<close>

ML \<open>length []\<close>
ML \<open>@{assert} (length [] = 0)\<close>


text \<open>Formal entities from the surrounding context may be referenced as
  follows:\<close>

term "1 + 1"   -- \<open>term within theory source\<close>

ML \<open>@{term "1 + 1"}   (* term as symbolic ML datatype value *)\<close>

ML \<open>@{term "1 + (1::int)"}\<close>


section \<open>IDE support\<close>

text \<open>
  ML embedded into the Isabelle environment is connected to the Prover IDE.
  Poly/ML provides:
  \begin{itemize}
    \item precise positions for warnings / errors
    \item markup for defining positions of identifiers
    \item markup for inferred types of sub-expressions
  \end{itemize}
\<close>

ML \<open>fn i => fn list => length list + i\<close>


section \<open>Example: factorial and ackermann function in Isabelle/ML\<close>

ML \<open>
  fun factorial 0 = 1
    | factorial n = n * factorial (n - 1)
\<close>

ML \<open>factorial 42\<close>
ML \<open>factorial 10000 div factorial 9999\<close>

text \<open>See @{url "http://mathworld.wolfram.com/AckermannFunction.html"}\<close>

ML \<open>
  fun ackermann 0 n = n + 1
    | ackermann m 0 = ackermann (m - 1) 1
    | ackermann m n = ackermann (m - 1) (ackermann m (n - 1))
\<close>

ML \<open>timeit (fn () => ackermann 3 10)\<close>


section \<open>Parallel Isabelle/ML\<close>

text \<open>
  Future.fork/join/cancel manage parallel evaluation.

  Note that within Isabelle theory documents, the top-level command boundary may
  not be transgressed without special precautions. This is normally managed by
  the system when performing parallel proof checking.\<close>

ML \<open>
  val x = Future.fork (fn () => ackermann 3 10);
  val y = Future.fork (fn () => ackermann 3 10);
  val z = Future.join x + Future.join y
\<close>

text \<open>The @{ML_structure Par_List} module provides high-level combinators
  for parallel list operations.\<close>

ML \<open>timeit (fn () => map (fn n => ackermann 3 n) (1 upto 10))\<close>
ML \<open>timeit (fn () => Par_List.map (fn n => ackermann 3 n) (1 upto 10))\<close>


section \<open>Function specifications in Isabelle/HOL\<close>

fun factorial :: "nat \<Rightarrow> nat"
where
  "factorial 0 = 1"
| "factorial (Suc n) = Suc n * factorial n"

term "factorial 4"  -- \<open>symbolic term\<close>
value "factorial 4"  -- \<open>evaluation via ML code generation in the background\<close>

declare [[ML_source_trace]]
ML \<open>@{term "factorial 4"}\<close>  -- \<open>symbolic term in ML\<close>
ML \<open>@{code "factorial"}\<close>  -- \<open>ML code from function specification\<close>


fun ackermann :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "ackermann 0 n = n + 1"
| "ackermann (Suc m) 0 = ackermann m 1"
| "ackermann (Suc m) (Suc n) = ackermann m (ackermann (Suc m) n)"

value "ackermann 3 5"

end

