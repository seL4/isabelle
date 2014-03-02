(*  Title:      HOL/ex/ML.thy
    Author:     Makarius
*)

header {* Isabelle/ML basics *}

theory "ML"
imports Main
begin

section {* ML expressions *}

text {*
  The Isabelle command 'ML' allows to embed Isabelle/ML source into the formal
  text. It is type-checked, compiled, and run within that environment.

  Note that side-effects should be avoided, unless the intention is to change
  global parameters of the run-time environment (rare).

  ML top-level bindings are managed within the theory context.
*}

ML {* 1 + 1 *}

ML {* val a = 1 *}
ML {* val b = 1 *}
ML {* val c = a + b *}


section {* Antiquotations *}

text {* There are some language extensions (via antiquotations), as explained in
  the "Isabelle/Isar implementation manual", chapter 0. *}

ML {* length [] *}
ML {* @{assert} (length [] = 0) *}


text {* Formal entities from the surrounding context may be referenced as
  follows: *}

term "1 + 1"   -- "term within theory source"

ML {*
  @{term "1 + 1"}   (* term as symbolic ML datatype value *)
*}

ML {*
  @{term "1 + (1::int)"}
*}


section {* IDE support *}

text {*
  ML embedded into the Isabelle environment is connected to the Prover IDE.
  Poly/ML provides:
  \begin{itemize}
    \item precise positions for warnings / errors
    \item markup for defining positions of identifiers
    \item markup for inferred types of sub-expressions
  \end{itemize}
*}

ML {* fn i => fn list => length list + i *}


section {* Example: factorial and ackermann function in Isabelle/ML *}

ML {*
  fun factorial 0 = 1
    | factorial n = n * factorial (n - 1)
*}

ML "factorial 42"
ML "factorial 10000 div factorial 9999"

text {*
  See @{url "http://mathworld.wolfram.com/AckermannFunction.html"}
*}

ML {*
  fun ackermann 0 n = n + 1
    | ackermann m 0 = ackermann (m - 1) 1
    | ackermann m n = ackermann (m - 1) (ackermann m (n - 1))
*}

ML {* timeit (fn () => ackermann 3 10) *}


section {* Parallel Isabelle/ML *}

text {*
  Future.fork/join/cancel manage parallel evaluation.

  Note that within Isabelle theory documents, the top-level command boundary may
  not be transgressed without special precautions. This is normally managed by
  the system when performing parallel proof checking. *}

ML {*
  val x = Future.fork (fn () => ackermann 3 10);
  val y = Future.fork (fn () => ackermann 3 10);
  val z = Future.join x + Future.join y
*}

text {*
  The @{ML_structure Par_List} module provides high-level combinators for
  parallel list operations. *}

ML {* timeit (fn () => map (fn n => ackermann 3 n) (1 upto 10)) *}
ML {* timeit (fn () => Par_List.map (fn n => ackermann 3 n) (1 upto 10)) *}


section {* Function specifications in Isabelle/HOL *}

fun factorial :: "nat \<Rightarrow> nat"
where
  "factorial 0 = 1"
| "factorial (Suc n) = Suc n * factorial n"

term "factorial 4"  -- "symbolic term"
value "factorial 4"  -- "evaluation via ML code generation in the background"

declare [[ML_trace]]
ML {* @{term "factorial 4"} *}  -- "symbolic term in ML"
ML {* @{code "factorial"} *}  -- "ML code from function specification"


fun ackermann :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "ackermann 0 n = n + 1"
| "ackermann (Suc m) 0 = ackermann m 1"
| "ackermann (Suc m) (Suc n) = ackermann m (ackermann (Suc m) n)"

value "ackermann 3 5"

end

