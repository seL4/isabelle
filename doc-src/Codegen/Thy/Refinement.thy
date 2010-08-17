theory Refinement
imports Setup
begin

section {* Program and datatype refinement \label{sec:refinement} *}

text {*
  Code generation by shallow embedding (cf.~\secref{sec:principle})
  allows to choose code equations and datatype constructors freely,
  given that some very basic syntactic properties are met; this
  flexibility opens up mechanisms for refinement which allow to extend
  the scope and quality of generated code dramatically.
*}


subsection {* Program refinement *}

text {*
  Program refinement works by choosing appropriate code equations
  explicitly (cf.~\label{sec:equations}); as example, we use Fibonacci
  numbers:
*}

fun %quote fib :: "nat \<Rightarrow> nat" where
    "fib 0 = 0"
  | "fib (Suc 0) = Suc 0"
  | "fib (Suc (Suc n)) = fib n + fib (Suc n)"

text {*
  \noindent The runtime of the corresponding code grows exponential due
  to two recursive calls:
*}

text %quote {*@{code_stmts fib (consts) fib (Haskell)}*}

text {*
  \noindent A more efficient implementation would use dynamic
  programming, e.g.~sharing of common intermediate results between
  recursive calls.  This idea is expressed by an auxiliary operation
  which computes a Fibonacci number and its successor simultaneously:
*}

definition %quote fib_step :: "nat \<Rightarrow> nat \<times> nat" where
  "fib_step n = (fib (Suc n), fib n)"

text {*
  \noindent This operation can be implemented by recursion using
  dynamic programming:
*}

lemma %quote [code]:
  "fib_step 0 = (Suc 0, 0)"
  "fib_step (Suc n) = (let (m, q) = fib_step n in (m + q, m))"
  by (simp_all add: fib_step_def)

text {*
  \noindent What remains is to implement @{const fib} by @{const
  fib_step} as follows:
*}

lemma %quote [code]:
  "fib 0 = 0"
  "fib (Suc n) = fst (fib_step n)"
  by (simp_all add: fib_step_def)

text {*
  \noindent The resulting code shows only linear growth of runtime:
*}

text %quote {*@{code_stmts fib (consts) fib fib_step (Haskell)}*}


subsection {* Datatypes \label{sec:datatypes} *}

text {*
  Conceptually, any datatype is spanned by a set of
  \emph{constructors} of type @{text "\<tau> = \<dots> \<Rightarrow> \<kappa> \<alpha>\<^isub>1 \<dots> \<alpha>\<^isub>n"} where @{text
  "{\<alpha>\<^isub>1, \<dots>, \<alpha>\<^isub>n}"} is exactly the set of \emph{all} type variables in
  @{text "\<tau>"}.  The HOL datatype package by default registers any new
  datatype in the table of datatypes, which may be inspected using the
  @{command print_codesetup} command.

  In some cases, it is appropriate to alter or extend this table.  As
  an example, we will develop an alternative representation of the
  queue example given in \secref{sec:queue_example}.  The amortised
  representation is convenient for generating code but exposes its
  \qt{implementation} details, which may be cumbersome when proving
  theorems about it.  Therefore, here is a simple, straightforward
  representation of queues:
*}

datatype %quote 'a queue = Queue "'a list"

definition %quote empty :: "'a queue" where
  "empty = Queue []"

primrec %quote enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "enqueue x (Queue xs) = Queue (xs @ [x])"

fun %quote dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
    "dequeue (Queue []) = (None, Queue [])"
  | "dequeue (Queue (x # xs)) = (Some x, Queue xs)"

text {*
  \noindent This we can use directly for proving;  for executing,
  we provide an alternative characterisation:
*}

definition %quote AQueue :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a queue" where
  "AQueue xs ys = Queue (ys @ rev xs)"

code_datatype %quote AQueue

text {*
  \noindent Here we define a \qt{constructor} @{const "AQueue"} which
  is defined in terms of @{text "Queue"} and interprets its arguments
  according to what the \emph{content} of an amortised queue is supposed
  to be.  Equipped with this, we are able to prove the following equations
  for our primitive queue operations which \qt{implement} the simple
  queues in an amortised fashion:
*}

lemma %quote empty_AQueue [code]:
  "empty = AQueue [] []"
  unfolding AQueue_def empty_def by simp

lemma %quote enqueue_AQueue [code]:
  "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"
  unfolding AQueue_def by simp

lemma %quote dequeue_AQueue [code]:
  "dequeue (AQueue xs []) =
    (if xs = [] then (None, AQueue [] [])
    else dequeue (AQueue [] (rev xs)))"
  "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
  unfolding AQueue_def by simp_all

text {*
  \noindent For completeness, we provide a substitute for the
  @{text case} combinator on queues:
*}

lemma %quote queue_case_AQueue [code]:
  "queue_case f (AQueue xs ys) = f (ys @ rev xs)"
  unfolding AQueue_def by simp

text {*
  \noindent The resulting code looks as expected:
*}

text %quote {*@{code_stmts empty enqueue dequeue (SML)}*}

text {*
  \noindent From this example, it can be glimpsed that using own
  constructor sets is a little delicate since it changes the set of
  valid patterns for values of that type.  Without going into much
  detail, here some practical hints:

  \begin{itemize}

    \item When changing the constructor set for datatypes, take care
      to provide alternative equations for the @{text case} combinator.

    \item Values in the target language need not to be normalised --
      different values in the target language may represent the same
      value in the logic.

    \item Usually, a good methodology to deal with the subtleties of
      pattern matching is to see the type as an abstract type: provide
      a set of operations which operate on the concrete representation
      of the type, and derive further operations by combinations of
      these primitive ones, without relying on a particular
      representation.

  \end{itemize}
*}

end
