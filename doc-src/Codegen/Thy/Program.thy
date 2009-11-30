theory Program
imports Introduction
begin

section {* Turning Theories into Programs \label{sec:program} *}

subsection {* The @{text "Isabelle/HOL"} default setup *}

text {*
  We have already seen how by default equations stemming from
  @{command definition}/@{command primrec}/@{command fun}
  statements are used for code generation.  This default behaviour
  can be changed, e.g. by providing different code equations.
  All kinds of customisation shown in this section is \emph{safe}
  in the sense that the user does not have to worry about
  correctness -- all programs generatable that way are partially
  correct.
*}

subsection {* Selecting code equations *}

text {*
  Coming back to our introductory example, we
  could provide an alternative code equations for @{const dequeue}
  explicitly:
*}

lemma %quote [code]:
  "dequeue (AQueue xs []) =
     (if xs = [] then (None, AQueue [] [])
       else dequeue (AQueue [] (rev xs)))"
  "dequeue (AQueue xs (y # ys)) =
     (Some y, AQueue xs ys)"
  by (cases xs, simp_all) (cases "rev xs", simp_all)

text {*
  \noindent The annotation @{text "[code]"} is an @{text Isar}
  @{text attribute} which states that the given theorems should be
  considered as code equations for a @{text fun} statement --
  the corresponding constant is determined syntactically.  The resulting code:
*}

text %quote {*@{code_stmts dequeue (consts) dequeue (Haskell)}*}

text {*
  \noindent You may note that the equality test @{term "xs = []"} has been
  replaced by the predicate @{term "null xs"}.  This is due to the default
  setup in the \qn{preprocessor} to be discussed further below (\secref{sec:preproc}).

  Changing the default constructor set of datatypes is also
  possible.  See \secref{sec:datatypes} for an example.

  As told in \secref{sec:concept}, code generation is based
  on a structured collection of code theorems.
  For explorative purpose, this collection
  may be inspected using the @{command code_thms} command:
*}

code_thms %quote dequeue

text {*
  \noindent prints a table with \emph{all} code equations
  for @{const dequeue}, including
  \emph{all} code equations those equations depend
  on recursively.
  
  Similarly, the @{command code_deps} command shows a graph
  visualising dependencies between code equations.
*}

subsection {* @{text class} and @{text instantiation} *}

text {*
  Concerning type classes and code generation, let us examine an example
  from abstract algebra:
*}

class %quote semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

class %quote monoid = semigroup +
  fixes neutral :: 'a ("\<one>")
  assumes neutl: "\<one> \<otimes> x = x"
    and neutr: "x \<otimes> \<one> = x"

instantiation %quote nat :: monoid
begin

primrec %quote mult_nat where
    "0 \<otimes> n = (0\<Colon>nat)"
  | "Suc m \<otimes> n = n + m \<otimes> n"

definition %quote neutral_nat where
  "\<one> = Suc 0"

lemma %quote add_mult_distrib:
  fixes n m q :: nat
  shows "(n + m) \<otimes> q = n \<otimes> q + m \<otimes> q"
  by (induct n) simp_all

instance %quote proof
  fix m n q :: nat
  show "m \<otimes> n \<otimes> q = m \<otimes> (n \<otimes> q)"
    by (induct m) (simp_all add: add_mult_distrib)
  show "\<one> \<otimes> n = n"
    by (simp add: neutral_nat_def)
  show "m \<otimes> \<one> = m"
    by (induct m) (simp_all add: neutral_nat_def)
qed

end %quote

text {*
  \noindent We define the natural operation of the natural numbers
  on monoids:
*}

primrec %quote (in monoid) pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
    "pow 0 a = \<one>"
  | "pow (Suc n) a = a \<otimes> pow n a"

text {*
  \noindent This we use to define the discrete exponentiation function:
*}

definition %quote bexp :: "nat \<Rightarrow> nat" where
  "bexp n = pow n (Suc (Suc 0))"

text {*
  \noindent The corresponding code:
*}

text %quote {*@{code_stmts bexp (Haskell)}*}

text {*
  \noindent This is a convenient place to show how explicit dictionary construction
  manifests in generated code (here, the same example in @{text SML}):
*}

text %quote {*@{code_stmts bexp (SML)}*}

text {*
  \noindent Note the parameters with trailing underscore (@{verbatim "A_"})
    which are the dictionary parameters.
*}

subsection {* The preprocessor \label{sec:preproc} *}

text {*
  Before selected function theorems are turned into abstract
  code, a chain of definitional transformation steps is carried
  out: \emph{preprocessing}.  In essence, the preprocessor
  consists of two components: a \emph{simpset} and \emph{function transformers}.

  The \emph{simpset} allows to employ the full generality of the
  Isabelle simplifier.  Due to the interpretation of theorems as code
  equations, rewrites are applied to the right hand side and the
  arguments of the left hand side of an equation, but never to the
  constant heading the left hand side.  An important special case are
  \emph{unfold theorems} which may be declared and undeclared using
  the @{attribute code_unfold} or \emph{@{attribute code_unfold} del}
  attribute respectively.

  Some common applications:
*}

text_raw {*
  \begin{itemize}
*}

text {*
     \item replacing non-executable constructs by executable ones:
*}     

lemma %quote [code_inline]:
  "x \<in> set xs \<longleftrightarrow> x mem xs" by (induct xs) simp_all

text {*
     \item eliminating superfluous constants:
*}

lemma %quote [code_inline]:
  "1 = Suc 0" by simp

text {*
     \item replacing executable but inconvenient constructs:
*}

lemma %quote [code_inline]:
  "xs = [] \<longleftrightarrow> List.null xs" by (induct xs) simp_all

text_raw {*
  \end{itemize}
*}

text {*
  \noindent \emph{Function transformers} provide a very general interface,
  transforming a list of function theorems to another
  list of function theorems, provided that neither the heading
  constant nor its type change.  The @{term "0\<Colon>nat"} / @{const Suc}
  pattern elimination implemented in
  theory @{text Efficient_Nat} (see \secref{eff_nat}) uses this
  interface.

  \noindent The current setup of the preprocessor may be inspected using
  the @{command print_codeproc} command.
  @{command code_thms} provides a convenient
  mechanism to inspect the impact of a preprocessor setup
  on code equations.

  \begin{warn}

    Attribute @{attribute code_unfold} also applies to the
    preprocessor of the ancient @{text "SML code generator"}; in case
    this is not what you intend, use @{attribute code_inline} instead.
  \end{warn}
*}

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
  queue example given in \secref{sec:intro}.  The amortised
  representation is convenient for generating code but exposes its
  \qt{implementation} details, which may be cumbersome when proving
  theorems about it.  Therefore, here a simple, straightforward
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


subsection {* Equality *}

text {*
  Surely you have already noticed how equality is treated
  by the code generator:
*}

primrec %quote collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "collect_duplicates xs ys [] = xs"
  | "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
      then if z \<in> set ys
        then collect_duplicates xs ys zs
        else collect_duplicates xs (z#ys) zs
      else collect_duplicates (z#xs) (z#ys) zs)"

text {*
  \noindent The membership test during preprocessing is rewritten,
  resulting in @{const List.member}, which itself
  performs an explicit equality check.
*}

text %quote {*@{code_stmts collect_duplicates (SML)}*}

text {*
  \noindent Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  HOL introduces
  an explicit class @{class eq} with a corresponding operation
  @{const eq_class.eq} such that @{thm eq [no_vars]}.
  The preprocessing framework does the rest by propagating the
  @{class eq} constraints through all dependent code equations.
  For datatypes, instances of @{class eq} are implicitly derived
  when possible.  For other types, you may instantiate @{text eq}
  manually like any other type class.
*}


subsection {* Explicit partiality *}

text {*
  Partiality usually enters the game by partial patterns, as
  in the following example, again for amortised queues:
*}

definition %quote strict_dequeue :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "strict_dequeue q = (case dequeue q
    of (Some x, q') \<Rightarrow> (x, q'))"

lemma %quote strict_dequeue_AQueue [code]:
  "strict_dequeue (AQueue xs (y # ys)) = (y, AQueue xs ys)"
  "strict_dequeue (AQueue xs []) =
    (case rev xs of y # ys \<Rightarrow> (y, AQueue [] ys))"
  by (simp_all add: strict_dequeue_def dequeue_AQueue split: list.splits)

text {*
  \noindent In the corresponding code, there is no equation
  for the pattern @{term "AQueue [] []"}:
*}

text %quote {*@{code_stmts strict_dequeue (consts) strict_dequeue (Haskell)}*}

text {*
  \noindent In some cases it is desirable to have this
  pseudo-\qt{partiality} more explicitly, e.g.~as follows:
*}

axiomatization %quote empty_queue :: 'a

definition %quote strict_dequeue' :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "strict_dequeue' q = (case dequeue q of (Some x, q') \<Rightarrow> (x, q') | _ \<Rightarrow> empty_queue)"

lemma %quote strict_dequeue'_AQueue [code]:
  "strict_dequeue' (AQueue xs []) = (if xs = [] then empty_queue
     else strict_dequeue' (AQueue [] (rev xs)))"
  "strict_dequeue' (AQueue xs (y # ys)) =
     (y, AQueue xs ys)"
  by (simp_all add: strict_dequeue'_def dequeue_AQueue split: list.splits)

text {*
  Observe that on the right hand side of the definition of @{const
  "strict_dequeue'"} the constant @{const empty_queue} occurs
  which is unspecified.

  Normally, if constants without any code equations occur in a
  program, the code generator complains (since in most cases this is
  not what the user expects).  But such constants can also be thought
  of as function definitions with no equations which always fail,
  since there is never a successful pattern match on the left hand
  side.  In order to categorise a constant into that category
  explicitly, use @{command "code_abort"}:
*}

code_abort %quote empty_queue

text {*
  \noindent Then the code generator will just insert an error or
  exception at the appropriate position:
*}

text %quote {*@{code_stmts strict_dequeue' (consts) empty_queue strict_dequeue' (Haskell)}*}

text {*
  \noindent This feature however is rarely needed in practice.
  Note also that the @{text HOL} default setup already declares
  @{const undefined} as @{command "code_abort"}, which is most
  likely to be used in such situations.
*}

subsection {* Inductive Predicates *}
(*<*)
hide const append

inductive append
where
  "append [] ys ys"
| "append xs ys zs ==> append (x # xs) ys (x # zs)"
(*>*)
text {*
To execute inductive predicates, a special preprocessor, the predicate
 compiler, generates code equations from the introduction rules of the predicates.
The mechanisms of this compiler are described in \cite{Berghofer-Bulwahn-Haftmann:2009:TPHOL}.
Consider the simple predicate @{const append} given by these two
introduction rules:
*}
text %quote {*
@{thm append.intros(1)[of ys]}\\
\noindent@{thm append.intros(2)[of xs ys zs x]}
*}
text {*
\noindent To invoke the compiler, simply use @{command_def "code_pred"}:
*}
code_pred %quote append .
text {*
\noindent The @{command "code_pred"} command takes the name
of the inductive predicate and then you put a period to discharge
a trivial correctness proof. 
The compiler infers possible modes 
for the predicate and produces the derived code equations.
Modes annotate which (parts of the) arguments are to be taken as input,
and which output. Modes are similar to types, but use the notation @{text "i"}
for input and @{text "o"} for output.
 
For @{term "append"}, the compiler can infer the following modes:
\begin{itemize}
\item @{text "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool"}
\item @{text "i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool"}
\item @{text "o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool"}
\end{itemize}
You can compute sets of predicates using @{command_def "values"}:
*}
values %quote "{zs. append [(1::nat),2,3] [4,5] zs}"
text {* \noindent outputs @{text "{[1, 2, 3, 4, 5]}"}, and *}
values %quote "{(xs, ys). append xs ys [(2::nat),3]}"
text {* \noindent outputs @{text "{([], [2, 3]), ([2], [3]), ([2, 3], [])}"}. *}
text {*
\noindent If you are only interested in the first elements of the set
comprehension (with respect to a depth-first search on the introduction rules), you can
pass an argument to
@{command "values"} to specify the number of elements you want:
*}

values %quote 1 "{(xs, ys). append xs ys [(1::nat),2,3,4]}"
values %quote 3 "{(xs, ys). append xs ys [(1::nat),2,3,4]}"

text {*
\noindent The @{command "values"} command can only compute set
 comprehensions for which a mode has been inferred.

The code equations for a predicate are made available as theorems with
 the suffix @{text "equation"}, and can be inspected with:
*}
thm %quote append.equation
text {*
\noindent More advanced options are described in the following subsections.
*}
subsubsection {* Alternative names for functions *}
text {* 
By default, the functions generated from a predicate are named after the predicate with the
mode mangled into the name (e.g., @{text "append_i_i_o"}).
You can specify your own names as follows:
*}
code_pred %quote (modes: i => i => o => bool as concat,
  o => o => i => bool as split,
  i => o => i => bool as suffix) append .

subsubsection {* Alternative introduction rules *}
text {*
Sometimes the introduction rules of an predicate are not executable because they contain
non-executable constants or specific modes could not be inferred.
It is also possible that the introduction rules yield a function that loops forever
due to the execution in a depth-first search manner.
Therefore, you can declare alternative introduction rules for predicates with the attribute
@{attribute "code_pred_intro"}.
For example, the transitive closure is defined by: 
*}
text %quote {*
@{thm tranclp.intros(1)[of r a b]}\\
\noindent @{thm tranclp.intros(2)[of r a b c]}
*}
text {*
\noindent These rules do not suit well for executing the transitive closure 
with the mode @{text "(i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool"}, as the second rule will
cause an infinite loop in the recursive call.
This can be avoided using the following alternative rules which are
declared to the predicate compiler by the attribute @{attribute "code_pred_intro"}:
*}
lemma %quote [code_pred_intro]:
  "r a b \<Longrightarrow> r\<^sup>+\<^sup>+ a b"
  "r a b \<Longrightarrow> r\<^sup>+\<^sup>+ b c \<Longrightarrow> r\<^sup>+\<^sup>+ a c"
by auto
text {*
\noindent After declaring all alternative rules for the transitive closure,
you invoke @{command "code_pred"} as usual.
As you have declared alternative rules for the predicate, you are urged to prove that these
introduction rules are complete, i.e., that you can derive an elimination rule for the
alternative rules:
*}
code_pred %quote tranclp
proof -
  case tranclp
  from this converse_tranclpE[OF this(1)] show thesis by metis
qed
text {*
\noindent Alternative rules can also be used for constants that have not
been defined inductively. For example, the lexicographic order which
is defined as: *}
text %quote {*
@{thm [display] lexord_def[of "r"]}
*}
text {*
\noindent To make it executable, you can derive the following two rules and prove the
elimination rule:
*}
(*<*)
lemma append: "append xs ys zs = (xs @ ys = zs)"
by (induct xs arbitrary: ys zs) (auto elim: append.cases intro: append.intros)
(*>*)
lemma %quote [code_pred_intro]:
  "append xs (a # v) ys \<Longrightarrow> lexord r (xs, ys)"
(*<*)unfolding lexord_def Collect_def by (auto simp add: append)(*>*)

lemma %quote [code_pred_intro]:
  "append u (a # v) xs \<Longrightarrow> append u (b # w) ys \<Longrightarrow> r (a, b)
  \<Longrightarrow> lexord r (xs, ys)"
(*<*)unfolding lexord_def Collect_def append mem_def apply simp
apply (rule disjI2) by auto
(*>*)

code_pred %quote lexord
(*<*)
proof -
  fix r a1
  assume lexord: "lexord r a1"
  assume 1: "\<And> xs ys a v. a1 = (xs, ys) \<Longrightarrow> append xs (a # v) ys \<Longrightarrow> thesis"
  assume 2: "\<And> xs ys u a v b w. a1 = (xs, ys) \<Longrightarrow> append u (a # v) xs \<Longrightarrow> append u (b # w) ys \<Longrightarrow> r (a, b) \<Longrightarrow> thesis"
  obtain xs ys where a1: "a1 = (xs, ys)" by fastsimp
  {
    assume "\<exists>a v. ys = xs @ a # v"
    from this 1 a1 have thesis
        by (fastsimp simp add: append)
  } moreover
  {
    assume "\<exists>u a b v w. (a, b) \<in> r \<and> xs = u @ a # v \<and> ys = u @ b # w"
    from this 2 a1 have thesis by (fastsimp simp add: append mem_def)
  } moreover
  note lexord[simplified a1]
  ultimately show thesis
    unfolding lexord_def
    by (fastsimp simp add: Collect_def)
qed
(*>*)
subsubsection {* Options for values *}
text {*
In the presence of higher-order predicates, multiple modes for some predicate could be inferred
that are not disambiguated by the pattern of the set comprehension.
To disambiguate the modes for the arguments of a predicate, you can state
the modes explicitly in the @{command "values"} command. 
Consider the simple predicate @{term "succ"}:
*}
inductive succ :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "succ 0 (Suc 0)"
| "succ x y \<Longrightarrow> succ (Suc x) (Suc y)"

code_pred succ .

text {*
\noindent For this, the predicate compiler can infer modes @{text "o \<Rightarrow> o \<Rightarrow> bool"}, @{text "i \<Rightarrow> o \<Rightarrow> bool"},
  @{text "o \<Rightarrow> i \<Rightarrow> bool"} and @{text "i \<Rightarrow> i \<Rightarrow> bool"}.
The invocation of @{command "values"} @{text "{n. tranclp succ 10 n}"} loops, as multiple
modes for the predicate @{text "succ"} are possible and here the first mode @{text "o \<Rightarrow> o \<Rightarrow> bool"}
is chosen. To choose another mode for the argument, you can declare the mode for the argument between
the @{command "values"} and the number of elements.
*}
values %quote [mode: i => o => bool] 20 "{n. tranclp succ 10 n}"
values %quote [mode: o => i => bool] 10 "{n. tranclp succ n 10}"

subsubsection {* Embedding into functional code within Isabelle/HOL *}
text {*
To embed the computation of an inductive predicate into functions that are defined in Isabelle/HOL,
you have a number of options:
\begin{itemize}
\item You want to use the first-order predicate with the mode
  where all arguments are input. Then you can use the predicate directly, e.g.
\begin{quote}
  @{text "valid_suffix ys zs = "}\\
  @{text "(if append [Suc 0, 2] ys zs then Some ys else None)"}
\end{quote}
\item If you know that the execution returns only one value (it is deterministic), then you can
  use the combinator @{term "Predicate.the"}, e.g., a functional concatenation of lists
  is defined with
\begin{quote}
  @{term "functional_concat xs ys = Predicate.the (append_i_i_o xs ys)"}
\end{quote}
  Note that if the evaluation does not return a unique value, it raises a run-time error
  @{term "not_unique"}.
\end{itemize}
*}
subsubsection {* Further Examples *}
text {* Further examples for compiling inductive predicates can be found in
the @{text "HOL/ex/Predicate_Compile_ex"} theory file.
There are also some examples in the Archive of Formal Proofs, notably
in the @{text "POPLmark-deBruijn"} and the @{text "FeatherweightJava"} sessions.
*}
end
