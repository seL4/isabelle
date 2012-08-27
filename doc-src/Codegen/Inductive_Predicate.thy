theory Inductive_Predicate
imports Setup
begin

(*<*)
hide_const %invisible append

inductive %invisible append where
  "append [] ys ys"
| "append xs ys zs \<Longrightarrow> append (x # xs) ys (x # zs)"

lemma %invisible append: "append xs ys zs = (xs @ ys = zs)"
  by (induct xs arbitrary: ys zs) (auto elim: append.cases intro: append.intros)

lemmas lexordp_def = 
  lexordp_def [unfolded lexord_def mem_Collect_eq split]
(*>*)

section {* Inductive Predicates \label{sec:inductive} *}

text {*
  The @{text "predicate compiler"} is an extension of the code generator
  which turns inductive specifications into equational ones, from
  which in turn executable code can be generated.  The mechanisms of
  this compiler are described in detail in
  \cite{Berghofer-Bulwahn-Haftmann:2009:TPHOL}.

  Consider the simple predicate @{const append} given by these two
  introduction rules:
*}

text %quote {*
  @{thm append.intros(1)[of ys]} \\
  @{thm append.intros(2)[of xs ys zs x]}
*}

text {*
  \noindent To invoke the compiler, simply use @{command_def "code_pred"}:
*}

code_pred %quote append .

text {*
  \noindent The @{command "code_pred"} command takes the name of the
  inductive predicate and then you put a period to discharge a trivial
  correctness proof.  The compiler infers possible modes for the
  predicate and produces the derived code equations.  Modes annotate
  which (parts of the) arguments are to be taken as input, and which
  output. Modes are similar to types, but use the notation @{text "i"}
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
  \noindent If you are only interested in the first elements of the
  set comprehension (with respect to a depth-first search on the
  introduction rules), you can pass an argument to @{command "values"}
  to specify the number of elements you want:
*}

values %quote 1 "{(xs, ys). append xs ys [(1::nat), 2, 3, 4]}"
values %quote 3 "{(xs, ys). append xs ys [(1::nat), 2, 3, 4]}"

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

subsection {* Alternative names for functions *}

text {* 
  By default, the functions generated from a predicate are named after
  the predicate with the mode mangled into the name (e.g., @{text
  "append_i_i_o"}).  You can specify your own names as follows:
*}

code_pred %quote (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as concat,
  o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool as split,
  i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool as suffix) append .

subsection {* Alternative introduction rules *}

text {*
  Sometimes the introduction rules of an predicate are not executable
  because they contain non-executable constants or specific modes
  could not be inferred.  It is also possible that the introduction
  rules yield a function that loops forever due to the execution in a
  depth-first search manner.  Therefore, you can declare alternative
  introduction rules for predicates with the attribute @{attribute
  "code_pred_intro"}.  For example, the transitive closure is defined
  by:
*}

text %quote {*
  @{lemma [source] "r a b \<Longrightarrow> tranclp r a b" by (fact tranclp.intros(1))}\\
  @{lemma [source] "tranclp r a b \<Longrightarrow> r b c \<Longrightarrow> tranclp r a c" by (fact tranclp.intros(2))}
*}

text {*
  \noindent These rules do not suit well for executing the transitive
  closure with the mode @{text "(i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool"}, as
  the second rule will cause an infinite loop in the recursive call.
  This can be avoided using the following alternative rules which are
  declared to the predicate compiler by the attribute @{attribute
  "code_pred_intro"}:
*}

lemma %quote [code_pred_intro]:
  "r a b \<Longrightarrow> tranclp r a b"
  "r a b \<Longrightarrow> tranclp r b c \<Longrightarrow> tranclp r a c"
by auto

text {*
  \noindent After declaring all alternative rules for the transitive
  closure, you invoke @{command "code_pred"} as usual.  As you have
  declared alternative rules for the predicate, you are urged to prove
  that these introduction rules are complete, i.e., that you can
  derive an elimination rule for the alternative rules:
*}

code_pred %quote tranclp
proof -
  case tranclp
  from this converse_tranclpE [OF tranclp.prems] show thesis by metis
qed

text {*
  \noindent Alternative rules can also be used for constants that have
  not been defined inductively. For example, the lexicographic order
  which is defined as:
*}

text %quote {*
  @{thm [display] lexordp_def [of r]}
*}

text {*
  \noindent To make it executable, you can derive the following two
  rules and prove the elimination rule:
*}

lemma %quote [code_pred_intro]:
  "append xs (a # v) ys \<Longrightarrow> lexordp r xs ys"
(*<*)unfolding lexordp_def by (auto simp add: append)(*>*)

lemma %quote [code_pred_intro]:
  "append u (a # v) xs \<Longrightarrow> append u (b # w) ys \<Longrightarrow> r a b
  \<Longrightarrow> lexordp r xs ys"
(*<*)unfolding lexordp_def append apply simp
apply (rule disjI2) by auto(*>*)

code_pred %quote lexordp
(*<*)proof -
  fix r xs ys
  assume lexord: "lexordp r xs ys"
  assume 1: "\<And>r' xs' ys' a v. r = r' \<Longrightarrow> xs = xs' \<Longrightarrow> ys = ys'
    \<Longrightarrow> append xs' (a # v) ys' \<Longrightarrow> thesis"
  assume 2: "\<And>r' xs' ys' u a v b w. r = r' \<Longrightarrow> xs = xs' \<Longrightarrow> ys = ys'
    \<Longrightarrow> append u (a # v) xs' \<Longrightarrow> append u (b # w) ys' \<Longrightarrow> r' a b \<Longrightarrow> thesis"
  {
    assume "\<exists>a v. ys = xs @ a # v"
    from this 1 have thesis
        by (fastforce simp add: append)
  } moreover
  {
    assume "\<exists>u a b v w. r a b \<and> xs = u @ a # v \<and> ys = u @ b # w"
    from this 2 have thesis by (fastforce simp add: append)
  } moreover
  note lexord
  ultimately show thesis
    unfolding lexordp_def
    by fastforce
qed(*>*)


subsection {* Options for values *}

text {*
  In the presence of higher-order predicates, multiple modes for some
  predicate could be inferred that are not disambiguated by the
  pattern of the set comprehension.  To disambiguate the modes for the
  arguments of a predicate, you can state the modes explicitly in the
  @{command "values"} command.  Consider the simple predicate @{term
  "succ"}:
*}

inductive %quote succ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "succ 0 (Suc 0)"
| "succ x y \<Longrightarrow> succ (Suc x) (Suc y)"

code_pred %quote succ .

text {*
  \noindent For this, the predicate compiler can infer modes @{text "o
  \<Rightarrow> o \<Rightarrow> bool"}, @{text "i \<Rightarrow> o \<Rightarrow> bool"}, @{text "o \<Rightarrow> i \<Rightarrow> bool"} and
  @{text "i \<Rightarrow> i \<Rightarrow> bool"}.  The invocation of @{command "values"}
  @{text "{n. tranclp succ 10 n}"} loops, as multiple modes for the
  predicate @{text "succ"} are possible and here the first mode @{text
  "o \<Rightarrow> o \<Rightarrow> bool"} is chosen. To choose another mode for the argument,
  you can declare the mode for the argument between the @{command
  "values"} and the number of elements.
*}

values %quote [mode: i \<Rightarrow> o \<Rightarrow> bool] 1 "{n. tranclp succ 10 n}" (*FIMXE does not terminate for n\<ge>1*)
values %quote [mode: o \<Rightarrow> i \<Rightarrow> bool] 1 "{n. tranclp succ n 10}"


subsection {* Embedding into functional code within Isabelle/HOL *}

text {*
  To embed the computation of an inductive predicate into functions
  that are defined in Isabelle/HOL, you have a number of options:

  \begin{itemize}

    \item You want to use the first-order predicate with the mode
      where all arguments are input. Then you can use the predicate directly, e.g.

      \begin{quote}
        @{text "valid_suffix ys zs = "} \\
        @{text "(if append [Suc 0, 2] ys zs then Some ys else None)"}
      \end{quote}

    \item If you know that the execution returns only one value (it is
      deterministic), then you can use the combinator @{term
      "Predicate.the"}, e.g., a functional concatenation of lists is
      defined with

      \begin{quote}
        @{term "functional_concat xs ys = Predicate.the (append_i_i_o xs ys)"}
      \end{quote}

      Note that if the evaluation does not return a unique value, it
      raises a run-time error @{term "not_unique"}.

  \end{itemize}
*}


subsection {* Further Examples *}

text {*
  Further examples for compiling inductive predicates can be found in
  the @{text "HOL/ex/Predicate_Compile_ex.thy"} theory file.  There are
  also some examples in the Archive of Formal Proofs, notably in the
  @{text "POPLmark-deBruijn"} and the @{text "FeatherweightJava"}
  sessions.
*}

end

