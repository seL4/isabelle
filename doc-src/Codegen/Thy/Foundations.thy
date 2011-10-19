theory Foundations
imports Introduction
begin

section {* Code generation foundations \label{sec:foundations} *}

subsection {* Code generator architecture \label{sec:architecture} *}

text {*
  The code generator is actually a framework consisting of different
  components which can be customised individually.

  Conceptually all components operate on Isabelle's logic framework
  @{theory Pure}.  Practically, the object logic @{theory HOL}
  provides the necessary facilities to make use of the code generator,
  mainly since it is an extension of @{theory Pure}.

  The constellation of the different components is visualized in the
  following picture.

  \begin{figure}[h]
    \includegraphics{architecture}
    \caption{Code generator architecture}
    \label{fig:arch}
  \end{figure}

  \noindent Central to code generation is the notion of \emph{code
  equations}.  A code equation as a first approximation is a theorem
  of the form @{text "f t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n \<equiv> t"} (an equation headed by a
  constant @{text f} with arguments @{text "t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n"} and right
  hand side @{text t}).

  \begin{itemize}

    \item Starting point of code generation is a collection of (raw)
      code equations in a theory. It is not relevant where they stem
      from, but typically they were either produced by specification
      tools or proved explicitly by the user.
      
    \item These raw code equations can be subjected to theorem
      transformations.  This \qn{preprocessor} (see
      \secref{sec:preproc}) can apply the full expressiveness of
      ML-based theorem transformations to code generation.  The result
      of preprocessing is a structured collection of code equations.

    \item These code equations are \qn{translated} to a program in an
      abstract intermediate language.  Think of it as a kind of
      \qt{Mini-Haskell} with four \qn{statements}: @{text data} (for
      datatypes), @{text fun} (stemming from code equations), also
      @{text class} and @{text inst} (for type classes).

    \item Finally, the abstract program is \qn{serialised} into
      concrete source code of a target language.  This step only
      produces concrete syntax but does not change the program in
      essence; all conceptual transformations occur in the translation
      step.

  \end{itemize}

  \noindent From these steps, only the last two are carried out
  outside the logic; by keeping this layer as thin as possible, the
  amount of code to trust is kept to a minimum.
*}


subsection {* The preprocessor \label{sec:preproc} *}

text {*
  Before selected function theorems are turned into abstract code, a
  chain of definitional transformation steps is carried out:
  \emph{preprocessing}.  The preprocessor consists of two
  components: a \emph{simpset} and \emph{function transformers}.

  The \emph{simpset} can apply the full generality of the Isabelle
  simplifier.  Due to the interpretation of theorems as code
  equations, rewrites are applied to the right hand side and the
  arguments of the left hand side of an equation, but never to the
  constant heading the left hand side.  An important special case are
  \emph{unfold theorems}, which may be declared and removed using the
  @{attribute code_unfold} or \emph{@{attribute code_unfold} del}
  attribute, respectively.

  Some common applications:
*}

text_raw {*
  \begin{itemize}
*}

text {*
     \item replacing non-executable constructs by executable ones:
*}     

lemma %quote [code_unfold]:
  "x \<in> set xs \<longleftrightarrow> List.member xs x" by (fact in_set_member)

text {*
     \item replacing executable but inconvenient constructs:
*}

lemma %quote [code_unfold]:
  "xs = [] \<longleftrightarrow> List.null xs" by (fact eq_Nil_null)

text {*
     \item eliminating disturbing expressions:
*}

lemma %quote [code_unfold]:
  "1 = Suc 0" by (fact One_nat_def)

text_raw {*
  \end{itemize}
*}

text {*
  \noindent \emph{Function transformers} provide a very general
  interface, transforming a list of function theorems to another list
  of function theorems, provided that neither the heading constant nor
  its type change.  The @{term "0\<Colon>nat"} / @{const Suc} pattern
  elimination implemented in theory @{theory Efficient_Nat} (see
  \secref{eff_nat}) uses this interface.

  \noindent The current setup of the preprocessor may be inspected
  using the @{command_def print_codeproc} command.  @{command_def
  code_thms} (see \secref{sec:equations}) provides a convenient
  mechanism to inspect the impact of a preprocessor setup on code
  equations.
*}


subsection {* Understanding code equations \label{sec:equations} *}

text {*
  As told in \secref{sec:principle}, the notion of code equations is
  vital to code generation.  Indeed most problems which occur in
  practice can be resolved by an inspection of the underlying code
  equations.

  It is possible to exchange the default code equations for constants
  by explicitly proving alternative ones:
*}

lemma %quote [code]:
  "dequeue (AQueue xs []) =
     (if xs = [] then (None, AQueue [] [])
       else dequeue (AQueue [] (rev xs)))"
  "dequeue (AQueue xs (y # ys)) =
     (Some y, AQueue xs ys)"
  by (cases xs, simp_all) (cases "rev xs", simp_all)

text {*
  \noindent The annotation @{text "[code]"} is an @{text attribute}
  which states that the given theorems should be considered as code
  equations for a @{text fun} statement -- the corresponding constant
  is determined syntactically.  The resulting code:
*}

text %quotetypewriter {*
  @{code_stmts dequeue (consts) dequeue (Haskell)}
*}

text {*
  \noindent You may note that the equality test @{term "xs = []"} has
  been replaced by the predicate @{term "List.null xs"}.  This is due
  to the default setup of the \qn{preprocessor}.

  This possibility to select arbitrary code equations is the key
  technique for program and datatype refinement (see
  \secref{sec:refinement}).

  Due to the preprocessor, there is the distinction of raw code
  equations (before preprocessing) and code equations (after
  preprocessing).

  The first can be listed (among other data) using the @{command_def
  print_codesetup} command.

  The code equations after preprocessing are already are blueprint of
  the generated program and can be inspected using the @{command
  code_thms} command:
*}

code_thms %quote dequeue

text {*
  \noindent This prints a table with the code equations for @{const
  dequeue}, including \emph{all} code equations those equations depend
  on recursively.  These dependencies themselves can be visualized using
  the @{command_def code_deps} command.
*}


subsection {* Equality *}

text {*
  Implementation of equality deserves some attention.  Here an example
  function involving polymorphic equality:
*}

primrec %quote collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "collect_duplicates xs ys [] = xs"
| "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
    then if z \<in> set ys
      then collect_duplicates xs ys zs
      else collect_duplicates xs (z#ys) zs
    else collect_duplicates (z#xs) (z#ys) zs)"

text {*
  \noindent During preprocessing, the membership test is rewritten,
  resulting in @{const List.member}, which itself performs an explicit
  equality check, as can be seen in the corresponding @{text SML} code:
*}

text %quotetypewriter {*
  @{code_stmts collect_duplicates (SML)}
*}

text {*
  \noindent Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  HOL introduces an
  explicit class @{class equal} with a corresponding operation @{const
  HOL.equal} such that @{thm equal [no_vars]}.  The preprocessing
  framework does the rest by propagating the @{class equal} constraints
  through all dependent code equations.  For datatypes, instances of
  @{class equal} are implicitly derived when possible.  For other types,
  you may instantiate @{text equal} manually like any other type class.
*}


subsection {* Explicit partiality \label{sec:partiality} *}

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
  by (simp_all add: strict_dequeue_def) (cases xs, simp_all split: list.split)

text {*
  \noindent In the corresponding code, there is no equation
  for the pattern @{term "AQueue [] []"}:
*}

text %quotetypewriter {*
  @{code_stmts strict_dequeue (consts) strict_dequeue (Haskell)}
*}

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
  by (simp_all add: strict_dequeue'_def split: list.splits)

text {*
  Observe that on the right hand side of the definition of @{const
  "strict_dequeue'"}, the unspecified constant @{const empty_queue} occurs.

  Normally, if constants without any code equations occur in a
  program, the code generator complains (since in most cases this is
  indeed an error).  But such constants can also be thought
  of as function definitions which always fail,
  since there is never a successful pattern match on the left hand
  side.  In order to categorise a constant into that category
  explicitly, use @{command_def "code_abort"}:
*}

code_abort %quote empty_queue

text {*
  \noindent Then the code generator will just insert an error or
  exception at the appropriate position:
*}

text %quotetypewriter {*
  @{code_stmts strict_dequeue' (consts) empty_queue strict_dequeue' (Haskell)}
*}

text {*
  \noindent This feature however is rarely needed in practice.  Note
  also that the HOL default setup already declares @{const undefined}
  as @{command "code_abort"}, which is most likely to be used in such
  situations.
*}


subsection {* If something goes utterly wrong \label{sec:utterly_wrong} *}

text {*
  Under certain circumstances, the code generator fails to produce
  code entirely.  To debug these, the following hints may prove
  helpful:

  \begin{description}

    \ditem{\emph{Check with a different target language}.}  Sometimes
      the situation gets more clear if you switch to another target
      language; the code generated there might give some hints what
      prevents the code generator to produce code for the desired
      language.

    \ditem{\emph{Inspect code equations}.}  Code equations are the central
      carrier of code generation.  Most problems occurring while generating
      code can be traced to single equations which are printed as part of
      the error message.  A closer inspection of those may offer the key
      for solving issues (cf.~\secref{sec:equations}).

    \ditem{\emph{Inspect preprocessor setup}.}  The preprocessor might
      transform code equations unexpectedly; to understand an
      inspection of its setup is necessary (cf.~\secref{sec:preproc}).

    \ditem{\emph{Generate exceptions}.}  If the code generator
      complains about missing code equations, in can be helpful to
      implement the offending constants as exceptions
      (cf.~\secref{sec:partiality}); this allows at least for a formal
      generation of code, whose inspection may then give clues what is
      wrong.

    \ditem{\emph{Remove offending code equations}.}  If code
      generation is prevented by just a single equation, this can be
      removed (cf.~\secref{sec:equations}) to allow formal code
      generation, whose result in turn can be used to trace the
      problem.  The most prominent case here are mismatches in type
      class signatures (\qt{wellsortedness error}).

  \end{description}
*}

end
