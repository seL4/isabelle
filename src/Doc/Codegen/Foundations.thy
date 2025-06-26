theory Foundations
imports Introduction
begin

section \<open>Code generation foundations \label{sec:foundations}\<close>

subsection \<open>Code generator architecture \label{sec:architecture}\<close>

text \<open>
  The code generator is actually a framework consisting of different
  components which can be customised individually.

  Conceptually all components operate on Isabelle's logic framework
  Pure.  Practically, the object logic HOL
  provides the necessary facilities to make use of the code generator,
  mainly since it is an extension of Isabelle/Pure.

  The constellation of the different components is visualized in the
  following picture.

  \begin{figure}[h]
    \def\sys#1{\emph{#1}}
    \begin{tikzpicture}[x = 4cm, y = 1cm]
      \tikzstyle positive=[color = black, fill = white];
      \tikzstyle negative=[color = white, fill = black];
      \tikzstyle entity=[rounded corners, draw, thick];
      \tikzstyle process=[ellipse, draw, thick];
      \tikzstyle arrow=[-stealth, semithick];
      \node (spec) at (0, 3) [entity, positive] {specification tools};
      \node (user) at (1, 3) [entity, positive] {user proofs};
      \node (spec_user_join) at (0.5, 3) [shape=coordinate] {};
      \node (raw) at (0.5, 4) [entity, positive] {raw code equations};
      \node (pre) at (1.5, 4) [process, positive] {preprocessing};
      \node (eqn) at (2.5, 4) [entity, positive] {code equations};
      \node (iml) at (0.5, 0) [entity, positive] {intermediate program};
      \node (seri) at (1.5, 0) [process, positive] {serialisation};
      \node (SML) at (2.5, 3) [entity, positive] {\sys{SML}};
      \node (OCaml) at (2.5, 2) [entity, positive] {\sys{OCaml}};
      \node (Haskell) at (2.5, 1) [entity, positive] {\sys{Haskell}};
      \node (Scala) at (2.5, 0) [entity, positive] {\sys{Scala}};
      \draw [semithick] (spec) -- (spec_user_join);
      \draw [semithick] (user) -- (spec_user_join);
      \draw [-diamond, semithick] (spec_user_join) -- (raw);
      \draw [arrow] (raw) -- (pre);
      \draw [arrow] (pre) -- (eqn);
      \draw [arrow] (eqn) -- node (transl) [process, positive] {translation} (iml);
      \draw [arrow] (iml) -- (seri);
      \draw [arrow] (seri) -- (SML);
      \draw [arrow] (seri) -- (OCaml);
      \draw [arrow] (seri) -- (Haskell);
      \draw [arrow] (seri) -- (Scala);
    \end{tikzpicture}
    \caption{Code generator architecture}
    \label{fig:arch}
  \end{figure}

  \noindent Central to code generation is the notion of \emph{code
  equations}.  A code equation as a first approximation is a theorem
  of the form \<open>f t\<^sub>1 t\<^sub>2 \<dots> t\<^sub>n \<equiv> t\<close> (an equation headed by a
  constant \<open>f\<close> with arguments \<open>t\<^sub>1 t\<^sub>2 \<dots> t\<^sub>n\<close> and right
  hand side \<open>t\<close>).

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
      \qt{Mini-Haskell} with four \qn{statements}: \<open>data\<close> (for
      datatypes), \<open>fun\<close> (stemming from code equations), also
      \<open>class\<close> and \<open>inst\<close> (for type classes).

    \item Finally, the abstract program is \qn{serialised} into
      concrete source code of a target language.  This step only
      produces concrete syntax but does not change the program in
      essence; all conceptual transformations occur in the translation
      step.

  \end{itemize}

  \noindent From these steps, only the last two are carried out
  outside the logic; by keeping this layer as thin as possible, the
  amount of code to trust is kept to a minimum.
\<close>


subsection \<open>The pre- and postprocessor \label{sec:preproc}\<close>

text \<open>
  Before selected function theorems are turned into abstract code, a
  chain of definitional transformation steps is carried out:
  \emph{preprocessing}.  The preprocessor consists of two
  components: a \emph{simpset} and \emph{function transformers}.

  The preprocessor simpset has a disparate brother, the
  \emph{postprocessor simpset}.
  In the theory-to-code scenario depicted in the picture 
  above, it plays no role.  But if generated code is used
  to evaluate expressions (cf.~\secref{sec:evaluation}), the
  postprocessor simpset is applied to the resulting expression before this
  is turned back.

  The pre- and postprocessor \emph{simpsets} can apply the
  full generality of the Isabelle
  simplifier.  Due to the interpretation of theorems as code
  equations, rewrites are applied to the right hand side and the
  arguments of the left hand side of an equation, but never to the
  constant heading the left hand side.

  Pre- and postprocessor can be setup to transfer between
  expressions suitable for logical reasoning and expressions 
  suitable for execution.  As example, take list membership; logically
  it is expressed as \<^term>\<open>x \<in> set xs\<close>.  But for execution
  the intermediate set is not desirable.  Hence the following
  specification:
\<close>

definition %quote member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
where
  [code_abbrev]: "member xs x \<longleftrightarrow> x \<in> set xs"

text \<open>
  \noindent The \emph{@{attribute code_abbrev} attribute} declares
  its theorem a rewrite rule for the postprocessor and the symmetric
  of its theorem as rewrite rule for the preprocessor.  Together,
  this has the effect that expressions @{thm (rhs) member_def [no_vars]}
  are replaced by @{thm (lhs) member_def [no_vars]} in generated code, but
  are turned back into @{thm (rhs) member_def [no_vars]} if generated
  code is used for evaluation.

  Rewrite rules for pre- or postprocessor may be
  declared independently using \emph{@{attribute code_unfold}}
  or \emph{@{attribute code_post}} respectively.

  \emph{Function transformers} provide a very general
  interface, transforming a list of function theorems to another list
  of function theorems, provided that neither the heading constant nor
  its type change.  The \<^term>\<open>0::nat\<close> / \<^const>\<open>Suc\<close> pattern
  used in theory \<open>Code_Abstract_Nat\<close> (see \secref{abstract_nat})
  uses this interface.

  \noindent The current setup of the pre- and postprocessor may be inspected
  using the @{command_def print_codeproc} command.  @{command_def
  code_thms} (see \secref{sec:equations}) provides a convenient
  mechanism to inspect the impact of a preprocessor setup on code
  equations.  Attribute @{attribute code_preproc_trace} allows
  for low-level tracing:
\<close>

declare %quote [[code_preproc_trace]]

declare %quote [[code_preproc_trace only: distinct remdups]]

declare %quote [[code_preproc_trace off]]


subsection \<open>Understanding code equations \label{sec:equations}\<close>

text \<open>
  As told in \secref{sec:principle}, the notion of code equations is
  vital to code generation.  Indeed most problems which occur in
  practice can be resolved by an inspection of the underlying code
  equations.

  It is possible to exchange the default code equations for constants
  by explicitly proving alternative ones:
\<close>

lemma %quote [code]:
  "dequeue (AQueue xs []) =
     (if xs = [] then (None, AQueue [] [])
       else dequeue (AQueue [] (rev xs)))"
  "dequeue (AQueue xs (y # ys)) =
     (Some y, AQueue xs ys)"
  by (cases xs, simp_all) (cases "rev xs", simp_all)

text \<open>
  \noindent The annotation \<open>[code]\<close> is an \<open>attribute\<close>
  which states that the given theorems should be considered as code
  equations for a \<open>fun\<close> statement -- the corresponding constant
  is determined syntactically.  The resulting code:
\<close>

text %quote \<open>
  @{code_stmts dequeue constant: dequeue (Haskell)}
\<close>

text \<open>
  \noindent You may note that the equality test \<^term>\<open>xs = []\<close> has
  been replaced by the predicate \<^term>\<open>List.null xs\<close>.  This is due
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
\<close>

code_thms %quote dequeue

text \<open>
  \noindent This prints a table with the code equations for \<^const>\<open>dequeue\<close>, including \emph{all} code equations those equations depend
  on recursively.  These dependencies themselves can be visualized using
  the @{command_def code_deps} command.
\<close>


subsection \<open>Equality\<close>

text \<open>
  Implementation of equality deserves some attention.  Here an example
  function involving polymorphic equality:
\<close>

primrec %quote collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "collect_duplicates xs ys [] = xs"
| "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
    then if z \<in> set ys
      then collect_duplicates xs ys zs
      else collect_duplicates xs (z#ys) zs
    else collect_duplicates (z#xs) (z#ys) zs)"

text \<open>
  \noindent During preprocessing, the membership test is rewritten,
  resulting in \<^const>\<open>List.member\<close>, which itself performs an explicit
  equality check, as can be seen in the corresponding \<open>SML\<close> code:
\<close>

text %quote \<open>
  @{code_stmts collect_duplicates (SML)}
\<close>

text \<open>
  \noindent Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  HOL introduces an
  explicit class \<^class>\<open>equal\<close> with a corresponding operation \<^const>\<open>HOL.equal\<close> such that @{thm equal [no_vars]}.  The preprocessing
  framework does the rest by propagating the \<^class>\<open>equal\<close> constraints
  through all dependent code equations.  For datatypes, instances of
  \<^class>\<open>equal\<close> are implicitly derived when possible.  For other types,
  you may instantiate \<open>equal\<close> manually like any other type class.
\<close>


subsection \<open>Explicit partiality \label{sec:partiality}\<close>

text \<open>
  Explicit partiality is caused by missing patterns
 (in contrast to partiality caused by nontermination, which is covered in Section~\ref{sec:partial}).
 Here is an example, again for amortised queues:
\<close>

definition %quote strict_dequeue :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "strict_dequeue q = (case dequeue q
    of (Some x, q') \<Rightarrow> (x, q'))"

lemma %quote strict_dequeue_AQueue [code]:
  "strict_dequeue (AQueue xs []) =
    (case rev xs of y # ys \<Rightarrow> (y, AQueue [] ys))"
  "strict_dequeue (AQueue xs (y # ys)) = (y, AQueue xs ys)"
  by (simp_all add: strict_dequeue_def) (cases xs, simp_all split: list.split)

text \<open>
  \noindent In the corresponding code, there is no equation
  for the pattern \<^term>\<open>AQueue [] []\<close>:
\<close>

text %quote \<open>
  @{code_stmts strict_dequeue constant: strict_dequeue (Haskell)}
\<close>

text \<open>
  \noindent In some cases it is desirable to state this
  pseudo-\qt{partiality} more explicitly, e.g.~as follows:
\<close>

axiomatization %quote empty_queue :: 'a

definition %quote strict_dequeue' :: "'a queue \<Rightarrow> 'a \<times> 'a queue" where
  "strict_dequeue' q = (case dequeue q of (Some x, q') \<Rightarrow> (x, q')
    | _ \<Rightarrow> empty_queue)"

lemma %quote strict_dequeue'_AQueue [code]:
  "strict_dequeue' (AQueue xs []) = (if xs = [] then empty_queue
     else strict_dequeue' (AQueue [] (rev xs)))"
  "strict_dequeue' (AQueue xs (y # ys)) =
     (y, AQueue xs ys)"
  by (simp_all add: strict_dequeue'_def split: list.splits)

text \<open>
  Observe that on the right hand side of the definition of \<^const>\<open>strict_dequeue'\<close>, the unspecified constant \<^const>\<open>empty_queue\<close> occurs.
  An attempt to generate code for \<^const>\<open>strict_dequeue'\<close> would
  make the code generator complain that \<^const>\<open>empty_queue\<close> has
  no associated code equations.  In most situations unimplemented
  constants indeed indicated a broken program; however such
  constants can also be thought of as function definitions which always fail,
  since there is never a successful pattern match on the left hand
  side.  In order to categorise a constant into that category
  explicitly, use the @{attribute code} attribute with
  \<open>abort\<close>:
\<close>

declare %quote [[code abort: empty_queue]]

text \<open>
  \noindent Then the code generator will just insert an error or
  exception at the appropriate position:
\<close>

text %quote \<open>
  @{code_stmts strict_dequeue' constant: empty_queue strict_dequeue' (Haskell)}
\<close>

text \<open>
  \noindent This feature however is rarely needed in practice.  Note
  that the HOL default setup already includes
\<close>

declare %quote [[code abort: undefined]]

text \<open>
  \noindent -- hence \<^const>\<open>undefined\<close> can always be used in such
  situations.
\<close>


subsection \<open>If something goes utterly wrong \label{sec:utterly_wrong}\<close>

text \<open>
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
\<close>

end
