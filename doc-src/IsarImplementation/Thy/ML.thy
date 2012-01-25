theory "ML"
imports Base
begin

chapter {* Isabelle/ML *}

text {* Isabelle/ML is best understood as a certain culture based on
  Standard ML.  Thus it is not a new programming language, but a
  certain way to use SML at an advanced level within the Isabelle
  environment.  This covers a variety of aspects that are geared
  towards an efficient and robust platform for applications of formal
  logic with fully foundational proof construction --- according to
  the well-known \emph{LCF principle}.  There is specific
  infrastructure with library modules to address the needs of this
  difficult task.  For example, the raw parallel programming model of
  Poly/ML is presented as considerably more abstract concept of
  \emph{future values}, which is then used to augment the inference
  kernel, proof interpreter, and theory loader accordingly.

  The main aspects of Isabelle/ML are introduced below.  These
  first-hand explanations should help to understand how proper
  Isabelle/ML is to be read and written, and to get access to the
  wealth of experience that is expressed in the source text and its
  history of changes.\footnote{See
  \url{http://isabelle.in.tum.de/repos/isabelle} for the full
  Mercurial history.  There are symbolic tags to refer to official
  Isabelle releases, as opposed to arbitrary \emph{tip} versions that
  merely reflect snapshots that are never really up-to-date.}  *}


section {* Style and orthography *}

text {* The sources of Isabelle/Isar are optimized for
  \emph{readability} and \emph{maintainability}.  The main purpose is
  to tell an informed reader what is really going on and how things
  really work.  This is a non-trivial aim, but it is supported by a
  certain style of writing Isabelle/ML that has emerged from long
  years of system development.\footnote{See also the interesting style
  guide for OCaml
  \url{http://caml.inria.fr/resources/doc/guides/guidelines.en.html}
  which shares many of our means and ends.}

  The main principle behind any coding style is \emph{consistency}.
  For a single author of a small program this merely means ``choose
  your style and stick to it''.  A complex project like Isabelle, with
  long years of development and different contributors, requires more
  standardization.  A coding style that is changed every few years or
  with every new contributor is no style at all, because consistency
  is quickly lost.  Global consistency is hard to achieve, though.
  Nonetheless, one should always strive at least for local consistency
  of modules and sub-systems, without deviating from some general
  principles how to write Isabelle/ML.

  In a sense, good coding style is like an \emph{orthography} for the
  sources: it helps to read quickly over the text and see through the
  main points, without getting distracted by accidental presentation
  of free-style code.
*}


subsection {* Header and sectioning *}

text {* Isabelle source files have a certain standardized header
  format (with precise spacing) that follows ancient traditions
  reaching back to the earliest versions of the system by Larry
  Paulson.  See @{file "~~/src/Pure/thm.ML"}, for example.

  The header includes at least @{verbatim Title} and @{verbatim
  Author} entries, followed by a prose description of the purpose of
  the module.  The latter can range from a single line to several
  paragraphs of explanations.

  The rest of the file is divided into sections, subsections,
  subsubsections, paragraphs etc.\ using a simple layout via ML
  comments as follows.

\begin{verbatim}
(*** section ***)

(** subsection **)

(* subsubsection *)

(*short paragraph*)

(*
  long paragraph,
  with more text
*)
\end{verbatim}

  As in regular typography, there is some extra space \emph{before}
  section headings that are adjacent to plain text (not other headings
  as in the example above).

  \medskip The precise wording of the prose text given in these
  headings is chosen carefully to introduce the main theme of the
  subsequent formal ML text.
*}


subsection {* Naming conventions *}

text {* Since ML is the primary medium to express the meaning of the
  source text, naming of ML entities requires special care.

  \paragraph{Notation.}  A name consists of 1--3 \emph{words} (rarely
  4, but not more) that are separated by underscore.  There are three
  variants concerning upper or lower case letters, which are used for
  certain ML categories as follows:

  \medskip
  \begin{tabular}{lll}
  variant & example & ML categories \\\hline
  lower-case & @{ML_text foo_bar} & values, types, record fields \\
  capitalized & @{ML_text Foo_Bar} & datatype constructors, structures, functors \\
  upper-case & @{ML_text FOO_BAR} & special values, exception constructors, signatures \\
  \end{tabular}
  \medskip

  For historical reasons, many capitalized names omit underscores,
  e.g.\ old-style @{ML_text FooBar} instead of @{ML_text Foo_Bar}.
  Genuine mixed-case names are \emph{not} used, bacause clear division
  of words is essential for readability.\footnote{Camel-case was
  invented to workaround the lack of underscore in some early
  non-ASCII character sets.  Later it became habitual in some language
  communities that are now strong in numbers.}

  A single (capital) character does not count as ``word'' in this
  respect: some Isabelle/ML names are suffixed by extra markers like
  this: @{ML_text foo_barT}.

  Name variants are produced by adding 1--3 primes, e.g.\ @{ML_text
  foo'}, @{ML_text foo''}, or @{ML_text foo'''}, but not @{ML_text
  foo''''} or more.  Decimal digits scale better to larger numbers,
  e.g.\ @{ML_text foo0}, @{ML_text foo1}, @{ML_text foo42}.

  \paragraph{Scopes.}  Apart from very basic library modules, ML
  structures are not ``opened'', but names are referenced with
  explicit qualification, as in @{ML Syntax.string_of_term} for
  example.  When devising names for structures and their components it
  is important aim at eye-catching compositions of both parts, because
  this is how they are seen in the sources and documentation.  For the
  same reasons, aliases of well-known library functions should be
  avoided.

  Local names of function abstraction or case/let bindings are
  typically shorter, sometimes using only rudiments of ``words'',
  while still avoiding cryptic shorthands.  An auxiliary function
  called @{ML_text helper}, @{ML_text aux}, or @{ML_text f} is
  considered bad style.

  Example:

  \begin{verbatim}
  (* RIGHT *)

  fun print_foo ctxt foo =
    let
      fun print t = ... Syntax.string_of_term ctxt t ...
    in ... end;


  (* RIGHT *)

  fun print_foo ctxt foo =
    let
      val string_of_term = Syntax.string_of_term ctxt;
      fun print t = ... string_of_term t ...
    in ... end;


  (* WRONG *)

  val string_of_term = Syntax.string_of_term;

  fun print_foo ctxt foo =
    let
      fun aux t = ... string_of_term ctxt t ...
    in ... end;

  \end{verbatim}


  \paragraph{Specific conventions.} Here are some specific name forms
  that occur frequently in the sources.

  \begin{itemize}

  \item A function that maps @{ML_text foo} to @{ML_text bar} is
  called @{ML_text foo_to_bar} or @{ML_text bar_of_foo} (never
  @{ML_text foo2bar}, @{ML_text bar_from_foo}, @{ML_text
  bar_for_foo}, or @{ML_text bar4foo}).

  \item The name component @{ML_text legacy} means that the operation
  is about to be discontinued soon.

  \item The name component @{ML_text old} means that this is historic
  material that might disappear at some later stage.

  \item The name component @{ML_text global} means that this works
  with the background theory instead of the regular local context
  (\secref{sec:context}), sometimes for historical reasons, sometimes
  due a genuine lack of locality of the concept involved, sometimes as
  a fall-back for the lack of a proper context in the application
  code.  Whenever there is a non-global variant available, the
  application should be migrated to use it with a proper local
  context.

  \item Variables of the main context types of the Isabelle/Isar
  framework (\secref{sec:context} and \chref{ch:local-theory}) have
  firm naming conventions as follows:

  \begin{itemize}

  \item theories are called @{ML_text thy}, rarely @{ML_text theory}
  (never @{ML_text thry})

  \item proof contexts are called @{ML_text ctxt}, rarely @{ML_text
  context} (never @{ML_text ctx})

  \item generic contexts are called @{ML_text context}, rarely
  @{ML_text ctxt}

  \item local theories are called @{ML_text lthy}, except for local
  theories that are treated as proof context (which is a semantic
  super-type)

  \end{itemize}

  Variations with primed or decimal numbers are always possible, as
  well as sematic prefixes like @{ML_text foo_thy} or @{ML_text
  bar_ctxt}, but the base conventions above need to be preserved.
  This allows to visualize the their data flow via plain regular
  expressions in the editor.

  \item The main logical entities (\secref{ch:logic}) have established
  naming convention as follows:

  \begin{itemize}

  \item sorts are called @{ML_text S}

  \item types are called @{ML_text T}, @{ML_text U}, or @{ML_text
  ty} (never @{ML_text t})

  \item terms are called @{ML_text t}, @{ML_text u}, or @{ML_text
  tm} (never @{ML_text trm})

  \item certified types are called @{ML_text cT}, rarely @{ML_text
  T}, with variants as for types

  \item certified terms are called @{ML_text ct}, rarely @{ML_text
  t}, with variants as for terms

  \item theorems are called @{ML_text th}, or @{ML_text thm}

  \end{itemize}

  Proper semantic names override these conventions completely.  For
  example, the left-hand side of an equation (as a term) can be called
  @{ML_text lhs} (not @{ML_text lhs_tm}).  Or a term that is known
  to be a variable can be called @{ML_text v} or @{ML_text x}.

  \item Tactics (\secref{sec:tactics}) are sufficiently important to
  have specific naming conventions.  The name of a basic tactic
  definition always has a @{ML_text "_tac"} suffix, the subgoal index
  (if applicable) is always called @{ML_text i}, and the goal state
  (if made explicit) is usually called @{ML_text st} instead of the
  somewhat misleading @{ML_text thm}.  Any other arguments are given
  before the latter two, and the general context is given first.
  Example:

  \begin{verbatim}
  fun my_tac ctxt arg1 arg2 i st = ...
  \end{verbatim}

  Note that the goal state @{ML_text st} above is rarely made
  explicit, if tactic combinators (tacticals) are used as usual.

  \end{itemize}
*}


subsection {* General source layout *}

text {* The general Isabelle/ML source layout imitates regular
  type-setting to some extent, augmented by the requirements for
  deeply nested expressions that are commonplace in functional
  programming.

  \paragraph{Line length} is 80 characters according to ancient
  standards, but we allow as much as 100 characters (not
  more).\footnote{Readability requires to keep the beginning of a line
  in view while watching its end.  Modern wide-screen displays do not
  change the way how the human brain works.  Sources also need to be
  printable on plain paper with reasonable font-size.} The extra 20
  characters acknowledge the space requirements due to qualified
  library references in Isabelle/ML.

  \paragraph{White-space} is used to emphasize the structure of
  expressions, following mostly standard conventions for mathematical
  typesetting, as can be seen in plain {\TeX} or {\LaTeX}.  This
  defines positioning of spaces for parentheses, punctuation, and
  infixes as illustrated here:

  \begin{verbatim}
  val x = y + z * (a + b);
  val pair = (a, b);
  val record = {foo = 1, bar = 2};
  \end{verbatim}

  Lines are normally broken \emph{after} an infix operator or
  punctuation character.  For example:

  \begin{verbatim}
  val x =
    a +
    b +
    c;

  val tuple =
   (a,
    b,
    c);
  \end{verbatim}

  Some special infixes (e.g.\ @{ML_text "|>"}) work better at the
  start of the line, but punctuation is always at the end.

  Function application follows the tradition of @{text "\<lambda>"}-calculus,
  not informal mathematics.  For example: @{ML_text "f a b"} for a
  curried function, or @{ML_text "g (a, b)"} for a tupled function.
  Note that the space between @{ML_text g} and the pair @{ML_text
  "(a, b)"} follows the important principle of
  \emph{compositionality}: the layout of @{ML_text "g p"} does not
  change when @{ML_text "p"} is refined to the concrete pair
  @{ML_text "(a, b)"}.

  \paragraph{Indentation} uses plain spaces, never hard
  tabulators.\footnote{Tabulators were invented to move the carriage
  of a type-writer to certain predefined positions.  In software they
  could be used as a primitive run-length compression of consecutive
  spaces, but the precise result would depend on non-standardized
  editor configuration.}

  Each level of nesting is indented by 2 spaces, sometimes 1, very
  rarely 4, never 8 or any other odd number.

  Indentation follows a simple logical format that only depends on the
  nesting depth, not the accidental length of the text that initiates
  a level of nesting.  Example:

  \begin{verbatim}
  (* RIGHT *)

  if b then
    expr1_part1
    expr1_part2
  else
    expr2_part1
    expr2_part2


  (* WRONG *)

  if b then expr1_part1
            expr1_part2
  else expr2_part1
       expr2_part2
  \end{verbatim}

  The second form has many problems: it assumes a fixed-width font
  when viewing the sources, it uses more space on the line and thus
  makes it hard to observe its strict length limit (working against
  \emph{readability}), it requires extra editing to adapt the layout
  to changes of the initial text (working against
  \emph{maintainability}) etc.

  \medskip For similar reasons, any kind of two-dimensional or tabular
  layouts, ASCII-art with lines or boxes of asterisks etc.\ should be
  avoided.

  \paragraph{Complex expressions} that consist of multi-clausal
  function definitions, @{ML_text handle}, @{ML_text case},
  @{ML_text let} (and combinations) require special attention.  The
  syntax of Standard ML is quite ambitious and admits a lot of
  variance that can distort the meaning of the text.

  Clauses of @{ML_text fun}, @{ML_text fn}, @{ML_text handle},
  @{ML_text case} get extra indentation to indicate the nesting
  clearly.  Example:

  \begin{verbatim}
  (* RIGHT *)

  fun foo p1 =
        expr1
    | foo p2 =
        expr2


  (* WRONG *)

  fun foo p1 =
    expr1
    | foo p2 =
    expr2
  \end{verbatim}

  Body expressions consisting of @{ML_text case} or @{ML_text let}
  require care to maintain compositionality, to prevent loss of
  logical indentation where it is especially important to see the
  structure of the text.  Example:

  \begin{verbatim}
  (* RIGHT *)

  fun foo p1 =
        (case e of
          q1 => ...
        | q2 => ...)
    | foo p2 =
        let
          ...
        in
          ...
        end


  (* WRONG *)

  fun foo p1 = case e of
      q1 => ...
    | q2 => ...
    | foo p2 =
    let
      ...
    in
      ...
    end
  \end{verbatim}

  Extra parentheses around @{ML_text case} expressions are optional,
  but help to analyse the nesting based on character matching in the
  editor.

  \medskip There are two main exceptions to the overall principle of
  compositionality in the layout of complex expressions.

  \begin{enumerate}

  \item @{ML_text "if"} expressions are iterated as if there would be
  a multi-branch conditional in SML, e.g.

  \begin{verbatim}
  (* RIGHT *)

  if b1 then e1
  else if b2 then e2
  else e3
  \end{verbatim}

  \item @{ML_text fn} abstractions are often layed-out as if they
  would lack any structure by themselves.  This traditional form is
  motivated by the possibility to shift function arguments back and
  forth wrt.\ additional combinators.  Example:

  \begin{verbatim}
  (* RIGHT *)

  fun foo x y = fold (fn z =>
    expr)
  \end{verbatim}

  Here the visual appearance is that of three arguments @{ML_text x},
  @{ML_text y}, @{ML_text z}.

  \end{enumerate}

  Such weakly structured layout should be use with great care.  Here
  are some counter-examples involving @{ML_text let} expressions:

  \begin{verbatim}
  (* WRONG *)

  fun foo x = let
      val y = ...
    in ... end


  (* WRONG *)

  fun foo x = let
    val y = ...
  in ... end


  (* WRONG *)

  fun foo x =
  let
    val y = ...
  in ... end
  \end{verbatim}

  \medskip In general the source layout is meant to emphasize the
  structure of complex language expressions, not to pretend that SML
  had a completely different syntax (say that of Haskell or Java).
*}


section {* SML embedded into Isabelle/Isar *}

text {* ML and Isar are intertwined via an open-ended bootstrap
  process that provides more and more programming facilities and
  logical content in an alternating manner.  Bootstrapping starts from
  the raw environment of existing implementations of Standard ML
  (mainly Poly/ML, but also SML/NJ).

  Isabelle/Pure marks the point where the original ML toplevel is
  superseded by the Isar toplevel that maintains a uniform context for
  arbitrary ML values (see also \secref{sec:context}).  This formal
  environment holds ML compiler bindings, logical entities, and many
  other things.  Raw SML is never encountered again after the initial
  bootstrap of Isabelle/Pure.

  Object-logics like Isabelle/HOL are built within the
  Isabelle/ML/Isar environment by introducing suitable theories with
  associated ML modules, either inlined or as separate files.  Thus
  Isabelle/HOL is defined as a regular user-space application within
  the Isabelle framework.  Further add-on tools can be implemented in
  ML within the Isar context in the same manner: ML is part of the
  standard repertoire of Isabelle, and there is no distinction between
  ``user'' and ``developer'' in this respect.
*}


subsection {* Isar ML commands *}

text {* The primary Isar source language provides facilities to ``open
  a window'' to the underlying ML compiler.  Especially see the Isar
  commands @{command_ref "use"} and @{command_ref "ML"}: both work the
  same way, only the source text is provided via a file vs.\ inlined,
  respectively.  Apart from embedding ML into the main theory
  definition like that, there are many more commands that refer to ML
  source, such as @{command_ref setup} or @{command_ref declaration}.
  Even more fine-grained embedding of ML into Isar is encountered in
  the proof method @{method_ref tactic}, which refines the pending
  goal state via a given expression of type @{ML_type tactic}.
*}

text %mlex {* The following artificial example demonstrates some ML
  toplevel declarations within the implicit Isar theory context.  This
  is regular functional programming without referring to logical
  entities yet.
*}

ML {*
  fun factorial 0 = 1
    | factorial n = n * factorial (n - 1)
*}

text {* Here the ML environment is already managed by Isabelle, i.e.\
  the @{ML factorial} function is not yet accessible in the preceding
  paragraph, nor in a different theory that is independent from the
  current one in the import hierarchy.

  Removing the above ML declaration from the source text will remove
  any trace of this definition as expected.  The Isabelle/ML toplevel
  environment is managed in a \emph{stateless} way: unlike the raw ML
  toplevel there are no global side-effects involved
  here.\footnote{Such a stateless compilation environment is also a
  prerequisite for robust parallel compilation within independent
  nodes of the implicit theory development graph.}

  \medskip The next example shows how to embed ML into Isar proofs, using
 @{command_ref "ML_prf"} instead of Instead of @{command_ref "ML"}.
  As illustrated below, the effect on the ML environment is local to
  the whole proof body, ignoring the block structure.
*}

notepad
begin
  ML_prf %"ML" {* val a = 1 *}
  {
    ML_prf %"ML" {* val b = a + 1 *}
  } -- {* Isar block structure ignored by ML environment *}
  ML_prf %"ML" {* val c = b + 1 *}
end

text {* By side-stepping the normal scoping rules for Isar proof
  blocks, embedded ML code can refer to the different contexts and
  manipulate corresponding entities, e.g.\ export a fact from a block
  context.

  \medskip Two further ML commands are useful in certain situations:
  @{command_ref ML_val} and @{command_ref ML_command} are
  \emph{diagnostic} in the sense that there is no effect on the
  underlying environment, and can thus used anywhere (even outside a
  theory).  The examples below produce long strings of digits by
  invoking @{ML factorial}: @{command ML_val} already takes care of
  printing the ML toplevel result, but @{command ML_command} is silent
  so we produce an explicit output message.  *}

ML_val {* factorial 100 *}
ML_command {* writeln (string_of_int (factorial 100)) *}

notepad
begin
  ML_val {* factorial 100 *}  (* FIXME check/fix indentation *)
  ML_command {* writeln (string_of_int (factorial 100)) *}
end


subsection {* Compile-time context *}

text {* Whenever the ML compiler is invoked within Isabelle/Isar, the
  formal context is passed as a thread-local reference variable.  Thus
  ML code may access the theory context during compilation, by reading
  or writing the (local) theory under construction.  Note that such
  direct access to the compile-time context is rare.  In practice it
  is typically done via some derived ML functions instead.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML ML_Context.the_generic_context: "unit -> Context.generic"} \\
  @{index_ML "Context.>>": "(Context.generic -> Context.generic) -> unit"} \\
  @{index_ML bind_thms: "string * thm list -> unit"} \\
  @{index_ML bind_thm: "string * thm -> unit"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML "ML_Context.the_generic_context ()"} refers to the theory
  context of the ML toplevel --- at compile time.  ML code needs to
  take care to refer to @{ML "ML_Context.the_generic_context ()"}
  correctly.  Recall that evaluation of a function body is delayed
  until actual run-time.

  \item @{ML "Context.>>"}~@{text f} applies context transformation
  @{text f} to the implicit context of the ML toplevel.

  \item @{ML bind_thms}~@{text "(name, thms)"} stores a list of
  theorems produced in ML both in the (global) theory context and the
  ML toplevel, associating it with the provided name.  Theorems are
  put into a global ``standard'' format before being stored.

  \item @{ML bind_thm} is similar to @{ML bind_thms} but refers to a
  singleton fact.

  \end{description}

  It is important to note that the above functions are really
  restricted to the compile time, even though the ML compiler is
  invoked at run-time.  The majority of ML code either uses static
  antiquotations (\secref{sec:ML-antiq}) or refers to the theory or
  proof context at run-time, by explicit functional abstraction.
*}


subsection {* Antiquotations \label{sec:ML-antiq} *}

text {* A very important consequence of embedding SML into Isar is the
  concept of \emph{ML antiquotation}.  The standard token language of
  ML is augmented by special syntactic entities of the following form:

  @{rail "
  @{syntax_def antiquote}: '@{' nameref args '}' | '\<lbrace>' | '\<rbrace>'
  "}

  Here @{syntax nameref} and @{syntax args} are regular outer syntax
  categories \cite{isabelle-isar-ref}.  Attributes and proof methods
  use similar syntax.

  \medskip A regular antiquotation @{text "@{name args}"} processes
  its arguments by the usual means of the Isar source language, and
  produces corresponding ML source text, either as literal
  \emph{inline} text (e.g. @{text "@{term t}"}) or abstract
  \emph{value} (e.g. @{text "@{thm th}"}).  This pre-compilation
  scheme allows to refer to formal entities in a robust manner, with
  proper static scoping and with some degree of logical checking of
  small portions of the code.

  Special antiquotations like @{text "@{let \<dots>}"} or @{text "@{note
  \<dots>}"} augment the compilation context without generating code.  The
  non-ASCII braces @{text "\<lbrace>"} and @{text "\<rbrace>"} allow to delimit the
  effect by introducing local blocks within the pre-compilation
  environment.

  \medskip See also \cite{Wenzel-Chaieb:2007b} for a broader
  perspective on Isabelle/ML antiquotations.  *}

text %mlantiq {*
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "let"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "note"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  @{rail "
  @@{ML_antiquotation let} ((term + @'and') '=' term + @'and')
  ;
  @@{ML_antiquotation note} (thmdef? thmrefs + @'and')
  "}

  \begin{description}

  \item @{text "@{let p = t}"} binds schematic variables in the
  pattern @{text "p"} by higher-order matching against the term @{text
  "t"}.  This is analogous to the regular @{command_ref let} command
  in the Isar proof language.  The pre-compilation environment is
  augmented by auxiliary term bindings, without emitting ML source.

  \item @{text "@{note a = b\<^sub>1 \<dots> b\<^sub>n}"} recalls existing facts @{text
  "b\<^sub>1, \<dots>, b\<^sub>n"}, binding the result as @{text a}.  This is analogous to
  the regular @{command_ref note} command in the Isar proof language.
  The pre-compilation environment is augmented by auxiliary fact
  bindings, without emitting ML source.

  \end{description}
*}

text %mlex {* The following artificial example gives some impression
  about the antiquotation elements introduced so far, together with
  the important @{text "@{thm}"} antiquotation defined later.
*}

ML {*
  \<lbrace>
    @{let ?t = my_term}
    @{note my_refl = reflexive [of ?t]}
    fun foo th = Thm.transitive th @{thm my_refl}
  \<rbrace>
*}

text {* The extra block delimiters do not affect the compiled code
  itself, i.e.\ function @{ML foo} is available in the present context
  of this paragraph.
*}


section {* Canonical argument order \label{sec:canonical-argument-order} *}

text {* Standard ML is a language in the tradition of @{text
  "\<lambda>"}-calculus and \emph{higher-order functional programming},
  similar to OCaml, Haskell, or Isabelle/Pure and HOL as logical
  languages.  Getting acquainted with the native style of representing
  functions in that setting can save a lot of extra boiler-plate of
  redundant shuffling of arguments, auxiliary abstractions etc.

  Functions are usually \emph{curried}: the idea of turning arguments
  of type @{text "\<tau>\<^sub>i"} (for @{text "i \<in> {1, \<dots> n}"}) into a result of
  type @{text "\<tau>"} is represented by the iterated function space
  @{text "\<tau>\<^sub>1 \<rightarrow> \<dots> \<rightarrow> \<tau>\<^sub>n \<rightarrow> \<tau>"}.  This is isomorphic to the well-known
  encoding via tuples @{text "\<tau>\<^sub>1 \<times> \<dots> \<times> \<tau>\<^sub>n \<rightarrow> \<tau>"}, but the curried
  version fits more smoothly into the basic calculus.\footnote{The
  difference is even more significant in higher-order logic, because
  the redundant tuple structure needs to be accommodated by formal
  reasoning.}

  Currying gives some flexiblity due to \emph{partial application}.  A
  function @{text "f: \<tau>\<^sub>1 \<rightarrow> \<tau>\<^bsub>2\<^esub> \<rightarrow> \<tau>"} can be applied to @{text "x: \<tau>\<^sub>1"}
  and the remaining @{text "(f x): \<tau>\<^sub>2 \<rightarrow> \<tau>"} passed to another function
  etc.  How well this works in practice depends on the order of
  arguments.  In the worst case, arguments are arranged erratically,
  and using a function in a certain situation always requires some
  glue code.  Thus we would get exponentially many oppurtunities to
  decorate the code with meaningless permutations of arguments.

  This can be avoided by \emph{canonical argument order}, which
  observes certain standard patterns and minimizes adhoc permutations
  in their application.  In Isabelle/ML, large portions of text can be
  written without ever using @{text "swap: \<alpha> \<times> \<beta> \<rightarrow> \<beta> \<times> \<alpha>"}, or the
  combinator @{text "C: (\<alpha> \<rightarrow> \<beta> \<rightarrow> \<gamma>) \<rightarrow> (\<beta> \<rightarrow> \<alpha> \<rightarrow> \<gamma>)"} that is not even
  defined in our library.

  \medskip The basic idea is that arguments that vary less are moved
  further to the left than those that vary more.  Two particularly
  important categories of functions are \emph{selectors} and
  \emph{updates}.

  The subsequent scheme is based on a hypothetical set-like container
  of type @{text "\<beta>"} that manages elements of type @{text "\<alpha>"}.  Both
  the names and types of the associated operations are canonical for
  Isabelle/ML.

  \medskip
  \begin{tabular}{ll}
  kind & canonical name and type \\\hline
  selector & @{text "member: \<beta> \<rightarrow> \<alpha> \<rightarrow> bool"} \\
  update & @{text "insert: \<alpha> \<rightarrow> \<beta> \<rightarrow> \<beta>"} \\
  \end{tabular}
  \medskip

  Given a container @{text "B: \<beta>"}, the partially applied @{text
  "member B"} is a predicate over elements @{text "\<alpha> \<rightarrow> bool"}, and
  thus represents the intended denotation directly.  It is customary
  to pass the abstract predicate to further operations, not the
  concrete container.  The argument order makes it easy to use other
  combinators: @{text "forall (member B) list"} will check a list of
  elements for membership in @{text "B"} etc. Often the explicit
  @{text "list"} is pointless and can be contracted to @{text "forall
  (member B)"} to get directly a predicate again.

  In contrast, an update operation varies the container, so it moves
  to the right: @{text "insert a"} is a function @{text "\<beta> \<rightarrow> \<beta>"} to
  insert a value @{text "a"}.  These can be composed naturally as
  @{text "insert c \<circ> insert b \<circ> insert a"}.  The slightly awkward
  inversion of the composition order is due to conventional
  mathematical notation, which can be easily amended as explained
  below.
*}


subsection {* Forward application and composition *}

text {* Regular function application and infix notation works best for
  relatively deeply structured expressions, e.g.\ @{text "h (f x y + g
  z)"}.  The important special case of \emph{linear transformation}
  applies a cascade of functions @{text "f\<^sub>n (\<dots> (f\<^sub>1 x))"}.  This
  becomes hard to read and maintain if the functions are themselves
  given as complex expressions.  The notation can be significantly
  improved by introducing \emph{forward} versions of application and
  composition as follows:

  \medskip
  \begin{tabular}{lll}
  @{text "x |> f"} & @{text "\<equiv>"} & @{text "f x"} \\
  @{text "(f #> g) x"} & @{text "\<equiv>"} & @{text "x |> f |> g"} \\
  \end{tabular}
  \medskip

  This enables to write conveniently @{text "x |> f\<^sub>1 |> \<dots> |> f\<^sub>n"} or
  @{text "f\<^sub>1 #> \<dots> #> f\<^sub>n"} for its functional abstraction over @{text
  "x"}.

  \medskip There is an additional set of combinators to accommodate
  multiple results (via pairs) that are passed on as multiple
  arguments (via currying).

  \medskip
  \begin{tabular}{lll}
  @{text "(x, y) |-> f"} & @{text "\<equiv>"} & @{text "f x y"} \\
  @{text "(f #-> g) x"} & @{text "\<equiv>"} & @{text "x |> f |-> g"} \\
  \end{tabular}
  \medskip
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_op "|> ": "'a * ('a -> 'b) -> 'b"} \\
  @{index_ML_op "|-> ": "('c * 'a) * ('c -> 'a -> 'b) -> 'b"} \\
  @{index_ML_op "#> ": "('a -> 'b) * ('b -> 'c) -> 'a -> 'c"} \\
  @{index_ML_op "#-> ": "('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd"} \\
  \end{mldecls}

  %FIXME description!?
*}


subsection {* Canonical iteration *}

text {* As explained above, a function @{text "f: \<alpha> \<rightarrow> \<beta> \<rightarrow> \<beta>"} can be
  understood as update on a configuration of type @{text "\<beta>"},
  parametrized by arguments of type @{text "\<alpha>"}.  Given @{text "a: \<alpha>"}
  the partial application @{text "(f a): \<beta> \<rightarrow> \<beta>"} operates
  homogeneously on @{text "\<beta>"}.  This can be iterated naturally over a
  list of parameters @{text "[a\<^sub>1, \<dots>, a\<^sub>n]"} as @{text "f a\<^sub>1 #> \<dots> #> f
  a\<^bsub>n\<^esub>\<^bsub>\<^esub>"}.  The latter expression is again a function @{text "\<beta> \<rightarrow> \<beta>"}.
  It can be applied to an initial configuration @{text "b: \<beta>"} to
  start the iteration over the given list of arguments: each @{text
  "a"} in @{text "a\<^sub>1, \<dots>, a\<^sub>n"} is applied consecutively by updating a
  cumulative configuration.

  The @{text fold} combinator in Isabelle/ML lifts a function @{text
  "f"} as above to its iterated version over a list of arguments.
  Lifting can be repeated, e.g.\ @{text "(fold \<circ> fold) f"} iterates
  over a list of lists as expected.

  The variant @{text "fold_rev"} works inside-out over the list of
  arguments, such that @{text "fold_rev f \<equiv> fold f \<circ> rev"} holds.

  The @{text "fold_map"} combinator essentially performs @{text
  "fold"} and @{text "map"} simultaneously: each application of @{text
  "f"} produces an updated configuration together with a side-result;
  the iteration collects all such side-results as a separate list.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML fold: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  @{index_ML fold_rev: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  @{index_ML fold_map: "('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML fold}~@{text f} lifts the parametrized update function
  @{text "f"} to a list of parameters.

  \item @{ML fold_rev}~@{text "f"} is similar to @{ML fold}~@{text
  "f"}, but works inside-out.

  \item @{ML fold_map}~@{text "f"} lifts the parametrized update
  function @{text "f"} (with side-result) to a list of parameters and
  cumulative side-results.

  \end{description}

  \begin{warn}
  The literature on functional programming provides a multitude of
  combinators called @{text "foldl"}, @{text "foldr"} etc.  SML97
  provides its own variations as @{ML List.foldl} and @{ML
  List.foldr}, while the classic Isabelle library also has the
  historic @{ML Library.foldl} and @{ML Library.foldr}.  To avoid
  further confusion, all of this should be ignored, and @{ML fold} (or
  @{ML fold_rev}) used exclusively.
  \end{warn}
*}

text %mlex {* The following example shows how to fill a text buffer
  incrementally by adding strings, either individually or from a given
  list.
*}

ML {*
  val s =
    Buffer.empty
    |> Buffer.add "digits: "
    |> fold (Buffer.add o string_of_int) (0 upto 9)
    |> Buffer.content;

  @{assert} (s = "digits: 0123456789");
*}

text {* Note how @{ML "fold (Buffer.add o string_of_int)"} above saves
  an extra @{ML "map"} over the given list.  This kind of peephole
  optimization reduces both the code size and the tree structures in
  memory (``deforestation''), but requires some practice to read and
  write it fluently.

  \medskip The next example elaborates the idea of canonical
  iteration, demonstrating fast accumulation of tree content using a
  text buffer.
*}

ML {*
  datatype tree = Text of string | Elem of string * tree list;

  fun slow_content (Text txt) = txt
    | slow_content (Elem (name, ts)) =
        "<" ^ name ^ ">" ^
        implode (map slow_content ts) ^
        "</" ^ name ^ ">"

  fun add_content (Text txt) = Buffer.add txt
    | add_content (Elem (name, ts)) =
        Buffer.add ("<" ^ name ^ ">") #>
        fold add_content ts #>
        Buffer.add ("</" ^ name ^ ">");

  fun fast_content tree =
    Buffer.empty |> add_content tree |> Buffer.content;
*}

text {* The slow part of @{ML slow_content} is the @{ML implode} of
  the recursive results, because it copies previously produced strings
  again.

  The incremental @{ML add_content} avoids this by operating on a
  buffer that is passed through in a linear fashion.  Using @{ML_text
  "#>"} and contraction over the actual buffer argument saves some
  additional boiler-plate.  Of course, the two @{ML "Buffer.add"}
  invocations with concatenated strings could have been split into
  smaller parts, but this would have obfuscated the source without
  making a big difference in allocations.  Here we have done some
  peephole-optimization for the sake of readability.

  Another benefit of @{ML add_content} is its ``open'' form as a
  function on buffers that can be continued in further linear
  transformations, folding etc.  Thus it is more compositional than
  the naive @{ML slow_content}.  As realistic example, compare the
  old-style @{ML "Term.maxidx_of_term: term -> int"} with the newer
  @{ML "Term.maxidx_term: term -> int -> int"} in Isabelle/Pure.

  Note that @{ML fast_content} above is only defined as example.  In
  many practical situations, it is customary to provide the
  incremental @{ML add_content} only and leave the initialization and
  termination to the concrete application by the user.
*}


section {* Message output channels \label{sec:message-channels} *}

text {* Isabelle provides output channels for different kinds of
  messages: regular output, high-volume tracing information, warnings,
  and errors.

  Depending on the user interface involved, these messages may appear
  in different text styles or colours.  The standard output for
  terminal sessions prefixes each line of warnings by @{verbatim
  "###"} and errors by @{verbatim "***"}, but leaves anything else
  unchanged.

  Messages are associated with the transaction context of the running
  Isar command.  This enables the front-end to manage commands and
  resulting messages together.  For example, after deleting a command
  from a given theory document version, the corresponding message
  output can be retracted from the display.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML writeln: "string -> unit"} \\
  @{index_ML tracing: "string -> unit"} \\
  @{index_ML warning: "string -> unit"} \\
  @{index_ML error: "string -> 'a"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML writeln}~@{text "text"} outputs @{text "text"} as regular
  message.  This is the primary message output operation of Isabelle
  and should be used by default.

  \item @{ML tracing}~@{text "text"} outputs @{text "text"} as special
  tracing message, indicating potential high-volume output to the
  front-end (hundreds or thousands of messages issued by a single
  command).  The idea is to allow the user-interface to downgrade the
  quality of message display to achieve higher throughput.

  Note that the user might have to take special actions to see tracing
  output, e.g.\ switch to a different output window.  So this channel
  should not be used for regular output.

  \item @{ML warning}~@{text "text"} outputs @{text "text"} as
  warning, which typically means some extra emphasis on the front-end
  side (color highlighting, icons, etc.).

  \item @{ML error}~@{text "text"} raises exception @{ML ERROR}~@{text
  "text"} and thus lets the Isar toplevel print @{text "text"} on the
  error channel, which typically means some extra emphasis on the
  front-end side (color highlighting, icons, etc.).

  This assumes that the exception is not handled before the command
  terminates.  Handling exception @{ML ERROR}~@{text "text"} is a
  perfectly legal alternative: it means that the error is absorbed
  without any message output.

  \begin{warn}
  The actual error channel is accessed via @{ML Output.error_msg}, but
  the interaction protocol of Proof~General \emph{crashes} if that
  function is used in regular ML code: error output and toplevel
  command failure always need to coincide.
  \end{warn}

  \end{description}

  \begin{warn}
  Regular Isabelle/ML code should output messages exclusively by the
  official channels.  Using raw I/O on \emph{stdout} or \emph{stderr}
  instead (e.g.\ via @{ML TextIO.output}) is apt to cause problems in
  the presence of parallel and asynchronous processing of Isabelle
  theories.  Such raw output might be displayed by the front-end in
  some system console log, with a low chance that the user will ever
  see it.  Moreover, as a genuine side-effect on global process
  channels, there is no proper way to retract output when Isar command
  transactions are reset by the system.
  \end{warn}

  \begin{warn}
  The message channels should be used in a message-oriented manner.
  This means that multi-line output that logically belongs together is
  issued by a \emph{single} invocation of @{ML writeln} etc.\ with the
  functional concatenation of all message constituents.
  \end{warn}
*}

text %mlex {* The following example demonstrates a multi-line
  warning.  Note that in some situations the user sees only the first
  line, so the most important point should be made first.
*}

ML_command {*
  warning (cat_lines
   ["Beware the Jabberwock, my son!",
    "The jaws that bite, the claws that catch!",
    "Beware the Jubjub Bird, and shun",
    "The frumious Bandersnatch!"]);
*}


section {* Exceptions \label{sec:exceptions} *}

text {* The Standard ML semantics of strict functional evaluation
  together with exceptions is rather well defined, but some delicate
  points need to be observed to avoid that ML programs go wrong
  despite static type-checking.  Exceptions in Isabelle/ML are
  subsequently categorized as follows.

  \paragraph{Regular user errors.}  These are meant to provide
  informative feedback about malformed input etc.

  The \emph{error} function raises the corresponding \emph{ERROR}
  exception, with a plain text message as argument.  \emph{ERROR}
  exceptions can be handled internally, in order to be ignored, turned
  into other exceptions, or cascaded by appending messages.  If the
  corresponding Isabelle/Isar command terminates with an \emph{ERROR}
  exception state, the toplevel will print the result on the error
  channel (see \secref{sec:message-channels}).

  It is considered bad style to refer to internal function names or
  values in ML source notation in user error messages.

  Grammatical correctness of error messages can be improved by
  \emph{omitting} final punctuation: messages are often concatenated
  or put into a larger context (e.g.\ augmented with source position).
  By not insisting in the final word at the origin of the error, the
  system can perform its administrative tasks more easily and
  robustly.

  \paragraph{Program failures.}  There is a handful of standard
  exceptions that indicate general failure situations, or failures of
  core operations on logical entities (types, terms, theorems,
  theories, see \chref{ch:logic}).

  These exceptions indicate a genuine breakdown of the program, so the
  main purpose is to determine quickly what has happened where.
  Traditionally, the (short) exception message would include the name
  of an ML function, although this is no longer necessary, because the
  ML runtime system prints a detailed source position of the
  corresponding @{ML_text raise} keyword.

  \medskip User modules can always introduce their own custom
  exceptions locally, e.g.\ to organize internal failures robustly
  without overlapping with existing exceptions.  Exceptions that are
  exposed in module signatures require extra care, though, and should
  \emph{not} be introduced by default.  Surprise by users of a module
  can be often minimized by using plain user errors instead.

  \paragraph{Interrupts.}  These indicate arbitrary system events:
  both the ML runtime system and the Isabelle/ML infrastructure signal
  various exceptional situations by raising the special
  \emph{Interrupt} exception in user code.

  This is the one and only way that physical events can intrude an
  Isabelle/ML program.  Such an interrupt can mean out-of-memory,
  stack overflow, timeout, internal signaling of threads, or the user
  producing a console interrupt manually etc.  An Isabelle/ML program
  that intercepts interrupts becomes dependent on physical effects of
  the environment.  Even worse, exception handling patterns that are
  too general by accident, e.g.\ by mispelled exception constructors,
  will cover interrupts unintentionally and thus render the program
  semantics ill-defined.

  Note that the Interrupt exception dates back to the original SML90
  language definition.  It was excluded from the SML97 version to
  avoid its malign impact on ML program semantics, but without
  providing a viable alternative.  Isabelle/ML recovers physical
  interruptibility (which is an indispensable tool to implement
  managed evaluation of command transactions), but requires user code
  to be strictly transparent wrt.\ interrupts.

  \begin{warn}
  Isabelle/ML user code needs to terminate promptly on interruption,
  without guessing at its meaning to the system infrastructure.
  Temporary handling of interrupts for cleanup of global resources
  etc.\ needs to be followed immediately by re-raising of the original
  exception.
  \end{warn}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML try: "('a -> 'b) -> 'a -> 'b option"} \\
  @{index_ML can: "('a -> 'b) -> 'a -> bool"} \\
  @{index_ML ERROR: "string -> exn"} \\
  @{index_ML Fail: "string -> exn"} \\
  @{index_ML Exn.is_interrupt: "exn -> bool"} \\
  @{index_ML reraise: "exn -> 'a"} \\
  @{index_ML exception_trace: "(unit -> 'a) -> 'a"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML try}~@{text "f x"} makes the partiality of evaluating
  @{text "f x"} explicit via the option datatype.  Interrupts are
  \emph{not} handled here, i.e.\ this form serves as safe replacement
  for the \emph{unsafe} version @{ML_text "(SOME"}~@{text "f
  x"}~@{ML_text "handle _ => NONE)"} that is occasionally seen in
  books about SML.

  \item @{ML can} is similar to @{ML try} with more abstract result.

  \item @{ML ERROR}~@{text "msg"} represents user errors; this
  exception is normally raised indirectly via the @{ML error} function
  (see \secref{sec:message-channels}).

  \item @{ML Fail}~@{text "msg"} represents general program failures.

  \item @{ML Exn.is_interrupt} identifies interrupts robustly, without
  mentioning concrete exception constructors in user code.  Handled
  interrupts need to be re-raised promptly!

  \item @{ML reraise}~@{text "exn"} raises exception @{text "exn"}
  while preserving its implicit position information (if possible,
  depending on the ML platform).

  \item @{ML exception_trace}~@{ML_text "(fn () =>"}~@{text
  "e"}@{ML_text ")"} evaluates expression @{text "e"} while printing
  a full trace of its stack of nested exceptions (if possible,
  depending on the ML platform).\footnote{In versions of Poly/ML the
  trace will appear on raw stdout of the Isabelle process.}

  Inserting @{ML exception_trace} into ML code temporarily is useful
  for debugging, but not suitable for production code.

  \end{description}
*}

text %mlantiq {*
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "assert"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  \begin{description}

  \item @{text "@{assert}"} inlines a function
  @{ML_type "bool -> unit"} that raises @{ML Fail} if the argument is
  @{ML false}.  Due to inlining the source position of failed
  assertions is included in the error output.

  \end{description}
*}


section {* Basic data types *}

text {* The basis library proposal of SML97 needs to be treated with
  caution.  Many of its operations simply do not fit with important
  Isabelle/ML conventions (like ``canonical argument order'', see
  \secref{sec:canonical-argument-order}), others cause problems with
  the parallel evaluation model of Isabelle/ML (such as @{ML
  TextIO.print} or @{ML OS.Process.system}).

  Subsequently we give a brief overview of important operations on
  basic ML data types.
*}


subsection {* Characters *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type char} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type char} is \emph{not} used.  The smallest textual
  unit in Isabelle is represented as a ``symbol'' (see
  \secref{sec:symbols}).

  \end{description}
*}


subsection {* Integers *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type int} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type int} represents regular mathematical integers,
  which are \emph{unbounded}.  Overflow never happens in
  practice.\footnote{The size limit for integer bit patterns in memory
  is 64\,MB for 32-bit Poly/ML, and much higher for 64-bit systems.}
  This works uniformly for all supported ML platforms (Poly/ML and
  SML/NJ).

  Literal integers in ML text are forced to be of this one true
  integer type --- overloading of SML97 is disabled.

  Structure @{ML_struct IntInf} of SML97 is obsolete and superseded by
  @{ML_struct Int}.  Structure @{ML_struct Integer} in @{file
  "~~/src/Pure/General/integer.ML"} provides some additional
  operations.

  \end{description}
*}


subsection {* Time *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Time.time} \\
  @{index_ML seconds: "real -> Time.time"} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type Time.time} represents time abstractly according
  to the SML97 basis library definition.  This is adequate for
  internal ML operations, but awkward in concrete time specifications.

  \item @{ML seconds}~@{text "s"} turns the concrete scalar @{text
  "s"} (measured in seconds) into an abstract time value.  Floating
  point numbers are easy to use as context parameters (e.g.\ via
  configuration options, see \secref{sec:config-options}) or
  preferences that are maintained by external tools as well.

  \end{description}
*}


subsection {* Options *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Option.map: "('a -> 'b) -> 'a option -> 'b option"} \\
  @{index_ML is_some: "'a option -> bool"} \\
  @{index_ML is_none: "'a option -> bool"} \\
  @{index_ML the: "'a option -> 'a"} \\
  @{index_ML these: "'a list option -> 'a list"} \\
  @{index_ML the_list: "'a option -> 'a list"} \\
  @{index_ML the_default: "'a -> 'a option -> 'a"} \\
  \end{mldecls}
*}

text {* Apart from @{ML Option.map} most operations defined in
  structure @{ML_struct Option} are alien to Isabelle/ML.  The
  operations shown above are defined in @{file
  "~~/src/Pure/General/basics.ML"}, among others.  *}


subsection {* Lists *}

text {* Lists are ubiquitous in ML as simple and light-weight
  ``collections'' for many everyday programming tasks.  Isabelle/ML
  provides important additions and improvements over operations that
  are predefined in the SML97 library. *}

text %mlref {*
  \begin{mldecls}
  @{index_ML cons: "'a -> 'a list -> 'a list"} \\
  @{index_ML member: "('b * 'a -> bool) -> 'a list -> 'b -> bool"} \\
  @{index_ML insert: "('a * 'a -> bool) -> 'a -> 'a list -> 'a list"} \\
  @{index_ML remove: "('b * 'a -> bool) -> 'b -> 'a list -> 'a list"} \\
  @{index_ML update: "('a * 'a -> bool) -> 'a -> 'a list -> 'a list"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML cons}~@{text "x xs"} evaluates to @{text "x :: xs"}.

  Tupled infix operators are a historical accident in Standard ML.
  The curried @{ML cons} amends this, but it should be only used when
  partial application is required.

  \item @{ML member}, @{ML insert}, @{ML remove}, @{ML update} treat
  lists as a set-like container that maintains the order of elements.
  See @{file "~~/src/Pure/library.ML"} for the full specifications
  (written in ML).  There are some further derived operations like
  @{ML union} or @{ML inter}.

  Note that @{ML insert} is conservative about elements that are
  already a @{ML member} of the list, while @{ML update} ensures that
  the latest entry is always put in front.  The latter discipline is
  often more appropriate in declarations of context data
  (\secref{sec:context-data}) that are issued by the user in Isar
  source: more recent declarations normally take precedence over
  earlier ones.

  \end{description}
*}

text %mlex {* Using canonical @{ML fold} together with @{ML cons}, or
  similar standard operations, alternates the orientation of data.
  The is quite natural and should not be altered forcible by inserting
  extra applications of @{ML rev}.  The alternative @{ML fold_rev} can
  be used in the few situations, where alternation should be
  prevented.
*}

ML {*
  val items = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

  val list1 = fold cons items [];
  @{assert} (list1 = rev items);

  val list2 = fold_rev cons items [];
  @{assert} (list2 = items);
*}

text {* The subsequent example demonstrates how to \emph{merge} two
  lists in a natural way. *}

ML {*
  fun merge_lists eq (xs, ys) = fold_rev (insert eq) ys xs;
*}

text {* Here the first list is treated conservatively: only the new
  elements from the second list are inserted.  The inside-out order of
  insertion via @{ML fold_rev} attempts to preserve the order of
  elements in the result.

  This way of merging lists is typical for context data
  (\secref{sec:context-data}).  See also @{ML merge} as defined in
  @{file "~~/src/Pure/library.ML"}.
*}


subsection {* Association lists *}

text {* The operations for association lists interpret a concrete list
  of pairs as a finite function from keys to values.  Redundant
  representations with multiple occurrences of the same key are
  implicitly normalized: lookup and update only take the first
  occurrence into account.
*}

text {*
  \begin{mldecls}
  @{index_ML AList.lookup: "('a * 'b -> bool) -> ('b * 'c) list -> 'a -> 'c option"} \\
  @{index_ML AList.defined: "('a * 'b -> bool) -> ('b * 'c) list -> 'a -> bool"} \\
  @{index_ML AList.update: "('a * 'a -> bool) -> 'a * 'b -> ('a * 'b) list -> ('a * 'b) list"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML AList.lookup}, @{ML AList.defined}, @{ML AList.update}
  implement the main ``framework operations'' for mappings in
  Isabelle/ML, following standard conventions for their names and
  types.

  Note that a function called @{text lookup} is obliged to express its
  partiality via an explicit option element.  There is no choice to
  raise an exception, without changing the name to something like
  @{text "the_element"} or @{text "get"}.

  The @{text "defined"} operation is essentially a contraction of @{ML
  is_some} and @{text "lookup"}, but this is sufficiently frequent to
  justify its independent existence.  This also gives the
  implementation some opportunity for peep-hole optimization.

  \end{description}

  Association lists are adequate as simple and light-weight
  implementation of finite mappings in many practical situations.  A
  more heavy-duty table structure is defined in @{file
  "~~/src/Pure/General/table.ML"}; that version scales easily to
  thousands or millions of elements.
*}


subsection {* Unsynchronized references *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type "'a Unsynchronized.ref"} \\
  @{index_ML Unsynchronized.ref: "'a -> 'a Unsynchronized.ref"} \\
  @{index_ML "!": "'a Unsynchronized.ref -> 'a"} \\
  @{index_ML_op ":=": "'a Unsynchronized.ref * 'a -> unit"} \\
  \end{mldecls}
*}

text {* Due to ubiquitous parallelism in Isabelle/ML (see also
  \secref{sec:multi-threading}), the mutable reference cells of
  Standard ML are notorious for causing problems.  In a highly
  parallel system, both correctness \emph{and} performance are easily
  degraded when using mutable data.

  The unwieldy name of @{ML Unsynchronized.ref} for the constructor
  for references in Isabelle/ML emphasizes the inconveniences caused by
  mutability.  Existing operations @{ML "!"}  and @{ML_op ":="} are
  unchanged, but should be used with special precautions, say in a
  strictly local situation that is guaranteed to be restricted to
  sequential evaluation --- now and in the future.

  \begin{warn}
  Never @{ML_text "open Unsynchronized"}, not even in a local scope!
  Pretending that mutable state is no problem is a very bad idea.
  \end{warn}
*}


section {* Thread-safe programming \label{sec:multi-threading} *}

text {* Multi-threaded execution has become an everyday reality in
  Isabelle since Poly/ML 5.2.1 and Isabelle2008.  Isabelle/ML provides
  implicit and explicit parallelism by default, and there is no way
  for user-space tools to ``opt out''.  ML programs that are purely
  functional, output messages only via the official channels
  (\secref{sec:message-channels}), and do not intercept interrupts
  (\secref{sec:exceptions}) can participate in the multi-threaded
  environment immediately without further ado.

  More ambitious tools with more fine-grained interaction with the
  environment need to observe the principles explained below.
*}


subsection {* Multi-threading with shared memory *}

text {* Multiple threads help to organize advanced operations of the
  system, such as real-time conditions on command transactions,
  sub-components with explicit communication, general asynchronous
  interaction etc.  Moreover, parallel evaluation is a prerequisite to
  make adequate use of the CPU resources that are available on
  multi-core systems.\footnote{Multi-core computing does not mean that
  there are ``spare cycles'' to be wasted.  It means that the
  continued exponential speedup of CPU performance due to ``Moore's
  Law'' follows different rules: clock frequency has reached its peak
  around 2005, and applications need to be parallelized in order to
  avoid a perceived loss of performance.  See also
  \cite{Sutter:2005}.}

  Isabelle/Isar exploits the inherent structure of theories and proofs
  to support \emph{implicit parallelism} to a large extent.  LCF-style
  theorem provides almost ideal conditions for that, see also
  \cite{Wenzel:2009}.  This means, significant parts of theory and
  proof checking is parallelized by default.  A maximum speedup-factor
  of 3.0 on 4 cores and 5.0 on 8 cores can be
  expected.\footnote{Further scalability is limited due to garbage
  collection, which is still sequential in Poly/ML 5.2/5.3/5.4.  It
  helps to provide initial heap space generously, using the
  \texttt{-H} option.  Initial heap size needs to be scaled-up
  together with the number of CPU cores: approximately 1--2\,GB per
  core..}

  \medskip ML threads lack the memory protection of separate
  processes, and operate concurrently on shared heap memory.  This has
  the advantage that results of independent computations are directly
  available to other threads: abstract values can be passed without
  copying or awkward serialization that is typically required for
  separate processes.

  To make shared-memory multi-threading work robustly and efficiently,
  some programming guidelines need to be observed.  While the ML
  system is responsible to maintain basic integrity of the
  representation of ML values in memory, the application programmer
  needs to ensure that multi-threaded execution does not break the
  intended semantics.

  \begin{warn}
  To participate in implicit parallelism, tools need to be
  thread-safe.  A single ill-behaved tool can affect the stability and
  performance of the whole system.
  \end{warn}

  Apart from observing the principles of thread-safeness passively,
  advanced tools may also exploit parallelism actively, e.g.\ by using
  ``future values'' (\secref{sec:futures}) or the more basic library
  functions for parallel list operations (\secref{sec:parlist}).

  \begin{warn}
  Parallel computing resources are managed centrally by the
  Isabelle/ML infrastructure.  User programs must not fork their own
  ML threads to perform computations.
  \end{warn}
*}


subsection {* Critical shared resources *}

text {* Thread-safeness is mainly concerned about concurrent
  read/write access to shared resources, which are outside the purely
  functional world of ML.  This covers the following in particular.

  \begin{itemize}

  \item Global references (or arrays), i.e.\ mutable memory cells that
  persist over several invocations of associated
  operations.\footnote{This is independent of the visibility of such
  mutable values in the toplevel scope.}

  \item Global state of the running Isabelle/ML process, i.e.\ raw I/O
  channels, environment variables, current working directory.

  \item Writable resources in the file-system that are shared among
  different threads or external processes.

  \end{itemize}

  Isabelle/ML provides various mechanisms to avoid critical shared
  resources in most situations.  As last resort there are some
  mechanisms for explicit synchronization.  The following guidelines
  help to make Isabelle/ML programs work smoothly in a concurrent
  environment.

  \begin{itemize}

  \item Avoid global references altogether.  Isabelle/Isar maintains a
  uniform context that incorporates arbitrary data declared by user
  programs (\secref{sec:context-data}).  This context is passed as
  plain value and user tools can get/map their own data in a purely
  functional manner.  Configuration options within the context
  (\secref{sec:config-options}) provide simple drop-in replacements
  for historic reference variables.

  \item Keep components with local state information re-entrant.
  Instead of poking initial values into (private) global references, a
  new state record can be created on each invocation, and passed
  through any auxiliary functions of the component.  The state record
  may well contain mutable references, without requiring any special
  synchronizations, as long as each invocation gets its own copy.

  \item Avoid raw output on @{text "stdout"} or @{text "stderr"}.  The
  Poly/ML library is thread-safe for each individual output operation,
  but the ordering of parallel invocations is arbitrary.  This means
  raw output will appear on some system console with unpredictable
  interleaving of atomic chunks.

  Note that this does not affect regular message output channels
  (\secref{sec:message-channels}).  An official message is associated
  with the command transaction from where it originates, independently
  of other transactions.  This means each running Isar command has
  effectively its own set of message channels, and interleaving can
  only happen when commands use parallelism internally (and only at
  message boundaries).

  \item Treat environment variables and the current working directory
  of the running process as strictly read-only.

  \item Restrict writing to the file-system to unique temporary files.
  Isabelle already provides a temporary directory that is unique for
  the running process, and there is a centralized source of unique
  serial numbers in Isabelle/ML.  Thus temporary files that are passed
  to to some external process will be always disjoint, and thus
  thread-safe.

  \end{itemize}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML File.tmp_path: "Path.T -> Path.T"} \\
  @{index_ML serial_string: "unit -> string"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML File.tmp_path}~@{text "path"} relocates the base
  component of @{text "path"} into the unique temporary directory of
  the running Isabelle/ML process.

  \item @{ML serial_string}~@{text "()"} creates a new serial number
  that is unique over the runtime of the Isabelle/ML process.

  \end{description}
*}

text %mlex {* The following example shows how to create unique
  temporary file names.
*}

ML {*
  val tmp1 = File.tmp_path (Path.basic ("foo" ^ serial_string ()));
  val tmp2 = File.tmp_path (Path.basic ("foo" ^ serial_string ()));
  @{assert} (tmp1 <> tmp2);
*}


subsection {* Explicit synchronization *}

text {* Isabelle/ML also provides some explicit synchronization
  mechanisms, for the rare situations where mutable shared resources
  are really required.  These are based on the synchronizations
  primitives of Poly/ML, which have been adapted to the specific
  assumptions of the concurrent Isabelle/ML environment.  User code
  must not use the Poly/ML primitives directly!

  \medskip The most basic synchronization concept is a single
  \emph{critical section} (also called ``monitor'' in the literature).
  A thread that enters the critical section prevents all other threads
  from doing the same.  A thread that is already within the critical
  section may re-enter it in an idempotent manner.

  Such centralized locking is convenient, because it prevents
  deadlocks by construction.

  \medskip More fine-grained locking works via \emph{synchronized
  variables}.  An explicit state component is associated with
  mechanisms for locking and signaling.  There are operations to
  await a condition, change the state, and signal the change to all
  other waiting threads.

  Here the synchronized access to the state variable is \emph{not}
  re-entrant: direct or indirect nesting within the same thread will
  cause a deadlock!
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML NAMED_CRITICAL: "string -> (unit -> 'a) -> 'a"} \\
  @{index_ML CRITICAL: "(unit -> 'a) -> 'a"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type "'a Synchronized.var"} \\
  @{index_ML Synchronized.var: "string -> 'a -> 'a Synchronized.var"} \\
  @{index_ML Synchronized.guarded_access: "'a Synchronized.var ->
  ('a -> ('b * 'a) option) -> 'b"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML NAMED_CRITICAL}~@{text "name e"} evaluates @{text "e ()"}
  within the central critical section of Isabelle/ML.  No other thread
  may do so at the same time, but non-critical parallel execution will
  continue.  The @{text "name"} argument is used for tracing and might
  help to spot sources of congestion.

  Entering the critical section without contention is very fast, and
  several basic system operations do so frequently.  Each thread
  should stay within the critical section quickly only very briefly,
  otherwise parallel performance may degrade.

  \item @{ML CRITICAL} is the same as @{ML NAMED_CRITICAL} with empty
  name argument.

  \item Type @{ML_type "'a Synchronized.var"} represents synchronized
  variables with state of type @{ML_type 'a}.

  \item @{ML Synchronized.var}~@{text "name x"} creates a synchronized
  variable that is initialized with value @{text "x"}.  The @{text
  "name"} is used for tracing.

  \item @{ML Synchronized.guarded_access}~@{text "var f"} lets the
  function @{text "f"} operate within a critical section on the state
  @{text "x"} as follows: if @{text "f x"} produces @{ML NONE}, it
  continues to wait on the internal condition variable, expecting that
  some other thread will eventually change the content in a suitable
  manner; if @{text "f x"} produces @{ML SOME}~@{text "(y, x')"} it is
  satisfied and assigns the new state value @{text "x'"}, broadcasts a
  signal to all waiting threads on the associated condition variable,
  and returns the result @{text "y"}.

  \end{description}

  There are some further variants of the @{ML
  Synchronized.guarded_access} combinator, see @{file
  "~~/src/Pure/Concurrent/synchronized.ML"} for details.
*}

text %mlex {* The following example implements a counter that produces
  positive integers that are unique over the runtime of the Isabelle
  process:
*}

ML {*
  local
    val counter = Synchronized.var "counter" 0;
  in
    fun next () =
      Synchronized.guarded_access counter
        (fn i =>
          let val j = i + 1
          in SOME (j, j) end);
  end;
*}

ML {*
  val a = next ();
  val b = next ();
  @{assert} (a <> b);
*}

text {* \medskip See @{file "~~/src/Pure/Concurrent/mailbox.ML"} how
  to implement a mailbox as synchronized variable over a purely
  functional queue. *}

end