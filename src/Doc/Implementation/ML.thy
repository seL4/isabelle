(*:maxLineLen=78:*)

theory "ML"
imports Base
begin

chapter \<open>Isabelle/ML\<close>

text \<open>
  Isabelle/ML is best understood as a certain culture based on Standard ML.
  Thus it is not a new programming language, but a certain way to use SML at
  an advanced level within the Isabelle environment. This covers a variety of
  aspects that are geared towards an efficient and robust platform for
  applications of formal logic with fully foundational proof construction ---
  according to the well-known \<^emph>\<open>LCF principle\<close>. There is specific
  infrastructure with library modules to address the needs of this difficult
  task. For example, the raw parallel programming model of Poly/ML is
  presented as considerably more abstract concept of \<^emph>\<open>futures\<close>, which is then
  used to augment the inference kernel, Isar theory and proof interpreter, and
  PIDE document management.

  The main aspects of Isabelle/ML are introduced below. These first-hand
  explanations should help to understand how proper Isabelle/ML is to be read
  and written, and to get access to the wealth of experience that is expressed
  in the source text and its history of changes.\<^footnote>\<open>See
  \<^url>\<open>https://isabelle.in.tum.de/repos/isabelle\<close> for the full Mercurial history.
  There are symbolic tags to refer to official Isabelle releases, as opposed
  to arbitrary \<^emph>\<open>tip\<close> versions that merely reflect snapshots that are never
  really up-to-date.\<close>
\<close>


section \<open>Style and orthography\<close>

text \<open>
  The sources of Isabelle/Isar are optimized for \<^emph>\<open>readability\<close> and
  \<^emph>\<open>maintainability\<close>. The main purpose is to tell an informed reader what is
  really going on and how things really work. This is a non-trivial aim, but
  it is supported by a certain style of writing Isabelle/ML that has emerged
  from long years of system development.\<^footnote>\<open>See also the interesting style guide
  for OCaml \<^url>\<open>https://caml.inria.fr/resources/doc/guides/guidelines.en.html\<close>
  which shares many of our means and ends.\<close>

  The main principle behind any coding style is \<^emph>\<open>consistency\<close>. For a single
  author of a small program this merely means ``choose your style and stick to
  it''. A complex project like Isabelle, with long years of development and
  different contributors, requires more standardization. A coding style that
  is changed every few years or with every new contributor is no style at all,
  because consistency is quickly lost. Global consistency is hard to achieve,
  though. Nonetheless, one should always strive at least for local consistency
  of modules and sub-systems, without deviating from some general principles
  how to write Isabelle/ML.

  In a sense, good coding style is like an \<^emph>\<open>orthography\<close> for the sources: it
  helps to read quickly over the text and see through the main points, without
  getting distracted by accidental presentation of free-style code.
\<close>


subsection \<open>Header and sectioning\<close>

text \<open>
  Isabelle source files have a certain standardized header format (with
  precise spacing) that follows ancient traditions reaching back to the
  earliest versions of the system by Larry Paulson. See
  \<^file>\<open>~~/src/Pure/thm.ML\<close>, for example.

  The header includes at least \<^verbatim>\<open>Title\<close> and \<^verbatim>\<open>Author\<close> entries, followed by a
  prose description of the purpose of the module. The latter can range from a
  single line to several paragraphs of explanations.

  The rest of the file is divided into chapters, sections, subsections,
  subsubsections, paragraphs etc.\ using a simple layout via ML comments as
  follows.

  @{verbatim [display]
\<open>  (**** chapter ****)
 
  (*** section ***)

  (** subsection **)

  (* subsubsection *)

  (*short paragraph*)

  (*
    long paragraph,
    with more text
  *)\<close>}

  As in regular typography, there is some extra space \<^emph>\<open>before\<close> section
  headings that are adjacent to plain text, but not other headings as in the
  example above.

  \<^medskip>
  The precise wording of the prose text given in these headings is chosen
  carefully to introduce the main theme of the subsequent formal ML text.
\<close>


subsection \<open>Naming conventions\<close>

text \<open>
  Since ML is the primary medium to express the meaning of the source text,
  naming of ML entities requires special care.
\<close>

paragraph \<open>Notation.\<close>
text \<open>
  A name consists of 1--3 \<^emph>\<open>words\<close> (rarely 4, but not more) that are separated
  by underscore. There are three variants concerning upper or lower case
  letters, which are used for certain ML categories as follows:

  \<^medskip>
  \begin{tabular}{lll}
  variant & example & ML categories \\\hline
  lower-case & \<^ML_text>\<open>foo_bar\<close> & values, types, record fields \\
  capitalized & \<^ML_text>\<open>Foo_Bar\<close> & datatype constructors, structures, functors \\
  upper-case & \<^ML_text>\<open>FOO_BAR\<close> & special values, exception constructors, signatures \\
  \end{tabular}
  \<^medskip>

  For historical reasons, many capitalized names omit underscores, e.g.\
  old-style \<^ML_text>\<open>FooBar\<close> instead of \<^ML_text>\<open>Foo_Bar\<close>. Genuine
  mixed-case names are \<^emph>\<open>not\<close> used, because clear division of words is
  essential for readability.\<^footnote>\<open>Camel-case was invented to workaround the lack
  of underscore in some early non-ASCII character sets. Later it became
  habitual in some language communities that are now strong in numbers.\<close>

  A single (capital) character does not count as ``word'' in this respect:
  some Isabelle/ML names are suffixed by extra markers like this: \<^ML_text>\<open>foo_barT\<close>.

  Name variants are produced by adding 1--3 primes, e.g.\ \<^ML_text>\<open>foo'\<close>,
  \<^ML_text>\<open>foo''\<close>, or \<^ML_text>\<open>foo'''\<close>, but not \<^ML_text>\<open>foo''''\<close> or more.
  Decimal digits scale better to larger numbers, e.g.\ \<^ML_text>\<open>foo0\<close>,
  \<^ML_text>\<open>foo1\<close>, \<^ML_text>\<open>foo42\<close>.
\<close>

paragraph \<open>Scopes.\<close>
text \<open>
  Apart from very basic library modules, ML structures are not ``opened'', but
  names are referenced with explicit qualification, as in \<^ML>\<open>Syntax.string_of_term\<close> for example. When devising names for structures and
  their components it is important to aim at eye-catching compositions of both
  parts, because this is how they are seen in the sources and documentation.
  For the same reasons, aliases of well-known library functions should be
  avoided.

  Local names of function abstraction or case/let bindings are typically
  shorter, sometimes using only rudiments of ``words'', while still avoiding
  cryptic shorthands. An auxiliary function called \<^ML_text>\<open>helper\<close>,
  \<^ML_text>\<open>aux\<close>, or \<^ML_text>\<open>f\<close> is considered bad style.

  Example:

  @{verbatim [display]
\<open>  (* RIGHT *)

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
    in ... end;\<close>}
\<close>

paragraph \<open>Specific conventions.\<close>
text \<open>
  Here are some specific name forms that occur frequently in the sources.

  \<^item> A function that maps \<^ML_text>\<open>foo\<close> to \<^ML_text>\<open>bar\<close> is called \<^ML_text>\<open>foo_to_bar\<close> or \<^ML_text>\<open>bar_of_foo\<close> (never \<^ML_text>\<open>foo2bar\<close>, nor
  \<^ML_text>\<open>bar_from_foo\<close>, nor \<^ML_text>\<open>bar_for_foo\<close>, nor \<^ML_text>\<open>bar4foo\<close>).

  \<^item> The name component \<^ML_text>\<open>legacy\<close> means that the operation is about to
  be discontinued soon.

  \<^item> The name component \<^ML_text>\<open>global\<close> means that this works with the
  background theory instead of the regular local context
  (\secref{sec:context}), sometimes for historical reasons, sometimes due a
  genuine lack of locality of the concept involved, sometimes as a fall-back
  for the lack of a proper context in the application code. Whenever there is
  a non-global variant available, the application should be migrated to use it
  with a proper local context.

  \<^item> Variables of the main context types of the Isabelle/Isar framework
  (\secref{sec:context} and \chref{ch:local-theory}) have firm naming
  conventions as follows:

    \<^item> theories are called \<^ML_text>\<open>thy\<close>, rarely \<^ML_text>\<open>theory\<close>
    (never \<^ML_text>\<open>thry\<close>)

    \<^item> proof contexts are called \<^ML_text>\<open>ctxt\<close>, rarely \<^ML_text>\<open>context\<close> (never \<^ML_text>\<open>ctx\<close>)

    \<^item> generic contexts are called \<^ML_text>\<open>context\<close>

    \<^item> local theories are called \<^ML_text>\<open>lthy\<close>, except for local
    theories that are treated as proof context (which is a semantic
    super-type)

  Variations with primed or decimal numbers are always possible, as well as
  semantic prefixes like \<^ML_text>\<open>foo_thy\<close> or \<^ML_text>\<open>bar_ctxt\<close>, but the
  base conventions above need to be preserved. This allows to emphasize their
  data flow via plain regular expressions in the text editor.

  \<^item> The main logical entities (\secref{ch:logic}) have established naming
  convention as follows:

    \<^item> sorts are called \<^ML_text>\<open>S\<close>

    \<^item> types are called \<^ML_text>\<open>T\<close>, \<^ML_text>\<open>U\<close>, or \<^ML_text>\<open>ty\<close> (never
    \<^ML_text>\<open>t\<close>)

    \<^item> terms are called \<^ML_text>\<open>t\<close>, \<^ML_text>\<open>u\<close>, or \<^ML_text>\<open>tm\<close> (never
    \<^ML_text>\<open>trm\<close>)

    \<^item> certified types are called \<^ML_text>\<open>cT\<close>, rarely \<^ML_text>\<open>T\<close>, with
    variants as for types

    \<^item> certified terms are called \<^ML_text>\<open>ct\<close>, rarely \<^ML_text>\<open>t\<close>, with
    variants as for terms (never \<^ML_text>\<open>ctrm\<close>)

    \<^item> theorems are called \<^ML_text>\<open>th\<close>, or \<^ML_text>\<open>thm\<close>

  Proper semantic names override these conventions completely. For example,
  the left-hand side of an equation (as a term) can be called \<^ML_text>\<open>lhs\<close>
  (not \<^ML_text>\<open>lhs_tm\<close>). Or a term that is known to be a variable can be
  called \<^ML_text>\<open>v\<close> or \<^ML_text>\<open>x\<close>.

  \<^item> Tactics (\secref{sec:tactics}) are sufficiently important to have specific
  naming conventions. The name of a basic tactic definition always has a
  \<^ML_text>\<open>_tac\<close> suffix, the subgoal index (if applicable) is always called
  \<^ML_text>\<open>i\<close>, and the goal state (if made explicit) is usually called
  \<^ML_text>\<open>st\<close> instead of the somewhat misleading \<^ML_text>\<open>thm\<close>. Any other
  arguments are given before the latter two, and the general context is given
  first. Example:

  @{verbatim [display] \<open>  fun my_tac ctxt arg1 arg2 i st = ...\<close>}

  Note that the goal state \<^ML_text>\<open>st\<close> above is rarely made explicit, if
  tactic combinators (tacticals) are used as usual.

  A tactic that requires a proof context needs to make that explicit as seen
  in the \<^verbatim>\<open>ctxt\<close> argument above. Do not refer to the background theory of
  \<^verbatim>\<open>st\<close> -- it is not a proper context, but merely a formal certificate.
\<close>


subsection \<open>General source layout\<close>

text \<open>
  The general Isabelle/ML source layout imitates regular type-setting
  conventions, augmented by the requirements for deeply nested expressions
  that are commonplace in functional programming.
\<close>

paragraph \<open>Line length\<close>
text \<open>
  is limited to 80 characters according to ancient standards, but we allow as
  much as 100 characters (not more).\<^footnote>\<open>Readability requires to keep the
  beginning of a line in view while watching its end. Modern wide-screen
  displays do not change the way how the human brain works. Sources also need
  to be printable on plain paper with reasonable font-size.\<close> The extra 20
  characters acknowledge the space requirements due to qualified library
  references in Isabelle/ML.
\<close>

paragraph \<open>White-space\<close>
text \<open>
  is used to emphasize the structure of expressions, following mostly standard
  conventions for mathematical typesetting, as can be seen in plain {\TeX} or
  {\LaTeX}. This defines positioning of spaces for parentheses, punctuation,
  and infixes as illustrated here:

  @{verbatim [display]
\<open>  val x = y + z * (a + b);
  val pair = (a, b);
  val record = {foo = 1, bar = 2};\<close>}

  Lines are normally broken \<^emph>\<open>after\<close> an infix operator or punctuation
  character. For example:

  @{verbatim [display]
\<open>
  val x =
    a +
    b +
    c;

  val tuple =
   (a,
    b,
    c);
\<close>}

  Some special infixes (e.g.\ \<^ML_text>\<open>|>\<close>) work better at the start of the
  line, but punctuation is always at the end.

  Function application follows the tradition of \<open>\<lambda>\<close>-calculus, not informal
  mathematics. For example: \<^ML_text>\<open>f a b\<close> for a curried function, or
  \<^ML_text>\<open>g (a, b)\<close> for a tupled function. Note that the space between
  \<^ML_text>\<open>g\<close> and the pair \<^ML_text>\<open>(a, b)\<close> follows the important
  principle of \<^emph>\<open>compositionality\<close>: the layout of \<^ML_text>\<open>g p\<close> does not
  change when \<^ML_text>\<open>p\<close> is refined to the concrete pair \<^ML_text>\<open>(a,
  b)\<close>.
\<close>

paragraph \<open>Indentation\<close>
text \<open>
  uses plain spaces, never hard tabulators.\<^footnote>\<open>Tabulators were invented to move
  the carriage of a type-writer to certain predefined positions. In software
  they could be used as a primitive run-length compression of consecutive
  spaces, but the precise result would depend on non-standardized text editor
  configuration.\<close>

  Each level of nesting is indented by 2 spaces, sometimes 1, very rarely 4,
  never 8 or any other odd number.

  Indentation follows a simple logical format that only depends on the nesting
  depth, not the accidental length of the text that initiates a level of
  nesting. Example:

  @{verbatim [display]
\<open>  (* RIGHT *)

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
       expr2_part2\<close>}

  The second form has many problems: it assumes a fixed-width font when
  viewing the sources, it uses more space on the line and thus makes it hard
  to observe its strict length limit (working against \<^emph>\<open>readability\<close>), it
  requires extra editing to adapt the layout to changes of the initial text
  (working against \<^emph>\<open>maintainability\<close>) etc.

  \<^medskip>
  For similar reasons, any kind of two-dimensional or tabular layouts,
  ASCII-art with lines or boxes of asterisks etc.\ should be avoided.
\<close>

paragraph \<open>Complex expressions\<close>
text \<open>
  that consist of multi-clausal function definitions, \<^ML_text>\<open>handle\<close>,
  \<^ML_text>\<open>case\<close>, \<^ML_text>\<open>let\<close> (and combinations) require special
  attention. The syntax of Standard ML is quite ambitious and admits a lot of
  variance that can distort the meaning of the text.

  Multiple clauses of \<^ML_text>\<open>fun\<close>, \<^ML_text>\<open>fn\<close>, \<^ML_text>\<open>handle\<close>,
  \<^ML_text>\<open>case\<close> get extra indentation to indicate the nesting clearly.
  Example:

  @{verbatim [display]
\<open>  (* RIGHT *)

  fun foo p1 =
        expr1
    | foo p2 =
        expr2


  (* WRONG *)

  fun foo p1 =
    expr1
    | foo p2 =
    expr2\<close>}

  Body expressions consisting of \<^ML_text>\<open>case\<close> or \<^ML_text>\<open>let\<close> require
  care to maintain compositionality, to prevent loss of logical indentation
  where it is especially important to see the structure of the text. Example:

  @{verbatim [display]
\<open>  (* RIGHT *)

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
    end\<close>}

  Extra parentheses around \<^ML_text>\<open>case\<close> expressions are optional, but help
  to analyse the nesting based on character matching in the text editor.

  \<^medskip>
  There are two main exceptions to the overall principle of compositionality
  in the layout of complex expressions.

  \<^enum> \<^ML_text>\<open>if\<close> expressions are iterated as if ML had multi-branch
  conditionals, e.g.

  @{verbatim [display]
\<open>  (* RIGHT *)

  if b1 then e1
  else if b2 then e2
  else e3\<close>}

  \<^enum> \<^ML_text>\<open>fn\<close> abstractions are often layed-out as if they would lack any
  structure by themselves. This traditional form is motivated by the
  possibility to shift function arguments back and forth wrt.\ additional
  combinators. Example:

  @{verbatim [display]
\<open>  (* RIGHT *)

  fun foo x y = fold (fn z =>
    expr)\<close>}

  Here the visual appearance is that of three arguments \<^ML_text>\<open>x\<close>,
  \<^ML_text>\<open>y\<close>, \<^ML_text>\<open>z\<close> in a row.


  Such weakly structured layout should be use with great care. Here are some
  counter-examples involving \<^ML_text>\<open>let\<close> expressions:

  @{verbatim [display]
\<open>  (* WRONG *)

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


  (* WRONG *)

  fun foo x =
    let
      val y = ...
    in
      ... end\<close>}

  \<^medskip>
  In general the source layout is meant to emphasize the structure of complex
  language expressions, not to pretend that SML had a completely different
  syntax (say that of Haskell, Scala, Java).
\<close>


section \<open>ML embedded into Isabelle/Isar\<close>

text \<open>
  ML and Isar are intertwined via an open-ended bootstrap process that
  provides more and more programming facilities and logical content in an
  alternating manner. Bootstrapping starts from the raw environment of
  existing implementations of Standard ML (mainly Poly/ML).

  Isabelle/Pure marks the point where the raw ML toplevel is superseded by
  Isabelle/ML within the Isar theory and proof language, with a uniform
  context for arbitrary ML values (see also \secref{sec:context}). This formal
  environment holds ML compiler bindings, logical entities, and many other
  things.

  Object-logics like Isabelle/HOL are built within the Isabelle/ML/Isar
  environment by introducing suitable theories with associated ML modules,
  either inlined within \<^verbatim>\<open>.thy\<close> files, or as separate \<^verbatim>\<open>.ML\<close> files that are
  loading from some theory. Thus Isabelle/HOL is defined as a regular
  user-space application within the Isabelle framework. Further add-on tools
  can be implemented in ML within the Isar context in the same manner: ML is
  part of the standard repertoire of Isabelle, and there is no distinction
  between ``users'' and ``developers'' in this respect.
\<close>


subsection \<open>Isar ML commands\<close>

text \<open>
  The primary Isar source language provides facilities to ``open a window'' to
  the underlying ML compiler. Especially see the Isar commands @{command_ref
  "ML_file"} and @{command_ref "ML"}: both work the same way, but the source
  text is provided differently, via a file vs.\ inlined, respectively. Apart
  from embedding ML into the main theory definition like that, there are many
  more commands that refer to ML source, such as @{command_ref setup} or
  @{command_ref declaration}. Even more fine-grained embedding of ML into Isar
  is encountered in the proof method @{method_ref tactic}, which refines the
  pending goal state via a given expression of type \<^ML_type>\<open>tactic\<close>.
\<close>

text %mlex \<open>
  The following artificial example demonstrates some ML toplevel declarations
  within the implicit Isar theory context. This is regular functional
  programming without referring to logical entities yet.
\<close>

ML \<open>
  fun factorial 0 = 1
    | factorial n = n * factorial (n - 1)
\<close>

text \<open>
  Here the ML environment is already managed by Isabelle, i.e.\ the \<^ML>\<open>factorial\<close> function is not yet accessible in the preceding paragraph, nor in
  a different theory that is independent from the current one in the import
  hierarchy.

  Removing the above ML declaration from the source text will remove any trace
  of this definition, as expected. The Isabelle/ML toplevel environment is
  managed in a \<^emph>\<open>stateless\<close> way: in contrast to the raw ML toplevel, there are
  no global side-effects involved here.\<^footnote>\<open>Such a stateless compilation
  environment is also a prerequisite for robust parallel compilation within
  independent nodes of the implicit theory development graph.\<close>

  \<^medskip>
  The next example shows how to embed ML into Isar proofs, using @{command_ref
  "ML_prf"} instead of @{command_ref "ML"}. As illustrated below, the effect
  on the ML environment is local to the whole proof body, but ignoring the
  block structure.
\<close>

notepad
begin
  ML_prf %"ML" \<open>val a = 1\<close>
  {
    ML_prf %"ML" \<open>val b = a + 1\<close>
  } \<comment> \<open>Isar block structure ignored by ML environment\<close>
  ML_prf %"ML" \<open>val c = b + 1\<close>
end

text \<open>
  By side-stepping the normal scoping rules for Isar proof blocks, embedded ML
  code can refer to the different contexts and manipulate corresponding
  entities, e.g.\ export a fact from a block context.

  \<^medskip>
  Two further ML commands are useful in certain situations: @{command_ref
  ML_val} and @{command_ref ML_command} are \<^emph>\<open>diagnostic\<close> in the sense that
  there is no effect on the underlying environment, and can thus be used
  anywhere. The examples below produce long strings of digits by invoking \<^ML>\<open>factorial\<close>: @{command ML_val} takes care of printing the ML toplevel result,
  but @{command ML_command} is silent so we produce an explicit output
  message.
\<close>

ML_val \<open>factorial 100\<close>
ML_command \<open>writeln (string_of_int (factorial 100))\<close>

notepad
begin
  ML_val \<open>factorial 100\<close>
  ML_command \<open>writeln (string_of_int (factorial 100))\<close>
end


subsection \<open>Compile-time context\<close>

text \<open>
  Whenever the ML compiler is invoked within Isabelle/Isar, the formal context
  is passed as a thread-local reference variable. Thus ML code may access the
  theory context during compilation, by reading or writing the (local) theory
  under construction. Note that such direct access to the compile-time context
  is rare. In practice it is typically done via some derived ML functions
  instead.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Context.the_generic_context: "unit -> Context.generic"} \\
  @{define_ML "Context.>>": "(Context.generic -> Context.generic) -> unit"} \\
  @{define_ML ML_Thms.bind_thms: "string * thm list -> unit"} \\
  @{define_ML ML_Thms.bind_thm: "string * thm -> unit"} \\
  \end{mldecls}

    \<^descr> \<^ML>\<open>Context.the_generic_context ()\<close> refers to the theory context of
    the ML toplevel --- at compile time. ML code needs to take care to refer to
    \<^ML>\<open>Context.the_generic_context ()\<close> correctly. Recall that evaluation
    of a function body is delayed until actual run-time.

    \<^descr> \<^ML>\<open>Context.>>\<close>~\<open>f\<close> applies context transformation \<open>f\<close> to the implicit
    context of the ML toplevel.

    \<^descr> \<^ML>\<open>ML_Thms.bind_thms\<close>~\<open>(name, thms)\<close> stores a list of theorems produced
    in ML both in the (global) theory context and the ML toplevel, associating
    it with the provided name.

    \<^descr> \<^ML>\<open>ML_Thms.bind_thm\<close> is similar to \<^ML>\<open>ML_Thms.bind_thms\<close> but refers to
    a singleton fact.

  It is important to note that the above functions are really restricted to
  the compile time, even though the ML compiler is invoked at run-time. The
  majority of ML code either uses static antiquotations
  (\secref{sec:ML-antiq}) or refers to the theory or proof context at
  run-time, by explicit functional abstraction.
\<close>


subsection \<open>Antiquotations \label{sec:ML-antiq}\<close>

text \<open>
  A very important consequence of embedding ML into Isar is the concept of
  \<^emph>\<open>ML antiquotation\<close>. The standard token language of ML is augmented by
  special syntactic entities of the following form:

  \<^rail>\<open>
  @{syntax_def antiquote}: '@{' name args '}'
  \<close>

  Here @{syntax name} and @{syntax args} are outer syntax categories, as
  defined in @{cite "isabelle-isar-ref"}.

  \<^medskip>
  A regular antiquotation \<open>@{name args}\<close> processes its arguments by the usual
  means of the Isar source language, and produces corresponding ML source
  text, either as literal \<^emph>\<open>inline\<close> text (e.g.\ \<open>@{term t}\<close>) or abstract
  \<^emph>\<open>value\<close> (e.g. \<open>@{thm th}\<close>). This pre-compilation scheme allows to refer to
  formal entities in a robust manner, with proper static scoping and with some
  degree of logical checking of small portions of the code.
\<close>


subsection \<open>Printing ML values\<close>

text \<open>
  The ML compiler knows about the structure of values according to their
  static type, and can print them in the manner of its toplevel, although the
  details are non-portable. The antiquotations @{ML_antiquotation_def
  "make_string"} and @{ML_antiquotation_def "print"} provide a quasi-portable
  way to refer to this potential capability of the underlying ML system in
  generic Isabelle/ML sources.

  This is occasionally useful for diagnostic or demonstration purposes. Note
  that production-quality tools require proper user-level error messages,
  avoiding raw ML values in the output.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "make_string"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "print"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  @@{ML_antiquotation make_string}
  ;
  @@{ML_antiquotation print} embedded?
  \<close>

  \<^descr> \<open>@{make_string}\<close> inlines a function to print arbitrary values similar to
  the ML toplevel. The result is compiler dependent and may fall back on "?"
  in certain situations. The value of configuration option @{attribute_ref
  ML_print_depth} determines further details of output.

  \<^descr> \<open>@{print f}\<close> uses the ML function \<open>f: string -> unit\<close> to output the result
  of \<open>@{make_string}\<close> above, together with the source position of the
  antiquotation. The default output function is \<^ML>\<open>writeln\<close>.
\<close>

text %mlex \<open>
  The following artificial examples show how to produce adhoc output of ML
  values for debugging purposes.
\<close>

ML_val \<open>
  val x = 42;
  val y = true;

  writeln (\<^make_string> {x = x, y = y});

  \<^print> {x = x, y = y};
  \<^print>\<open>tracing\<close> {x = x, y = y};
\<close>


section \<open>Canonical argument order \label{sec:canonical-argument-order}\<close>

text \<open>
  Standard ML is a language in the tradition of \<open>\<lambda>\<close>-calculus and
  \<^emph>\<open>higher-order functional programming\<close>, similar to OCaml, Haskell, or
  Isabelle/Pure and HOL as logical languages. Getting acquainted with the
  native style of representing functions in that setting can save a lot of
  extra boiler-plate of redundant shuffling of arguments, auxiliary
  abstractions etc.

  Functions are usually \<^emph>\<open>curried\<close>: the idea of turning arguments of type
  \<open>\<tau>\<^sub>i\<close> (for \<open>i \<in> {1, \<dots> n}\<close>) into a result of type \<open>\<tau>\<close> is represented by the
  iterated function space \<open>\<tau>\<^sub>1 \<rightarrow> \<dots> \<rightarrow> \<tau>\<^sub>n \<rightarrow> \<tau>\<close>. This is isomorphic to the
  well-known encoding via tuples \<open>\<tau>\<^sub>1 \<times> \<dots> \<times> \<tau>\<^sub>n \<rightarrow> \<tau>\<close>, but the curried version
  fits more smoothly into the basic calculus.\<^footnote>\<open>The difference is even more
  significant in HOL, because the redundant tuple structure needs to be
  accommodated extraneous proof steps.\<close>

  Currying gives some flexibility due to \<^emph>\<open>partial application\<close>. A function
  \<open>f: \<tau>\<^sub>1 \<rightarrow> \<tau>\<^sub>2 \<rightarrow> \<tau>\<close> can be applied to \<open>x: \<tau>\<^sub>1\<close> and the remaining \<open>(f x): \<tau>\<^sub>2
  \<rightarrow> \<tau>\<close> passed to another function etc. How well this works in practice depends
  on the order of arguments. In the worst case, arguments are arranged
  erratically, and using a function in a certain situation always requires
  some glue code. Thus we would get exponentially many opportunities to
  decorate the code with meaningless permutations of arguments.

  This can be avoided by \<^emph>\<open>canonical argument order\<close>, which observes certain
  standard patterns and minimizes adhoc permutations in their application. In
  Isabelle/ML, large portions of text can be written without auxiliary
  operations like \<open>swap: \<alpha> \<times> \<beta> \<rightarrow> \<beta> \<times> \<alpha>\<close> or \<open>C: (\<alpha> \<rightarrow> \<beta> \<rightarrow> \<gamma>) \<rightarrow> (\<beta> \<rightarrow> \<alpha> \<rightarrow> \<gamma>)\<close> (the
  latter is not present in the Isabelle/ML library).

  \<^medskip>
  The main idea is that arguments that vary less are moved further to the left
  than those that vary more. Two particularly important categories of
  functions are \<^emph>\<open>selectors\<close> and \<^emph>\<open>updates\<close>.

  The subsequent scheme is based on a hypothetical set-like container of type
  \<open>\<beta>\<close> that manages elements of type \<open>\<alpha>\<close>. Both the names and types of the
  associated operations are canonical for Isabelle/ML.

  \begin{center}
  \begin{tabular}{ll}
  kind & canonical name and type \\\hline
  selector & \<open>member: \<beta> \<rightarrow> \<alpha> \<rightarrow> bool\<close> \\
  update & \<open>insert: \<alpha> \<rightarrow> \<beta> \<rightarrow> \<beta>\<close> \\
  \end{tabular}
  \end{center}

  Given a container \<open>B: \<beta>\<close>, the partially applied \<open>member B\<close> is a predicate
  over elements \<open>\<alpha> \<rightarrow> bool\<close>, and thus represents the intended denotation
  directly. It is customary to pass the abstract predicate to further
  operations, not the concrete container. The argument order makes it easy to
  use other combinators: \<open>forall (member B) list\<close> will check a list of
  elements for membership in \<open>B\<close> etc. Often the explicit \<open>list\<close> is pointless
  and can be contracted to \<open>forall (member B)\<close> to get directly a predicate
  again.

  In contrast, an update operation varies the container, so it moves to the
  right: \<open>insert a\<close> is a function \<open>\<beta> \<rightarrow> \<beta>\<close> to insert a value \<open>a\<close>. These can be
  composed naturally as \<open>insert c \<circ> insert b \<circ> insert a\<close>. The slightly awkward
  inversion of the composition order is due to conventional mathematical
  notation, which can be easily amended as explained below.
\<close>


subsection \<open>Forward application and composition\<close>

text \<open>
  Regular function application and infix notation works best for relatively
  deeply structured expressions, e.g.\ \<open>h (f x y + g z)\<close>. The important
  special case of \<^emph>\<open>linear transformation\<close> applies a cascade of functions \<open>f\<^sub>n
  (\<dots> (f\<^sub>1 x))\<close>. This becomes hard to read and maintain if the functions are
  themselves given as complex expressions. The notation can be significantly
  improved by introducing \<^emph>\<open>forward\<close> versions of application and composition
  as follows:

  \<^medskip>
  \begin{tabular}{lll}
  \<open>x |> f\<close> & \<open>\<equiv>\<close> & \<open>f x\<close> \\
  \<open>(f #> g) x\<close> & \<open>\<equiv>\<close> & \<open>x |> f |> g\<close> \\
  \end{tabular}
  \<^medskip>

  This enables to write conveniently \<open>x |> f\<^sub>1 |> \<dots> |> f\<^sub>n\<close> or \<open>f\<^sub>1 #> \<dots> #>
  f\<^sub>n\<close> for its functional abstraction over \<open>x\<close>.

  \<^medskip>
  There is an additional set of combinators to accommodate multiple results
  (via pairs) that are passed on as multiple arguments (via currying).

  \<^medskip>
  \begin{tabular}{lll}
  \<open>(x, y) |-> f\<close> & \<open>\<equiv>\<close> & \<open>f x y\<close> \\
  \<open>(f #-> g) x\<close> & \<open>\<equiv>\<close> & \<open>x |> f |-> g\<close> \\
  \end{tabular}
  \<^medskip>
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_infix "|>" : "'a * ('a -> 'b) -> 'b"} \\
  @{define_ML_infix "|->" : "('c * 'a) * ('c -> 'a -> 'b) -> 'b"} \\
  @{define_ML_infix "#>" : "('a -> 'b) * ('b -> 'c) -> 'a -> 'c"} \\
  @{define_ML_infix "#->" : "('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd"} \\
  \end{mldecls}
\<close>


subsection \<open>Canonical iteration\<close>

text \<open>
  As explained above, a function \<open>f: \<alpha> \<rightarrow> \<beta> \<rightarrow> \<beta>\<close> can be understood as update on
  a configuration of type \<open>\<beta>\<close>, parameterized by an argument of type \<open>\<alpha>\<close>. Given
  \<open>a: \<alpha>\<close> the partial application \<open>(f a): \<beta> \<rightarrow> \<beta>\<close> operates homogeneously on \<open>\<beta>\<close>.
  This can be iterated naturally over a list of parameters \<open>[a\<^sub>1, \<dots>, a\<^sub>n]\<close> as
  \<open>f a\<^sub>1 #> \<dots> #> f a\<^sub>n\<close>. The latter expression is again a function \<open>\<beta> \<rightarrow> \<beta>\<close>. It
  can be applied to an initial configuration \<open>b: \<beta>\<close> to start the iteration
  over the given list of arguments: each \<open>a\<close> in \<open>a\<^sub>1, \<dots>, a\<^sub>n\<close> is applied
  consecutively by updating a cumulative configuration.

  The \<open>fold\<close> combinator in Isabelle/ML lifts a function \<open>f\<close> as above to its
  iterated version over a list of arguments. Lifting can be repeated, e.g.\
  \<open>(fold \<circ> fold) f\<close> iterates over a list of lists as expected.

  The variant \<open>fold_rev\<close> works inside-out over the list of arguments, such
  that \<open>fold_rev f \<equiv> fold f \<circ> rev\<close> holds.

  The \<open>fold_map\<close> combinator essentially performs \<open>fold\<close> and \<open>map\<close>
  simultaneously: each application of \<open>f\<close> produces an updated configuration
  together with a side-result; the iteration collects all such side-results as
  a separate list.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML fold: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  @{define_ML fold_rev: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  @{define_ML fold_map: "('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>fold\<close>~\<open>f\<close> lifts the parametrized update function \<open>f\<close> to a list of
  parameters.

  \<^descr> \<^ML>\<open>fold_rev\<close>~\<open>f\<close> is similar to \<^ML>\<open>fold\<close>~\<open>f\<close>, but works inside-out, as
  if the list would be reversed.

  \<^descr> \<^ML>\<open>fold_map\<close>~\<open>f\<close> lifts the parametrized update function \<open>f\<close> (with
  side-result) to a list of parameters and cumulative side-results.


  \begin{warn}
  The literature on functional programming provides a confusing multitude of
  combinators called \<open>foldl\<close>, \<open>foldr\<close> etc. SML97 provides its own variations
  as \<^ML>\<open>List.foldl\<close> and \<^ML>\<open>List.foldr\<close>, while the classic Isabelle library
  also has the historic \<^ML>\<open>Library.foldl\<close> and \<^ML>\<open>Library.foldr\<close>. To avoid
  unnecessary complication, all these historical versions should be ignored,
  and the canonical \<^ML>\<open>fold\<close> (or \<^ML>\<open>fold_rev\<close>) used exclusively.
  \end{warn}
\<close>

text %mlex \<open>
  The following example shows how to fill a text buffer incrementally by
  adding strings, either individually or from a given list.
\<close>

ML_val \<open>
  val s =
    Buffer.empty
    |> Buffer.add "digits: "
    |> fold (Buffer.add o string_of_int) (0 upto 9)
    |> Buffer.content;

  \<^assert> (s = "digits: 0123456789");
\<close>

text \<open>
  Note how \<^ML>\<open>fold (Buffer.add o string_of_int)\<close> above saves an extra \<^ML>\<open>map\<close> over the given list. This kind of peephole optimization reduces both
  the code size and the tree structures in memory (``deforestation''), but it
  requires some practice to read and write fluently.

  \<^medskip>
  The next example elaborates the idea of canonical iteration, demonstrating
  fast accumulation of tree content using a text buffer.
\<close>

ML \<open>
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
\<close>

text \<open>
  The slowness of \<^ML>\<open>slow_content\<close> is due to the \<^ML>\<open>implode\<close> of the
  recursive results, because it copies previously produced strings again and
  again.

  The incremental \<^ML>\<open>add_content\<close> avoids this by operating on a buffer that
  is passed through in a linear fashion. Using \<^ML_text>\<open>#>\<close> and contraction
  over the actual buffer argument saves some additional boiler-plate. Of
  course, the two \<^ML>\<open>Buffer.add\<close> invocations with concatenated strings
  could have been split into smaller parts, but this would have obfuscated the
  source without making a big difference in performance. Here we have done
  some peephole-optimization for the sake of readability.

  Another benefit of \<^ML>\<open>add_content\<close> is its ``open'' form as a function on
  buffers that can be continued in further linear transformations, folding
  etc. Thus it is more compositional than the naive \<^ML>\<open>slow_content\<close>. As
  realistic example, compare the old-style
  \<^ML>\<open>Term.maxidx_of_term: term -> int\<close> with the newer \<^ML>\<open>Term.maxidx_term: term -> int -> int\<close> in Isabelle/Pure.

  Note that \<^ML>\<open>fast_content\<close> above is only defined as example. In many
  practical situations, it is customary to provide the incremental \<^ML>\<open>add_content\<close> only and leave the initialization and termination to the
  concrete application to the user.
\<close>


section \<open>Message output channels \label{sec:message-channels}\<close>

text \<open>
  Isabelle provides output channels for different kinds of messages: regular
  output, high-volume tracing information, warnings, and errors.

  Depending on the user interface involved, these messages may appear in
  different text styles or colours. The standard output for batch sessions
  prefixes each line of warnings by \<^verbatim>\<open>###\<close> and errors by \<^verbatim>\<open>***\<close>, but leaves
  anything else unchanged. The message body may contain further markup and
  formatting, which is routinely used in the Prover IDE @{cite
  "isabelle-jedit"}.

  Messages are associated with the transaction context of the running Isar
  command. This enables the front-end to manage commands and resulting
  messages together. For example, after deleting a command from a given theory
  document version, the corresponding message output can be retracted from the
  display.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML writeln: "string -> unit"} \\
  @{define_ML tracing: "string -> unit"} \\
  @{define_ML warning: "string -> unit"} \\
  @{define_ML error: "string -> 'a"} % FIXME Output.error_message (!?) \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>writeln\<close>~\<open>text\<close> outputs \<open>text\<close> as regular message. This is the
  primary message output operation of Isabelle and should be used by default.

  \<^descr> \<^ML>\<open>tracing\<close>~\<open>text\<close> outputs \<open>text\<close> as special tracing message, indicating
  potential high-volume output to the front-end (hundreds or thousands of
  messages issued by a single command). The idea is to allow the
  user-interface to downgrade the quality of message display to achieve higher
  throughput.

  Note that the user might have to take special actions to see tracing output,
  e.g.\ switch to a different output window. So this channel should not be
  used for regular output.

  \<^descr> \<^ML>\<open>warning\<close>~\<open>text\<close> outputs \<open>text\<close> as warning, which typically means some
  extra emphasis on the front-end side (color highlighting, icons, etc.).

  \<^descr> \<^ML>\<open>error\<close>~\<open>text\<close> raises exception \<^ML>\<open>ERROR\<close>~\<open>text\<close> and thus lets the
  Isar toplevel print \<open>text\<close> on the error channel, which typically means some
  extra emphasis on the front-end side (color highlighting, icons, etc.).

  This assumes that the exception is not handled before the command
  terminates. Handling exception \<^ML>\<open>ERROR\<close>~\<open>text\<close> is a perfectly legal
  alternative: it means that the error is absorbed without any message output.

  \begin{warn}
  The actual error channel is accessed via \<^ML>\<open>Output.error_message\<close>, but
  this is normally not used directly in user code.
  \end{warn}


  \begin{warn}
  Regular Isabelle/ML code should output messages exclusively by the official
  channels. Using raw I/O on \<^emph>\<open>stdout\<close> or \<^emph>\<open>stderr\<close> instead (e.g.\ via \<^ML>\<open>TextIO.output\<close>) is apt to cause problems in the presence of parallel and
  asynchronous processing of Isabelle theories. Such raw output might be
  displayed by the front-end in some system console log, with a low chance
  that the user will ever see it. Moreover, as a genuine side-effect on global
  process channels, there is no proper way to retract output when Isar command
  transactions are reset by the system.
  \end{warn}

  \begin{warn}
  The message channels should be used in a message-oriented manner. This means
  that multi-line output that logically belongs together is issued by a single
  invocation of \<^ML>\<open>writeln\<close> etc.\ with the functional concatenation of all
  message constituents.
  \end{warn}
\<close>

text %mlex \<open>
  The following example demonstrates a multi-line warning. Note that in some
  situations the user sees only the first line, so the most important point
  should be made first.
\<close>

ML_command \<open>
  warning (cat_lines
   ["Beware the Jabberwock, my son!",
    "The jaws that bite, the claws that catch!",
    "Beware the Jubjub Bird, and shun",
    "The frumious Bandersnatch!"]);
\<close>

text \<open>
  \<^medskip>
  An alternative is to make a paragraph of freely-floating words as follows.
\<close>

ML_command \<open>
  warning (Pretty.string_of (Pretty.para
    "Beware the Jabberwock, my son! \
    \The jaws that bite, the claws that catch! \
    \Beware the Jubjub Bird, and shun \
    \The frumious Bandersnatch!"))
\<close>

text \<open>
  This has advantages with variable window / popup sizes, but might make it
  harder to search for message content systematically, e.g.\ by other tools or
  by humans expecting the ``verse'' of a formal message in a fixed layout.
\<close>


section \<open>Exceptions \label{sec:exceptions}\<close>

text \<open>
  The Standard ML semantics of strict functional evaluation together with
  exceptions is rather well defined, but some delicate points need to be
  observed to avoid that ML programs go wrong despite static type-checking.
  Exceptions in Isabelle/ML are subsequently categorized as follows.
\<close>

paragraph \<open>Regular user errors.\<close>
text \<open>
  These are meant to provide informative feedback about malformed input etc.

  The \<^emph>\<open>error\<close> function raises the corresponding \<^ML>\<open>ERROR\<close> exception, with a
  plain text message as argument. \<^ML>\<open>ERROR\<close> exceptions can be handled
  internally, in order to be ignored, turned into other exceptions, or
  cascaded by appending messages. If the corresponding Isabelle/Isar command
  terminates with an \<^ML>\<open>ERROR\<close> exception state, the system will print the
  result on the error channel (see \secref{sec:message-channels}).

  It is considered bad style to refer to internal function names or values in
  ML source notation in user error messages. Do not use \<open>@{make_string}\<close> nor
  \<open>@{here}\<close>!

  Grammatical correctness of error messages can be improved by \<^emph>\<open>omitting\<close>
  final punctuation: messages are often concatenated or put into a larger
  context (e.g.\ augmented with source position). Note that punctuation after
  formal entities (types, terms, theorems) is particularly prone to user
  confusion.
\<close>

paragraph \<open>Program failures.\<close>
text \<open>
  There is a handful of standard exceptions that indicate general failure
  situations, or failures of core operations on logical entities (types,
  terms, theorems, theories, see \chref{ch:logic}).

  These exceptions indicate a genuine breakdown of the program, so the main
  purpose is to determine quickly what has happened where. Traditionally, the
  (short) exception message would include the name of an ML function, although
  this is no longer necessary, because the ML runtime system attaches detailed
  source position stemming from the corresponding \<^ML_text>\<open>raise\<close> keyword.

  \<^medskip>
  User modules can always introduce their own custom exceptions locally, e.g.\
  to organize internal failures robustly without overlapping with existing
  exceptions. Exceptions that are exposed in module signatures require extra
  care, though, and should \<^emph>\<open>not\<close> be introduced by default. Surprise by users
  of a module can be often minimized by using plain user errors instead.
\<close>

paragraph \<open>Interrupts.\<close>
text \<open>
  These indicate arbitrary system events: both the ML runtime system and the
  Isabelle/ML infrastructure signal various exceptional situations by raising
  the special \<^ML>\<open>Exn.Interrupt\<close> exception in user code.

  This is the one and only way that physical events can intrude an Isabelle/ML
  program. Such an interrupt can mean out-of-memory, stack overflow, timeout,
  internal signaling of threads, or a POSIX process signal. An Isabelle/ML
  program that intercepts interrupts becomes dependent on physical effects of
  the environment. Even worse, exception handling patterns that are too
  general by accident, e.g.\ by misspelled exception constructors, will cover
  interrupts unintentionally and thus render the program semantics
  ill-defined.

  Note that the Interrupt exception dates back to the original SML90 language
  definition. It was excluded from the SML97 version to avoid its malign
  impact on ML program semantics, but without providing a viable alternative.
  Isabelle/ML recovers physical interruptibility (which is an indispensable
  tool to implement managed evaluation of command transactions), but requires
  user code to be strictly transparent wrt.\ interrupts.

  \begin{warn}
  Isabelle/ML user code needs to terminate promptly on interruption, without
  guessing at its meaning to the system infrastructure. Temporary handling of
  interrupts for cleanup of global resources etc.\ needs to be followed
  immediately by re-raising of the original exception.
  \end{warn}
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML try: "('a -> 'b) -> 'a -> 'b option"} \\
  @{define_ML can: "('a -> 'b) -> 'a -> bool"} \\
  @{define_ML_exception ERROR of string} \\
  @{define_ML_exception Fail of string} \\
  @{define_ML Exn.is_interrupt: "exn -> bool"} \\
  @{define_ML Exn.reraise: "exn -> 'a"} \\
  @{define_ML Runtime.exn_trace: "(unit -> 'a) -> 'a"} \\
  \end{mldecls}

  \<^rail>\<open>
    (@@{ML_antiquotation try} | @@{ML_antiquotation can}) embedded
  \<close>

  \<^descr> \<^ML>\<open>try\<close>~\<open>f x\<close> makes the partiality of evaluating \<open>f x\<close> explicit via the
  option datatype. Interrupts are \<^emph>\<open>not\<close> handled here, i.e.\ this form serves
  as safe replacement for the \<^emph>\<open>unsafe\<close> version \<^ML_text>\<open>(SOME\<close>~\<open>f
  x\<close>~\<^ML_text>\<open>handle _ => NONE)\<close> that is occasionally seen in books about
  SML97, but not in Isabelle/ML.

  \<^descr> \<^ML>\<open>can\<close> is similar to \<^ML>\<open>try\<close> with more abstract result.

  \<^descr> \<^ML>\<open>ERROR\<close>~\<open>msg\<close> represents user errors; this exception is normally
  raised indirectly via the \<^ML>\<open>error\<close> function (see
  \secref{sec:message-channels}).

  \<^descr> \<^ML>\<open>Fail\<close>~\<open>msg\<close> represents general program failures.

  \<^descr> \<^ML>\<open>Exn.is_interrupt\<close> identifies interrupts robustly, without mentioning
  concrete exception constructors in user code. Handled interrupts need to be
  re-raised promptly!

  \<^descr> \<^ML>\<open>Exn.reraise\<close>~\<open>exn\<close> raises exception \<open>exn\<close> while preserving its implicit
  position information (if possible, depending on the ML platform).

  \<^descr> \<^ML>\<open>Runtime.exn_trace\<close>~\<^ML_text>\<open>(fn () =>\<close>~\<open>e\<close>\<^ML_text>\<open>)\<close> evaluates
  expression \<open>e\<close> while printing a full trace of its stack of nested exceptions
  (if possible, depending on the ML platform).

  Inserting \<^ML>\<open>Runtime.exn_trace\<close> into ML code temporarily is useful for
  debugging, but not suitable for production code.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "try"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "can"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "assert"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "undefined"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^descr> \<open>@{try}\<close> and \<open>{can}\<close> are similar to the corresponding functions, but the
  argument is taken directly as ML expression: functional abstraction and
  application is done implicitly.

  \<^descr> \<open>@{assert}\<close> inlines a function \<^ML_type>\<open>bool -> unit\<close> that raises
  \<^ML>\<open>Fail\<close> if the argument is \<^ML>\<open>false\<close>. Due to inlining the source
  position of failed assertions is included in the error output.

  \<^descr> \<open>@{undefined}\<close> inlines \<^verbatim>\<open>raise\<close>~\<^ML>\<open>Match\<close>, i.e.\ the ML program
  behaves as in some function application of an undefined case.
\<close>

text %mlex \<open>
  We define a total version of division: any failures are swept under the
  carpet and mapped to a default value. Thus division-by-zero becomes 0, but
  there could be other exceptions like overflow that produce the same result
  (for unbounded integers this does not happen).
\<close>

ML \<open>
  fun div_total x y = \<^try>\<open>x div y\<close> |> the_default 0;

  \<^assert> (div_total 1 0 = 0);
\<close>

text \<open>
  The ML function \<^ML>\<open>undefined\<close> is defined in \<^file>\<open>~~/src/Pure/library.ML\<close>
  as follows:
\<close>

ML \<open>fun undefined _ = raise Match\<close>

text \<open>
  \<^medskip>
  The following variant uses the antiquotation @{ML_antiquotation undefined}
  instead:
\<close>

ML \<open>fun undefined _ = \<^undefined>\<close>

text \<open>
  \<^medskip>
  Here is the same, using control-symbol notation for the antiquotation, with
  special rendering of \<^verbatim>\<open>\<^undefined>\<close>:
\<close>

ML \<open>fun undefined _ = \<^undefined>\<close>

text \<open>
  \<^medskip> Semantically, all forms are equivalent to a function definition
  without any clauses, but that is syntactically not allowed in ML.
\<close>


section \<open>Strings of symbols \label{sec:symbols}\<close>

text \<open>
  A \<^emph>\<open>symbol\<close> constitutes the smallest textual unit in Isabelle/ML --- raw ML
  characters are normally not encountered at all. Isabelle strings consist of
  a sequence of symbols, represented as a packed string or an exploded list of
  strings. Each symbol is in itself a small string, which has either one of
  the following forms:

    \<^enum> a single ASCII character ``\<open>c\<close>'', for example ``\<^verbatim>\<open>a\<close>'',

    \<^enum> a codepoint according to UTF-8 (non-ASCII byte sequence),

    \<^enum> a regular symbol ``\<^verbatim>\<open>\<ident>\<close>'', for example ``\<^verbatim>\<open>\<alpha>\<close>'',

    \<^enum> a control symbol ``\<^verbatim>\<open>\<^ident>\<close>'', for example ``\<^verbatim>\<open>\<^bold>\<close>'',

  The \<open>ident\<close> syntax for symbol names is \<open>letter (letter | digit)\<^sup>*\<close>, where
  \<open>letter = A..Za..z\<close> and \<open>digit = 0..9\<close>. There are infinitely many regular
  symbols and control symbols, but a fixed collection of standard symbols is
  treated specifically. For example, ``\<^verbatim>\<open>\<alpha>\<close>'' is classified as a letter, which
  means it may occur within regular Isabelle identifiers.

  The character set underlying Isabelle symbols is 7-bit ASCII, but 8-bit
  character sequences are passed-through unchanged. Unicode/UCS data in UTF-8
  encoding is processed in a non-strict fashion, such that well-formed code
  sequences are recognized accordingly. Unicode provides its own collection of
  mathematical symbols, but within the core Isabelle/ML world there is no link
  to the standard collection of Isabelle regular symbols.

  \<^medskip>
  Output of Isabelle symbols depends on the print mode. For example, the
  standard {\LaTeX} setup of the Isabelle document preparation system would
  present ``\<^verbatim>\<open>\<alpha>\<close>'' as \<open>\<alpha>\<close>, and ``\<^verbatim>\<open>\<^bold>\<alpha>\<close>'' as \<open>\<^bold>\<alpha>\<close>. On-screen rendering usually
  works by mapping a finite subset of Isabelle symbols to suitable Unicode
  characters.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Symbol.symbol = string} \\
  @{define_ML Symbol.explode: "string -> Symbol.symbol list"} \\
  @{define_ML Symbol.is_letter: "Symbol.symbol -> bool"} \\
  @{define_ML Symbol.is_digit: "Symbol.symbol -> bool"} \\
  @{define_ML Symbol.is_quasi: "Symbol.symbol -> bool"} \\
  @{define_ML Symbol.is_blank: "Symbol.symbol -> bool"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML_type "Symbol.sym"} \\
  @{define_ML Symbol.decode: "Symbol.symbol -> Symbol.sym"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Symbol.symbol\<close> represents individual Isabelle symbols.

  \<^descr> \<^ML>\<open>Symbol.explode\<close>~\<open>str\<close> produces a symbol list from the packed form.
  This function supersedes \<^ML>\<open>String.explode\<close> for virtually all purposes
  of manipulating text in Isabelle!\<^footnote>\<open>The runtime overhead for exploded strings
  is mainly that of the list structure: individual symbols that happen to be a
  singleton string do not require extra memory in Poly/ML.\<close>

  \<^descr> \<^ML>\<open>Symbol.is_letter\<close>, \<^ML>\<open>Symbol.is_digit\<close>, \<^ML>\<open>Symbol.is_quasi\<close>, \<^ML>\<open>Symbol.is_blank\<close> classify standard symbols
  according to fixed syntactic conventions of Isabelle, cf.\ @{cite
  "isabelle-isar-ref"}.

  \<^descr> Type \<^ML_type>\<open>Symbol.sym\<close> is a concrete datatype that represents the
  different kinds of symbols explicitly, with constructors \<^ML>\<open>Symbol.Char\<close>, \<^ML>\<open>Symbol.UTF8\<close>, \<^ML>\<open>Symbol.Sym\<close>, \<^ML>\<open>Symbol.Control\<close>, \<^ML>\<open>Symbol.Malformed\<close>.

  \<^descr> \<^ML>\<open>Symbol.decode\<close> converts the string representation of a symbol into
  the datatype version.
\<close>

paragraph \<open>Historical note.\<close>
text \<open>
  In the original SML90 standard the primitive ML type \<^ML_type>\<open>char\<close> did not
  exists, and \<^ML_text>\<open>explode: string -> string list\<close> produced a list of
  singleton strings like \<^ML>\<open>raw_explode: string -> string list\<close> in
  Isabelle/ML today. When SML97 came out, Isabelle did not adopt its somewhat
  anachronistic 8-bit or 16-bit characters, but the idea of exploding a string
  into a list of small strings was extended to ``symbols'' as explained above.
  Thus Isabelle sources can refer to an infinite store of user-defined
  symbols, without having to worry about the multitude of Unicode encodings
  that have emerged over the years.
\<close>


section \<open>Basic data types\<close>

text \<open>
  The basis library proposal of SML97 needs to be treated with caution. Many
  of its operations simply do not fit with important Isabelle/ML conventions
  (like ``canonical argument order'', see
  \secref{sec:canonical-argument-order}), others cause problems with the
  parallel evaluation model of Isabelle/ML (such as \<^ML>\<open>TextIO.print\<close> or \<^ML>\<open>OS.Process.system\<close>).

  Subsequently we give a brief overview of important operations on basic ML
  data types.
\<close>


subsection \<open>Characters\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type char} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>char\<close> is \<^emph>\<open>not\<close> used. The smallest textual unit in Isabelle
  is represented as a ``symbol'' (see \secref{sec:symbols}).
\<close>


subsection \<open>Strings\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type string} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>string\<close> represents immutable vectors of 8-bit characters.
  There are operations in SML to convert back and forth to actual byte
  vectors, which are seldom used.

  This historically important raw text representation is used for
  Isabelle-specific purposes with the following implicit substructures packed
  into the string content:

    \<^enum> sequence of Isabelle symbols (see also \secref{sec:symbols}), with \<^ML>\<open>Symbol.explode\<close> as key operation;
  
    \<^enum> XML tree structure via YXML (see also @{cite "isabelle-system"}), with
    \<^ML>\<open>YXML.parse_body\<close> as key operation.

  Note that Isabelle/ML string literals may refer Isabelle symbols like
  ``\<^verbatim>\<open>\<alpha>\<close>'' natively, \<^emph>\<open>without\<close> escaping the backslash. This is a consequence
  of Isabelle treating all source text as strings of symbols, instead of raw
  characters.
\<close>

text %mlex \<open>
  The subsequent example illustrates the difference of physical addressing of
  bytes versus logical addressing of symbols in Isabelle strings.
\<close>

ML_val \<open>
  val s = "\<A>";

  \<^assert> (length (Symbol.explode s) = 1);
  \<^assert> (size s = 4);
\<close>

text \<open>
  Note that in Unicode renderings of the symbol \<open>\<A>\<close>, variations of encodings
  like UTF-8 or UTF-16 pose delicate questions about the multi-byte
  representations of its codepoint, which is outside of the 16-bit address
  space of the original Unicode standard from the 1990-ies. In Isabelle/ML it
  is just ``\<^verbatim>\<open>\<A>\<close>'' literally, using plain ASCII characters beyond any
  doubts.
\<close>


subsection \<open>Integers\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type int} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>int\<close> represents regular mathematical integers, which are
  \<^emph>\<open>unbounded\<close>. Overflow is treated properly, but should never happen in
  practice.\<^footnote>\<open>The size limit for integer bit patterns in memory is 64\,MB for
  32-bit Poly/ML, and much higher for 64-bit systems.\<close>

  Structure \<^ML_structure>\<open>IntInf\<close> of SML97 is obsolete and superseded by
  \<^ML_structure>\<open>Int\<close>. Structure \<^ML_structure>\<open>Integer\<close> in
  \<^file>\<open>~~/src/Pure/General/integer.ML\<close> provides some additional operations.
\<close>


subsection \<open>Rational numbers\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Rat.rat} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Rat.rat\<close> represents rational numbers, based on the
  unbounded integers of Poly/ML.

  Literal rationals may be written with special antiquotation syntax
  \<^verbatim>\<open>@\<close>\<open>int\<close>\<^verbatim>\<open>/\<close>\<open>nat\<close> or \<^verbatim>\<open>@\<close>\<open>int\<close> (without any white space). For example
  \<^verbatim>\<open>@~1/4\<close> or \<^verbatim>\<open>@10\<close>. The ML toplevel pretty printer uses the same format.

  Standard operations are provided via ad-hoc overloading of \<^verbatim>\<open>+\<close>, \<^verbatim>\<open>-\<close>, \<^verbatim>\<open>*\<close>,
  \<^verbatim>\<open>/\<close>, etc.
\<close>


subsection \<open>Time\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Time.time} \\
  @{define_ML seconds: "real -> Time.time"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Time.time\<close> represents time abstractly according to the
  SML97 basis library definition. This is adequate for internal ML operations,
  but awkward in concrete time specifications.

  \<^descr> \<^ML>\<open>seconds\<close>~\<open>s\<close> turns the concrete scalar \<open>s\<close> (measured in seconds) into
  an abstract time value. Floating point numbers are easy to use as
  configuration options in the context (see \secref{sec:config-options}) or
  system options that are maintained externally.
\<close>


subsection \<open>Options\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Option.map: "('a -> 'b) -> 'a option -> 'b option"} \\
  @{define_ML is_some: "'a option -> bool"} \\
  @{define_ML is_none: "'a option -> bool"} \\
  @{define_ML the: "'a option -> 'a"} \\
  @{define_ML these: "'a list option -> 'a list"} \\
  @{define_ML the_list: "'a option -> 'a list"} \\
  @{define_ML the_default: "'a -> 'a option -> 'a"} \\
  \end{mldecls}
\<close>

text \<open>
  Apart from \<^ML>\<open>Option.map\<close> most other operations defined in structure
  \<^ML_structure>\<open>Option\<close> are alien to Isabelle/ML and never used. The
  operations shown above are defined in \<^file>\<open>~~/src/Pure/General/basics.ML\<close>.
\<close>


subsection \<open>Lists\<close>

text \<open>
  Lists are ubiquitous in ML as simple and light-weight ``collections'' for
  many everyday programming tasks. Isabelle/ML provides important additions
  and improvements over operations that are predefined in the SML97 library.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML cons: "'a -> 'a list -> 'a list"} \\
  @{define_ML member: "('b * 'a -> bool) -> 'a list -> 'b -> bool"} \\
  @{define_ML insert: "('a * 'a -> bool) -> 'a -> 'a list -> 'a list"} \\
  @{define_ML remove: "('b * 'a -> bool) -> 'b -> 'a list -> 'a list"} \\
  @{define_ML update: "('a * 'a -> bool) -> 'a -> 'a list -> 'a list"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>cons\<close>~\<open>x xs\<close> evaluates to \<open>x :: xs\<close>.

  Tupled infix operators are a historical accident in Standard ML. The curried
  \<^ML>\<open>cons\<close> amends this, but it should be only used when partial application
  is required.

  \<^descr> \<^ML>\<open>member\<close>, \<^ML>\<open>insert\<close>, \<^ML>\<open>remove\<close>, \<^ML>\<open>update\<close> treat lists as a
  set-like container that maintains the order of elements. See
  \<^file>\<open>~~/src/Pure/library.ML\<close> for the full specifications (written in ML).
  There are some further derived operations like \<^ML>\<open>union\<close> or \<^ML>\<open>inter\<close>.

  Note that \<^ML>\<open>insert\<close> is conservative about elements that are already a
  \<^ML>\<open>member\<close> of the list, while \<^ML>\<open>update\<close> ensures that the latest entry
  is always put in front. The latter discipline is often more appropriate in
  declarations of context data (\secref{sec:context-data}) that are issued by
  the user in Isar source: later declarations take precedence over earlier
  ones. \<close>

text %mlex \<open>
  Using canonical \<^ML>\<open>fold\<close> together with \<^ML>\<open>cons\<close> (or similar standard
  operations) alternates the orientation of data. The is quite natural and
  should not be altered forcible by inserting extra applications of \<^ML>\<open>rev\<close>.
  The alternative \<^ML>\<open>fold_rev\<close> can be used in the few situations, where
  alternation should be prevented.
\<close>

ML_val \<open>
  val items = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

  val list1 = fold cons items [];
  \<^assert> (list1 = rev items);

  val list2 = fold_rev cons items [];
  \<^assert> (list2 = items);
\<close>

text \<open>
  The subsequent example demonstrates how to \<^emph>\<open>merge\<close> two lists in a natural
  way.
\<close>

ML_val \<open>
  fun merge_lists eq (xs, ys) = fold_rev (insert eq) ys xs;
\<close>

text \<open>
  Here the first list is treated conservatively: only the new elements from
  the second list are inserted. The inside-out order of insertion via \<^ML>\<open>fold_rev\<close> attempts to preserve the order of elements in the result.

  This way of merging lists is typical for context data
  (\secref{sec:context-data}). See also \<^ML>\<open>merge\<close> as defined in
  \<^file>\<open>~~/src/Pure/library.ML\<close>.
\<close>


subsection \<open>Association lists\<close>

text \<open>
  The operations for association lists interpret a concrete list of pairs as a
  finite function from keys to values. Redundant representations with multiple
  occurrences of the same key are implicitly normalized: lookup and update
  only take the first occurrence into account.
\<close>

text \<open>
  \begin{mldecls}
  @{define_ML AList.lookup: "('a * 'b -> bool) -> ('b * 'c) list -> 'a -> 'c option"} \\
  @{define_ML AList.defined: "('a * 'b -> bool) -> ('b * 'c) list -> 'a -> bool"} \\
  @{define_ML AList.update: "('a * 'a -> bool) -> 'a * 'b -> ('a * 'b) list -> ('a * 'b) list"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>AList.lookup\<close>, \<^ML>\<open>AList.defined\<close>, \<^ML>\<open>AList.update\<close> implement the
  main ``framework operations'' for mappings in Isabelle/ML, following
  standard conventions for their names and types.

  Note that a function called \<^verbatim>\<open>lookup\<close> is obliged to express its partiality
  via an explicit option element. There is no choice to raise an exception,
  without changing the name to something like \<open>the_element\<close> or \<open>get\<close>.

  The \<open>defined\<close> operation is essentially a contraction of \<^ML>\<open>is_some\<close> and
  \<^verbatim>\<open>lookup\<close>, but this is sufficiently frequent to justify its independent
  existence. This also gives the implementation some opportunity for peep-hole
  optimization.


  Association lists are adequate as simple implementation of finite mappings
  in many practical situations. A more advanced table structure is defined in
  \<^file>\<open>~~/src/Pure/General/table.ML\<close>; that version scales easily to thousands or
  millions of elements.
\<close>


subsection \<open>Unsynchronized references\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type 'a "Unsynchronized.ref"} \\
  @{define_ML Unsynchronized.ref: "'a -> 'a Unsynchronized.ref"} \\
  @{define_ML "!": "'a Unsynchronized.ref -> 'a"} \\
  @{define_ML_infix ":=" : "'a Unsynchronized.ref * 'a -> unit"} \\
  \end{mldecls}
\<close>

text \<open>
  Due to ubiquitous parallelism in Isabelle/ML (see also
  \secref{sec:multi-threading}), the mutable reference cells of Standard ML
  are notorious for causing problems. In a highly parallel system, both
  correctness \<^emph>\<open>and\<close> performance are easily degraded when using mutable data.

  The unwieldy name of \<^ML>\<open>Unsynchronized.ref\<close> for the constructor for
  references in Isabelle/ML emphasizes the inconveniences caused by
  mutability. Existing operations \<^ML>\<open>!\<close> and \<^ML_infix>\<open>:=\<close> are unchanged,
  but should be used with special precautions, say in a strictly local
  situation that is guaranteed to be restricted to sequential evaluation ---
  now and in the future.

  \begin{warn}
  Never \<^ML_text>\<open>open Unsynchronized\<close>, not even in a local scope!
  Pretending that mutable state is no problem is a very bad idea.
  \end{warn}
\<close>


section \<open>Thread-safe programming \label{sec:multi-threading}\<close>

text \<open>
  Multi-threaded execution has become an everyday reality in Isabelle since
  Poly/ML 5.2.1 and Isabelle2008. Isabelle/ML provides implicit and explicit
  parallelism by default, and there is no way for user-space tools to ``opt
  out''. ML programs that are purely functional, output messages only via the
  official channels (\secref{sec:message-channels}), and do not intercept
  interrupts (\secref{sec:exceptions}) can participate in the multi-threaded
  environment immediately without further ado.

  More ambitious tools with more fine-grained interaction with the environment
  need to observe the principles explained below.
\<close>


subsection \<open>Multi-threading with shared memory\<close>

text \<open>
  Multiple threads help to organize advanced operations of the system, such as
  real-time conditions on command transactions, sub-components with explicit
  communication, general asynchronous interaction etc. Moreover, parallel
  evaluation is a prerequisite to make adequate use of the CPU resources that
  are available on multi-core systems.\<^footnote>\<open>Multi-core computing does not mean
  that there are ``spare cycles'' to be wasted. It means that the continued
  exponential speedup of CPU performance due to ``Moore's Law'' follows
  different rules: clock frequency has reached its peak around 2005, and
  applications need to be parallelized in order to avoid a perceived loss of
  performance. See also @{cite "Sutter:2005"}.\<close>

  Isabelle/Isar exploits the inherent structure of theories and proofs to
  support \<^emph>\<open>implicit parallelism\<close> to a large extent. LCF-style theorem proving
  provides almost ideal conditions for that, see also @{cite "Wenzel:2009"}.
  This means, significant parts of theory and proof checking is parallelized
  by default. In Isabelle2013, a maximum speedup-factor of 3.5 on 4 cores and
  6.5 on 8 cores can be expected @{cite "Wenzel:2013:ITP"}.

  \<^medskip>
  ML threads lack the memory protection of separate processes, and operate
  concurrently on shared heap memory. This has the advantage that results of
  independent computations are directly available to other threads: abstract
  values can be passed without copying or awkward serialization that is
  typically required for separate processes.

  To make shared-memory multi-threading work robustly and efficiently, some
  programming guidelines need to be observed. While the ML system is
  responsible to maintain basic integrity of the representation of ML values
  in memory, the application programmer needs to ensure that multi-threaded
  execution does not break the intended semantics.

  \begin{warn}
  To participate in implicit parallelism, tools need to be thread-safe. A
  single ill-behaved tool can affect the stability and performance of the
  whole system.
  \end{warn}

  Apart from observing the principles of thread-safeness passively, advanced
  tools may also exploit parallelism actively, e.g.\ by using library
  functions for parallel list operations (\secref{sec:parlist}).

  \begin{warn}
  Parallel computing resources are managed centrally by the Isabelle/ML
  infrastructure. User programs should not fork their own ML threads to
  perform heavy computations.
  \end{warn}
\<close>


subsection \<open>Critical shared resources\<close>

text \<open>
  Thread-safeness is mainly concerned about concurrent read/write access to
  shared resources, which are outside the purely functional world of ML. This
  covers the following in particular.

    \<^item> Global references (or arrays), i.e.\ mutable memory cells that persist
    over several invocations of associated operations.\<^footnote>\<open>This is independent of
    the visibility of such mutable values in the toplevel scope.\<close>

    \<^item> Global state of the running Isabelle/ML process, i.e.\ raw I/O channels,
    environment variables, current working directory.

    \<^item> Writable resources in the file-system that are shared among different
    threads or external processes.

  Isabelle/ML provides various mechanisms to avoid critical shared resources
  in most situations. As last resort there are some mechanisms for explicit
  synchronization. The following guidelines help to make Isabelle/ML programs
  work smoothly in a concurrent environment.

  \<^item> Avoid global references altogether. Isabelle/Isar maintains a uniform
  context that incorporates arbitrary data declared by user programs
  (\secref{sec:context-data}). This context is passed as plain value and user
  tools can get/map their own data in a purely functional manner.
  Configuration options within the context (\secref{sec:config-options})
  provide simple drop-in replacements for historic reference variables.

  \<^item> Keep components with local state information re-entrant. Instead of poking
  initial values into (private) global references, a new state record can be
  created on each invocation, and passed through any auxiliary functions of
  the component. The state record contain mutable references in special
  situations, without requiring any synchronization, as long as each
  invocation gets its own copy and the tool itself is single-threaded.

  \<^item> Avoid raw output on \<open>stdout\<close> or \<open>stderr\<close>. The Poly/ML library is
  thread-safe for each individual output operation, but the ordering of
  parallel invocations is arbitrary. This means raw output will appear on some
  system console with unpredictable interleaving of atomic chunks.

  Note that this does not affect regular message output channels
  (\secref{sec:message-channels}). An official message id is associated with
  the command transaction from where it originates, independently of other
  transactions. This means each running Isar command has effectively its own
  set of message channels, and interleaving can only happen when commands use
  parallelism internally (and only at message boundaries).

  \<^item> Treat environment variables and the current working directory of the
  running process as read-only.

  \<^item> Restrict writing to the file-system to unique temporary files. Isabelle
  already provides a temporary directory that is unique for the running
  process, and there is a centralized source of unique serial numbers in
  Isabelle/ML. Thus temporary files that are passed to to some external
  process will be always disjoint, and thus thread-safe.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML File.tmp_path: "Path.T -> Path.T"} \\
  @{define_ML serial_string: "unit -> string"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>File.tmp_path\<close>~\<open>path\<close> relocates the base component of \<open>path\<close> into the
  unique temporary directory of the running Isabelle/ML process.

  \<^descr> \<^ML>\<open>serial_string\<close>~\<open>()\<close> creates a new serial number that is unique over
  the runtime of the Isabelle/ML process.
\<close>

text %mlex \<open>
  The following example shows how to create unique temporary file names.
\<close>

ML_val \<open>
  val tmp1 = File.tmp_path (Path.basic ("foo" ^ serial_string ()));
  val tmp2 = File.tmp_path (Path.basic ("foo" ^ serial_string ()));
  \<^assert> (tmp1 <> tmp2);
\<close>


subsection \<open>Explicit synchronization\<close>

text \<open>
  Isabelle/ML provides explicit synchronization for mutable variables over
  immutable data, which may be updated atomically and exclusively. This
  addresses the rare situations where mutable shared resources are really
  required. Synchronization in Isabelle/ML is based on primitives of Poly/ML,
  which have been adapted to the specific assumptions of the concurrent
  Isabelle environment. User code should not break this abstraction, but stay
  within the confines of concurrent Isabelle/ML.

  A \<^emph>\<open>synchronized variable\<close> is an explicit state component associated with
  mechanisms for locking and signaling. There are operations to await a
  condition, change the state, and signal the change to all other waiting
  threads. Synchronized access to the state variable is \<^emph>\<open>not\<close> re-entrant:
  direct or indirect nesting within the same thread will cause a deadlock!
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type 'a "Synchronized.var"} \\
  @{define_ML Synchronized.var: "string -> 'a -> 'a Synchronized.var"} \\
  @{define_ML Synchronized.guarded_access: "'a Synchronized.var ->
  ('a -> ('b * 'a) option) -> 'b"} \\
  \end{mldecls}

    \<^descr> Type \<^ML_type>\<open>'a Synchronized.var\<close> represents synchronized variables
    with state of type \<^ML_type>\<open>'a\<close>.

    \<^descr> \<^ML>\<open>Synchronized.var\<close>~\<open>name x\<close> creates a synchronized variable that is
    initialized with value \<open>x\<close>. The \<open>name\<close> is used for tracing.

    \<^descr> \<^ML>\<open>Synchronized.guarded_access\<close>~\<open>var f\<close> lets the function \<open>f\<close> operate
    within a critical section on the state \<open>x\<close> as follows: if \<open>f x\<close> produces
    \<^ML>\<open>NONE\<close>, it continues to wait on the internal condition variable,
    expecting that some other thread will eventually change the content in a
    suitable manner; if \<open>f x\<close> produces \<^ML>\<open>SOME\<close>~\<open>(y, x')\<close> it is satisfied and
    assigns the new state value \<open>x'\<close>, broadcasts a signal to all waiting threads
    on the associated condition variable, and returns the result \<open>y\<close>.

  There are some further variants of the \<^ML>\<open>Synchronized.guarded_access\<close>
  combinator, see \<^file>\<open>~~/src/Pure/Concurrent/synchronized.ML\<close> for details.
\<close>

text %mlex \<open>
  The following example implements a counter that produces positive integers
  that are unique over the runtime of the Isabelle process:
\<close>

ML_val \<open>
  local
    val counter = Synchronized.var "counter" 0;
  in
    fun next () =
      Synchronized.guarded_access counter
        (fn i =>
          let val j = i + 1
          in SOME (j, j) end);
  end;

  val a = next ();
  val b = next ();
  \<^assert> (a <> b);
\<close>

text \<open>
  \<^medskip>
  See \<^file>\<open>~~/src/Pure/Concurrent/mailbox.ML\<close> how to implement a mailbox as
  synchronized variable over a purely functional list.
\<close>


section \<open>Managed evaluation\<close>

text \<open>
  Execution of Standard ML follows the model of strict functional evaluation
  with optional exceptions. Evaluation happens whenever some function is
  applied to (sufficiently many) arguments. The result is either an explicit
  value or an implicit exception.

  \<^emph>\<open>Managed evaluation\<close> in Isabelle/ML organizes expressions and results to
  control certain physical side-conditions, to say more specifically when and
  how evaluation happens. For example, the Isabelle/ML library supports lazy
  evaluation with memoing, parallel evaluation via futures, asynchronous
  evaluation via promises, evaluation with time limit etc.

  \<^medskip>
  An \<^emph>\<open>unevaluated expression\<close> is represented either as unit abstraction
  \<^verbatim>\<open>fn () => a\<close> of type \<^verbatim>\<open>unit -> 'a\<close> or as regular function \<^verbatim>\<open>fn a => b\<close> of
  type \<^verbatim>\<open>'a -> 'b\<close>. Both forms occur routinely, and special care is required
  to tell them apart --- the static type-system of SML is only of limited help
  here.

  The first form is more intuitive: some combinator \<^verbatim>\<open>(unit -> 'a) -> 'a\<close>
  applies the given function to \<^verbatim>\<open>()\<close> to initiate the postponed evaluation
  process. The second form is more flexible: some combinator
  \<^verbatim>\<open>('a -> 'b) -> 'a -> 'b\<close> acts like a modified form of function application;
  several such combinators may be cascaded to modify a given function, before
  it is ultimately applied to some argument.

  \<^medskip>
  \<^emph>\<open>Reified results\<close> make the disjoint sum of regular values versions
  exceptional situations explicit as ML datatype: \<open>'a result = Res of 'a | Exn
  of exn\<close>. This is typically used for administrative purposes, to store the
  overall outcome of an evaluation process.

  \<^emph>\<open>Parallel exceptions\<close> aggregate reified results, such that multiple
  exceptions are digested as a collection in canonical form that identifies
  exceptions according to their original occurrence. This is particular
  important for parallel evaluation via futures \secref{sec:futures}, which
  are organized as acyclic graph of evaluations that depend on other
  evaluations: exceptions stemming from shared sub-graphs are exposed exactly
  once and in the order of their original occurrence (e.g.\ when printed at
  the toplevel). Interrupt counts as neutral element here: it is treated as
  minimal information about some canceled evaluation process, and is absorbed
  by the presence of regular program exceptions.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type 'a "Exn.result"} \\
  @{define_ML Exn.capture: "('a -> 'b) -> 'a -> 'b Exn.result"} \\
  @{define_ML Exn.interruptible_capture: "('a -> 'b) -> 'a -> 'b Exn.result"} \\
  @{define_ML Exn.release: "'a Exn.result -> 'a"} \\
  @{define_ML Par_Exn.release_all: "'a Exn.result list -> 'a list"} \\
  @{define_ML Par_Exn.release_first: "'a Exn.result list -> 'a list"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>'a Exn.result\<close> represents the disjoint sum of ML results
  explicitly, with constructor \<^ML>\<open>Exn.Res\<close> for regular values and \<^ML>\<open>Exn.Exn\<close> for exceptions.

  \<^descr> \<^ML>\<open>Exn.capture\<close>~\<open>f x\<close> manages the evaluation of \<open>f x\<close> such that
  exceptions are made explicit as \<^ML>\<open>Exn.Exn\<close>. Note that this includes
  physical interrupts (see also \secref{sec:exceptions}), so the same
  precautions apply to user code: interrupts must not be absorbed
  accidentally!

  \<^descr> \<^ML>\<open>Exn.interruptible_capture\<close> is similar to \<^ML>\<open>Exn.capture\<close>, but
  interrupts are immediately re-raised as required for user code.

  \<^descr> \<^ML>\<open>Exn.release\<close>~\<open>result\<close> releases the original runtime result, exposing
  its regular value or raising the reified exception.

  \<^descr> \<^ML>\<open>Par_Exn.release_all\<close>~\<open>results\<close> combines results that were produced
  independently (e.g.\ by parallel evaluation). If all results are regular
  values, that list is returned. Otherwise, the collection of all exceptions
  is raised, wrapped-up as collective parallel exception. Note that the latter
  prevents access to individual exceptions by conventional \<^verbatim>\<open>handle\<close> of ML.

  \<^descr> \<^ML>\<open>Par_Exn.release_first\<close> is similar to \<^ML>\<open>Par_Exn.release_all\<close>, but
  only the first (meaningful) exception that has occurred in the original
  evaluation process is raised again, the others are ignored. That single
  exception may get handled by conventional means in ML.
\<close>


subsection \<open>Parallel skeletons \label{sec:parlist}\<close>

text \<open>
  Algorithmic skeletons are combinators that operate on lists in parallel, in
  the manner of well-known \<open>map\<close>, \<open>exists\<close>, \<open>forall\<close> etc. Management of
  futures (\secref{sec:futures}) and their results as reified exceptions is
  wrapped up into simple programming interfaces that resemble the sequential
  versions.

  What remains is the application-specific problem to present expressions with
  suitable \<^emph>\<open>granularity\<close>: each list element corresponds to one evaluation
  task. If the granularity is too coarse, the available CPUs are not
  saturated. If it is too fine-grained, CPU cycles are wasted due to the
  overhead of organizing parallel processing. In the worst case, parallel
  performance will be less than the sequential counterpart!
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Par_List.map: "('a -> 'b) -> 'a list -> 'b list"} \\
  @{define_ML Par_List.get_some: "('a -> 'b option) -> 'a list -> 'b option"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Par_List.map\<close>~\<open>f [x\<^sub>1, \<dots>, x\<^sub>n]\<close> is like \<^ML>\<open>map\<close>~\<open>f [x\<^sub>1, \<dots>,
  x\<^sub>n]\<close>, but the evaluation of \<open>f x\<^sub>i\<close> for \<open>i = 1, \<dots>, n\<close> is performed in
  parallel.

  An exception in any \<open>f x\<^sub>i\<close> cancels the overall evaluation process. The
  final result is produced via \<^ML>\<open>Par_Exn.release_first\<close> as explained above,
  which means the first program exception that happened to occur in the
  parallel evaluation is propagated, and all other failures are ignored.

  \<^descr> \<^ML>\<open>Par_List.get_some\<close>~\<open>f [x\<^sub>1, \<dots>, x\<^sub>n]\<close> produces some \<open>f x\<^sub>i\<close> that is of
  the form \<open>SOME y\<^sub>i\<close>, if that exists, otherwise \<open>NONE\<close>. Thus it is similar to
  \<^ML>\<open>Library.get_first\<close>, but subject to a non-deterministic parallel choice
  process. The first successful result cancels the overall evaluation process;
  other exceptions are propagated as for \<^ML>\<open>Par_List.map\<close>.

  This generic parallel choice combinator is the basis for derived forms, such
  as \<^ML>\<open>Par_List.find_some\<close>, \<^ML>\<open>Par_List.exists\<close>, \<^ML>\<open>Par_List.forall\<close>.
\<close>

text %mlex \<open>
  Subsequently, the Ackermann function is evaluated in parallel for some
  ranges of arguments.
\<close>

ML_val \<open>
  fun ackermann 0 n = n + 1
    | ackermann m 0 = ackermann (m - 1) 1
    | ackermann m n = ackermann (m - 1) (ackermann m (n - 1));

  Par_List.map (ackermann 2) (500 upto 1000);
  Par_List.map (ackermann 3) (5 upto 10);
\<close>


subsection \<open>Lazy evaluation\<close>

text \<open>
  Classic lazy evaluation works via the \<open>lazy\<close>~/ \<open>force\<close> pair of operations:
  \<open>lazy\<close> to wrap an unevaluated expression, and \<open>force\<close> to evaluate it once
  and store its result persistently. Later invocations of \<open>force\<close> retrieve the
  stored result without another evaluation. Isabelle/ML refines this idea to
  accommodate the aspects of multi-threading, synchronous program exceptions
  and asynchronous interrupts.

  The first thread that invokes \<open>force\<close> on an unfinished lazy value changes
  its state into a \<^emph>\<open>promise\<close> of the eventual result and starts evaluating it.
  Any other threads that \<open>force\<close> the same lazy value in the meantime need to
  wait for it to finish, by producing a regular result or program exception.
  If the evaluation attempt is interrupted, this event is propagated to all
  waiting threads and the lazy value is reset to its original state.

  This means a lazy value is completely evaluated at most once, in a
  thread-safe manner. There might be multiple interrupted evaluation attempts,
  and multiple receivers of intermediate interrupt events. Interrupts are
  \<^emph>\<open>not\<close> made persistent: later evaluation attempts start again from the
  original expression.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type 'a "lazy"} \\
  @{define_ML Lazy.lazy: "(unit -> 'a) -> 'a lazy"} \\
  @{define_ML Lazy.value: "'a -> 'a lazy"} \\
  @{define_ML Lazy.force: "'a lazy -> 'a"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>'a lazy\<close> represents lazy values over type \<^verbatim>\<open>'a\<close>.

  \<^descr> \<^ML>\<open>Lazy.lazy\<close>~\<open>(fn () => e)\<close> wraps the unevaluated expression \<open>e\<close> as
  unfinished lazy value.

  \<^descr> \<^ML>\<open>Lazy.value\<close>~\<open>a\<close> wraps the value \<open>a\<close> as finished lazy value. When
  forced, it returns \<open>a\<close> without any further evaluation.

  There is very low overhead for this proforma wrapping of strict values as
  lazy values.

  \<^descr> \<^ML>\<open>Lazy.force\<close>~\<open>x\<close> produces the result of the lazy value in a
  thread-safe manner as explained above. Thus it may cause the current thread
  to wait on a pending evaluation attempt by another thread.
\<close>


subsection \<open>Futures \label{sec:futures}\<close>

text \<open>
  Futures help to organize parallel execution in a value-oriented manner, with
  \<open>fork\<close>~/ \<open>join\<close> as the main pair of operations, and some further variants;
  see also @{cite "Wenzel:2009" and "Wenzel:2013:ITP"}. Unlike lazy values,
  futures are evaluated strictly and spontaneously on separate worker threads.
  Futures may be canceled, which leads to interrupts on running evaluation
  attempts, and forces structurally related futures to fail for all time;
  already finished futures remain unchanged. Exceptions between related
  futures are propagated as well, and turned into parallel exceptions (see
  above).

  Technically, a future is a single-assignment variable together with a
  \<^emph>\<open>task\<close> that serves administrative purposes, notably within the \<^emph>\<open>task
  queue\<close> where new futures are registered for eventual evaluation and the
  worker threads retrieve their work.

  The pool of worker threads is limited, in correlation with the number of
  physical cores on the machine. Note that allocation of runtime resources may
  be distorted either if workers yield CPU time (e.g.\ via system sleep or
  wait operations), or if non-worker threads contend for significant runtime
  resources independently. There is a limited number of replacement worker
  threads that get activated in certain explicit wait conditions, after a
  timeout.

  \<^medskip>
  Each future task belongs to some \<^emph>\<open>task group\<close>, which represents the
  hierarchic structure of related tasks, together with the exception status a
  that point. By default, the task group of a newly created future is a new
  sub-group of the presently running one, but it is also possible to indicate
  different group layouts under program control.

  Cancellation of futures actually refers to the corresponding task group and
  all its sub-groups. Thus interrupts are propagated down the group hierarchy.
  Regular program exceptions are treated likewise: failure of the evaluation
  of some future task affects its own group and all sub-groups. Given a
  particular task group, its \<^emph>\<open>group status\<close> cumulates all relevant exceptions
  according to its position within the group hierarchy. Interrupted tasks that
  lack regular result information, will pick up parallel exceptions from the
  cumulative group status.

  \<^medskip>
  A \<^emph>\<open>passive future\<close> or \<^emph>\<open>promise\<close> is a future with slightly different
  evaluation policies: there is only a single-assignment variable and some
  expression to evaluate for the \<^emph>\<open>failed\<close> case (e.g.\ to clean up resources
  when canceled). A regular result is produced by external means, using a
  separate \<^emph>\<open>fulfill\<close> operation.

  Promises are managed in the same task queue, so regular futures may depend
  on them. This allows a form of reactive programming, where some promises are
  used as minimal elements (or guards) within the future dependency graph:
  when these promises are fulfilled the evaluation of subsequent futures
  starts spontaneously, according to their own inter-dependencies.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type 'a "future"} \\
  @{define_ML Future.fork: "(unit -> 'a) -> 'a future"} \\
  @{define_ML Future.forks: "Future.params -> (unit -> 'a) list -> 'a future list"} \\
  @{define_ML Future.join: "'a future -> 'a"} \\
  @{define_ML Future.joins: "'a future list -> 'a list"} \\
  @{define_ML Future.value: "'a -> 'a future"} \\
  @{define_ML Future.map: "('a -> 'b) -> 'a future -> 'b future"} \\
  @{define_ML Future.cancel: "'a future -> unit"} \\
  @{define_ML Future.cancel_group: "Future.group -> unit"} \\[0.5ex]
  @{define_ML Future.promise: "(unit -> unit) -> 'a future"} \\
  @{define_ML Future.fulfill: "'a future -> 'a -> unit"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>'a future\<close> represents future values over type \<^verbatim>\<open>'a\<close>.

  \<^descr> \<^ML>\<open>Future.fork\<close>~\<open>(fn () => e)\<close> registers the unevaluated expression \<open>e\<close>
  as unfinished future value, to be evaluated eventually on the parallel
  worker-thread farm. This is a shorthand for \<^ML>\<open>Future.forks\<close> below, with
  default parameters and a single expression.

  \<^descr> \<^ML>\<open>Future.forks\<close>~\<open>params exprs\<close> is the general interface to fork several
  futures simultaneously. The \<open>params\<close> consist of the following fields:

    \<^item> \<open>name : string\<close> (default \<^ML>\<open>""\<close>) specifies a common name for the
    tasks of the forked futures, which serves diagnostic purposes.

    \<^item> \<open>group : Future.group option\<close> (default \<^ML>\<open>NONE\<close>) specifies an optional
    task group for the forked futures. \<^ML>\<open>NONE\<close> means that a new sub-group
    of the current worker-thread task context is created. If this is not a
    worker thread, the group will be a new root in the group hierarchy.

    \<^item> \<open>deps : Future.task list\<close> (default \<^ML>\<open>[]\<close>) specifies dependencies on
    other future tasks, i.e.\ the adjacency relation in the global task queue.
    Dependencies on already finished tasks are ignored.

    \<^item> \<open>pri : int\<close> (default \<^ML>\<open>0\<close>) specifies a priority within the task
    queue.

    Typically there is only little deviation from the default priority \<^ML>\<open>0\<close>. As a rule of thumb, \<^ML>\<open>~1\<close> means ``low priority" and \<^ML>\<open>1\<close> means
    ``high priority''.

    Note that the task priority only affects the position in the queue, not
    the thread priority. When a worker thread picks up a task for processing,
    it runs with the normal thread priority to the end (or until canceled).
    Higher priority tasks that are queued later need to wait until this (or
    another) worker thread becomes free again.

    \<^item> \<open>interrupts : bool\<close> (default \<^ML>\<open>true\<close>) tells whether the worker thread
    that processes the corresponding task is initially put into interruptible
    state. This state may change again while running, by modifying the thread
    attributes.

    With interrupts disabled, a running future task cannot be canceled. It is
    the responsibility of the programmer that this special state is retained
    only briefly.

  \<^descr> \<^ML>\<open>Future.join\<close>~\<open>x\<close> retrieves the value of an already finished future,
  which may lead to an exception, according to the result of its previous
  evaluation.

  For an unfinished future there are several cases depending on the role of
  the current thread and the status of the future. A non-worker thread waits
  passively until the future is eventually evaluated. A worker thread
  temporarily changes its task context and takes over the responsibility to
  evaluate the future expression on the spot. The latter is done in a
  thread-safe manner: other threads that intend to join the same future need
  to wait until the ongoing evaluation is finished.

  Note that excessive use of dynamic dependencies of futures by adhoc joining
  may lead to bad utilization of CPU cores, due to threads waiting on other
  threads to finish required futures. The future task farm has a limited
  amount of replacement threads that continue working on unrelated tasks after
  some timeout.

  Whenever possible, static dependencies of futures should be specified
  explicitly when forked (see \<open>deps\<close> above). Thus the evaluation can work from
  the bottom up, without join conflicts and wait states.

  \<^descr> \<^ML>\<open>Future.joins\<close>~\<open>xs\<close> joins the given list of futures simultaneously,
  which is more efficient than \<^ML>\<open>map Future.join\<close>~\<open>xs\<close>.

  Based on the dependency graph of tasks, the current thread takes over the
  responsibility to evaluate future expressions that are required for the main
  result, working from the bottom up. Waiting on future results that are
  presently evaluated on other threads only happens as last resort, when no
  other unfinished futures are left over.

  \<^descr> \<^ML>\<open>Future.value\<close>~\<open>a\<close> wraps the value \<open>a\<close> as finished future value,
  bypassing the worker-thread farm. When joined, it returns \<open>a\<close> without any
  further evaluation.

  There is very low overhead for this proforma wrapping of strict values as
  futures.

  \<^descr> \<^ML>\<open>Future.map\<close>~\<open>f x\<close> is a fast-path implementation of \<^ML>\<open>Future.fork\<close>~\<open>(fn () => f (\<close>\<^ML>\<open>Future.join\<close>~\<open>x))\<close>, which avoids the full
  overhead of the task queue and worker-thread farm as far as possible. The
  function \<open>f\<close> is supposed to be some trivial post-processing or projection of
  the future result.

  \<^descr> \<^ML>\<open>Future.cancel\<close>~\<open>x\<close> cancels the task group of the given future, using
  \<^ML>\<open>Future.cancel_group\<close> below.

  \<^descr> \<^ML>\<open>Future.cancel_group\<close>~\<open>group\<close> cancels all tasks of the given task
  group for all time. Threads that are presently processing a task of the
  given group are interrupted: it may take some time until they are actually
  terminated. Tasks that are queued but not yet processed are dequeued and
  forced into interrupted state. Since the task group is itself invalidated,
  any further attempt to fork a future that belongs to it will yield a
  canceled result as well.

  \<^descr> \<^ML>\<open>Future.promise\<close>~\<open>abort\<close> registers a passive future with the given
  \<open>abort\<close> operation: it is invoked when the future task group is canceled.

  \<^descr> \<^ML>\<open>Future.fulfill\<close>~\<open>x a\<close> finishes the passive future \<open>x\<close> by the given
  value \<open>a\<close>. If the promise has already been canceled, the attempt to fulfill
  it causes an exception.
\<close>

end
