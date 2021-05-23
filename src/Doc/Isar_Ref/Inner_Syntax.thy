(*:maxLineLen=78:*)

theory Inner_Syntax
  imports Main Base
begin

chapter \<open>Inner syntax --- the term language \label{ch:inner-syntax}\<close>

text \<open>
  The inner syntax of Isabelle provides concrete notation for the main
  entities of the logical framework, notably \<open>\<lambda>\<close>-terms with types and type
  classes. Applications may either extend existing syntactic categories by
  additional notation, or define new sub-languages that are linked to the
  standard term language via some explicit markers. For example \<^verbatim>\<open>FOO\<close>~\<open>foo\<close>
  could embed the syntax corresponding for some user-defined nonterminal \<open>foo\<close>
  --- within the bounds of the given lexical syntax of Isabelle/Pure.

  The most basic way to specify concrete syntax for logical entities works via
  mixfix annotations (\secref{sec:mixfix}), which may be usually given as part
  of the original declaration or via explicit notation commands later on
  (\secref{sec:notation}). This already covers many needs of concrete syntax
  without having to understand the full complexity of inner syntax layers.

  Further details of the syntax engine involves the classical distinction of
  lexical language versus context-free grammar (see \secref{sec:pure-syntax}),
  and various mechanisms for \<^emph>\<open>syntax transformations\<close> (see
  \secref{sec:syntax-transformations}).
\<close>


section \<open>Printing logical entities\<close>

subsection \<open>Diagnostic commands \label{sec:print-diag}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "typ"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "term"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "prop"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "thm"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "prf"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "full_prf"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{command_def "print_state"}\<open>\<^sup>*\<close> & : & \<open>any \<rightarrow>\<close> \\
  \end{matharray}

  These diagnostic commands assist interactive development by printing
  internal logical entities in a human-readable fashion.

  \<^rail>\<open>
    @@{command typ} @{syntax modes}? @{syntax type} ('::' @{syntax sort})?
    ;
    @@{command term} @{syntax modes}? @{syntax term}
    ;
    @@{command prop} @{syntax modes}? @{syntax prop}
    ;
    @@{command thm} @{syntax modes}? @{syntax thms}
    ;
    ( @@{command prf} | @@{command full_prf} ) @{syntax modes}? @{syntax thms}?
    ;
    @@{command print_state} @{syntax modes}?
    ;
    @{syntax_def modes}: '(' (@{syntax name} + ) ')'
  \<close>

  \<^descr> @{command "typ"}~\<open>\<tau>\<close> reads and prints a type expression according to the
  current context.

  \<^descr> @{command "typ"}~\<open>\<tau> :: s\<close> uses type-inference to determine the most
  general way to make \<open>\<tau>\<close> conform to sort \<open>s\<close>. For concrete \<open>\<tau>\<close> this checks if
  the type belongs to that sort. Dummy type parameters ``\<open>_\<close>'' (underscore)
  are assigned to fresh type variables with most general sorts, according the
  the principles of type-inference.

    \<^descr> @{command "term"}~\<open>t\<close> and @{command "prop"}~\<open>\<phi>\<close> read, type-check and
    print terms or propositions according to the current theory or proof
    context; the inferred type of \<open>t\<close> is output as well. Note that these
    commands are also useful in inspecting the current environment of term
    abbreviations.

    \<^descr> @{command "thm"}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> retrieves theorems from the current theory
    or proof context. Note that any attributes included in the theorem
    specifications are applied to a temporary context derived from the current
    theory or proof; the result is discarded, i.e.\ attributes involved in
    \<open>a\<^sub>1, \<dots>, a\<^sub>n\<close> do not have any permanent effect.

    \<^descr> @{command "prf"} displays the (compact) proof term of the current proof
    state (if present), or of the given theorems. Note that this requires an
    underlying logic image with proof terms enabled, e.g. \<open>HOL-Proofs\<close>.

    \<^descr> @{command "full_prf"} is like @{command "prf"}, but displays the full
    proof term, i.e.\ also displays information omitted in the compact proof
    term, which is denoted by ``\<open>_\<close>'' placeholders there.

    \<^descr> @{command "print_state"} prints the current proof state (if present),
    including current facts and goals.

  All of the diagnostic commands above admit a list of \<open>modes\<close> to be
  specified, which is appended to the current print mode; see also
  \secref{sec:print-modes}. Thus the output behavior may be modified according
  particular print mode features. For example, @{command
  "print_state"}~\<open>(latex)\<close> prints the current proof state with mathematical
  symbols and special characters represented in {\LaTeX} source, according to
  the Isabelle style @{cite "isabelle-system"}.

  Note that antiquotations (cf.\ \secref{sec:antiq}) provide a more systematic
  way to include formal items into the printed text document.
\<close>


subsection \<open>Details of printed content\<close>

text \<open>
  \begin{tabular}{rcll}
    @{attribute_def show_markup} & : & \<open>attribute\<close> \\
    @{attribute_def show_types} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def show_sorts} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def show_consts} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def show_abbrevs} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def show_brackets} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def names_long} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def names_short} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def names_unique} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def eta_contract} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def goals_limit} & : & \<open>attribute\<close> & default \<open>10\<close> \\
    @{attribute_def show_main_goal} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def show_hyps} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def show_tags} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def show_question_marks} & : & \<open>attribute\<close> & default \<open>true\<close> \\
  \end{tabular}
  \<^medskip>

  These configuration options control the detail of information that is
  displayed for types, terms, theorems, goals etc. See also
  \secref{sec:config}.

  \<^descr> @{attribute show_markup} controls direct inlining of markup into the
  printed representation of formal entities --- notably type and sort
  constraints. This enables Prover IDE users to retrieve that information via
  tooltips or popups while hovering with the mouse over the output window, for
  example. Consequently, this option is enabled by default for Isabelle/jEdit.

  \<^descr> @{attribute show_types} and @{attribute show_sorts} control printing of
  type constraints for term variables, and sort constraints for type
  variables. By default, neither of these are shown in output. If @{attribute
  show_sorts} is enabled, types are always shown as well. In Isabelle/jEdit,
  manual setting of these options is normally not required thanks to
  @{attribute show_markup} above.

  Note that displaying types and sorts may explain why a polymorphic inference
  rule fails to resolve with some goal, or why a rewrite rule does not apply
  as expected.

  \<^descr> @{attribute show_consts} controls printing of types of constants when
  displaying a goal state.

  Note that the output can be enormous, because polymorphic constants often
  occur at several different type instances.

  \<^descr> @{attribute show_abbrevs} controls folding of constant abbreviations.

  \<^descr> @{attribute show_brackets} controls bracketing in pretty printed output.
  If enabled, all sub-expressions of the pretty printing tree will be
  parenthesized, even if this produces malformed term syntax! This crude way
  of showing the internal structure of pretty printed entities may
  occasionally help to diagnose problems with operator priorities, for
  example.

  \<^descr> @{attribute names_long}, @{attribute names_short}, and @{attribute
  names_unique} control the way of printing fully qualified internal names in
  external form. See also \secref{sec:antiq} for the document antiquotation
  options of the same names.

  \<^descr> @{attribute eta_contract} controls \<open>\<eta>\<close>-contracted printing of terms.

  The \<open>\<eta>\<close>-contraction law asserts \<^prop>\<open>(\<lambda>x. f x) \<equiv> f\<close>, provided \<open>x\<close> is not
  free in \<open>f\<close>. It asserts \<^emph>\<open>extensionality\<close> of functions: \<^prop>\<open>f \<equiv> g\<close> if
  \<^prop>\<open>f x \<equiv> g x\<close> for all \<open>x\<close>. Higher-order unification frequently puts
  terms into a fully \<open>\<eta>\<close>-expanded form. For example, if \<open>F\<close> has type \<open>(\<tau> \<Rightarrow> \<tau>)
  \<Rightarrow> \<tau>\<close> then its expanded form is \<^term>\<open>\<lambda>h. F (\<lambda>x. h x)\<close>.

  Enabling @{attribute eta_contract} makes Isabelle perform \<open>\<eta>\<close>-contractions
  before printing, so that \<^term>\<open>\<lambda>h. F (\<lambda>x. h x)\<close> appears simply as \<open>F\<close>.

  Note that the distinction between a term and its \<open>\<eta>\<close>-expanded form
  occasionally matters. While higher-order resolution and rewriting operate
  modulo \<open>\<alpha>\<beta>\<eta>\<close>-conversion, some other tools might look at terms more
  discretely.

  \<^descr> @{attribute goals_limit} controls the maximum number of subgoals to be
  printed.

  \<^descr> @{attribute show_main_goal} controls whether the main result to be proven
  should be displayed. This information might be relevant for schematic goals,
  to inspect the current claim that has been synthesized so far.

  \<^descr> @{attribute show_hyps} controls printing of implicit hypotheses of local
  facts. Normally, only those hypotheses are displayed that are \<^emph>\<open>not\<close> covered
  by the assumptions of the current context: this situation indicates a fault
  in some tool being used.

  By enabling @{attribute show_hyps}, output of \<^emph>\<open>all\<close> hypotheses can be
  enforced, which is occasionally useful for diagnostic purposes.

  \<^descr> @{attribute show_tags} controls printing of extra annotations within
  theorems, such as internal position information, or the case names being
  attached by the attribute @{attribute case_names}.

  Note that the @{attribute tagged} and @{attribute untagged} attributes
  provide low-level access to the collection of tags associated with a
  theorem.

  \<^descr> @{attribute show_question_marks} controls printing of question marks for
  schematic variables, such as \<open>?x\<close>. Only the leading question mark is
  affected, the remaining text is unchanged (including proper markup for
  schematic variables that might be relevant for user interfaces).
\<close>


subsection \<open>Alternative print modes \label{sec:print-modes}\<close>

text \<open>
  \begin{mldecls}
    @{define_ML print_mode_value: "unit -> string list"} \\
    @{define_ML Print_Mode.with_modes: "string list -> ('a -> 'b) -> 'a -> 'b"} \\
  \end{mldecls}

  The \<^emph>\<open>print mode\<close> facility allows to modify various operations for printing.
  Commands like @{command typ}, @{command term}, @{command thm} (see
  \secref{sec:print-diag}) take additional print modes as optional argument.
  The underlying ML operations are as follows.

    \<^descr> \<^ML>\<open>print_mode_value ()\<close> yields the list of currently active print
    mode names. This should be understood as symbolic representation of
    certain individual features for printing (with precedence from left to
    right).

    \<^descr> \<^ML>\<open>Print_Mode.with_modes\<close>~\<open>modes f x\<close> evaluates \<open>f x\<close> in an execution
    context where the print mode is prepended by the given \<open>modes\<close>. This
    provides a thread-safe way to augment print modes. It is also monotonic in
    the set of mode names: it retains the default print mode that certain
    user-interfaces might have installed for their proper functioning!

  \<^medskip>
  The pretty printer for inner syntax maintains alternative mixfix productions
  for any print mode name invented by the user, say in commands like @{command
  notation} or @{command abbreviation}. Mode names can be arbitrary, but the
  following ones have a specific meaning by convention:

    \<^item> \<^verbatim>\<open>""\<close> (the empty string): default mode; implicitly active as last
    element in the list of modes.

    \<^item> \<^verbatim>\<open>input\<close>: dummy print mode that is never active; may be used to specify
    notation that is only available for input.

    \<^item> \<^verbatim>\<open>internal\<close> dummy print mode that is never active; used internally in
    Isabelle/Pure.

    \<^item> \<^verbatim>\<open>ASCII\<close>: prefer ASCII art over mathematical symbols.

    \<^item> \<^verbatim>\<open>latex\<close>: additional mode that is active in {\LaTeX} document
    preparation of Isabelle theory sources; allows to provide alternative
    output notation.
\<close>


section \<open>Mixfix annotations \label{sec:mixfix}\<close>

text \<open>
  Mixfix annotations specify concrete \<^emph>\<open>inner syntax\<close> of Isabelle types and
  terms. Locally fixed parameters in toplevel theorem statements, locale and
  class specifications also admit mixfix annotations in a fairly uniform
  manner. A mixfix annotation describes the concrete syntax, the translation
  to abstract syntax, and the pretty printing. Special case annotations
  provide a simple means of specifying infix operators and binders.

  Isabelle mixfix syntax is inspired by {\OBJ} @{cite OBJ}. It allows to
  specify any context-free priority grammar, which is more general than the
  fixity declarations of ML and Prolog.

  \<^rail>\<open>
    @{syntax_def mixfix}: '('
      (@{syntax template} prios? @{syntax nat}? |
        (@'infix' | @'infixl' | @'infixr') @{syntax template} @{syntax nat} |
        @'binder' @{syntax template} prio? @{syntax nat} |
        @'structure') ')'
    ;
    @{syntax template}: (string | cartouche)
    ;
    prios: '[' (@{syntax nat} + ',') ']'
    ;
    prio: '[' @{syntax nat} ']'
  \<close>

  The mixfix \<open>template\<close> may include literal text, spacing, blocks, and
  arguments (denoted by ``\<open>_\<close>''); the special symbol ``\<^verbatim>\<open>\<index>\<close>'' (printed as
  ``\<open>\<index>\<close>'') represents an index argument that specifies an implicit @{keyword
  "structure"} reference (see also \secref{sec:locale}). Only locally fixed
  variables may be declared as @{keyword "structure"}.

  Infix and binder declarations provide common abbreviations for particular
  mixfix declarations. So in practice, mixfix templates mostly degenerate to
  literal text for concrete syntax, such as ``\<^verbatim>\<open>++\<close>'' for an infix symbol.
\<close>


subsection \<open>The general mixfix form\<close>

text \<open>
  In full generality, mixfix declarations work as follows. Suppose a constant
  \<open>c :: \<tau>\<^sub>1 \<Rightarrow> \<dots> \<tau>\<^sub>n \<Rightarrow> \<tau>\<close> is annotated by \<open>(mixfix [p\<^sub>1, \<dots>, p\<^sub>n] p)\<close>, where
  \<open>mixfix\<close> is a string \<open>d\<^sub>0 _ d\<^sub>1 _ \<dots> _ d\<^sub>n\<close> consisting of delimiters that
  surround argument positions as indicated by underscores.

  Altogether this determines a production for a context-free priority grammar,
  where for each argument \<open>i\<close> the syntactic category is determined by \<open>\<tau>\<^sub>i\<close>
  (with priority \<open>p\<^sub>i\<close>), and the result category is determined from \<open>\<tau>\<close> (with
  priority \<open>p\<close>). Priority specifications are optional, with default 0 for
  arguments and 1000 for the result.\<^footnote>\<open>Omitting priorities is prone to
  syntactic ambiguities unless the delimiter tokens determine fully bracketed
  notation, as in \<open>if _ then _ else _ fi\<close>.\<close>

  Since \<open>\<tau>\<close> may be again a function type, the constant type scheme may have
  more argument positions than the mixfix pattern. Printing a nested
  application \<open>c t\<^sub>1 \<dots> t\<^sub>m\<close> for \<open>m > n\<close> works by attaching concrete notation
  only to the innermost part, essentially by printing \<open>(c t\<^sub>1 \<dots> t\<^sub>n) \<dots> t\<^sub>m\<close>
  instead. If a term has fewer arguments than specified in the mixfix
  template, the concrete syntax is ignored.

  \<^medskip>
  A mixfix template may also contain additional directives for pretty
  printing, notably spaces, blocks, and breaks. The general template format is
  a sequence over any of the following entities.

  \<^descr> \<open>d\<close> is a delimiter, namely a non-empty sequence delimiter items of the
  following form:
    \<^enum> a control symbol followed by a cartouche
    \<^enum> a single symbol, excluding the following special characters:
      \<^medskip>
      \begin{tabular}{ll}
        \<^verbatim>\<open>'\<close> & single quote \\
        \<^verbatim>\<open>_\<close> & underscore \\
        \<open>\<index>\<close> & index symbol \\
        \<^verbatim>\<open>(\<close> & open parenthesis \\
        \<^verbatim>\<open>)\<close> & close parenthesis \\
        \<^verbatim>\<open>/\<close> & slash \\
        \<open>\<open> \<close>\<close> & cartouche delimiters \\
      \end{tabular}
      \<^medskip>

  \<^descr> \<^verbatim>\<open>'\<close> escapes the special meaning of these meta-characters, producing a
  literal version of the following character, unless that is a blank.

  A single quote followed by a blank separates delimiters, without affecting
  printing, but input tokens may have additional white space here.

  \<^descr> \<^verbatim>\<open>_\<close> is an argument position, which stands for a certain syntactic
  category in the underlying grammar.

  \<^descr> \<open>\<index>\<close> is an indexed argument position; this is the place where implicit
  structure arguments can be attached.

  \<^descr> \<open>s\<close> is a non-empty sequence of spaces for printing. This and the following
  specifications do not affect parsing at all.

  \<^descr> \<^verbatim>\<open>(\<close>\<open>n\<close> opens a pretty printing block. The optional natural number
  specifies the block indentation, i.e. how much spaces to add when a line
  break occurs within the block. The default indentation is 0.

  \<^descr> \<^verbatim>\<open>(\<close>\<open>\<open>properties\<close>\<close> opens a pretty printing block, with properties
  specified within the given text cartouche. The syntax and semantics of
  the category @{syntax_ref mixfix_properties} is described below.

  \<^descr> \<^verbatim>\<open>)\<close> closes a pretty printing block.

  \<^descr> \<^verbatim>\<open>//\<close> forces a line break.

  \<^descr> \<^verbatim>\<open>/\<close>\<open>s\<close> allows a line break. Here \<open>s\<close> stands for the string of spaces
  (zero or more) right after the slash. These spaces are printed if the break
  is \<^emph>\<open>not\<close> taken.


  \<^medskip>
  Block properties allow more control over the details of pretty-printed
  output. The concrete syntax is defined as follows.

  \<^rail>\<open>
    @{syntax_def "mixfix_properties"}: (entry *)
    ;
    entry: atom ('=' atom)?
    ;
    atom: @{syntax short_ident} | @{syntax int} | @{syntax float} | @{syntax cartouche}
  \<close>

  Each @{syntax entry} is a name-value pair: if the value is omitted, it
  defaults to \<^verbatim>\<open>true\<close> (intended for Boolean properties). The following
  standard block properties are supported:

    \<^item> \<open>indent\<close> (natural number): the block indentation --- the same as for the
    simple syntax without block properties.

    \<^item> \<open>consistent\<close> (Boolean): this block has consistent breaks (if one break
    is taken, all breaks are taken).

    \<^item> \<open>unbreakable\<close> (Boolean): all possible breaks of the block are disabled
    (turned into spaces).

    \<^item> \<open>markup\<close> (string): the optional name of the markup node. If this is
    provided, all remaining properties are turned into its XML attributes.
    This allows to specify free-form PIDE markup, e.g.\ for specialized
    output.

  \<^medskip>
  Note that the general idea of pretty printing with blocks and breaks is
  described in @{cite "paulson-ml2"}; it goes back to @{cite "Oppen:1980"}.
\<close>


subsection \<open>Infixes\<close>

text \<open>
  Infix operators are specified by convenient short forms that abbreviate
  general mixfix annotations as follows:

  \begin{center}
  \begin{tabular}{lll}

  \<^verbatim>\<open>(\<close>@{keyword_def "infix"}~\<^verbatim>\<open>"\<close>\<open>sy\<close>\<^verbatim>\<open>"\<close> \<open>p\<close>\<^verbatim>\<open>)\<close>
  & \<open>\<mapsto>\<close> &
  \<^verbatim>\<open>("(_\<close>~\<open>sy\<close>\<^verbatim>\<open>/ _)" [\<close>\<open>p + 1\<close>\<^verbatim>\<open>,\<close>~\<open>p + 1\<close>\<^verbatim>\<open>]\<close>~\<open>p\<close>\<^verbatim>\<open>)\<close> \\
  \<^verbatim>\<open>(\<close>@{keyword_def "infixl"}~\<^verbatim>\<open>"\<close>\<open>sy\<close>\<^verbatim>\<open>"\<close> \<open>p\<close>\<^verbatim>\<open>)\<close>
  & \<open>\<mapsto>\<close> &
  \<^verbatim>\<open>("(_\<close>~\<open>sy\<close>\<^verbatim>\<open>/ _)" [\<close>\<open>p\<close>\<^verbatim>\<open>,\<close>~\<open>p + 1\<close>\<^verbatim>\<open>]\<close>~\<open>p\<close>\<^verbatim>\<open>)\<close> \\
  \<^verbatim>\<open>(\<close>@{keyword_def "infixr"}~\<^verbatim>\<open>"\<close>\<open>sy\<close>\<^verbatim>\<open>"\<close>~\<open>p\<close>\<^verbatim>\<open>)\<close>
  & \<open>\<mapsto>\<close> &
  \<^verbatim>\<open>("(_\<close>~\<open>sy\<close>\<^verbatim>\<open>/ _)" [\<close>\<open>p + 1\<close>\<^verbatim>\<open>,\<close>~\<open>p\<close>\<^verbatim>\<open>]\<close>~\<open>p\<close>\<^verbatim>\<open>)\<close> \\

  \end{tabular}
  \end{center}

  The mixfix template \<^verbatim>\<open>"(_\<close>~\<open>sy\<close>\<^verbatim>\<open>/ _)"\<close> specifies two argument positions;
  the delimiter is preceded by a space and followed by a space or line break;
  the entire phrase is a pretty printing block.

  The alternative notation \<^verbatim>\<open>(\<close>\<open>sy\<close>\<^verbatim>\<open>)\<close> is introduced in addition. Thus any
  infix operator may be written in prefix form (as in Haskell), independently of
  the number of arguments.
\<close>


subsection \<open>Binders\<close>

text \<open>
  A \<^emph>\<open>binder\<close> is a variable-binding construct such as a quantifier. The idea
  to formalize \<open>\<forall>x. b\<close> as \<open>All (\<lambda>x. b)\<close> for \<open>All :: ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  already goes back to @{cite church40}. Isabelle declarations of certain
  higher-order operators may be annotated with @{keyword_def "binder"}
  annotations as follows:

  \begin{center}
  \<open>c ::\<close>~\<^verbatim>\<open>"\<close>\<open>(\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2) \<Rightarrow> \<tau>\<^sub>3\<close>\<^verbatim>\<open>"  (\<close>@{keyword "binder"}~\<^verbatim>\<open>"\<close>\<open>sy\<close>\<^verbatim>\<open>" [\<close>\<open>p\<close>\<^verbatim>\<open>]\<close>~\<open>q\<close>\<^verbatim>\<open>)\<close>
  \end{center}

  This introduces concrete binder syntax \<open>sy x. b\<close>, where \<open>x\<close> is a bound
  variable of type \<open>\<tau>\<^sub>1\<close>, the body \<open>b\<close> has type \<open>\<tau>\<^sub>2\<close> and the whole term has
  type \<open>\<tau>\<^sub>3\<close>. The optional integer \<open>p\<close> specifies the syntactic priority of the
  body; the default is \<open>q\<close>, which is also the priority of the whole construct.

  Internally, the binder syntax is expanded to something like this:
  \begin{center}
  \<open>c_binder ::\<close>~\<^verbatim>\<open>"\<close>\<open>idts \<Rightarrow> \<tau>\<^sub>2 \<Rightarrow> \<tau>\<^sub>3\<close>\<^verbatim>\<open>"  ("(3\<close>\<open>sy\<close>\<^verbatim>\<open>_./ _)" [0,\<close>~\<open>p\<close>\<^verbatim>\<open>]\<close>~\<open>q\<close>\<^verbatim>\<open>)\<close>
  \end{center}

  Here @{syntax (inner) idts} is the nonterminal symbol for a list of
  identifiers with optional type constraints (see also
  \secref{sec:pure-grammar}). The mixfix template \<^verbatim>\<open>"(3\<close>\<open>sy\<close>\<^verbatim>\<open>_./ _)"\<close> defines
  argument positions for the bound identifiers and the body, separated by a
  dot with optional line break; the entire phrase is a pretty printing block
  of indentation level 3. Note that there is no extra space after \<open>sy\<close>, so it
  needs to be included user specification if the binder syntax ends with a
  token that may be continued by an identifier token at the start of @{syntax
  (inner) idts}.

  Furthermore, a syntax translation to transforms \<open>c_binder x\<^sub>1 \<dots> x\<^sub>n b\<close> into
  iterated application \<open>c (\<lambda>x\<^sub>1. \<dots> c (\<lambda>x\<^sub>n. b)\<dots>)\<close>. This works in both
  directions, for parsing and printing.
\<close>


section \<open>Explicit notation \label{sec:notation}\<close>

text \<open>
  \begin{matharray}{rcll}
    @{command_def "type_notation"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "no_type_notation"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "notation"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "no_notation"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "write"} & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
  \end{matharray}

  Commands that introduce new logical entities (terms or types) usually allow
  to provide mixfix annotations on the spot, which is convenient for default
  notation. Nonetheless, the syntax may be modified later on by declarations
  for explicit notation. This allows to add or delete mixfix annotations for
  of existing logical entities within the current context.

  \<^rail>\<open>
    (@@{command type_notation} | @@{command no_type_notation}) @{syntax mode}? \<newline>
      (@{syntax name} @{syntax mixfix} + @'and')
    ;
    (@@{command notation} | @@{command no_notation}) @{syntax mode}? \<newline>
      (@{syntax name} @{syntax mixfix} + @'and')
    ;
    @@{command write} @{syntax mode}? (@{syntax name} @{syntax mixfix} + @'and')
  \<close>

  \<^descr> @{command "type_notation"}~\<open>c (mx)\<close> associates mixfix syntax with an
  existing type constructor. The arity of the constructor is retrieved from
  the context.

  \<^descr> @{command "no_type_notation"} is similar to @{command "type_notation"},
  but removes the specified syntax annotation from the present context.

  \<^descr> @{command "notation"}~\<open>c (mx)\<close> associates mixfix syntax with an existing
  constant or fixed variable. The type declaration of the given entity is
  retrieved from the context.

  \<^descr> @{command "no_notation"} is similar to @{command "notation"}, but removes
  the specified syntax annotation from the present context.

  \<^descr> @{command "write"} is similar to @{command "notation"}, but works within
  an Isar proof body.
\<close>


section \<open>The Pure syntax \label{sec:pure-syntax}\<close>

subsection \<open>Lexical matters \label{sec:inner-lex}\<close>

text \<open>
  The inner lexical syntax vaguely resembles the outer one
  (\secref{sec:outer-lex}), but some details are different. There are two main
  categories of inner syntax tokens:

  \<^enum> \<^emph>\<open>delimiters\<close> --- the literal tokens occurring in productions of the given
  priority grammar (cf.\ \secref{sec:priority-grammar});

  \<^enum> \<^emph>\<open>named tokens\<close> --- various categories of identifiers etc.


  Delimiters override named tokens and may thus render certain identifiers
  inaccessible. Sometimes the logical context admits alternative ways to refer
  to the same entity, potentially via qualified names.

  \<^medskip>
  The categories for named tokens are defined once and for all as follows,
  reusing some categories of the outer token syntax (\secref{sec:outer-lex}).

  \begin{center}
  \begin{supertabular}{rcl}
    @{syntax_def (inner) id} & = & @{syntax_ref short_ident} \\
    @{syntax_def (inner) longid} & = & @{syntax_ref long_ident} \\
    @{syntax_def (inner) var} & = & @{syntax_ref var} \\
    @{syntax_def (inner) tid} & = & @{syntax_ref type_ident} \\
    @{syntax_def (inner) tvar} & = & @{syntax_ref type_var} \\
    @{syntax_def (inner) num_token} & = & @{syntax_ref nat} \\
    @{syntax_def (inner) float_token} & = & @{syntax_ref nat}\<^verbatim>\<open>.\<close>@{syntax_ref nat} \\
    @{syntax_def (inner) str_token} & = & \<^verbatim>\<open>''\<close> \<open>\<dots>\<close> \<^verbatim>\<open>''\<close> \\
    @{syntax_def (inner) string_token} & = & \<^verbatim>\<open>"\<close> \<open>\<dots>\<close> \<^verbatim>\<open>"\<close> \\
    @{syntax_def (inner) cartouche} & = & \<^verbatim>\<open>\<open>\<close> \<open>\<dots>\<close> \<^verbatim>\<open>\<close>\<close> \\
  \end{supertabular}
  \end{center}

  The token categories @{syntax (inner) num_token}, @{syntax (inner)
  float_token}, @{syntax (inner) str_token}, @{syntax (inner) string_token},
  and @{syntax (inner) cartouche} are not used in Pure. Object-logics may
  implement numerals and string literals by adding appropriate syntax
  declarations, together with some translation functions (e.g.\ see
  \<^file>\<open>~~/src/HOL/Tools/string_syntax.ML\<close>).

  The derived categories @{syntax_def (inner) num_const}, and @{syntax_def
  (inner) float_const}, provide robust access to the respective tokens: the
  syntax tree holds a syntactic constant instead of a free variable.

  Formal document comments (\secref{sec:comments}) may be also used within the
  inner syntax.
\<close>


subsection \<open>Priority grammars \label{sec:priority-grammar}\<close>

text \<open>
  A context-free grammar consists of a set of \<^emph>\<open>terminal symbols\<close>, a set of
  \<^emph>\<open>nonterminal symbols\<close> and a set of \<^emph>\<open>productions\<close>. Productions have the
  form \<open>A = \<gamma>\<close>, where \<open>A\<close> is a nonterminal and \<open>\<gamma>\<close> is a string of terminals
  and nonterminals. One designated nonterminal is called the \<^emph>\<open>root symbol\<close>.
  The language defined by the grammar consists of all strings of terminals
  that can be derived from the root symbol by applying productions as rewrite
  rules.

  The standard Isabelle parser for inner syntax uses a \<^emph>\<open>priority grammar\<close>.
  Each nonterminal is decorated by an integer priority: \<open>A\<^sup>(\<^sup>p\<^sup>)\<close>. In a
  derivation, \<open>A\<^sup>(\<^sup>p\<^sup>)\<close> may be rewritten using a production \<open>A\<^sup>(\<^sup>q\<^sup>) = \<gamma>\<close> only
  if \<open>p \<le> q\<close>. Any priority grammar can be translated into a normal
  context-free grammar by introducing new nonterminals and productions.

  \<^medskip>
  Formally, a set of context free productions \<open>G\<close> induces a derivation
  relation \<open>\<longrightarrow>\<^sub>G\<close> as follows. Let \<open>\<alpha>\<close> and \<open>\<beta>\<close> denote strings of terminal or
  nonterminal symbols. Then \<open>\<alpha> A\<^sup>(\<^sup>p\<^sup>) \<beta> \<longrightarrow>\<^sub>G \<alpha> \<gamma> \<beta>\<close> holds if and only if \<open>G\<close>
  contains some production \<open>A\<^sup>(\<^sup>q\<^sup>) = \<gamma>\<close> for \<open>p \<le> q\<close>.

  \<^medskip>
  The following grammar for arithmetic expressions demonstrates how binding
  power and associativity of operators can be enforced by priorities.

  \begin{center}
  \begin{tabular}{rclr}
  \<open>A\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)\<close> & \<open>=\<close> & \<^verbatim>\<open>(\<close> \<open>A\<^sup>(\<^sup>0\<^sup>)\<close> \<^verbatim>\<open>)\<close> \\
  \<open>A\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)\<close> & \<open>=\<close> & \<^verbatim>\<open>0\<close> \\
  \<open>A\<^sup>(\<^sup>0\<^sup>)\<close> & \<open>=\<close> & \<open>A\<^sup>(\<^sup>0\<^sup>)\<close> \<^verbatim>\<open>+\<close> \<open>A\<^sup>(\<^sup>1\<^sup>)\<close> \\
  \<open>A\<^sup>(\<^sup>2\<^sup>)\<close> & \<open>=\<close> & \<open>A\<^sup>(\<^sup>3\<^sup>)\<close> \<^verbatim>\<open>*\<close> \<open>A\<^sup>(\<^sup>2\<^sup>)\<close> \\
  \<open>A\<^sup>(\<^sup>3\<^sup>)\<close> & \<open>=\<close> & \<^verbatim>\<open>-\<close> \<open>A\<^sup>(\<^sup>3\<^sup>)\<close> \\
  \end{tabular}
  \end{center}
  The choice of priorities determines that \<^verbatim>\<open>-\<close> binds tighter than \<^verbatim>\<open>*\<close>, which
  binds tighter than \<^verbatim>\<open>+\<close>. Furthermore \<^verbatim>\<open>+\<close> associates to the left and \<^verbatim>\<open>*\<close> to
  the right.

  \<^medskip>
  For clarity, grammars obey these conventions:

    \<^item> All priorities must lie between 0 and 1000.

    \<^item> Priority 0 on the right-hand side and priority 1000 on the left-hand
    side may be omitted.

    \<^item> The production \<open>A\<^sup>(\<^sup>p\<^sup>) = \<alpha>\<close> is written as \<open>A = \<alpha> (p)\<close>, i.e.\ the
    priority of the left-hand side actually appears in a column on the far
    right.

    \<^item> Alternatives are separated by \<open>|\<close>.

    \<^item> Repetition is indicated by dots \<open>(\<dots>)\<close> in an informal but obvious way.

  Using these conventions, the example grammar specification above
  takes the form:
  \begin{center}
  \begin{tabular}{rclc}
    \<open>A\<close> & \<open>=\<close> & \<^verbatim>\<open>(\<close> \<open>A\<close> \<^verbatim>\<open>)\<close> \\
              & \<open>|\<close> & \<^verbatim>\<open>0\<close> & \qquad\qquad \\
              & \<open>|\<close> & \<open>A\<close> \<^verbatim>\<open>+\<close> \<open>A\<^sup>(\<^sup>1\<^sup>)\<close> & \<open>(0)\<close> \\
              & \<open>|\<close> & \<open>A\<^sup>(\<^sup>3\<^sup>)\<close> \<^verbatim>\<open>*\<close> \<open>A\<^sup>(\<^sup>2\<^sup>)\<close> & \<open>(2)\<close> \\
              & \<open>|\<close> & \<^verbatim>\<open>-\<close> \<open>A\<^sup>(\<^sup>3\<^sup>)\<close> & \<open>(3)\<close> \\
  \end{tabular}
  \end{center}
\<close>


subsection \<open>The Pure grammar \label{sec:pure-grammar}\<close>

text \<open>
  The priority grammar of the \<open>Pure\<close> theory is defined approximately like
  this:

  \begin{center}
  \begin{supertabular}{rclr}

  @{syntax_def (inner) any} & = & \<open>prop  |  logic\<close> \\\\

  @{syntax_def (inner) prop} & = & \<^verbatim>\<open>(\<close> \<open>prop\<close> \<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<open>prop\<^sup>(\<^sup>4\<^sup>)\<close> \<^verbatim>\<open>::\<close> \<open>type\<close> & \<open>(3)\<close> \\
    & \<open>|\<close> & \<open>any\<^sup>(\<^sup>3\<^sup>)\<close> \<^verbatim>\<open>==\<close> \<open>any\<^sup>(\<^sup>3\<^sup>)\<close> & \<open>(2)\<close> \\
    & \<open>|\<close> & \<open>any\<^sup>(\<^sup>3\<^sup>)\<close> \<open>\<equiv>\<close> \<open>any\<^sup>(\<^sup>3\<^sup>)\<close> & \<open>(2)\<close> \\
    & \<open>|\<close> & \<open>prop\<^sup>(\<^sup>3\<^sup>)\<close> \<^verbatim>\<open>&&&\<close> \<open>prop\<^sup>(\<^sup>2\<^sup>)\<close> & \<open>(2)\<close> \\
    & \<open>|\<close> & \<open>prop\<^sup>(\<^sup>2\<^sup>)\<close> \<^verbatim>\<open>==>\<close> \<open>prop\<^sup>(\<^sup>1\<^sup>)\<close> & \<open>(1)\<close> \\
    & \<open>|\<close> & \<open>prop\<^sup>(\<^sup>2\<^sup>)\<close> \<open>\<Longrightarrow>\<close> \<open>prop\<^sup>(\<^sup>1\<^sup>)\<close> & \<open>(1)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>[|\<close> \<open>prop\<close> \<^verbatim>\<open>;\<close> \<open>\<dots>\<close> \<^verbatim>\<open>;\<close> \<open>prop\<close> \<^verbatim>\<open>|]\<close> \<^verbatim>\<open>==>\<close> \<open>prop\<^sup>(\<^sup>1\<^sup>)\<close> & \<open>(1)\<close> \\
    & \<open>|\<close> & \<open>\<lbrakk>\<close> \<open>prop\<close> \<^verbatim>\<open>;\<close> \<open>\<dots>\<close> \<^verbatim>\<open>;\<close> \<open>prop\<close> \<open>\<rbrakk>\<close> \<open>\<Longrightarrow>\<close> \<open>prop\<^sup>(\<^sup>1\<^sup>)\<close> & \<open>(1)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>!!\<close> \<open>idts\<close> \<^verbatim>\<open>.\<close> \<open>prop\<close> & \<open>(0)\<close> \\
    & \<open>|\<close> & \<open>\<And>\<close> \<open>idts\<close> \<^verbatim>\<open>.\<close> \<open>prop\<close> & \<open>(0)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>OFCLASS\<close> \<^verbatim>\<open>(\<close> \<open>type\<close> \<^verbatim>\<open>,\<close> \<open>logic\<close> \<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>SORT_CONSTRAINT\<close> \<^verbatim>\<open>(\<close> \<open>type\<close> \<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>TERM\<close> \<open>logic\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>PROP\<close> \<open>aprop\<close> \\\\

  @{syntax_def (inner) aprop} & = & \<^verbatim>\<open>(\<close> \<open>aprop\<close> \<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<open>id  |  longid  |  var  |\<close>~~\<^verbatim>\<open>_\<close>~~\<open>|\<close>~~\<^verbatim>\<open>...\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>CONST\<close> \<open>id  |\<close>~~\<^verbatim>\<open>CONST\<close> \<open>longid\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>XCONST\<close> \<open>id  |\<close>~~\<^verbatim>\<open>XCONST\<close> \<open>longid\<close> \\
    & \<open>|\<close> & \<open>logic\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)  any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) \<dots> any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)\<close> & \<open>(999)\<close> \\\\

  @{syntax_def (inner) logic} & = & \<^verbatim>\<open>(\<close> \<open>logic\<close> \<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<open>logic\<^sup>(\<^sup>4\<^sup>)\<close> \<^verbatim>\<open>::\<close> \<open>type\<close> & \<open>(3)\<close> \\
    & \<open>|\<close> & \<open>id  |  longid  |  var  |\<close>~~\<^verbatim>\<open>_\<close>~~\<open>|\<close>~~\<^verbatim>\<open>...\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>CONST\<close> \<open>id  |\<close>~~\<^verbatim>\<open>CONST\<close> \<open>longid\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>XCONST\<close> \<open>id  |\<close>~~\<^verbatim>\<open>XCONST\<close> \<open>longid\<close> \\
    & \<open>|\<close> & \<open>logic\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)  any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) \<dots> any\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>)\<close> & \<open>(999)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>%\<close> \<open>pttrns\<close> \<^verbatim>\<open>.\<close> \<open>any\<^sup>(\<^sup>3\<^sup>)\<close> & \<open>(3)\<close> \\
    & \<open>|\<close> & \<open>\<lambda>\<close> \<open>pttrns\<close> \<^verbatim>\<open>.\<close> \<open>any\<^sup>(\<^sup>3\<^sup>)\<close> & \<open>(3)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>(==)\<close>~~\<open>|\<close>~~\<^verbatim>\<open>(\<close>\<open>\<equiv>\<close>\<^verbatim>\<open>)\<close>~~\<open>|\<close>~~\<^verbatim>\<open>(&&&)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>(==>)\<close>~~\<open>|\<close>~~\<^verbatim>\<open>(\<close>\<open>\<Longrightarrow>\<close>\<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>TYPE\<close> \<^verbatim>\<open>(\<close> \<open>type\<close> \<^verbatim>\<open>)\<close> \\\\

  @{syntax_def (inner) idt} & = & \<^verbatim>\<open>(\<close> \<open>idt\<close> \<^verbatim>\<open>)\<close>~~\<open>|  id  |\<close>~~\<^verbatim>\<open>_\<close> \\
    & \<open>|\<close> & \<open>id\<close> \<^verbatim>\<open>::\<close> \<open>type\<close> & \<open>(0)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>_\<close> \<^verbatim>\<open>::\<close> \<open>type\<close> & \<open>(0)\<close> \\\\

  @{syntax_def (inner) index} & = & \<^verbatim>\<open>\<^bsub>\<close> \<open>logic\<^sup>(\<^sup>0\<^sup>)\<close> \<^verbatim>\<open>\<^esub>\<close>~~\<open>|  |  \<index>\<close> \\\\

  @{syntax_def (inner) idts} & = & \<open>idt  |  idt\<^sup>(\<^sup>1\<^sup>) idts\<close> & \<open>(0)\<close> \\\\

  @{syntax_def (inner) pttrn} & = & \<open>idt\<close> \\\\

  @{syntax_def (inner) pttrns} & = & \<open>pttrn  |  pttrn\<^sup>(\<^sup>1\<^sup>) pttrns\<close> & \<open>(0)\<close> \\\\

  @{syntax_def (inner) type} & = & \<^verbatim>\<open>(\<close> \<open>type\<close> \<^verbatim>\<open>)\<close> \\
    & \<open>|\<close> & \<open>tid  |  tvar  |\<close>~~\<^verbatim>\<open>_\<close> \\
    & \<open>|\<close> & \<open>tid\<close> \<^verbatim>\<open>::\<close> \<open>sort  |  tvar\<close>~~\<^verbatim>\<open>::\<close> \<open>sort  |\<close>~~\<^verbatim>\<open>_\<close> \<^verbatim>\<open>::\<close> \<open>sort\<close> \\
    & \<open>|\<close> & \<open>type_name  |  type\<^sup>(\<^sup>1\<^sup>0\<^sup>0\<^sup>0\<^sup>) type_name\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>(\<close> \<open>type\<close> \<^verbatim>\<open>,\<close> \<open>\<dots>\<close> \<^verbatim>\<open>,\<close> \<open>type\<close> \<^verbatim>\<open>)\<close> \<open>type_name\<close> \\
    & \<open>|\<close> & \<open>type\<^sup>(\<^sup>1\<^sup>)\<close> \<^verbatim>\<open>=>\<close> \<open>type\<close> & \<open>(0)\<close> \\
    & \<open>|\<close> & \<open>type\<^sup>(\<^sup>1\<^sup>)\<close> \<open>\<Rightarrow>\<close> \<open>type\<close> & \<open>(0)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>[\<close> \<open>type\<close> \<^verbatim>\<open>,\<close> \<open>\<dots>\<close> \<^verbatim>\<open>,\<close> \<open>type\<close> \<^verbatim>\<open>]\<close> \<^verbatim>\<open>=>\<close> \<open>type\<close> & \<open>(0)\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>[\<close> \<open>type\<close> \<^verbatim>\<open>,\<close> \<open>\<dots>\<close> \<^verbatim>\<open>,\<close> \<open>type\<close> \<^verbatim>\<open>]\<close> \<open>\<Rightarrow>\<close> \<open>type\<close> & \<open>(0)\<close> \\
  @{syntax_def (inner) type_name} & = & \<open>id  |  longid\<close> \\\\

  @{syntax_def (inner) sort} & = & @{syntax class_name}~~\<open>|\<close>~~\<^verbatim>\<open>_\<close>~~\<open>|\<close>~~\<^verbatim>\<open>{}\<close> \\
    & \<open>|\<close> & \<^verbatim>\<open>{\<close> @{syntax class_name} \<^verbatim>\<open>,\<close> \<open>\<dots>\<close> \<^verbatim>\<open>,\<close> @{syntax class_name} \<^verbatim>\<open>}\<close> \\
  @{syntax_def (inner) class_name} & = & \<open>id  |  longid\<close> \\
  \end{supertabular}
  \end{center}

  \<^medskip>
  Here literal terminals are printed \<^verbatim>\<open>verbatim\<close>; see also
  \secref{sec:inner-lex} for further token categories of the inner syntax. The
  meaning of the nonterminals defined by the above grammar is as follows:

  \<^descr> @{syntax_ref (inner) any} denotes any term.

  \<^descr> @{syntax_ref (inner) prop} denotes meta-level propositions, which are
  terms of type \<^typ>\<open>prop\<close>. The syntax of such formulae of the meta-logic is
  carefully distinguished from usual conventions for object-logics. In
  particular, plain \<open>\<lambda>\<close>-term notation is \<^emph>\<open>not\<close> recognized as @{syntax (inner)
  prop}.

  \<^descr> @{syntax_ref (inner) aprop} denotes atomic propositions, which are
  embedded into regular @{syntax (inner) prop} by means of an explicit \<^verbatim>\<open>PROP\<close>
  token.

  Terms of type \<^typ>\<open>prop\<close> with non-constant head, e.g.\ a plain variable,
  are printed in this form. Constants that yield type \<^typ>\<open>prop\<close> are expected
  to provide their own concrete syntax; otherwise the printed version will
  appear like @{syntax (inner) logic} and cannot be parsed again as @{syntax
  (inner) prop}.

  \<^descr> @{syntax_ref (inner) logic} denotes arbitrary terms of a logical type,
  excluding type \<^typ>\<open>prop\<close>. This is the main syntactic category of
  object-logic entities, covering plain \<open>\<lambda>\<close>-term notation (variables,
  abstraction, application), plus anything defined by the user.

  When specifying notation for logical entities, all logical types (excluding
  \<^typ>\<open>prop\<close>) are \<^emph>\<open>collapsed\<close> to this single category of @{syntax (inner)
  logic}.

  \<^descr> @{syntax_ref (inner) index} denotes an optional index term for indexed
  syntax. If omitted, it refers to the first @{keyword_ref "structure"}
  variable in the context. The special dummy ``\<open>\<index>\<close>'' serves as pattern
  variable in mixfix annotations that introduce indexed notation.

  \<^descr> @{syntax_ref (inner) idt} denotes identifiers, possibly constrained by
  types.

  \<^descr> @{syntax_ref (inner) idts} denotes a sequence of @{syntax_ref (inner)
  idt}. This is the most basic category for variables in iterated binders,
  such as \<open>\<lambda>\<close> or \<open>\<And>\<close>.

  \<^descr> @{syntax_ref (inner) pttrn} and @{syntax_ref (inner) pttrns} denote
  patterns for abstraction, cases bindings etc. In Pure, these categories
  start as a merely copy of @{syntax (inner) idt} and @{syntax (inner) idts},
  respectively. Object-logics may add additional productions for binding
  forms.

  \<^descr> @{syntax_ref (inner) type} denotes types of the meta-logic.

  \<^descr> @{syntax_ref (inner) sort} denotes meta-level sorts.


  Here are some further explanations of certain syntax features.

  \<^item> In @{syntax (inner) idts}, note that \<open>x :: nat y\<close> is parsed as \<open>x :: (nat
  y)\<close>, treating \<open>y\<close> like a type constructor applied to \<open>nat\<close>. To avoid this
  interpretation, write \<open>(x :: nat) y\<close> with explicit parentheses.

  \<^item> Similarly, \<open>x :: nat y :: nat\<close> is parsed as \<open>x :: (nat y :: nat)\<close>. The
  correct form is \<open>(x :: nat) (y :: nat)\<close>, or \<open>(x :: nat) y :: nat\<close> if \<open>y\<close> is
  last in the sequence of identifiers.

  \<^item> Type constraints for terms bind very weakly. For example, \<open>x < y :: nat\<close>
  is normally parsed as \<open>(x < y) :: nat\<close>, unless \<open><\<close> has a very low priority,
  in which case the input is likely to be ambiguous. The correct form is \<open>x <
  (y :: nat)\<close>.

  \<^item> Dummy variables (written as underscore) may occur in different
  roles.

    \<^descr> A sort ``\<open>_\<close>'' refers to a vacuous constraint for type variables, which
    is effectively ignored in type-inference.

    \<^descr> A type ``\<open>_\<close>'' or ``\<open>_ :: sort\<close>'' acts like an anonymous inference
    parameter, which is filled-in according to the most general type produced
    by the type-checking phase.

    \<^descr> A bound ``\<open>_\<close>'' refers to a vacuous abstraction, where the body does not
    refer to the binding introduced here. As in the term \<^term>\<open>\<lambda>x _. x\<close>,
    which is \<open>\<alpha>\<close>-equivalent to \<open>\<lambda>x y. x\<close>.

    \<^descr> A free ``\<open>_\<close>'' refers to an implicit outer binding. Higher definitional
    packages usually allow forms like \<open>f x _ = x\<close>.

    \<^descr> A schematic ``\<open>_\<close>'' (within a term pattern, see \secref{sec:term-decls})
    refers to an anonymous variable that is implicitly abstracted over its
    context of locally bound variables. For example, this allows pattern
    matching of \<open>{x. f x = g x}\<close> against \<open>{x. _ = _}\<close>, or even \<open>{_. _ = _}\<close> by
    using both bound and schematic dummies.

  \<^descr> The three literal dots ``\<^verbatim>\<open>...\<close>'' may be also written as ellipsis symbol
  \<^verbatim>\<open>\<dots>\<close>. In both cases this refers to a special schematic variable, which is
  bound in the context. This special term abbreviation works nicely with
  calculational reasoning (\secref{sec:calculation}).

  \<^descr> \<^verbatim>\<open>CONST\<close> ensures that the given identifier is treated as constant term,
  and passed through the parse tree in fully internalized form. This is
  particularly relevant for translation rules (\secref{sec:syn-trans}),
  notably on the RHS.

  \<^descr> \<^verbatim>\<open>XCONST\<close> is similar to \<^verbatim>\<open>CONST\<close>, but retains the constant name as given.
  This is only relevant to translation rules (\secref{sec:syn-trans}), notably
  on the LHS.
\<close>


subsection \<open>Inspecting the syntax\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "print_syntax"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  \<^descr> @{command "print_syntax"} prints the inner syntax of the current context.
  The output can be quite large; the most important sections are explained
  below.

    \<^descr> \<open>lexicon\<close> lists the delimiters of the inner token language; see
    \secref{sec:inner-lex}.

    \<^descr> \<open>productions\<close> lists the productions of the underlying priority grammar;
    see \secref{sec:priority-grammar}.

    Many productions have an extra \<open>\<dots> \<^bold>\<Rightarrow> name\<close>. These names later become the
    heads of parse trees; they also guide the pretty printer.

    Productions without such parse tree names are called \<^emph>\<open>copy productions\<close>.
    Their right-hand side must have exactly one nonterminal symbol (or named
    token). The parser does not create a new parse tree node for copy
    productions, but simply returns the parse tree of the right-hand symbol.

    If the right-hand side of a copy production consists of a single
    nonterminal without any delimiters, then it is called a \<^emph>\<open>chain
    production\<close>. Chain productions act as abbreviations: conceptually, they
    are removed from the grammar by adding new productions. Priority
    information attached to chain productions is ignored.

    \<^descr> \<open>print modes\<close> lists the alternative print modes provided by this
    grammar; see \secref{sec:print-modes}.

    \<^descr> \<open>parse_rules\<close> and \<open>print_rules\<close> relate to syntax translations (macros);
    see \secref{sec:syn-trans}.

    \<^descr> \<open>parse_ast_translation\<close> and \<open>print_ast_translation\<close> list sets of
    constants that invoke translation functions for abstract syntax trees,
    which are only required in very special situations; see
    \secref{sec:tr-funs}.

    \<^descr> \<open>parse_translation\<close> and \<open>print_translation\<close> list the sets of constants
    that invoke regular translation functions; see \secref{sec:tr-funs}.
\<close>


subsection \<open>Ambiguity of parsed expressions\<close>

text \<open>
  \begin{tabular}{rcll}
    @{attribute_def syntax_ambiguity_warning} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def syntax_ambiguity_limit} & : & \<open>attribute\<close> & default \<open>10\<close> \\
  \end{tabular}

  Depending on the grammar and the given input, parsing may be ambiguous.
  Isabelle lets the Earley parser enumerate all possible parse trees, and then
  tries to make the best out of the situation. Terms that cannot be
  type-checked are filtered out, which often leads to a unique result in the
  end. Unlike regular type reconstruction, which is applied to the whole
  collection of input terms simultaneously, the filtering stage only treats
  each given term in isolation. Filtering is also not attempted for individual
  types or raw ASTs (as required for @{command translations}).

  Certain warning or error messages are printed, depending on the situation
  and the given configuration options. Parsing ultimately fails, if multiple
  results remain after the filtering phase.

  \<^descr> @{attribute syntax_ambiguity_warning} controls output of explicit warning
  messages about syntax ambiguity.

  \<^descr> @{attribute syntax_ambiguity_limit} determines the number of resulting
  parse trees that are shown as part of the printed message in case of an
  ambiguity.
\<close>


section \<open>Syntax transformations \label{sec:syntax-transformations}\<close>

text \<open>
  The inner syntax engine of Isabelle provides separate mechanisms to
  transform parse trees either via rewrite systems on first-order ASTs
  (\secref{sec:syn-trans}), or ML functions on ASTs or syntactic \<open>\<lambda>\<close>-terms
  (\secref{sec:tr-funs}). This works both for parsing and printing, as
  outlined in \figref{fig:parse-print}.

  \begin{figure}[htbp]
  \begin{center}
  \begin{tabular}{cl}
  string          & \\
  \<open>\<down>\<close>     & lexer + parser \\
  parse tree      & \\
  \<open>\<down>\<close>     & parse AST translation \\
  AST             & \\
  \<open>\<down>\<close>     & AST rewriting (macros) \\
  AST             & \\
  \<open>\<down>\<close>     & parse translation \\
  --- pre-term ---    & \\
  \<open>\<down>\<close>     & print translation \\
  AST             & \\
  \<open>\<down>\<close>     & AST rewriting (macros) \\
  AST             & \\
  \<open>\<down>\<close>     & print AST translation \\
  string          &
  \end{tabular}
  \end{center}
  \caption{Parsing and printing with translations}\label{fig:parse-print}
  \end{figure}

  These intermediate syntax tree formats eventually lead to a pre-term with
  all names and binding scopes resolved, but most type information still
  missing. Explicit type constraints might be given by the user, or implicit
  position information by the system --- both need to be passed-through
  carefully by syntax transformations.

  Pre-terms are further processed by the so-called \<^emph>\<open>check\<close> and \<^emph>\<open>uncheck\<close>
  phases that are intertwined with type-inference (see also @{cite
  "isabelle-implementation"}). The latter allows to operate on higher-order
  abstract syntax with proper binding and type information already available.

  As a rule of thumb, anything that manipulates bindings of variables or
  constants needs to be implemented as syntax transformation (see below).
  Anything else is better done via check/uncheck: a prominent example
  application is the @{command abbreviation} concept of Isabelle/Pure.
\<close>


subsection \<open>Abstract syntax trees \label{sec:ast}\<close>

text \<open>
  The ML datatype \<^ML_type>\<open>Ast.ast\<close> explicitly represents the intermediate
  AST format that is used for syntax rewriting (\secref{sec:syn-trans}). It is
  defined in ML as follows:
  @{verbatim [display]
\<open>datatype ast =
  Constant of string |
  Variable of string |
  Appl of ast list\<close>}

  An AST is either an atom (constant or variable) or a list of (at least two)
  subtrees. Occasional diagnostic output of ASTs uses notation that resembles
  S-expression of LISP. Constant atoms are shown as quoted strings, variable
  atoms as non-quoted strings and applications as a parenthesized list of
  subtrees. For example, the AST
  @{ML [display] \<open>Ast.Appl [Ast.Constant "_abs", Ast.Variable "x", Ast.Variable "t"]\<close>}
  is pretty-printed as \<^verbatim>\<open>("_abs" x t)\<close>. Note that \<^verbatim>\<open>()\<close> and \<^verbatim>\<open>(x)\<close> are
  excluded as ASTs, because they have too few subtrees.

  \<^medskip>
  AST application is merely a pro-forma mechanism to indicate certain
  syntactic structures. Thus \<^verbatim>\<open>(c a b)\<close> could mean either term application or
  type application, depending on the syntactic context.

  Nested application like \<^verbatim>\<open>(("_abs" x t) u)\<close> is also possible, but ASTs are
  definitely first-order: the syntax constant \<^verbatim>\<open>"_abs"\<close> does not bind the \<^verbatim>\<open>x\<close>
  in any way. Proper bindings are introduced in later stages of the term
  syntax, where \<^verbatim>\<open>("_abs" x t)\<close> becomes an \<^ML>\<open>Abs\<close> node and occurrences of
  \<^verbatim>\<open>x\<close> in \<^verbatim>\<open>t\<close> are replaced by bound variables (represented as de-Bruijn
  indices).
\<close>


subsubsection \<open>AST constants versus variables\<close>

text \<open>
  Depending on the situation --- input syntax, output syntax, translation
  patterns --- the distinction of atomic ASTs as \<^ML>\<open>Ast.Constant\<close> versus
  \<^ML>\<open>Ast.Variable\<close> serves slightly different purposes.

  Input syntax of a term such as \<open>f a b = c\<close> does not yet indicate the scopes
  of atomic entities \<open>f, a, b, c\<close>: they could be global constants or local
  variables, even bound ones depending on the context of the term. \<^ML>\<open>Ast.Variable\<close> leaves this choice still open: later syntax layers (or
  translation functions) may capture such a variable to determine its role
  specifically, to make it a constant, bound variable, free variable etc. In
  contrast, syntax translations that introduce already known constants would
  rather do it via \<^ML>\<open>Ast.Constant\<close> to prevent accidental re-interpretation
  later on.

  Output syntax turns term constants into \<^ML>\<open>Ast.Constant\<close> and variables
  (free or schematic) into \<^ML>\<open>Ast.Variable\<close>. This information is precise
  when printing fully formal \<open>\<lambda>\<close>-terms.

  \<^medskip>
  AST translation patterns (\secref{sec:syn-trans}) that represent terms
  cannot distinguish constants and variables syntactically. Explicit
  indication of \<open>CONST c\<close> inside the term language is required, unless \<open>c\<close> is
  known as special \<^emph>\<open>syntax constant\<close> (see also @{command syntax}). It is also
  possible to use @{command syntax} declarations (without mixfix annotation)
  to enforce that certain unqualified names are always treated as constant
  within the syntax machinery.

  The situation is simpler for ASTs that represent types or sorts, since the
  concrete syntax already distinguishes type variables from type constants
  (constructors). So \<open>('a, 'b) foo\<close> corresponds to an AST application of some
  constant for \<open>foo\<close> and variable arguments for \<open>'a\<close> and \<open>'b\<close>. Note that the
  postfix application is merely a feature of the concrete syntax, while in the
  AST the constructor occurs in head position.
\<close>


subsubsection \<open>Authentic syntax names\<close>

text \<open>
  Naming constant entities within ASTs is another delicate issue. Unqualified
  names are resolved in the name space tables in the last stage of parsing,
  after all translations have been applied. Since syntax transformations do
  not know about this later name resolution, there can be surprises in
  boundary cases.

  \<^emph>\<open>Authentic syntax names\<close> for \<^ML>\<open>Ast.Constant\<close> avoid this problem: the
  fully-qualified constant name with a special prefix for its formal category
  (\<open>class\<close>, \<open>type\<close>, \<open>const\<close>, \<open>fixed\<close>) represents the information faithfully
  within the untyped AST format. Accidental overlap with free or bound
  variables is excluded as well. Authentic syntax names work implicitly in the
  following situations:

    \<^item> Input of term constants (or fixed variables) that are introduced by
    concrete syntax via @{command notation}: the correspondence of a
    particular grammar production to some known term entity is preserved.

    \<^item> Input of type constants (constructors) and type classes --- thanks to
    explicit syntactic distinction independently on the context.

    \<^item> Output of term constants, type constants, type classes --- this
    information is already available from the internal term to be printed.

  In other words, syntax transformations that operate on input terms written
  as prefix applications are difficult to make robust. Luckily, this case
  rarely occurs in practice, because syntax forms to be translated usually
  correspond to some concrete notation.
\<close>


subsection \<open>Raw syntax and translations \label{sec:syn-trans}\<close>

text \<open>
  \begin{tabular}{rcll}
    @{command_def "nonterminal"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "syntax"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "no_syntax"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "translations"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "no_translations"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{attribute_def syntax_ast_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def syntax_ast_stats} & : & \<open>attribute\<close> & default \<open>false\<close> \\
  \end{tabular}
  \<^medskip>

  Unlike mixfix notation for existing formal entities (\secref{sec:notation}),
  raw syntax declarations provide full access to the priority grammar of the
  inner syntax, without any sanity checks. This includes additional syntactic
  categories (via @{command nonterminal}) and free-form grammar productions
  (via @{command syntax}). Additional syntax translations (or macros, via
  @{command translations}) are required to turn resulting parse trees into
  proper representations of formal entities again.

  \<^rail>\<open>
    @@{command nonterminal} (@{syntax name} + @'and')
    ;
    (@@{command syntax} | @@{command no_syntax}) @{syntax mode}? (constdecl +)
    ;
    (@@{command translations} | @@{command no_translations})
      (transpat ('==' | '=>' | '<=' | '\<rightleftharpoons>' | '\<rightharpoonup>' | '\<leftharpoondown>') transpat +)
    ;

    constdecl: @{syntax name} '::' @{syntax type} @{syntax mixfix}?
    ;
    mode: ('(' ( @{syntax name} | @'output' | @{syntax name} @'output' ) ')')
    ;
    transpat: ('(' @{syntax name} ')')? @{syntax string}
  \<close>

  \<^descr> @{command "nonterminal"}~\<open>c\<close> declares a type constructor \<open>c\<close> (without
  arguments) to act as purely syntactic type: a nonterminal symbol of the
  inner syntax.

  \<^descr> @{command "syntax"}~\<open>(mode) c :: \<sigma> (mx)\<close> augments the priority grammar and
  the pretty printer table for the given print mode (default \<^verbatim>\<open>""\<close>). An
  optional keyword @{keyword_ref "output"} means that only the pretty printer
  table is affected.

  Following \secref{sec:mixfix}, the mixfix annotation \<open>mx = template ps q\<close>
  together with type \<open>\<sigma> = \<tau>\<^sub>1 \<Rightarrow> \<dots> \<tau>\<^sub>n \<Rightarrow> \<tau>\<close> and specify a grammar production.
  The \<open>template\<close> contains delimiter tokens that surround \<open>n\<close> argument
  positions (\<^verbatim>\<open>_\<close>). The latter correspond to nonterminal symbols \<open>A\<^sub>i\<close> derived
  from the argument types \<open>\<tau>\<^sub>i\<close> as follows:

    \<^item> \<open>prop\<close> if \<open>\<tau>\<^sub>i = prop\<close>

    \<^item> \<open>logic\<close> if \<open>\<tau>\<^sub>i = (\<dots>)\<kappa>\<close> for logical type constructor \<open>\<kappa> \<noteq> prop\<close>

    \<^item> \<open>any\<close> if \<open>\<tau>\<^sub>i = \<alpha>\<close> for type variables

    \<^item> \<open>\<kappa>\<close> if \<open>\<tau>\<^sub>i = \<kappa>\<close> for nonterminal \<open>\<kappa>\<close> (syntactic type constructor)

  Each \<open>A\<^sub>i\<close> is decorated by priority \<open>p\<^sub>i\<close> from the given list \<open>ps\<close>; missing
  priorities default to 0.

  The resulting nonterminal of the production is determined similarly from
  type \<open>\<tau>\<close>, with priority \<open>q\<close> and default 1000.

  \<^medskip>
  Parsing via this production produces parse trees \<open>t\<^sub>1, \<dots>, t\<^sub>n\<close> for the
  argument slots. The resulting parse tree is composed as \<open>c t\<^sub>1 \<dots> t\<^sub>n\<close>, by
  using the syntax constant \<open>c\<close> of the syntax declaration.

  Such syntactic constants are invented on the spot, without formal check
  wrt.\ existing declarations. It is conventional to use plain identifiers
  prefixed by a single underscore (e.g.\ \<open>_foobar\<close>). Names should be chosen
  with care, to avoid clashes with other syntax declarations.

  \<^medskip>
  The special case of copy production is specified by \<open>c =\<close>~\<^verbatim>\<open>""\<close> (empty
  string). It means that the resulting parse tree \<open>t\<close> is copied directly,
  without any further decoration.

  \<^descr> @{command "no_syntax"}~\<open>(mode) decls\<close> removes grammar declarations (and
  translations) resulting from \<open>decls\<close>, which are interpreted in the same
  manner as for @{command "syntax"} above.

  \<^descr> @{command "translations"}~\<open>rules\<close> specifies syntactic translation rules
  (i.e.\ macros) as first-order rewrite rules on ASTs (\secref{sec:ast}). The
  theory context maintains two independent lists translation rules: parse
  rules (\<^verbatim>\<open>=>\<close> or \<open>\<rightharpoonup>\<close>) and print rules (\<^verbatim>\<open><=\<close> or \<open>\<leftharpoondown>\<close>). For convenience, both
  can be specified simultaneously as parse~/ print rules (\<^verbatim>\<open>==\<close> or \<open>\<rightleftharpoons>\<close>).

  Translation patterns may be prefixed by the syntactic category to be used
  for parsing; the default is \<open>logic\<close> which means that regular term syntax is
  used. Both sides of the syntax translation rule undergo parsing and parse
  AST translations \secref{sec:tr-funs}, in order to perform some fundamental
  normalization like \<open>\<lambda>x y. b \<leadsto> \<lambda>x. \<lambda>y. b\<close>, but other AST translation rules
  are \<^emph>\<open>not\<close> applied recursively here.

  When processing AST patterns, the inner syntax lexer runs in a different
  mode that allows identifiers to start with underscore. This accommodates the
  usual naming convention for auxiliary syntax constants --- those that do not
  have a logical counter part --- by allowing to specify arbitrary AST
  applications within the term syntax, independently of the corresponding
  concrete syntax.

  Atomic ASTs are distinguished as \<^ML>\<open>Ast.Constant\<close> versus \<^ML>\<open>Ast.Variable\<close> as follows: a qualified name or syntax constant declared via
  @{command syntax}, or parse tree head of concrete notation becomes \<^ML>\<open>Ast.Constant\<close>, anything else \<^ML>\<open>Ast.Variable\<close>. Note that \<open>CONST\<close> and
  \<open>XCONST\<close> within the term language (\secref{sec:pure-grammar}) allow to
  enforce treatment as constants.

  AST rewrite rules \<open>(lhs, rhs)\<close> need to obey the following side-conditions:

    \<^item> Rules must be left linear: \<open>lhs\<close> must not contain repeated
    variables.\<^footnote>\<open>The deeper reason for this is that AST equality is not
    well-defined: different occurrences of the ``same'' AST could be decorated
    differently by accidental type-constraints or source position information,
    for example.\<close>

    \<^item> Every variable in \<open>rhs\<close> must also occur in \<open>lhs\<close>.

  \<^descr> @{command "no_translations"}~\<open>rules\<close> removes syntactic translation rules,
  which are interpreted in the same manner as for @{command "translations"}
  above.

  \<^descr> @{attribute syntax_ast_trace} and @{attribute syntax_ast_stats} control
  diagnostic output in the AST normalization process, when translation rules
  are applied to concrete input or output.


  Raw syntax and translations provides a slightly more low-level access to the
  grammar and the form of resulting parse trees. It is often possible to avoid
  this untyped macro mechanism, and use type-safe @{command abbreviation} or
  @{command notation} instead. Some important situations where @{command
  syntax} and @{command translations} are really need are as follows:

  \<^item> Iterated replacement via recursive @{command translations}. For example,
  consider list enumeration \<^term>\<open>[a, b, c, d]\<close> as defined in theory
  \<^theory>\<open>HOL.List\<close>.

  \<^item> Change of binding status of variables: anything beyond the built-in
  @{keyword "binder"} mixfix annotation requires explicit syntax translations.
  For example, consider the set comprehension syntax \<^term>\<open>{x. P}\<close> as
  defined in theory \<^theory>\<open>HOL.Set\<close>.
\<close>


subsubsection \<open>Applying translation rules\<close>

text \<open>
  As a term is being parsed or printed, an AST is generated as an intermediate
  form according to \figref{fig:parse-print}. The AST is normalized by
  applying translation rules in the manner of a first-order term rewriting
  system. We first examine how a single rule is applied.

  Let \<open>t\<close> be the abstract syntax tree to be normalized and \<open>(lhs, rhs)\<close> some
  translation rule. A subtree \<open>u\<close> of \<open>t\<close> is called \<^emph>\<open>redex\<close> if it is an
  instance of \<open>lhs\<close>; in this case the pattern \<open>lhs\<close> is said to match the
  object \<open>u\<close>. A redex matched by \<open>lhs\<close> may be replaced by the corresponding
  instance of \<open>rhs\<close>, thus \<^emph>\<open>rewriting\<close> the AST \<open>t\<close>. Matching requires some
  notion of \<^emph>\<open>place-holders\<close> in rule patterns: \<^ML>\<open>Ast.Variable\<close> serves this
  purpose.

  More precisely, the matching of the object \<open>u\<close> against the pattern \<open>lhs\<close> is
  performed as follows:

    \<^item> Objects of the form \<^ML>\<open>Ast.Variable\<close>~\<open>x\<close> or \<^ML>\<open>Ast.Constant\<close>~\<open>x\<close> are
    matched by pattern \<^ML>\<open>Ast.Constant\<close>~\<open>x\<close>. Thus all atomic ASTs in the
    object are treated as (potential) constants, and a successful match makes
    them actual constants even before name space resolution (see also
    \secref{sec:ast}).

    \<^item> Object \<open>u\<close> is matched by pattern \<^ML>\<open>Ast.Variable\<close>~\<open>x\<close>, binding \<open>x\<close> to
    \<open>u\<close>.

    \<^item> Object \<^ML>\<open>Ast.Appl\<close>~\<open>us\<close> is matched by \<^ML>\<open>Ast.Appl\<close>~\<open>ts\<close> if \<open>us\<close> and
    \<open>ts\<close> have the same length and each corresponding subtree matches.

    \<^item> In every other case, matching fails.

  A successful match yields a substitution that is applied to \<open>rhs\<close>,
  generating the instance that replaces \<open>u\<close>.

  Normalizing an AST involves repeatedly applying translation rules until none
  are applicable. This works yoyo-like: top-down, bottom-up, top-down, etc. At
  each subtree position, rules are chosen in order of appearance in the theory
  definitions.

  The configuration options @{attribute syntax_ast_trace} and @{attribute
  syntax_ast_stats} might help to understand this process and diagnose
  problems.

  \begin{warn}
  If syntax translation rules work incorrectly, the output of @{command_ref
  print_syntax} with its \<^emph>\<open>rules\<close> sections reveals the actual internal forms
  of AST pattern, without potentially confusing concrete syntax. Recall that
  AST constants appear as quoted strings and variables without quotes.
  \end{warn}

  \begin{warn}
  If @{attribute_ref eta_contract} is set to \<open>true\<close>, terms will be
  \<open>\<eta>\<close>-contracted \<^emph>\<open>before\<close> the AST rewriter sees them. Thus some abstraction
  nodes needed for print rules to match may vanish. For example, \<open>Ball A (\<lambda>x.
  P x)\<close> would contract to \<open>Ball A P\<close> and the standard print rule would fail to
  apply. This problem can be avoided by hand-written ML translation functions
  (see also \secref{sec:tr-funs}), which is in fact the same mechanism used in
  built-in @{keyword "binder"} declarations.
  \end{warn}
\<close>


subsection \<open>Syntax translation functions \label{sec:tr-funs}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "parse_ast_translation"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "parse_translation"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "print_translation"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "typed_print_translation"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def "print_ast_translation"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{ML_antiquotation_def "class_syntax"} & : & \<open>ML antiquotation\<close> \\
    @{ML_antiquotation_def "type_syntax"} & : & \<open>ML antiquotation\<close> \\
    @{ML_antiquotation_def "const_syntax"} & : & \<open>ML antiquotation\<close> \\
    @{ML_antiquotation_def "syntax_const"} & : & \<open>ML antiquotation\<close> \\
  \end{matharray}

  Syntax translation functions written in ML admit almost arbitrary
  manipulations of inner syntax, at the expense of some complexity and
  obscurity in the implementation.

  \<^rail>\<open>
  ( @@{command parse_ast_translation} | @@{command parse_translation} |
    @@{command print_translation} | @@{command typed_print_translation} |
    @@{command print_ast_translation}) @{syntax text}
  ;
  (@@{ML_antiquotation class_syntax} |
   @@{ML_antiquotation type_syntax} |
   @@{ML_antiquotation const_syntax} |
   @@{ML_antiquotation syntax_const}) embedded
  \<close>

  \<^descr> @{command parse_translation} etc. declare syntax translation functions to
  the theory. Any of these commands have a single @{syntax text} argument that
  refers to an ML expression of appropriate type as follows:

  \<^medskip>
  {\footnotesize
  \begin{tabular}{l}
  @{command parse_ast_translation} : \\
  \quad \<^ML_type>\<open>(string * (Proof.context -> Ast.ast list -> Ast.ast)) list\<close> \\
  @{command parse_translation} : \\
  \quad \<^ML_type>\<open>(string * (Proof.context -> term list -> term)) list\<close> \\
  @{command print_translation} : \\
  \quad \<^ML_type>\<open>(string * (Proof.context -> term list -> term)) list\<close> \\
  @{command typed_print_translation} : \\
  \quad \<^ML_type>\<open>(string * (Proof.context -> typ -> term list -> term)) list\<close> \\
  @{command print_ast_translation} : \\
  \quad \<^ML_type>\<open>(string * (Proof.context -> Ast.ast list -> Ast.ast)) list\<close> \\
  \end{tabular}}
  \<^medskip>

  The argument list consists of \<open>(c, tr)\<close> pairs, where \<open>c\<close> is the syntax name
  of the formal entity involved, and \<open>tr\<close> a function that translates a syntax
  form \<open>c args\<close> into \<open>tr ctxt args\<close> (depending on the context). The
  Isabelle/ML naming convention for parse translations is \<open>c_tr\<close> and for print
  translations \<open>c_tr'\<close>.

  The @{command_ref print_syntax} command displays the sets of names
  associated with the translation functions of a theory under
  \<open>parse_ast_translation\<close> etc.

  \<^descr> \<open>@{class_syntax c}\<close>, \<open>@{type_syntax c}\<close>, \<open>@{const_syntax c}\<close> inline the
  authentic syntax name of the given formal entities into the ML source. This
  is the fully-qualified logical name prefixed by a special marker to indicate
  its kind: thus different logical name spaces are properly distinguished
  within parse trees.

  \<^descr> \<open>@{const_syntax c}\<close> inlines the name \<open>c\<close> of the given syntax constant,
  having checked that it has been declared via some @{command syntax} commands
  within the theory context. Note that the usual naming convention makes
  syntax constants start with underscore, to reduce the chance of accidental
  clashes with other names occurring in parse trees (unqualified constants
  etc.).
\<close>


subsubsection \<open>The translation strategy\<close>

text \<open>
  The different kinds of translation functions are invoked during the
  transformations between parse trees, ASTs and syntactic terms (cf.\
  \figref{fig:parse-print}). Whenever a combination of the form \<open>c x\<^sub>1 \<dots> x\<^sub>n\<close>
  is encountered, and a translation function \<open>f\<close> of appropriate kind is
  declared for \<open>c\<close>, the result is produced by evaluation of \<open>f [x\<^sub>1, \<dots>, x\<^sub>n]\<close>
  in ML.

  For AST translations, the arguments \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are ASTs. A combination
  has the form \<^ML>\<open>Ast.Constant\<close>~\<open>c\<close> or \<^ML>\<open>Ast.Appl\<close>~\<open>[\<close>\<^ML>\<open>Ast.Constant\<close>~\<open>c, x\<^sub>1, \<dots>, x\<^sub>n]\<close>. For term translations, the arguments are
  terms and a combination has the form \<^ML>\<open>Const\<close>~\<open>(c, \<tau>)\<close> or \<^ML>\<open>Const\<close>~\<open>(c, \<tau>) $ x\<^sub>1 $ \<dots> $ x\<^sub>n\<close>. Terms allow more sophisticated
  transformations than ASTs do, typically involving abstractions and bound
  variables. \<^emph>\<open>Typed\<close> print translations may even peek at the type \<open>\<tau>\<close> of the
  constant they are invoked on, although some information might have been
  suppressed for term output already.

  Regardless of whether they act on ASTs or terms, translation functions
  called during the parsing process differ from those for printing in their
  overall behaviour:

    \<^descr>[Parse translations] are applied bottom-up. The arguments are already in
    translated form. The translations must not fail; exceptions trigger an
    error message. There may be at most one function associated with any
    syntactic name.

    \<^descr>[Print translations] are applied top-down. They are supplied with
    arguments that are partly still in internal form. The result again
    undergoes translation; therefore a print translation should not introduce
    as head the very constant that invoked it. The function may raise
    exception \<^ML>\<open>Match\<close> to indicate failure; in this event it has no effect.
    Multiple functions associated with some syntactic name are tried in the
    order of declaration in the theory.

  Only constant atoms --- constructor \<^ML>\<open>Ast.Constant\<close> for ASTs and \<^ML>\<open>Const\<close> for terms --- can invoke translation functions. This means that parse
  translations can only be associated with parse tree heads of concrete
  syntax, or syntactic constants introduced via other translations. For plain
  identifiers within the term language, the status of constant versus variable
  is not yet know during parsing. This is in contrast to print translations,
  where constants are explicitly known from the given term in its fully
  internal form.
\<close>


subsection \<open>Built-in syntax transformations\<close>

text \<open>
  Here are some further details of the main syntax transformation phases of
  \figref{fig:parse-print}.
\<close>


subsubsection \<open>Transforming parse trees to ASTs\<close>

text \<open>
  The parse tree is the raw output of the parser. It is transformed into an
  AST according to some basic scheme that may be augmented by AST translation
  functions as explained in \secref{sec:tr-funs}.

  The parse tree is constructed by nesting the right-hand sides of the
  productions used to recognize the input. Such parse trees are simply lists
  of tokens and constituent parse trees, the latter representing the
  nonterminals of the productions. Ignoring AST translation functions, parse
  trees are transformed to ASTs by stripping out delimiters and copy
  productions, while retaining some source position information from input
  tokens.

  The Pure syntax provides predefined AST translations to make the basic
  \<open>\<lambda>\<close>-term structure more apparent within the (first-order) AST
  representation, and thus facilitate the use of @{command translations} (see
  also \secref{sec:syn-trans}). This covers ordinary term application, type
  application, nested abstraction, iterated meta implications and function
  types. The effect is illustrated on some representative input strings is as
  follows:

  \begin{center}
  \begin{tabular}{ll}
  input source & AST \\
  \hline
  \<open>f x y z\<close> & \<^verbatim>\<open>(f x y z)\<close> \\
  \<open>'a ty\<close> & \<^verbatim>\<open>(ty 'a)\<close> \\
  \<open>('a, 'b)ty\<close> & \<^verbatim>\<open>(ty 'a 'b)\<close> \\
  \<open>\<lambda>x y z. t\<close> & \<^verbatim>\<open>("_abs" x ("_abs" y ("_abs" z t)))\<close> \\
  \<open>\<lambda>x :: 'a. t\<close> & \<^verbatim>\<open>("_abs" ("_constrain" x 'a) t)\<close> \\
  \<open>\<lbrakk>P; Q; R\<rbrakk> \<Longrightarrow> S\<close> & \<^verbatim>\<open>("Pure.imp" P ("Pure.imp" Q ("Pure.imp" R S)))\<close> \\
   \<open>['a, 'b, 'c] \<Rightarrow> 'd\<close> & \<^verbatim>\<open>("fun" 'a ("fun" 'b ("fun" 'c 'd)))\<close> \\
  \end{tabular}
  \end{center}

  Note that type and sort constraints may occur in further places ---
  translations need to be ready to cope with them. The built-in syntax
  transformation from parse trees to ASTs insert additional constraints that
  represent source positions.
\<close>


subsubsection \<open>Transforming ASTs to terms\<close>

text \<open>
  After application of macros (\secref{sec:syn-trans}), the AST is transformed
  into a term. This term still lacks proper type information, but it might
  contain some constraints consisting of applications with head \<^verbatim>\<open>_constrain\<close>,
  where the second argument is a type encoded as a pre-term within the syntax.
  Type inference later introduces correct types, or indicates type errors in
  the input.

  Ignoring parse translations, ASTs are transformed to terms by mapping AST
  constants to term constants, AST variables to term variables or constants
  (according to the name space), and AST applications to iterated term
  applications.

  The outcome is still a first-order term. Proper abstractions and bound
  variables are introduced by parse translations associated with certain
  syntax constants. Thus \<^verbatim>\<open>("_abs" x x)\<close> eventually becomes a de-Bruijn term
  \<^verbatim>\<open>Abs ("x", _, Bound 0)\<close>.
\<close>


subsubsection \<open>Printing of terms\<close>

text \<open>
  The output phase is essentially the inverse of the input phase. Terms are
  translated via abstract syntax trees into pretty-printed text.

  Ignoring print translations, the transformation maps term constants,
  variables and applications to the corresponding constructs on ASTs.
  Abstractions are mapped to applications of the special constant \<^verbatim>\<open>_abs\<close> as
  seen before. Type constraints are represented via special \<^verbatim>\<open>_constrain\<close>
  forms, according to various policies of type annotation determined
  elsewhere. Sort constraints of type variables are handled in a similar
  fashion.

  After application of macros (\secref{sec:syn-trans}), the AST is finally
  pretty-printed. The built-in print AST translations reverse the
  corresponding parse AST translations.

  \<^medskip>
  For the actual printing process, the priority grammar
  (\secref{sec:priority-grammar}) plays a vital role: productions are used as
  templates for pretty printing, with argument slots stemming from
  nonterminals, and syntactic sugar stemming from literal tokens.

  Each AST application with constant head \<open>c\<close> and arguments \<open>t\<^sub>1\<close>, \dots,
  \<open>t\<^sub>n\<close> (for \<open>n = 0\<close> the AST is just the constant \<open>c\<close> itself) is printed
  according to the first grammar production of result name \<open>c\<close>. The required
  syntax priority of the argument slot is given by its nonterminal \<open>A\<^sup>(\<^sup>p\<^sup>)\<close>.
  The argument \<open>t\<^sub>i\<close> that corresponds to the position of \<open>A\<^sup>(\<^sup>p\<^sup>)\<close> is printed
  recursively, and then put in parentheses \<^emph>\<open>if\<close> its priority \<open>p\<close> requires
  this. The resulting output is concatenated with the syntactic sugar
  according to the grammar production.

  If an AST application \<open>(c x\<^sub>1 \<dots> x\<^sub>m)\<close> has more arguments than the
  corresponding production, it is first split into \<open>((c x\<^sub>1 \<dots> x\<^sub>n) x\<^sub>n\<^sub>+\<^sub>1 \<dots>
  x\<^sub>m)\<close> and then printed recursively as above.

  Applications with too few arguments or with non-constant head or without a
  corresponding production are printed in prefix-form like \<open>f t\<^sub>1 \<dots> t\<^sub>n\<close> for
  terms.

  Multiple productions associated with some name \<open>c\<close> are tried in order of
  appearance within the grammar. An occurrence of some AST variable \<open>x\<close> is
  printed as \<open>x\<close> outright.

  \<^medskip>
  White space is \<^emph>\<open>not\<close> inserted automatically. If blanks (or breaks) are
  required to separate tokens, they need to be specified in the mixfix
  declaration (\secref{sec:mixfix}).
\<close>

end
