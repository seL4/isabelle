theory Adaption
imports Setup
begin

setup %invisible {* Code_Target.extend_target ("\<SML>", ("SML", K I)) *}

section {* Adaption to target languages \label{sec:adaption} *}

subsection {* Adapting code generation *}

text {*
  The aspects of code generation introduced so far have two aspects
  in common:

  \begin{itemize}
    \item They act uniformly, without reference to a specific
       target language.
    \item They are \emph{safe} in the sense that as long as you trust
       the code generator meta theory and implementation, you cannot
       produce programs that yield results which are not derivable
       in the logic.
  \end{itemize}

  \noindent In this section we will introduce means to \emph{adapt} the serialiser
  to a specific target language, i.e.~to print program fragments
  in a way which accommodates \qt{already existing} ingredients of
  a target language environment, for three reasons:

  \begin{itemize}
    \item improving readability and aesthetics of generated code
    \item gaining efficiency
    \item interface with language parts which have no direct counterpart
      in @{text "HOL"} (say, imperative data structures)
  \end{itemize}

  \noindent Generally, you should avoid using those features yourself
  \emph{at any cost}:

  \begin{itemize}
    \item The safe configuration methods act uniformly on every target language,
      whereas for adaption you have to treat each target language separate.
    \item Application is extremely tedious since there is no abstraction
      which would allow for a static check, making it easy to produce garbage.
    \item More or less subtle errors can be introduced unconsciously.
  \end{itemize}

  \noindent However, even if you ought refrain from setting up adaption
  yourself, already the @{text "HOL"} comes with some reasonable default
  adaptions (say, using target language list syntax).  There also some
  common adaption cases which you can setup by importing particular
  library theories.  In order to understand these, we provide some clues here;
  these however are not supposed to replace a careful study of the sources.
*}

subsection {* The adaption principle *}

text {*
  The following figure illustrates what \qt{adaption} is conceptually
  supposed to be:

  \begin{figure}[here]
    \begin{tikzpicture}[scale = 0.5]
      \tikzstyle water=[color = blue, thick]
      \tikzstyle ice=[color = black, very thick, cap = round, join = round, fill = white]
      \tikzstyle process=[color = green, semithick, ->]
      \tikzstyle adaption=[color = red, semithick, ->]
      \tikzstyle target=[color = black]
      \foreach \x in {0, ..., 24}
        \draw[style=water] (\x, 0.25) sin + (0.25, 0.25) cos + (0.25, -0.25) sin
          + (0.25, -0.25) cos + (0.25, 0.25);
      \draw[style=ice] (1, 0) --
        (3, 6) node[above, fill=white] {logic} -- (5, 0) -- cycle;
      \draw[style=ice] (9, 0) --
        (11, 6) node[above, fill=white] {intermediate language} -- (13, 0) -- cycle;
      \draw[style=ice] (15, -6) --
        (19, 6) node[above, fill=white] {target language} -- (23, -6) -- cycle;
      \draw[style=process]
        (3.5, 3) .. controls (7, 5) .. node[fill=white] {translation} (10.5, 3);
      \draw[style=process]
        (11.5, 3) .. controls (15, 5) .. node[fill=white] (serialisation) {serialisation} (18.5, 3);
      \node (adaption) at (11, -2) [style=adaption] {adaption};
      \node at (19, 3) [rotate=90] {generated};
      \node at (19.5, -5) {language};
      \node at (19.5, -3) {library};
      \node (includes) at (19.5, -1) {includes};
      \node (reserved) at (16.5, -3) [rotate=72] {reserved}; % proper 71.57
      \draw[style=process]
        (includes) -- (serialisation);
      \draw[style=process]
        (reserved) -- (serialisation);
      \draw[style=adaption]
        (adaption) -- (serialisation);
      \draw[style=adaption]
        (adaption) -- (includes);
      \draw[style=adaption]
        (adaption) -- (reserved);
    \end{tikzpicture}
    \caption{The adaption principle}
    \label{fig:adaption}
  \end{figure}

  \noindent In the tame view, code generation acts as broker between
  @{text logic}, @{text "intermediate language"} and
  @{text "target language"} by means of @{text translation} and
  @{text serialisation};  for the latter, the serialiser has to observe
  the structure of the @{text language} itself plus some @{text reserved}
  keywords which have to be avoided for generated code.
  However, if you consider @{text adaption} mechanisms, the code generated
  by the serializer is just the tip of the iceberg:

  \begin{itemize}
    \item @{text serialisation} can be \emph{parametrised} such that
      logical entities are mapped to target-specific ones
      (e.g. target-specific list syntax,
        see also \secref{sec:adaption_mechanisms})
    \item Such parametrisations can involve references to a
      target-specific standard @{text library} (e.g. using
      the @{text Haskell} @{verbatim Maybe} type instead
      of the @{text HOL} @{type "option"} type);
      if such are used, the corresponding identifiers
      (in our example, @{verbatim Maybe}, @{verbatim Nothing}
      and @{verbatim Just}) also have to be considered @{text reserved}.
    \item Even more, the user can enrich the library of the
      target-language by providing code snippets
      (\qt{@{text "includes"}}) which are prepended to
      any generated code (see \secref{sec:include});  this typically
      also involves further @{text reserved} identifiers.
  \end{itemize}

  \noindent As figure \ref{fig:adaption} illustrates, all these adaption mechanisms
  have to act consistently;  it is at the discretion of the user
  to take care for this.
*}

subsection {* Common adaption patterns *}

text {*
  The @{theory HOL} @{theory Main} theory already provides a code
  generator setup
  which should be suitable for most applications.  Common extensions
  and modifications are available by certain theories of the @{text HOL}
  library; beside being useful in applications, they may serve
  as a tutorial for customising the code generator setup (see below
  \secref{sec:adaption_mechanisms}).

  \begin{description}

    \item[@{theory "Code_Integer"}] represents @{text HOL} integers by big
       integer literals in target languages.
    \item[@{theory "Code_Char"}] represents @{text HOL} characters by 
       character literals in target languages.
    \item[@{theory "Code_Char_chr"}] like @{text "Code_Char"},
       but also offers treatment of character codes; includes
       @{theory "Code_Char"}.
    \item[@{theory "Efficient_Nat"}] \label{eff_nat} implements natural numbers by integers,
       which in general will result in higher efficiency; pattern
       matching with @{term "0\<Colon>nat"} / @{const "Suc"}
       is eliminated;  includes @{theory "Code_Integer"}
       and @{theory "Code_Index"}.
    \item[@{theory "Code_Index"}] provides an additional datatype
       @{typ index} which is mapped to target-language built-in integers.
       Useful for code setups which involve e.g. indexing of
       target-language arrays.
    \item[@{theory "Code_Message"}] provides an additional datatype
       @{typ message_string} which is isomorphic to strings;
       @{typ message_string}s are mapped to target-language strings.
       Useful for code setups which involve e.g. printing (error) messages.

  \end{description}

  \begin{warn}
    When importing any of these theories, they should form the last
    items in an import list.  Since these theories adapt the
    code generator setup in a non-conservative fashion,
    strange effects may occur otherwise.
  \end{warn}
*}


subsection {* Parametrising serialisation \label{sec:adaption_mechanisms} *}

text {*
  Consider the following function and its corresponding
  SML code:
*}

primrec %quote in_interval :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "in_interval (k, l) n \<longleftrightarrow> k \<le> n \<and> n \<le> l"
(*<*)
code_type %invisible bool
  (SML)
code_const %invisible True and False and "op \<and>" and Not
  (SML and and and)
(*>*)
text %quote {*@{code_stmts in_interval (SML)}*}

text {*
  \noindent Though this is correct code, it is a little bit unsatisfactory:
  boolean values and operators are materialised as distinguished
  entities with have nothing to do with the SML-built-in notion
  of \qt{bool}.  This results in less readable code;
  additionally, eager evaluation may cause programs to
  loop or break which would perfectly terminate when
  the existing SML @{verbatim "bool"} would be used.  To map
  the HOL @{typ bool} on SML @{verbatim "bool"}, we may use
  \qn{custom serialisations}:
*}

code_type %quotett bool
  (SML "bool")
code_const %quotett True and False and "op \<and>"
  (SML "true" and "false" and "_ andalso _")

text {*
  \noindent The @{command code_type} command takes a type constructor
  as arguments together with a list of custom serialisations.
  Each custom serialisation starts with a target language
  identifier followed by an expression, which during
  code serialisation is inserted whenever the type constructor
  would occur.  For constants, @{command code_const} implements
  the corresponding mechanism.  Each ``@{verbatim "_"}'' in
  a serialisation expression is treated as a placeholder
  for the type constructor's (the constant's) arguments.
*}

text %quote {*@{code_stmts in_interval (SML)}*}

text {*
  \noindent This still is not perfect: the parentheses
  around the \qt{andalso} expression are superfluous.
  Though the serialiser
  by no means attempts to imitate the rich Isabelle syntax
  framework, it provides some common idioms, notably
  associative infixes with precedences which may be used here:
*}

code_const %quotett "op \<and>"
  (SML infixl 1 "andalso")

text %quote {*@{code_stmts in_interval (SML)}*}

text {*
  \noindent The attentive reader may ask how we assert that no generated
  code will accidentally overwrite.  For this reason the serialiser has
  an internal table of identifiers which have to be avoided to be used
  for new declarations.  Initially, this table typically contains the
  keywords of the target language.  It can be extended manually, thus avoiding
  accidental overwrites, using the @{command "code_reserved"} command:
*}

code_reserved %quote "\<SML>" bool true false andalso

text {*
  \noindent Next, we try to map HOL pairs to SML pairs, using the
  infix ``@{verbatim "*"}'' type constructor and parentheses:
*}
(*<*)
code_type %invisible *
  (SML)
code_const %invisible Pair
  (SML)
(*>*)
code_type %quotett *
  (SML infix 2 "*")
code_const %quotett Pair
  (SML "!((_),/ (_))")

text {*
  \noindent The initial bang ``@{verbatim "!"}'' tells the serialiser
  never to put
  parentheses around the whole expression (they are already present),
  while the parentheses around argument place holders
  tell not to put parentheses around the arguments.
  The slash ``@{verbatim "/"}'' (followed by arbitrary white space)
  inserts a space which may be used as a break if necessary
  during pretty printing.

  These examples give a glimpse what mechanisms
  custom serialisations provide; however their usage
  requires careful thinking in order not to introduce
  inconsistencies -- or, in other words:
  custom serialisations are completely axiomatic.

  A further noteworthy details is that any special
  character in a custom serialisation may be quoted
  using ``@{verbatim "'"}''; thus, in
  ``@{verbatim "fn '_ => _"}'' the first
  ``@{verbatim "_"}'' is a proper underscore while the
  second ``@{verbatim "_"}'' is a placeholder.
*}


subsection {* @{text Haskell} serialisation *}

text {*
  For convenience, the default
  @{text HOL} setup for @{text Haskell} maps the @{class eq} class to
  its counterpart in @{text Haskell}, giving custom serialisations
  for the class @{class eq} (by command @{command code_class}) and its operation
  @{const HOL.eq}
*}

code_class %quotett eq
  (Haskell "Eq")

code_const %quotett "op ="
  (Haskell infixl 4 "==")

text {*
  \noindent A problem now occurs whenever a type which
  is an instance of @{class eq} in @{text HOL} is mapped
  on a @{text Haskell}-built-in type which is also an instance
  of @{text Haskell} @{text Eq}:
*}

typedecl %quote bar

instantiation %quote bar :: eq
begin

definition %quote "eq_class.eq (x\<Colon>bar) y \<longleftrightarrow> x = y"

instance %quote by default (simp add: eq_bar_def)

end %quote

code_type %quotett bar
  (Haskell "Integer")

text {*
  \noindent The code generator would produce
  an additional instance, which of course is rejected by the @{text Haskell}
  compiler.
  To suppress this additional instance, use
  @{text "code_instance"}:
*}

code_instance %quotett bar :: eq
  (Haskell -)


subsection {* Enhancing the target language context \label{sec:include} *}

text {*
  In rare cases it is necessary to \emph{enrich} the context of a
  target language;  this is accomplished using the @{command "code_include"}
  command:
*}

code_include %quotett Haskell "Errno"
{*errno i = error ("Error number: " ++ show i)*}

code_reserved %quotett Haskell Errno

text {*
  \noindent Such named @{text include}s are then prepended to every generated code.
  Inspect such code in order to find out how @{command "code_include"} behaves
  with respect to a particular target language.
*}

end
