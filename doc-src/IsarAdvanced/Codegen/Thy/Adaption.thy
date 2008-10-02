theory Adaption
imports Setup
begin

section {* Adaption to target languages \label{sec:adaption} *}

subsection {* Common adaption cases *}

text {*
  The @{theory HOL} @{theory Main} theory already provides a code
  generator setup
  which should be suitable for most applications. Common extensions
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
       @{theory "Code_Char_chr"}.
    \item[@{theory "Efficient_Nat"}] \label{eff_nat} implements natural numbers by integers,
       which in general will result in higher efficiency; pattern
       matching with @{term "0\<Colon>nat"} / @{const "Suc"}
       is eliminated;  includes @{theory "Code_Integer"}.
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


subsection {* Adaption mechanisms \label{sec:adaption_mechanisms} *}

text {*
  \begin{warn}
    The mechanisms shown here are especially for the curious;  the user
    rarely needs to do anything on his own beyond the defaults in @{text HOL}.
    Adaption is a delicated task which requires a lot of dilligence since
    it happend \emph{completely} outside the logic.
  \end{warn}
*}

text {*
  \noindent Consider the following function and its corresponding
  SML code:
*}

primrec %quoteme in_interval :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "in_interval (k, l) n \<longleftrightarrow> k \<le> n \<and> n \<le> l"
(*<*)
code_type %invisible bool
  (SML)
code_const %invisible True and False and "op \<and>" and Not
  (SML and and and)
(*>*)
text %quoteme {*@{code_stmts in_interval (SML)}*}

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

code_type %tt bool
  (SML "bool")
code_const %tt True and False and "op \<and>"
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

text %quoteme {*@{code_stmts in_interval (SML)}*}

text {*
  \noindent This still is not perfect: the parentheses
  around the \qt{andalso} expression are superfluous.
  Though the serializer
  by no means attempts to imitate the rich Isabelle syntax
  framework, it provides some common idioms, notably
  associative infixes with precedences which may be used here:
*}

code_const %tt "op \<and>"
  (SML infixl 1 "andalso")

text %quoteme {*@{code_stmts in_interval (SML)}*}

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
code_type %tt *
  (SML infix 2 "*")
code_const %tt Pair
  (SML "!((_),/ (_))")

text {*
  \noindent The initial bang ``@{verbatim "!"}'' tells the serializer to never put
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

  The HOL theories provide further
  examples for custom serialisations.
*}


subsection {* @{text Haskell} serialisation *}

text {*
  For convenience, the default
  @{text HOL} setup for @{text Haskell} maps the @{class eq} class to
  its counterpart in @{text Haskell}, giving custom serialisations
  for the class @{class eq} (by command @{command code_class}) and its operation
  @{const HOL.eq}
*}

code_class %tt eq
  (Haskell "Eq" where "HOL.eq" \<equiv> "(==)")

code_const %tt "op ="
  (Haskell infixl 4 "==")

text {*
  \noindent A problem now occurs whenever a type which
  is an instance of @{class eq} in @{text HOL} is mapped
  on a @{text Haskell}-built-in type which is also an instance
  of @{text Haskell} @{text Eq}:
*}

typedecl %quoteme bar

instantiation %quoteme bar :: eq
begin

definition %quoteme "eq_class.eq (x\<Colon>bar) y \<longleftrightarrow> x = y"

instance %quoteme by default (simp add: eq_bar_def)

end %quoteme

code_type %tt bar
  (Haskell "Integer")

text {*
  \noindent The code generator would produce
  an additional instance, which of course is rejectedby the @{text Haskell}
  compiler.
  To suppress this additional instance, use
  @{text "code_instance"}:
*}

code_instance %tt bar :: eq
  (Haskell -)

end
