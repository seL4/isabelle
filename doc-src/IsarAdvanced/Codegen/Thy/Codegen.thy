
(* $Id$ *)

(*<*)
theory Codegen
imports Main
uses "../../../IsarImplementation/Thy/setup.ML"
begin

ML {*
CodegenSerializer.sml_code_width := 74;
*}

(*>*)

chapter {* Code generation from Isabelle theories *}

section {* Introduction *}

subsection {* Motivation *}

text {*
  Executing formal specifications as programs is a well-established
  topic in the theorem proving community.  With increasing
  application of theorem proving systems in the area of
  software development and verification, its relevance manifests
  for running test cases and rapid prototyping.  In logical
  calculi like constructive type theory,
  a notion of executability is implicit due to the nature
  of the calculus.  In contrast, specifications in Isabelle/HOL
  can be highly non-executable.  In order to bridge
  the gap between logic and executable specifications,
  an explicit non-trivial transformation has to be applied:
  code generation.

  This tutorial introduces a generic code generator for the
  Isabelle system \cite{isa-tutorial}.
  Generic in the sense that the
  \qn{target language} for which code shall ultimately be
  generated is not fixed but may be an arbitrary state-of-the-art
  functional programming language (currently, the implementation
  supports SML \cite{web:sml} and Haskell \cite{web:haskell}).
  We aim to provide a
  versatile environment
  suitable for software development and verification,
  structuring the process
  of code generation into a small set of orthogonal principles
  while achieving a big coverage of application areas
  with maximum flexibility.
*}


subsection {* Overview *}

text {*
  The code generator aims to be usable with no further ado
  in most cases while allowing for detailed customization.
  This manifests in the structure of this tutorial: this introduction
  continues with a short introduction of concepts.  Section
  \secref{sec:basics} explains how to use the framework naivly,
  presuming a reasonable default setup.  Then, section
  \secref{sec:advanced} deals with advanced topics,
  introducing further aspects of the code generator framework
  in a motivation-driven manner.  Last, section \secref{sec:ml}
  introduces the framework's internal programming interfaces.

  \begin{warn}
    Ultimately, the code generator which this tutorial deals with
    is supposed to replace the already established code generator
    by Stefan Berghofer \cite{Berghofer-Nipkow:2002}.
    So, for the moment, there are two distinct code generators
    in Isabelle.
    Also note that while the framework itself is largely
    object-logic independent, only HOL provides a reasonable
    framework setup.    
  \end{warn}
*}


subsection {* Code generation process *}

text {*
  The code generator employs a notion of executability
  for three foundational executable ingredients known
  from functional programming:
  \emph{function equations}, \emph{datatypes}, and
  \emph{type classes}. A function equation as a first approximation
  is a theorem of the form @{text "f t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n \<equiv> t"}
  (an equation headed by a constant @{text f} with arguments
  @{text "t\<^isub>1 t\<^isub>2 \<dots> t\<^isub>n"} and right hand side @{text t}.
  Code generation aims to turn function equations
  into a functional program by running through
  a process (see figure \ref{fig:process}):

  \begin{itemize}

    \item Out of the vast collection of theorems proven in a
      \qn{theory}, a reasonable subset modeling
      function equations is \qn{selected}.

    \item On those selected theorems, certain
      transformations are carried out
      (\qn{preprocessing}).  Their purpose is to turn theorems
      representing non- or badly executable
      specifications into equivalent but executable counterparts.
      The result is a structured collection of \qn{code theorems}.

    \item These \qn{code theorems} then are extracted
      into an Haskell-like intermediate
      language.

    \item Finally, out of the intermediate language the final
      code in the desired \qn{target language} is \qn{serialized}.

  \end{itemize}

  \begin{figure}[h]
  \centering
  \includegraphics[width=0.3\textwidth]{codegen_process}
  \caption{code generator -- processing overview}
  \label{fig:process}
  \end{figure}

  From these steps, only the two last are carried out
  outside the logic; by keeping this layer as
  thin as possible, the amount of code to trust is
  kept to a minimum.
*}



section {* Basics \label{sec:basics} *}

subsection {* Invoking the code generator *}

text {*
  Thanks to a reasonable setup of the HOL theories, in
  most cases code generation proceeds without further ado:
*}

consts
  fac :: "nat \<Rightarrow> nat"

primrec
  "fac 0 = 1"
  "fac (Suc n) = Suc n * fac n"

text {*
  This executable specification is now turned to SML code:
*}

code_gen fac (SML "examples/fac.ML")

text {*
  The \isasymCODEGEN command takes a space-seperated list of
  constants together with \qn{serialization directives}
  in parentheses. These start with a \qn{target language}
  identifer, followed by arguments, their semantics
  depending on the target. In the SML case, a filename
  is given where to write the generated code to.

  Internally, the function equations for all selected
  constants are taken, including any tranitivly required
  constants, datatypes and classes, resulting in the following
  code:

  \lstsml{Thy/examples/fac.ML}

  The code generator will complain when a required
  ingredient does not provide a executable counterpart.
  This is the case if an involved type is not a datatype:
*}

(*<*)
setup {* Sign.add_path "foo" *}
(*>*)

typedecl 'a foo

definition
  bar :: "'a foo \<Rightarrow> 'a \<Rightarrow> 'a"
  "bar x y = y"

(*<*)
hide type foo
hide const bar

setup {* Sign.parent_path *}

datatype 'a foo = Foo

definition
  bar :: "'a foo \<Rightarrow> 'a \<Rightarrow> 'a"
  "bar x y = y"
(*>*)

code_gen bar (SML "examples/fail_type.ML")

text {*
  \noindent will result in an error. Likewise, generating code
  for constants not yielding
  a function equation will fail, e.g.~the Hilbert choice
  operation @{text "SOME"}:
*}

(*<*)
setup {* Sign.add_path "foo" *}
(*>*)

definition
  pick_some :: "'a list \<Rightarrow> 'a"
  "pick_some xs = (SOME x. x \<in> set xs)"

(*<*)
hide const pick_some

setup {* Sign.parent_path *}

definition
  pick_some :: "'a list \<Rightarrow> 'a"
  "pick_some = hd"
(*>*)

code_gen pick_some (SML "examples/fail_const.ML")

subsection {* Theorem selection *}

text {*
  The list of all function equations in a theory may be inspected
  using the \isasymPRINTCODETHMS command:
*}

print_codethms

text {*
  \noindent which displays a table of constant with corresponding
  function equations (the additional stuff displayed
  shall not bother us for the moment). If this table does
  not provide at least one function
  equation, the table of primititve definitions is searched
  whether it provides one.

  The typical HOL tools are already set up in a way that
  function definitions introduced by \isasymFUN, \isasymFUNCTION,
  \isasymPRIMREC, \isasymRECDEF are implicitly propagated
  to this function equation table. Specific theorems may be
  selected using an attribute: \emph{code func}. As example,
  a weight selector function:
*}

consts
  pick :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> 'a"

primrec
  "pick (x#xs) n = (let (k, v) = x in
    if n < k then v else pick xs (n - k))"

text {*
  We want to eliminate the explicit destruction
  of @{term x} to @{term "(k, v)"}:
*}

lemma [code func]:
  "pick ((k, v)#xs) n = (if n < k then v else pick xs (n - k))"
  by simp

code_gen pick (SML "examples/pick1.ML")

text {*
  This theorem is now added to the function equation table:

  \lstsml{Thy/examples/pick1.ML}

  It might be convenient to remove the pointless original
  equation, using the \emph{nofunc} attribute:
*}

lemmas [code nofunc] = pick.simps 

code_gen pick (SML "examples/pick2.ML")

text {*
  \lstsml{Thy/examples/pick2.ML}

  Syntactic redundancies are implicitly dropped. For example,
  using a modified version of the @{const fac} function
  as function equation, the then redundant (since
  syntactically subsumed) original function equations
  are dropped, resulting in a warning:
*}

lemma [code func]:
  "fac n = (case n of 0 \<Rightarrow> 1 | Suc m \<Rightarrow> n * fac m)"
  by (cases n) simp_all

code_gen fac (SML "examples/fac_case.ML")

text {*
  \lstsml{Thy/examples/fac_case.ML}

  \begin{warn}
    Some statements in this section have to be treated with some
    caution. First, since the HOL function package is still
    under development, its setup with respect to code generation
    may differ from what is presumed here.
    Further, the attributes \emph{code} and \emph{code del}
    associated with the existing code generator also apply to
    the new one: \emph{code} implies \emph{code func},
    and \emph{code del} implies \emph{code nofunc}.
  \end{warn}
*}

subsection {* Type classes *}

text {*
  Type classes enter the game via the Isar class package.
  For a short introduction how to use it, see \cite{isabelle-classes};
  here we just illustrate its impact on code generation.

  In a target language, type classes may be represented
  nativly (as in the case of Haskell). For languages
  like SML, they are implemented using \emph{dictionaries}.
  Our following example specifiedsa class \qt{null},
  assigning to each of its inhabitants a \qt{null} value:
*}

class null =
  fixes null :: 'a

consts
  head :: "'a\<Colon>null list \<Rightarrow> 'a"

primrec
  "head [] = null"
  "head (x#xs) = x"

text {*
  We provide some instances for our @{text null}:
*}

instance option :: (type) null
  "null \<equiv> None" ..

instance list :: (type) null
  "null \<equiv> []" ..

text {*
  Constructing a dummy example:
*}

definition
  "dummy = head [Some (Suc 0), None]"

text {*
  Type classes offer a suitable occassion to introduce
  the Haskell serializer.  Its usage is almost the same
  as SML, but, in accordance with conventions
  some Haskell systems enforce, each module ends
  up in a single file. The module hierarchy is reflected in
  the file system, with root given by the user.
*}

code_gen dummy (Haskell "examples/")
  (* NOTE: you may use Haskell only once in this document, otherwise
  you have to work in distinct subdirectories *)

text {*
  \lsthaskell{Thy/examples/Codegen.hs}

  (we have left out all other modules).

  The whole code in SML with explicit dictionary passing:
*}

code_gen dummy (SML "examples/class.ML")

text {*
  \lstsml{Thy/examples/class.ML}
*}

subsection {* Incremental code generation *}

text {*
  Code generation is \emph{incremental}: theorems
  and abstract intermediate code are cached and extended on demand.
  The cache may be partially or fully dropped if the underlying
  executable content of the theory changes.
  Implementation of caching is supposed to transparently
  hid away the details from the user.  Anyway, caching
  reaches the surface by using a slightly more general form
  of the \isasymCODEGEN: either the list of constants or the
  list of serialization expressions may be dropped.  If no
  serialization expressions are given, only abstract code
  is generated and cached; if no constants are given, the
  current cache is serialized.

  For explorative reasons, an extended version of the
  \isasymCODEGEN command may prove useful:
*}

print_codethms ()

text {*
  \noindent print all cached function equations (i.e.~\emph{after}
  any applied transformation. Inside the brackets a
  list of constants may be given; their function
  euqations are added to the cache if not already present.
*}


section {* Recipes and advanced topics \label{sec:advanced} *}

text {*
  In this tutorial, we do not attempt to give an exhaustive
  description of the code generator framework; instead,
  we cast a light on advanced topics by introducing
  them together with practically motivated examples.  Concerning
  further reading, see

  \begin{itemize}

  \item the Isabelle/Isar Reference Manual \cite{isabelle-isar-ref}
    for exhaustive syntax diagrams.
  \item or \fixme{ref} which deals with foundational issues
    of the code generator framework.

  \end{itemize}
*}

subsection {* Library theories *}

text {*
  The HOL \emph{Main} theory already provides a code generator setup
  which should be suitable for most applications. Common extensions
  and modifications are available by certain theories of the HOL
  library; beside being useful in applications, they may serve
  as a tutorial for cutomizing the code generator setup.

  \begin{description}

    \item[ExecutableSet] allows to generate code
       for finite sets using lists.
    \item[ExecutableRat] implements rational
       numbers as triples @{text "(sign, enumerator, denominator)"}.
    \item[EfficientNat] implements natural numbers by integers,
       which in geneal will result in higher efficency; pattern
       matching with @{const "0\<Colon>nat"} / @{const "Suc"}
       is eliminated. \label{eff_nat}
    \item[MLString] provides an additional datatype @{text "mlstring"};
       in the HOL default setup, strings in HOL are mapped to list
       of chars in SML; values of type @{text "mlstring"} are
       mapped to strings in SML.

  \end{description}
*}

subsection {* Preprocessing *}

text {*
  Before selected function theorems are turned into abstract
  code, a chain of definitional transformation steps is carried
  out: \emph{preprocessing}. There are three possibilites
  to customize preprocessing: \emph{inline theorems},
  \emph{inline procedures} and \emph{generic preprocessors}.

  \emph{Inline theorems} are rewriting rules applied to each
  function equation.  Due to the interpretation of theorems
  of function equations, rewrites are applied to the right
  hand side and the arguments of the left hand side of an
  equation, but never to the constant heading the left hand side.
  Inline theorems may be declared an undeclared using the
  \emph{code inline} or \emph{code noinline} attribute respectivly.

  Some common applications:
*}

text_raw {*
  \begin{itemize}
     \item replacing non-executable constructs by executable ones: \\
*}     

lemma [code inline]:
  "x \<in> set xs \<longleftrightarrow> x mem xs" by (induct xs) simp_all

text_raw {*
     \item eliminating superfluous constants: \\
*}

lemma [code inline]:
  "1 = Suc 0" by simp

text_raw {*
     \item replacing executable but inconvenient constructs: \\
*}

lemma [code inline]:
  "xs = [] \<longleftrightarrow> List.null xs" by (induct xs) simp_all

text_raw {*
  \end{itemize}
*}

text {*
  The current set of inline theorems may be inspected using
  the \isasymPRINTCODETHMS command.

  \emph{Inline procedures} are a generalized version of inline
  theorems written in ML -- rewrite rules are generated dependent
  on the function theorems for a certain function.  One
  application is the implicit expanding of @{typ nat} numerals
  to @{const "0\<Colon>nat"} / @{const Suc} representation.  See further
  \secref{sec:ml}

  \emph{Generic preprocessors} provide a most general interface,
  transforming a list of function theorems to another
  list of function theorems, provided that neither the heading
  constant nor its type change.  The @{const "0\<Colon>nat"} / @{const Suc}
  pattern elimination implemented in \secref{eff_nat} uses this
  interface.

  \begin{warn}
    The order in which single preprocessing steps are carried
    out currently is not specified; in particular, preprocessing
    is \emph{no} fixpoint process.  Keep this in mind when
    setting up the preprocessor.

    Further, the attribute \emph{code unfold}
    associated with the existing code generator also applies to
    the new one: \emph{code unfold} implies \emph{code inline}.
  \end{warn}
*}

subsection {* Customizing serialization  *}

text {*
  Consider the following function and its corresponding
  SML code:
*}

fun
  in_interval :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "in_interval (k, l) n \<longleftrightarrow> k \<le> n \<and> n \<le> l"
termination by (auto_term "{}")
(*<*)
declare in_interval.simps [code func]
(*>*)

(*<*)
code_type bool
  (SML)
code_const True and False and "op \<and>" and Not
  (SML and and and)
(*>*)

code_gen in_interval (SML "examples/bool1.ML")

text {*
  \lstsml{Thy/examples/bool1.ML}

  Though this is correct code, it is a little bit unsatisfactory:
  boolean values and operators are materialized as distinguished
  entities with have nothing to do with the SML-builtin notion
  of \qt{bool}.  This results in less readable code;
  additionally, eager evaluation may cause programs to
  loop or break which would perfectly terminate when
  the existing SML \qt{bool} would be used.  To map
  the HOL \qt{bool} on SML \qt{bool}, we may use
  \qn{custom serializations}:
*}

code_type bool
  (SML "bool")
code_const True and False and "op \<and>"
  (SML "true" and "false" and "_ andalso _")

text {*
  The \isasymCODETYPE commad takes a type constructor
  as arguments together with a list of custom serializations.
  Each custom serialization starts with a target language
  identifier followed by an expression, which during
  code serialization is inserted whenever the type constructor
  would occur.  For constants, \isasymCODECONST implements
  the corresponding mechanism.  Each \qt{\_} in
  a serialization expression is treated as a placeholder
  for the type constructor's (the constant's) arguments.
*}

code_reserved SML
  bool true false

text {*
  To assert that the existing \qt{bool}, \qt{true} and \qt{false}
  is not used for generated code, we use \isasymCODERESERVED.

  After this setup, code looks quite more readable:
*}

code_gen in_interval (SML "examples/bool2.ML")

text {*
  \lstsml{Thy/examples/bool2.ML}

  This still is not perfect: the parentheses
  around \qt{andalso} are superfluos.  Though the serializer
  by no means attempts to imitate the rich Isabelle syntax
  framework, it provides some common idioms, notably
  associative infixes with precedences which may be used here:
*}

code_const "op \<and>"
  (SML infixl 1 "andalso")

code_gen in_interval (SML "examples/bool3.ML")

text {*
  \lstsml{Thy/examples/bool3.ML}

  Next, we try to map HOL pairs to SML pairs, using the
  infix \qt{ * } type constructor and parentheses:
*}

(*<*)
code_type *
  (SML)
code_const Pair
  (SML)
(*>*)

code_type *
  (SML infix 2 "*")

code_const Pair
  (SML "!((_),/ (_))")

text {*
  The initial bang \qt{!} tells the serializer to never put
  parentheses around the whole expression (they are already present),
  while the parentheses around argument place holders
  tell not to put parentheses around the arguments.
  The slash \qt{/} (followed by arbitrary white space)
  inserts a space which may be used as a break if necessary
  during pretty printing.

  So far, 
*}

code_type int
  (SML "IntInf.int")
  (Haskell "Integer")

code_const "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"
    and "op - \<Colon> int \<Rightarrow> int \<Rightarrow> int"
    and "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.+ (_, _)" and "IntInf.- (_, _)" and "IntInf.* (_, _)")
  (Haskell infixl 6 "+" and infixl 6 "-" and infixl 7 "*")

(* quote with ' HOL Setup, careful *)


(* Better ops, code_moduleprolog *)
(* code_modulename *)


subsection {* Types matter  *}

(* shadowing by user-defined serilizations, understanding the type game,
reflexive equations, dangerous equations *)

subsection {* Concerning operational equality *}

text {*
  Surely you have already noticed how equality is treated
  by the code generator:
*}

fun
  collect_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "collect_duplicates xs ys [] = xs"
  "collect_duplicates xs ys (z#zs) = (if z \<in> set xs
    then if z \<in> set ys
      then collect_duplicates xs ys zs
      else collect_duplicates xs (z#ys) zs
    else collect_duplicates (z#xs) (z#ys) zs)"
termination by (auto_term "measure (length o snd o snd)")
(*<*)
lemmas [code func] = collect_duplicates.simps
(*>*)

text {*
  The membership test during preprocessing is rewritting,
  resulting in @{const List.memberl}, which itself
  performs an explicit equality check.
*}

code_gen collect_duplicates (SML "examples/collect_duplicates.ML")

text {*
  \lstsml{Thy/examples/collect_duplicates.ML}
*}

text {*
  Obviously, polymorphic equality is implemented the Haskell
  way using a type class.  How is this achieved?  By an
  almost trivial definition in the HOL setup:
*}

(*<*)
setup {* Sign.add_path "foo" *}
(*>*)

class eq =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

defs
  eq [symmetric(*, code inline, code func*)]: "eq \<equiv> (op =)"

text {*
  This merely introduces a class @{text eq} with corresponding
  operation @{const eq}, which by definition is isomorphic
  to @{const "op ="}; the preprocessing framework does the rest.
*}

(*<*)
lemmas [code noinline] = eq

hide (open) "class" eq
hide (open) const eq

lemmas [symmetric, code func] = eq_def

setup {* Sign.parent_path *}
(*>*)

text {*
  For datatypes, instances of @{text eq} are implicitly derived
  when possible.

  Though this class is designed to get rarely in the way, there
  are some cases when it suddenly comes to surface:
*}

text_raw {*
  \begin {description}
    \item[code lemmas and customary serializations for equality]
      Examine the following: \\
*}

code_const "op = \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!(_ : IntInf.int = _)")

text_raw {*
  \\ What is wrong here? Since @{const "op ="} is nothing else then
  a plain constant, this customary serialization will refer
  to polymorphic equality @{const "op = \<Colon> 'a \<Rightarrow> 'a \<Rightarrow> bool"}.
  Instead, we want the specific equality on @{typ int},
  by using the overloaded constant @{const "Code_Generator.eq"}: \\
*}

code_const "Code_Generator.eq \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!(_ : IntInf.int = _)")

text_raw {*
  \\ \item[typedecls interpretated by customary serializations] A
  common idiom is to use unspecified types for formalizations
  and interpret them for a specific target language: \\
*}

typedecl key

fun
  lookup :: "(key \<times> 'a) list \<Rightarrow> key \<Rightarrow> 'a option" where
  "lookup [] l = None"
  "lookup ((k, v) # xs) l = (if k = l then Some v else lookup xs l)"
termination by (auto_term "measure (length o fst)")
(*<*)
lemmas [code func] = lookup.simps
(*>*)

code_type key
  (SML "string")

text_raw {*
  \\ This, though, is not sufficient: @{typ key} is no instance
  of @{text eq} since @{typ key} is no datatype; the instance
  has to be declared manually, including a serialization
  for the particular instance of @{const "Code_Generator.eq"}: \\
*}

instance key :: eq ..

code_const "Code_Generator.eq \<Colon> key \<Rightarrow> key \<Rightarrow> bool"
  (SML "!(_ : string = _)")

text_raw {*
  \\ Then everything goes fine: \\
*}

code_gen lookup (SML "examples/lookup.ML")

text {*
  \lstsml{Thy/examples/lookup.ML}
*}

text_raw {*
  \item[lexicographic orderings and corregularity] Another sublety
  enters the stage when definitions of overloaded constants
  are dependent on operational equality.  For example, let
  us define a lexicographic ordering on tuples: \\
*}

(*<*)
(*setup {* Sign.add_path "foo" *}

class ord = ord*)
(*>*)

(*
instance * :: ("{eq, ord}", ord) ord
  "p1 < p2 \<equiv> let (x1, y1) = p1; (x2, y2) = p2 in
    x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  "p1 \<le> p2 \<equiv> p1 < p2 \<or> p1 = p2" ..
*)

(*<*)
(*hide (open) "class" ord
setup {* Sign.parent_path *}*)
(*>*)

text_raw {*
  \\ Then code generation will fail.  Why?  The definition
  of @{const "op \<le>"} depends on equality on both arguments,
  which are polymorhpic and impose an additional @{text eq}
  class constraint, thus violating the type discipline
  for class operations.

  The solution is to add @{text eq} to both sort arguments: \\
*}

instance * :: ("{eq, ord}", "{eq, ord}") ord
  "p1 < p2 \<equiv> let (x1, y1) = p1; (x2, y2) = p2 in
    x1 < x2 \<or> (x1 = x2 \<and> y1 < y2)"
  "p1 \<le> p2 \<equiv> p1 < p2 \<or> p1 = p2" ..

text_raw {*
  \\ Then code generation succeeds: \\
*}

code_gen "op \<le> \<Colon> 'a\<Colon>{eq, ord} \<times> 'b\<Colon>{eq, ord} \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  (SML "examples/lexicographic.ML")

text {*
  \lstsml{Thy/examples/lexicographic.ML}
*}

text_raw {*
  \item[Haskell serialization]
*}

text_raw {*
  \end {description}
*}


subsection {* Axiomatic extensions *}

text {*
  \begin{warn}
    The extensions introduced in this section, though working
    in practice, are not the cream of the crop.  They will
    eventually be replaced by more mature approaches.
  \end{warn}
*}

(* existing libraries, code inline code_constsubst, code_abstype*)

section {* ML interfaces \label{sec:ml} *}

subsection {* Constants with type discipline: codegen\_consts.ML *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type CodegenConsts.const} \\
  @{index_ML CodegenConsts.inst_of_typ: "theory -> string * typ -> CodegenConsts.const"} \\
  @{index_ML CodegenConsts.typ_of_inst: "theory -> CodegenConsts.const -> string * typ"} \\
  @{index_ML CodegenConsts.norm: "theory -> CodegenConsts.const -> CodegenConsts.const"} \\
  @{index_ML CodegenConsts.norm_of_typ: "theory -> string * typ -> CodegenConsts.const"}
  \end{mldecls}
*}

subsection {* Executable theory content: codegen\_data.ML *}

text {*
  This Pure module implements the core notions of
  executable content of a theory.
*}

subsubsection {* Suspended theorems *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type CodegenData.lthms} \\
  @{index_ML CodegenData.lazy: "(unit -> thm list) -> CodegenData.lthms"}
  \end{mldecls}
*}

subsubsection {* Executable content *}

text %mlref {*
  \begin{mldecls}
  @{index_ML CodegenData.add_func: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.del_func: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.add_funcl: "CodegenConsts.const * CodegenData.lthms -> theory -> theory"} \\
  @{index_ML CodegenData.add_datatype: "string * (((string * sort) list * (string * typ list) list) * CodegenData.lthms) -> theory -> theory"} \\
  @{index_ML CodegenData.del_datatype: "string -> theory -> theory"} \\
  @{index_ML CodegenData.add_inline: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.del_inline: "thm -> theory -> theory"} \\
  @{index_ML CodegenData.add_inline_proc: "(theory -> cterm list -> thm list) -> theory -> theory"} \\
  @{index_ML CodegenData.add_preproc: "(theory -> thm list -> thm list) -> theory -> theory"} \\
  @{index_ML CodegenData.these_funcs: "theory -> CodegenConsts.const -> thm list"} \\
  @{index_ML CodegenData.get_datatype: "theory -> string -> ((string * sort) list * (string * typ list) list) option"} \\
  @{index_ML CodegenData.get_datatype_of_constr: "theory -> CodegenConsts.const -> string option"}
  \end{mldecls}

  \begin{description}

  \item @{ML CodegenData.add_func}~@{text "thm"}

  \end{description}
*}

subsection {* Further auxiliary *}

text %mlref {*
  \begin{mldecls}
  @{index_ML CodegenConsts.const_ord: "CodegenConsts.const * CodegenConsts.const -> order"} \\
  @{index_ML CodegenConsts.eq_const: "CodegenConsts.const * CodegenConsts.const -> bool"} \\
  @{index_ML CodegenConsts.consts_of: "theory -> term -> CodegenConsts.const list"} \\
  @{index_ML CodegenConsts.read_const: "theory -> string -> CodegenConsts.const"} \\
  @{index_ML_structure CodegenConsts.Consttab} \\
  @{index_ML CodegenData.typ_func: "theory -> thm -> typ"} \\
  @{index_ML CodegenData.rewrite_func: "thm list -> thm -> thm"} \\
  \end{mldecls}
*}

subsection {* Implementing code generator applications *}

text {*
  \begin{warn}
    Some interfaces discussed here have not reached
    a final state yet.
    Changes likely to occur in future.
  \end{warn}
*}

subsubsection {* Data depending on the theory's executable content *}

subsubsection {* Datatype hooks *}

text {*
  \emph{Happy proving, happy hacking!}
*}

end
