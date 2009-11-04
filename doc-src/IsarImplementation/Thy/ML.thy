theory "ML"
imports Base
begin

chapter {* Advanced ML programming *}

section {* Style *}

text {*
  Like any style guide, also this one should not be interpreted dogmatically, but
  with care and discernment.  It consists of a collection of
  recommendations which have been turned out useful over long years of
  Isabelle system development and are supposed to support writing of readable
  and managable code.  Special cases encourage derivations,
  as far as you know what you are doing.
  \footnote{This style guide is loosely based on
  \url{http://caml.inria.fr/resources/doc/guides/guidelines.en.html}}

  \begin{description}

    \item[fundamental law of programming]
      Whenever writing code, keep in mind: A program is
      written once, modified ten times, and read
      hundred times.  So simplify its writing,
      always keep future modifications in mind,
      and never jeopardize readability.  Every second you hesitate
      to spend on making your code more clear you will
      have to spend ten times understanding what you have
      written later on.

    \item[white space matters]
      Treat white space in your code as if it determines
      the meaning of code.

      \begin{itemize}

        \item The space bar is the easiest key to find on the keyboard,
          press it as often as necessary. @{verbatim "2 + 2"} is better
          than @{verbatim "2+2"}, likewise @{verbatim "f (x, y)"} is
          better than @{verbatim "f(x,y)"}.

        \item Restrict your lines to 80 characters.  This will allow
          you to keep the beginning of a line in view while watching
          its end.\footnote{To acknowledge the lax practice of
          text editing these days, we tolerate as much as 100
          characters per line, but anything beyond 120 is not
          considered proper source text.}

        \item Ban tabulators; they are a context-sensitive formatting
          feature and likely to confuse anyone not using your favorite
          editor.\footnote{Some modern programming language even
          forbid tabulators altogether according to the formal syntax
          definition.}

        \item Get rid of trailing whitespace.  Instead, do not
          suppress a trailing newline at the end of your files.

        \item Choose a generally accepted style of indentation,
          then use it systematically throughout the whole
          application.  An indentation of two spaces is appropriate.
          Avoid dangling indentation.

      \end{itemize}

    \item[cut-and-paste succeeds over copy-and-paste]
       \emph{Never} copy-and-paste code when programming.  If you
        need the same piece of code twice, introduce a
        reasonable auxiliary function (if there is no
        such function, very likely you got something wrong).
        Any copy-and-paste will turn out to be painful 
        when something has to be changed later on.

    \item[comments]
      are a device which requires careful thinking before using
      it.  The best comment for your code should be the code itself.
      Prefer efforts to write clear, understandable code
      over efforts to explain nasty code.

    \item[functional programming is based on functions]
      Model things as abstract as appropriate.  Avoid unnecessarrily
      concrete datatype  representations.  For example, consider a function
      taking some table data structure as argument and performing
      lookups on it.  Instead of taking a table, it could likewise
      take just a lookup function.  Accustom
      your way of coding to the level of expressiveness a functional
      programming language is giving onto you.

    \item[tuples]
      are often in the way.  When there is no striking argument
      to tuple function arguments, just write your function curried.

    \item[telling names]
      Any name should tell its purpose as exactly as possible, while
      keeping its length to the absolutely necessary minimum.  Always
      give the same name to function arguments which have the same
      meaning. Separate words by underscores (@{verbatim
      int_of_string}, not @{verbatim intOfString}).\footnote{Some
      recent tools for Emacs include special precautions to cope with
      bumpy names in @{text "camelCase"}, e.g.\ for improved on-screen
      readability.  It is easier to abstain from using such names in the
      first place.}

  \end{description}
*}


section {* Thread-safe programming *}

text {*
  Recent versions of Poly/ML (5.2.1 or later) support robust
  multithreaded execution, based on native operating system threads of
  the underlying platform.  Thus threads will actually be executed in
  parallel on multi-core systems.  A speedup-factor of approximately
  1.5--3 can be expected on a regular 4-core machine.\footnote{There
  is some inherent limitation of the speedup factor due to garbage
  collection, which is still sequential.  It helps to provide initial
  heap space generously, using the \texttt{-H} option of Poly/ML.}
  Threads also help to organize advanced operations of the system,
  with explicit communication between sub-components, real-time
  conditions, time-outs etc.

  Threads lack the memory protection of separate processes, and
  operate concurrently on shared heap memory.  This has the advantage
  that results of independent computations are immediately available
  to other threads, without requiring untyped character streams,
  awkward serialization etc.

  On the other hand, some programming guidelines need to be observed
  in order to make unprotected parallelism work out smoothly.  While
  the ML system implementation is responsible to maintain basic
  integrity of the representation of ML values in memory, the
  application programmer needs to ensure that multithreaded execution
  does not break the intended semantics.

  \medskip \paragraph{Critical shared resources.} Actually only those
  parts outside the purely functional world of ML are critical.  In
  particular, this covers

  \begin{itemize}

  \item global references (or arrays), i.e.\ those that persist over
  several invocations of associated operations,\footnote{This is
  independent of the visibility of such mutable values in the toplevel
  scope.}

  \item direct I/O on shared channels, notably @{text "stdin"}, @{text
  "stdout"}, @{text "stderr"}.

  \end{itemize}

  The majority of tools implemented within the Isabelle/Isar framework
  will not require any of these critical elements: nothing special
  needs to be observed when staying in the purely functional fragment
  of ML.  Note that output via the official Isabelle channels does not
  count as direct I/O, so the operations @{ML "writeln"}, @{ML
  "warning"}, @{ML "tracing"} etc.\ are safe.

  Moreover, ML bindings within the toplevel environment (@{verbatim
  "type"}, @{verbatim val}, @{verbatim "structure"} etc.) due to
  run-time invocation of the compiler are also safe, because
  Isabelle/Isar manages this as part of the theory or proof context.

  \paragraph{Multithreading in Isabelle/Isar.}  The theory loader
  automatically exploits the overall parallelism of independent nodes
  in the development graph, as well as the inherent irrelevance of
  proofs for goals being fully specified in advance.  This means,
  checking of individual Isar proofs is parallelized by default.
  Beyond that, very sophisticated proof tools may use local
  parallelism internally, via the general programming model of
  ``future values'' (see also @{"file"
  "~~/src/Pure/Concurrent/future.ML"}).

  Any ML code that works relatively to the present background theory
  is already safe.  Contextual data may be easily stored within the
  theory or proof context, thanks to the generic data concept of
  Isabelle/Isar (see \secref{sec:context-data}).  This greatly
  diminishes the demand for global state information in the first
  place.

  \medskip In rare situations where actual mutable content needs to be
  manipulated, Isabelle provides a single \emph{critical section} that
  may be entered while preventing any other thread from doing the
  same.  Entering the critical section without contention is very
  fast, and several basic system operations do so frequently.  This
  also means that each thread should leave the critical section
  quickly, otherwise parallel execution performance may degrade
  significantly.

  Despite this potential bottle-neck, centralized locking is
  convenient, because it prevents deadlocks without demanding special
  precautions.  Explicit communication demands other means, though.
  The high-level abstraction of synchronized variables @{"file"
  "~~/src/Pure/Concurrent/synchronized.ML"} enables parallel
  components to communicate via shared state; see also @{"file"
  "~~/src/Pure/Concurrent/mailbox.ML"} as canonical example.

  \paragraph{Good conduct of impure programs.} The following
  guidelines enable non-functional programs to participate in
  multithreading.

  \begin{itemize}

  \item Minimize global state information.  Using proper theory and
  proof context data will actually return to functional update of
  values, without any special precautions for multithreading.  Apart
  from the fully general functors for theory and proof data (see
  \secref{sec:context-data}) there are drop-in replacements that
  emulate primitive references for common cases of \emph{configuration
  options} for type @{ML_type "bool"}/@{ML_type "int"}/@{ML_type
  "string"} (see structure @{ML_struct Config} and @{ML
  Attrib.config_bool} etc.), and lists of theorems (see functor
  @{ML_functor NamedThmsFun}).

  \item Keep components with local state information
  \emph{re-entrant}.  Instead of poking initial values into (private)
  global references, create a new state record on each invocation, and
  pass that through any auxiliary functions of the component.  The
  state record may well contain mutable references, without requiring
  any special synchronizations, as long as each invocation sees its
  own copy.  Occasionally, one might even return to plain functional
  updates on non-mutable record values here.

  \item Isolate process configuration flags.  The main legitimate
  application of global references is to configure the whole process
  in a certain way, essentially affecting all threads.  A typical
  example is the @{ML show_types} flag, which tells the pretty printer
  to output explicit type information for terms.  Such flags usually
  do not affect the functionality of the core system, but only the
  view being presented to the user.

  Occasionally, such global process flags are treated like implicit
  arguments to certain operations, by using the @{ML setmp_CRITICAL} combinator
  for safe temporary assignment.  Its traditional purpose was to
  ensure proper recovery of the original value when exceptions are
  raised in the body, now the functionality is extended to enter the
  \emph{critical section} (with its usual potential of degrading
  parallelism).

  Note that recovery of plain value passing semantics via @{ML
  setmp_CRITICAL}~@{text "ref value"} assumes that this @{text "ref"} is
  exclusively manipulated within the critical section.  In particular,
  any persistent global assignment of @{text "ref := value"} needs to
  be marked critical as well, to prevent intruding another threads
  local view, and a lost-update in the global scope, too.

  \end{itemize}

  Recall that in an open ``LCF-style'' system like Isabelle/Isar, the
  user participates in constructing the overall environment.  This
  means that state-based facilities offered by one component will
  require special caution later on.  So minimizing critical elements,
  by staying within the plain value-oriented view relative to theory
  or proof contexts most of the time, will also reduce the chance of
  mishaps occurring to end-users.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML NAMED_CRITICAL: "string -> (unit -> 'a) -> 'a"} \\
  @{index_ML CRITICAL: "(unit -> 'a) -> 'a"} \\
  @{index_ML setmp_CRITICAL: "'a Unsynchronized.ref -> 'a -> ('b -> 'c) -> 'b -> 'c"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML NAMED_CRITICAL}~@{text "name f"} evaluates @{text "f ()"}
  while staying within the critical section of Isabelle/Isar.  No
  other thread may do so at the same time, but non-critical parallel
  execution will continue.  The @{text "name"} argument serves for
  diagnostic purposes and might help to spot sources of congestion.

  \item @{ML CRITICAL} is the same as @{ML NAMED_CRITICAL} with empty
  name argument.

  \item @{ML setmp_CRITICAL}~@{text "ref value f x"} evaluates @{text "f x"}
  while staying within the critical section and having @{text "ref :=
  value"} assigned temporarily.  This recovers a value-passing
  semantics involving global references, regardless of exceptions or
  concurrency.

  \end{description}
*}


chapter {* Basic library functions *}

text {*
  Beyond the proposal of the SML/NJ basis library, Isabelle comes
  with its own library, from which selected parts are given here.
  These should encourage a study of the Isabelle sources,
  in particular files \emph{Pure/library.ML} and \emph{Pure/General/*.ML}.
*}

section {* Linear transformations \label{sec:ML-linear-trans} *}

text %mlref {*
  \begin{mldecls}
  @{index_ML "op |> ": "'a * ('a -> 'b) -> 'b"} \\
  \end{mldecls}
*}

(*<*)
typedecl foo
consts foo :: foo
ML {*
val thy = Theory.copy @{theory}
*}
(*>*)

text {*
  \noindent Many problems in functional programming can be thought of
  as linear transformations, i.e.~a caluclation starts with a
  particular value @{ML_text "x : foo"} which is then transformed
  by application of a function @{ML_text "f : foo -> foo"},
  continued by an application of a function @{ML_text "g : foo -> bar"},
  and so on.  As a canoncial example, take functions enriching
  a theory by constant declararion and primitive definitions:

  \smallskip\begin{mldecls}
  @{ML "Sign.declare_const: (binding * typ) * mixfix
  -> theory -> term * theory"} \\
  @{ML "Thm.add_def: bool -> bool -> binding * term -> theory -> thm * theory"}
  \end{mldecls}

  \noindent Written with naive application, an addition of constant
  @{term bar} with type @{typ "foo \<Rightarrow> foo"} and
  a corresponding definition @{term "bar \<equiv> \<lambda>x. x"} would look like:

  \smallskip\begin{mldecls}
  @{ML "(fn (t, thy) => Thm.add_def false false
  (Binding.name \"bar_def\", Logic.mk_equals (t, @{term \"%x. x\"})) thy)
    (Sign.declare_const
      ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn) thy)"}
  \end{mldecls}

  \noindent With increasing numbers of applications, this code gets quite
  unreadable.  Further, it is unintuitive that things are
  written down in the opposite order as they actually ``happen''.
*}

text {*
  \noindent At this stage, Isabelle offers some combinators which allow
  for more convenient notation, most notably reverse application:

  \smallskip\begin{mldecls}
@{ML "thy
|> Sign.declare_const ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn)
|> (fn (t, thy) => thy
|> Thm.add_def false false
     (Binding.name \"bar_def\", Logic.mk_equals (t, @{term \"%x. x\"})))"}
  \end{mldecls}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML "op |-> ": "('c * 'a) * ('c -> 'a -> 'b) -> 'b"} \\
  @{index_ML "op |>> ": "('a * 'c) * ('a -> 'b) -> 'b * 'c"} \\
  @{index_ML "op ||> ": "('c * 'a) * ('a -> 'b) -> 'c * 'b"} \\
  @{index_ML "op ||>> ": "('c * 'a) * ('a -> 'd * 'b) -> ('c * 'd) * 'b"} \\
  \end{mldecls}
*}

text {*
  \noindent Usually, functions involving theory updates also return
  side results; to use these conveniently, yet another
  set of combinators is at hand, most notably @{ML "op |->"}
  which allows curried access to side results:

  \smallskip\begin{mldecls}
@{ML "thy
|> Sign.declare_const ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn)
|-> (fn t => Thm.add_def false false
      (Binding.name \"bar_def\", Logic.mk_equals (t, @{term \"%x. x\"})))
"}
  \end{mldecls}

  \noindent @{ML "op |>>"} allows for processing side results on their own:

  \smallskip\begin{mldecls}
@{ML "thy
|> Sign.declare_const ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn)
|>> (fn t => Logic.mk_equals (t, @{term \"%x. x\"}))
|-> (fn def => Thm.add_def false false (Binding.name \"bar_def\", def))
"}
  \end{mldecls}

  \noindent Orthogonally, @{ML "op ||>"} applies a transformation
  in the presence of side results which are left unchanged:

  \smallskip\begin{mldecls}
@{ML "thy
|> Sign.declare_const ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn)
||> Sign.add_path \"foobar\"
|-> (fn t => Thm.add_def false false
      (Binding.name \"bar_def\", Logic.mk_equals (t, @{term \"%x. x\"})))
||> Sign.restore_naming thy
"}
  \end{mldecls}

  \noindent @{ML "op ||>>"} accumulates side results:

  \smallskip\begin{mldecls}
@{ML "thy
|> Sign.declare_const ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn)
||>> Sign.declare_const ((Binding.name \"foobar\", @{typ \"foo => foo\"}), NoSyn)
|-> (fn (t1, t2) => Thm.add_def false false
      (Binding.name \"bar_def\", Logic.mk_equals (t1, t2)))
"}
  \end{mldecls}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML fold: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  @{index_ML fold_map: "('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b"} \\
  \end{mldecls}
*}

text {*
  \noindent This principles naturally lift to \emph{lists} using
  the @{ML fold} and @{ML fold_map} combinators.
  The first lifts a single function
  \begin{quote}\footnotesize
    @{ML_text "f : 'a -> 'b -> 'b"} to @{ML_text "'a list -> 'b -> 'b"}
  \end{quote}
  such that
  \begin{quote}\footnotesize
    @{ML_text "y |> fold f [x1, x2, ..., x_n]"} \\
    \hspace*{2ex}@{text "\<leadsto>"} @{ML_text "y |> f x1 |> f x2 |> ... |> f x_n"}
  \end{quote}
  \noindent The second accumulates side results in a list by lifting
  a single function
  \begin{quote}\footnotesize
    @{ML_text "f : 'a -> 'b -> 'c * 'b"} to @{ML_text "'a list -> 'b -> 'c list * 'b"}
  \end{quote}
  such that
  \begin{quote}\footnotesize
    @{ML_text "y |> fold_map f [x1, x2, ..., x_n]"} \\
    \hspace*{2ex}@{text "\<leadsto>"} @{ML_text "y |> f x1 ||>> f x2 ||>> ... ||>> f x_n"} \\
    \hspace*{6ex}@{ML_text "||> (fn ((z1, z2), ..., z_n) => [z1, z2, ..., z_n])"}
  \end{quote}
  
  \noindent Example:

  \smallskip\begin{mldecls}
@{ML "let
  val consts = [\"foo\", \"bar\"];
in
  thy
  |> fold_map (fn const => Sign.declare_const
       ((Binding.name const, @{typ \"foo => foo\"}), NoSyn)) consts
  |>> map (fn t => Logic.mk_equals (t, @{term \"%x. x\"}))
  |-> (fn defs => fold_map (fn def =>
       Thm.add_def false false (Binding.empty, def)) defs)
end"}
  \end{mldecls}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML "op #> ": "('a -> 'b) * ('b -> 'c) -> 'a -> 'c"} \\
  @{index_ML "op #-> ": "('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd"} \\
  @{index_ML "op #>> ": "('a -> 'c * 'b) * ('c -> 'd) -> 'a -> 'd * 'b"} \\
  @{index_ML "op ##> ": "('a -> 'c * 'b) * ('b -> 'd) -> 'a -> 'c * 'd"} \\
  @{index_ML "op ##>> ": "('a -> 'c * 'b) * ('b -> 'e * 'd) -> 'a -> ('c * 'e) * 'd"} \\
  \end{mldecls}
*}

text {*
  \noindent All those linear combinators also exist in higher-order
  variants which do not expect a value on the left hand side
  but a function.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML "op ` ": "('b -> 'a) -> 'b -> 'a * 'b"} \\
  @{index_ML tap: "('b -> 'a) -> 'b -> 'b"} \\
  \end{mldecls}
*}

text {*
  \noindent These operators allow to ``query'' a context
  in a series of context transformations:

  \smallskip\begin{mldecls}
@{ML "thy
|> tap (fn _ => writeln \"now adding constant\")
|> Sign.declare_const ((Binding.name \"bar\", @{typ \"foo => foo\"}), NoSyn)
||>> `(fn thy => Sign.declared_const thy
         (Sign.full_name thy (Binding.name \"foobar\")))
|-> (fn (t, b) => if b then I
       else Sign.declare_const
         ((Binding.name \"foobar\", @{typ \"foo => foo\"}), NoSyn) #> snd)
"}
  \end{mldecls}
*}

section {* Options and partiality *}

text %mlref {*
  \begin{mldecls}
  @{index_ML is_some: "'a option -> bool"} \\
  @{index_ML is_none: "'a option -> bool"} \\
  @{index_ML the: "'a option -> 'a"} \\
  @{index_ML these: "'a list option -> 'a list"} \\
  @{index_ML the_list: "'a option -> 'a list"} \\
  @{index_ML the_default: "'a -> 'a option -> 'a"} \\
  @{index_ML try: "('a -> 'b) -> 'a -> 'b option"} \\
  @{index_ML can: "('a -> 'b) -> 'a -> bool"} \\
  \end{mldecls}
*}

text {*
  Standard selector functions on @{text option}s are provided.  The
  @{ML try} and @{ML can} functions provide a convenient interface for
  handling exceptions -- both take as arguments a function @{ML_text f}
  together with a parameter @{ML_text x} and handle any exception during
  the evaluation of the application of @{ML_text f} to @{ML_text x}, either
  return a lifted result (@{ML NONE} on failure) or a boolean value
  (@{ML false} on failure).
*}


section {* Common data structures *}

subsection {* Lists (as set-like data structures) *}

text {*
  \begin{mldecls}
  @{index_ML member: "('b * 'a -> bool) -> 'a list -> 'b -> bool"} \\
  @{index_ML insert: "('a * 'a -> bool) -> 'a -> 'a list -> 'a list"} \\
  @{index_ML remove: "('b * 'a -> bool) -> 'b -> 'a list -> 'a list"} \\
  @{index_ML merge: "('a * 'a -> bool) -> 'a list * 'a list -> 'a list"} \\
  \end{mldecls}
*}

text {*
  Lists are often used as set-like data structures -- set-like in
  the sense that they support a notion of @{ML member}-ship,
  @{ML insert}-ing and @{ML remove}-ing, but are order-sensitive.
  This is convenient when implementing a history-like mechanism:
  @{ML insert} adds an element \emph{to the front} of a list,
  if not yet present; @{ML remove} removes \emph{all} occurences
  of a particular element.  Correspondingly @{ML merge} implements a 
  a merge on two lists suitable for merges of context data
  (\secref{sec:context-theory}).

  Functions are parametrized by an explicit equality function
  to accomplish overloaded equality;  in most cases of monomorphic
  equality, writing @{ML "op ="} should suffice.
*}

subsection {* Association lists *}

text {*
  \begin{mldecls}
  @{index_ML_exn AList.DUP} \\
  @{index_ML AList.lookup: "('a * 'b -> bool) -> ('b * 'c) list -> 'a -> 'c option"} \\
  @{index_ML AList.defined: "('a * 'b -> bool) -> ('b * 'c) list -> 'a -> bool"} \\
  @{index_ML AList.update: "('a * 'a -> bool) -> ('a * 'b) -> ('a * 'b) list -> ('a * 'b) list"} \\
  @{index_ML AList.default: "('a * 'a -> bool) -> ('a * 'b) -> ('a * 'b) list -> ('a * 'b) list"} \\
  @{index_ML AList.delete: "('a * 'b -> bool) -> 'a -> ('b * 'c) list -> ('b * 'c) list"} \\
  @{index_ML AList.map_entry: "('a * 'b -> bool) -> 'a
    -> ('c -> 'c) -> ('b * 'c) list -> ('b * 'c) list"} \\
  @{index_ML AList.map_default: "('a * 'a -> bool) -> 'a * 'b -> ('b -> 'b)
    -> ('a * 'b) list -> ('a * 'b) list"} \\
  @{index_ML AList.join: "('a * 'a -> bool) -> ('a -> 'b * 'b -> 'b) (*exception DUP*)
    -> ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list (*exception AList.DUP*)"} \\
  @{index_ML AList.merge: "('a * 'a -> bool) -> ('b * 'b -> bool)
    -> ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list (*exception AList.DUP*)"}
  \end{mldecls}
*}

text {*
  Association lists can be seens as an extension of set-like lists:
  on the one hand, they may be used to implement finite mappings,
  on the other hand, they remain order-sensitive and allow for
  multiple key-value-pair with the same key: @{ML AList.lookup}
  returns the \emph{first} value corresponding to a particular
  key, if present.  @{ML AList.update} updates
  the \emph{first} occurence of a particular key; if no such
  key exists yet, the key-value-pair is added \emph{to the front}.
  @{ML AList.delete} only deletes the \emph{first} occurence of a key.
  @{ML AList.merge} provides an operation suitable for merges of context data
  (\secref{sec:context-theory}), where an equality parameter on
  values determines whether a merge should be considered a conflict.
  A slightly generalized operation if implementend by the @{ML AList.join}
  function which allows for explicit conflict resolution.
*}

subsection {* Tables *}

text {*
  \begin{mldecls}
  @{index_ML_type "'a Symtab.table"} \\
  @{index_ML_exn Symtab.DUP: string} \\
  @{index_ML_exn Symtab.SAME} \\
  @{index_ML_exn Symtab.UNDEF: string} \\
  @{index_ML Symtab.empty: "'a Symtab.table"} \\
  @{index_ML Symtab.lookup: "'a Symtab.table -> string -> 'a option"} \\
  @{index_ML Symtab.defined: "'a Symtab.table -> string -> bool"} \\
  @{index_ML Symtab.update: "(string * 'a) -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.default: "string * 'a -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.delete: "string
    -> 'a Symtab.table -> 'a Symtab.table (*exception Symtab.UNDEF*)"} \\
  @{index_ML Symtab.map_entry: "string -> ('a -> 'a)
    -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.map_default: "(string * 'a) -> ('a -> 'a)
    -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.join: "(string -> 'a * 'a -> 'a) (*exception Symtab.DUP/Symtab.SAME*)
    -> 'a Symtab.table * 'a Symtab.table
    -> 'a Symtab.table (*exception Symtab.DUP*)"} \\
  @{index_ML Symtab.merge: "('a * 'a -> bool)
    -> 'a Symtab.table * 'a Symtab.table
    -> 'a Symtab.table (*exception Symtab.DUP*)"}
  \end{mldecls}
*}

text {*
  Tables are an efficient representation of finite mappings without
  any notion of order;  due to their efficiency they should be used
  whenever such pure finite mappings are neccessary.

  The key type of tables must be given explicitly by instantiating
  the @{ML_functor TableFun} functor which takes the key type
  together with its @{ML_type order}; for convience, we restrict
  here to the @{ML_struct Symtab} instance with @{ML_type string}
  as key type.

  Most table functions correspond to those of association lists.
*}

end