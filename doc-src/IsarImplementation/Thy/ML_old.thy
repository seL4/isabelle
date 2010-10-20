theory ML_old
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
  @{ML "Thm.add_def: bool -> bool -> binding * term -> theory -> (string * thm) * theory"}
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

end