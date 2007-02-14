(* $Id$ *)

theory "ML" imports base begin

chapter {* Aesthetics of ML programming *}

text FIXME

text {* This style guide is loosely based on
  \url{http://caml.inria.fr/resources/doc/guides/guidelines.en.html}.
%  FIMXE \url{http://www.cs.cornell.edu/Courses/cs312/2003sp/handouts/style.htm}

  Like any style guide, it should not be interpreted dogmatically.
  Instead, it forms a collection of recommendations which,
  if obeyed, result in code that is not considered to be
  obfuscated.  In certain cases, derivations are encouraged,
  as far as you know what you are doing.

  \begin{description}

    \item[fundamental law of programming]
      Whenever writing code, keep in mind: A program is
      written once, modified ten times, and read
      100 times.  So simplify its writing,
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
          press it as often as necessary. {\ttfamily 2 + 2} is better
          than {\ttfamily 2+2}, likewise {\ttfamily f (x, y)}
          better than {\ttfamily f(x,y)}.

        \item Restrict your lines to \emph{at most} 80 characters.
          This will allow you to keep the beginning of a line
          in view while watching its end.

        \item Ban tabs; they are a context-sensitive formatting
          feature and likely to confuse anyone not using your
          favourite editor.

        \item Get rid of trailing whitespace.  Instead, do not
          surpess a trailing newline at the end of your files.

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
        when something has to be changed or fixed later on.

    \item[comments]
      are a device which requires careful thinking before using
      it.  The best comment for your code should be the code itself.
      Prefer efforts to write clear, understandable code
      over efforts to explain nasty code.

    \item[functional programming is based on functions]
      Avoid ``constructivisms'', e.g. pass a table lookup function,
      rather than an actual table with lookup in body.  Accustom
      your way of codeing to the level of expressiveness
      a functional programming language is giving onto you.

    \item[tuples]
      are often in the way.  When there is no striking argument
      to tuple function arguments, just write your function curried.

    \item[telling names]
      Any name should tell its purpose as exactly as possible,
      while keeping its length to the absolutely neccessary minimum.
      Always give the same name to function arguments which
      have the same meaning. Separate words by underscores
      (``@{verbatim int_of_string}'', not ``@{verbatim intOfString}'')

  \end{description}
*}


chapter {* Basic library functions *}

text {*
  Beyond the proposal of the SML/NJ basis library, Isabelle comes
  with its own library, from which selected parts are given here.
  See further files \emph{Pure/library.ML} and \emph{Pure/General/*.ML}.
*}

section {* Linear transformations *}

text %mlref {*
  \begin{mldecls}
  @{index_ML "(op |>)": "'a * ('a -> 'b) -> 'b"} \\
  @{index_ML fold: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  @{index_ML fold_rev: "('a -> 'b -> 'b) -> 'a list -> 'b -> 'b"} \\
  \end{mldecls}
*}

(*<*)
typedecl foo
consts foo :: foo
ML {*
val dummy_const = ("bar", @{typ foo}, NoSyn)
val dummy_def = ("bar", @{term foo})
val thy = Theory.copy @{theory}
*}
(*>*)

text {*
  Many problems in functional programming can be thought of
  as linear transformations, i.e.~a caluclation starts with a
  particular value @{text "x \<Colon> foo"} which is then transformed
  by application of a function @{text "f \<Colon> foo \<Rightarrow> foo"},
  continued by an application of a function @{text "g \<Colon> foo \<Rightarrow> bar"},
  and so on.  As a canoncial example, take primitive functions enriching
  theories by constants and definitions:
  @{ML "Sign.add_consts_i: (string * typ * mixfix) list -> theory -> theory"}
  and @{ML "Theory.add_defs_i: bool -> bool -> (bstring * term) list -> theory -> theory"}.
  Written with naive application, an addition of a constant with
  a corresponding definition would look like:
  @{ML "Theory.add_defs_i false false [dummy_def] (Sign.add_consts_i [dummy_const] thy)"}
  With increasing numbers of applications, this code gets quite unreadable.
  Using composition, at least the nesting of brackets may be reduced:
  @{ML "(Theory.add_defs_i false false [dummy_def] o Sign.add_consts_i [dummy_const]) thy"}
  What remains unsatisfactory is that things are written down in the opposite order
  as they actually ``happen''.
*}

(*<*)
ML {*
val thy = Theory.copy @{theory}
*}
(*>*)

text {*
  At this stage, Isabelle offers some combinators which allow for more convenient
  notation, most notably reverse application:
  @{ML "
thy
|> Sign.add_consts_i [dummy_const]
|> Theory.add_defs_i false false [dummy_def]"}
*}

text {*
  When iterating over a list of parameters @{text "[x\<^isub>1, x\<^isub>2, \<dots> x\<^isub>n] \<Colon> 'a list"},
  the @{ML fold} combinator lifts a single function @{text "f \<Colon> 'a -> 'b -> 'b"}:
  @{text "y |> fold f [x\<^isub>1, x\<^isub>2, \<dots> x\<^isub>n] \<equiv> y |> f x\<^isub>1 |> f x\<^isub>2 |> \<dots> |> f x\<^isub>n"}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML "(op |->)": "('c * 'a) * ('c -> 'a -> 'b) -> 'b"} \\
  @{index_ML "(op |>>)": "('a * 'c) * ('a -> 'b) -> 'b * 'c"} \\
  @{index_ML "(op ||>)": "('c * 'a) * ('a -> 'b) -> 'c * 'b"} \\
  @{index_ML "(op ||>>)": "('c * 'a) * ('a -> 'd * 'b) -> ('c * 'd) * 'b"} \\
  @{index_ML fold_map: "('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b"} \\
  \end{mldecls}
*}

text {*
  FIXME transformations involving side results
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML "(op #>)": "('a -> 'b) * ('b -> 'c) -> 'a -> 'c"} \\
  @{index_ML "(op #->)": "('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd"} \\
  @{index_ML "(op #>>)": "('a -> 'c * 'b) * ('c -> 'd) -> 'a -> 'd * 'b"} \\
  @{index_ML "(op ##>)": "('a -> 'c * 'b) * ('b -> 'd) -> 'a -> 'c * 'd"} \\
  @{index_ML "(op ##>>)": "('a -> 'c * 'b) * ('b -> 'e * 'd) -> 'a -> ('c * 'e) * 'd"} \\
  \end{mldecls}
*}

text {*
  FIXME higher-order variants
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML "(op `)": "('b -> 'a) -> 'b -> 'a * 'b"} \\
  @{index_ML tap: "('b -> 'a) -> 'b -> 'b"} \\
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

text FIXME

section {* Common data structures *}

text "FIXME chronicle"

subsection {* Lists (as set-like data structures) *}

text {*
  \begin{mldecls}
  @{index_ML member: "('b * 'a -> bool) -> 'a list -> 'b -> bool"} \\
  @{index_ML insert: "('a * 'a -> bool) -> 'a -> 'a list -> 'a list"} \\
  @{index_ML remove: "('b * 'a -> bool) -> 'b -> 'a list -> 'a list"} \\
  @{index_ML merge: "('a * 'a -> bool) -> 'a list * 'a list -> 'a list"} \\
  \end{mldecls}
*}

text FIXME

subsection {* Association lists *}

text {*
  \begin{mldecls}
  @{index_ML_exc AList.DUP} \\
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

text FIXME

subsection {* Tables *}

text {*
  \begin{mldecls}
  @{index_ML_type Symtab.key} \\
  @{index_ML_type "'a Symtab.table"} \\
  @{index_ML_exc Symtab.DUP: Symtab.key} \\
  @{index_ML_exc Symtab.DUPS: "Symtab.key list"} \\
  @{index_ML_exc Symtab.SAME} \\
  @{index_ML_exc Symtab.UNDEF: Symtab.key} \\
  @{index_ML Symtab.empty: "'a Symtab.table"} \\
  @{index_ML Symtab.dest: "'a Symtab.table -> (Symtab.key * 'a) list"} \\
  @{index_ML Symtab.keys: "'a Symtab.table -> Symtab.key list"} \\
  @{index_ML Symtab.lookup: "'a Symtab.table -> Symtab.key -> 'a option"} \\
  @{index_ML Symtab.defined: "'a Symtab.table -> Symtab.key -> bool"} \\
  @{index_ML Symtab.update: "(Symtab.key * 'a) -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.default: "Symtab.key * 'a -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.delete: "Symtab.key
    -> 'a Symtab.table -> 'a Symtab.table (*exception Symtab.UNDEF*)"} \\
  @{index_ML Symtab.map_entry: "Symtab.key -> ('a -> 'a)
    -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.map_default: "(Symtab.key * 'a) -> ('a -> 'a)
    -> 'a Symtab.table -> 'a Symtab.table"} \\
  @{index_ML Symtab.join: "(Symtab.key -> 'a * 'a -> 'a) (*exception Symtab.DUP/Symtab.SAME*)
    -> 'a Symtab.table * 'a Symtab.table
    -> 'a Symtab.table (*exception Symtab.DUPS*)"} \\
  @{index_ML Symtab.merge: "('a * 'a -> bool)
    -> 'a Symtab.table * 'a Symtab.table
    -> 'a Symtab.table (*exception Symtab.DUPS*)"}
  \end{mldecls}
*}

text FIXME

chapter {* Cookbook *}

section {* A method that depends on declarations in the context *}

text FIXME

end
