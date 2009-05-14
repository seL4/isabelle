theory "ML"
imports Setup
begin

section {* ML system interfaces \label{sec:ml} *}

text {*
  Since the code generator framework not only aims to provide
  a nice Isar interface but also to form a base for
  code-generation-based applications, here a short
  description of the most important ML interfaces.
*}

subsection {* Executable theory content: @{text Code} *}

text {*
  This Pure module implements the core notions of
  executable content of a theory.
*}

subsubsection {* Managing executable content *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Code.add_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code.del_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code.add_eqnl: "string * (thm * bool) list lazy -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_pre: "(simpset -> simpset) -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_post: "(simpset -> simpset) -> theory -> theory"} \\
  @{index_ML Code_Preproc.add_functrans: "string * (theory -> (thm * bool) list -> (thm * bool) list option)
    -> theory -> theory"} \\
  @{index_ML Code_Preproc.del_functrans: "string -> theory -> theory"} \\
  @{index_ML Code.add_datatype: "(string * typ) list -> theory -> theory"} \\
  @{index_ML Code.get_datatype: "theory -> string
    -> (string * sort) list * (string * typ list) list"} \\
  @{index_ML Code.get_datatype_of_constr: "theory -> string -> string option"}
  \end{mldecls}

  \begin{description}

  \item @{ML Code.add_eqn}~@{text "thm"}~@{text "thy"} adds function
     theorem @{text "thm"} to executable content.

  \item @{ML Code.del_eqn}~@{text "thm"}~@{text "thy"} removes function
     theorem @{text "thm"} from executable content, if present.

  \item @{ML Code.add_eqnl}~@{text "(const, lthms)"}~@{text "thy"} adds
     suspended code equations @{text lthms} for constant
     @{text const} to executable content.

  \item @{ML Code_Preproc.map_pre}~@{text "f"}~@{text "thy"} changes
     the preprocessor simpset.

  \item @{ML Code_Preproc.add_functrans}~@{text "(name, f)"}~@{text "thy"} adds
     function transformer @{text f} (named @{text name}) to executable content;
     @{text f} is a transformer of the code equations belonging
     to a certain function definition, depending on the
     current theory context.  Returning @{text NONE} indicates that no
     transformation took place;  otherwise, the whole process will be iterated
     with the new code equations.

  \item @{ML Code_Preproc.del_functrans}~@{text "name"}~@{text "thy"} removes
     function transformer named @{text name} from executable content.

  \item @{ML Code.add_datatype}~@{text cs}~@{text thy} adds
     a datatype to executable content, with generation
     set @{text cs}.

  \item @{ML Code.get_datatype_of_constr}~@{text "thy"}~@{text "const"}
     returns type constructor corresponding to
     constructor @{text const}; returns @{text NONE}
     if @{text const} is no constructor.

  \end{description}
*}

subsection {* Auxiliary *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Code.read_const: "theory -> string -> string"} \\
  @{index_ML Code.rewrite_eqn: "simpset -> thm -> thm"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Code.read_const}~@{text thy}~@{text s}
     reads a constant as a concrete term expression @{text s}.

  \item @{ML Code.rewrite_eqn}~@{text ss}~@{text thm}
     rewrites a code equation @{text thm} with a simpset @{text ss};
     only arguments and right hand side are rewritten,
     not the head of the code equation.

  \end{description}

*}

subsection {* Implementing code generator applications *}

text {*
  Implementing code generator applications on top
  of the framework set out so far usually not only
  involves using those primitive interfaces
  but also storing code-dependent data and various
  other things.
*}

subsubsection {* Data depending on the theory's executable content *}

text {*
  Due to incrementality of code generation, changes in the
  theory's executable content have to be propagated in a
  certain fashion.  Additionally, such changes may occur
  not only during theory extension but also during theory
  merge, which is a little bit nasty from an implementation
  point of view.  The framework provides a solution
  to this technical challenge by providing a functorial
  data slot @{ML_functor CodeDataFun}; on instantiation
  of this functor, the following types and operations
  are required:

  \medskip
  \begin{tabular}{l}
  @{text "type T"} \\
  @{text "val empty: T"} \\
  @{text "val purge: theory \<rightarrow> string list option \<rightarrow> T \<rightarrow> T"}
  \end{tabular}

  \begin{description}

  \item @{text T} the type of data to store.

  \item @{text empty} initial (empty) data.

  \item @{text purge}~@{text thy}~@{text consts} propagates changes in executable content;
    @{text consts} indicates the kind
    of change: @{ML NONE} stands for a fundamental change
    which invalidates any existing code, @{text "SOME consts"}
    hints that executable content for constants @{text consts}
    has changed.

  \end{description}

  \noindent An instance of @{ML_functor CodeDataFun} provides the following
  interface:

  \medskip
  \begin{tabular}{l}
  @{text "get: theory \<rightarrow> T"} \\
  @{text "change: theory \<rightarrow> (T \<rightarrow> T) \<rightarrow> T"} \\
  @{text "change_yield: theory \<rightarrow> (T \<rightarrow> 'a * T) \<rightarrow> 'a * T"}
  \end{tabular}

  \begin{description}

  \item @{text get} retrieval of the current data.

  \item @{text change} update of current data (cached!)
    by giving a continuation.

  \item @{text change_yield} update with side result.

  \end{description}
*}

text {*
  \bigskip

  \emph{Happy proving, happy hacking!}
*}

end
