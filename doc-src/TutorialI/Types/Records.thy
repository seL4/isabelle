
header {* Records \label{sec:records} *}

(*<*)
theory Records = Main:
(*>*)

text {*
  \index{records|(}%
  Records are familiar from programming languages.  A record of $n$
  fields is essentially an $n$-tuple, but the record's components have
  names, which can make expressions easier to read and reduces the
  risk of confusing one field for another.

  A record of Isabelle/HOL covers a collection of fields, with select
  and update operations.  Each field has a specified type, which may
  be polymorphic.  The field names are part of the record type, and
  the order of the fields is significant --- as it is in Pascal but
  not in Standard ML.  If two different record types have field names
  in common, then the ambiguity is resolved in the usual way, by
  qualified names.

  Record types can also be defined by extending other record types.
  Extensible records make use of the reserved pseudo-field \cdx{more},
  which is present in every record type.  Generic record operations
  work on all possible extensions of a given type scheme; polymorphism
  takes care of structural sub-typing behind the scenes.  There are
  also explicit coercion functions between fixed record types.
*}


subsection {* Record Basics *}

text {*
  Record types are not primitive in Isabelle and have a delicate
  internal representation based on nested copies of the primitive
  product type.  A \commdx{record} declaration introduces a new record
  type scheme by specifying its fields, which are packaged internally
  to hold up the perception of the record as a distinguished entity.
*}

record point =
  Xcoord :: int
  Ycoord :: int

text {*
  Records of type @{typ point} have two fields named @{text Xcoord}
  and @{text Ycoord}, both of type~@{typ int}.  We now define a
  constant of type @{typ point}:
*}

constdefs
  pt1 :: point
  "pt1 \<equiv> (| Xcoord = 999, Ycoord = 23 |)"

text {*
  We see above the ASCII notation for record brackets.  You can also
  use the symbolic brackets @{text \<lparr>} and @{text \<rparr>}.  Record type
  expressions can be written directly as well, without referring to
  previously declared names (which happen to be mere type
  abbreviations):
*}

constdefs
  pt2 :: "\<lparr>Xcoord :: int, Ycoord :: int\<rparr>"
  "pt2 \<equiv> \<lparr>Xcoord = -45, Ycoord = 97\<rparr>"

text {*
  For each field, there is a \emph{selector}\index{selector!record}
  function of the same name.  For example, if @{text p} has type @{typ
  point} then @{text "Xcoord p"} denotes the value of the @{text
  Xcoord} field of~@{text p}.  Expressions involving field selection
  of explicit records are simplified automatically:
*}

lemma "Xcoord \<lparr>Xcoord = a, Ycoord = b\<rparr> = a"
  by simp

text {*
  The \emph{update}\index{update!record} operation is functional.  For
  example, @{term "p\<lparr>Xcoord := 0\<rparr>"} is a record whose @{text Xcoord}
  value is zero and whose @{text Ycoord} value is copied from~@{text
  p}.  Updates are also simplified automatically:
*}

lemma "\<lparr>Xcoord = a, Ycoord = b\<rparr>\<lparr>Xcoord := 0\<rparr> =
    \<lparr>Xcoord = 0, Ycoord = b\<rparr>"
  by simp

text {*
  \begin{warn}
  Field names are declared as constants and can no longer be used as
  variables.  It would be unwise, for example, to call the fields of
  type @{typ point} simply @{text x} and~@{text y}.
  \end{warn}
*}


subsection {* Extensible Records and Generic Operations *}

text {*
  \index{records!extensible|(}%

  Now, let us define coloured points (type @{text cpoint}) to be
  points extended with a field @{text col} of type @{text colour}:
*}

datatype colour = Red | Green | Blue

record cpoint = point +
  col :: colour

text {*
  The fields of this new type are @{text Xcoord}, @{text Ycoord} and
  @{text col}, in that order:
*}

constdefs
  cpt1 :: cpoint
  "cpt1 \<equiv> \<lparr>Xcoord = 999, Ycoord = 23, col = Green\<rparr>"

text {*
  We can define generic operations that work on arbitrary instances of
  a record scheme, e.g.\ covering @{typ point}, @{typ cpoint} and any
  further extensions.  Every record structure has an implicit
  pseudo-field, \cdx{more}, that keeps the extension as an explicit
  value.  Its type is declared as completely polymorphic:~@{typ 'a}.
  When a fixed record value is expressed using just its standard
  fields, the value of @{text more} is implicitly set to @{text "()"},
  the empty tuple, which has type @{typ unit}.  Within the record
  brackets, you can refer to the @{text more} field by writing @{text
  "\<dots>"} (three dots):
*}

lemma "Xcoord \<lparr>Xcoord = a, Ycoord = b, \<dots> = p\<rparr> = a"
  by simp

text {*
  This lemma applies to any record whose first two fields are @{text
  Xcoord} and~@{text Ycoord}.  Note that @{text "\<lparr>Xcoord = a, Ycoord =
  b, \<dots> = ()\<rparr>"} is really the same as @{text "\<lparr>Xcoord = a, Ycoord =
  b\<rparr>"}.  Selectors and updates are always polymorphic wrt.\ the @{text
  more} part of a record scheme, its value is just ignored (for
  select) or copied (for update).

  The @{text more} pseudo-field may be manipulated directly as well,
  but the identifier needs to be qualified:
*}

lemma "point.more cpt1 = \<lparr>col = Green\<rparr>"
  by (simp add: cpt1_def)

text {*
  We see that the colour attached to this @{typ point} is a
  (rudimentary) record in its own right, namely @{text "\<lparr>col =
  Green\<rparr>"}.  In order to select or update @{text col}, this fragment
  needs to be put back into the context of the parent type scheme, say
  as @{text more} part of another @{typ point}.

  To define generic operations, we need to know a bit more about
  records.  Our definition of @{typ point} above generated two type
  abbreviations:

  \medskip
  \begin{tabular}{l}
  @{typ point}~@{text "="}~@{typ "\<lparr>Xcoord :: int, Ycoord :: int\<rparr>"} \\
  @{typ "'a point_scheme"}~@{text "="}~@{typ "\<lparr>Xcoord :: int, Ycoord :: int, \<dots> :: 'a\<rparr>"} \\
  \end{tabular}
  \medskip

  Type @{typ point} is for fixed records having exactly the two fields
  @{text Xcoord} and~@{text Ycoord}, while the polymorphic type @{typ
  "'a point_scheme"} comprises all possible extensions to those two
  fields.  Note that @{typ "unit point_scheme"} coincides with @{typ
  point}, and @{typ "\<lparr>col :: colour\<rparr> point_scheme"} with @{typ
  cpoint}.

  In the following example we define two operations --- methods, if we
  regard records as objects --- to get and set any point's @{text
  Xcoord} field.
*}

constdefs
  getX :: "'a point_scheme \<Rightarrow> int"
  "getX r \<equiv> Xcoord r"
  setX :: "'a point_scheme \<Rightarrow> int \<Rightarrow> 'a point_scheme"
  "setX r a \<equiv> r\<lparr>Xcoord := a\<rparr>"

text {*
  Here is a generic method that modifies a point, incrementing its
  @{text Xcoord} field.  The @{text Ycoord} and @{text more} fields
  are copied across.  It works for any record type scheme derived from
  @{typ point} (including @{typ cpoint} etc.):
*}

constdefs
  incX :: "'a point_scheme \<Rightarrow> 'a point_scheme"
  "incX r \<equiv> \<lparr>Xcoord = Xcoord r + 1,
    Ycoord = Ycoord r, \<dots> = point.more r\<rparr>"

text {*
  Generic theorems can be proved about generic methods.  This trivial
  lemma relates @{text incX} to @{text getX} and @{text setX}:
*}

lemma "incX r = setX r (getX r + 1)"
  by (simp add: getX_def setX_def incX_def)

text {*
  \begin{warn}
  If you use the symbolic record brackets @{text \<lparr>} and @{text \<rparr>},
  then you must also use the symbolic ellipsis, ``@{text \<dots>}'', rather
  than three consecutive periods, ``@{text "..."}''.  Mixing the ASCII
  and symbolic versions causes a syntax error.  (The two versions are
  more distinct on screen than they are on paper.)
  \end{warn}%
  \index{records!extensible|)}
*}


subsection {* Record Equality *}

text {*
  Two records are equal\index{equality!of records} if all pairs of
  corresponding fields are equal.  Record equalities are simplified
  automatically:
*}

lemma "(\<lparr>Xcoord = a, Ycoord = b\<rparr> = \<lparr>Xcoord = a', Ycoord = b'\<rparr>) =
    (a = a' \<and> b = b')"
  by simp

text {*
  The following equality is similar, but generic, in that @{text r}
  can be any instance of @{typ "'a point_scheme"}:
*}

lemma "r\<lparr>Xcoord := a, Ycoord := b\<rparr> = r\<lparr>Ycoord := b, Xcoord := a\<rparr>"
  by simp

text {*
  We see above the syntax for iterated updates.  We could equivalently
  have written the left-hand side as @{text "r\<lparr>Xcoord := a\<rparr>\<lparr>Ycoord :=
  b\<rparr>"}.

  \medskip Record equality is \emph{extensional}:
  \index{extensionality!for records} a record is determined entirely
  by the values of its fields.
*}

lemma "r = \<lparr>Xcoord = Xcoord r, Ycoord = Ycoord r\<rparr>"
  by simp

text {*
  The generic version of this equality includes the pseudo-field
  @{text more}:
*}

lemma "r = \<lparr>Xcoord = Xcoord r, Ycoord = Ycoord r, \<dots> = point.more r\<rparr>"
  by simp

text {*
  \medskip The simplifier can prove many record equalities
  automatically, but general equality reasoning can be tricky.
  Consider proving this obvious fact:
*}

lemma "r\<lparr>Xcoord := a\<rparr> = r\<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"
  apply simp?
  oops

text {*
  Here the simplifier can do nothing, since general record equality is
  not eliminated automatically.  One way to proceed is by an explicit
  forward step that applies the selector @{text Xcoord} to both sides
  of the assumed record equality:
*}

lemma "r\<lparr>Xcoord := a\<rparr> = r\<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"
  apply (drule_tac f = Xcoord in arg_cong)
  txt {* @{subgoals [display, indent = 0, margin = 65]}
    Now, @{text simp} will reduce the assumption to the desired
    conclusion. *}
  apply simp
  done

text {*
  The @{text cases} method is preferable to such a forward proof.  We
  state the desired lemma again:
*}

lemma "r\<lparr>Xcoord := a\<rparr> = r\<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"

  txt {* The \methdx{cases} method adds an equality to replace the
  named record term by an explicit record expression, listing all
  fields.  It even includes the pseudo-field @{text more}, since the
  record equality stated here is generic for all extensions. *}

  apply (cases r)

  txt {* @{subgoals [display, indent = 0, margin = 65]} Again, @{text
  simp} finishes the proof.  Because @{text r} is now represented as
  an explicit record construction, the updates can be applied and the
  record equality can be replaced by equality of the corresponding
  fields (due to injectivity). *}

  apply simp
  done

text {*
  The generic cases method does not admit references to locally bound
  parameters of a goal.  In longer proof scripts one might have to
  fall back on the primitive @{text rule_tac} used together with the
  internal representation rules of records.  E.g.\ the above use of
  @{text "(cases r)"} would become @{text "(rule_tac r = r in
  point.cases_scheme)"}.
*}


subsection {* Extending and Truncating Records *}

text {*
  Each record declaration introduces a number of derived operations to
  refer collectively to a record's fields and to convert between fixed
  record types.  They can, for instance, convert between types @{typ
  point} and @{typ cpoint}.  We can add a colour to a point or convert
  a @{typ cpoint} to a @{typ point} by forgetting its colour.

  \begin{itemize}

  \item Function \cdx{make} takes as arguments all of the record's
  fields (including those inherited from ancestors).  It returns the
  corresponding record.

  \item Function \cdx{fields} takes the record's very own fields and
  returns a record fragment consisting of just those fields.  This may
  be filled into the @{text more} part of the parent record scheme.

  \item Function \cdx{extend} takes two arguments: a record to be
  extended and a record containing the new fields.

  \item Function \cdx{truncate} takes a record (possibly an extension
  of the original record type) and returns a fixed record, removing
  any additional fields.

  \end{itemize}

  These functions merely provide handsome abbreviations for standard
  record expressions involving constructors and selectors.  The
  definitions, which are \emph{not} unfolded by default, are made
  available by the collective name of @{text defs} (@{text
  point.defs}, @{text cpoint.defs}, etc.).

  For example, here are the versions of those functions generated for
  record @{typ point}.  We omit @{text point.fields}, which happens to
  be the same as @{text point.make}.

  @{thm [display, indent = 0, margin = 65] point.make_def [no_vars]
  point.extend_def [no_vars] point.truncate_def [no_vars]}

  Contrast those with the corresponding functions for record @{typ
  cpoint}.  Observe @{text cpoint.fields} in particular.

  @{thm [display, indent = 0, margin = 65] cpoint.make_def [no_vars]
  cpoint.fields_def [no_vars] cpoint.extend_def [no_vars]
  cpoint.truncate_def [no_vars]}

  To demonstrate these functions, we declare a new coloured point by
  extending an ordinary point.  Function @{text point.extend} augments
  @{text pt1} with a colour value, which is converted into an
  appropriate record fragment by @{text cpoint.fields}.
*}

constdefs
  cpt2 :: cpoint
  "cpt2 \<equiv> point.extend pt1 (cpoint.fields Green)"

text {*
  The coloured points @{text cpt1} and @{text cpt2} are equal.  The
  proof is trivial, by unfolding all the definitions.  We deliberately
  omit the definition of~@{text pt1} in order to reveal the underlying
  comparison on type @{typ point}.
*}

lemma "cpt1 = cpt2"
  apply (simp add: cpt1_def cpt2_def point.defs cpoint.defs)
  txt {* @{subgoals [display, indent = 0, margin = 65]} *}
  apply (simp add: pt1_def)
  done

text {*
  In the example below, a coloured point is truncated to leave a
  point.  We use the @{text truncate} function of the target record.
*}

lemma "point.truncate cpt2 = pt1"
  by (simp add: pt1_def cpt2_def point.defs)

text {*
  \begin{exercise}
  Extend record @{typ cpoint} to have a further field, @{text
  intensity}, of type~@{typ nat}.  Experiment with generic operations
  (using polymorphic selectors and updates) and explicit coercions
  (using @{text extend}, @{text truncate} etc.) among the three record
  types.
  \end{exercise}

  \begin{exercise}
  (For Java programmers.)
  Model a small class hierarchy using records.
  \end{exercise}
  \index{records|)}
*}

(*<*)
end
(*>*)
