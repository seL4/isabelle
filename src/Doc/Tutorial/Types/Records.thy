
section \<open>Records \label{sec:records}\<close>

(*<*)
theory Records imports Main begin
(*>*)

text \<open>
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
\<close>


subsection \<open>Record Basics\<close>

text \<open>
  Record types are not primitive in Isabelle and have a delicate
  internal representation @{cite "NaraschewskiW-TPHOLs98"}, based on
  nested copies of the primitive product type.  A \commdx{record}
  declaration introduces a new record type scheme by specifying its
  fields, which are packaged internally to hold up the perception of
  the record as a distinguished entity.  Here is a simple example:
\<close>

record point =
  Xcoord :: int
  Ycoord :: int

text \<open>\noindent
  Records of type \<^typ>\<open>point\<close> have two fields named \<^const>\<open>Xcoord\<close>
  and \<^const>\<open>Ycoord\<close>, both of type~\<^typ>\<open>int\<close>.  We now define a
  constant of type \<^typ>\<open>point\<close>:
\<close>

definition pt1 :: point where
"pt1 \<equiv> (| Xcoord = 999, Ycoord = 23 |)"

text \<open>\noindent
  We see above the ASCII notation for record brackets.  You can also
  use the symbolic brackets \<open>\<lparr>\<close> and \<open>\<rparr>\<close>.  Record type
  expressions can be also written directly with individual fields.
  The type name above is merely an abbreviation.
\<close>

definition pt2 :: "\<lparr>Xcoord :: int, Ycoord :: int\<rparr>" where
"pt2 \<equiv> \<lparr>Xcoord = -45, Ycoord = 97\<rparr>"

text \<open>
  For each field, there is a \emph{selector}\index{selector!record}
  function of the same name.  For example, if \<open>p\<close> has type \<^typ>\<open>point\<close> then \<open>Xcoord p\<close> denotes the value of the \<open>Xcoord\<close> field of~\<open>p\<close>.  Expressions involving field selection
  of explicit records are simplified automatically:
\<close>

lemma "Xcoord \<lparr>Xcoord = a, Ycoord = b\<rparr> = a"
  by simp

text \<open>
  The \emph{update}\index{update!record} operation is functional.  For
  example, \<^term>\<open>p\<lparr>Xcoord := 0\<rparr>\<close> is a record whose \<^const>\<open>Xcoord\<close>
  value is zero and whose \<^const>\<open>Ycoord\<close> value is copied from~\<open>p\<close>.  Updates of explicit records are also simplified automatically:
\<close>

lemma "\<lparr>Xcoord = a, Ycoord = b\<rparr>\<lparr>Xcoord := 0\<rparr> =
         \<lparr>Xcoord = 0, Ycoord = b\<rparr>"
  by simp

text \<open>
  \begin{warn}
  Field names are declared as constants and can no longer be used as
  variables.  It would be unwise, for example, to call the fields of
  type \<^typ>\<open>point\<close> simply \<open>x\<close> and~\<open>y\<close>.
  \end{warn}
\<close>


subsection \<open>Extensible Records and Generic Operations\<close>

text \<open>
  \index{records!extensible|(}%

  Now, let us define coloured points (type \<open>cpoint\<close>) to be
  points extended with a field \<open>col\<close> of type \<open>colour\<close>:
\<close>

datatype colour = Red | Green | Blue

record cpoint = point +
  col :: colour

text \<open>\noindent
  The fields of this new type are \<^const>\<open>Xcoord\<close>, \<open>Ycoord\<close> and
  \<open>col\<close>, in that order.
\<close>

definition cpt1 :: cpoint where
"cpt1 \<equiv> \<lparr>Xcoord = 999, Ycoord = 23, col = Green\<rparr>"

text \<open>
  We can define generic operations that work on arbitrary
  instances of a record scheme, e.g.\ covering \<^typ>\<open>point\<close>, \<^typ>\<open>cpoint\<close>, and any further extensions.  Every record structure has an
  implicit pseudo-field, \cdx{more}, that keeps the extension as an
  explicit value.  Its type is declared as completely
  polymorphic:~\<^typ>\<open>'a\<close>.  When a fixed record value is expressed
  using just its standard fields, the value of \<open>more\<close> is
  implicitly set to \<open>()\<close>, the empty tuple, which has type
  \<^typ>\<open>unit\<close>.  Within the record brackets, you can refer to the
  \<open>more\<close> field by writing ``\<open>\<dots>\<close>'' (three dots):
\<close>

lemma "Xcoord \<lparr>Xcoord = a, Ycoord = b, \<dots> = p\<rparr> = a"
  by simp

text \<open>
  This lemma applies to any record whose first two fields are \<open>Xcoord\<close> and~\<^const>\<open>Ycoord\<close>.  Note that \<open>\<lparr>Xcoord = a, Ycoord
  = b, \<dots> = ()\<rparr>\<close> is exactly the same as \<open>\<lparr>Xcoord = a, Ycoord
  = b\<rparr>\<close>.  Selectors and updates are always polymorphic wrt.\ the
  \<open>more\<close> part of a record scheme, its value is just ignored (for
  select) or copied (for update).

  The \<open>more\<close> pseudo-field may be manipulated directly as well,
  but the identifier needs to be qualified:
\<close>

lemma "point.more cpt1 = \<lparr>col = Green\<rparr>"
  by (simp add: cpt1_def)

text \<open>\noindent
  We see that the colour part attached to this \<^typ>\<open>point\<close> is a
  rudimentary record in its own right, namely \<open>\<lparr>col =
  Green\<rparr>\<close>.  In order to select or update \<open>col\<close>, this fragment
  needs to be put back into the context of the parent type scheme, say
  as \<open>more\<close> part of another \<^typ>\<open>point\<close>.

  To define generic operations, we need to know a bit more about
  records.  Our definition of \<^typ>\<open>point\<close> above has generated two
  type abbreviations:

  \medskip
  \begin{tabular}{l}
  \<^typ>\<open>point\<close>~\<open>=\<close>~\<open>\<lparr>Xcoord :: int, Ycoord :: int\<rparr>\<close> \\
  \<^typ>\<open>'a point_scheme\<close>~\<open>=\<close>~\<open>\<lparr>Xcoord :: int, Ycoord :: int, \<dots> :: 'a\<rparr>\<close> \\
  \end{tabular}
  \medskip
  
\noindent
  Type \<^typ>\<open>point\<close> is for fixed records having exactly the two fields
  \<^const>\<open>Xcoord\<close> and~\<open>Ycoord\<close>, while the polymorphic type \<^typ>\<open>'a point_scheme\<close> comprises all possible extensions to those two
  fields.  Note that \<^typ>\<open>unit point_scheme\<close> coincides with \<^typ>\<open>point\<close>, and \<^typ>\<open>\<lparr>col :: colour\<rparr> point_scheme\<close> with \<^typ>\<open>cpoint\<close>.

  In the following example we define two operations --- methods, if we
  regard records as objects --- to get and set any point's \<open>Xcoord\<close> field.
\<close>

definition getX :: "'a point_scheme \<Rightarrow> int" where
"getX r \<equiv> Xcoord r"
definition setX :: "'a point_scheme \<Rightarrow> int \<Rightarrow> 'a point_scheme" where
"setX r a \<equiv> r\<lparr>Xcoord := a\<rparr>"

text \<open>
  Here is a generic method that modifies a point, incrementing its
  \<^const>\<open>Xcoord\<close> field.  The \<open>Ycoord\<close> and \<open>more\<close> fields
  are copied across.  It works for any record type scheme derived from
  \<^typ>\<open>point\<close> (including \<^typ>\<open>cpoint\<close> etc.):
\<close>

definition incX :: "'a point_scheme \<Rightarrow> 'a point_scheme" where
"incX r \<equiv>
  \<lparr>Xcoord = Xcoord r + 1, Ycoord = Ycoord r, \<dots> = point.more r\<rparr>"

text \<open>
  Generic theorems can be proved about generic methods.  This trivial
  lemma relates \<^const>\<open>incX\<close> to \<open>getX\<close> and \<open>setX\<close>:
\<close>

lemma "incX r = setX r (getX r + 1)"
  by (simp add: getX_def setX_def incX_def)

text \<open>
  \begin{warn}
  If you use the symbolic record brackets \<open>\<lparr>\<close> and \<open>\<rparr>\<close>,
  then you must also use the symbolic ellipsis, ``\<open>\<dots>\<close>'', rather
  than three consecutive periods, ``\<open>...\<close>''.  Mixing the ASCII
  and symbolic versions causes a syntax error.  (The two versions are
  more distinct on screen than they are on paper.)
  \end{warn}%
  \index{records!extensible|)}
\<close>


subsection \<open>Record Equality\<close>

text \<open>
  Two records are equal\index{equality!of records} if all pairs of
  corresponding fields are equal.  Concrete record equalities are
  simplified automatically:
\<close>

lemma "(\<lparr>Xcoord = a, Ycoord = b\<rparr> = \<lparr>Xcoord = a', Ycoord = b'\<rparr>) =
    (a = a' \<and> b = b')"
  by simp

text \<open>
  The following equality is similar, but generic, in that \<open>r\<close>
  can be any instance of \<^typ>\<open>'a point_scheme\<close>:
\<close>

lemma "r\<lparr>Xcoord := a, Ycoord := b\<rparr> = r\<lparr>Ycoord := b, Xcoord := a\<rparr>"
  by simp

text \<open>\noindent
  We see above the syntax for iterated updates.  We could equivalently
  have written the left-hand side as \<open>r\<lparr>Xcoord := a\<rparr>\<lparr>Ycoord :=
  b\<rparr>\<close>.

  Record equality is \emph{extensional}:
  \index{extensionality!for records} a record is determined entirely
  by the values of its fields.
\<close>

lemma "r = \<lparr>Xcoord = Xcoord r, Ycoord = Ycoord r\<rparr>"
  by simp

text \<open>\noindent
  The generic version of this equality includes the pseudo-field
  \<open>more\<close>:
\<close>

lemma "r = \<lparr>Xcoord = Xcoord r, Ycoord = Ycoord r, \<dots> = point.more r\<rparr>"
  by simp

text \<open>
  The simplifier can prove many record equalities
  automatically, but general equality reasoning can be tricky.
  Consider proving this obvious fact:
\<close>

lemma "r\<lparr>Xcoord := a\<rparr> = r\<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"
  apply simp?
  oops

text \<open>\noindent
  Here the simplifier can do nothing, since general record equality is
  not eliminated automatically.  One way to proceed is by an explicit
  forward step that applies the selector \<^const>\<open>Xcoord\<close> to both sides
  of the assumed record equality:
\<close>

lemma "r\<lparr>Xcoord := a\<rparr> = r\<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"
  apply (drule_tac f = Xcoord in arg_cong)
  txt \<open>@{subgoals [display, indent = 0, margin = 65]}
    Now, \<open>simp\<close> will reduce the assumption to the desired
    conclusion.\<close>
  apply simp
  done

text \<open>
  The \<open>cases\<close> method is preferable to such a forward proof.  We
  state the desired lemma again:
\<close>

lemma "r\<lparr>Xcoord := a\<rparr> = r\<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"

  txt \<open>The \methdx{cases} method adds an equality to replace the
  named record term by an explicit record expression, listing all
  fields.  It even includes the pseudo-field \<open>more\<close>, since the
  record equality stated here is generic for all extensions.\<close>

  apply (cases r)

  txt \<open>@{subgoals [display, indent = 0, margin = 65]} Again, \<open>simp\<close> finishes the proof.  Because \<open>r\<close> is now represented as
  an explicit record construction, the updates can be applied and the
  record equality can be replaced by equality of the corresponding
  fields (due to injectivity).\<close>

  apply simp
  done

text \<open>
  The generic cases method does not admit references to locally bound
  parameters of a goal.  In longer proof scripts one might have to
  fall back on the primitive \<open>rule_tac\<close> used together with the
  internal field representation rules of records.  The above use of
  \<open>(cases r)\<close> would become \<open>(rule_tac r = r in
  point.cases_scheme)\<close>.
\<close>


subsection \<open>Extending and Truncating Records\<close>

text \<open>
  Each record declaration introduces a number of derived operations to
  refer collectively to a record's fields and to convert between fixed
  record types.  They can, for instance, convert between types \<^typ>\<open>point\<close> and \<^typ>\<open>cpoint\<close>.  We can add a colour to a point or convert
  a \<^typ>\<open>cpoint\<close> to a \<^typ>\<open>point\<close> by forgetting its colour.

  \begin{itemize}

  \item Function \cdx{make} takes as arguments all of the record's
  fields (including those inherited from ancestors).  It returns the
  corresponding record.

  \item Function \cdx{fields} takes the record's very own fields and
  returns a record fragment consisting of just those fields.  This may
  be filled into the \<open>more\<close> part of the parent record scheme.

  \item Function \cdx{extend} takes two arguments: a record to be
  extended and a record containing the new fields.

  \item Function \cdx{truncate} takes a record (possibly an extension
  of the original record type) and returns a fixed record, removing
  any additional fields.

  \end{itemize}
  These functions provide useful abbreviations for standard
  record expressions involving constructors and selectors.  The
  definitions, which are \emph{not} unfolded by default, are made
  available by the collective name of \<open>defs\<close> (\<open>point.defs\<close>, \<open>cpoint.defs\<close>, etc.).
  For example, here are the versions of those functions generated for
  record \<^typ>\<open>point\<close>.  We omit \<open>point.fields\<close>, which happens to
  be the same as \<open>point.make\<close>.

  @{thm [display, indent = 0, margin = 65] point.make_def [no_vars]
  point.extend_def [no_vars] point.truncate_def [no_vars]}
  Contrast those with the corresponding functions for record \<^typ>\<open>cpoint\<close>.  Observe \<open>cpoint.fields\<close> in particular.
  @{thm [display, indent = 0, margin = 65] cpoint.make_def [no_vars]
  cpoint.fields_def [no_vars] cpoint.extend_def [no_vars]
  cpoint.truncate_def [no_vars]}

  To demonstrate these functions, we declare a new coloured point by
  extending an ordinary point.  Function \<open>point.extend\<close> augments
  \<open>pt1\<close> with a colour value, which is converted into an
  appropriate record fragment by \<open>cpoint.fields\<close>.
\<close>

definition cpt2 :: cpoint where
"cpt2 \<equiv> point.extend pt1 (cpoint.fields Green)"

text \<open>
  The coloured points \<^const>\<open>cpt1\<close> and \<open>cpt2\<close> are equal.  The
  proof is trivial, by unfolding all the definitions.  We deliberately
  omit the definition of~\<open>pt1\<close> in order to reveal the underlying
  comparison on type \<^typ>\<open>point\<close>.
\<close>

lemma "cpt1 = cpt2"
  apply (simp add: cpt1_def cpt2_def point.defs cpoint.defs)
  txt \<open>@{subgoals [display, indent = 0, margin = 65]}\<close>
  apply (simp add: pt1_def)
  done

text \<open>
  In the example below, a coloured point is truncated to leave a
  point.  We use the \<open>truncate\<close> function of the target record.
\<close>

lemma "point.truncate cpt2 = pt1"
  by (simp add: pt1_def cpt2_def point.defs)

text \<open>
  \begin{exercise}
  Extend record \<^typ>\<open>cpoint\<close> to have a further field, \<open>intensity\<close>, of type~\<^typ>\<open>nat\<close>.  Experiment with generic operations
  (using polymorphic selectors and updates) and explicit coercions
  (using \<open>extend\<close>, \<open>truncate\<close> etc.) among the three record
  types.
  \end{exercise}

  \begin{exercise}
  (For Java programmers.)
  Model a small class hierarchy using records.
  \end{exercise}
  \index{records|)}
\<close>

(*<*)
end
(*>*)
