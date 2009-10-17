theory Examples
imports Main GCD
begin

hide %invisible const Lattices.lattice
pretty_setmargin %invisible 65

(*
text {* The following presentation will use notation of
  Isabelle's meta logic, hence a few sentences to explain this.
  The logical
  primitives are universal quantification (@{text "\<And>"}), entailment
  (@{text "\<Longrightarrow>"}) and equality (@{text "\<equiv>"}).  Variables (not bound
  variables) are sometimes preceded by a question mark.  The logic is
  typed.  Type variables are denoted by @{text "'a"}, @{text "'b"}
  etc., and @{text "\<Rightarrow>"} is the function type.  Double brackets @{text
  "\<lbrakk>"} and @{text "\<rbrakk>"} are used to abbreviate nested entailment.
*}
*)

section {* Introduction *}

text {*
  Locales are based on contexts.  A \emph{context} can be seen as a
  formula schema
\[
  @{text "\<And>x\<^sub>1\<dots>x\<^sub>n. \<lbrakk> A\<^sub>1; \<dots> ;A\<^sub>m \<rbrakk> \<Longrightarrow> \<dots>"}
\]
  where variables @{text "x\<^sub>1"}, \ldots, @{text "x\<^sub>n"} are called
  \emph{parameters} and the premises $@{text "A\<^sub>1"}, \ldots,
  @{text "A\<^sub>m"}$ \emph{assumptions}.  A formula @{text "C"}
  is a \emph{theorem} in the context if it is a conclusion
\[
%\label{eq-fact-in-context}
  @{text "\<And>x\<^sub>1\<dots>x\<^sub>n. \<lbrakk> A\<^sub>1; \<dots> ;A\<^sub>m \<rbrakk> \<Longrightarrow> C"}.
\]
  Isabelle/Isar's notion of context goes beyond this logical view.
  Its contexts record, in a consecutive order, proved
  conclusions along with attributes, which
  may control proof procedures.  Contexts also contain syntax information
  for parameters and for terms depending on them.
  *}

section {* Simple Locales *}

text {*
  Locales can be seen as persistent contexts.  In its simplest form, a
  \emph{locale declaration} consists of a sequence of context elements
  declaring parameters (keyword \isakeyword{fixes}) and assumptions
  (keyword \isakeyword{assumes}).  The following is the specification of
  partial orders, as locale @{text partial_order}.
  *}

  locale partial_order =
    fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
    assumes refl [intro, simp]: "x \<sqsubseteq> x"
      and anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
      and trans [trans]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

text {* The parameter of this locale is @{term le}, with infix syntax
  @{text \<sqsubseteq>}.  There is an implicit type parameter @{typ "'a"}.  It
  is not necessary to declare parameter types: most general types will
  be inferred from the context elements for all parameters.

  The above declaration not only introduces the locale, it also
  defines the \emph{locale predicate} @{term partial_order} with
  definition @{thm [source] partial_order_def}:
  @{thm [display, indent=2] partial_order_def}

  The specification of a locale is fixed, but its list of conclusions
  may be extended through Isar commands that take a \emph{target} argument.
  In the following, \isakeyword{definition} and 
  \isakeyword{theorem} are illustrated.
  Table~\ref{tab:commands-with-target} lists Isar commands that accept
  a target.  There are various ways of specifying the target.  A
  target for a single command may be indicated with keyword
  \isakeyword{in} in the following way:

\begin{table}
\hrule
\vspace{2ex}
\begin{center}
\begin{tabular}{ll}
  \isakeyword{definition} & definition through an equation \\
  \isakeyword{inductive} & inductive definition \\
  \isakeyword{primrec} & primitive recursion \\
  \isakeyword{fun}, \isakeyword{function} & general recursion \\
  \isakeyword{abbreviation} & syntactic abbreviation \\
  \isakeyword{theorem}, etc.\ & theorem statement with proof \\
  \isakeyword{theorems}, etc.\ & redeclaration of theorems \\
  \isakeyword{text}, etc.\ & document markup
\end{tabular}
\end{center}
\hrule
\caption{Isar commands that accept a target.}
\label{tab:commands-with-target}
\end{table}
  *}

  definition (in partial_order)
    less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
    where "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

text {* A definition in a locale depends on the locale parameters.
  Here, a global constant @{term partial_order.less} is declared, which is lifted over the
  locale parameter @{term le}.  Its definition is the global theorem
  @{thm [source] partial_order.less_def}:
  @{thm [display, indent=2] partial_order.less_def}
  At the same time, the locale is extended by syntax transformations
  hiding this construction in the context of the locale.  That is,
  @{term "partial_order.less le"} is printed and parsed as infix
  @{text \<sqsubset>}. *}

text (in partial_order) {* Finally, the conclusion of the definition
  is added to the locale, @{thm [source] less_def}:
  @{thm [display, indent=2] less_def}
  *}

text {* As an example of a theorem statement in the locale, here is the
  derivation of a transitivity law. *}

  lemma (in partial_order) less_le_trans [trans]:
    "\<lbrakk> x \<sqsubset> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
    unfolding %visible less_def by %visible (blast intro: trans)

text {* In the context of the proof, assumptions and theorems of the
  locale may be used.  Attributes are effective: @{text anti_sym} was
  declared as introduction rule, hence it is in the context's set of
  rules used by the classical reasoner by default.  *}

text {* When working with locales, sequences of commands with the same
  target are frequent.  A block of commands, delimited by
  \isakeyword{begin} and \isakeyword{end}, makes a theory-like style
  of working possible.  All commands inside the block refer to the
  same target.  A block may immediately follow a locale
  declaration, which makes that locale the target.  Alternatively the
  target for a block may be given with the \isakeyword{context}
  command.

  This style of working is illustrated in the block below, where
  notions of infimum and supremum for partial orders are introduced,
  together with theorems.  *}

  context partial_order begin

  definition
    is_inf where "is_inf x y i =
      (i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i))"

  definition
    is_sup where "is_sup x y s =
      (x \<sqsubseteq> s \<and> y \<sqsubseteq> s \<and> (\<forall>z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> s \<sqsubseteq> z))"

  lemma %invisible is_infI [intro?]: "i \<sqsubseteq> x \<Longrightarrow> i \<sqsubseteq> y \<Longrightarrow>
      (\<And>z. z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> i) \<Longrightarrow> is_inf x y i"
    by (unfold is_inf_def) blast

  lemma %invisible is_inf_lower [elim?]:
    "is_inf x y i \<Longrightarrow> (i \<sqsubseteq> x \<Longrightarrow> i \<sqsubseteq> y \<Longrightarrow> C) \<Longrightarrow> C"
    by (unfold is_inf_def) blast

  lemma %invisible is_inf_greatest [elim?]:
      "is_inf x y i \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> i"
    by (unfold is_inf_def) blast

  theorem is_inf_uniq: "\<lbrakk>is_inf x y i; is_inf x y i'\<rbrakk> \<Longrightarrow> i = i'"
  proof -
    assume inf: "is_inf x y i"
    assume inf': "is_inf x y i'"
    show ?thesis
    proof (rule anti_sym)
      from inf' show "i \<sqsubseteq> i'"
      proof (rule is_inf_greatest)
        from inf show "i \<sqsubseteq> x" ..
        from inf show "i \<sqsubseteq> y" ..
      qed
      from inf show "i' \<sqsubseteq> i"
      proof (rule is_inf_greatest)
        from inf' show "i' \<sqsubseteq> x" ..
        from inf' show "i' \<sqsubseteq> y" ..
      qed
    qed
  qed

  theorem %invisible is_inf_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> is_inf x y x"
  proof -
    assume "x \<sqsubseteq> y"
    show ?thesis
    proof
      show "x \<sqsubseteq> x" ..
      show "x \<sqsubseteq> y" by fact
      fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y" show "z \<sqsubseteq> x" by fact
    qed
  qed

  lemma %invisible is_supI [intro?]: "x \<sqsubseteq> s \<Longrightarrow> y \<sqsubseteq> s \<Longrightarrow>
      (\<And>z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> s \<sqsubseteq> z) \<Longrightarrow> is_sup x y s"
    by (unfold is_sup_def) blast

  lemma %invisible is_sup_least [elim?]:
      "is_sup x y s \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> s \<sqsubseteq> z"
    by (unfold is_sup_def) blast

  lemma %invisible is_sup_upper [elim?]:
      "is_sup x y s \<Longrightarrow> (x \<sqsubseteq> s \<Longrightarrow> y \<sqsubseteq> s \<Longrightarrow> C) \<Longrightarrow> C"
    by (unfold is_sup_def) blast

  theorem is_sup_uniq: "\<lbrakk>is_sup x y s; is_sup x y s'\<rbrakk> \<Longrightarrow> s = s'"
  proof -
    assume sup: "is_sup x y s"
    assume sup': "is_sup x y s'"
    show ?thesis
    proof (rule anti_sym)
      from sup show "s \<sqsubseteq> s'"
      proof (rule is_sup_least)
        from sup' show "x \<sqsubseteq> s'" ..
        from sup' show "y \<sqsubseteq> s'" ..
      qed
      from sup' show "s' \<sqsubseteq> s"
      proof (rule is_sup_least)
        from sup show "x \<sqsubseteq> s" ..
        from sup show "y \<sqsubseteq> s" ..
      qed
    qed
  qed

  theorem %invisible is_sup_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> is_sup x y y"
  proof -
    assume "x \<sqsubseteq> y"
    show ?thesis
    proof
      show "x \<sqsubseteq> y" by fact
      show "y \<sqsubseteq> y" ..
      fix z assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
      show "y \<sqsubseteq> z" by fact
    qed
  qed

  end

text {* Two commands are provided to inspect locales:
  \isakeyword{print\_locales} lists the names of all locales of the
  current theory; \isakeyword{print\_locale}~$n$ prints the parameters
  and assumptions of locale $n$; \isakeyword{print\_locale!}~$n$
  additionally outputs the conclusions.

  The syntax of the locale commands discussed in this tutorial is
  shown in Table~\ref{tab:commands}.  The grammer is complete with the
  exception of additional context elements not discussed here.  See the
  Isabelle/Isar Reference Manual~\cite{IsarRef}
  for full documentation.  *}


section {* Import \label{sec:import} *}

text {* 
  Algebraic structures are commonly defined by adding operations and
  properties to existing structures.  For example, partial orders
  are extended to lattices and total orders.  Lattices are extended to
  distributive lattices.

  With locales, this inheritance is achieved through \emph{import} of a
  locale.  Import is a separate entity in the locale declaration.  If
  present, it precedes the context elements.
  *}

  locale lattice = partial_order +
    assumes ex_inf: "\<exists>inf. is_inf x y inf"
      and ex_sup: "\<exists>sup. is_sup x y sup"
  begin

text {* These assumptions refer to the predicates for infimum
  and supremum defined in @{text partial_order}.  We may now introduce
  the notions of meet and join.  *}

  definition
    meet (infixl "\<sqinter>" 70) where "x \<sqinter> y = (THE inf. is_inf x y inf)"

  definition
    join (infixl "\<squnion>" 65) where "x \<squnion> y = (THE sup. is_sup x y sup)"

  lemma %invisible meet_equality [elim?]: "is_inf x y i \<Longrightarrow> x \<sqinter> y = i"
  proof (unfold meet_def)
    assume "is_inf x y i"
    then show "(THE i. is_inf x y i) = i"
      by (rule the_equality) (rule is_inf_uniq [OF _ `is_inf x y i`])
  qed

  lemma %invisible meetI [intro?]:
      "i \<sqsubseteq> x \<Longrightarrow> i \<sqsubseteq> y \<Longrightarrow> (\<And>z. z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> i) \<Longrightarrow> x \<sqinter> y = i"
    by (rule meet_equality, rule is_infI) blast+

  lemma %invisible is_inf_meet [intro?]: "is_inf x y (x \<sqinter> y)"
  proof (unfold meet_def)
    from ex_inf obtain i where "is_inf x y i" ..
    then show "is_inf x y (THE i. is_inf x y i)"
      by (rule theI) (rule is_inf_uniq [OF _ `is_inf x y i`])
  qed

  lemma %invisible meet_left [intro?]:
    "x \<sqinter> y \<sqsubseteq> x"
    by (rule is_inf_lower) (rule is_inf_meet)

  lemma %invisible meet_right [intro?]:
    "x \<sqinter> y \<sqsubseteq> y"
    by (rule is_inf_lower) (rule is_inf_meet)

  lemma %invisible meet_le [intro?]:
    "\<lbrakk> z \<sqsubseteq> x; z \<sqsubseteq> y \<rbrakk> \<Longrightarrow> z \<sqsubseteq> x \<sqinter> y"
    by (rule is_inf_greatest) (rule is_inf_meet)

  lemma %invisible join_equality [elim?]: "is_sup x y s \<Longrightarrow> x \<squnion> y = s"
  proof (unfold join_def)
    assume "is_sup x y s"
    then show "(THE s. is_sup x y s) = s"
      by (rule the_equality) (rule is_sup_uniq [OF _ `is_sup x y s`])
  qed

  lemma %invisible joinI [intro?]: "x \<sqsubseteq> s \<Longrightarrow> y \<sqsubseteq> s \<Longrightarrow>
      (\<And>z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> s \<sqsubseteq> z) \<Longrightarrow> x \<squnion> y = s"
    by (rule join_equality, rule is_supI) blast+

  lemma %invisible is_sup_join [intro?]: "is_sup x y (x \<squnion> y)"
  proof (unfold join_def)
    from ex_sup obtain s where "is_sup x y s" ..
    then show "is_sup x y (THE s. is_sup x y s)"
      by (rule theI) (rule is_sup_uniq [OF _ `is_sup x y s`])
  qed

  lemma %invisible join_left [intro?]:
    "x \<sqsubseteq> x \<squnion> y"
    by (rule is_sup_upper) (rule is_sup_join)

  lemma %invisible join_right [intro?]:
    "y \<sqsubseteq> x \<squnion> y"
    by (rule is_sup_upper) (rule is_sup_join)

  lemma %invisible join_le [intro?]:
    "\<lbrakk> x \<sqsubseteq> z; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
    by (rule is_sup_least) (rule is_sup_join)

  theorem %invisible meet_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  proof (rule meetI)
    show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> x \<sqinter> y"
    proof
      show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> x" ..
      show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y"
      proof -
        have "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y \<sqinter> z" ..
        also have "\<dots> \<sqsubseteq> y" ..
        finally show ?thesis .
      qed
    qed
    show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> z"
    proof -
      have "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y \<sqinter> z" ..
      also have "\<dots> \<sqsubseteq> z" ..
      finally show ?thesis .
    qed
    fix w assume "w \<sqsubseteq> x \<sqinter> y" and "w \<sqsubseteq> z"
    show "w \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
    proof
      show "w \<sqsubseteq> x"
      proof -
        have "w \<sqsubseteq> x \<sqinter> y" by fact
        also have "\<dots> \<sqsubseteq> x" ..
        finally show ?thesis .
      qed
      show "w \<sqsubseteq> y \<sqinter> z"
      proof
        show "w \<sqsubseteq> y"
        proof -
          have "w \<sqsubseteq> x \<sqinter> y" by fact
          also have "\<dots> \<sqsubseteq> y" ..
          finally show ?thesis .
        qed
        show "w \<sqsubseteq> z" by fact
      qed
    qed
  qed

  theorem %invisible meet_commute: "x \<sqinter> y = y \<sqinter> x"
  proof (rule meetI)
    show "y \<sqinter> x \<sqsubseteq> x" ..
    show "y \<sqinter> x \<sqsubseteq> y" ..
    fix z assume "z \<sqsubseteq> y" and "z \<sqsubseteq> x"
    then show "z \<sqsubseteq> y \<sqinter> x" ..
  qed

  theorem %invisible meet_join_absorb: "x \<sqinter> (x \<squnion> y) = x"
  proof (rule meetI)
    show "x \<sqsubseteq> x" ..
    show "x \<sqsubseteq> x \<squnion> y" ..
    fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> x \<squnion> y"
    show "z \<sqsubseteq> x" by fact
  qed

  theorem %invisible join_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  proof (rule joinI)
    show "x \<squnion> y \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    proof
      show "x \<sqsubseteq> x \<squnion> (y \<squnion> z)" ..
      show "y \<sqsubseteq> x \<squnion> (y \<squnion> z)"
      proof -
        have "y \<sqsubseteq> y \<squnion> z" ..
        also have "... \<sqsubseteq> x \<squnion> (y \<squnion> z)" ..
        finally show ?thesis .
      qed
    qed
    show "z \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    proof -
      have "z \<sqsubseteq> y \<squnion> z"  ..
      also have "... \<sqsubseteq> x \<squnion> (y \<squnion> z)" ..
      finally show ?thesis .
    qed
    fix w assume "x \<squnion> y \<sqsubseteq> w" and "z \<sqsubseteq> w"
    show "x \<squnion> (y \<squnion> z) \<sqsubseteq> w"
    proof
      show "x \<sqsubseteq> w"
      proof -
        have "x \<sqsubseteq> x \<squnion> y" ..
        also have "\<dots> \<sqsubseteq> w" by fact
        finally show ?thesis .
      qed
      show "y \<squnion> z \<sqsubseteq> w"
      proof
        show "y \<sqsubseteq> w"
        proof -
          have "y \<sqsubseteq> x \<squnion> y" ..
          also have "... \<sqsubseteq> w" by fact
          finally show ?thesis .
        qed
        show "z \<sqsubseteq> w" by fact
      qed
    qed
  qed

  theorem %invisible join_commute: "x \<squnion> y = y \<squnion> x"
  proof (rule joinI)
    show "x \<sqsubseteq> y \<squnion> x" ..
    show "y \<sqsubseteq> y \<squnion> x" ..
    fix z assume "y \<sqsubseteq> z" and "x \<sqsubseteq> z"
    then show "y \<squnion> x \<sqsubseteq> z" ..
  qed

  theorem %invisible join_meet_absorb: "x \<squnion> (x \<sqinter> y) = x"
  proof (rule joinI)
    show "x \<sqsubseteq> x" ..
    show "x \<sqinter> y \<sqsubseteq> x" ..
    fix z assume "x \<sqsubseteq> z" and "x \<sqinter> y \<sqsubseteq> z"
    show "x \<sqsubseteq> z" by fact
  qed

  theorem %invisible meet_idem: "x \<sqinter> x = x"
  proof -
    have "x \<sqinter> (x \<squnion> (x \<sqinter> x)) = x" by (rule meet_join_absorb)
    also have "x \<squnion> (x \<sqinter> x) = x" by (rule join_meet_absorb)
    finally show ?thesis .
  qed

  theorem %invisible meet_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
  proof (rule meetI)
    assume "x \<sqsubseteq> y"
    show "x \<sqsubseteq> x" ..
    show "x \<sqsubseteq> y" by fact
    fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    show "z \<sqsubseteq> x" by fact
  qed

  theorem %invisible meet_related2 [elim?]: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
    by (drule meet_related) (simp add: meet_commute)

  theorem %invisible join_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  proof (rule joinI)
    assume "x \<sqsubseteq> y"
    show "y \<sqsubseteq> y" ..
    show "x \<sqsubseteq> y" by fact
    fix z assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    show "y \<sqsubseteq> z" by fact
  qed

  theorem %invisible join_related2 [elim?]: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
    by (drule join_related) (simp add: join_commute)

  theorem %invisible meet_connection: "(x \<sqsubseteq> y) = (x \<sqinter> y = x)"
  proof
    assume "x \<sqsubseteq> y"
    then have "is_inf x y x" ..
    then show "x \<sqinter> y = x" ..
  next
    have "x \<sqinter> y \<sqsubseteq> y" ..
    also assume "x \<sqinter> y = x"
    finally show "x \<sqsubseteq> y" .
  qed

  theorem %invisible join_connection: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
  proof
    assume "x \<sqsubseteq> y"
    then have "is_sup x y y" ..
    then show "x \<squnion> y = y" ..
  next
    have "x \<sqsubseteq> x \<squnion> y" ..
    also assume "x \<squnion> y = y"
    finally show "x \<sqsubseteq> y" .
  qed

  theorem %invisible meet_connection2: "(x \<sqsubseteq> y) = (y \<sqinter> x = x)"
    using meet_commute meet_connection by simp

  theorem %invisible join_connection2: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
    using join_commute join_connection by simp

  text %invisible {* Naming according to Jacobson I, p.\ 459. *}
  lemmas %invisible L1 = join_commute meet_commute
  lemmas %invisible L2 = join_assoc meet_assoc
  (* lemmas L3 = join_idem meet_idem *)
  lemmas %invisible L4 = join_meet_absorb meet_join_absorb

  end

text {* Locales for total orders and distributive lattices follow.
  Each comes with an example theorem. *}

  locale total_order = partial_order +
    assumes total: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

  lemma (in total_order) less_total: "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
    using total
    by (unfold less_def) blast

  locale distrib_lattice = lattice +
    assumes meet_distr: "x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> x \<sqinter> z"

  lemma (in distrib_lattice) join_distr:
    "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"  (* txt {* Jacobson I, p.\ 462 *} *)
    proof -
    have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)" by (simp add: L4)
    also have "... = x \<squnion> ((x \<sqinter> z) \<squnion> (y \<sqinter> z))" by (simp add: L2)
    also have "... = x \<squnion> ((x \<squnion> y) \<sqinter> z)" by (simp add: L1 meet_distr)
    also have "... = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)" by (simp add: L1 L4)
    also have "... = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by (simp add: meet_distr)
    finally show ?thesis .
  qed

text {*
  The locale hierachy obtained through these declarations is shown in Figure~\ref{fig:lattices}(a).

\begin{figure}
\hrule \vspace{2ex}
\begin{center}
\subfigure[Declared hierachy]{
\begin{tikzpicture}
  \node (po) at (0,0) {@{text partial_order}};
  \node (lat) at (-1.5,-1) {@{text lattice}};
  \node (dlat) at (-1.5,-2) {@{text distrib_lattice}};
  \node (to) at (1.5,-1) {@{text total_order}};
  \draw (po) -- (lat);
  \draw (lat) -- (dlat);
  \draw (po) -- (to);
%  \draw[->, dashed] (lat) -- (to);
\end{tikzpicture}
} \\
\subfigure[Total orders are lattices]{
\begin{tikzpicture}
  \node (po) at (0,0) {@{text partial_order}};
  \node (lat) at (0,-1) {@{text lattice}};
  \node (dlat) at (-1.5,-2) {@{text distrib_lattice}};
  \node (to) at (1.5,-2) {@{text total_order}};
  \draw (po) -- (lat);
  \draw (lat) -- (dlat);
  \draw (lat) -- (to);
%  \draw[->, dashed] (dlat) -- (to);
\end{tikzpicture}
} \quad
\subfigure[Total orders are distributive lattices]{
\begin{tikzpicture}
  \node (po) at (0,0) {@{text partial_order}};
  \node (lat) at (0,-1) {@{text lattice}};
  \node (dlat) at (0,-2) {@{text distrib_lattice}};
  \node (to) at (0,-3) {@{text total_order}};
  \draw (po) -- (lat);
  \draw (lat) -- (dlat);
  \draw (dlat) -- (to);
\end{tikzpicture}
}
\end{center}
\hrule
\caption{Hierarchy of Lattice Locales.}
\label{fig:lattices}
\end{figure}
  *}

section {* Changing the Locale Hierarchy
  \label{sec:changing-the-hierarchy} *}

text {*
  Total orders are lattices.  Hence, by deriving the lattice
  axioms for total orders, the hierarchy may be changed
  and @{text lattice} be placed between @{text partial_order}
  and @{text total_order}, as shown in Figure~\ref{fig:lattices}(b).
  Changes to the locale hierarchy may be declared
  with the \isakeyword{sublocale} command. *}

  sublocale %visible total_order \<subseteq> lattice

txt {* This enters the context of locale @{text total_order}, in
  which the goal @{subgoals [display]} must be shown.  First, the
  locale predicate needs to be unfolded --- for example using its
  definition or by introduction rules
  provided by the locale package.  The methods @{text intro_locales}
  and @{text unfold_locales} automate this.  They are aware of the
  current context and dependencies between locales and automatically
  discharge goals implied by these.  While @{text unfold_locales}
  always unfolds locale predicates to assumptions, @{text
  intro_locales} only unfolds definitions along the locale
  hierarchy, leaving a goal consisting of predicates defined by the
  locale package.  Occasionally the latter is of advantage since the goal
  is smaller.

  For the current goal, we would like to get hold of
  the assumptions of @{text lattice}, hence @{text unfold_locales}
  is appropriate. *}

  proof unfold_locales

txt {* Since both @{text lattice} and @{text total_order}
  inherit @{text partial_order}, the assumptions of the latter are
  discharged, and the only subgoals that remain are the assumptions
  introduced in @{text lattice} @{subgoals [display]}
  The proof for the first subgoal is *}

    fix x y
    from total have "is_inf x y (if x \<sqsubseteq> y then x else y)"
      by (auto simp: is_inf_def)
    then show "\<exists>inf. is_inf x y inf" ..
txt {* The proof for the second subgoal is analogous and not
  reproduced here. *}
  next %invisible
    fix x y
    from total have "is_sup x y (if x \<sqsubseteq> y then y else x)"
      by (auto simp: is_sup_def)
    then show "\<exists>sup. is_sup x y sup" .. qed %visible

text {* Similarly, total orders are distributive lattices. *}

  sublocale total_order \<subseteq> distrib_lattice
  proof unfold_locales
    fix %"proof" x y z
    show "x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> x \<sqinter> z" (is "?l = ?r")
      txt {* Jacobson I, p.\ 462 *}
    proof -
      { assume c: "y \<sqsubseteq> x" "z \<sqsubseteq> x"
        from c have "?l = y \<squnion> z"
          by (metis c join_connection2 join_related2 meet_related2 total)
        also from c have "... = ?r" by (metis meet_related2)
        finally have "?l = ?r" . }
      moreover
      { assume c: "x \<sqsubseteq> y \<or> x \<sqsubseteq> z"
        from c have "?l = x"
          by (metis join_connection2 join_related2 meet_connection total trans)
        also from c have "... = ?r"
          by (metis join_commute join_related2 meet_connection meet_related2 total)
        finally have "?l = ?r" . }
      moreover note total
      ultimately show ?thesis by blast
    qed
  qed

text {* The locale hierarchy is now as shown in Figure~\ref{fig:lattices}(c). *}

end
