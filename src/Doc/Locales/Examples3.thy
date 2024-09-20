theory Examples3
imports Examples
begin

subsection \<open>Third Version: Local Interpretation
  \label{sec:local-interpretation}\<close>

text \<open>In the above example, the fact that \<^term>\<open>(\<le>)\<close> is a partial
  order for the integers was used in the second goal to
  discharge the premise in the definition of \<open>(\<sqsubset>)\<close>.  In
  general, proofs of the equations not only may involve definitions
  from the interpreted locale but arbitrarily complex arguments in the
  context of the locale.  Therefore it would be convenient to have the
  interpreted locale conclusions temporarily available in the proof.
  This can be achieved by a locale interpretation in the proof body.
  The command for local interpretations is \isakeyword{interpret}.  We
  repeat the example from the previous section to illustrate this.\<close>

  interpretation %visible int: partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
    rewrites "int.less x y = (x < y)"
  proof -
    show "partial_order ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
      by unfold_locales auto
    then interpret int: partial_order "(\<le>) :: [int, int] \<Rightarrow> bool" .
    show "int.less x y = (x < y)"
      unfolding int.less_def by auto
  qed

text \<open>The inner interpretation is immediate from the preceding fact
  and proved by assumption (Isar short hand ``.'').  It enriches the
  local proof context by the theorems
  also obtained in the interpretation from Section~\ref{sec:po-first},
  and \<open>int.less_def\<close> may directly be used to unfold the
  definition.  Theorems from the local interpretation disappear after
  leaving the proof context --- that is, after the succeeding
  \isakeyword{next} or \isakeyword{qed} statement.\<close>


subsection \<open>Further Interpretations\<close>

text \<open>Further interpretations are necessary for
  the other locales.  In \<open>lattice\<close> the operations~\<open>\<sqinter>\<close>
  and~\<open>\<squnion>\<close> are substituted by \<^term>\<open>min :: int \<Rightarrow> int \<Rightarrow> int\<close>
  and \<^term>\<open>max :: int \<Rightarrow> int \<Rightarrow> int\<close>.  The entire proof for the
  interpretation is reproduced to give an example of a more
  elaborate interpretation proof.  Note that the equations are named
  so they can be used in a later example.\<close>

  interpretation %visible int: lattice "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
    rewrites int_min_eq: "int.meet x y = min x y"
      and int_max_eq: "int.join x y = max x y"
  proof -
    show "lattice ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
      txt \<open>\normalsize We have already shown that this is a partial
        order,\<close>
      apply unfold_locales
      txt \<open>\normalsize hence only the lattice axioms remain to be
        shown.
        @{subgoals [display]}
        By \<open>is_inf\<close> and \<open>is_sup\<close>,\<close>
      apply (unfold int.is_inf_def int.is_sup_def)
      txt \<open>\normalsize the goals are transformed to these
        statements:
        @{subgoals [display]}
        This is Presburger arithmetic, which can be solved by the
        method \<open>arith\<close>.\<close>
      by arith+
    txt \<open>\normalsize In order to show the equations, we put ourselves
      in a situation where the lattice theorems can be used in a
      convenient way.\<close>
    then interpret int: lattice "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" .
    show "int.meet x y = min x y"
      by (bestsimp simp: int.meet_def int.is_inf_def)
    show "int.join x y = max x y"
      by (bestsimp simp: int.join_def int.is_sup_def)
  qed

text \<open>Next follows that \<open>(\<le>)\<close> is a total order, again for
  the integers.\<close>

  interpretation %visible int: total_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
    by unfold_locales arith

text \<open>Theorems that are available in the theory at this point are shown in
  Table~\ref{tab:int-lattice}.  Two points are worth noting:

\begin{table}
\hrule
\vspace{2ex}
\begin{center}
\begin{tabular}{l}
  @{thm [source] int.less_def} from locale \<open>partial_order\<close>: \\
  \quad @{thm int.less_def} \\
  @{thm [source] int.meet_left} from locale \<open>lattice\<close>: \\
  \quad @{thm int.meet_left} \\
  @{thm [source] int.join_distr} from locale \<open>distrib_lattice\<close>: \\
  \quad @{thm int.join_distr} \\
  @{thm [source] int.less_total} from locale \<open>total_order\<close>: \\
  \quad @{thm int.less_total}
\end{tabular}
\end{center}
\hrule
\caption{Interpreted theorems for~\<open>\<le>\<close> on the integers.}
\label{tab:int-lattice}
\end{table}

\begin{itemize}
\item
  Locale \<open>distrib_lattice\<close> was also interpreted.  Since the
  locale hierarchy reflects that total orders are distributive
  lattices, the interpretation of the latter was inserted
  automatically with the interpretation of the former.  In general,
  interpretation traverses the locale hierarchy upwards and interprets
  all encountered locales, regardless whether imported or proved via
  the \isakeyword{sublocale} command.  Existing interpretations are
  skipped avoiding duplicate work.
\item
  The predicate \<^term>\<open>(<)\<close> appears in theorem @{thm [source]
  int.less_total}
  although an equation for the replacement of \<open>(\<sqsubset>)\<close> was only
  given in the interpretation of \<open>partial_order\<close>.  The
  interpretation equations are pushed downwards the hierarchy for
  related interpretations --- that is, for interpretations that share
  the instances of parameters they have in common.
\end{itemize}
\<close>

text \<open>The interpretations for a locale $n$ within the current
  theory may be inspected with \isakeyword{print\_interps}~$n$.  This
  prints the list of instances of $n$, for which interpretations exist.
  For example, \isakeyword{print\_interps} \<^term>\<open>partial_order\<close>
  outputs the following:
\begin{small}
\begin{alltt}
  int : partial_order "(\(\le\))"
\end{alltt}
\end{small}
  Of course, there is only one interpretation.
  The interpretation qualifier on the left is mandatory.  Qualifiers
  can either be \emph{mandatory} or \emph{optional}.  Optional qualifiers
  are designated by ``?''.  Mandatory qualifiers must occur in
  name references while optional ones need not.  Mandatory qualifiers
  prevent accidental hiding of names, while optional qualifiers can be
  more convenient to use.  The default is mandatory.
\<close>


section \<open>Locale Expressions \label{sec:expressions}\<close>

text \<open>
  A map~\<^term>\<open>\<phi>\<close> between partial orders~\<open>\<sqsubseteq>\<close> and~\<open>\<preceq>\<close>
  is called order preserving if \<open>x \<sqsubseteq> y\<close> implies \<open>\<phi> x \<preceq>
  \<phi> y\<close>.  This situation is more complex than those encountered so
  far: it involves two partial orders, and it is desirable to use the
  existing locale for both.

  A locale for order preserving maps requires three parameters: \<open>le\<close>~(\isakeyword{infixl}~\<open>\<sqsubseteq>\<close>) and \<open>le'\<close>~(\isakeyword{infixl}~\<open>\<preceq>\<close>) for the orders and~\<open>\<phi>\<close>
  for the map.

  In order to reuse the existing locale for partial orders, which has
  the single parameter~\<open>le\<close>, it must be imported twice, once
  mapping its parameter to~\<open>le\<close> from the new locale and once
  to~\<open>le'\<close>.  This can be achieved with a compound locale
  expression.

  In general, a locale expression is a sequence of \emph{locale instances}
  separated by~``$\textbf{+}$'' and followed by a \isakeyword{for}
  clause.
  An instance has the following format:
\begin{quote}
  \textit{qualifier} \textbf{:} \textit{locale-name}
  \textit{parameter-instantiation}
\end{quote}
  We have already seen locale instances as arguments to
  \isakeyword{interpretation} in Section~\ref{sec:interpretation}.
  As before, the qualifier serves to disambiguate names from
  different instances of the same locale, and unless designated with a
  ``?'' it must occur in name references.

  Since the parameters~\<open>le\<close> and~\<open>le'\<close> are to be partial
  orders, our locale for order preserving maps will import the these
  instances:
\begin{small}
\begin{alltt}
  le: partial_order le
  le': partial_order le'
\end{alltt}
\end{small}
  For matter of convenience we choose to name parameter names and
  qualifiers alike.  This is an arbitrary decision.  Technically, qualifiers
  and parameters are unrelated.

  Having determined the instances, let us turn to the \isakeyword{for}
  clause.  It serves to declare locale parameters in the same way as
  the context element \isakeyword{fixes} does.  Context elements can
  only occur after the import section, and therefore the parameters
  referred to in the instances must be declared in the \isakeyword{for}
  clause.  The \isakeyword{for} clause is also where the syntax of these
  parameters is declared.

  Two context elements for the map parameter~\<open>\<phi>\<close> and the
  assumptions that it is order preserving complete the locale
  declaration.\<close>

  locale order_preserving =
    le: partial_order le + le': partial_order le'
      for le (infixl \<open>\<sqsubseteq>\<close> 50) and le' (infixl \<open>\<preceq>\<close> 50) +
    fixes \<phi>
    assumes hom_le: "x \<sqsubseteq> y \<Longrightarrow> \<phi> x \<preceq> \<phi> y"

text (in order_preserving) \<open>Here are examples of theorems that are
  available in the locale:

  \hspace*{1em}@{thm [source] hom_le}: @{thm hom_le}

  \hspace*{1em}@{thm [source] le.less_le_trans}: @{thm le.less_le_trans}

  \hspace*{1em}@{thm [source] le'.less_le_trans}:
  @{thm [display, indent=4] le'.less_le_trans}
  While there is infix syntax for the strict operation associated with
  \<^term>\<open>(\<sqsubseteq>)\<close>, there is none for the strict version of \<^term>\<open>(\<preceq>)\<close>.  The syntax \<open>\<sqsubset>\<close> for \<open>less\<close> is only
  available for the original instance it was declared for.  We may
  introduce infix syntax for \<open>le'.less\<close> with the following declaration:\<close>

  notation (in order_preserving) le'.less (infixl \<open>\<prec>\<close> 50)

text (in order_preserving) \<open>Now the theorem is displayed nicely as
  @{thm [source]  le'.less_le_trans}:
  @{thm [display, indent=2] le'.less_le_trans}\<close>

text \<open>There are short notations for locale expressions.  These are
  discussed in the following.\<close>


subsection \<open>Default Instantiations\<close>

text \<open>
  It is possible to omit parameter instantiations.  The
  instantiation then defaults to the name of
  the parameter itself.  For example, the locale expression \<open>partial_order\<close> is short for \<open>partial_order le\<close>, since the
  locale's single parameter is~\<open>le\<close>.  We took advantage of this
  in the \isakeyword{sublocale} declarations of
  Section~\ref{sec:changing-the-hierarchy}.\<close>


subsection \<open>Implicit Parameters \label{sec:implicit-parameters}\<close>

text \<open>In a locale expression that occurs within a locale
  declaration, omitted parameters additionally extend the (possibly
  empty) \isakeyword{for} clause.

  The \isakeyword{for} clause is a general construct of Isabelle/Isar
  to mark names occurring in the preceding declaration as ``arbitrary
  but fixed''.  This is necessary for example, if the name is already
  bound in a surrounding context.  In a locale expression, names
  occurring in parameter instantiations should be bound by a
  \isakeyword{for} clause whenever these names are not introduced
  elsewhere in the context --- for example, on the left hand side of a
  \isakeyword{sublocale} declaration.

  There is an exception to this rule in locale declarations, where the
  \isakeyword{for} clause serves to declare locale parameters.  Here,
  locale parameters for which no parameter instantiation is given are
  implicitly added, with their mixfix syntax, at the beginning of the
  \isakeyword{for} clause.  For example, in a locale declaration, the
  expression \<open>partial_order\<close> is short for
\begin{small}
\begin{alltt}
  partial_order le \isakeyword{for} le (\isakeyword{infixl} "\(\sqsubseteq\)" 50)\textrm{.}
\end{alltt}
\end{small}
  This short hand was used in the locale declarations throughout
  Section~\ref{sec:import}.
\<close>

text\<open>
  The following locale declarations provide more examples.  A
  map~\<open>\<phi>\<close> is a lattice homomorphism if it preserves meet and
  join.\<close>

  locale lattice_hom =
    le: lattice + le': lattice le' for le' (infixl \<open>\<preceq>\<close> 50) +
    fixes \<phi>
    assumes hom_meet: "\<phi> (x \<sqinter> y) = le'.meet (\<phi> x) (\<phi> y)"
      and hom_join: "\<phi> (x \<squnion> y) = le'.join (\<phi> x) (\<phi> y)"

text \<open>The parameter instantiation in the first instance of \<^term>\<open>lattice\<close> is omitted.  This causes the parameter~\<open>le\<close> to be
  added to the \isakeyword{for} clause, and the locale has
  parameters~\<open>le\<close>,~\<open>le'\<close> and, of course,~\<open>\<phi>\<close>.

  Before turning to the second example, we complete the locale by
  providing infix syntax for the meet and join operations of the
  second lattice.
\<close>

  context lattice_hom
  begin
  notation le'.meet (infixl \<open>\<sqinter>''\<close> 50)
  notation le'.join (infixl \<open>\<squnion>''\<close> 50)
  end

text \<open>The next example makes radical use of the short hand
  facilities.  A homomorphism is an endomorphism if both orders
  coincide.\<close>

  locale lattice_end = lattice_hom _ le

text \<open>The notation~\<open>_\<close> enables to omit a parameter in a
  positional instantiation.  The omitted parameter,~\<open>le\<close> becomes
  the parameter of the declared locale and is, in the following
  position, used to instantiate the second parameter of \<open>lattice_hom\<close>.  The effect is that of identifying the first in second
  parameter of the homomorphism locale.\<close>

text \<open>The inheritance diagram of the situation we have now is shown
  in Figure~\ref{fig:hom}, where the dashed line depicts an
  interpretation which is introduced below.  Parameter instantiations
  are indicated by $\sqsubseteq \mapsto \preceq$ etc.  By looking at
  the inheritance diagram it would seem
  that two identical copies of each of the locales \<open>partial_order\<close> and \<open>lattice\<close> are imported by \<open>lattice_end\<close>.  This is not the case!  Inheritance paths with
  identical morphisms are automatically detected and
  the conclusions of the respective locales appear only once.

\begin{figure}
\hrule \vspace{2ex}
\begin{center}
\begin{tikzpicture}
  \node (o) at (0,0) {\<open>partial_order\<close>};
  \node (oh) at (1.5,-2) {\<open>order_preserving\<close>};
  \node (oh1) at (1.5,-0.7) {$\scriptscriptstyle \sqsubseteq \mapsto \sqsubseteq$};
  \node (oh2) at (0,-1.3) {$\scriptscriptstyle \sqsubseteq \mapsto \preceq$};
  \node (l) at (-1.5,-2) {\<open>lattice\<close>};
  \node (lh) at (0,-4) {\<open>lattice_hom\<close>};
  \node (lh1) at (0,-2.7) {$\scriptscriptstyle \sqsubseteq \mapsto \sqsubseteq$};
  \node (lh2) at (-1.5,-3.3) {$\scriptscriptstyle \sqsubseteq \mapsto \preceq$};
  \node (le) at (0,-6) {\<open>lattice_end\<close>};
  \node (le1) at (0,-4.8)
    [anchor=west]{$\scriptscriptstyle \sqsubseteq \mapsto \sqsubseteq$};
  \node (le2) at (0,-5.2)
    [anchor=west]{$\scriptscriptstyle \preceq \mapsto \sqsubseteq$};
  \draw (o) -- (l);
  \draw[dashed] (oh) -- (lh);
  \draw (lh) -- (le);
  \draw (o) .. controls (oh1.south west) .. (oh);
  \draw (o) .. controls (oh2.north east) .. (oh);
  \draw (l) .. controls (lh1.south west) .. (lh);
  \draw (l) .. controls (lh2.north east) .. (lh);
\end{tikzpicture}
\end{center}
\hrule
\caption{Hierarchy of Homomorphism Locales.}
\label{fig:hom}
\end{figure}
\<close>

text \<open>It can be shown easily that a lattice homomorphism is order
  preserving.  As the final example of this section, a locale
  interpretation is used to assert this:\<close>

  sublocale lattice_hom \<subseteq> order_preserving
  proof unfold_locales
    fix x y
    assume "x \<sqsubseteq> y"
    then have "y = (x \<squnion> y)" by (simp add: le.join_connection)
    then have "\<phi> y = (\<phi> x \<squnion>' \<phi> y)" by (simp add: hom_join [symmetric])
    then show "\<phi> x \<preceq> \<phi> y" by (simp add: le'.join_connection)
  qed

text (in lattice_hom) \<open>
  Theorems and other declarations --- syntax, in particular --- from
  the locale \<open>order_preserving\<close> are now active in \<open>lattice_hom\<close>, for example
  @{thm [source] hom_le}:
  @{thm [display, indent=2] hom_le}
  This theorem will be useful in the following section.
\<close>


section \<open>Conditional Interpretation\<close>

text \<open>There are situations where an interpretation is not possible
  in the general case since the desired property is only valid if
  certain conditions are fulfilled.  Take, for example, the function
  \<open>\<lambda>i. n * i\<close> that scales its argument by a constant factor.
  This function is order preserving (and even a lattice endomorphism)
  with respect to \<^term>\<open>(\<le>)\<close> provided \<open>n \<ge> 0\<close>.

  It is not possible to express this using a global interpretation,
  because it is in general unspecified whether~\<^term>\<open>n\<close> is
  non-negative, but one may make an interpretation in an inner context
  of a proof where full information is available.
  This is not fully satisfactory either, since potentially
  interpretations may be required to make interpretations in many
  contexts.  What is
  required is an interpretation that depends on the condition --- and
  this can be done with the \isakeyword{sublocale} command.  For this
  purpose, we introduce a locale for the condition.\<close>

  locale non_negative =
    fixes n :: int
    assumes non_neg: "0 \<le> n"

text \<open>It is again convenient to make the interpretation in an
  incremental fashion, first for order preserving maps, then for
  lattice endomorphisms.\<close>

  sublocale non_negative \<subseteq>
      order_preserving "(\<le>)" "(\<le>)" "\<lambda>i. n * i"
    using non_neg by unfold_locales (rule mult_left_mono)

text \<open>While the proof of the previous interpretation
  is straightforward from monotonicity lemmas for~\<^term>\<open>(*)\<close>, the
  second proof follows a useful pattern.\<close>

  sublocale %visible non_negative \<subseteq> lattice_end "(\<le>)" "\<lambda>i. n * i"
  proof (unfold_locales, unfold int_min_eq int_max_eq)
    txt \<open>\normalsize Unfolding the locale predicates \emph{and} the
      interpretation equations immediately yields two subgoals that
      reflect the core conjecture.
      @{subgoals [display]}
      It is now necessary to show, in the context of \<^term>\<open>non_negative\<close>, that multiplication by~\<^term>\<open>n\<close> commutes with
      \<^term>\<open>min\<close> and \<^term>\<open>max\<close>.\<close>
  qed (auto simp: hom_le)

text (in order_preserving) \<open>The lemma @{thm [source] hom_le}
  simplifies a proof that would have otherwise been lengthy and we may
  consider making it a default rule for the simplifier:\<close>

  lemmas (in order_preserving) hom_le [simp]


subsection \<open>Avoiding Infinite Chains of Interpretations
  \label{sec:infinite-chains}\<close>

text \<open>Similar situations arise frequently in formalisations of
  abstract algebra where it is desirable to express that certain
  constructions preserve certain properties.  For example, polynomials
  over rings are rings, or --- an example from the domain where the
  illustrations of this tutorial are taken from --- a partial order
  may be obtained for a function space by point-wise lifting of the
  partial order of the co-domain.  This corresponds to the following
  interpretation:\<close>

  sublocale %visible partial_order \<subseteq> f: partial_order "\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x"
    oops

text \<open>Unfortunately this is a cyclic interpretation that leads to an
  infinite chain, namely
  @{text [display, indent=2] "partial_order \<subseteq> partial_order (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x) \<subseteq>
  partial_order (\<lambda>f g. \<forall>x y. f x y \<sqsubseteq> g x y) \<subseteq>  \<dots>"}
  and the interpretation is rejected.

  Instead it is necessary to declare a locale that is logically
  equivalent to \<^term>\<open>partial_order\<close> but serves to collect facts
  about functions spaces where the co-domain is a partial order, and
  to make the interpretation in its context:\<close>

  locale fun_partial_order = partial_order

  sublocale fun_partial_order \<subseteq>
      f: partial_order "\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x"
    by unfold_locales (fast,rule,fast,blast intro: trans)

text \<open>It is quite common in abstract algebra that such a construction
  maps a hierarchy of algebraic structures (or specifications) to a
  related hierarchy.  By means of the same lifting, a function space
  is a lattice if its co-domain is a lattice:\<close>

  locale fun_lattice = fun_partial_order + lattice

  sublocale fun_lattice \<subseteq> f: lattice "\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x"
  proof unfold_locales
    fix f g
    have "partial_order.is_inf (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x) f g (\<lambda>x. f x \<sqinter> g x)"
      apply (rule f.is_infI) apply rule+ apply (drule spec, assumption)+ done
    then show "\<exists>inf. partial_order.is_inf (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x) f g inf"
      by fast
  next
    fix f g
    have "partial_order.is_sup (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x) f g (\<lambda>x. f x \<squnion> g x)"
      apply (rule f.is_supI) apply rule+ apply (drule spec, assumption)+ done
    then show "\<exists>sup. partial_order.is_sup (\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x) f g sup"
      by fast
  qed


section \<open>Further Reading\<close>

text \<open>More information on locales and their interpretation is
  available.  For the locale hierarchy of import and interpretation
  dependencies see~\<^cite>\<open>Ballarin2006a\<close>; interpretations in theories
  and proofs are covered in~\<^cite>\<open>Ballarin2006b\<close>.  In the latter, I
  show how interpretation in proofs enables to reason about families
  of algebraic structures, which cannot be expressed with locales
  directly.

  Haftmann and Wenzel~\<^cite>\<open>HaftmannWenzel2007\<close> overcome a restriction
  of axiomatic type classes through a combination with locale
  interpretation.  The result is a Haskell-style class system with a
  facility to generate ML and Haskell code.  Classes are sufficient for
  simple specifications with a single type parameter.  The locales for
  orders and lattices presented in this tutorial fall into this
  category.  Order preserving maps, homomorphisms and vector spaces,
  on the other hand, do not.

  The locales reimplementation for Isabelle 2009 provides, among other
  improvements, a clean integration with Isabelle/Isar's local theory
  mechanisms, which are described in another paper by Haftmann and
  Wenzel~\<^cite>\<open>HaftmannWenzel2009\<close>.

  The original work of Kammüller on locales~\<^cite>\<open>KammullerEtAl1999\<close>
  may be of interest from a historical perspective.  My previous
  report on locales and locale expressions~\<^cite>\<open>Ballarin2004a\<close>
  describes a simpler form of expressions than available now and is
  outdated. The mathematical background on orders and lattices is
  taken from Jacobson's textbook on algebra~\<^cite>\<open>\<open>Chapter~8\<close> in Jacobson1985\<close>.

  The sources of this tutorial, which include all proofs, are
  available with the Isabelle distribution at
  \<^url>\<open>https://isabelle.in.tum.de\<close>.
\<close>

text \<open>
\begin{table}
\hrule
\vspace{2ex}
\begin{center}
\begin{tabular}{l>$c<$l}
  \multicolumn{3}{l}{Miscellaneous} \\

  \textit{attr-name} & ::=
  & \textit{name} $|$ \textit{attribute} $|$
    \textit{name} \textit{attribute} \\
  \textit{qualifier} & ::=
  & \textit{name} [``\textbf{?}''] \\[2ex]

  \multicolumn{3}{l}{Context Elements} \\

  \textit{fixes} & ::=
  & \textit{name} [ ``\textbf{::}'' \textit{type} ]
    [ ``\textbf{(}'' \textbf{structure} ``\textbf{)}'' $|$
    \textit{mixfix} ] \\
\begin{comment}
  \textit{constrains} & ::=
  & \textit{name} ``\textbf{::}'' \textit{type} \\
\end{comment}
  \textit{assumes} & ::=
  & [ \textit{attr-name} ``\textbf{:}'' ] \textit{proposition} \\
\begin{comment}
  \textit{defines} & ::=
  & [ \textit{attr-name} ``\textbf{:}'' ] \textit{proposition} \\
  \textit{notes} & ::=
  & [ \textit{attr-name} ``\textbf{=}'' ]
    ( \textit{qualified-name} [ \textit{attribute} ] )$^+$ \\
\end{comment}

  \textit{element} & ::=
  & \textbf{fixes} \textit{fixes} ( \textbf{and} \textit{fixes} )$^*$ \\
\begin{comment}
  & |
  & \textbf{constrains} \textit{constrains}
    ( \textbf{and} \textit{constrains} )$^*$ \\
\end{comment}
  & |
  & \textbf{assumes} \textit{assumes} ( \textbf{and} \textit{assumes} )$^*$ \\[2ex]
%\begin{comment}
%  & |
%  & \textbf{defines} \textit{defines} ( \textbf{and} \textit{defines} )$^*$ \\
%  & |
%  & \textbf{notes} \textit{notes} ( \textbf{and} \textit{notes} )$^*$ \\
%\end{comment}

  \multicolumn{3}{l}{Locale Expressions} \\

  \textit{pos-insts} & ::=
  & ( \textit{term} $|$ ``\textbf{\_}'' )$^*$ \\
  \textit{named-insts} & ::=
  & \textbf{where} \textit{name} ``\textbf{=}'' \textit{term}
  ( \textbf{and} \textit{name} ``\textbf{=}'' \textit{term} )$^*$ \\
  \textit{instance} & ::=
  & [ \textit{qualifier} ``\textbf{:}'' ]
    \textit{name} ( \textit{pos-insts} $|$ \textit{named-inst} ) \\
  \textit{expression}  & ::= 
  & \textit{instance} ( ``\textbf{+}'' \textit{instance} )$^*$
    [ \textbf{for} \textit{fixes} ( \textbf{and} \textit{fixes} )$^*$ ] \\[2ex]

  \multicolumn{3}{l}{Declaration of Locales} \\

  \textit{locale} & ::=
  & \textit{element}$^+$ \\
  & | & \textit{expression} [ ``\textbf{+}'' \textit{element}$^+$ ] \\
  \textit{toplevel} & ::=
  & \textbf{locale} \textit{name} [ ``\textbf{=}''
    \textit{locale} ] \\[2ex]

  \multicolumn{3}{l}{Interpretation} \\

  \textit{equation} & ::= & [ \textit{attr-name} ``\textbf{:}'' ]
    \textit{prop} \\
  \textit{equations} & ::= &  \textbf{rewrites} \textit{equation} ( \textbf{and}
    \textit{equation} )$^*$  \\
  \textit{toplevel} & ::=
  & \textbf{sublocale} \textit{name} ( ``$<$'' $|$
    ``$\subseteq$'' ) \textit{expression} \textit{proof} \\
  & |
  & \textbf{interpretation}
    \textit{expression} [ \textit{equations} ] \textit{proof} \\
  & |
  & \textbf{interpret}
    \textit{expression} \textit{proof} \\[2ex]

  \multicolumn{3}{l}{Diagnostics} \\

  \textit{toplevel} & ::=
  & \textbf{print\_locales} \\
  & | & \textbf{print\_locale} [ ``\textbf{!}'' ] \textit{name} \\
  & | & \textbf{print\_interps} \textit{name}
\end{tabular}
\end{center}
\hrule
\caption{Syntax of Locale Commands.}
\label{tab:commands}
\end{table}
\<close>

text \<open>\textbf{Revision History.}  The present fourth revision of the
  tutorial accommodates minor updates to the syntax of the locale commands
  and the handling of notation under morphisms introduced with Isabelle 2016.
  For the third revision of the tutorial, which corresponds to the published
  version, much of the explanatory text was rewritten.  Inheritance of
  interpretation equations was made available with Isabelle 2009-1.
  The second revision accommodates changes introduced by the locales
  reimplementation for Isabelle 2009.  Most notably locale expressions
  were generalised from renaming to instantiation.\<close>

text \<open>\textbf{Acknowledgements.}  Alexander Krauss, Tobias Nipkow,
  Randy Pollack, Andreas Schropp, Christian Sternagel and Makarius Wenzel
  have made
  useful comments on earlier versions of this document.  The section
  on conditional interpretation was inspired by a number of e-mail
  enquiries the author received from locale users, and which suggested
  that this use case is important enough to deserve explicit
  explanation.  The term \emph{conditional interpretation} is due to
  Larry Paulson.\<close>

end
