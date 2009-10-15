theory Examples3
imports Examples "~~/src/HOL/Number_Theory/UniqueFactorization"
begin
hide %invisible const Lattices.lattice
  (* imported again through Number_Theory *)
text {* \vspace{-5ex} *}
subsection {* Third Version: Local Interpretation
  \label{sec:local-interpretation} *}

text {* In the above example, the fact that @{term "op \<le>"} is a partial
  order for the integers was used in the second goal to
  discharge the premise in the definition of @{text "op \<sqsubset>"}.  In
  general, proofs of the equations not only may involve definitions
  fromthe interpreted locale but arbitrarily complex arguments in the
  context of the locale.  Therefore is would be convenient to have the
  interpreted locale conclusions temporary available in the proof.
  This can be achieved by a locale interpretation in the proof body.
  The command for local interpretations is \isakeyword{interpret}.  We
  repeat the example from the previous section to illustrate this. *}

  interpretation %visible int: partial_order "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"
    where "partial_order.less op \<le> (x::int) y = (x < y)"
  proof -
    show "partial_order (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)"
      by unfold_locales auto
    then interpret int: partial_order "op \<le> :: [int, int] \<Rightarrow> bool" .
    show "partial_order.less op \<le> (x::int) y = (x < y)"
      unfolding int.less_def by auto
  qed

text {* The inner interpretation is immediate from the preceding fact
  and proved by assumption (Isar short hand ``.'').  It enriches the
  local proof context by the theorems
  also obtained in the interpretation from Section~\ref{sec:po-first},
  and @{text int.less_def} may directly be used to unfold the
  definition.  Theorems from the local interpretation disappear after
  leaving the proof context --- that is, after the closing a
  \isakeyword{next} or \isakeyword{qed} statement. *}


subsection {* Further Interpretations *}

text {* Further interpretations are necessary for
  the other locales.  In @{text lattice} the operations @{text \<sqinter>} and
  @{text \<squnion>} are substituted by @{term "min :: int \<Rightarrow> int \<Rightarrow> int"} and
  @{term "max :: int \<Rightarrow> int \<Rightarrow> int"}.  The entire proof for the
  interpretation is reproduced to give an example of a more
  elaborate interpretation proof.  *}

  interpretation %visible int: lattice "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"
    where "lattice.meet op \<le> (x::int) y = min x y"
      and "lattice.join op \<le> (x::int) y = max x y"
  proof -
    show "lattice (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)"
      txt {* \normalsize We have already shown that this is a partial
	order, *}
      apply unfold_locales
      txt {* \normalsize hence only the lattice axioms remain to be
	shown: @{subgoals [display]}  After unfolding @{text is_inf} and
	@{text is_sup}, *}
      apply (unfold int.is_inf_def int.is_sup_def)
      txt {* \normalsize the goals become @{subgoals [display]}
	This can be solved by Presburger arithmetic, which is contained
	in @{text arith}. *}
      by arith+
    txt {* \normalsize In order to show the equations, we put ourselves
      in a situation where the lattice theorems can be used in a
      convenient way. *}
    then interpret int: lattice "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool" .
    show "lattice.meet op \<le> (x::int) y = min x y"
      by (bestsimp simp: int.meet_def int.is_inf_def)
    show "lattice.join op \<le> (x::int) y = max x y"
      by (bestsimp simp: int.join_def int.is_sup_def)
  qed

text {* Next follows that @{text "op \<le>"} is a total order, again for
  the integers. *}

  interpretation %visible int: total_order "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"
    by unfold_locales arith

text {* Theorems that are available in the theory at this point are shown in
  Table~\ref{tab:int-lattice}.  Two points are worth noting:

\begin{table}
\hrule
\vspace{2ex}
\begin{center}
\begin{tabular}{l}
  @{thm [source] int.less_def} from locale @{text partial_order}: \\
  \quad @{thm int.less_def} \\
  @{thm [source] int.meet_left} from locale @{text lattice}: \\
  \quad @{thm int.meet_left} \\
  @{thm [source] int.join_distr} from locale @{text distrib_lattice}: \\
  \quad @{thm int.join_distr} \\
  @{thm [source] int.less_total} from locale @{text total_order}: \\
  \quad @{thm int.less_total}
\end{tabular}
\end{center}
\hrule
\caption{Interpreted theorems for @{text \<le>} on the integers.}
\label{tab:int-lattice}
\end{table}

\begin{itemize}
\item
  Locale @{text distrib_lattice} was also interpreted.  Since the
  locale hierarcy reflects that total orders are distributive
  lattices, the interpretation of the latter was inserted
  automatically with the interpretation of the former.  In general,
  interpretation of a locale will also interpret all locales further
  up in the hierarchy, regardless whether imported or proved via the
  \isakeyword{sublocale} command.
\item
  Theorem @{thm [source] int.less_total} makes use of @{term "op <"}
  although an equation for the replacement of @{text "op \<sqsubset>"} was only
  given in the interpretation of @{text partial_order}.  These
  equations are pushed downwards the hierarchy for related
  interpretations --- that is, for interpretations that share the
  instance for parameters they have in common.
\end{itemize}
  In the next section, the divisibility relation on the natural
  numbers will be explored.
  *}


subsection {* Interpretations for Divisibility *}

text {* In this section, further examples of interpretations are
  presented.  Impatient readers may skip this section at first
  reading.

  Divisibility on the natural numbers is a distributive lattice
  but not a total order.  Interpretation again proceeds
  incrementally.  In order to distinguish divisibility from the order
  relation $\le$, we use the qualifier @{text nat_dvd} for
  divisibility. *}

  interpretation nat_dvd: partial_order "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool"
    where "partial_order.less op dvd (x::nat) y = (x dvd y \<and> x \<noteq> y)"
  proof -
    show "partial_order (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool)"
      by unfold_locales (auto simp: dvd_def)
    then interpret nat_dvd: partial_order "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool" .
    show "partial_order.less op dvd (x::nat) y = (x dvd y \<and> x \<noteq> y)"
      apply (unfold nat_dvd.less_def)
      apply auto
      done
  qed

text {* Note that in Isabelle/HOL there is no operator for strict
  divisibility.  Instead, we substitute @{term "x dvd y \<and> x \<noteq> y"}.  *}

  interpretation nat_dvd: lattice "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool"
    where nat_dvd_meet_eq:
	"lattice.meet (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool) = gcd"
      and nat_dvd_join_eq:
	"lattice.join (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool) = lcm"
  proof -
    show "lattice (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool)"
      apply unfold_locales
      apply (unfold nat_dvd.is_inf_def nat_dvd.is_sup_def)
      apply (rule_tac x = "gcd x y" in exI)
      apply auto [1]
      apply (rule_tac x = "lcm x y" in exI)
      apply (auto intro: lcm_least_nat)
      done
    then interpret nat_dvd: lattice "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool" .
    show "lattice.meet (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool) = gcd"
      apply (auto simp add: expand_fun_eq)
      apply (unfold nat_dvd.meet_def)
      apply (rule the_equality)
      apply (unfold nat_dvd.is_inf_def)
      by auto
    show "lattice.join (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool) = lcm"
      apply (auto simp add: expand_fun_eq)
      apply (unfold nat_dvd.join_def)
      apply (rule the_equality)
      apply (unfold nat_dvd.is_sup_def)
      apply (auto intro: lcm_least_nat iff: lcm_unique_nat)
      done
  qed

text {* The replacement equations @{thm [source] nat_dvd_meet_eq} and
  @{thm [source] nat_dvd_join_eq} are theorems of current theories.
  They are named so that they can be used in the main part of the
  subsequent interpretation. *}

  interpretation %visible nat_dvd:
    distrib_lattice "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool"
    apply unfold_locales
    txt {* \normalsize @{subgoals [display]}
      Distributivity of lattice meet and join needs to be shown.  This is
      distributivity of gcd and lcm, as becomes apparent when unfolding
      the replacement equations from the previous interpretation: *}
    unfolding nat_dvd_meet_eq nat_dvd_join_eq
    txt {* \normalsize @{subgoals [display]}
      This is a result of number theory: *}
    by (rule UniqueFactorization.gcd_lcm_distrib_nat)

text {* Theorems that are available in the theory after these
  interpretations are shown in Table~\ref{tab:nat-dvd-lattice}.

\begin{table}
\hrule
\vspace{2ex}
\begin{center}
\begin{tabular}{l}
  @{thm [source] nat_dvd.less_def} from locale @{text partial_order}: \\
  \quad @{thm nat_dvd.less_def} \\
  @{thm [source] nat_dvd.meet_left} from locale @{text lattice}: \\
  \quad @{thm nat_dvd.meet_left} \\
  @{thm [source] nat_dvd.join_distr} from locale @{text distrib_lattice}: \\
  \quad @{thm nat_dvd.join_distr} \\
\end{tabular}
\end{center}
\hrule
\caption{Interpreted theorems for @{text dvd} on the natural numbers.}
\label{tab:nat-dvd-lattice}
\end{table}
  *}


subsection {* Inspecting Interpretations of a Locale *}

text {* The interpretations for a locale $n$ within the current
  theory may be inspected with \isakeyword{print\_interps}~$n$.  This
  prints the list of instances of $n$, for which interpretations exist.
  For example, \isakeyword{print\_interps} @{term partial_order}
  outputs the following:
\begin{alltt}
  int! : partial_order "op \(\le\)"
  nat_dvd! : partial_order "op dvd"
\end{alltt}
  The interpretation qualifiers on the left are decorated with an
  exclamation point, which means that they are mandatory.  Qualifiers
  can either be \emph{mandatory} or \emph{optional}, designated by
  ``!'' or ``?'' respectively.  Mandatory qualifiers must occur in a
  name reference while optional ones need not.  Mandatory qualifiers
  prevent accidental hiding of names, while optional qualifers can be
  more convenient to use.  For \isakeyword{interpretation}, the
  default for qualifiers without an explicit designator is ``!''.
*}


section {* Locale Expressions \label{sec:expressions} *}

text {*
  A map @{term \<phi>} between partial orders @{text \<sqsubseteq>} and @{text \<preceq>}
  is called order preserving if @{text "x \<sqsubseteq> y"} implies @{text "\<phi> x \<preceq>
  \<phi> y"}.  This situation is more complex than those encountered so
  far: it involves two partial orders, and it is desirable to use the
  existing locale for both.

  A locale for order preserving maps requires three parameters: @{text
  le} (\isakeyword{infixl}~@{text \<sqsubseteq>}), @{text le'}
  (\isakeyword{infixl}~@{text \<preceq>}) for the orders and @{text \<phi>} for the
  map.

  In order to reuse the existing locale for partial orders, which has
  the single parameter @{text le}, it must be imported twice, once
  mapping its parameter to @{text le} (\isakeyword{infixl}~@{text \<sqsubseteq>})
  from the new locale and once to @{text le'}
  (\isakeyword{infixl}~@{text \<preceq>}).  This can be achieved with a locale
  expression.

  A \emph{locale expression} is a sequence of \emph{locale instances}
  separated by ``$\textbf{+}$'' and followed by a \isakeyword{for}
  clause.
An instance has the following format:
\begin{quote}
  \textit{qualifier} \textbf{:} \textit{locale-name}
  \textit{parameter-instantiation}
\end{quote}
  We have already seen locale instances as arguments to
  \isakeyword{interpretation} in Section~\ref{sec:interpretation}.
  The qualifier serves to disambiguate the names from different
  instances of the same locale.

  Since the parameters @{text le} and @{text le'} are to be partial
  orders, our locale for order preserving maps will import the these
  instances:
\begin{alltt}
  le: partial_order le
  le': partial_order le'
\end{alltt}
  For matter of convenience we choose the parameter names also as
  qualifiers.  This is an arbitrary decision.  Technically, qualifiers
  and parameters are unrelated.

  Having determined the instances, let us turn to the \isakeyword{for}
  clause.  It serves to declare locale parameters in the same way as
  the context element \isakeyword{fixes} does.  Context elements can
  only occur after the import section, and therefore the parameters
  referred to inthe instances must be declared in the \isakeyword{for}
  clause.%
\footnote{Since all parameters can be declared in the \isakeyword{for}
  clause, the context element \isakeyword{fixes} is not needed in
  locales.  It is provided for compatibility with the long goals
  format, where the context element also occurs.}
  The \isakeyword{for} clause is also where the syntax of these
  parameters is declared.

  Two context elements for the map parameter @{text \<phi>} and the
  assumptions that it is order perserving complete the locale
  declaration. *}

  locale order_preserving =
    le: partial_order le + le': partial_order le'
      for le (infixl "\<sqsubseteq>" 50) and le' (infixl "\<preceq>" 50) +
    fixes \<phi>
    assumes hom_le: "x \<sqsubseteq> y \<Longrightarrow> \<phi> x \<preceq> \<phi> y"

text (in order_preserving) {* Here are examples of theorems that are
  available in the locale:

  @{thm [source] hom_le}: @{thm hom_le}

  @{thm [source] le.less_le_trans}: @{thm le.less_le_trans}

  @{thm [source] le'.less_le_trans}:
  @{thm [display, indent=2] le'.less_le_trans}

  While there is infix syntax for the strict operation associated to
  @{term "op \<sqsubseteq>"}, there is none for the strict version of @{term
  "op \<preceq>"}.  The abbreviation @{text less} with its infix syntax is only
  available for the original instance it was declared for.  We may
  introduce the abbreviation @{text less'} with infix syntax @{text \<prec>}
  with this declaration: *}

  abbreviation (in order_preserving)
    less' (infixl "\<prec>" 50) where "less' \<equiv> partial_order.less le'"

text (in order_preserving) {* Now the theorem is displayed nicely as
  @{thm [source]  le'.less_le_trans}:
  @{thm [display, indent=2] le'.less_le_trans} *}


subsection {* Default Instantiations and Implicit Parameters *}

text {* It is possible to omit parameter instantiations in a locale
  expression.  In that case, the instantiation defaults to the name of
  the parameter itself.  That is, the locale expression @{text
  partial_order} is short for @{text "partial_order le"}, since the
  locale's single parameter is @{text le}.  We took advantage of this
  short hand in the \isakeyword{sublocale} declarations of
  Section~\ref{sec:changing-the-hierarchy}. *}


text {* In a locale expression that occurs within a locale
  declaration, omitted parameters additionally extend the (possibly
  empty) \isakeyword{for} clause.

  The \isakeyword{for} clause is a
  general construct of Isabelle/Isar to mark names from the preceding
  declaration as ``arbitrary but fixed''.  This is necessary for
  example, if the name is already bound in a surrounding context.  In
  a locale expression, names occurring in parameter instantiations
  should be bound by a \isakeyword{for} clause whenever these names
  are not introduced elsewhere in the context --- for example, on the
  left hand side of a \isakeyword{sublocale} declaration.

  There is an exception to this rule in locale declarations, where the
  \isakeyword{for} clause servers to declare locale parameters.  Here,
  locale parameters for which no parameter instantiation is given are
  implicitly added, with their mixfix syntax, at the beginning of the
  \isakeyword{for} clause.  For example, in a locale declaration, the
  expression @{text partial_order} is short for
\begin{alltt}
  partial_order le \isakeyword{for} le (\isakeyword{infixl} "\(\sqsubseteq\)" 50)\textrm{.}
\end{alltt}
  This short hand was used in the locale declarations of
  Section~\ref{sec:import}.
 *}

text{*
  The following locale declarations provide more examples.  A map
  @{text \<phi>} is a lattice homomorphism if it preserves meet and
  join. *}

  locale lattice_hom =
    le: lattice + le': lattice le' for le' (infixl "\<preceq>" 50) +
    fixes \<phi>
    assumes hom_meet: "\<phi> (x \<sqinter> y) = le'.meet (\<phi> x) (\<phi> y)"
      and hom_join: "\<phi> (x \<squnion> y) = le'.join (\<phi> x) (\<phi> y)"

text {* We omit the parameter instantiation in the first instance of
  @{term lattice}.  This causes the parameter @{text le} to be added
  to the \isakeyword{for} clause, and the locale has parameters
  @{text le} and @{text le'}.

  Before turning to the second example, we complete the locale by
  provinding infix syntax for the meet and join operations of the
  second lattice.
*}

  context lattice_hom begin
  abbreviation meet' (infixl "\<sqinter>''" 50) where "meet' \<equiv> le'.meet"
  abbreviation join' (infixl "\<squnion>''" 50) where "join' \<equiv> le'.join"
  end

text {* The next example pushes the short hand facilities.  A
  homomorphism is an endomorphism if both orders coincide. *}

  locale lattice_end = lattice_hom _ le

text {* The notation @{text _} enables to omit a parameter in a
  positional instantiation.  The omitted parameter, @{text le} becomes
  the parameter of the declared locale and is, in the following
  position used to instantiate the second parameter of @{text
  lattice_hom}.  The effect is that of identifying the first in second
  parameter of the homomorphism locale. *}

text {* The inheritance diagram of the situation we have now is shown
  in Figure~\ref{fig:hom}, where the dashed line depicts an
  interpretation which is introduced below.  Renamings are
  indicated by $\sqsubseteq \mapsto \preceq$ etc.  By looking at the
  inheritance diagram it would seem
  that two identical copies of each of the locales @{text
  partial_order} and @{text lattice} are imported by @{text
  lattice_end}.  This is not the case!  Inheritance paths with
  identical morphisms are automatically detected and
  the conclusions of the respective locales appear only once.

\begin{figure}
\hrule \vspace{2ex}
\begin{center}
\begin{tikzpicture}
  \node (o) at (0,0) {@{text partial_order}};
  \node (oh) at (1.5,-2) {@{text order_preserving}};
  \node (oh1) at (1.5,-0.7) {$\scriptscriptstyle \sqsubseteq \mapsto \sqsubseteq$};
  \node (oh2) at (0,-1.3) {$\scriptscriptstyle \sqsubseteq \mapsto \preceq$};
  \node (l) at (-1.5,-2) {@{text lattice}};
  \node (lh) at (0,-4) {@{text lattice_hom}};
  \node (lh1) at (0,-2.7) {$\scriptscriptstyle \sqsubseteq \mapsto \sqsubseteq$};
  \node (lh2) at (-1.5,-3.3) {$\scriptscriptstyle \sqsubseteq \mapsto \preceq$};
  \node (le) at (0,-6) {@{text lattice_end}};
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
  *}

text {* It can be shown easily that a lattice homomorphism is order
  preserving.  As the final example of this section, a locale
  interpretation is used to assert this: *}

  sublocale lattice_hom \<subseteq> order_preserving proof unfold_locales
    fix x y
    assume "x \<sqsubseteq> y"
    then have "y = (x \<squnion> y)" by (simp add: le.join_connection)
    then have "\<phi> y = (\<phi> x \<squnion>' \<phi> y)" by (simp add: hom_join [symmetric])
    then show "\<phi> x \<preceq> \<phi> y" by (simp add: le'.join_connection)
  qed

text (in lattice_hom) {*
  Theorems and other declarations --- syntax, in particular --- from
  the locale @{text order_preserving} are now active in @{text
  lattice_hom}, for example
  @{thm [source] hom_le}:
  @{thm [display, indent=2] hom_le}
  *}

(*
section {* Conditional Interpretation *}

  locale non_negative =
    fixes n :: int
    assumes non_negative: "0 \<le> n"

  interpretation partial_order "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"
    where "partial_order.less op \<le> (x::int) y = (x < y)"
    sorry

  sublocale non_negative \<subseteq> order_preserving "op \<le>" "op \<le>" "\<lambda>i. n * i"
    apply unfold_locales using non_negative apply - by (rule mult_left_mono)

  interpretation lattice "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"
    where min_eq: "lattice.meet op \<le> (x::int) y = min x y"
      and max_eq: "lattice.join op \<le> (x::int) y = max x y"
    sorry

    apply unfold_locales unfolding is_inf_def is_sup_def by arith+


  sublocale non_negative \<subseteq> lattice_end "op \<le>" "\<lambda>i. n * i"
    apply unfold_locales unfolding min_eq max_eq apply (case_tac "x \<le> y")
    unfolding min_def apply auto apply arith
    apply (rule sym)
    apply (rule the_equality)
  proof

  locale fspace_po = partial_order
  sublocale fspace_po \<subseteq> fspace: partial_order "\<lambda>f g. \<forall>x. f x \<sqsubseteq> g x"
(* fspace needed to disambiguate less etc *)
apply unfold_locales
apply auto
apply (rule) apply auto apply (blast intro: trans) done

*)

section {* Further Reading *}

text {* More information on locales and their interpretation is
  available.  For the locale hierarchy of import and interpretation
  dependencies see \cite{Ballarin2006a}; interpretations in theories
  and proofs are covered in \cite{Ballarin2006b}.  In the latter, I
  show how interpretation in proofs enables to reason about families
  of algebraic structures, which cannot be expressed with locales
  directly.

  Haftmann and Wenzel \cite{HaftmannWenzel2007} overcome a restriction
  of axiomatic type classes through a combination with locale
  interpretation.  The result is a Haskell-style class system with a
  facility to generate ML and Haskell code.  Classes are sufficient for
  simple specifications with a single type parameter.  The locales for
  orders and lattices presented in this tutorial fall into this
  category.  Order preserving maps, homomorphisms and vector spaces,
  on the other hand, do not.

  The locales reimplementation for Isabelle 2009 provides, among other
  improvements, a clean intergration with Isabelle/Isar's local theory
  mechnisms, which are described in \cite{HaftmannWenzel2009}.

  The original work of Kamm\"uller on locales \cite{KammullerEtAl1999}
  may be of interest from a historical perspective.  The mathematical
  background on orders and lattices is taken from Jacobson's textbook
  on algebra \cite[Chapter~8]{Jacobson1985}.

  The sources of this tutorial, which include all proofs, are
  available with the Isabelle distribution at
  \url{http://isabelle.in.tum.de}.
  *}

text {*
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
  & \textit{name} [``\textbf{?}'' $|$ ``\textbf{!}''] \\[2ex]

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
    \textit{qualified-name} ( \textit{pos-insts} $|$ \textit{named-inst} ) \\
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
  \textit{equations} & ::= &  \textbf{where} \textit{equation} ( \textbf{and}
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
  & | & \textbf{print\_locale} [ ``\textbf{!}'' ] \textit{locale} \\
  & | & \textbf{print\_interps} \textit{locale}
\end{tabular}
\end{center}
\hrule
\caption{Syntax of Locale Commands.}
\label{tab:commands}
\end{table}
  *}

text {* \textbf{Revision History.}  For the present third revision,
  which was completed in October 2009, much of the explanatory text
  has been rewritten.  In addition, inheritance of interpretation
  equations, which was not available for Isabelle 2009, but in the
  meantime has been implemented, is illustrated.  The second revision
  accommodates changes introduced by the locales reimplementation for
  Isabelle 2009.  Most notably, in complex specifications
  (\emph{locale expressions}) renaming has been generalised to
  instantiation.  *}

text {* \textbf{Acknowledgements.}  Alexander Krauss, Tobias Nipkow,
  Randy Pollack, Christian Sternagel and Makarius Wenzel have made
  useful comments on earlier versions of this document. *}

end
