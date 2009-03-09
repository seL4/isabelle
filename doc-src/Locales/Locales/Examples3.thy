(* $Id$ *)

theory Examples3
imports Examples
begin

subsection {* Third Version: Local Interpretation *}

text {* In the above example, the fact that @{text \<le>} is a partial
  order for the natural numbers was used in the proof of the
  second goal.  In general, proofs of the equations may involve
  theorems implied by the fact the assumptions of the instantiated
  locale hold for the instantiating structure.  If these theorems have
  been shown abstractly in the locale they can be made available
  conveniently in the context through an auxiliary local interpretation (keyword
  \isakeyword{interpret}).  This interpretation is inside the proof of the global
  interpretation.  The third revision of the example illustrates this.  *}

interpretation %visible nat: partial_order "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"
  where "partial_order.less (op \<le>) (x::nat) y = (x < y)"
proof -
  show "partial_order (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
    by unfold_locales auto
  then interpret nat: partial_order "op \<le> :: [nat, nat] \<Rightarrow> bool" .
  show "partial_order.less (op \<le>) (x::nat) y = (x < y)"
    unfolding nat.less_def by auto
qed

text {* The inner interpretation does not require an
  elaborate new proof, it is immediate from the preceeding fact and
  proved with ``.''.
  This interpretation enriches the local proof context by
  the very theorems also obtained in the interpretation from
  Section~\ref{sec:po-first}, and @{text nat.less_def} may directly be
  used to unfold the definition.  Theorems from the local
  interpretation disappear after leaving the proof context --- that
  is, after the closing \isakeyword{qed} --- and are
  then replaced by those with the desired substitutions of the strict
  order. *}


subsection {* Further Interpretations *}

text {* Further interpretations are necessary to reuse theorems from
  the other locales.  In @{text lattice} the operations @{text \<sqinter>} and
  @{text \<squnion>} are substituted by @{term "min :: nat \<Rightarrow> nat \<Rightarrow> nat"} and
  @{term "max :: nat \<Rightarrow> nat \<Rightarrow> nat"}.  The entire proof for the
  interpretation is reproduced in order to give an example of a more
  elaborate interpretation proof.  *}

interpretation %visible nat: lattice "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"
  where "lattice.meet op \<le> (x::nat) y = min x y"
    and "lattice.join op \<le> (x::nat) y = max x y"
proof -
  show "lattice (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"
    txt {* We have already shown that this is a partial order, *}
    apply unfold_locales
    txt {* hence only the lattice axioms remain to be shown: @{subgoals
      [display]}  After unfolding @{text is_inf} and @{text is_sup}, *}
    apply (unfold nat.is_inf_def nat.is_sup_def)
    txt {* the goals become @{subgoals [display]} which can be solved
      by Presburger arithmetic. *}
    by arith+
  txt {* In order to show the equations, we put ourselves in a
    situation where the lattice theorems can be used in a convenient way. *}
  then interpret nat: lattice "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool" .
  show "lattice.meet op \<le> (x::nat) y = min x y"
    by (bestsimp simp: nat.meet_def nat.is_inf_def)
  show "lattice.join op \<le> (x::nat) y = max x y"
    by (bestsimp simp: nat.join_def nat.is_sup_def)
qed

text {* That the relation @{text \<le>} is a total order completes this
  sequence of interpretations. *}

interpretation %visible nat: total_order "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"
  by unfold_locales arith

text {* Theorems that are available in the theory at this point are shown in
  Table~\ref{tab:nat-lattice}.

\begin{table}
\hrule
\vspace{2ex}
\begin{center}
\begin{tabular}{l}
  @{thm [source] nat.less_def} from locale @{text partial_order}: \\
  \quad @{thm nat.less_def} \\
  @{thm [source] nat.meet_left} from locale @{text lattice}: \\
  \quad @{thm nat.meet_left} \\
  @{thm [source] nat.join_distr} from locale @{text distrib_lattice}: \\
  \quad @{thm nat.join_distr} \\
  @{thm [source] nat.less_total} from locale @{text total_order}: \\
  \quad @{thm nat.less_total}
\end{tabular}
\end{center}
\hrule
\caption{Interpreted theorems for @{text \<le>} on the natural numbers.}
\label{tab:nat-lattice}
\end{table}

  Note that since the locale hierarchy reflects that total orders are
  distributive lattices, an explicit interpretation of distributive
  lattices for the order relation on natural numbers is not neccessary.

  Why not push this idea further and just give the last interpretation
  as a single interpretation instead of the sequence of three?  The
  reasons for this are twofold:
\begin{itemize}
\item
  Often it is easier to work in an incremental fashion, because later
  interpretations require theorems provided by earlier
  interpretations.
\item
  Assume that a definition is made in some locale $l_1$, and that $l_2$
  imports $l_1$.  Let an equation for the definition be
  proved in an interpretation of $l_2$.  The equation will be unfolded
  in interpretations of theorems added to $l_2$ or below in the import
  hierarchy, but not for theorems added above $l_2$.
  Hence, an equation interpreting a definition should always be given in
  an interpretation of the locale where the definition is made, not in
  an interpretation of a locale further down the hierarchy.
\end{itemize}
  *}


subsection {* Lattice @{text "dvd"} on @{typ nat} *}

text {* Divisibility on the natural numbers is a distributive lattice
  but not a total order.  Interpretation again proceeds
  incrementally. *}

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

text {* Note that there is no symbol for strict divisibility.  Instead,
  interpretation substitutes @{term "x dvd y \<and> x \<noteq> y"}.   *}

interpretation nat_dvd: lattice "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool"
  where nat_dvd_meet_eq:
      "lattice.meet op dvd = gcd"
    and nat_dvd_join_eq:
      "lattice.join op dvd = lcm"
proof -
  show "lattice (op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool)"
    apply unfold_locales
    apply (unfold nat_dvd.is_inf_def nat_dvd.is_sup_def)
    apply (rule_tac x = "gcd x y" in exI)
    apply auto [1]
    apply (rule_tac x = "lcm x y" in exI)
    apply (auto intro: lcm_dvd1 lcm_dvd2 lcm_least)
    done
  then interpret nat_dvd: lattice "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool" .
  show "lattice.meet op dvd = gcd"
    apply (auto simp add: expand_fun_eq)
    apply (unfold nat_dvd.meet_def)
    apply (rule the_equality)
    apply (unfold nat_dvd.is_inf_def)
    by auto
  show "lattice.join op dvd = lcm"
    apply (auto simp add: expand_fun_eq)
    apply (unfold nat_dvd.join_def)
    apply (rule the_equality)
    apply (unfold nat_dvd.is_sup_def)
    by (auto intro: lcm_dvd1 lcm_dvd2 lcm_least)
qed

text {* Equations @{thm [source] nat_dvd_meet_eq} and @{thm [source]
  nat_dvd_join_eq} are named since they are handy in the proof of
  the subsequent interpretation. *}

(*
definition
  is_lcm :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_lcm p m n \<longleftrightarrow> m dvd p \<and> n dvd p \<and>
    (\<forall>d. m dvd d \<longrightarrow> n dvd d \<longrightarrow> p dvd d)"

lemma is_gcd: "is_lcm (lcm (m, n)) m n"
  by (simp add: is_lcm_def lcm_least)

lemma gcd_lcm_distr_lemma:
  "[| is_gcd g1 x l1; is_lcm l1 y z; is_gcd g2 x y; is_gcd g3 x z |] ==> is_lcm g1 g2 g3"
apply (unfold is_gcd_def is_lcm_def dvd_def)
apply (clarsimp simp: mult_ac)
apply (blast intro: mult_is_0)
thm mult_is_0 [THEN iffD1]
*)

lemma %invisible gcd_lcm_distr:
  "gcd x (lcm y z) = lcm (gcd x y) (gcd x z)" sorry

interpretation %visible nat_dvd:
  distrib_lattice "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool"
  apply unfold_locales
  txt {* @{subgoals [display]} *}
  apply (unfold nat_dvd_meet_eq nat_dvd_join_eq)
  txt {* @{subgoals [display]} *}
  apply (rule gcd_lcm_distr) done


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

text {*
  The full syntax of the interpretation commands is shown in
  Table~\ref{tab:commands}.  The grammar refers to
  \textit{expr}, which stands for a \emph{locale} expression.  Locale
  expressions are discussed in Section~\ref{sec:expressions}.
  *}


section {* Locale Expressions \label{sec:expressions} *}

text {*
  A map @{term \<phi>} between partial orders @{text \<sqsubseteq>} and @{text \<preceq>}
  is called order preserving if @{text "x \<sqsubseteq> y"} implies @{text "\<phi> x \<preceq>
  \<phi> y"}.  This situation is more complex than those encountered so
  far: it involves two partial orders, and it is desirable to use the
  existing locale for both.

  Inspecting the grammar of locale commands in
  Table~\ref{tab:commands} reveals that the import of a locale can be
  more than just a single locale.  In general, the import is a
  \emph{locale expression}.  Locale expressions enable to combine locales
  and rename parameters.  A locale name is a locale expression.  If
  $e_1$ and $e_2$ are locale expressions then $e_1 + e_2$ is their
  \emph{merge}.  If $e$ is an expression, then $e~q_1 \ldots q_n$ is
  a \emph{renamed expression} where the parameters in $e$ are renamed
  to $q_1 \ldots q_n$.  Using a locale expression, a locale for order
  preserving maps can be declared in the following way.  *}

  locale order_preserving =
    le: partial_order + le': partial_order le' for le' (infixl "\<preceq>" 50) +
    fixes \<phi> :: "'a \<Rightarrow> 'b"
    assumes hom_le: "x \<sqsubseteq> y \<Longrightarrow> \<phi> x \<preceq> \<phi> y"

text {* The second line contains the expression, which is the
  merge of two partial order locales.  The parameter of the second one
  is @{text le'} with new infix syntax @{text \<preceq>}.  The
  parameters of the entire locale are @{text le}, @{text le'} and
  @{text \<phi>}.  This is their \emph{canonical order},
  which is obtained by a left-to-right traversal of the expression,
  where only the new parameters are appended to the end of the list.  The
  parameters introduced in the locale elements of the declaration
  follow.

  In renamings parameters are referred to by position in the canonical
  order; an underscore is used to skip a parameter position, which is
  then not renamed.  Renaming deletes the syntax of a parameter unless
  a new mixfix annotation is given.

  Parameter renamings are morphisms between locales.  These can be
  lifted to terms and theorems and thus be applied to assumptions and
  conclusions.  The assumption of a merge is the conjunction of the
  assumptions of the merged locale.  The conclusions of a merge are
  obtained by appending the conclusions of the left locale and of the
  right locale.  *}

text {* The locale @{text order_preserving} contains theorems for both
  orders @{text \<sqsubseteq>} and @{text \<preceq>}.  How can one refer to a theorem for
  a particular order, @{text \<sqsubseteq>} or @{text \<preceq>}?  Names in locales are
  qualified by the locale parameters.  More precisely, a name is
  qualified by the parameters of the locale in which its declaration
  occurs.  Here are examples: *}

context %invisible order_preserving begin

text {*
  @{thm [source] le.less_le_trans}: @{thm le.less_le_trans}

  @{thm [source] hom_le}: @{thm hom_le}
  *}

text {* When renaming a locale, the morphism is also applied
  to the qualifiers.  Hence theorems for the partial order @{text \<preceq>}
  are qualified by @{text le'}.  For example, @{thm [source]
  le'.less_le_trans}: @{thm [display, indent=2] le'.less_le_trans} *}

end %invisible

text {* This example reveals that there is no infix syntax for the strict
  version of @{text \<preceq>}!  This can, of course, not be introduced
  automatically, but it can be declared manually through an abbreviation.
  *}

  abbreviation (in order_preserving)
    less' (infixl "\<prec>" 50) where "less' \<equiv> partial_order.less le'"

text (in order_preserving) {* Now the theorem is displayed nicely as
  @{thm le'.less_le_trans}.  *}

text {* Not only names of theorems are qualified.  In fact, all names
  are qualified, in particular names introduced by definitions and
  abbreviations.  The name of the strict order of @{text \<sqsubseteq>} is @{text
  le.less} and therefore @{text le'.less} is the name of the strict
  order of @{text \<preceq>}.  Hence, the equation in the above abbreviation
  could have been written as @{text "less' \<equiv> le'.less"}. *}

text {* Two more locales illustrate working with locale expressions.
  A map @{text \<phi>} is a lattice homomorphism if it preserves meet and join. *}

  locale lattice_hom = le: lattice + le': lattice le' for le' (infixl "\<preceq>" 50) +
    fixes \<phi>
    assumes hom_meet:
	"\<phi> (lattice.meet le x y) = lattice.meet le' (\<phi> x) (\<phi> y)"
      and hom_join:
	"\<phi> (lattice.join le x y) = lattice.join le' (\<phi> x) (\<phi> y)"

  abbreviation (in lattice_hom)
    meet' (infixl "\<sqinter>''" 50) where "meet' \<equiv> le'.meet"
  abbreviation (in lattice_hom)
    join' (infixl "\<squnion>''" 50) where "join' \<equiv> le'.join"

text {* A homomorphism is an endomorphism if both orders coincide. *}

  locale lattice_end =
    lattice_hom le le for le (infixl "\<sqsubseteq>" 50)

text {* The inheritance diagram of the situation we have now is shown
  in Figure~\ref{fig:hom}, where the dashed line depicts an
  interpretation which is introduced below.  Renamings are
  indicated by $\sqsubseteq \mapsto \preceq$ etc.  The expression
  imported by @{text lattice_end} identifies the first and second
  parameter of @{text lattice_hom}.  By looking at the inheritance diagram it would seem
  that two identical copies of each of the locales @{text
  partial_order} and @{text lattice} are imported.  This is not the
  case!  Inheritance paths with identical morphisms are detected and
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
  interpretation is used to assert this. *}

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
  @{thm [source] le'.less_le_trans}:
  @{thm le'.less_le_trans}
  *}



section {* Further Reading *}

text {* More information on locales and their interpretation is
  available.  For the locale hierarchy of import and interpretation
  dependencies see \cite{Ballarin2006a}; interpretations in theories
  and proofs are covered in \cite{Ballarin2006b}.  In the latter, we
  show how interpretation in proofs enables to reason about families
  of algebraic structures, which cannot be expressed with locales
  directly.

  Haftmann and Wenzel \cite{HaftmannWenzel2007} overcome a restriction
  of axiomatic type classes through a combination with locale
  interpretation.  The result is a Haskell-style class system with a
  facility to generate Haskell code.  Classes are sufficient for
  simple specifications with a single type parameter.  The locales for
  orders and lattices presented in this tutorial fall into this
  category.  Order preserving maps, homomorphisms and vector spaces,
  on the other hand, do not.

  The original work of Kamm\"uller on locales \cite{KammullerEtAl1999}
  may be of interest from a historical perspective.  The mathematical
  background on orders and lattices is taken from Jacobson's textbook
  on algebra \cite[Chapter~8]{Jacobson1985}.
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
  & \textit{name} [``\textbf{!}''] \\[2ex]

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
  & [ \textit{qualifier} \textbf{:} ]
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
  & \textbf{print\_locale} [ ``\textbf{!}'' ] \textit{locale} \\
  & | & \textbf{print\_locales} 
\end{tabular}
\end{center}
\hrule
\caption{Syntax of Locale Commands (abridged).}
\label{tab:commands}
\end{table}
  *}

text {* \textbf{Acknowledgements.}  Alexander Krauss, Tobias Nipkow,
  Christian Sternagel and Makarius Wenzel have made useful comments on
  a draft of this document. *}

end
