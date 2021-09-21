(*<*)
theory Main_Doc
imports Main
begin

setup \<open>
  Document_Output.antiquotation_pretty_source \<^binding>\<open>term_type_only\<close> (Args.term -- Args.typ_abbrev)
    (fn ctxt => fn (t, T) =>
      (if fastype_of t = Sign.certify_typ (Proof_Context.theory_of ctxt) T then ()
       else error "term_type_only: type mismatch";
       Syntax.pretty_typ ctxt T))
\<close>
setup \<open>
  Document_Output.antiquotation_pretty_source \<^binding>\<open>expanded_typ\<close> Args.typ
    Syntax.pretty_typ
\<close>
(*>*)
text\<open>

\begin{abstract}
This document lists the main types, functions and syntax provided by theory \<^theory>\<open>Main\<close>. It is meant as a quick overview of what is available. For infix operators and their precedences see the final section. The sophisticated class structure is only hinted at. For details see \<^url>\<open>https://isabelle.in.tum.de/library/HOL\<close>.
\end{abstract}

\section*{HOL}

The basic logic: \<^prop>\<open>x = y\<close>, \<^const>\<open>True\<close>, \<^const>\<open>False\<close>, \<^prop>\<open>\<not> P\<close>, \<^prop>\<open>P \<and> Q\<close>,
\<^prop>\<open>P \<or> Q\<close>, \<^prop>\<open>P \<longrightarrow> Q\<close>, \<^prop>\<open>\<forall>x. P\<close>, \<^prop>\<open>\<exists>x. P\<close>, \<^prop>\<open>\<exists>! x. P\<close>,
\<^term>\<open>THE x. P\<close>.
\<^smallskip>

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>HOL.undefined\<close> & \<^typeof>\<open>HOL.undefined\<close>\\
\<^const>\<open>HOL.default\<close> & \<^typeof>\<open>HOL.default\<close>\\
\end{tabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<^term>\<open>\<not> (x = y)\<close> & @{term[source]"\<not> (x = y)"} & (\<^verbatim>\<open>~=\<close>)\\
@{term[source]"P \<longleftrightarrow> Q"} & \<^term>\<open>P \<longleftrightarrow> Q\<close> \\
\<^term>\<open>If x y z\<close> & @{term[source]"If x y z"}\\
\<^term>\<open>Let e\<^sub>1 (\<lambda>x. e\<^sub>2)\<close> & @{term[source]"Let e\<^sub>1 (\<lambda>x. e\<^sub>2)"}\\
\end{supertabular}


\section*{Orderings}

A collection of classes defining basic orderings:
preorder, partial order, linear order, dense linear order and wellorder.
\<^smallskip>

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
\<^const>\<open>Orderings.less_eq\<close> & \<^typeof>\<open>Orderings.less_eq\<close> & (\<^verbatim>\<open><=\<close>)\\
\<^const>\<open>Orderings.less\<close> & \<^typeof>\<open>Orderings.less\<close>\\
\<^const>\<open>Orderings.Least\<close> & \<^typeof>\<open>Orderings.Least\<close>\\
\<^const>\<open>Orderings.Greatest\<close> & \<^typeof>\<open>Orderings.Greatest\<close>\\
\<^const>\<open>Orderings.min\<close> & \<^typeof>\<open>Orderings.min\<close>\\
\<^const>\<open>Orderings.max\<close> & \<^typeof>\<open>Orderings.max\<close>\\
@{const[source] top} & \<^typeof>\<open>Orderings.top\<close>\\
@{const[source] bot} & \<^typeof>\<open>Orderings.bot\<close>\\
\<^const>\<open>Orderings.mono\<close> & \<^typeof>\<open>Orderings.mono\<close>\\
\<^const>\<open>Orderings.strict_mono\<close> & \<^typeof>\<open>Orderings.strict_mono\<close>\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term[source]"x \<ge> y"} & \<^term>\<open>x \<ge> y\<close> & (\<^verbatim>\<open>>=\<close>)\\
@{term[source]"x > y"} & \<^term>\<open>x > y\<close>\\
\<^term>\<open>\<forall>x\<le>y. P\<close> & @{term[source]"\<forall>x. x \<le> y \<longrightarrow> P"}\\
\<^term>\<open>\<exists>x\<le>y. P\<close> & @{term[source]"\<exists>x. x \<le> y \<and> P"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for $<$, $\ge$ and $>$}\\
\<^term>\<open>LEAST x. P\<close> & @{term[source]"Least (\<lambda>x. P)"}\\
\<^term>\<open>GREATEST x. P\<close> & @{term[source]"Greatest (\<lambda>x. P)"}\\
\end{supertabular}


\section*{Lattices}

Classes semilattice, lattice, distributive lattice and complete lattice (the
latter in theory \<^theory>\<open>HOL.Set\<close>).

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Lattices.inf\<close> & \<^typeof>\<open>Lattices.inf\<close>\\
\<^const>\<open>Lattices.sup\<close> & \<^typeof>\<open>Lattices.sup\<close>\\
\<^const>\<open>Complete_Lattices.Inf\<close> & @{term_type_only Complete_Lattices.Inf "'a set \<Rightarrow> 'a::Inf"}\\
\<^const>\<open>Complete_Lattices.Sup\<close> & @{term_type_only Complete_Lattices.Sup "'a set \<Rightarrow> 'a::Sup"}\\
\end{tabular}

\subsubsection*{Syntax}

Available via \<^theory_text>\<open>unbundle lattice_syntax\<close>.

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{text[source]"x \<sqsubseteq> y"} & \<^term>\<open>x \<le> y\<close>\\
@{text[source]"x \<sqsubset> y"} & \<^term>\<open>x < y\<close>\\
@{text[source]"x \<sqinter> y"} & \<^term>\<open>inf x y\<close>\\
@{text[source]"x \<squnion> y"} & \<^term>\<open>sup x y\<close>\\
@{text[source]"\<Sqinter>A"} & \<^term>\<open>Inf A\<close>\\
@{text[source]"\<Squnion>A"} & \<^term>\<open>Sup A\<close>\\
@{text[source]"\<top>"} & @{term[source] top}\\
@{text[source]"\<bottom>"} & @{term[source] bot}\\
\end{supertabular}


\section*{Set}

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
\<^const>\<open>Set.empty\<close> & @{term_type_only "Set.empty" "'a set"}\\
\<^const>\<open>Set.insert\<close> & @{term_type_only insert "'a\<Rightarrow>'a set\<Rightarrow>'a set"}\\
\<^const>\<open>Collect\<close> & @{term_type_only Collect "('a\<Rightarrow>bool)\<Rightarrow>'a set"}\\
\<^const>\<open>Set.member\<close> & @{term_type_only Set.member "'a\<Rightarrow>'a set\<Rightarrow>bool"} & (\<^verbatim>\<open>:\<close>)\\
\<^const>\<open>Set.union\<close> & @{term_type_only Set.union "'a set\<Rightarrow>'a set \<Rightarrow> 'a set"} & (\<^verbatim>\<open>Un\<close>)\\
\<^const>\<open>Set.inter\<close> & @{term_type_only Set.inter "'a set\<Rightarrow>'a set \<Rightarrow> 'a set"} & (\<^verbatim>\<open>Int\<close>)\\
\<^const>\<open>Union\<close> & @{term_type_only Union "'a set set\<Rightarrow>'a set"}\\
\<^const>\<open>Inter\<close> & @{term_type_only Inter "'a set set\<Rightarrow>'a set"}\\
\<^const>\<open>Pow\<close> & @{term_type_only Pow "'a set \<Rightarrow>'a set set"}\\
\<^const>\<open>UNIV\<close> & @{term_type_only UNIV "'a set"}\\
\<^const>\<open>image\<close> & @{term_type_only image "('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>'b set"}\\
\<^const>\<open>Ball\<close> & @{term_type_only Ball "'a set\<Rightarrow>('a\<Rightarrow>bool)\<Rightarrow>bool"}\\
\<^const>\<open>Bex\<close> & @{term_type_only Bex "'a set\<Rightarrow>('a\<Rightarrow>bool)\<Rightarrow>bool"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<open>{a\<^sub>1,\<dots>,a\<^sub>n}\<close> & \<open>insert a\<^sub>1 (\<dots> (insert a\<^sub>n {})\<dots>)\<close>\\
\<^term>\<open>a \<notin> A\<close> & @{term[source]"\<not>(x \<in> A)"}\\
\<^term>\<open>A \<subseteq> B\<close> & @{term[source]"A \<le> B"}\\
\<^term>\<open>A \<subset> B\<close> & @{term[source]"A < B"}\\
@{term[source]"A \<supseteq> B"} & @{term[source]"B \<le> A"}\\
@{term[source]"A \<supset> B"} & @{term[source]"B < A"}\\
\<^term>\<open>{x. P}\<close> & @{term[source]"Collect (\<lambda>x. P)"}\\
\<open>{t | x\<^sub>1 \<dots> x\<^sub>n. P}\<close> & \<open>{v. \<exists>x\<^sub>1 \<dots> x\<^sub>n. v = t \<and> P}\<close>\\
@{term[source]"\<Union>x\<in>I. A"} & @{term[source]"\<Union>((\<lambda>x. A) ` I)"} & (\texttt{UN})\\
@{term[source]"\<Union>x. A"} & @{term[source]"\<Union>((\<lambda>x. A) ` UNIV)"}\\
@{term[source]"\<Inter>x\<in>I. A"} & @{term[source]"\<Inter>((\<lambda>x. A) ` I)"} & (\texttt{INT})\\
@{term[source]"\<Inter>x. A"} & @{term[source]"\<Inter>((\<lambda>x. A) ` UNIV)"}\\
\<^term>\<open>\<forall>x\<in>A. P\<close> & @{term[source]"Ball A (\<lambda>x. P)"}\\
\<^term>\<open>\<exists>x\<in>A. P\<close> & @{term[source]"Bex A (\<lambda>x. P)"}\\
\<^term>\<open>range f\<close> & @{term[source]"f ` UNIV"}\\
\end{supertabular}


\section*{Fun}

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
\<^const>\<open>Fun.id\<close> & \<^typeof>\<open>Fun.id\<close>\\
\<^const>\<open>Fun.comp\<close> & \<^typeof>\<open>Fun.comp\<close> & (\texttt{o})\\
\<^const>\<open>Fun.inj_on\<close> & @{term_type_only Fun.inj_on "('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>bool"}\\
\<^const>\<open>Fun.inj\<close> & \<^typeof>\<open>Fun.inj\<close>\\
\<^const>\<open>Fun.surj\<close> & \<^typeof>\<open>Fun.surj\<close>\\
\<^const>\<open>Fun.bij\<close> & \<^typeof>\<open>Fun.bij\<close>\\
\<^const>\<open>Fun.bij_betw\<close> & @{term_type_only Fun.bij_betw "('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>'b set\<Rightarrow>bool"}\\
\<^const>\<open>Fun.fun_upd\<close> & \<^typeof>\<open>Fun.fun_upd\<close>\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>fun_upd f x y\<close> & @{term[source]"fun_upd f x y"}\\
\<open>f(x\<^sub>1:=y\<^sub>1,\<dots>,x\<^sub>n:=y\<^sub>n)\<close> & \<open>f(x\<^sub>1:=y\<^sub>1)\<dots>(x\<^sub>n:=y\<^sub>n)\<close>\\
\end{tabular}


\section*{Hilbert\_Choice}

Hilbert's selection ($\varepsilon$) operator: \<^term>\<open>SOME x. P\<close>.
\<^smallskip>

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Hilbert_Choice.inv_into\<close> & @{term_type_only Hilbert_Choice.inv_into "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"}
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>inv\<close> & @{term[source]"inv_into UNIV"}
\end{tabular}

\section*{Fixed Points}

Theory: \<^theory>\<open>HOL.Inductive\<close>.

Least and greatest fixed points in a complete lattice \<^typ>\<open>'a\<close>:

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Inductive.lfp\<close> & \<^typeof>\<open>Inductive.lfp\<close>\\
\<^const>\<open>Inductive.gfp\<close> & \<^typeof>\<open>Inductive.gfp\<close>\\
\end{tabular}

Note that in particular sets (\<^typ>\<open>'a \<Rightarrow> bool\<close>) are complete lattices.

\section*{Sum\_Type}

Type constructor \<open>+\<close>.

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Sum_Type.Inl\<close> & \<^typeof>\<open>Sum_Type.Inl\<close>\\
\<^const>\<open>Sum_Type.Inr\<close> & \<^typeof>\<open>Sum_Type.Inr\<close>\\
\<^const>\<open>Sum_Type.Plus\<close> & @{term_type_only Sum_Type.Plus "'a set\<Rightarrow>'b set\<Rightarrow>('a+'b)set"}
\end{tabular}


\section*{Product\_Type}

Types \<^typ>\<open>unit\<close> and \<open>\<times>\<close>.

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Product_Type.Unity\<close> & \<^typeof>\<open>Product_Type.Unity\<close>\\
\<^const>\<open>Pair\<close> & \<^typeof>\<open>Pair\<close>\\
\<^const>\<open>fst\<close> & \<^typeof>\<open>fst\<close>\\
\<^const>\<open>snd\<close> & \<^typeof>\<open>snd\<close>\\
\<^const>\<open>case_prod\<close> & \<^typeof>\<open>case_prod\<close>\\
\<^const>\<open>curry\<close> & \<^typeof>\<open>curry\<close>\\
\<^const>\<open>Product_Type.Sigma\<close> & @{term_type_only Product_Type.Sigma "'a set\<Rightarrow>('a\<Rightarrow>'b set)\<Rightarrow>('a*'b)set"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} ll @ {}}
\<^term>\<open>Pair a b\<close> & @{term[source]"Pair a b"}\\
\<^term>\<open>case_prod (\<lambda>x y. t)\<close> & @{term[source]"case_prod (\<lambda>x y. t)"}\\
\<^term>\<open>A \<times> B\<close> &  \<open>Sigma A (\<lambda>\<^latex>\<open>\_\<close>. B)\<close>
\end{tabular}

Pairs may be nested. Nesting to the right is printed as a tuple,
e.g.\ \mbox{\<^term>\<open>(a,b,c)\<close>} is really \mbox{\<open>(a, (b, c))\<close>.}
Pattern matching with pairs and tuples extends to all binders,
e.g.\ \mbox{\<^prop>\<open>\<forall>(x,y)\<in>A. P\<close>,} \<^term>\<open>{(x,y). P}\<close>, etc.


\section*{Relation}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Relation.converse\<close> & @{term_type_only Relation.converse "('a * 'b)set \<Rightarrow> ('b*'a)set"}\\
\<^const>\<open>Relation.relcomp\<close> & @{term_type_only Relation.relcomp "('a*'b)set\<Rightarrow>('b*'c)set\<Rightarrow>('a*'c)set"}\\
\<^const>\<open>Relation.Image\<close> & @{term_type_only Relation.Image "('a*'b)set\<Rightarrow>'a set\<Rightarrow>'b set"}\\
\<^const>\<open>Relation.inv_image\<close> & @{term_type_only Relation.inv_image "('a*'a)set\<Rightarrow>('b\<Rightarrow>'a)\<Rightarrow>('b*'b)set"}\\
\<^const>\<open>Relation.Id_on\<close> & @{term_type_only Relation.Id_on "'a set\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>Relation.Id\<close> & @{term_type_only Relation.Id "('a*'a)set"}\\
\<^const>\<open>Relation.Domain\<close> & @{term_type_only Relation.Domain "('a*'b)set\<Rightarrow>'a set"}\\
\<^const>\<open>Relation.Range\<close> & @{term_type_only Relation.Range "('a*'b)set\<Rightarrow>'b set"}\\
\<^const>\<open>Relation.Field\<close> & @{term_type_only Relation.Field "('a*'a)set\<Rightarrow>'a set"}\\
\<^const>\<open>Relation.refl_on\<close> & @{term_type_only Relation.refl_on "'a set\<Rightarrow>('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.refl\<close> & @{term_type_only Relation.refl "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.sym\<close> & @{term_type_only Relation.sym "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.antisym\<close> & @{term_type_only Relation.antisym "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.trans\<close> & @{term_type_only Relation.trans "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.irrefl\<close> & @{term_type_only Relation.irrefl "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.total_on\<close> & @{term_type_only Relation.total_on "'a set\<Rightarrow>('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Relation.total\<close> & @{term_type_only Relation.total "('a*'a)set\<Rightarrow>bool"}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<^term>\<open>converse r\<close> & @{term[source]"converse r"} & (\<^verbatim>\<open>^-1\<close>)
\end{tabular}
\<^medskip>

\noindent
Type synonym \ \<^typ>\<open>'a rel\<close> \<open>=\<close> @{expanded_typ "'a rel"}

\section*{Equiv\_Relations}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Equiv_Relations.equiv\<close> & @{term_type_only Equiv_Relations.equiv "'a set \<Rightarrow> ('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Equiv_Relations.quotient\<close> & @{term_type_only Equiv_Relations.quotient "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set"}\\
\<^const>\<open>Equiv_Relations.congruent\<close> & @{term_type_only Equiv_Relations.congruent "('a*'a)set\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>bool"}\\
\<^const>\<open>Equiv_Relations.congruent2\<close> & @{term_type_only Equiv_Relations.congruent2 "('a*'a)set\<Rightarrow>('b*'b)set\<Rightarrow>('a\<Rightarrow>'b\<Rightarrow>'c)\<Rightarrow>bool"}\\
%@ {const Equiv_Relations.} & @ {term_type_only Equiv_Relations. ""}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>congruent r f\<close> & @{term[source]"congruent r f"}\\
\<^term>\<open>congruent2 r r f\<close> & @{term[source]"congruent2 r r f"}\\
\end{tabular}


\section*{Transitive\_Closure}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Transitive_Closure.rtrancl\<close> & @{term_type_only Transitive_Closure.rtrancl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>Transitive_Closure.trancl\<close> & @{term_type_only Transitive_Closure.trancl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>Transitive_Closure.reflcl\<close> & @{term_type_only Transitive_Closure.reflcl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>Transitive_Closure.acyclic\<close> & @{term_type_only Transitive_Closure.acyclic "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>compower\<close> & @{term_type_only "(^^) :: ('a*'a)set\<Rightarrow>nat\<Rightarrow>('a*'a)set" "('a*'a)set\<Rightarrow>nat\<Rightarrow>('a*'a)set"}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<^term>\<open>rtrancl r\<close> & @{term[source]"rtrancl r"} & (\<^verbatim>\<open>^*\<close>)\\
\<^term>\<open>trancl r\<close> & @{term[source]"trancl r"} & (\<^verbatim>\<open>^+\<close>)\\
\<^term>\<open>reflcl r\<close> & @{term[source]"reflcl r"} & (\<^verbatim>\<open>^=\<close>)
\end{tabular}


\section*{Algebra}

Theories \<^theory>\<open>HOL.Groups\<close>, \<^theory>\<open>HOL.Rings\<close>, \<^theory>\<open>HOL.Fields\<close> and \<^theory>\<open>HOL.Divides\<close> define a large collection of classes describing common algebraic
structures from semigroups up to fields. Everything is done in terms of
overloaded operators:

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
\<open>0\<close> & \<^typeof>\<open>zero\<close>\\
\<open>1\<close> & \<^typeof>\<open>one\<close>\\
\<^const>\<open>plus\<close> & \<^typeof>\<open>plus\<close>\\
\<^const>\<open>minus\<close> & \<^typeof>\<open>minus\<close>\\
\<^const>\<open>uminus\<close> & \<^typeof>\<open>uminus\<close> & (\<^verbatim>\<open>-\<close>)\\
\<^const>\<open>times\<close> & \<^typeof>\<open>times\<close>\\
\<^const>\<open>inverse\<close> & \<^typeof>\<open>inverse\<close>\\
\<^const>\<open>divide\<close> & \<^typeof>\<open>divide\<close>\\
\<^const>\<open>abs\<close> & \<^typeof>\<open>abs\<close>\\
\<^const>\<open>sgn\<close> & \<^typeof>\<open>sgn\<close>\\
\<^const>\<open>Rings.dvd\<close> & \<^typeof>\<open>Rings.dvd\<close>\\
\<^const>\<open>divide\<close> & \<^typeof>\<open>divide\<close>\\
\<^const>\<open>modulo\<close> & \<^typeof>\<open>modulo\<close>\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>\<bar>x\<bar>\<close> & @{term[source] "abs x"}
\end{tabular}


\section*{Nat}

\<^datatype>\<open>nat\<close>
\<^bigskip>

\begin{tabular}{@ {} lllllll @ {}}
\<^term>\<open>(+) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> &
\<^term>\<open>(-) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> &
\<^term>\<open>(*) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> &
\<^term>\<open>(^) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> &
\<^term>\<open>(div) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close>&
\<^term>\<open>(mod) :: nat \<Rightarrow> nat \<Rightarrow> nat\<close>&
\<^term>\<open>(dvd) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close>\\
\<^term>\<open>(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> &
\<^term>\<open>(<) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> &
\<^term>\<open>min :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> &
\<^term>\<open>max :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> &
\<^term>\<open>Min :: nat set \<Rightarrow> nat\<close> &
\<^term>\<open>Max :: nat set \<Rightarrow> nat\<close>\\
\end{tabular}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Nat.of_nat\<close> & \<^typeof>\<open>Nat.of_nat\<close>\\
\<^term>\<open>(^^) :: ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a\<close> &
  @{term_type_only "(^^) :: ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"}
\end{tabular}

\section*{Int}

Type \<^typ>\<open>int\<close>
\<^bigskip>

\begin{tabular}{@ {} llllllll @ {}}
\<^term>\<open>(+) :: int \<Rightarrow> int \<Rightarrow> int\<close> &
\<^term>\<open>(-) :: int \<Rightarrow> int \<Rightarrow> int\<close> &
\<^term>\<open>uminus :: int \<Rightarrow> int\<close> &
\<^term>\<open>(*) :: int \<Rightarrow> int \<Rightarrow> int\<close> &
\<^term>\<open>(^) :: int \<Rightarrow> nat \<Rightarrow> int\<close> &
\<^term>\<open>(div) :: int \<Rightarrow> int \<Rightarrow> int\<close>&
\<^term>\<open>(mod) :: int \<Rightarrow> int \<Rightarrow> int\<close>&
\<^term>\<open>(dvd) :: int \<Rightarrow> int \<Rightarrow> bool\<close>\\
\<^term>\<open>(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool\<close> &
\<^term>\<open>(<) :: int \<Rightarrow> int \<Rightarrow> bool\<close> &
\<^term>\<open>min :: int \<Rightarrow> int \<Rightarrow> int\<close> &
\<^term>\<open>max :: int \<Rightarrow> int \<Rightarrow> int\<close> &
\<^term>\<open>Min :: int set \<Rightarrow> int\<close> &
\<^term>\<open>Max :: int set \<Rightarrow> int\<close>\\
\<^term>\<open>abs :: int \<Rightarrow> int\<close> &
\<^term>\<open>sgn :: int \<Rightarrow> int\<close>\\
\end{tabular}

\begin{tabular}{@ {} l @ {~::~} l l @ {}}
\<^const>\<open>Int.nat\<close> & \<^typeof>\<open>Int.nat\<close>\\
\<^const>\<open>Int.of_int\<close> & \<^typeof>\<open>Int.of_int\<close>\\
\<^const>\<open>Int.Ints\<close> & @{term_type_only Int.Ints "'a::ring_1 set"} & (\<^verbatim>\<open>Ints\<close>)
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>of_nat::nat\<Rightarrow>int\<close> & @{term[source]"of_nat"}\\
\end{tabular}


\section*{Finite\_Set}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Finite_Set.finite\<close> & @{term_type_only Finite_Set.finite "'a set\<Rightarrow>bool"}\\
\<^const>\<open>Finite_Set.card\<close> & @{term_type_only Finite_Set.card "'a set \<Rightarrow> nat"}\\
\<^const>\<open>Finite_Set.fold\<close> & @{term_type_only Finite_Set.fold "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"}\\
\end{supertabular}


\section*{Lattices\_Big}

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
\<^const>\<open>Lattices_Big.Min\<close> & \<^typeof>\<open>Lattices_Big.Min\<close>\\
\<^const>\<open>Lattices_Big.Max\<close> & \<^typeof>\<open>Lattices_Big.Max\<close>\\
\<^const>\<open>Lattices_Big.arg_min\<close> & \<^typeof>\<open>Lattices_Big.arg_min\<close>\\
\<^const>\<open>Lattices_Big.is_arg_min\<close> & \<^typeof>\<open>Lattices_Big.is_arg_min\<close>\\
\<^const>\<open>Lattices_Big.arg_max\<close> & \<^typeof>\<open>Lattices_Big.arg_max\<close>\\
\<^const>\<open>Lattices_Big.is_arg_max\<close> & \<^typeof>\<open>Lattices_Big.is_arg_max\<close>\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<^term>\<open>ARG_MIN f x. P\<close> & @{term[source]"arg_min f (\<lambda>x. P)"}\\
\<^term>\<open>ARG_MAX f x. P\<close> & @{term[source]"arg_max f (\<lambda>x. P)"}\\
\end{supertabular}


\section*{Groups\_Big}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Groups_Big.sum\<close> & @{term_type_only Groups_Big.sum "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b::comm_monoid_add"}\\
\<^const>\<open>Groups_Big.prod\<close> & @{term_type_only Groups_Big.prod "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b::comm_monoid_mult"}\\
\end{supertabular}


\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<^term>\<open>sum (\<lambda>x. x) A\<close> & @{term[source]"sum (\<lambda>x. x) A"} & (\<^verbatim>\<open>SUM\<close>)\\
\<^term>\<open>sum (\<lambda>x. t) A\<close> & @{term[source]"sum (\<lambda>x. t) A"}\\
@{term[source] "\<Sum>x|P. t"} & \<^term>\<open>\<Sum>x|P. t\<close>\\
\multicolumn{2}{@ {}l@ {}}{Similarly for \<open>\<Prod>\<close> instead of \<open>\<Sum>\<close>} & (\<^verbatim>\<open>PROD\<close>)\\
\end{supertabular}


\section*{Wellfounded}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Wellfounded.wf\<close> & @{term_type_only Wellfounded.wf "('a*'a)set\<Rightarrow>bool"}\\
\<^const>\<open>Wellfounded.acc\<close> & @{term_type_only Wellfounded.acc "('a*'a)set\<Rightarrow>'a set"}\\
\<^const>\<open>Wellfounded.measure\<close> & @{term_type_only Wellfounded.measure "('a\<Rightarrow>nat)\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>Wellfounded.lex_prod\<close> & @{term_type_only Wellfounded.lex_prod "('a*'a)set\<Rightarrow>('b*'b)set\<Rightarrow>(('a*'b)*('a*'b))set"}\\
\<^const>\<open>Wellfounded.mlex_prod\<close> & @{term_type_only Wellfounded.mlex_prod "('a\<Rightarrow>nat)\<Rightarrow>('a*'a)set\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>Wellfounded.less_than\<close> & @{term_type_only Wellfounded.less_than "(nat*nat)set"}\\
\<^const>\<open>Wellfounded.pred_nat\<close> & @{term_type_only Wellfounded.pred_nat "(nat*nat)set"}\\
\end{supertabular}


\section*{Set\_Interval} % \<^theory>\<open>HOL.Set_Interval\<close>

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>lessThan\<close> & @{term_type_only lessThan "'a::ord \<Rightarrow> 'a set"}\\
\<^const>\<open>atMost\<close> & @{term_type_only atMost "'a::ord \<Rightarrow> 'a set"}\\
\<^const>\<open>greaterThan\<close> & @{term_type_only greaterThan "'a::ord \<Rightarrow> 'a set"}\\
\<^const>\<open>atLeast\<close> & @{term_type_only atLeast "'a::ord \<Rightarrow> 'a set"}\\
\<^const>\<open>greaterThanLessThan\<close> & @{term_type_only greaterThanLessThan "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
\<^const>\<open>atLeastLessThan\<close> & @{term_type_only atLeastLessThan "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
\<^const>\<open>greaterThanAtMost\<close> & @{term_type_only greaterThanAtMost "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
\<^const>\<open>atLeastAtMost\<close> & @{term_type_only atLeastAtMost "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>lessThan y\<close> & @{term[source] "lessThan y"}\\
\<^term>\<open>atMost y\<close> & @{term[source] "atMost y"}\\
\<^term>\<open>greaterThan x\<close> & @{term[source] "greaterThan x"}\\
\<^term>\<open>atLeast x\<close> & @{term[source] "atLeast x"}\\
\<^term>\<open>greaterThanLessThan x y\<close> & @{term[source] "greaterThanLessThan x y"}\\
\<^term>\<open>atLeastLessThan x y\<close> & @{term[source] "atLeastLessThan x y"}\\
\<^term>\<open>greaterThanAtMost x y\<close> & @{term[source] "greaterThanAtMost x y"}\\
\<^term>\<open>atLeastAtMost x y\<close> & @{term[source] "atLeastAtMost x y"}\\
@{term[source] "\<Union>i\<le>n. A"} & @{term[source] "\<Union>i \<in> {..n}. A"}\\
@{term[source] "\<Union>i<n. A"} & @{term[source] "\<Union>i \<in> {..<n}. A"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for \<open>\<Inter>\<close> instead of \<open>\<Union>\<close>}\\
\<^term>\<open>sum (\<lambda>x. t) {a..b}\<close> & @{term[source] "sum (\<lambda>x. t) {a..b}"}\\
\<^term>\<open>sum (\<lambda>x. t) {a..<b}\<close> & @{term[source] "sum (\<lambda>x. t) {a..<b}"}\\
\<^term>\<open>sum (\<lambda>x. t) {..b}\<close> & @{term[source] "sum (\<lambda>x. t) {..b}"}\\
\<^term>\<open>sum (\<lambda>x. t) {..<b}\<close> & @{term[source] "sum (\<lambda>x. t) {..<b}"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for \<open>\<Prod>\<close> instead of \<open>\<Sum>\<close>}\\
\end{supertabular}


\section*{Power}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Power.power\<close> & \<^typeof>\<open>Power.power\<close>
\end{tabular}


\section*{Option}

\<^datatype>\<open>option\<close>
\<^bigskip>

\begin{tabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Option.the\<close> & \<^typeof>\<open>Option.the\<close>\\
\<^const>\<open>map_option\<close> & @{typ[source]"('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"}\\
\<^const>\<open>set_option\<close> & @{term_type_only set_option "'a option \<Rightarrow> 'a set"}\\
\<^const>\<open>Option.bind\<close> & @{term_type_only Option.bind "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"}
\end{tabular}

\section*{List}

\<^datatype>\<open>list\<close>
\<^bigskip>

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>List.append\<close> & \<^typeof>\<open>List.append\<close>\\
\<^const>\<open>List.butlast\<close> & \<^typeof>\<open>List.butlast\<close>\\
\<^const>\<open>List.concat\<close> & \<^typeof>\<open>List.concat\<close>\\
\<^const>\<open>List.distinct\<close> & \<^typeof>\<open>List.distinct\<close>\\
\<^const>\<open>List.drop\<close> & \<^typeof>\<open>List.drop\<close>\\
\<^const>\<open>List.dropWhile\<close> & \<^typeof>\<open>List.dropWhile\<close>\\
\<^const>\<open>List.filter\<close> & \<^typeof>\<open>List.filter\<close>\\
\<^const>\<open>List.find\<close> & \<^typeof>\<open>List.find\<close>\\
\<^const>\<open>List.fold\<close> & \<^typeof>\<open>List.fold\<close>\\
\<^const>\<open>List.foldr\<close> & \<^typeof>\<open>List.foldr\<close>\\
\<^const>\<open>List.foldl\<close> & \<^typeof>\<open>List.foldl\<close>\\
\<^const>\<open>List.hd\<close> & \<^typeof>\<open>List.hd\<close>\\
\<^const>\<open>List.last\<close> & \<^typeof>\<open>List.last\<close>\\
\<^const>\<open>List.length\<close> & \<^typeof>\<open>List.length\<close>\\
\<^const>\<open>List.lenlex\<close> & @{term_type_only List.lenlex "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
\<^const>\<open>List.lex\<close> & @{term_type_only List.lex "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
\<^const>\<open>List.lexn\<close> & @{term_type_only List.lexn "('a*'a)set\<Rightarrow>nat\<Rightarrow>('a list * 'a list)set"}\\
\<^const>\<open>List.lexord\<close> & @{term_type_only List.lexord "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
\<^const>\<open>List.listrel\<close> & @{term_type_only List.listrel "('a*'b)set\<Rightarrow>('a list * 'b list)set"}\\
\<^const>\<open>List.listrel1\<close> & @{term_type_only List.listrel1 "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
\<^const>\<open>List.lists\<close> & @{term_type_only List.lists "'a set\<Rightarrow>'a list set"}\\
\<^const>\<open>List.listset\<close> & @{term_type_only List.listset "'a set list \<Rightarrow> 'a list set"}\\
\<^const>\<open>Groups_List.sum_list\<close> & \<^typeof>\<open>Groups_List.sum_list\<close>\\
\<^const>\<open>Groups_List.prod_list\<close> & \<^typeof>\<open>Groups_List.prod_list\<close>\\
\<^const>\<open>List.list_all2\<close> & \<^typeof>\<open>List.list_all2\<close>\\
\<^const>\<open>List.list_update\<close> & \<^typeof>\<open>List.list_update\<close>\\
\<^const>\<open>List.map\<close> & \<^typeof>\<open>List.map\<close>\\
\<^const>\<open>List.measures\<close> & @{term_type_only List.measures "('a\<Rightarrow>nat)list\<Rightarrow>('a*'a)set"}\\
\<^const>\<open>List.nth\<close> & \<^typeof>\<open>List.nth\<close>\\
\<^const>\<open>List.nths\<close> & \<^typeof>\<open>List.nths\<close>\\
\<^const>\<open>List.remdups\<close> & \<^typeof>\<open>List.remdups\<close>\\
\<^const>\<open>List.removeAll\<close> & \<^typeof>\<open>List.removeAll\<close>\\
\<^const>\<open>List.remove1\<close> & \<^typeof>\<open>List.remove1\<close>\\
\<^const>\<open>List.replicate\<close> & \<^typeof>\<open>List.replicate\<close>\\
\<^const>\<open>List.rev\<close> & \<^typeof>\<open>List.rev\<close>\\
\<^const>\<open>List.rotate\<close> & \<^typeof>\<open>List.rotate\<close>\\
\<^const>\<open>List.rotate1\<close> & \<^typeof>\<open>List.rotate1\<close>\\
\<^const>\<open>List.set\<close> & @{term_type_only List.set "'a list \<Rightarrow> 'a set"}\\
\<^const>\<open>List.shuffles\<close> & \<^typeof>\<open>List.shuffles\<close>\\
\<^const>\<open>List.sort\<close> & \<^typeof>\<open>List.sort\<close>\\
\<^const>\<open>List.sorted\<close> & \<^typeof>\<open>List.sorted\<close>\\
\<^const>\<open>List.sorted_wrt\<close> & \<^typeof>\<open>List.sorted_wrt\<close>\\
\<^const>\<open>List.splice\<close> & \<^typeof>\<open>List.splice\<close>\\
\<^const>\<open>List.take\<close> & \<^typeof>\<open>List.take\<close>\\
\<^const>\<open>List.takeWhile\<close> & \<^typeof>\<open>List.takeWhile\<close>\\
\<^const>\<open>List.tl\<close> & \<^typeof>\<open>List.tl\<close>\\
\<^const>\<open>List.upt\<close> & \<^typeof>\<open>List.upt\<close>\\
\<^const>\<open>List.upto\<close> & \<^typeof>\<open>List.upto\<close>\\
\<^const>\<open>List.zip\<close> & \<^typeof>\<open>List.zip\<close>\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<open>[x\<^sub>1,\<dots>,x\<^sub>n]\<close> & \<open>x\<^sub>1 # \<dots> # x\<^sub>n # []\<close>\\
\<^term>\<open>[m..<n]\<close> & @{term[source]"upt m n"}\\
\<^term>\<open>[i..j]\<close> & @{term[source]"upto i j"}\\
\<^term>\<open>xs[n := x]\<close> & @{term[source]"list_update xs n x"}\\
\<^term>\<open>\<Sum>x\<leftarrow>xs. e\<close> & @{term[source]"listsum (map (\<lambda>x. e) xs)"}\\
\end{supertabular}
\<^medskip>

Filter input syntax \<open>[pat \<leftarrow> e. b]\<close>, where
\<open>pat\<close> is a tuple pattern, which stands for \<^term>\<open>filter (\<lambda>pat. b) e\<close>.

List comprehension input syntax: \<open>[e. q\<^sub>1, \<dots>, q\<^sub>n]\<close> where each
qualifier \<open>q\<^sub>i\<close> is either a generator \mbox{\<open>pat \<leftarrow> e\<close>} or a
guard, i.e.\ boolean expression.

\section*{Map}

Maps model partial functions and are often used as finite tables. However,
the domain of a map may be infinite.

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
\<^const>\<open>Map.empty\<close> & \<^typeof>\<open>Map.empty\<close>\\
\<^const>\<open>Map.map_add\<close> & \<^typeof>\<open>Map.map_add\<close>\\
\<^const>\<open>Map.map_comp\<close> & \<^typeof>\<open>Map.map_comp\<close>\\
\<^const>\<open>Map.restrict_map\<close> & @{term_type_only Map.restrict_map "('a\<Rightarrow>'b option)\<Rightarrow>'a set\<Rightarrow>('a\<Rightarrow>'b option)"}\\
\<^const>\<open>Map.dom\<close> & @{term_type_only Map.dom "('a\<Rightarrow>'b option)\<Rightarrow>'a set"}\\
\<^const>\<open>Map.ran\<close> & @{term_type_only Map.ran "('a\<Rightarrow>'b option)\<Rightarrow>'b set"}\\
\<^const>\<open>Map.map_le\<close> & \<^typeof>\<open>Map.map_le\<close>\\
\<^const>\<open>Map.map_of\<close> & \<^typeof>\<open>Map.map_of\<close>\\
\<^const>\<open>Map.map_upds\<close> & \<^typeof>\<open>Map.map_upds\<close>\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<^term>\<open>Map.empty\<close> & \<^term>\<open>\<lambda>x. None\<close>\\
\<^term>\<open>m(x:=Some y)\<close> & @{term[source]"m(x:=Some y)"}\\
\<open>m(x\<^sub>1\<mapsto>y\<^sub>1,\<dots>,x\<^sub>n\<mapsto>y\<^sub>n)\<close> & @{text[source]"m(x\<^sub>1\<mapsto>y\<^sub>1)\<dots>(x\<^sub>n\<mapsto>y\<^sub>n)"}\\
\<open>[x\<^sub>1\<mapsto>y\<^sub>1,\<dots>,x\<^sub>n\<mapsto>y\<^sub>n]\<close> & @{text[source]"Map.empty(x\<^sub>1\<mapsto>y\<^sub>1,\<dots>,x\<^sub>n\<mapsto>y\<^sub>n)"}\\
\<^term>\<open>map_upds m xs ys\<close> & @{term[source]"map_upds m xs ys"}\\
\end{tabular}

\section*{Infix operators in Main} % \<^theory>\<open>Main\<close>

\begin{center}
\begin{tabular}{llll}
 & Operator & precedence & associativity \\
\hline
Meta-logic & \<open>\<Longrightarrow>\<close> & 1 & right \\
& \<open>\<equiv>\<close> & 2 \\
\hline
Logic & \<open>\<and>\<close> & 35 & right \\
&\<open>\<or>\<close> & 30 & right \\
&\<open>\<longrightarrow>\<close>, \<open>\<longleftrightarrow>\<close> & 25 & right\\
&\<open>=\<close>, \<open>\<noteq>\<close> & 50 & left\\
\hline
Orderings & \<open>\<le>\<close>, \<open><\<close>, \<open>\<ge>\<close>, \<open>>\<close> & 50 \\
\hline
Sets & \<open>\<subseteq>\<close>, \<open>\<subset>\<close>, \<open>\<supseteq>\<close>, \<open>\<supset>\<close> & 50 \\
&\<open>\<in>\<close>, \<open>\<notin>\<close> & 50 \\
&\<open>\<inter>\<close> & 70 & left \\
&\<open>\<union>\<close> & 65 & left \\
\hline
Functions and Relations & \<open>\<circ>\<close> & 55 & left\\
&\<open>`\<close> & 90 & right\\
&\<open>O\<close> & 75 & right\\
&\<open>``\<close> & 90 & right\\
&\<open>^^\<close> & 80 & right\\
\hline
Numbers & \<open>+\<close>, \<open>-\<close> & 65 & left \\
&\<open>*\<close>, \<open>/\<close> & 70 & left \\
&\<open>div\<close>, \<open>mod\<close> & 70 & left\\
&\<open>^\<close> & 80 & right\\
&\<open>dvd\<close> & 50 \\
\hline
Lists & \<open>#\<close>, \<open>@\<close> & 65 & right\\
&\<open>!\<close> & 100 & left
\end{tabular}
\end{center}
\<close>
(*<*)
end
(*>*)
