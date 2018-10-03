(*<*)
theory Main_Doc
imports Main
begin

setup \<open>
  Thy_Output.antiquotation_pretty_source @{binding term_type_only} (Args.term -- Args.typ_abbrev)
    (fn ctxt => fn (t, T) =>
      (if fastype_of t = Sign.certify_typ (Proof_Context.theory_of ctxt) T then ()
       else error "term_type_only: type mismatch";
       Syntax.pretty_typ ctxt T))
\<close>
setup \<open>
  Thy_Output.antiquotation_pretty_source @{binding expanded_typ} Args.typ
    Syntax.pretty_typ
\<close>
(*>*)
text\<open>

\begin{abstract}
This document lists the main types, functions and syntax provided by theory @{theory Main}. It is meant as a quick overview of what is available. For infix operators and their precedences see the final section. The sophisticated class structure is only hinted at. For details see \<^url>\<open>https://isabelle.in.tum.de/library/HOL\<close>.
\end{abstract}

\section*{HOL}

The basic logic: @{prop "x = y"}, @{const True}, @{const False}, @{prop "\<not> P"}, @{prop"P \<and> Q"},
@{prop "P \<or> Q"}, @{prop "P \<longrightarrow> Q"}, @{prop "\<forall>x. P"}, @{prop "\<exists>x. P"}, @{prop"\<exists>! x. P"},
@{term"THE x. P"}.
\<^smallskip>

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const HOL.undefined} & @{typeof HOL.undefined}\\
@{const HOL.default} & @{typeof HOL.default}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term"\<not> (x = y)"} & @{term[source]"\<not> (x = y)"} & (\<^verbatim>\<open>~=\<close>)\\
@{term[source]"P \<longleftrightarrow> Q"} & @{term"P \<longleftrightarrow> Q"} \\
@{term"If x y z"} & @{term[source]"If x y z"}\\
@{term"Let e\<^sub>1 (\<lambda>x. e\<^sub>2)"} & @{term[source]"Let e\<^sub>1 (\<lambda>x. e\<^sub>2)"}\\
\end{supertabular}


\section*{Orderings}

A collection of classes defining basic orderings:
preorder, partial order, linear order, dense linear order and wellorder.
\<^smallskip>

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
@{const Orderings.less_eq} & @{typeof Orderings.less_eq} & (\<^verbatim>\<open><=\<close>)\\
@{const Orderings.less} & @{typeof Orderings.less}\\
@{const Orderings.Least} & @{typeof Orderings.Least}\\
@{const Orderings.Greatest} & @{typeof Orderings.Greatest}\\
@{const Orderings.min} & @{typeof Orderings.min}\\
@{const Orderings.max} & @{typeof Orderings.max}\\
@{const[source] top} & @{typeof Orderings.top}\\
@{const[source] bot} & @{typeof Orderings.bot}\\
@{const Orderings.mono} & @{typeof Orderings.mono}\\
@{const Orderings.strict_mono} & @{typeof Orderings.strict_mono}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term[source]"x \<ge> y"} & @{term"x \<ge> y"} & (\<^verbatim>\<open>>=\<close>)\\
@{term[source]"x > y"} & @{term"x > y"}\\
@{term "\<forall>x\<le>y. P"} & @{term[source]"\<forall>x. x \<le> y \<longrightarrow> P"}\\
@{term "\<exists>x\<le>y. P"} & @{term[source]"\<exists>x. x \<le> y \<and> P"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for $<$, $\ge$ and $>$}\\
@{term "LEAST x. P"} & @{term[source]"Least (\<lambda>x. P)"}\\
@{term "GREATEST x. P"} & @{term[source]"Greatest (\<lambda>x. P)"}\\
\end{supertabular}


\section*{Lattices}

Classes semilattice, lattice, distributive lattice and complete lattice (the
latter in theory @{theory HOL.Set}).

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Lattices.inf} & @{typeof Lattices.inf}\\
@{const Lattices.sup} & @{typeof Lattices.sup}\\
@{const Complete_Lattices.Inf} & @{term_type_only Complete_Lattices.Inf "'a set \<Rightarrow> 'a::Inf"}\\
@{const Complete_Lattices.Sup} & @{term_type_only Complete_Lattices.Sup "'a set \<Rightarrow> 'a::Sup"}\\
\end{tabular}

\subsubsection*{Syntax}

Available by loading theory \<open>Lattice_Syntax\<close> in directory \<open>Library\<close>.

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{text[source]"x \<sqsubseteq> y"} & @{term"x \<le> y"}\\
@{text[source]"x \<sqsubset> y"} & @{term"x < y"}\\
@{text[source]"x \<sqinter> y"} & @{term"inf x y"}\\
@{text[source]"x \<squnion> y"} & @{term"sup x y"}\\
@{text[source]"\<Sqinter>A"} & @{term"Inf A"}\\
@{text[source]"\<Squnion>A"} & @{term"Sup A"}\\
@{text[source]"\<top>"} & @{term[source] top}\\
@{text[source]"\<bottom>"} & @{term[source] bot}\\
\end{supertabular}


\section*{Set}

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
@{const Set.empty} & @{term_type_only "Set.empty" "'a set"}\\
@{const Set.insert} & @{term_type_only insert "'a\<Rightarrow>'a set\<Rightarrow>'a set"}\\
@{const Collect} & @{term_type_only Collect "('a\<Rightarrow>bool)\<Rightarrow>'a set"}\\
@{const Set.member} & @{term_type_only Set.member "'a\<Rightarrow>'a set\<Rightarrow>bool"} & (\<^verbatim>\<open>:\<close>)\\
@{const Set.union} & @{term_type_only Set.union "'a set\<Rightarrow>'a set \<Rightarrow> 'a set"} & (\<^verbatim>\<open>Un\<close>)\\
@{const Set.inter} & @{term_type_only Set.inter "'a set\<Rightarrow>'a set \<Rightarrow> 'a set"} & (\<^verbatim>\<open>Int\<close>)\\
@{const UNION} & @{term_type_only UNION "'a set\<Rightarrow>('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"}\\
@{const INTER} & @{term_type_only INTER "'a set\<Rightarrow>('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"}\\
@{const Union} & @{term_type_only Union "'a set set\<Rightarrow>'a set"}\\
@{const Inter} & @{term_type_only Inter "'a set set\<Rightarrow>'a set"}\\
@{const Pow} & @{term_type_only Pow "'a set \<Rightarrow>'a set set"}\\
@{const UNIV} & @{term_type_only UNIV "'a set"}\\
@{const image} & @{term_type_only image "('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>'b set"}\\
@{const Ball} & @{term_type_only Ball "'a set\<Rightarrow>('a\<Rightarrow>bool)\<Rightarrow>bool"}\\
@{const Bex} & @{term_type_only Bex "'a set\<Rightarrow>('a\<Rightarrow>bool)\<Rightarrow>bool"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
\<open>{a\<^sub>1,\<dots>,a\<^sub>n}\<close> & \<open>insert a\<^sub>1 (\<dots> (insert a\<^sub>n {})\<dots>)\<close>\\
@{term "a \<notin> A"} & @{term[source]"\<not>(x \<in> A)"}\\
@{term "A \<subseteq> B"} & @{term[source]"A \<le> B"}\\
@{term "A \<subset> B"} & @{term[source]"A < B"}\\
@{term[source]"A \<supseteq> B"} & @{term[source]"B \<le> A"}\\
@{term[source]"A \<supset> B"} & @{term[source]"B < A"}\\
@{term "{x. P}"} & @{term[source]"Collect (\<lambda>x. P)"}\\
\<open>{t | x\<^sub>1 \<dots> x\<^sub>n. P}\<close> & \<open>{v. \<exists>x\<^sub>1 \<dots> x\<^sub>n. v = t \<and> P}\<close>\\
@{term[source]"\<Union>x\<in>I. A"} & @{term[source]"UNION I (\<lambda>x. A)"} & (\texttt{UN})\\
@{term[source]"\<Union>x. A"} & @{term[source]"UNION UNIV (\<lambda>x. A)"}\\
@{term[source]"\<Inter>x\<in>I. A"} & @{term[source]"INTER I (\<lambda>x. A)"} & (\texttt{INT})\\
@{term[source]"\<Inter>x. A"} & @{term[source]"INTER UNIV (\<lambda>x. A)"}\\
@{term "\<forall>x\<in>A. P"} & @{term[source]"Ball A (\<lambda>x. P)"}\\
@{term "\<exists>x\<in>A. P"} & @{term[source]"Bex A (\<lambda>x. P)"}\\
@{term "range f"} & @{term[source]"f ` UNIV"}\\
\end{supertabular}


\section*{Fun}

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
@{const "Fun.id"} & @{typeof Fun.id}\\
@{const "Fun.comp"} & @{typeof Fun.comp} & (\texttt{o})\\
@{const "Fun.inj_on"} & @{term_type_only Fun.inj_on "('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>bool"}\\
@{const "Fun.inj"} & @{typeof Fun.inj}\\
@{const "Fun.surj"} & @{typeof Fun.surj}\\
@{const "Fun.bij"} & @{typeof Fun.bij}\\
@{const "Fun.bij_betw"} & @{term_type_only Fun.bij_betw "('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>'b set\<Rightarrow>bool"}\\
@{const "Fun.fun_upd"} & @{typeof Fun.fun_upd}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"fun_upd f x y"} & @{term[source]"fun_upd f x y"}\\
\<open>f(x\<^sub>1:=y\<^sub>1,\<dots>,x\<^sub>n:=y\<^sub>n)\<close> & \<open>f(x\<^sub>1:=y\<^sub>1)\<dots>(x\<^sub>n:=y\<^sub>n)\<close>\\
\end{tabular}


\section*{Hilbert\_Choice}

Hilbert's selection ($\varepsilon$) operator: @{term"SOME x. P"}.
\<^smallskip>

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Hilbert_Choice.inv_into} & @{term_type_only Hilbert_Choice.inv_into "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"}
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term inv} & @{term[source]"inv_into UNIV"}
\end{tabular}

\section*{Fixed Points}

Theory: @{theory HOL.Inductive}.

Least and greatest fixed points in a complete lattice @{typ 'a}:

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Inductive.lfp} & @{typeof Inductive.lfp}\\
@{const Inductive.gfp} & @{typeof Inductive.gfp}\\
\end{tabular}

Note that in particular sets (@{typ"'a \<Rightarrow> bool"}) are complete lattices.

\section*{Sum\_Type}

Type constructor \<open>+\<close>.

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Sum_Type.Inl} & @{typeof Sum_Type.Inl}\\
@{const Sum_Type.Inr} & @{typeof Sum_Type.Inr}\\
@{const Sum_Type.Plus} & @{term_type_only Sum_Type.Plus "'a set\<Rightarrow>'b set\<Rightarrow>('a+'b)set"}
\end{tabular}


\section*{Product\_Type}

Types @{typ unit} and \<open>\<times>\<close>.

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Product_Type.Unity} & @{typeof Product_Type.Unity}\\
@{const Pair} & @{typeof Pair}\\
@{const fst} & @{typeof fst}\\
@{const snd} & @{typeof snd}\\
@{const case_prod} & @{typeof case_prod}\\
@{const curry} & @{typeof curry}\\
@{const Product_Type.Sigma} & @{term_type_only Product_Type.Sigma "'a set\<Rightarrow>('a\<Rightarrow>'b set)\<Rightarrow>('a*'b)set"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} ll @ {}}
@{term "Pair a b"} & @{term[source]"Pair a b"}\\
@{term "case_prod (\<lambda>x y. t)"} & @{term[source]"case_prod (\<lambda>x y. t)"}\\
@{term "A \<times> B"} &  \<open>Sigma A (\<lambda>\<^latex>\<open>\_\<close>. B)\<close>
\end{tabular}

Pairs may be nested. Nesting to the right is printed as a tuple,
e.g.\ \mbox{@{term "(a,b,c)"}} is really \mbox{\<open>(a, (b, c))\<close>.}
Pattern matching with pairs and tuples extends to all binders,
e.g.\ \mbox{@{prop "\<forall>(x,y)\<in>A. P"},} @{term "{(x,y). P}"}, etc.


\section*{Relation}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Relation.converse} & @{term_type_only Relation.converse "('a * 'b)set \<Rightarrow> ('b*'a)set"}\\
@{const Relation.relcomp} & @{term_type_only Relation.relcomp "('a*'b)set\<Rightarrow>('b*'c)set\<Rightarrow>('a*'c)set"}\\
@{const Relation.Image} & @{term_type_only Relation.Image "('a*'b)set\<Rightarrow>'a set\<Rightarrow>'b set"}\\
@{const Relation.inv_image} & @{term_type_only Relation.inv_image "('a*'a)set\<Rightarrow>('b\<Rightarrow>'a)\<Rightarrow>('b*'b)set"}\\
@{const Relation.Id_on} & @{term_type_only Relation.Id_on "'a set\<Rightarrow>('a*'a)set"}\\
@{const Relation.Id} & @{term_type_only Relation.Id "('a*'a)set"}\\
@{const Relation.Domain} & @{term_type_only Relation.Domain "('a*'b)set\<Rightarrow>'a set"}\\
@{const Relation.Range} & @{term_type_only Relation.Range "('a*'b)set\<Rightarrow>'b set"}\\
@{const Relation.Field} & @{term_type_only Relation.Field "('a*'a)set\<Rightarrow>'a set"}\\
@{const Relation.refl_on} & @{term_type_only Relation.refl_on "'a set\<Rightarrow>('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.refl} & @{term_type_only Relation.refl "('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.sym} & @{term_type_only Relation.sym "('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.antisym} & @{term_type_only Relation.antisym "('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.trans} & @{term_type_only Relation.trans "('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.irrefl} & @{term_type_only Relation.irrefl "('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.total_on} & @{term_type_only Relation.total_on "'a set\<Rightarrow>('a*'a)set\<Rightarrow>bool"}\\
@{const Relation.total} & @{term_type_only Relation.total "('a*'a)set\<Rightarrow>bool"}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term"converse r"} & @{term[source]"converse r"} & (\<^verbatim>\<open>^-1\<close>)
\end{tabular}
\<^medskip>

\noindent
Type synonym \ @{typ"'a rel"} \<open>=\<close> @{expanded_typ "'a rel"}

\section*{Equiv\_Relations}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Equiv_Relations.equiv} & @{term_type_only Equiv_Relations.equiv "'a set \<Rightarrow> ('a*'a)set\<Rightarrow>bool"}\\
@{const Equiv_Relations.quotient} & @{term_type_only Equiv_Relations.quotient "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set set"}\\
@{const Equiv_Relations.congruent} & @{term_type_only Equiv_Relations.congruent "('a*'a)set\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>bool"}\\
@{const Equiv_Relations.congruent2} & @{term_type_only Equiv_Relations.congruent2 "('a*'a)set\<Rightarrow>('b*'b)set\<Rightarrow>('a\<Rightarrow>'b\<Rightarrow>'c)\<Rightarrow>bool"}\\
%@ {const Equiv_Relations.} & @ {term_type_only Equiv_Relations. ""}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"congruent r f"} & @{term[source]"congruent r f"}\\
@{term"congruent2 r r f"} & @{term[source]"congruent2 r r f"}\\
\end{tabular}


\section*{Transitive\_Closure}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Transitive_Closure.rtrancl} & @{term_type_only Transitive_Closure.rtrancl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Transitive_Closure.trancl} & @{term_type_only Transitive_Closure.trancl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Transitive_Closure.reflcl} & @{term_type_only Transitive_Closure.reflcl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Transitive_Closure.acyclic} & @{term_type_only Transitive_Closure.acyclic "('a*'a)set\<Rightarrow>bool"}\\
@{const compower} & @{term_type_only "(^^) :: ('a*'a)set\<Rightarrow>nat\<Rightarrow>('a*'a)set" "('a*'a)set\<Rightarrow>nat\<Rightarrow>('a*'a)set"}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term"rtrancl r"} & @{term[source]"rtrancl r"} & (\<^verbatim>\<open>^*\<close>)\\
@{term"trancl r"} & @{term[source]"trancl r"} & (\<^verbatim>\<open>^+\<close>)\\
@{term"reflcl r"} & @{term[source]"reflcl r"} & (\<^verbatim>\<open>^=\<close>)
\end{tabular}


\section*{Algebra}

Theories @{theory HOL.Groups}, @{theory HOL.Rings}, @{theory HOL.Fields} and @{theory
HOL.Divides} define a large collection of classes describing common algebraic
structures from semigroups up to fields. Everything is done in terms of
overloaded operators:

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
\<open>0\<close> & @{typeof zero}\\
\<open>1\<close> & @{typeof one}\\
@{const plus} & @{typeof plus}\\
@{const minus} & @{typeof minus}\\
@{const uminus} & @{typeof uminus} & (\<^verbatim>\<open>-\<close>)\\
@{const times} & @{typeof times}\\
@{const inverse} & @{typeof inverse}\\
@{const divide} & @{typeof divide}\\
@{const abs} & @{typeof abs}\\
@{const sgn} & @{typeof sgn}\\
@{const Rings.dvd} & @{typeof Rings.dvd}\\
@{const divide} & @{typeof divide}\\
@{const modulo} & @{typeof modulo}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term "\<bar>x\<bar>"} & @{term[source] "abs x"}
\end{tabular}


\section*{Nat}

@{datatype nat}
\<^bigskip>

\begin{tabular}{@ {} lllllll @ {}}
@{term "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "(-) :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "(*) :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "(^) :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "(div) :: nat \<Rightarrow> nat \<Rightarrow> nat"}&
@{term "(mod) :: nat \<Rightarrow> nat \<Rightarrow> nat"}&
@{term "(dvd) :: nat \<Rightarrow> nat \<Rightarrow> bool"}\\
@{term "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool"} &
@{term "(<) :: nat \<Rightarrow> nat \<Rightarrow> bool"} &
@{term "min :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "max :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "Min :: nat set \<Rightarrow> nat"} &
@{term "Max :: nat set \<Rightarrow> nat"}\\
\end{tabular}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Nat.of_nat} & @{typeof Nat.of_nat}\\
@{term "(^^) :: ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"} &
  @{term_type_only "(^^) :: ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"}
\end{tabular}

\section*{Int}

Type @{typ int}
\<^bigskip>

\begin{tabular}{@ {} llllllll @ {}}
@{term "(+) :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "(-) :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "uminus :: int \<Rightarrow> int"} &
@{term "(*) :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "(^) :: int \<Rightarrow> nat \<Rightarrow> int"} &
@{term "(div) :: int \<Rightarrow> int \<Rightarrow> int"}&
@{term "(mod) :: int \<Rightarrow> int \<Rightarrow> int"}&
@{term "(dvd) :: int \<Rightarrow> int \<Rightarrow> bool"}\\
@{term "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"} &
@{term "(<) :: int \<Rightarrow> int \<Rightarrow> bool"} &
@{term "min :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "max :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "Min :: int set \<Rightarrow> int"} &
@{term "Max :: int set \<Rightarrow> int"}\\
@{term "abs :: int \<Rightarrow> int"} &
@{term "sgn :: int \<Rightarrow> int"}\\
\end{tabular}

\begin{tabular}{@ {} l @ {~::~} l l @ {}}
@{const Int.nat} & @{typeof Int.nat}\\
@{const Int.of_int} & @{typeof Int.of_int}\\
@{const Int.Ints} & @{term_type_only Int.Ints "'a::ring_1 set"} & (\<^verbatim>\<open>Ints\<close>)
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"of_nat::nat\<Rightarrow>int"} & @{term[source]"of_nat"}\\
\end{tabular}


\section*{Finite\_Set}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Finite_Set.finite} & @{term_type_only Finite_Set.finite "'a set\<Rightarrow>bool"}\\
@{const Finite_Set.card} & @{term_type_only Finite_Set.card "'a set \<Rightarrow> nat"}\\
@{const Finite_Set.fold} & @{term_type_only Finite_Set.fold "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"}\\
\end{supertabular}


\section*{Lattices\_Big}

\begin{supertabular}{@ {} l @ {~::~} l l @ {}}
@{const Lattices_Big.Min} & @{typeof Lattices_Big.Min}\\
@{const Lattices_Big.Max} & @{typeof Lattices_Big.Max}\\
@{const Lattices_Big.arg_min} & @{typeof Lattices_Big.arg_min}\\
@{const Lattices_Big.is_arg_min} & @{typeof Lattices_Big.is_arg_min}\\
@{const Lattices_Big.arg_max} & @{typeof Lattices_Big.arg_max}\\
@{const Lattices_Big.is_arg_max} & @{typeof Lattices_Big.is_arg_max}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term "ARG_MIN f x. P"} & @{term[source]"arg_min f (\<lambda>x. P)"}\\
@{term "ARG_MAX f x. P"} & @{term[source]"arg_max f (\<lambda>x. P)"}\\
\end{supertabular}


\section*{Groups\_Big}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Groups_Big.sum} & @{term_type_only Groups_Big.sum "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b::comm_monoid_add"}\\
@{const Groups_Big.prod} & @{term_type_only Groups_Big.prod "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b::comm_monoid_mult"}\\
\end{supertabular}


\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l l @ {}}
@{term "sum (\<lambda>x. x) A"} & @{term[source]"sum (\<lambda>x. x) A"} & (\<^verbatim>\<open>SUM\<close>)\\
@{term "sum (\<lambda>x. t) A"} & @{term[source]"sum (\<lambda>x. t) A"}\\
@{term[source] "\<Sum>x|P. t"} & @{term"\<Sum>x|P. t"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for \<open>\<Prod>\<close> instead of \<open>\<Sum>\<close>} & (\<^verbatim>\<open>PROD\<close>)\\
\end{supertabular}


\section*{Wellfounded}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Wellfounded.wf} & @{term_type_only Wellfounded.wf "('a*'a)set\<Rightarrow>bool"}\\
@{const Wellfounded.acc} & @{term_type_only Wellfounded.acc "('a*'a)set\<Rightarrow>'a set"}\\
@{const Wellfounded.measure} & @{term_type_only Wellfounded.measure "('a\<Rightarrow>nat)\<Rightarrow>('a*'a)set"}\\
@{const Wellfounded.lex_prod} & @{term_type_only Wellfounded.lex_prod "('a*'a)set\<Rightarrow>('b*'b)set\<Rightarrow>(('a*'b)*('a*'b))set"}\\
@{const Wellfounded.mlex_prod} & @{term_type_only Wellfounded.mlex_prod "('a\<Rightarrow>nat)\<Rightarrow>('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Wellfounded.less_than} & @{term_type_only Wellfounded.less_than "(nat*nat)set"}\\
@{const Wellfounded.pred_nat} & @{term_type_only Wellfounded.pred_nat "(nat*nat)set"}\\
\end{supertabular}


\section*{Set\_Interval} % @{theory HOL.Set_Interval}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const lessThan} & @{term_type_only lessThan "'a::ord \<Rightarrow> 'a set"}\\
@{const atMost} & @{term_type_only atMost "'a::ord \<Rightarrow> 'a set"}\\
@{const greaterThan} & @{term_type_only greaterThan "'a::ord \<Rightarrow> 'a set"}\\
@{const atLeast} & @{term_type_only atLeast "'a::ord \<Rightarrow> 'a set"}\\
@{const greaterThanLessThan} & @{term_type_only greaterThanLessThan "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
@{const atLeastLessThan} & @{term_type_only atLeastLessThan "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
@{const greaterThanAtMost} & @{term_type_only greaterThanAtMost "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
@{const atLeastAtMost} & @{term_type_only atLeastAtMost "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a set"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term "lessThan y"} & @{term[source] "lessThan y"}\\
@{term "atMost y"} & @{term[source] "atMost y"}\\
@{term "greaterThan x"} & @{term[source] "greaterThan x"}\\
@{term "atLeast x"} & @{term[source] "atLeast x"}\\
@{term "greaterThanLessThan x y"} & @{term[source] "greaterThanLessThan x y"}\\
@{term "atLeastLessThan x y"} & @{term[source] "atLeastLessThan x y"}\\
@{term "greaterThanAtMost x y"} & @{term[source] "greaterThanAtMost x y"}\\
@{term "atLeastAtMost x y"} & @{term[source] "atLeastAtMost x y"}\\
@{term[source] "\<Union>i\<le>n. A"} & @{term[source] "\<Union>i \<in> {..n}. A"}\\
@{term[source] "\<Union>i<n. A"} & @{term[source] "\<Union>i \<in> {..<n}. A"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for \<open>\<Inter>\<close> instead of \<open>\<Union>\<close>}\\
@{term "sum (\<lambda>x. t) {a..b}"} & @{term[source] "sum (\<lambda>x. t) {a..b}"}\\
@{term "sum (\<lambda>x. t) {a..<b}"} & @{term[source] "sum (\<lambda>x. t) {a..<b}"}\\
@{term "sum (\<lambda>x. t) {..b}"} & @{term[source] "sum (\<lambda>x. t) {..b}"}\\
@{term "sum (\<lambda>x. t) {..<b}"} & @{term[source] "sum (\<lambda>x. t) {..<b}"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for \<open>\<Prod>\<close> instead of \<open>\<Sum>\<close>}\\
\end{supertabular}


\section*{Power}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Power.power} & @{typeof Power.power}
\end{tabular}


\section*{Option}

@{datatype option}
\<^bigskip>

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Option.the} & @{typeof Option.the}\\
@{const map_option} & @{typ[source]"('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"}\\
@{const set_option} & @{term_type_only set_option "'a option \<Rightarrow> 'a set"}\\
@{const Option.bind} & @{term_type_only Option.bind "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"}
\end{tabular}

\section*{List}

@{datatype list}
\<^bigskip>

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const List.append} & @{typeof List.append}\\
@{const List.butlast} & @{typeof List.butlast}\\
@{const List.concat} & @{typeof List.concat}\\
@{const List.distinct} & @{typeof List.distinct}\\
@{const List.drop} & @{typeof List.drop}\\
@{const List.dropWhile} & @{typeof List.dropWhile}\\
@{const List.filter} & @{typeof List.filter}\\
@{const List.find} & @{typeof List.find}\\
@{const List.fold} & @{typeof List.fold}\\
@{const List.foldr} & @{typeof List.foldr}\\
@{const List.foldl} & @{typeof List.foldl}\\
@{const List.hd} & @{typeof List.hd}\\
@{const List.last} & @{typeof List.last}\\
@{const List.length} & @{typeof List.length}\\
@{const List.lenlex} & @{term_type_only List.lenlex "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lex} & @{term_type_only List.lex "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lexn} & @{term_type_only List.lexn "('a*'a)set\<Rightarrow>nat\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lexord} & @{term_type_only List.lexord "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.listrel} & @{term_type_only List.listrel "('a*'b)set\<Rightarrow>('a list * 'b list)set"}\\
@{const List.listrel1} & @{term_type_only List.listrel1 "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lists} & @{term_type_only List.lists "'a set\<Rightarrow>'a list set"}\\
@{const List.listset} & @{term_type_only List.listset "'a set list \<Rightarrow> 'a list set"}\\
@{const Groups_List.sum_list} & @{typeof Groups_List.sum_list}\\
@{const Groups_List.prod_list} & @{typeof Groups_List.prod_list}\\
@{const List.list_all2} & @{typeof List.list_all2}\\
@{const List.list_update} & @{typeof List.list_update}\\
@{const List.map} & @{typeof List.map}\\
@{const List.measures} & @{term_type_only List.measures "('a\<Rightarrow>nat)list\<Rightarrow>('a*'a)set"}\\
@{const List.nth} & @{typeof List.nth}\\
@{const List.nths} & @{typeof List.nths}\\
@{const List.remdups} & @{typeof List.remdups}\\
@{const List.removeAll} & @{typeof List.removeAll}\\
@{const List.remove1} & @{typeof List.remove1}\\
@{const List.replicate} & @{typeof List.replicate}\\
@{const List.rev} & @{typeof List.rev}\\
@{const List.rotate} & @{typeof List.rotate}\\
@{const List.rotate1} & @{typeof List.rotate1}\\
@{const List.set} & @{term_type_only List.set "'a list \<Rightarrow> 'a set"}\\
@{const List.shuffles} & @{typeof List.shuffles}\\
@{const List.sort} & @{typeof List.sort}\\
@{const List.sorted} & @{typeof List.sorted}\\
@{const List.sorted_wrt} & @{typeof List.sorted_wrt}\\
@{const List.splice} & @{typeof List.splice}\\
@{const List.take} & @{typeof List.take}\\
@{const List.takeWhile} & @{typeof List.takeWhile}\\
@{const List.tl} & @{typeof List.tl}\\
@{const List.upt} & @{typeof List.upt}\\
@{const List.upto} & @{typeof List.upto}\\
@{const List.zip} & @{typeof List.zip}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
\<open>[x\<^sub>1,\<dots>,x\<^sub>n]\<close> & \<open>x\<^sub>1 # \<dots> # x\<^sub>n # []\<close>\\
@{term"[m..<n]"} & @{term[source]"upt m n"}\\
@{term"[i..j]"} & @{term[source]"upto i j"}\\
@{term"xs[n := x]"} & @{term[source]"list_update xs n x"}\\
@{term"\<Sum>x\<leftarrow>xs. e"} & @{term[source]"listsum (map (\<lambda>x. e) xs)"}\\
\end{supertabular}
\<^medskip>

Filter input syntax \<open>[pat \<leftarrow> e. b]\<close>, where
\<open>pat\<close> is a tuple pattern, which stands for @{term "filter (\<lambda>pat. b) e"}.

List comprehension input syntax: \<open>[e. q\<^sub>1, \<dots>, q\<^sub>n]\<close> where each
qualifier \<open>q\<^sub>i\<close> is either a generator \mbox{\<open>pat \<leftarrow> e\<close>} or a
guard, i.e.\ boolean expression.

\section*{Map}

Maps model partial functions and are often used as finite tables. However,
the domain of a map may be infinite.

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Map.empty} & @{typeof Map.empty}\\
@{const Map.map_add} & @{typeof Map.map_add}\\
@{const Map.map_comp} & @{typeof Map.map_comp}\\
@{const Map.restrict_map} & @{term_type_only Map.restrict_map "('a\<Rightarrow>'b option)\<Rightarrow>'a set\<Rightarrow>('a\<Rightarrow>'b option)"}\\
@{const Map.dom} & @{term_type_only Map.dom "('a\<Rightarrow>'b option)\<Rightarrow>'a set"}\\
@{const Map.ran} & @{term_type_only Map.ran "('a\<Rightarrow>'b option)\<Rightarrow>'b set"}\\
@{const Map.map_le} & @{typeof Map.map_le}\\
@{const Map.map_of} & @{typeof Map.map_of}\\
@{const Map.map_upds} & @{typeof Map.map_upds}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"Map.empty"} & @{term"\<lambda>x. None"}\\
@{term"m(x:=Some y)"} & @{term[source]"m(x:=Some y)"}\\
\<open>m(x\<^sub>1\<mapsto>y\<^sub>1,\<dots>,x\<^sub>n\<mapsto>y\<^sub>n)\<close> & @{text[source]"m(x\<^sub>1\<mapsto>y\<^sub>1)\<dots>(x\<^sub>n\<mapsto>y\<^sub>n)"}\\
\<open>[x\<^sub>1\<mapsto>y\<^sub>1,\<dots>,x\<^sub>n\<mapsto>y\<^sub>n]\<close> & @{text[source]"Map.empty(x\<^sub>1\<mapsto>y\<^sub>1,\<dots>,x\<^sub>n\<mapsto>y\<^sub>n)"}\\
@{term"map_upds m xs ys"} & @{term[source]"map_upds m xs ys"}\\
\end{tabular}

\section*{Infix operators in Main} % @{theory Main}

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
