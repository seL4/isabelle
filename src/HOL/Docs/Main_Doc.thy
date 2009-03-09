(*<*)
theory Main_Doc
imports Main
begin

ML {*
fun pretty_term_type_only ctxt (t, T) =
  (if fastype_of t = Sign.certify_typ (ProofContext.theory_of ctxt) T then ()
   else error "term_type_only: type mismatch";
   Syntax.pretty_typ ctxt T)

val _ = ThyOutput.antiquotation "term_type_only" (Args.term -- Args.typ_abbrev)
  (fn {source, context, ...} => fn arg =>
    ThyOutput.output
      (ThyOutput.maybe_pretty_source (pretty_term_type_only context) source [arg]));
*}
(*>*)
text{*

\begin{abstract}
This document lists the main types, functions and syntax provided by theory @{theory Main}. It is meant as a quick overview of what is available. The sophisicated class structure is only hinted at.
\end{abstract}

\section{HOL}

The basic logic: @{prop "x = y"}, @{const True}, @{const False}, @{prop"Not P"}, @{prop"P & Q"}, @{prop "P | Q"}, @{prop "P --> Q"}, @{prop"ALL x. P"}, @{prop"EX x. P"}, @{prop"EX! x. P"}, @{term"THE x. P"}.

Overloaded operators:

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{text "0"} & @{typeof HOL.zero}\\
@{text "1"} & @{typeof HOL.one}\\
@{const HOL.plus} & @{typeof HOL.plus}\\
@{const HOL.minus} & @{typeof HOL.minus}\\
@{const HOL.uminus} & @{typeof HOL.uminus}\\
@{const HOL.times} & @{typeof HOL.times}\\
@{const HOL.inverse} & @{typeof HOL.inverse}\\
@{const HOL.divide} & @{typeof HOL.divide}\\
@{const HOL.abs} & @{typeof HOL.abs}\\
@{const HOL.sgn} & @{typeof HOL.sgn}\\
@{const HOL.less_eq} & @{typeof HOL.less_eq}\\
@{const HOL.less} & @{typeof HOL.less}\\
@{const HOL.default} & @{typeof HOL.default}\\
@{const HOL.undefined} & @{typeof HOL.undefined}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"~(x = y)"} & @{term[source]"\<not> (x = y)"}\\
@{term[source]"P \<longleftrightarrow> Q"} & @{term"P \<longleftrightarrow> Q"}\\
@{term"If x y z"} & @{term[source]"If x y z"}\\
@{term"Let e\<^isub>1 (%x. e\<^isub>2)"} & @{term[source]"Let e\<^isub>1 (\<lambda>x. e\<^isub>2)"}\\
@{term"abs x"} & @{term[source]"abs x"}\\
@{term"uminus x"} & @{term[source]"uminus x"}\\
\end{supertabular}

\section{Orderings}

A collection of classes constraining @{text"\<le>"} and @{text"<"}:
preorder, partial order, linear order, dense linear order and wellorder.

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Orderings.Least} & @{typeof Orderings.Least}\\
@{const Orderings.min} & @{typeof Orderings.min}\\
@{const Orderings.max} & @{typeof Orderings.max}\\
@{const Orderings.mono} & @{typeof Orderings.mono}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term[source]"x \<ge> y"} & @{term"x \<ge> y"}\\
@{term[source]"x > y"} & @{term"x > y"}\\
@{term"ALL x<=y. P"} & @{term[source]"\<forall>x. x \<le> y \<longrightarrow> P"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for $<$, $\ge$ and $>$, and for @{text"\<exists>"}}\\
@{term"LEAST x. P"} & @{term[source]"Least (\<lambda>x. P)"}\\
\end{supertabular}


\section{Lattices}

Classes semilattice, lattice, distributive lattice and complete lattice (the
latter in theory @{theory Set}).

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Lattices.inf} & @{typeof Lattices.inf}\\
@{const Lattices.sup} & @{typeof Lattices.sup}\\
@{const Set.Inf} & @{term_type_only Set.Inf "'a set \<Rightarrow> 'a::complete_lattice"}\\
@{const Set.Sup} & @{term_type_only Set.Sup "'a set \<Rightarrow> 'a::complete_lattice"}\\
\end{tabular}

\subsubsection*{Syntax}

Only available locally:

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{text[source]"x \<sqsubseteq> y"} & @{term"x \<le> y"}\\
@{text[source]"x \<sqsubset> y"} & @{term"x < y"}\\
@{text[source]"x \<sqinter> y"} & @{term"inf x y"}\\
@{text[source]"x \<squnion> y"} & @{term"sup x y"}\\
@{text[source]"\<Sqinter> A"} & @{term"Sup A"}\\
@{text[source]"\<Squnion> A"} & @{term"Inf A"}\\
\end{supertabular}


\section{Set}

Sets are predicates: @{text[source]"'a set  =  'a \<Rightarrow> bool"}
\bigskip

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Set.empty} & @{term_type_only "Set.empty" "'a set"}\\
@{const insert} & @{term_type_only insert "'a\<Rightarrow>'a set\<Rightarrow>'a set"}\\
@{const Collect} & @{term_type_only Collect "('a\<Rightarrow>bool)\<Rightarrow>'a set"}\\
@{const "op :"} & @{term_type_only "op :" "'a\<Rightarrow>'a set\<Rightarrow>bool"} \qquad(\textsc{ascii} @{text":"})\\
@{const Set.Un} & @{term_type_only Set.Un "'a set\<Rightarrow>'a set \<Rightarrow> 'a set"} \qquad(\textsc{ascii} @{text"Un"})\\
@{const Set.Int} & @{term_type_only Set.Int "'a set\<Rightarrow>'a set \<Rightarrow> 'a set"} \qquad(\textsc{ascii} @{text"Int"})\\
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

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{text"{x\<^isub>1,\<dots>,x\<^isub>n}"} & @{text"insert x\<^isub>1 (\<dots> (insert x\<^isub>n {})\<dots>)"}\\
@{term"x ~: A"} & @{term[source]"\<not>(x \<in> A)"}\\
@{term"A \<subseteq> B"} & @{term[source]"A \<le> B"}\\
@{term"A \<subset> B"} & @{term[source]"A < B"}\\
@{term[source]"A \<supseteq> B"} & @{term[source]"B \<le> A"}\\
@{term[source]"A \<supset> B"} & @{term[source]"B < A"}\\
@{term"{x. P}"} & @{term[source]"Collect(\<lambda>x. P)"}\\
@{term[mode=xsymbols]"UN x:I. A"} & @{term[source]"UNION I (\<lambda>x. A)"}\\
@{term[mode=xsymbols]"UN x. A"} & @{term[source]"UNION UNIV (\<lambda>x. A)"}\\
@{term[mode=xsymbols]"INT x:I. A"} & @{term[source]"INTER I (\<lambda>x. A)"}\\
@{term[mode=xsymbols]"INT x. A"} & @{term[source]"INTER UNIV (\<lambda>x. A)"}\\
@{term"ALL x:A. P"} & @{term[source]"Ball A (\<lambda>x. P)"}\\
@{term"EX x:A. P"} & @{term[source]"Bex A (\<lambda>x. P)"}\\
@{term"range f"} & @{term[source]"f ` UNIV"}\\
\end{supertabular}


\section{Fun}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const "Fun.id"} & @{typeof Fun.id}\\
@{const "Fun.comp"} & @{typeof Fun.comp}\\
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
@{text"f(x\<^isub>1:=y\<^isub>1,\<dots>,x\<^isub>n:=y\<^isub>n)"} & @{text"f(x\<^isub>1:=y\<^isub>1)\<dots>(x\<^isub>n:=y\<^isub>n)"}\\
\end{tabular}


\section{Fixed Points}

Theory: @{theory Inductive}.

Least and greatest fixed points in a complete lattice @{typ 'a}:

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Inductive.lfp} & @{typeof Inductive.lfp}\\
@{const Inductive.gfp} & @{typeof Inductive.gfp}\\
\end{tabular}

Note that in particular sets (@{typ"'a \<Rightarrow> bool"}) are complete lattices.

\section{Sum\_Type}

Type constructor @{text"+"}.

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Sum_Type.Inl} & @{typeof Sum_Type.Inl}\\
@{const Sum_Type.Inr} & @{typeof Sum_Type.Inr}\\
@{const Sum_Type.Plus} & @{term_type_only Sum_Type.Plus "'a set\<Rightarrow>'b set\<Rightarrow>('a+'b)set"}
\end{tabular}


\section{Product\_Type}

Types @{typ unit} and @{text"\<times>"}.

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Product_Type.Unity} & @{typeof Product_Type.Unity}\\
@{const Pair} & @{typeof Pair}\\
@{const fst} & @{typeof fst}\\
@{const snd} & @{typeof snd}\\
@{const split} & @{typeof split}\\
@{const curry} & @{typeof curry}\\
@{const Product_Type.Times} & @{typeof Product_Type.Times}\\
@{const Product_Type.Sigma} & @{term_type_only Product_Type.Sigma "'a set\<Rightarrow>('a\<Rightarrow>'b set)\<Rightarrow>('a*'b)set"}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"Pair a b"} & @{term[source]"Pair a b"}\\
@{term"split (\<lambda>x y. t)"} & @{term[source]"split (\<lambda>x y. t)"}\\
\end{tabular}

Pairs may be nested. Nesting to the right is printed as a tuple,
e.g.\ \mbox{@{term"(a,b,c)"}} is really @{text"(a,(b,c))"}.
Pattern matching with pairs and tuples extends to all binders,
e.g.\ @{prop"ALL (x,y):A. P"}, @{term"{(x,y). P}"}, etc.


\section{Relation}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Relation.converse} & @{term_type_only Relation.converse "('a * 'b)set \<Rightarrow> ('b*'a)set"}\\
@{const Relation.rel_comp} & @{term_type_only Relation.rel_comp "('a*'b)set\<Rightarrow>('c*'a)set\<Rightarrow>('c*'b)set"}\\
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
@{const Relation.total} & @{term_type_only Relation.total "('a*'a)set\<Rightarrow>bool"}
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"converse r"} & @{term[source]"converse r"}
\end{tabular}

\section{Equiv\_Relations}

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


\section{Transitive\_Closure}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Transitive_Closure.rtrancl} & @{term_type_only Transitive_Closure.rtrancl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Transitive_Closure.trancl} & @{term_type_only Transitive_Closure.trancl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Transitive_Closure.reflcl} & @{term_type_only Transitive_Closure.reflcl "('a*'a)set\<Rightarrow>('a*'a)set"}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"rtrancl r"} & @{term[source]"rtrancl r"}\\
@{term"trancl r"} & @{term[source]"trancl r"}\\
@{term"reflcl r"} & @{term[source]"reflcl r"}
\end{tabular}


\section{Algebra}

Theories @{theory OrderedGroup} and @{theory Ring_and_Field} define a large
collection of classes describing common algebraic structures from semigroups
up to fields. Everything is done in terms of @{const plus}, @{const times}
and other overloaded operators.


\section{Nat}

@{datatype nat}
\bigskip

\begin{tabular}{@ {} lllllll @ {}}
@{term "op + :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "op - :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "op * :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "op ^ :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "op div :: nat \<Rightarrow> nat \<Rightarrow> nat"}&
@{term "op mod :: nat \<Rightarrow> nat \<Rightarrow> nat"}&
@{term "op dvd :: nat \<Rightarrow> nat \<Rightarrow> bool"}\\
@{term "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"} &
@{term "op < :: nat \<Rightarrow> nat \<Rightarrow> bool"} &
@{term "min :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "max :: nat \<Rightarrow> nat \<Rightarrow> nat"} &
@{term "Min :: nat set \<Rightarrow> nat"} &
@{term "Max :: nat set \<Rightarrow> nat"}\\
\end{tabular}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Nat.of_nat} & @{typeof Nat.of_nat}
\end{tabular}

\section{Int}

Type @{typ int}
\bigskip

\begin{tabular}{@ {} llllllll @ {}}
@{term "op + :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "op - :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "uminus :: int \<Rightarrow> int"} &
@{term "op * :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "op ^ :: int \<Rightarrow> nat \<Rightarrow> int"} &
@{term "op div :: int \<Rightarrow> int \<Rightarrow> int"}&
@{term "op mod :: int \<Rightarrow> int \<Rightarrow> int"}&
@{term "op dvd :: int \<Rightarrow> int \<Rightarrow> bool"}\\
@{term "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"} &
@{term "op < :: int \<Rightarrow> int \<Rightarrow> bool"} &
@{term "min :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "max :: int \<Rightarrow> int \<Rightarrow> int"} &
@{term "Min :: int set \<Rightarrow> int"} &
@{term "Max :: int set \<Rightarrow> int"}\\
@{term "abs :: int \<Rightarrow> int"} &
@{term "sgn :: int \<Rightarrow> int"}\\
\end{tabular}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Int.nat} & @{typeof Int.nat}\\
@{const Int.of_int} & @{typeof Int.of_int}\\
@{const Int.Ints} & @{term_type_only Int.Ints "'a::ring_1 set"}\\
\end{tabular}

\subsubsection*{Syntax}

\begin{tabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"of_nat::nat\<Rightarrow>int"} & @{term[source]"of_nat"}\\
\end{tabular}


\section{Finite\_Set}


\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Finite_Set.finite} & @{term_type_only Finite_Set.finite "'a set\<Rightarrow>bool"}\\
@{const Finite_Set.card} & @{term_type_only Finite_Set.card "'a set => nat"}\\
@{const Finite_Set.fold} & @{term_type_only Finite_Set.fold "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"}\\
@{const Finite_Set.fold_image} & @{typ "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"}\\
@{const Finite_Set.setsum} & @{term_type_only Finite_Set.setsum "('a => 'b) => 'a set => 'b::comm_monoid_add"}\\
@{const Finite_Set.setprod} & @{term_type_only Finite_Set.setprod "('a => 'b) => 'a set => 'b::comm_monoid_mult"}\\
\end{supertabular}


\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{term"setsum (%x. x) A"} & @{term[source]"setsum (\<lambda>x. x) A"}\\
@{term"setsum (%x. t) A"} & @{term[source]"setsum (\<lambda>x. t) A"}\\
@{term[source]"\<Sum>x|P. t"} & @{term"\<Sum>x|P. t"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for @{text"\<Prod>"} instead of @{text"\<Sum>"}}\\
\end{supertabular}


\section{Wellfounded}

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const Wellfounded.wf} & @{term_type_only Wellfounded.wf "('a*'a)set\<Rightarrow>bool"}\\
@{const Wellfounded.acyclic} & @{term_type_only Wellfounded.acyclic "('a*'a)set\<Rightarrow>bool"}\\
@{const Wellfounded.acc} & @{term_type_only Wellfounded.acc "('a*'a)set\<Rightarrow>'a set"}\\
@{const Wellfounded.measure} & @{term_type_only Wellfounded.measure "('a\<Rightarrow>nat)\<Rightarrow>('a*'a)set"}\\
@{const Wellfounded.lex_prod} & @{term_type_only Wellfounded.lex_prod "('a*'a)set\<Rightarrow>('b*'b)set\<Rightarrow>(('a*'b)*('a*'b))set"}\\
@{const Wellfounded.mlex_prod} & @{term_type_only Wellfounded.mlex_prod "('a\<Rightarrow>nat)\<Rightarrow>('a*'a)set\<Rightarrow>('a*'a)set"}\\
@{const Wellfounded.less_than} & @{term_type_only Wellfounded.less_than "(nat*nat)set"}\\
@{const Wellfounded.pred_nat} & @{term_type_only Wellfounded.pred_nat "(nat*nat)set"}\\
\end{supertabular}


\section{SetInterval}

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
@{term[mode=xsymbols] "UN i:{..n}. A"} & @{term[source] "\<Union> i \<in> {..n}. A"}\\
@{term[mode=xsymbols] "UN i:{..<n}. A"} & @{term[source] "\<Union> i \<in> {..<n}. A"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for @{text"\<Inter>"} instead of @{text"\<Union>"}}\\
@{term "setsum (%x. t) {a..b}"} & @{term[source] "setsum (\<lambda>x. t) {a..b}"}\\
@{term "setsum (%x. t) {a..<b}"} & @{term[source] "setsum (\<lambda>x. t) {a..<b}"}\\
@{term "setsum (%x. t) {..b}"} & @{term[source] "setsum (\<lambda>x. t) {..b}"}\\
@{term "setsum (%x. t) {..<b}"} & @{term[source] "setsum (\<lambda>x. t) {..<b}"}\\
\multicolumn{2}{@ {}l@ {}}{Similarly for @{text"\<Prod>"} instead of @{text"\<Sum>"}}\\
\end{supertabular}


\section{Power}

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Power.power} & @{typeof Power.power}
\end{tabular}


\section{Iterated Functions and Relations}

Theory: @{theory Relation_Power}

Iterated functions \ @{term[source]"(f::'a\<Rightarrow>'a) ^ n"} \
and relations \ @{term[source]"(r::('a\<times>'a)set) ^ n"}.


\section{Option}

@{datatype option}
\bigskip

\begin{tabular}{@ {} l @ {~::~} l @ {}}
@{const Option.the} & @{typeof Option.the}\\
@{const Option.map} & @{typ[source]"('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"}\\
@{const Option.set} & @{term_type_only Option.set "'a option \<Rightarrow> 'a set"}
\end{tabular}

\section{List}

@{datatype list}
\bigskip

\begin{supertabular}{@ {} l @ {~::~} l @ {}}
@{const List.append} & @{typeof List.append}\\
@{const List.butlast} & @{typeof List.butlast}\\
@{const List.concat} & @{typeof List.concat}\\
@{const List.distinct} & @{typeof List.distinct}\\
@{const List.drop} & @{typeof List.drop}\\
@{const List.dropWhile} & @{typeof List.dropWhile}\\
@{const List.filter} & @{typeof List.filter}\\
@{const List.foldl} & @{typeof List.foldl}\\
@{const List.foldr} & @{typeof List.foldr}\\
@{const List.hd} & @{typeof List.hd}\\
@{const List.last} & @{typeof List.last}\\
@{const List.length} & @{typeof List.length}\\
@{const List.lenlex} & @{term_type_only List.lenlex "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lex} & @{term_type_only List.lex "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lexn} & @{term_type_only List.lexn "('a*'a)set\<Rightarrow>nat\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lexord} & @{term_type_only List.lexord "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.listrel} & @{term_type_only List.listrel "('a*'a)set\<Rightarrow>('a list * 'a list)set"}\\
@{const List.lists} & @{term_type_only List.lists "'a set\<Rightarrow>'a list set"}\\
@{const List.listset} & @{term_type_only List.listset "'a set list \<Rightarrow> 'a list set"}\\
@{const List.listsum} & @{typeof List.listsum}\\
@{const List.list_all2} & @{typeof List.list_all2}\\
@{const List.list_update} & @{typeof List.list_update}\\
@{const List.map} & @{typeof List.map}\\
@{const List.measures} & @{term_type_only List.measures "('a\<Rightarrow>nat)list\<Rightarrow>('a*'a)set"}\\
@{const List.remdups} & @{typeof List.remdups}\\
@{const List.removeAll} & @{typeof List.removeAll}\\
@{const List.remove1} & @{typeof List.remove1}\\
@{const List.replicate} & @{typeof List.replicate}\\
@{const List.rev} & @{typeof List.rev}\\
@{const List.rotate} & @{typeof List.rotate}\\
@{const List.rotate1} & @{typeof List.rotate1}\\
@{const List.set} & @{term_type_only List.set "'a list \<Rightarrow> 'a set"}\\
@{const List.sort} & @{typeof List.sort}\\
@{const List.sorted} & @{typeof List.sorted}\\
@{const List.splice} & @{typeof List.splice}\\
@{const List.sublist} & @{typeof List.sublist}\\
@{const List.take} & @{typeof List.take}\\
@{const List.takeWhile} & @{typeof List.takeWhile}\\
@{const List.tl} & @{typeof List.tl}\\
@{const List.upt} & @{typeof List.upt}\\
@{const List.upto} & @{typeof List.upto}\\
@{const List.zip} & @{typeof List.zip}\\
\end{supertabular}

\subsubsection*{Syntax}

\begin{supertabular}{@ {} l @ {\quad$\equiv$\quad} l @ {}}
@{text"[x\<^isub>1,\<dots>,x\<^isub>n]"} & @{text"x\<^isub>1 # \<dots> # x\<^isub>n # []"}\\
@{term"[m..<n]"} & @{term[source]"upt m n"}\\
@{term"[i..j]"} & @{term[source]"upto i j"}\\
@{text"[e. x \<leftarrow> xs]"} & @{term"map (%x. e) xs"}\\
@{term"[x \<leftarrow> xs. b]"} & @{term[source]"filter (\<lambda>x. b) xs"} \\
@{term"xs[n := x]"} & @{term[source]"list_update xs n x"}\\
@{term"\<Sum>x\<leftarrow>xs. e"} & @{term[source]"listsum (map (\<lambda>x. e) xs)"}\\
\end{supertabular}
\medskip

Comprehension: @{text"[e. q\<^isub>1, \<dots>, q\<^isub>n]"} where each
qualifier @{text q\<^isub>i} is either a generator @{text"pat \<leftarrow> e"} or a
guard, i.e.\ boolean expression.

\section{Map}

Maps model partial functions and are often used as finite tables. However,
the domain of a map may be infinite.

@{text"'a \<rightharpoonup> 'b  =  'a \<Rightarrow> 'b option"}
\bigskip

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
@{text"m(x\<^isub>1\<mapsto>y\<^isub>1,\<dots>,x\<^isub>n\<mapsto>y\<^isub>n)"} & @{text[source]"m(x\<^isub>1\<mapsto>y\<^isub>1)\<dots>(x\<^isub>n\<mapsto>y\<^isub>n)"}\\
@{term"map_upds m xs ys"} & @{term[source]"map_upds m xs ys"}\\
\end{tabular}

*}
(*<*)
end
(*>*)