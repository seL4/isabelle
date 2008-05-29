(*<*)theory Base imports Main begin(*>*)

section{*Case Study: Verified Model Checking*}

text{*\label{sec:VMC}
This chapter ends with a case study concerning model checking for 
Computation Tree Logic (CTL), a temporal logic.
Model checking is a popular technique for the verification of finite
state systems (implementations) with respect to temporal logic formulae
(specifications) \cite{ClarkeGP-book,Huth-Ryan-book}. Its foundations are set theoretic
and this section will explore them in HOL\@. This is done in two steps.  First
we consider a simple modal logic called propositional dynamic
logic (PDL)\@.  We then proceed to the temporal logic CTL, which is
used in many real
model checkers. In each case we give both a traditional semantics (@{text \<Turnstile>}) and a
recursive function @{term mc} that maps a formula into the set of all states of
the system where the formula is valid. If the system has a finite number of
states, @{term mc} is directly executable: it is a model checker, albeit an
inefficient one. The main proof obligation is to show that the semantics
and the model checker agree.

\underscoreon

Our models are \emph{transition systems}:\index{transition systems}
sets of \emph{states} with
transitions between them.  Here is a simple example:
\begin{center}
\unitlength.5mm
\thicklines
\begin{picture}(100,60)
\put(50,50){\circle{20}}
\put(50,50){\makebox(0,0){$p,q$}}
\put(61,55){\makebox(0,0)[l]{$s_0$}}
\put(44,42){\vector(-1,-1){26}}
\put(16,18){\vector(1,1){26}}
\put(57,43){\vector(1,-1){26}}
\put(10,10){\circle{20}}
\put(10,10){\makebox(0,0){$q,r$}}
\put(-1,15){\makebox(0,0)[r]{$s_1$}}
\put(20,10){\vector(1,0){60}}
\put(90,10){\circle{20}}
\put(90,10){\makebox(0,0){$r$}}
\put(98, 5){\line(1,0){10}}
\put(108, 5){\line(0,1){10}}
\put(108,15){\vector(-1,0){10}}
\put(91,21){\makebox(0,0)[bl]{$s_2$}}
\end{picture}
\end{center}
Each state has a unique name or number ($s_0,s_1,s_2$), and in each state
certain \emph{atomic propositions} ($p,q,r$) hold.  The aim of temporal logic
is to formalize statements such as ``there is no path starting from $s_2$
leading to a state where $p$ or $q$ holds,'' which is true, and ``on all paths
starting from $s_0$, $q$ always holds,'' which is false.

Abstracting from this concrete example, we assume there is a type of
states:
*}

typedecl state

text{*\noindent
Command \commdx{typedecl} merely declares a new type but without
defining it (see \S\ref{sec:typedecl}). Thus we know nothing
about the type other than its existence. That is exactly what we need
because @{typ state} really is an implicit parameter of our model.  Of
course it would have been more generic to make @{typ state} a type
parameter of everything but declaring @{typ state} globally as above
reduces clutter.  Similarly we declare an arbitrary but fixed
transition system, i.e.\ a relation between states:
*}

consts M :: "(state \<times> state)set";

text{*\noindent
This is Isabelle's way of declaring a constant without defining it.
Finally we introduce a type of atomic propositions
*}

typedecl "atom"

text{*\noindent
and a \emph{labelling function}
*}

consts L :: "state \<Rightarrow> atom set"

text{*\noindent
telling us which atomic propositions are true in each state.
*}

(*<*)end(*>*)
