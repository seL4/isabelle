(*<*)theory Base = Main:(*>*)

section{*A verified model checker*}

text{*
Model checking is a very popular technique for the verification of finite
state systems (implementations) w.r.t.\ temporal logic formulae
(specifications) \cite{Clark}. Its foundations are completely set theoretic
and this section shall develop them in HOL. This is done in two steps: first
we consider a very simple ``temporal'' logic called propositional dynamic
logic (PDL) which we then extend to the temporal logic CTL used in many real
model checkers. In each case we give both a traditional semantics (@{text \<Turnstile>}) and a
recursive function @{term mc} that maps a formula into the set of all states of
the system where the formula is valid. If the system has a finite number of
states, @{term mc} is directly executable, i.e.\ a model checker, albeit not a
very efficient one. The main proof obligation is to show that the semantics
and the model checker agree.

Our models are transition systems.

START with simple example: mutex or something.

Abstracting from this concrete example, we assume there is some type of
atomic propositions
*}

typedecl atom

text{*\noindent
which we merely declare rather than define because it is an implicit parameter of our model.
Of course it would have been more generic to make @{typ atom} a type parameter of everything
but fixing @{typ atom} as above reduces clutter.

Instead of introducing both a separate type of states and a function
telling us which atoms are true in each state we simply identify each
state with that set of atoms:
*}

types state = "atom set";

text{*\noindent
Finally we declare an arbitrary but fixed transition system, i.e.\ relation between states:
*}

consts M :: "(state \<times> state)set";

text{*\noindent
Again, we could have made @{term M} a parameter of everything.
*}
(*<*)end(*>*)
