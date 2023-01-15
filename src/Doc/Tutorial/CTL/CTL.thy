(*<*)theory CTL imports Base begin(*>*)

subsection\<open>Computation Tree Logic --- CTL\<close>

text\<open>\label{sec:CTL}
\index{CTL|(}%
The semantics of PDL only needs reflexive transitive closure.
Let us be adventurous and introduce a more expressive temporal operator.
We extend the datatype
\<open>formula\<close> by a new constructor
\<close>
(*<*)
datatype formula = Atom "atom"
                  | Neg formula
                  | And formula formula
                  | AX formula
                  | EF formula(*>*)
                  | AF formula

text\<open>\noindent
which stands for ``\emph{A}lways in the \emph{F}uture'':
on all infinite paths, at some point the formula holds.
Formalizing the notion of an infinite path is easy
in HOL: it is simply a function from \<^typ>\<open>nat\<close> to \<^typ>\<open>state\<close>.
\<close>

definition Paths :: "state \<Rightarrow> (nat \<Rightarrow> state)set" where
"Paths s \<equiv> {p. s = p 0 \<and> (\<forall>i. (p i, p(i+1)) \<in> M)}"

text\<open>\noindent
This definition allows a succinct statement of the semantics of \<^const>\<open>AF\<close>:
\footnote{Do not be misled: neither datatypes nor recursive functions can be
extended by new constructors or equations. This is just a trick of the
presentation (see \S\ref{sec:doc-prep-suppress}). In reality one has to define
a new datatype and a new function.}
\<close>
(*<*)
primrec valid :: "state \<Rightarrow> formula \<Rightarrow> bool" ("(_ \<Turnstile> _)" [80,80] 80) where
"s \<Turnstile> Atom a  =  (a \<in> L s)" |
"s \<Turnstile> Neg f   = (~(s \<Turnstile> f))" |
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)" |
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)" |
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<Turnstile> f)" |
(*>*)
"s \<Turnstile> AF f    = (\<forall>p \<in> Paths s. \<exists>i. p i \<Turnstile> f)"

text\<open>\noindent
Model checking \<^const>\<open>AF\<close> involves a function which
is just complicated enough to warrant a separate definition:
\<close>

definition af :: "state set \<Rightarrow> state set \<Rightarrow> state set" where
"af A T \<equiv> A \<union> {s. \<forall>t. (s, t) \<in> M \<longrightarrow> t \<in> T}"

text\<open>\noindent
Now we define \<^term>\<open>mc(AF f)\<close> as the least set \<^term>\<open>T\<close> that includes
\<^term>\<open>mc f\<close> and all states all of whose direct successors are in \<^term>\<open>T\<close>:
\<close>
(*<*)
primrec mc :: "formula \<Rightarrow> state set" where
"mc(Atom a)  = {s. a \<in> L s}" |
"mc(Neg f)   = -mc f" |
"mc(And f g) = mc f \<inter> mc g" |
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}" |
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> M\<inverse> `` T)"|(*>*)
"mc(AF f)    = lfp(af(mc f))"

text\<open>\noindent
Because \<^const>\<open>af\<close> is monotone in its second argument (and also its first, but
that is irrelevant), \<^term>\<open>af A\<close> has a least fixed point:
\<close>

lemma mono_af: "mono(af A)"
apply(simp add: mono_def af_def)
apply blast
done
(*<*)
lemma mono_ef: "mono(\<lambda>T. A \<union> M\<inverse> `` T)"
apply(rule monoI)
by(blast)

lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> M\<inverse> `` T) = {s. \<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<in> A}"
apply(rule equalityI)
 apply(rule subsetI)
 apply(simp)
 apply(erule lfp_induct_set)
  apply(rule mono_ef)
 apply(simp)
 apply(blast intro: rtrancl_trans)
apply(rule subsetI)
apply(simp, clarify)
apply(erule converse_rtrancl_induct)
 apply(subst lfp_unfold[OF mono_ef])
 apply(blast)
apply(subst lfp_unfold[OF mono_ef])
by(blast)
(*>*)
text\<open>
All we need to prove now is  \<^prop>\<open>mc(AF f) = {s. s \<Turnstile> AF f}\<close>, which states
that \<^term>\<open>mc\<close> and \<open>\<Turnstile>\<close> agree for \<^const>\<open>AF\<close>\@.
This time we prove the two inclusions separately, starting
with the easy one:
\<close>

theorem AF_lemma1: "lfp(af A) \<subseteq> {s. \<forall>p \<in> Paths s. \<exists>i. p i \<in> A}"

txt\<open>\noindent
In contrast to the analogous proof for \<^const>\<open>EF\<close>, and just
for a change, we do not use fixed point induction.  Park-induction,
named after David Park, is weaker but sufficient for this proof:
\begin{center}
@{thm lfp_lowerbound[of _ "S",no_vars]} \hfill (@{thm[source]lfp_lowerbound})
\end{center}
The instance of the premise \<^prop>\<open>f S \<subseteq> S\<close> is proved pointwise,
a decision that \isa{auto} takes for us:
\<close>
apply(rule lfp_lowerbound)
apply(auto simp add: af_def Paths_def)

txt\<open>
@{subgoals[display,indent=0,margin=70,goals_limit=1]}
In this remaining case, we set \<^term>\<open>t\<close> to \<^term>\<open>p(1::nat)\<close>.
The rest is automatic, which is surprising because it involves
finding the instantiation \<^term>\<open>\<lambda>i::nat. p(i+1)\<close>
for \<open>\<forall>p\<close>.
\<close>

apply(erule_tac x = "p 1" in allE)
apply(auto)
done


text\<open>
The opposite inclusion is proved by contradiction: if some state
\<^term>\<open>s\<close> is not in \<^term>\<open>lfp(af A)\<close>, then we can construct an
infinite \<^term>\<open>A\<close>-avoiding path starting from~\<^term>\<open>s\<close>. The reason is
that by unfolding \<^const>\<open>lfp\<close> we find that if \<^term>\<open>s\<close> is not in
\<^term>\<open>lfp(af A)\<close>, then \<^term>\<open>s\<close> is not in \<^term>\<open>A\<close> and there is a
direct successor of \<^term>\<open>s\<close> that is again not in \mbox{\<^term>\<open>lfp(af
A)\<close>}. Iterating this argument yields the promised infinite
\<^term>\<open>A\<close>-avoiding path. Let us formalize this sketch.

The one-step argument in the sketch above
is proved by a variant of contraposition:
\<close>

lemma not_in_lfp_afD:
 "s \<notin> lfp(af A) \<Longrightarrow> s \<notin> A \<and> (\<exists> t. (s,t) \<in> M \<and> t \<notin> lfp(af A))"
apply(erule contrapos_np)
apply(subst lfp_unfold[OF mono_af])
apply(simp add: af_def)
done

text\<open>\noindent
We assume the negation of the conclusion and prove \<^term>\<open>s \<in> lfp(af A)\<close>.
Unfolding \<^const>\<open>lfp\<close> once and
simplifying with the definition of \<^const>\<open>af\<close> finishes the proof.

Now we iterate this process. The following construction of the desired
path is parameterized by a predicate \<^term>\<open>Q\<close> that should hold along the path:
\<close>

primrec path :: "state \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> state)" where
"path s Q 0 = s" |
"path s Q (Suc n) = (SOME t. (path s Q n,t) \<in> M \<and> Q t)"

text\<open>\noindent
Element \<^term>\<open>n+1::nat\<close> on this path is some arbitrary successor
\<^term>\<open>t\<close> of element \<^term>\<open>n\<close> such that \<^term>\<open>Q t\<close> holds.  Remember that \<open>SOME t. R t\<close>
is some arbitrary but fixed \<^term>\<open>t\<close> such that \<^prop>\<open>R t\<close> holds (see \S\ref{sec:SOME}). Of
course, such a \<^term>\<open>t\<close> need not exist, but that is of no
concern to us since we will only use \<^const>\<open>path\<close> when a
suitable \<^term>\<open>t\<close> does exist.

Let us show that if each state \<^term>\<open>s\<close> that satisfies \<^term>\<open>Q\<close>
has a successor that again satisfies \<^term>\<open>Q\<close>, then there exists an infinite \<^term>\<open>Q\<close>-path:
\<close>

lemma infinity_lemma:
  "\<lbrakk> Q s; \<forall>s. Q s \<longrightarrow> (\<exists> t. (s,t) \<in> M \<and> Q t) \<rbrakk> \<Longrightarrow>
   \<exists>p\<in>Paths s. \<forall>i. Q(p i)"

txt\<open>\noindent
First we rephrase the conclusion slightly because we need to prove simultaneously
both the path property and the fact that \<^term>\<open>Q\<close> holds:
\<close>

apply(subgoal_tac
  "\<exists>p. s = p 0 \<and> (\<forall>i::nat. (p i, p(i+1)) \<in> M \<and> Q(p i))")

txt\<open>\noindent
From this proposition the original goal follows easily:
\<close>

 apply(simp add: Paths_def, blast)

txt\<open>\noindent
The new subgoal is proved by providing the witness \<^term>\<open>path s Q\<close> for \<^term>\<open>p\<close>:
\<close>

apply(rule_tac x = "path s Q" in exI)
apply(clarsimp)

txt\<open>\noindent
After simplification and clarification, the subgoal has the following form:
@{subgoals[display,indent=0,margin=70,goals_limit=1]}
It invites a proof by induction on \<^term>\<open>i\<close>:
\<close>

apply(induct_tac i)
 apply(simp)

txt\<open>\noindent
After simplification, the base case boils down to
@{subgoals[display,indent=0,margin=70,goals_limit=1]}
The conclusion looks exceedingly trivial: after all, \<^term>\<open>t\<close> is chosen such that \<^prop>\<open>(s,t)\<in>M\<close>
holds. However, we first have to show that such a \<^term>\<open>t\<close> actually exists! This reasoning
is embodied in the theorem @{thm[source]someI2_ex}:
@{thm[display,eta_contract=false]someI2_ex}
When we apply this theorem as an introduction rule, \<open>?P x\<close> becomes
\<^prop>\<open>(s, x) \<in> M \<and> Q x\<close> and \<open>?Q x\<close> becomes \<^prop>\<open>(s,x) \<in> M\<close> and we have to prove
two subgoals: \<^prop>\<open>\<exists>a. (s, a) \<in> M \<and> Q a\<close>, which follows from the assumptions, and
\<^prop>\<open>(s, x) \<in> M \<and> Q x \<Longrightarrow> (s,x) \<in> M\<close>, which is trivial. Thus it is not surprising that
\<open>fast\<close> can prove the base case quickly:
\<close>

 apply(fast intro: someI2_ex)

txt\<open>\noindent
What is worth noting here is that we have used \methdx{fast} rather than
\<open>blast\<close>.  The reason is that \<open>blast\<close> would fail because it cannot
cope with @{thm[source]someI2_ex}: unifying its conclusion with the current
subgoal is non-trivial because of the nested schematic variables. For
efficiency reasons \<open>blast\<close> does not even attempt such unifications.
Although \<open>fast\<close> can in principle cope with complicated unification
problems, in practice the number of unifiers arising is often prohibitive and
the offending rule may need to be applied explicitly rather than
automatically. This is what happens in the step case.

The induction step is similar, but more involved, because now we face nested
occurrences of \<open>SOME\<close>. As a result, \<open>fast\<close> is no longer able to
solve the subgoal and we apply @{thm[source]someI2_ex} by hand.  We merely
show the proof commands but do not describe the details:
\<close>

apply(simp)
apply(rule someI2_ex)
 apply(blast)
apply(rule someI2_ex)
 apply(blast)
apply(blast)
done

text\<open>
Function \<^const>\<open>path\<close> has fulfilled its purpose now and can be forgotten.
It was merely defined to provide the witness in the proof of the
@{thm[source]infinity_lemma}. Aficionados of minimal proofs might like to know
that we could have given the witness without having to define a new function:
the term
@{term[display]"rec_nat s (\<lambda>n t. SOME u. (t,u)\<in>M \<and> Q u)"}
is extensionally equal to \<^term>\<open>path s Q\<close>,
where \<^term>\<open>rec_nat\<close> is the predefined primitive recursor on \<^typ>\<open>nat\<close>.
\<close>
(*<*)
lemma
"\<lbrakk> Q s; \<forall> s. Q s \<longrightarrow> (\<exists> t. (s,t)\<in>M \<and> Q t) \<rbrakk> \<Longrightarrow>
 \<exists> p\<in>Paths s. \<forall> i. Q(p i)"
apply(subgoal_tac
 "\<exists> p. s = p 0 \<and> (\<forall> i. (p i,p(Suc i))\<in>M \<and> Q(p i))")
 apply(simp add: Paths_def)
 apply(blast)
apply(rule_tac x = "rec_nat s (\<lambda>n t. SOME u. (t,u)\<in>M \<and> Q u)" in exI)
apply(simp)
apply(intro strip)
apply(induct_tac i)
 apply(simp)
 apply(fast intro: someI2_ex)
apply(simp)
apply(rule someI2_ex)
 apply(blast)
apply(rule someI2_ex)
 apply(blast)
by(blast)
(*>*)

text\<open>
At last we can prove the opposite direction of @{thm[source]AF_lemma1}:
\<close>

theorem AF_lemma2: "{s. \<forall>p \<in> Paths s. \<exists>i. p i \<in> A} \<subseteq> lfp(af A)"

txt\<open>\noindent
The proof is again pointwise and then by contraposition:
\<close>

apply(rule subsetI)
apply(erule contrapos_pp)
apply simp

txt\<open>
@{subgoals[display,indent=0,goals_limit=1]}
Applying the @{thm[source]infinity_lemma} as a destruction rule leaves two subgoals, the second
premise of @{thm[source]infinity_lemma} and the original subgoal:
\<close>

apply(drule infinity_lemma)

txt\<open>
@{subgoals[display,indent=0,margin=65]}
Both are solved automatically:
\<close>

 apply(auto dest: not_in_lfp_afD)
done

text\<open>
If you find these proofs too complicated, we recommend that you read
\S\ref{sec:CTL-revisited}, where we show how inductive definitions lead to
simpler arguments.

The main theorem is proved as for PDL, except that we also derive the
necessary equality \<open>lfp(af A) = ...\<close> by combining
@{thm[source]AF_lemma1} and @{thm[source]AF_lemma2} on the spot:
\<close>

theorem "mc f = {s. s \<Turnstile> f}"
apply(induct_tac f)
apply(auto simp add: EF_lemma equalityI[OF AF_lemma1 AF_lemma2])
done

text\<open>

The language defined above is not quite CTL\@. The latter also includes an
until-operator \<^term>\<open>EU f g\<close> with semantics ``there \emph{E}xists a path
where \<^term>\<open>f\<close> is true \emph{U}ntil \<^term>\<open>g\<close> becomes true''.  We need
an auxiliary function:
\<close>

primrec
until:: "state set \<Rightarrow> state set \<Rightarrow> state \<Rightarrow> state list \<Rightarrow> bool" where
"until A B s []    = (s \<in> B)" |
"until A B s (t#p) = (s \<in> A \<and> (s,t) \<in> M \<and> until A B t p)"
(*<*)definition
 eusem :: "state set \<Rightarrow> state set \<Rightarrow> state set" where
"eusem A B \<equiv> {s. \<exists>p. until A B s p}"(*>*)

text\<open>\noindent
Expressing the semantics of \<^term>\<open>EU\<close> is now straightforward:
@{prop[display]"s \<Turnstile> EU f g = (\<exists>p. until {t. t \<Turnstile> f} {t. t \<Turnstile> g} s p)"}
Note that \<^term>\<open>EU\<close> is not definable in terms of the other operators!

Model checking \<^term>\<open>EU\<close> is again a least fixed point construction:
@{text[display]"mc(EU f g) = lfp(\<lambda>T. mc g \<union> mc f \<inter> (M\<inverse> `` T))"}

\begin{exercise}
Extend the datatype of formulae by the above until operator
and prove the equivalence between semantics and model checking, i.e.\ that
@{prop[display]"mc(EU f g) = {s. s \<Turnstile> EU f g}"}
%For readability you may want to annotate {term EU} with its customary syntax
%{text[display]"| EU formula formula    E[_ U _]"}
%which enables you to read and write {text"E[f U g]"} instead of {term"EU f g"}.
\end{exercise}
For more CTL exercises see, for example, Huth and Ryan \<^cite>\<open>"Huth-Ryan-book"\<close>.
\<close>

(*<*)
definition eufix :: "state set \<Rightarrow> state set \<Rightarrow> state set \<Rightarrow> state set" where
"eufix A B T \<equiv> B \<union> A \<inter> (M\<inverse> `` T)"

lemma "lfp(eufix A B) \<subseteq> eusem A B"
apply(rule lfp_lowerbound)
apply(auto simp add: eusem_def eufix_def)
 apply(rule_tac x = "[]" in exI)
 apply simp
apply(rule_tac x = "xa#xb" in exI)
apply simp
done

lemma mono_eufix: "mono(eufix A B)"
apply(simp add: mono_def eufix_def)
apply blast
done

lemma "eusem A B \<subseteq> lfp(eufix A B)"
apply(clarsimp simp add: eusem_def)
apply(erule rev_mp)
apply(rule_tac x = x in spec)
apply(induct_tac p)
 apply(subst lfp_unfold[OF mono_eufix])
 apply(simp add: eufix_def)
apply(clarsimp)
apply(subst lfp_unfold[OF mono_eufix])
apply(simp add: eufix_def)
apply blast
done

(*
definition eusem :: "state set \<Rightarrow> state set \<Rightarrow> state set" where
"eusem A B \<equiv> {s. \<exists>p\<in>Paths s. \<exists>j. p j \<in> B \<and> (\<forall>i < j. p i \<in> A)}"

axiomatization where
M_total: "\<exists>t. (s,t) \<in> M"

consts apath :: "state \<Rightarrow> (nat \<Rightarrow> state)"
primrec
"apath s 0 = s"
"apath s (Suc i) = (SOME t. (apath s i,t) \<in> M)"

lemma [iff]: "apath s \<in> Paths s";
apply(simp add: Paths_def);
apply(blast intro: M_total[THEN someI_ex])
done

definition pcons :: "state \<Rightarrow> (nat \<Rightarrow> state) \<Rightarrow> (nat \<Rightarrow> state)" where
"pcons s p == \<lambda>i. case i of 0 \<Rightarrow> s | Suc j \<Rightarrow> p j"

lemma pcons_PathI: "[| (s,t) : M; p \<in> Paths t |] ==> pcons s p \<in> Paths s";
by(simp add: Paths_def pcons_def split: nat.split);

lemma "lfp(eufix A B) \<subseteq> eusem A B"
apply(rule lfp_lowerbound)
apply(clarsimp simp add: eusem_def eufix_def);
apply(erule disjE);
 apply(rule_tac x = "apath x" in bexI);
  apply(rule_tac x = 0 in exI);
  apply simp;
 apply simp;
apply(clarify);
apply(rule_tac x = "pcons xb p" in bexI);
 apply(rule_tac x = "j+1" in exI);
 apply (simp add: pcons_def split: nat.split);
apply (simp add: pcons_PathI)
done
*)
(*>*)

text\<open>Let us close this section with a few words about the executability of
our model checkers.  It is clear that if all sets are finite, they can be
represented as lists and the usual set operations are easily
implemented. Only \<^const>\<open>lfp\<close> requires a little thought.  Fortunately, theory
\<open>While_Combinator\<close> in the Library~\<^cite>\<open>"HOL-Library"\<close> provides a
theorem stating that in the case of finite sets and a monotone
function~\<^term>\<open>F\<close>, the value of \mbox{\<^term>\<open>lfp F\<close>} can be computed by
iterated application of \<^term>\<open>F\<close> to~\<^term>\<open>{}\<close> until a fixed point is
reached. It is actually possible to generate executable functional programs
from HOL definitions, but that is beyond the scope of the tutorial.%
\index{CTL|)}\<close>
(*<*)end(*>*)
