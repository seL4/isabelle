(*<*)theory CTL = Base:;(*>*)

subsection{*Computation tree logic---CTL*};

text{*
The semantics of PDL only needs transitive reflexive closure.
Let us now be a bit more adventurous and introduce a new temporal operator
that goes beyond transitive reflexive closure. We extend the datatype
@{text formula} by a new constructor
*};
(*<*)
datatype formula = Atom atom
                  | Neg formula
                  | And formula formula
                  | AX formula
                  | EF formula(*>*)
                  | AF formula;

text{*\noindent
which stands for "always in the future":
on all paths, at some point the formula holds. Formalizing the notion of an infinite path is easy
in HOL: it is simply a function from @{typ nat} to @{typ state}.
*};

constdefs Paths :: "state \<Rightarrow> (nat \<Rightarrow> state)set"
         "Paths s \<equiv> {p. s = p 0 \<and> (\<forall>i. (p i, p(i+1)) \<in> M)}";

text{*\noindent
This definition allows a very succinct statement of the semantics of @{term AF}:
\footnote{Do not be mislead: neither datatypes nor recursive functions can be
extended by new constructors or equations. This is just a trick of the
presentation. In reality one has to define a new datatype and a new function.}
*};
(*<*)
consts valid :: "state \<Rightarrow> formula \<Rightarrow> bool" ("(_ \<Turnstile> _)" [80,80] 80);

primrec
"s \<Turnstile> Atom a  =  (a \<in> L s)"
"s \<Turnstile> Neg f   = (~(s \<Turnstile> f))"
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)"
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)"
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M^* \<and> t \<Turnstile> f)"
(*>*)
"s \<Turnstile> AF f    = (\<forall>p \<in> Paths s. \<exists>i. p i \<Turnstile> f)";

text{*\noindent
Model checking @{term AF} involves a function which
is just complicated enough to warrant a separate definition:
*};

constdefs af :: "state set \<Rightarrow> state set \<Rightarrow> state set"
         "af A T \<equiv> A \<union> {s. \<forall>t. (s, t) \<in> M \<longrightarrow> t \<in> T}";

text{*\noindent
Now we define @{term "mc(AF f)"} as the least set @{term T} that contains
@{term"mc f"} and all states all of whose direct successors are in @{term T}:
*};
(*<*)
consts mc :: "formula \<Rightarrow> state set";
primrec
"mc(Atom a)  = {s. a \<in> L s}"
"mc(Neg f)   = -mc f"
"mc(And f g) = mc f \<inter> mc g"
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}"
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> M^-1 ^^ T)"(*>*)
"mc(AF f)    = lfp(af(mc f))";

text{*\noindent
Because @{term af} is monotone in its second argument (and also its first, but
that is irrelevant) @{term"af A"} has a least fixpoint:
*};

lemma mono_af: "mono(af A)";
apply(simp add: mono_def af_def);
apply blast;
done
(*<*)
lemma mono_ef: "mono(\<lambda>T. A \<union> M^-1 ^^ T)";
apply(rule monoI);
by(blast);

lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> M^-1 ^^ T) = {s. \<exists>t. (s,t) \<in> M^* \<and> t \<in> A}";
apply(rule equalityI);
 apply(rule subsetI);
 apply(simp);
 apply(erule Lfp.induct);
  apply(rule mono_ef);
 apply(simp);
 apply(blast intro: r_into_rtrancl rtrancl_trans);
apply(rule subsetI);
apply(simp, clarify);
apply(erule converse_rtrancl_induct);
 apply(rule ssubst[OF lfp_Tarski[OF mono_ef]]);
 apply(blast);
apply(rule ssubst[OF lfp_Tarski[OF mono_ef]]);
by(blast);
(*>*)
text{*
All we need to prove now is that @{term mc} and @{text"\<Turnstile>"}
agree for @{term AF}, i.e.\ that @{prop"mc(AF f) = {s. s \<Turnstile>
AF f}"}. This time we prove the two containments separately, starting
with the easy one:
*};

theorem AF_lemma1:
  "lfp(af A) \<subseteq> {s. \<forall> p \<in> Paths s. \<exists> i. p i \<in> A}";

txt{*\noindent
The proof is again pointwise. Fixpoint induction on the premise @{prop"s \<in> lfp(af A)"} followed
by simplification and clarification
*};

apply(rule subsetI);
apply(erule Lfp.induct[OF _ mono_af]);
apply(clarsimp simp add: af_def Paths_def);
(*ML"Pretty.setmargin 70";
pr(latex xsymbols symbols);*)
txt{*\noindent
FIXME OF/of with undescore?

leads to the following somewhat involved proof state
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}p{\isachardot}\ {\isasymlbrakk}p\ \isadigit{0}\ {\isasymin}\ A\ {\isasymor}\isanewline
\ \ \ \ \ \ \ \ \ {\isacharparenleft}{\isasymforall}t{\isachardot}\ {\isacharparenleft}p\ \isadigit{0}{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymlongrightarrow}\isanewline
\ \ \ \ \ \ \ \ \ \ \ \ \ \ t\ {\isasymin}\ lfp\ {\isacharparenleft}af\ A{\isacharparenright}\ {\isasymand}\isanewline
\ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}{\isasymforall}p{\isachardot}\ t\ {\isacharequal}\ p\ \isadigit{0}\ {\isasymand}\ {\isacharparenleft}{\isasymforall}i{\isachardot}\ {\isacharparenleft}p\ i{\isacharcomma}\ p\ {\isacharparenleft}Suc\ i{\isacharparenright}{\isacharparenright}\ {\isasymin}\ M{\isacharparenright}\ {\isasymlongrightarrow}\isanewline
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}{\isasymexists}i{\isachardot}\ p\ i\ {\isasymin}\ A{\isacharparenright}{\isacharparenright}{\isacharparenright}{\isacharsemicolon}\isanewline
\ \ \ \ \ \ \ \ \ \ \ {\isasymforall}i{\isachardot}\ {\isacharparenleft}p\ i{\isacharcomma}\ p\ {\isacharparenleft}Suc\ i{\isacharparenright}{\isacharparenright}\ {\isasymin}\ M{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymexists}i{\isachardot}\ p\ i\ {\isasymin}\ A
\end{isabelle}
Now we eliminate the disjunction. The case @{prop"p 0 \<in> A"} is trivial:
*};

apply(erule disjE);
 apply(blast);

txt{*\noindent
In the other case we set @{term t} to @{term"p 1"} and simplify matters:
*};

apply(erule_tac x = "p 1" in allE);
apply(clarsimp);
(*ML"Pretty.setmargin 70";
pr(latex xsymbols symbols);*)

txt{*
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}p{\isachardot}\ {\isasymlbrakk}{\isasymforall}i{\isachardot}\ {\isacharparenleft}p\ i{\isacharcomma}\ p\ {\isacharparenleft}Suc\ i{\isacharparenright}{\isacharparenright}\ {\isasymin}\ M{\isacharsemicolon}\ p\ \isadigit{1}\ {\isasymin}\ lfp\ {\isacharparenleft}af\ A{\isacharparenright}{\isacharsemicolon}\isanewline
\ \ \ \ \ \ \ \ \ \ \ {\isasymforall}pa{\isachardot}\ p\ \isadigit{1}\ {\isacharequal}\ pa\ \isadigit{0}\ {\isasymand}\ {\isacharparenleft}{\isasymforall}i{\isachardot}\ {\isacharparenleft}pa\ i{\isacharcomma}\ pa\ {\isacharparenleft}Suc\ i{\isacharparenright}{\isacharparenright}\ {\isasymin}\ M{\isacharparenright}\ {\isasymlongrightarrow}\isanewline
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}{\isasymexists}i{\isachardot}\ pa\ i\ {\isasymin}\ A{\isacharparenright}{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymexists}i{\isachardot}\ p\ i\ {\isasymin}\ A
\end{isabelle}
It merely remains to set @{term pa} to @{term"\<lambda>i. p(i+1)"}, i.e.\ @{term p} without its
first element. The rest is practically automatic:
*};

apply(erule_tac x = "\<lambda>i. p(i+1)" in allE);
apply simp;
apply blast;
done;

text{*
The opposite containment is proved by contradiction: if some state
@{term s} is not in @{term"lfp(af A)"}, then we can construct an
infinite @{term A}-avoiding path starting from @{term s}. The reason is
that by unfolding @{term lfp} we find that if @{term s} is not in
@{term"lfp(af A)"}, then @{term s} is not in @{term A} and there is a
direct successor of @{term s} that is again not in @{term"lfp(af
A)"}. Iterating this argument yields the promised infinite
@{term A}-avoiding path. Let us formalize this sketch.

The one-step argument in the above sketch
*};

lemma not_in_lfp_afD:
 "s \<notin> lfp(af A) \<Longrightarrow> s \<notin> A \<and> (\<exists> t. (s,t)\<in>M \<and> t \<notin> lfp(af A))";
apply(erule swap);
apply(rule ssubst[OF lfp_Tarski[OF mono_af]]);
apply(simp add:af_def);
done;

text{*\noindent
is proved by a variant of contraposition (@{thm[source]swap}:
@{thm swap[no_vars]}), i.e.\ assuming the negation of the conclusion
and proving @{term"s : lfp(af A)"}. Unfolding @{term lfp} once and
simplifying with the definition of @{term af} finishes the proof.

Now we iterate this process. The following construction of the desired
path is parameterized by a predicate @{term P} that should hold along the path:
*};

consts path :: "state \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> state)";
primrec
"path s P 0 = s"
"path s P (Suc n) = (SOME t. (path s P n,t) \<in> M \<and> P t)";

text{*\noindent
Element @{term"n+1"} on this path is some arbitrary successor
@{term t} of element @{term n} such that @{term"P t"} holds.  Remember that @{text"SOME t. R t"}
is some arbitrary but fixed @{term t} such that @{prop"R t"} holds (see \S\ref{sec-SOME}). Of
course, such a @{term t} may in general not exist, but that is of no
concern to us since we will only use @{term path} in such cases where a
suitable @{term t} does exist.

Let us show that if each state @{term s} that satisfies @{term P}
has a successor that again satisfies @{term P}, then there exists an infinite @{term P}-path:
*};

lemma infinity_lemma:
  "\<lbrakk> P s; \<forall>s. P s \<longrightarrow> (\<exists> t. (s,t) \<in> M \<and> P t) \<rbrakk> \<Longrightarrow>
   \<exists>p\<in>Paths s. \<forall>i. P(p i)";

txt{*\noindent
First we rephrase the conclusion slightly because we need to prove both the path property
and the fact that @{term P} holds simultaneously:
*};

apply(subgoal_tac "\<exists>p. s = p 0 \<and> (\<forall>i. (p i,p(i+1)) \<in> M \<and> P(p i))");

txt{*\noindent
From this proposition the original goal follows easily:
*};

 apply(simp add:Paths_def, blast);

txt{*\noindent
The new subgoal is proved by providing the witness @{term "path s P"} for @{term p}:
*};

apply(rule_tac x = "path s P" in exI);
apply(clarsimp);
(*ML"Pretty.setmargin 70";
pr(latex xsymbols symbols);*)

txt{*\noindent
After simplification and clarification the subgoal has the following compact form
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}i{\isachardot}\ {\isasymlbrakk}P\ s{\isacharsemicolon}\ {\isasymforall}s{\isachardot}\ P\ s\ {\isasymlongrightarrow}\ {\isacharparenleft}{\isasymexists}t{\isachardot}\ {\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymand}\ P\ t{\isacharparenright}{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isacharparenleft}path\ s\ P\ i{\isacharcomma}\ SOME\ t{\isachardot}\ {\isacharparenleft}path\ s\ P\ i{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymand}\ P\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymand}\isanewline
\ \ \ \ \ \ \ \ \ \ \ \ P\ {\isacharparenleft}path\ s\ P\ i{\isacharparenright}
\end{isabelle}
and invites a proof by induction on @{term i}:
*};

apply(induct_tac i);
 apply(simp);
(*ML"Pretty.setmargin 70";
pr(latex xsymbols symbols);*)

txt{*\noindent
After simplification the base case boils down to
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymlbrakk}P\ s{\isacharsemicolon}\ {\isasymforall}s{\isachardot}\ P\ s\ {\isasymlongrightarrow}\ {\isacharparenleft}{\isasymexists}t{\isachardot}\ {\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymand}\ P\ t{\isacharparenright}{\isasymrbrakk}\isanewline
\ \ \ \ {\isasymLongrightarrow}\ {\isacharparenleft}s{\isacharcomma}\ SOME\ t{\isachardot}\ {\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymand}\ P\ t{\isacharparenright}\ {\isasymin}\ M
\end{isabelle}
The conclusion looks exceedingly trivial: after all, @{term t} is chosen such that @{prop"(s,t):M"}
holds. However, we first have to show that such a @{term t} actually exists! This reasoning
is embodied in the theorem @{thm[source]someI2_ex}:
@{thm[display,eta_contract=false]someI2_ex}
When we apply this theorem as an introduction rule, @{text"?P x"} becomes
@{prop"(s, x) : M & P x"} and @{text"?Q x"} becomes @{prop"(s,x) : M"} and we have to prove
two subgoals: @{prop"EX a. (s, a) : M & P a"}, which follows from the assumptions, and
@{prop"(s, x) : M & P x ==> (s,x) : M"}, which is trivial. Thus it is not surprising that
@{text fast} can prove the base case quickly:
*};

 apply(fast intro:someI2_ex);

txt{*\noindent
What is worth noting here is that we have used @{text fast} rather than @{text blast}.
The reason is that @{text blast} would fail because it cannot cope with @{thm[source]someI2_ex}:
unifying its conclusion with the current subgoal is nontrivial because of the nested schematic
variables. For efficiency reasons @{text blast} does not even attempt such unifications.
Although @{text fast} can in principle cope with complicated unification problems, in practice
the number of unifiers arising is often prohibitive and the offending rule may need to be applied
explicitly rather than automatically.

The induction step is similar, but more involved, because now we face nested occurrences of
@{text SOME}. We merely show the proof commands but do not describe th details:
*};

apply(simp);
apply(rule someI2_ex);
 apply(blast);
apply(rule someI2_ex);
 apply(blast);
apply(blast);
done;

text{*
Function @{term path} has fulfilled its purpose now and can be forgotten
about. It was merely defined to provide the witness in the proof of the
@{thm[source]infinity_lemma}. Afficionados of minimal proofs might like to know
that we could have given the witness without having to define a new function:
the term
@{term[display]"nat_rec s (\<lambda>n t. SOME u. (t,u)\<in>M \<and> P u)"}
where @{term nat_rec} is the predefined primitive recursor on @{typ nat}, whose defining
equations we omit, is extensionally equal to @{term"path s P"}.
*};
(*<*)
lemma infinity_lemma:
"\<lbrakk> P s; \<forall> s. P s \<longrightarrow> (\<exists> t. (s,t)\<in>M \<and> P t) \<rbrakk> \<Longrightarrow>
 \<exists> p\<in>Paths s. \<forall> i. P(p i)";
apply(subgoal_tac
 "\<exists> p. s = p 0 \<and> (\<forall> i. (p i,p(Suc i))\<in>M \<and> P(p i))");
 apply(simp add:Paths_def);
 apply(blast);
apply(rule_tac x = "nat_rec s (\<lambda>n t. SOME u. (t,u)\<in>M \<and> P u)" in exI);
apply(simp);
apply(intro strip);
apply(induct_tac i);
 apply(simp);
 apply(fast intro:someI2_ex);
apply(simp);
apply(rule someI2_ex);
 apply(blast);
apply(rule someI2_ex);
 apply(blast);
by(blast);
(*>*)

text{*
At last we can prove the opposite direction of @{thm[source]AF_lemma1}:
*};

theorem AF_lemma2:
"{s. \<forall> p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)";

txt{*\noindent
The proof is again pointwise and then by contraposition (@{thm[source]contrapos2} is the rule
@{thm contrapos2}):
*};

apply(rule subsetI);
apply(erule contrapos2);
apply simp;
(*pr(latex xsymbols symbols);*)

txt{*
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}s{\isachardot}\ s\ {\isasymnotin}\ lfp\ {\isacharparenleft}af\ A{\isacharparenright}\ {\isasymLongrightarrow}\ {\isasymexists}p{\isasymin}Paths\ s{\isachardot}\ {\isasymforall}i{\isachardot}\ p\ i\ {\isasymnotin}\ A
\end{isabelle}
Applying the @{thm[source]infinity_lemma} as a destruction rule leaves two subgoals, the second
premise of @{thm[source]infinity_lemma} and the original subgoal:
*};

apply(drule infinity_lemma);
(*pr(latex xsymbols symbols);*)

txt{*
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymAnd}s{\isachardot}\ {\isasymforall}s{\isachardot}\ s\ {\isasymnotin}\ lfp\ {\isacharparenleft}af\ A{\isacharparenright}\ {\isasymlongrightarrow}\ {\isacharparenleft}{\isasymexists}t{\isachardot}\ {\isacharparenleft}s{\isacharcomma}\ t{\isacharparenright}\ {\isasymin}\ M\ {\isasymand}\ t\ {\isasymnotin}\ lfp\ {\isacharparenleft}af\ A{\isacharparenright}{\isacharparenright}\isanewline
\ \isadigit{2}{\isachardot}\ {\isasymAnd}s{\isachardot}\ {\isasymexists}p{\isasymin}Paths\ s{\isachardot}\ {\isasymforall}i{\isachardot}\ p\ i\ {\isasymnotin}\ lfp\ {\isacharparenleft}af\ A{\isacharparenright}\isanewline
\ \ \ \ \ \ {\isasymLongrightarrow}\ {\isasymexists}p{\isasymin}Paths\ s{\isachardot}\ {\isasymforall}i{\isachardot}\ p\ i\ {\isasymnotin}\ A
\end{isabelle}
Both are solved automatically:
*};

 apply(auto dest:not_in_lfp_afD);
done;

text{*
The main theorem is proved as for PDL, except that we also derive the necessary equality
@{text"lfp(af A) = ..."} by combining @{thm[source]AF_lemma1} and @{thm[source]AF_lemma2}
on the spot:
*}

theorem "mc f = {s. s \<Turnstile> f}";
apply(induct_tac f);
apply(auto simp add: EF_lemma equalityI[OF AF_lemma1 AF_lemma2]);
done

text{*
Let us close this section with a few words about the executability of @{term mc}.
It is clear that if all sets are finite, they can be represented as lists and the usual
set operations are easily implemented. Only @{term lfp} requires a little thought.
Fortunately the HOL library proves that in the case of finite sets and a monotone @{term F},
@{term"lfp F"} can be computed by iterated application of @{term F} to @{term"{}"} until
a fixpoint is reached. It is possible to generate executable functional programs
from HOL definitions, but that is beyond the scope of the tutorial.
*}

(*<*)
(*
Second proof of opposite direction, directly by wellfounded induction
on the initial segment of M that avoids A.

Avoid s A = the set of successors of s that can be reached by a finite A-avoiding path
*)

consts Avoid :: "state \<Rightarrow> state set \<Rightarrow> state set";
inductive "Avoid s A"
intros "s \<in> Avoid s A"
       "\<lbrakk> t \<in> Avoid s A; t \<notin> A; (t,u) \<in> M \<rbrakk> \<Longrightarrow> u \<in> Avoid s A";

(* For any infinite A-avoiding path (f) in Avoid s A,
   there is some infinite A-avoiding path (p) in Avoid s A that starts with s.
*)
lemma ex_infinite_path[rule_format]:
"t \<in> Avoid s A  \<Longrightarrow>
 \<forall>f. t = f 0 \<longrightarrow> (\<forall>i. (f i, f (Suc i)) \<in> M \<and> f i \<in> Avoid s A \<and> f i \<notin> A)
                \<longrightarrow> (\<exists> p\<in>Paths s. \<forall>i. p i \<notin> A)";
apply(simp add:Paths_def);
apply(erule Avoid.induct);
 apply(blast);
apply(rule allI);
apply(erule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> t | Suc i \<Rightarrow> f i" in allE);
by(force split:nat.split);

lemma Avoid_in_lfp[rule_format(no_asm)]:
"\<forall>p\<in>Paths s. \<exists>i. p i \<in> A \<Longrightarrow> t \<in> Avoid s A \<longrightarrow> t \<in> lfp(af A)";
apply(subgoal_tac "wf{(y,x). (x,y)\<in>M \<and> x \<in> Avoid s A \<and> y \<in> Avoid s A \<and> x \<notin> A}");
 apply(erule_tac a = t in wf_induct);
 apply(clarsimp);
 apply(rule ssubst [OF lfp_Tarski[OF mono_af]]);
 apply(unfold af_def);
 apply(blast intro:Avoid.intros);
apply(erule contrapos2);
apply(simp add:wf_iff_no_infinite_down_chain);
apply(erule exE);
apply(rule ex_infinite_path);
by(auto);

theorem AF_lemma2:
"{s. \<forall>p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)";
apply(rule subsetI);
apply(simp);
apply(erule Avoid_in_lfp);
by(rule Avoid.intros);

end(*>*)
