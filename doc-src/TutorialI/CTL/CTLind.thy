(*<*)theory CTLind = CTL:(*>*)

subsection{*CTL Revisited*}

text{*\label{sec:CTL-revisited}
The purpose of this section is twofold: we want to demonstrate
some of the induction principles and heuristics discussed above and we want to
show how inductive definitions can simplify proofs.
In \S\ref{sec:CTL} we gave a fairly involved proof of the correctness of a
model checker for CTL\@. In particular the proof of the
@{thm[source]infinity_lemma} on the way to @{thm[source]AF_lemma2} is not as
simple as one might intuitively expect, due to the @{text SOME} operator
involved. Below we give a simpler proof of @{thm[source]AF_lemma2}
based on an auxiliary inductive definition.

Let us call a (finite or infinite) path \emph{@{term A}-avoiding} if it does
not touch any node in the set @{term A}. Then @{thm[source]AF_lemma2} says
that if no infinite path from some state @{term s} is @{term A}-avoiding,
then @{prop"s \<in> lfp(af A)"}. We prove this by inductively defining the set
@{term"Avoid s A"} of states reachable from @{term s} by a finite @{term
A}-avoiding path:
% Second proof of opposite direction, directly by well-founded induction
% on the initial segment of M that avoids A.
*}

consts Avoid :: "state \<Rightarrow> state set \<Rightarrow> state set";
inductive "Avoid s A"
intros "s \<in> Avoid s A"
       "\<lbrakk> t \<in> Avoid s A; t \<notin> A; (t,u) \<in> M \<rbrakk> \<Longrightarrow> u \<in> Avoid s A";

text{*
It is easy to see that for any infinite @{term A}-avoiding path @{term f}
with @{prop"f 0 \<in> Avoid s A"} there is an infinite @{term A}-avoiding path
starting with @{term s} because (by definition of @{term Avoid}) there is a
finite @{term A}-avoiding path from @{term s} to @{term"f 0"}.
The proof is by induction on @{prop"f 0 \<in> Avoid s A"}. However,
this requires the following
reformulation, as explained in \S\ref{sec:ind-var-in-prems} above;
the @{text rule_format} directive undoes the reformulation after the proof.
*}

lemma ex_infinite_path[rule_format]:
  "t \<in> Avoid s A  \<Longrightarrow>
   \<forall>f\<in>Paths t. (\<forall>i. f i \<notin> A) \<longrightarrow> (\<exists>p\<in>Paths s. \<forall>i. p i \<notin> A)";
apply(erule Avoid.induct);
 apply(blast);
apply(clarify);
apply(drule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> t | Suc i \<Rightarrow> f i" in bspec);
apply(simp_all add:Paths_def split:nat.split);
done

text{*\noindent
The base case (@{prop"t = s"}) is trivial (@{text blast}).
In the induction step, we have an infinite @{term A}-avoiding path @{term f}
starting from @{term u}, a successor of @{term t}. Now we simply instantiate
the @{text"\<forall>f\<in>Paths t"} in the induction hypothesis by the path starting with
@{term t} and continuing with @{term f}. That is what the above $\lambda$-term
expresses.  Simplification shows that this is a path starting with @{term t} 
and that the instantiated induction hypothesis implies the conclusion.

Now we come to the key lemma. It says that if @{term t} can be reached by a
finite @{term A}-avoiding path from @{term s}, then @{prop"t \<in> lfp(af A)"},
provided there is no infinite @{term A}-avoiding path starting from @{term
s}.
*}

lemma Avoid_in_lfp[rule_format(no_asm)]:
  "\<forall>p\<in>Paths s. \<exists>i. p i \<in> A \<Longrightarrow> t \<in> Avoid s A \<longrightarrow> t \<in> lfp(af A)";
txt{*\noindent
The trick is not to induct on @{prop"t \<in> Avoid s A"}, as even the base
case would be a problem, but to proceed by well-founded induction on~@{term
t}. Hence\hbox{ @{prop"t \<in> Avoid s A"}} must be brought into the conclusion as
well, which the directive @{text rule_format} undoes at the end (see below).
But induction with respect to which well-founded relation? The
one we want is the restriction
of @{term M} to @{term"Avoid s A"}:
@{term[display]"{(y,x). (x,y) \<in> M \<and> x \<in> Avoid s A \<and> y \<in> Avoid s A \<and> x \<notin> A}"}
As we shall see in a moment, the absence of infinite @{term A}-avoiding paths
starting from @{term s} implies well-foundedness of this relation. For the
moment we assume this and proceed with the induction:
*}

apply(subgoal_tac
  "wf{(y,x). (x,y)\<in>M \<and> x \<in> Avoid s A \<and> y \<in> Avoid s A \<and> x \<notin> A}");
 apply(erule_tac a = t in wf_induct);
 apply(clarsimp);

txt{*\noindent
@{subgoals[display,indent=0,margin=65]}
\REMARK{I put in this proof state but I wonder if readers will be able to
follow this proof. You could prove that your relation is WF in a 
lemma beforehand, maybe omitting that proof.}
Now the induction hypothesis states that if @{prop"t \<notin> A"}
then all successors of @{term t} that are in @{term"Avoid s A"} are in
@{term"lfp (af A)"}. To prove the actual goal we unfold @{term lfp} once. Now
we have to prove that @{term t} is in @{term A} or all successors of @{term
t} are in @{term"lfp (af A)"}. If @{term t} is not in @{term A}, the second
@{term Avoid}-rule implies that all successors of @{term t} are in
@{term"Avoid s A"} (because we also assume @{prop"t \<in> Avoid s A"}), and
hence, by the induction hypothesis, all successors of @{term t} are indeed in
@{term"lfp(af A)"}. Mechanically:
*}

 apply(rule ssubst [OF lfp_unfold[OF mono_af]]);
 apply(simp only: af_def);
 apply(blast intro:Avoid.intros);

txt{*
Having proved the main goal we return to the proof obligation that the above
relation is indeed well-founded. This is proved by contradiction: if
the relation is not well-founded then there exists an infinite @{term
A}-avoiding path all in @{term"Avoid s A"}, by theorem
@{thm[source]wf_iff_no_infinite_down_chain}:
@{thm[display]wf_iff_no_infinite_down_chain[no_vars]}
From lemma @{thm[source]ex_infinite_path} the existence of an infinite
@{term A}-avoiding path starting in @{term s} follows, contradiction.
*}

apply(erule contrapos_pp);
apply(simp add:wf_iff_no_infinite_down_chain);
apply(erule exE);
apply(rule ex_infinite_path);
apply(auto simp add:Paths_def);
done

text{*
The @{text"(no_asm)"} modifier of the @{text"rule_format"} directive means
that the assumption is left unchanged --- otherwise the @{text"\<forall>p"} is turned
into a @{text"\<And>p"}, which would complicate matters below. As it is,
@{thm[source]Avoid_in_lfp} is now
@{thm[display]Avoid_in_lfp[no_vars]}
The main theorem is simply the corollary where @{prop"t = s"},
in which case the assumption @{prop"t \<in> Avoid s A"} is trivially true
by the first @{term Avoid}-rule. Isabelle confirms this:
*}

theorem AF_lemma2:  "{s. \<forall>p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)";
by(auto elim:Avoid_in_lfp intro:Avoid.intros);


(*<*)end(*>*)
