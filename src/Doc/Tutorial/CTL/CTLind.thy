(*<*)theory CTLind imports CTL begin(*>*)

subsection\<open>CTL Revisited\<close>

text\<open>\label{sec:CTL-revisited}
\index{CTL|(}%
The purpose of this section is twofold: to demonstrate
some of the induction principles and heuristics discussed above and to
show how inductive definitions can simplify proofs.
In \S\ref{sec:CTL} we gave a fairly involved proof of the correctness of a
model checker for CTL\@. In particular the proof of the
@{thm[source]infinity_lemma} on the way to @{thm[source]AF_lemma2} is not as
simple as one might expect, due to the \<open>SOME\<close> operator
involved. Below we give a simpler proof of @{thm[source]AF_lemma2}
based on an auxiliary inductive definition.

Let us call a (finite or infinite) path \emph{\<^term>\<open>A\<close>-avoiding} if it does
not touch any node in the set \<^term>\<open>A\<close>. Then @{thm[source]AF_lemma2} says
that if no infinite path from some state \<^term>\<open>s\<close> is \<^term>\<open>A\<close>-avoiding,
then \<^prop>\<open>s \<in> lfp(af A)\<close>. We prove this by inductively defining the set
\<^term>\<open>Avoid s A\<close> of states reachable from \<^term>\<open>s\<close> by a finite \<^term>\<open>A\<close>-avoiding path:
% Second proof of opposite direction, directly by well-founded induction
% on the initial segment of M that avoids A.
\<close>

inductive_set
  Avoid :: "state \<Rightarrow> state set \<Rightarrow> state set"
  for s :: state and A :: "state set"
where
    "s \<in> Avoid s A"
  | "\<lbrakk> t \<in> Avoid s A; t \<notin> A; (t,u) \<in> M \<rbrakk> \<Longrightarrow> u \<in> Avoid s A"

text\<open>
It is easy to see that for any infinite \<^term>\<open>A\<close>-avoiding path \<^term>\<open>f\<close>
with \<^prop>\<open>f(0::nat) \<in> Avoid s A\<close> there is an infinite \<^term>\<open>A\<close>-avoiding path
starting with \<^term>\<open>s\<close> because (by definition of \<^const>\<open>Avoid\<close>) there is a
finite \<^term>\<open>A\<close>-avoiding path from \<^term>\<open>s\<close> to \<^term>\<open>f(0::nat)\<close>.
The proof is by induction on \<^prop>\<open>f(0::nat) \<in> Avoid s A\<close>. However,
this requires the following
reformulation, as explained in \S\ref{sec:ind-var-in-prems} above;
the \<open>rule_format\<close> directive undoes the reformulation after the proof.
\<close>

lemma ex_infinite_path[rule_format]:
  "t \<in> Avoid s A  \<Longrightarrow>
   \<forall>f\<in>Paths t. (\<forall>i. f i \<notin> A) \<longrightarrow> (\<exists>p\<in>Paths s. \<forall>i. p i \<notin> A)"
apply(erule Avoid.induct)
 apply(blast)
apply(clarify)
apply(drule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> t | Suc i \<Rightarrow> f i" in bspec)
apply(simp_all add: Paths_def split: nat.split)
done

text\<open>\noindent
The base case (\<^prop>\<open>t = s\<close>) is trivial and proved by \<open>blast\<close>.
In the induction step, we have an infinite \<^term>\<open>A\<close>-avoiding path \<^term>\<open>f\<close>
starting from \<^term>\<open>u\<close>, a successor of \<^term>\<open>t\<close>. Now we simply instantiate
the \<open>\<forall>f\<in>Paths t\<close> in the induction hypothesis by the path starting with
\<^term>\<open>t\<close> and continuing with \<^term>\<open>f\<close>. That is what the above $\lambda$-term
expresses.  Simplification shows that this is a path starting with \<^term>\<open>t\<close> 
and that the instantiated induction hypothesis implies the conclusion.

Now we come to the key lemma. Assuming that no infinite \<^term>\<open>A\<close>-avoiding
path starts from \<^term>\<open>s\<close>, we want to show \<^prop>\<open>s \<in> lfp(af A)\<close>. For the
inductive proof this must be generalized to the statement that every point \<^term>\<open>t\<close>
``between'' \<^term>\<open>s\<close> and \<^term>\<open>A\<close>, in other words all of \<^term>\<open>Avoid s A\<close>,
is contained in \<^term>\<open>lfp(af A)\<close>:
\<close>

lemma Avoid_in_lfp[rule_format(no_asm)]:
  "\<forall>p\<in>Paths s. \<exists>i. p i \<in> A \<Longrightarrow> t \<in> Avoid s A \<longrightarrow> t \<in> lfp(af A)"

txt\<open>\noindent
The proof is by induction on the ``distance'' between \<^term>\<open>t\<close> and \<^term>\<open>A\<close>. Remember that \<^prop>\<open>lfp(af A) = A \<union> M\<inverse> `` lfp(af A)\<close>.
If \<^term>\<open>t\<close> is already in \<^term>\<open>A\<close>, then \<^prop>\<open>t \<in> lfp(af A)\<close> is
trivial. If \<^term>\<open>t\<close> is not in \<^term>\<open>A\<close> but all successors are in
\<^term>\<open>lfp(af A)\<close> (induction hypothesis), then \<^prop>\<open>t \<in> lfp(af A)\<close> is
again trivial.

The formal counterpart of this proof sketch is a well-founded induction
on~\<^term>\<open>M\<close> restricted to \<^term>\<open>Avoid s A - A\<close>, roughly speaking:
@{term[display]"{(y,x). (x,y) \<in> M \<and> x \<in> Avoid s A \<and> x \<notin> A}"}
As we shall see presently, the absence of infinite \<^term>\<open>A\<close>-avoiding paths
starting from \<^term>\<open>s\<close> implies well-foundedness of this relation. For the
moment we assume this and proceed with the induction:
\<close>

apply(subgoal_tac "wf{(y,x). (x,y) \<in> M \<and> x \<in> Avoid s A \<and> x \<notin> A}")
 apply(erule_tac a = t in wf_induct)
 apply(clarsimp)
(*<*)apply(rename_tac t)(*>*)

txt\<open>\noindent
@{subgoals[display,indent=0,margin=65]}
Now the induction hypothesis states that if \<^prop>\<open>t \<notin> A\<close>
then all successors of \<^term>\<open>t\<close> that are in \<^term>\<open>Avoid s A\<close> are in
\<^term>\<open>lfp (af A)\<close>. Unfolding \<^term>\<open>lfp\<close> in the conclusion of the first
subgoal once, we have to prove that \<^term>\<open>t\<close> is in \<^term>\<open>A\<close> or all successors
of \<^term>\<open>t\<close> are in \<^term>\<open>lfp (af A)\<close>.  But if \<^term>\<open>t\<close> is not in \<^term>\<open>A\<close>,
the second 
\<^const>\<open>Avoid\<close>-rule implies that all successors of \<^term>\<open>t\<close> are in
\<^term>\<open>Avoid s A\<close>, because we also assume \<^prop>\<open>t \<in> Avoid s A\<close>.
Hence, by the induction hypothesis, all successors of \<^term>\<open>t\<close> are indeed in
\<^term>\<open>lfp(af A)\<close>. Mechanically:
\<close>

 apply(subst lfp_unfold[OF mono_af])
 apply(simp (no_asm) add: af_def)
 apply(blast intro: Avoid.intros)

txt\<open>
Having proved the main goal, we return to the proof obligation that the 
relation used above is indeed well-founded. This is proved by contradiction: if
the relation is not well-founded then there exists an infinite \<^term>\<open>A\<close>-avoiding path all in \<^term>\<open>Avoid s A\<close>, by theorem
@{thm[source]wf_iff_no_infinite_down_chain}:
@{thm[display]wf_iff_no_infinite_down_chain[no_vars]}
From lemma @{thm[source]ex_infinite_path} the existence of an infinite
\<^term>\<open>A\<close>-avoiding path starting in \<^term>\<open>s\<close> follows, contradiction.
\<close>

apply(erule contrapos_pp)
apply(simp add: wf_iff_no_infinite_down_chain)
apply(erule exE)
apply(rule ex_infinite_path)
apply(auto simp add: Paths_def)
done

text\<open>
The \<open>(no_asm)\<close> modifier of the \<open>rule_format\<close> directive in the
statement of the lemma means
that the assumption is left unchanged; otherwise the \<open>\<forall>p\<close> 
would be turned
into a \<open>\<And>p\<close>, which would complicate matters below. As it is,
@{thm[source]Avoid_in_lfp} is now
@{thm[display]Avoid_in_lfp[no_vars]}
The main theorem is simply the corollary where \<^prop>\<open>t = s\<close>,
when the assumption \<^prop>\<open>t \<in> Avoid s A\<close> is trivially true
by the first \<^const>\<open>Avoid\<close>-rule. Isabelle confirms this:%
\index{CTL|)}\<close>

theorem AF_lemma2:  "{s. \<forall>p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)"
by(auto elim: Avoid_in_lfp intro: Avoid.intros)


(*<*)end(*>*)
