(*<*)theory CTLind = CTL:(*>*)

subsection{*CTL Revisited*}

text{*\label{sec:CTL-revisited}
\index{CTL|(}%
The purpose of this section is twofold: to demonstrate
some of the induction principles and heuristics discussed above and to
show how inductive definitions can simplify proofs.
In \S\ref{sec:CTL} we gave a fairly involved proof of the correctness of a
model checker for CTL\@. In particular the proof of the
@{thm[source]infinity_lemma} on the way to @{thm[source]AF_lemma2} is not as
simple as one might expect, due to the @{text SOME} operator
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
with @{prop"f(0::nat) \<in> Avoid s A"} there is an infinite @{term A}-avoiding path
starting with @{term s} because (by definition of @{term Avoid}) there is a
finite @{term A}-avoiding path from @{term s} to @{term"f(0::nat)"}.
The proof is by induction on @{prop"f(0::nat) \<in> Avoid s A"}. However,
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
apply(simp_all add: Paths_def split: nat.split);
done

text{*\noindent
The base case (@{prop"t = s"}) is trivial and proved by @{text blast}.
In the induction step, we have an infinite @{term A}-avoiding path @{term f}
starting from @{term u}, a successor of @{term t}. Now we simply instantiate
the @{text"\<forall>f\<in>Paths t"} in the induction hypothesis by the path starting with
@{term t} and continuing with @{term f}. That is what the above $\lambda$-term
expresses.  Simplification shows that this is a path starting with @{term t} 
and that the instantiated induction hypothesis implies the conclusion.

Now we come to the key lemma. Assuming that no infinite @{term A}-avoiding
path starts from @{term s}, we want to show @{prop"s \<in> lfp(af A)"}. For the
inductive proof this must be generalized to the statement that every point @{term t}
``between'' @{term s} and @{term A}, in other words all of @{term"Avoid s A"},
is contained in @{term"lfp(af A)"}:
*}

lemma Avoid_in_lfp[rule_format(no_asm)]:
  "\<forall>p\<in>Paths s. \<exists>i. p i \<in> A \<Longrightarrow> t \<in> Avoid s A \<longrightarrow> t \<in> lfp(af A)";

txt{*\noindent
The proof is by induction on the ``distance'' between @{term t} and @{term
A}. Remember that @{prop"lfp(af A) = A \<union> M\<inverse> `` lfp(af A)"}.
If @{term t} is already in @{term A}, then @{prop"t \<in> lfp(af A)"} is
trivial. If @{term t} is not in @{term A} but all successors are in
@{term"lfp(af A)"} (induction hypothesis), then @{prop"t \<in> lfp(af A)"} is
again trivial.

The formal counterpart of this proof sketch is a well-founded induction
on~@{term M} restricted to @{term"Avoid s A - A"}, roughly speaking:
@{term[display]"{(y,x). (x,y) \<in> M \<and> x \<in> Avoid s A \<and> x \<notin> A}"}
As we shall see presently, the absence of infinite @{term A}-avoiding paths
starting from @{term s} implies well-foundedness of this relation. For the
moment we assume this and proceed with the induction:
*}

apply(subgoal_tac "wf{(y,x). (x,y) \<in> M \<and> x \<in> Avoid s A \<and> x \<notin> A}");
 apply(erule_tac a = t in wf_induct);
 apply(clarsimp);
(*<*)apply(rename_tac t)(*>*)

txt{*\noindent
@{subgoals[display,indent=0,margin=65]}
Now the induction hypothesis states that if @{prop"t \<notin> A"}
then all successors of @{term t} that are in @{term"Avoid s A"} are in
@{term"lfp (af A)"}. Unfolding @{term lfp} in the conclusion of the first
subgoal once, we have to prove that @{term t} is in @{term A} or all successors
of @{term t} are in @{term"lfp (af A)"}.  But if @{term t} is not in @{term A},
the second 
@{term Avoid}-rule implies that all successors of @{term t} are in
@{term"Avoid s A"}, because we also assume @{prop"t \<in> Avoid s A"}.
Hence, by the induction hypothesis, all successors of @{term t} are indeed in
@{term"lfp(af A)"}. Mechanically:
*}

 apply(subst lfp_unfold[OF mono_af]);
 apply(simp (no_asm) add: af_def);
 apply(blast intro: Avoid.intros);

txt{*
Having proved the main goal, we return to the proof obligation that the 
relation used above is indeed well-founded. This is proved by contradiction: if
the relation is not well-founded then there exists an infinite @{term
A}-avoiding path all in @{term"Avoid s A"}, by theorem
@{thm[source]wf_iff_no_infinite_down_chain}:
@{thm[display]wf_iff_no_infinite_down_chain[no_vars]}
From lemma @{thm[source]ex_infinite_path} the existence of an infinite
@{term A}-avoiding path starting in @{term s} follows, contradiction.
*}

apply(erule contrapos_pp);
apply(simp add: wf_iff_no_infinite_down_chain);
apply(erule exE);
apply(rule ex_infinite_path);
apply(auto simp add: Paths_def);
done

text{*
The @{text"(no_asm)"} modifier of the @{text"rule_format"} directive in the
statement of the lemma means
that the assumption is left unchanged; otherwise the @{text"\<forall>p"} 
would be turned
into a @{text"\<And>p"}, which would complicate matters below. As it is,
@{thm[source]Avoid_in_lfp} is now
@{thm[display]Avoid_in_lfp[no_vars]}
The main theorem is simply the corollary where @{prop"t = s"},
when the assumption @{prop"t \<in> Avoid s A"} is trivially true
by the first @{term Avoid}-rule. Isabelle confirms this:%
\index{CTL|)}*}

theorem AF_lemma2:  "{s. \<forall>p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)";
by(auto elim: Avoid_in_lfp intro: Avoid.intros);


(*<*)end(*>*)
