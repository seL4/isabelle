(*<*)theory CTL = Base:(*>*)

subsection{*Computation tree logic---CTL*}

text{*
The semantics of PDL only needs transitive reflexive closure.
Let us now be a bit more adventurous and introduce a new temporal operator
that goes beyond transitive reflexive closure. We extend the datatype
@{text formula} by a new constructor
*}
(*<*)
datatype formula = Atom atom
                  | Neg formula
                  | And formula formula
                  | AX formula
                  | EF formula(*>*)
                  | AF formula

text{*\noindent
which stands for "always in the future":
on all paths, at some point the formula holds. 
Introducing the notion of paths (in @{term M})
*}

constdefs Paths :: "state \<Rightarrow> (nat \<Rightarrow> state)set"
         "Paths s \<equiv> {p. s = p 0 \<and> (\<forall>i. (p i, p(i+1)) \<in> M)}";

text{*\noindent
allows a very succinct definition of the semantics of @{term AF}:
\footnote{Do not be mislead: neither datatypes nor recursive functions can be
extended by new constructors or equations. This is just a trick of the
presentation. In reality one has to define a new datatype and a new function.}
*}
(*<*)
consts valid :: "state \<Rightarrow> formula \<Rightarrow> bool" ("(_ \<Turnstile> _)" [80,80] 80)

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
is just large enough to warrant a separate definition:
*}

constdefs af :: "state set \<Rightarrow> state set \<Rightarrow> state set"
         "af A T \<equiv> A \<union> {s. \<forall>t. (s, t) \<in> M \<longrightarrow> t \<in> T}";

text{*\noindent
This function is monotone in its second argument (and also its first, but
that is irrelevant), and hence @{term"af A"} has a least fixpoint.
*}

lemma mono_af: "mono(af A)";
apply(simp add: mono_def af_def)
by(blast);

text{*\noindent
Now we can define @{term "mc(AF f)"} as the least set @{term T} that contains
@{term"mc f"} and all states all of whose direct successors are in @{term T}:
*}
(*<*)
consts mc :: "formula \<Rightarrow> state set";
primrec
"mc(Atom a)  = {s. a \<in> L s}"
"mc(Neg f)   = -mc f"
"mc(And f g) = mc f \<inter> mc g"
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}"
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> M^-1 ^^ T)"(*>*)
"mc(AF f)    = lfp(af(mc f))";
(*<*)
lemma mono_ef: "mono(\<lambda>T. A \<union> M^-1 ^^ T)"
apply(rule monoI)
by(blast)

lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> M^-1 ^^ T) = {s. \<exists>t. (s,t) \<in> M^* \<and> t \<in> A}"
apply(rule equalityI);
 apply(rule subsetI);
 apply(simp)
 apply(erule Lfp.induct)
  apply(rule mono_ef)
 apply(simp)
 apply(blast intro: r_into_rtrancl rtrancl_trans);
apply(rule subsetI)
apply(simp, clarify)
apply(erule converse_rtrancl_induct)
 apply(rule ssubst[OF lfp_Tarski[OF mono_ef]])
 apply(blast)
apply(rule ssubst[OF lfp_Tarski[OF mono_ef]])
by(blast)
(*>*)

theorem lfp_subset_AF:
"lfp(af A) \<subseteq> {s. \<forall> p \<in> Paths s. \<exists> i. p i \<in> A}";
apply(rule subsetI);
apply(erule Lfp.induct[OF _ mono_af]);
apply(simp add: af_def Paths_def);
apply(erule disjE);
 apply(blast);
apply(clarify);
apply(erule_tac x = "p 1" in allE);
apply(clarsimp);
apply(erule_tac x = "\<lambda>i. p(i+1)" in allE);
apply(simp);
by(blast);

text{*
The opposite direction is proved by contradiction: if some state
{term s} is not in @{term"lfp(af A)"}, then we can construct an
infinite @{term A}-avoiding path starting from @{term s}. The reason is
that by unfolding @{term"lfp"} we find that if @{term s} is not in
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
by(simp add:af_def);

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
@{term"t"} of element @{term"n"} such that @{term"P t"} holds.  Of
course, such a @{term"t"} may in general not exist, but that is of no
concern to us since we will only use @{term path} in such cases where a
suitable @{term"t"} does exist.

Now we prove that if each state @{term"s"} that satisfies @{term"P"}
has a successor that again satisfies @{term"P"}, then there exists an infinite @{term"P"}-path.
*};

lemma seq_lemma:
"\<lbrakk> P s; \<forall>s. P s \<longrightarrow> (\<exists> t. (s,t)\<in>M \<and> P t) \<rbrakk> \<Longrightarrow> \<exists>p\<in>Paths s. \<forall>i. P(p i)";

txt{*\noindent
First we rephrase the conclusion slightly because we need to prove both the path property
and the fact that @{term"P"} holds simultaneously:
*};

apply(subgoal_tac "\<exists> p. s = p 0 \<and> (\<forall> i. (p i,p(i+1)) \<in> M \<and> P(p i))");

txt{*\noindent
From this proposition the original goal follows easily
*};

 apply(simp add:Paths_def, blast);
apply(rule_tac x = "path s P" in exI);
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

lemma seq_lemma:
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

theorem AF_subset_lfp:
"{s. \<forall> p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)";
apply(rule subsetI);
apply(erule contrapos2);
apply simp;
apply(drule seq_lemma);
by(auto dest:not_in_lfp_afD);


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

theorem AF_subset_lfp:
"{s. \<forall>p \<in> Paths s. \<exists> i. p i \<in> A} \<subseteq> lfp(af A)";
apply(rule subsetI);
apply(simp);
apply(erule Avoid_in_lfp);
by(rule Avoid.intros);


theorem "mc f = {s. s \<Turnstile> f}";
apply(induct_tac f);
by(auto simp add: EF_lemma equalityI[OF lfp_subset_AF AF_subset_lfp]);

(*<*)end(*>*)
