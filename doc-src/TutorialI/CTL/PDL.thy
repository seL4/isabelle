(*<*)theory PDL = Base:(*>*)

subsection{*Propositional dynmic logic---PDL*}

text{*
The formulae of PDL are built up from atomic propositions via the customary
propositional connectives of negation and conjunction and the two temporal
connectives @{text AX} and @{text EF}. Since formulae are essentially
(syntax) trees, they are naturally modelled as a datatype:
*}

datatype pdl_form = Atom atom
                  | NOT pdl_form
                  | And pdl_form pdl_form
                  | AX pdl_form
                  | EF pdl_form;

text{*\noindent
The meaning of these formulae is given by saying which formula is true in
which state:
*}

consts valid :: "state \<Rightarrow> pdl_form \<Rightarrow> bool" ("(_ \<Turnstile> _)" [80,80] 80)

primrec
"s \<Turnstile> Atom a  = (a \<in> L s)"
"s \<Turnstile> NOT f   = (\<not>(s \<Turnstile> f))"
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)"
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)"
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M^* \<and> t \<Turnstile> f)";

text{*
Now we come to the model checker itself. It maps a formula into the set of
states where the formula is true and is defined by recursion over the syntax:
*}

consts mc :: "pdl_form \<Rightarrow> state set";
primrec
"mc(Atom a)  = {s. a \<in> L s}"
"mc(NOT f)   = -mc f"
"mc(And f g) = mc f \<inter> mc g"
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}"
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> M^-1 ^^ T)"


text{*
Only the equation for @{term EF} deserves a comment: the postfix @{text"^-1"}
and the infix @{text"^^"} are predefined and denote the converse of a
relation and the application of a relation to a set. Thus @{term "M^-1 ^^ T"}
is the set of all predecessors of @{term T} and @{term"mc(EF f)"} is the least
set @{term T} containing @{term"mc f"} and all predecessors of @{term T}.
*}

lemma mono_lemma: "mono(\<lambda>T. A \<union> M^-1 ^^ T)"
apply(rule monoI);
by(blast);

lemma lfp_conv_EF:
"lfp(\<lambda>T. A \<union> M^-1 ^^ T) = {s. \<exists>t. (s,t) \<in> M^* \<and> t \<in> A}";
apply(rule equalityI);
 apply(rule subsetI);
 apply(simp);
 apply(erule Lfp.induct);
  apply(rule mono_lemma);
 apply(simp);
 apply(blast intro: r_into_rtrancl rtrancl_trans);
apply(rule subsetI);
apply(simp);
apply(erule exE);
apply(erule conjE);
apply(erule_tac P = "t\<in>A" in rev_mp);
apply(erule converse_rtrancl_induct);
 apply(rule ssubst[OF lfp_Tarski[OF mono_lemma]]);
 apply(blast);
apply(rule ssubst[OF lfp_Tarski[OF mono_lemma]]);
by(blast);

theorem "mc f = {s. s \<Turnstile> f}";
apply(induct_tac f);
by(auto simp add:lfp_conv_EF);
(*<*)end(*>*)
