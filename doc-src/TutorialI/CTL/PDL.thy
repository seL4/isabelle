theory PDL = Main:;

typedecl atom;
types state = "atom set";

datatype ctl_form = Atom atom
                  | NOT ctl_form
                  | And ctl_form ctl_form
                  | AX ctl_form
                  | EF ctl_form;

consts valid :: "state \<Rightarrow> ctl_form \<Rightarrow> bool" ("(_ \<Turnstile> _)" [80,80] 80)
       M :: "(state \<times> state)set";

primrec
"s \<Turnstile> Atom a  = (a\<in>s)"
"s \<Turnstile> NOT f   = (\<not>(s \<Turnstile> f))"
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)"
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)"
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M^* \<and> t \<Turnstile> f)";

consts mc :: "ctl_form \<Rightarrow> state set";
primrec
"mc(Atom a)  = {s. a\<in>s}"
"mc(NOT f)   = -mc f"
"mc(And f g) = mc f Int mc g"
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}"
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> {s. \<exists>t. (s,t)\<in>M \<and> t\<in>T})";

lemma mono_lemma: "mono(\<lambda>T. A \<union> {s. \<exists>t. (s,t)\<in>M \<and> t\<in>T})";
apply(rule monoI);
by(blast);

lemma lfp_conv_EF:
"lfp(\<lambda>T. A \<union> {s. \<exists>t. (s,t)\<in>M \<and> t\<in>T}) = {s. \<exists>t. (s,t) \<in> M^* \<and> t \<in> A}";
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

end;
