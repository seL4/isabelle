(*<*)theory Star = Main:(*>*)

section{*The reflexive transitive closure*}

text{*
A perfect example of an inductive definition is the reflexive transitive
closure of a relation. This concept was already introduced in
\S\ref{sec:rtrancl}, but it was not shown how it is defined. In fact,
the operator @{text"^*"} is not defined inductively but via a least
fixpoint because at that point in the theory hierarchy
inductive definitions are not yet available. But now they are:
*}

consts rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"  ("_*" [1000] 999)
inductive "r*"
intros
rtc_refl[intro!]:                        "(x,x) \<in> r*"
rtc_step: "\<lbrakk> (x,y) \<in> r*; (y,z) \<in> r \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

lemma [intro]: "(x,y) : r \<Longrightarrow> (x,y) \<in> r*"
by(blast intro: rtc_step);

lemma step2[rule_format]:
  "(y,z) \<in> r*  \<Longrightarrow> (x,y) \<in> r \<longrightarrow> (x,z) \<in> r*"
apply(erule rtc.induct)
 apply(blast);
apply(blast intro: rtc_step);
done

lemma rtc_trans[rule_format]:
  "(x,y) \<in> r*  \<Longrightarrow> \<forall>z. (y,z) \<in> r* \<longrightarrow> (x,z) \<in> r*"
apply(erule rtc.induct)
 apply blast;
apply(blast intro: step2);
done

consts rtc2 :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"
inductive "rtc2 r"
intros
"(x,y) \<in> r \<Longrightarrow> (x,y) \<in> rtc2 r"
"(x,x) \<in> rtc2 r"
"\<lbrakk> (x,y) \<in> rtc2 r; (y,z) \<in> rtc2 r \<rbrakk> \<Longrightarrow> (x,z) \<in> rtc2 r"

text{*
The equivalence of the two definitions is easily shown by the obvious rule
inductions:
*}

lemma "(x,y) \<in> rtc2 r \<Longrightarrow> (x,y) \<in> r*"
apply(erule rtc2.induct);
  apply(blast);
 apply(blast);
apply(blast intro: rtc_trans);
done

lemma "(x,y) \<in> r* \<Longrightarrow> (x,y) \<in> rtc2 r"
apply(erule rtc.induct);
 apply(blast intro: rtc2.intros);
apply(blast intro: rtc2.intros);
done

(*<*)end(*>*)
