(*<*)theory Star = Main:(*>*)

section{*The transitive and reflexive closure*}

text{*
A perfect example of an inductive definition is the transitive, reflexive
closure of a relation. This concept was already introduced in
\S\ref{sec:rtrancl}, but it was not shown how it is defined. In fact,
the operator @{text"^*"} is not defined inductively but via a least
fixpoint because at that point in the theory hierarchy
inductive definitions are not yet available. But now they are:
*}

consts trc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"  ("_*" [1000] 999)
inductive "r*"
intros
trc_refl[intro!]:                        "(x,x) \<in> r*"
trc_step: "\<lbrakk> (x,y) \<in> r*; (y,z) \<in> r \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

lemma [intro]: "(x,y) : r \<Longrightarrow> (x,y) \<in> r*"
by(blast intro: trc_step);

lemma step2[rule_format]:
  "(y,z) \<in> r*  \<Longrightarrow> (x,y) \<in> r \<longrightarrow> (x,z) \<in> r*"
apply(erule trc.induct)
 apply(blast);
apply(blast intro: trc_step);
done

lemma trc_trans[rule_format]:
  "(x,y) \<in> r*  \<Longrightarrow> \<forall>z. (y,z) \<in> r* \<longrightarrow> (x,z) \<in> r*"
apply(erule trc.induct)
 apply blast;
apply(blast intro: step2);
done

consts trc2 :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"
inductive "trc2 r"
intros
"(x,y) \<in> r \<Longrightarrow> (x,y) \<in> trc2 r"
"(x,x) \<in> trc2 r"
"\<lbrakk> (x,y) \<in> trc2 r; (y,z) \<in> trc2 r \<rbrakk> \<Longrightarrow> (x,z) \<in> trc2 r"


lemma "((x,y) \<in> trc2 r) = ((x,y) \<in> r*)"
apply(rule iffI);
 apply(erule trc2.induct);
   apply(blast);
  apply(blast);
 apply(blast intro: trc_trans);
apply(erule trc.induct);
 apply(blast intro: trc2.intros);
apply(blast intro: trc2.intros);
done

(*<*)end(*>*)
