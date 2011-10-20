(* Author: Tobias Nipkow *)

header "Hoare Logic"

theory Hoare imports Big_Step begin

subsection "Hoare Logic for Partial Correctness"

type_synonym assn = "state \<Rightarrow> bool"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip: "\<turnstile> {P} SKIP {P}"  |

Assign:  "\<turnstile> {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Semi: "\<lbrakk> \<turnstile> {P} c\<^isub>1 {Q};  \<turnstile> {Q} c\<^isub>2 {R} \<rbrakk>
       \<Longrightarrow> \<turnstile> {P} c\<^isub>1;c\<^isub>2 {R}"  |

If: "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^isub>1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^isub>2 {Q} \<rbrakk>
     \<Longrightarrow> \<turnstile> {P} IF b THEN c\<^isub>1 ELSE c\<^isub>2 {Q}"  |

While: "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow>
        \<turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> {P'} c {Q'}"

lemmas [simp] = hoare.Skip hoare.Assign hoare.Semi If

lemmas [intro!] = hoare.Skip hoare.Assign hoare.Semi hoare.If

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P'} c {Q}"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> {P} c {Q'}"
by (blast intro: conseq)

text{* The assignment and While rule are awkward to use in actual proofs
because their pre and postcondition are of a very special form and the actual
goal would have to match this form exactly. Therefore we derive two variants
with arbitrary pre and postconditions. *}

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile> {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

lemma While':
assumes "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P}" and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile> {P} WHILE b DO c {Q}"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])

end
