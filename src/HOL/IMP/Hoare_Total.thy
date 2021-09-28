(* Author: Tobias Nipkow *)

subsection "Hoare Logic for Total Correctness"

subsubsection "Separate Termination Relation"

theory Hoare_Total
imports Hoare_Examples
begin

text\<open>Note that this definition of total validity \<open>\<Turnstile>\<^sub>t\<close> only
works if execution is deterministic (which it is in our case).\<close>

definition hoare_tvalid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q}  \<longleftrightarrow>  (\<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q t))"

text\<open>Provability of Hoare triples in the proof system for total
correctness is written \<open>\<turnstile>\<^sub>t {P}c{Q}\<close> and defined
inductively. The rules for \<open>\<turnstile>\<^sub>t\<close> differ from those for
\<open>\<turnstile>\<close> only in the one place where nontermination can arise: the
\<^term>\<open>While\<close>-rule.\<close>

inductive
  hoaret :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>t {P} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>t {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1 {P\<^sub>2}; \<turnstile>\<^sub>t {P\<^sub>2} c\<^sub>2 {P\<^sub>3} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |

If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q}; \<turnstile>\<^sub>t {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>t {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |

While:
  "(\<And>n::nat.
    \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> T s n} c {\<lambda>s. P s \<and> (\<exists>n'<n. T s n')})
   \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> (\<exists>n. T s n)} WHILE b DO c {\<lambda>s. P s \<and> \<not>bval b s}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"

text\<open>The \<^term>\<open>While\<close>-rule is like the one for partial correctness but it
requires additionally that with every execution of the loop body some measure
relation @{term[source]"T :: state \<Rightarrow> nat \<Rightarrow> bool"} decreases.
The following functional version is more intuitive:\<close>

lemma While_fun:
  "\<lbrakk> \<And>n::nat. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> n = f s} c {\<lambda>s. P s \<and> f s < n}\<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {P} WHILE b DO c {\<lambda>s. P s \<and> \<not>bval b s}"
  by (rule While [where T="\<lambda>s n. n = f s", simplified])

text\<open>Building in the consequence rule:\<close>

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile>\<^sub>t {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q}"
by (metis conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile>\<^sub>t {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>t {P} c {Q'}"
by (metis conseq)

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile>\<^sub>t {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

lemma While_fun':
assumes "\<And>n::nat. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> n = f s} c {\<lambda>s. P s \<and> f s < n}"
    and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile>\<^sub>t {P} WHILE b DO c {Q}"
by(blast intro: assms(1) weaken_post[OF While_fun assms(2)])


text\<open>Our standard example:\<close>

lemma "\<turnstile>\<^sub>t {\<lambda>s. s ''x'' = i} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum i}"
apply(rule Seq)
 prefer 2
 apply(rule While_fun' [where P = "\<lambda>s. (s ''y'' = sum i - sum(s ''x''))"
    and f = "\<lambda>s. nat(s ''x'')"])
   apply(rule Seq)
   prefer 2
   apply(rule Assign)
  apply(rule Assign')
  apply simp
 apply(simp)
apply(rule Assign')
apply simp
done

text \<open>Nested loops. This poses a problem for VCGs because the proof of the inner loop needs to
refer to outer loops. This works here because the invariant is not written down statically but
created in the context of a proof that has already introduced/fixed outer \<open>n\<close>s that can be
referred to.\<close>

lemma
 "\<turnstile>\<^sub>t {\<lambda>_. True}
  WHILE Less (N 0) (V ''x'')
  DO (''x'' ::= Plus (V ''x'') (N(-1));;
      ''y'' ::= V ''x'';;
      WHILE Less (N 0) (V ''y'') DO ''y'' ::= Plus (V ''y'') (N(-1)))
  {\<lambda>_. True}"
apply(rule While_fun'[where f = "\<lambda>s. nat(s ''x'')"])
 prefer 2 apply simp
apply(rule_tac P\<^sub>2 = "\<lambda>s. nat(s ''x'') < n" in Seq)
 apply(rule_tac P\<^sub>2 = "\<lambda>s. nat(s ''x'') < n" in Seq)
  apply(rule Assign')
  apply simp
 apply(rule Assign')
 apply simp
(* note that the invariant refers to the outer \<open>n\<close>: *)
apply(rule While_fun'[where f = "\<lambda>s. nat(s ''y'')"])
 prefer 2 apply simp
apply(rule Assign')
apply simp
done

text\<open>The soundness theorem:\<close>

theorem hoaret_sound: "\<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"
proof(unfold hoare_tvalid_def, induction rule: hoaret.induct)
  case (While P b T c)
  have "\<lbrakk> P s; T s n \<rbrakk> \<Longrightarrow> \<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P t \<and> \<not> bval b t" for s n
  proof(induction "n" arbitrary: s rule: less_induct)
    case (less n) thus ?case by (metis While.IH WhileFalse WhileTrue)
  qed
  thus ?case by auto
next
  case If thus ?case by auto blast
qed fastforce+


text\<open>
The completeness proof proceeds along the same lines as the one for partial
correctness. First we have to strengthen our notion of weakest precondition
to take termination into account:\<close>

definition wpt :: "com \<Rightarrow> assn \<Rightarrow> assn" ("wp\<^sub>t") where
"wp\<^sub>t c Q  =  (\<lambda>s. \<exists>t. (c,s) \<Rightarrow> t \<and> Q t)"

lemma [simp]: "wp\<^sub>t SKIP Q = Q"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (x ::= e) Q = (\<lambda>s. Q(s(x := aval e s)))"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>t c\<^sub>1 (wp\<^sub>t c\<^sub>2 Q)"
unfolding wpt_def
apply(rule ext)
apply auto
done

lemma [simp]:
 "wp\<^sub>t (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. wp\<^sub>t (if bval b s then c\<^sub>1 else c\<^sub>2) Q s)"
apply(unfold wpt_def)
apply(rule ext)
apply auto
done


text\<open>Now we define the number of iterations \<^term>\<open>WHILE b DO c\<close> needs to
terminate when started in state \<open>s\<close>. Because this is a truly partial
function, we define it as an (inductive) relation first:\<close>

inductive Its :: "bexp \<Rightarrow> com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool" where
Its_0: "\<not> bval b s \<Longrightarrow> Its b c s 0" |
Its_Suc: "\<lbrakk> bval b s;  (c,s) \<Rightarrow> s';  Its b c s' n \<rbrakk> \<Longrightarrow> Its b c s (Suc n)"

text\<open>The relation is in fact a function:\<close>

lemma Its_fun: "Its b c s n \<Longrightarrow> Its b c s n' \<Longrightarrow> n=n'"
proof(induction arbitrary: n' rule:Its.induct)
  case Its_0 thus ?case by(metis Its.cases)
next
  case Its_Suc thus ?case by(metis Its.cases big_step_determ)
qed

text\<open>For all terminating loops, \<^const>\<open>Its\<close> yields a result:\<close>

lemma WHILE_Its: "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> \<exists>n. Its b c s n"
proof(induction "WHILE b DO c" s t rule: big_step_induct)
  case WhileFalse thus ?case by (metis Its_0)
next
  case WhileTrue thus ?case by (metis Its_Suc)
qed

lemma wpt_is_pre: "\<turnstile>\<^sub>t {wp\<^sub>t c Q} c {Q}"
proof (induction c arbitrary: Q)
  case SKIP show ?case by (auto intro:hoaret.Skip)
next
  case Assign show ?case by (auto intro:hoaret.Assign)
next
  case Seq thus ?case by (auto intro:hoaret.Seq)
next
  case If thus ?case by (auto intro:hoaret.If hoaret.conseq)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  let ?T = "Its b c"
  have 1: "\<forall>s. wp\<^sub>t ?w Q s \<longrightarrow> wp\<^sub>t ?w Q s \<and> (\<exists>n. Its b c s n)"
    unfolding wpt_def by (metis WHILE_Its)
  let ?R = "\<lambda>n s'. wp\<^sub>t ?w Q s' \<and> (\<exists>n'<n. ?T s' n')"
  have "\<forall>s. wp\<^sub>t ?w Q s \<and> bval b s \<and> ?T s n \<longrightarrow> wp\<^sub>t c (?R n) s" for n
  proof -
    have "wp\<^sub>t c (?R n) s" if "bval b s" and "?T s n" and "(?w, s) \<Rightarrow> t" and "Q t" for s t
    proof -
      from \<open>bval b s\<close> and \<open>(?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c,s) \<Rightarrow> s'" "(?w,s') \<Rightarrow> t" by auto
      from \<open>(?w, s') \<Rightarrow> t\<close> obtain n' where "?T s' n'"
        by (blast dest: WHILE_Its)
      with \<open>bval b s\<close> and \<open>(c, s) \<Rightarrow> s'\<close> have "?T s (Suc n')" by (rule Its_Suc)
      with \<open>?T s n\<close> have "n = Suc n'" by (rule Its_fun)
      with \<open>(c,s) \<Rightarrow> s'\<close> and \<open>(?w,s') \<Rightarrow> t\<close> and \<open>Q t\<close> and \<open>?T s' n'\<close>
      show ?thesis by (auto simp: wpt_def)
    qed
    thus ?thesis
      unfolding wpt_def by auto
      (* by (metis WhileE Its_Suc Its_fun WHILE_Its lessI) *) 
  qed
  note 2 = hoaret.While[OF strengthen_pre[OF this While.IH]]
  have "\<forall>s. wp\<^sub>t ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s"
    by (auto simp add:wpt_def)
  with 1 2 show ?case by (rule conseq)
qed


text\<open>\noindent In the \<^term>\<open>While\<close>-case, \<^const>\<open>Its\<close> provides the obvious
termination argument.

The actual completeness theorem follows directly, in the same manner
as for partial correctness:\<close>

theorem hoaret_complete: "\<Turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>t {P}c{Q}"
apply(rule strengthen_pre[OF _ wpt_is_pre])
apply(auto simp: hoare_tvalid_def wpt_def)
done

corollary hoaret_sound_complete: "\<turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> \<Turnstile>\<^sub>t {P}c{Q}"
by (metis hoaret_sound hoaret_complete)

end
