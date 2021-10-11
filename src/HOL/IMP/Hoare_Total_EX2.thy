(* Author: Tobias Nipkow *)

subsubsection "Hoare Logic for Total Correctness With Logical Variables"

theory Hoare_Total_EX2
imports Hoare
begin

text\<open>This is the standard set of rules that you find in many publications.
In the while-rule, a logical variable is needed to remember the pre-value
of the variant (an expression that decreases by one with each iteration).
In this theory, logical variables are modeled explicitly.
A simpler (but not quite as flexible) approach is found in theory \<open>Hoare_Total_EX\<close>:
pre and post-condition are connected via a universally quantified HOL variable.\<close>

type_synonym lvname = string
type_synonym assn2 = "(lvname \<Rightarrow> nat) \<Rightarrow> state \<Rightarrow> bool"

definition hoare_tvalid :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q}  \<longleftrightarrow>  (\<forall>l s. P l s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q l t))"

inductive
  hoaret :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>t {P} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>t {\<lambda>l s. P l (s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1 {P\<^sub>2}; \<turnstile>\<^sub>t {P\<^sub>2} c\<^sub>2 {P\<^sub>3} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}" |

If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>l s. P l s \<and> bval b s} c\<^sub>1 {Q}; \<turnstile>\<^sub>t {\<lambda>l s. P l s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>t {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}" |

While:
  "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>l. P (l(x := Suc(l(x))))} c {P};
     \<forall>l s. l x > 0 \<and> P l s \<longrightarrow> bval b s;
     \<forall>l s. l x = 0 \<and> P l s \<longrightarrow> \<not> bval b s \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>l s. \<exists>n. P (l(x:=n)) s} WHILE b DO c {\<lambda>l s. P (l(x := 0)) s}" |

conseq: "\<lbrakk> \<forall>l s. P' l s \<longrightarrow> P l s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>l s. Q l s \<longrightarrow> Q' l s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"

text\<open>Building in the consequence rule:\<close>

lemma strengthen_pre:
  "\<lbrakk> \<forall>l s. P' l s \<longrightarrow> P l s;  \<turnstile>\<^sub>t {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q}"
by (metis conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile>\<^sub>t {P} c {Q};  \<forall>l s. Q l s \<longrightarrow> Q' l s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>t {P} c {Q'}"
by (metis conseq)

lemma Assign': "\<forall>l s. P l s \<longrightarrow> Q l (s[a/x]) \<Longrightarrow> \<turnstile>\<^sub>t {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

text\<open>The soundness theorem:\<close>

theorem hoaret_sound: "\<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"
proof(unfold hoare_tvalid_def, induction rule: hoaret.induct)
  case (While P x c b)
  have "\<lbrakk> l x = n; P l s \<rbrakk> \<Longrightarrow> \<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P (l(x := 0)) t" for n l s
  proof(induction "n" arbitrary: l s)
    case 0 thus ?case using While.hyps(3) WhileFalse
      by (metis fun_upd_triv)
  next
    case Suc
    thus ?case using While.IH While.hyps(2) WhileTrue
      by (metis fun_upd_same fun_upd_triv fun_upd_upd zero_less_Suc)
  qed
  thus ?case by fastforce
next
  case If thus ?case by auto blast
qed fastforce+


definition wpt :: "com \<Rightarrow> assn2 \<Rightarrow> assn2" ("wp\<^sub>t") where
"wp\<^sub>t c Q  =  (\<lambda>l s. \<exists>t. (c,s) \<Rightarrow> t \<and> Q l t)"

lemma [simp]: "wp\<^sub>t SKIP Q = Q"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (x ::= e) Q = (\<lambda>l s. Q l (s(x := aval e s)))"
by(auto intro!: ext simp: wpt_def)

lemma wpt_Seq[simp]: "wp\<^sub>t (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>t c\<^sub>1 (wp\<^sub>t c\<^sub>2 Q)"
by (auto simp: wpt_def fun_eq_iff)

lemma [simp]:
 "wp\<^sub>t (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>l s. wp\<^sub>t (if bval b s then c\<^sub>1 else c\<^sub>2) Q l s)"
by (auto simp: wpt_def fun_eq_iff)


text\<open>Function \<open>wpw\<close> computes the weakest precondition of a While-loop
that is unfolded a fixed number of times.\<close>

fun wpw :: "bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> assn2 \<Rightarrow> assn2" where
"wpw b c 0 Q l s = (\<not> bval b s \<and> Q l s)" |
"wpw b c (Suc n) Q l s = (bval b s \<and> (\<exists>s'. (c,s) \<Rightarrow> s' \<and>  wpw b c n Q l s'))"

lemma WHILE_Its:
  "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> Q l t \<Longrightarrow> \<exists>n. wpw b c n Q l s"
proof(induction "WHILE b DO c" s t arbitrary: l rule: big_step_induct)
  case WhileFalse thus ?case using wpw.simps(1) by blast
next
  case WhileTrue show ?case
    using wpw.simps(2) WhileTrue(1,2) WhileTrue(5)[OF WhileTrue(6)] by blast
qed

definition support :: "assn2 \<Rightarrow> string set" where
"support P = {x. \<exists>l1 l2 s. (\<forall>y. y \<noteq> x \<longrightarrow> l1 y = l2 y) \<and> P l1 s \<noteq> P l2 s}"

lemma support_wpt: "support (wp\<^sub>t c Q) \<subseteq> support Q"
by(simp add: support_def wpt_def) blast


lemma support_wpw0: "support (wpw b c n Q) \<subseteq> support Q"
proof(induction n)
  case 0 show ?case by (simp add: support_def) blast
next
  case Suc
  have 1: "support (\<lambda>l s. A s \<and> B l s) \<subseteq> support B" for A B
    by(auto simp: support_def)
  have 2: "support (\<lambda>l s. \<exists>s'. A s s' \<and> B l s') \<subseteq> support B" for A B
    by(auto simp: support_def) blast+
  from Suc 1 2 show ?case by simp (meson order_trans)
qed

lemma support_wpw_Un:
  "support (%l. wpw b c (l x) Q l) \<subseteq> insert x (UN n. support(wpw b c n Q))"
using support_wpw0[of b c _ Q]
apply(auto simp add: support_def subset_iff)
apply metis
apply metis
done

lemma support_wpw: "support (%l. wpw b c (l x) Q l) \<subseteq> insert x (support Q)"
using support_wpw0[of b c _ Q] support_wpw_Un[of b c _ Q]
by blast

lemma assn2_lupd: "x \<notin> support Q \<Longrightarrow> Q (l(x:=n)) = Q l"
by(simp add: support_def fun_upd_other fun_eq_iff)
  (metis (no_types, lifting) fun_upd_def)

abbreviation "new Q \<equiv> SOME x. x \<notin> support Q"

lemma wpw_lupd: "x \<notin> support Q \<Longrightarrow> wpw b c n Q (l(x := u)) = wpw b c n Q l"
by(induction n) (auto simp: assn2_lupd fun_eq_iff)

lemma wpt_is_pre: "finite(support Q) \<Longrightarrow> \<turnstile>\<^sub>t {wp\<^sub>t c Q} c {Q}"
proof (induction c arbitrary: Q)
  case SKIP show ?case by (auto intro:hoaret.Skip)
next
  case Assign show ?case by (auto intro:hoaret.Assign)
next
  case (Seq c1 c2) show ?case
    by (auto intro:hoaret.Seq Seq finite_subset[OF support_wpt])
next
  case If thus ?case by (auto intro:hoaret.If hoaret.conseq)
next
  case (While b c)
  let ?x = "new Q"
  have "\<exists>x. x \<notin> support Q" using While.prems infinite_UNIV_listI
    using ex_new_if_finite by blast
  hence [simp]: "?x \<notin> support Q" by (rule someI_ex)
  let ?w = "WHILE b DO c"
  have fsup: "finite (support (\<lambda>l. wpw b c (l x) Q l))" for x
    using finite_subset[OF support_wpw] While.prems by simp
  have c1: "\<forall>l s. wp\<^sub>t ?w Q l s \<longrightarrow> (\<exists>n. wpw b c n Q l s)"
    unfolding wpt_def by (metis WHILE_Its)
  have c2: "\<forall>l s. l ?x = 0 \<and> wpw b c (l ?x) Q l s \<longrightarrow> \<not> bval b s"
    by (simp cong: conj_cong)
  have w2: "\<forall>l s. 0 < l ?x \<and> wpw b c (l ?x) Q l s \<longrightarrow> bval b s"
    by (auto simp: gr0_conv_Suc cong: conj_cong)
  have 1: "\<forall>l s. wpw b c (Suc(l ?x)) Q l s \<longrightarrow>
                  (\<exists>t. (c, s) \<Rightarrow> t \<and> wpw b c (l ?x) Q l t)"
    by simp
  have *: "\<turnstile>\<^sub>t {\<lambda>l. wpw b c (Suc (l ?x)) Q l} c {\<lambda>l. wpw b c (l ?x) Q l}"
    by(rule strengthen_pre[OF 1
          While.IH[of "\<lambda>l. wpw b c (l ?x) Q l", unfolded wpt_def, OF fsup]])
  show ?case
  apply(rule conseq[OF _ hoaret.While[OF _ w2 c2]])
    apply (simp_all add: c1 * assn2_lupd wpw_lupd del: wpw.simps(2))
  done
qed

theorem hoaret_complete: "finite(support Q) \<Longrightarrow> \<Turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>t {P}c{Q}"
apply(rule strengthen_pre[OF _ wpt_is_pre])
apply(auto simp: hoare_tvalid_def wpt_def)
done


text \<open>Two examples:\<close>

lemma "\<turnstile>\<^sub>t 
{\<lambda>l s. l ''x'' = nat(s ''x'')}
 WHILE Less (N 0) (V ''x'') DO ''x'' ::= Plus (V ''x'') (N (-1))
{\<lambda>l s. s ''x'' \<le> 0}"
apply(rule conseq)
prefer 2
 apply(rule While[where P = "\<lambda>l s. l ''x'' = nat(s ''x'')" and x = "''x''"])
   apply(rule Assign')
   apply auto
done

lemma "\<turnstile>\<^sub>t 
{\<lambda>l s. l ''x'' = nat(s ''x'')}
 WHILE Less (N 0) (V ''x'')
 DO (''x'' ::= Plus (V ''x'') (N (-1));;
    (''y'' ::= V ''x'';;
     WHILE Less (N 0) (V ''y'') DO ''y'' ::= Plus (V ''y'') (N (-1))))
{\<lambda>l s. s ''x'' \<le> 0}"
apply(rule conseq)
prefer 2
 apply(rule While[where P = "\<lambda>l s. l ''x'' = nat(s ''x'')" and x = "''x''"])
   defer
   apply auto
apply(rule Seq)
 prefer 2
 apply(rule Seq)
  prefer 2
  apply(rule weaken_post)
   apply(rule_tac P = "\<lambda>l s. l ''x'' = nat(s ''x'') \<and> l ''y'' = nat(s ''y'')" and x = "''y''" in While)
     apply(rule Assign')
     apply auto[4]
 apply(rule Assign)
apply(rule Assign')
apply auto
done

end
