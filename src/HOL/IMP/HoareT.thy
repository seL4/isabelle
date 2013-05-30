(* Author: Tobias Nipkow *)

theory HoareT imports Hoare_Sound_Complete begin

subsection "Hoare Logic for Total Correctness"

text{* Note that this definition of total validity @{text"\<Turnstile>\<^sub>t"} only
works if execution is deterministic (which it is in our case). *}

definition hoare_tvalid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q}  \<equiv>  \<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q t)"

text{* Provability of Hoare triples in the proof system for total
correctness is written @{text"\<turnstile>\<^sub>t {P}c{Q}"} and defined
inductively. The rules for @{text"\<turnstile>\<^sub>t"} differ from those for
@{text"\<turnstile>"} only in the one place where nontermination can arise: the
@{term While}-rule. *}

inductive
  hoaret :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip:  "\<turnstile>\<^sub>t {P} SKIP {P}" |
Assign:  "\<turnstile>\<^sub>t {\<lambda>s. P(s[a/x])} x::=a {P}" |
Seq: "\<lbrakk> \<turnstile>\<^sub>t {P\<^isub>1} c\<^isub>1 {P\<^isub>2}; \<turnstile>\<^sub>t {P\<^isub>2} c\<^isub>2 {P\<^isub>3} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^isub>1} c\<^isub>1;;c\<^isub>2 {P\<^isub>3}" |
If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s} c\<^isub>1 {Q}; \<turnstile>\<^sub>t {\<lambda>s. P s \<and> \<not> bval b s} c\<^isub>2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>t {P} IF b THEN c\<^isub>1 ELSE c\<^isub>2 {Q}" |
While:
  "\<lbrakk> \<And>n::nat. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> T n s} c {\<lambda>s. P s \<and> (\<exists>n'. T n' s \<and> n' < n)} \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> (\<exists>n. T n s)} WHILE b DO c {\<lambda>s. P s \<and> \<not>bval b s}" |
conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"

text{* The @{term While}-rule is like the one for partial correctness but it
requires additionally that with every execution of the loop body some measure
function @{term[source]"f :: state \<Rightarrow> nat"} decreases. *}

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile>\<^sub>t {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q}"
by (metis conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile>\<^sub>t {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile>\<^sub>t {P} c {Q'}"
by (metis conseq)

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile>\<^sub>t {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

lemma While':
assumes "\<And>n::nat. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> T n s} c {\<lambda>s. P s \<and> (\<exists>n'. T n' s \<and> n' < n)}"
    and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile>\<^sub>t {\<lambda>s. P s \<and> (\<exists>n. T n s)} WHILE b DO c {Q}"
by(blast intro: assms(1) weaken_post[OF While assms(2)])

lemma While_fun:
  "\<lbrakk> \<And>n::nat. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> f s = n} c {\<lambda>s. P s \<and> f s < n}\<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {P} WHILE b DO c {\<lambda>s. P s \<and> \<not>bval b s}"
  by (rule While [where T="\<lambda>n s. f s = n", simplified])

text{* Our standard example: *}

abbreviation "w n ==
  WHILE Less (V ''y'') (N n)
  DO ( ''y'' ::= Plus (V ''y'') (N 1);; ''x'' ::= Plus (V ''x'') (V ''y'') )"

lemma "\<turnstile>\<^sub>t {\<lambda>s. 0 \<le> n} ''x'' ::= N 0;; ''y'' ::= N 0;; w n {\<lambda>s. s ''x'' = \<Sum>{1..n}}"
apply(rule Seq)
prefer 2
apply(rule While'
  [where P = "\<lambda>s. s ''x'' = \<Sum> {1..s ''y''} \<and> 0 \<le> s ''y'' \<and> s ''y'' \<le> n"
   and T = "\<lambda>n' s. n' = nat (n - s ''y'')"])
apply(rule Seq)
prefer 2
apply(rule Assign)
apply(rule Assign')
apply (simp add: atLeastAtMostPlus1_int_conv algebra_simps)
apply clarsimp
apply(rule Seq)
prefer 2
apply(rule Assign)
apply(rule Assign')
apply simp
done


text{* The soundness theorem: *}

theorem hoaret_sound: "\<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"
proof(unfold hoare_tvalid_def, induct rule: hoaret.induct)
  case (While P b T c)
  {
    fix s n
    have "\<lbrakk> P s; T n s \<rbrakk> \<Longrightarrow> \<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P t \<and> \<not> bval b t"
    proof(induction "n" arbitrary: s rule: less_induct)
      case (less n)
      thus ?case by (metis While(2) WhileFalse WhileTrue)
    qed
  }
  thus ?case by auto
next
  case If thus ?case by auto blast
qed fastforce+


text{*
The completeness proof proceeds along the same lines as the one for partial
correctness. First we have to strengthen our notion of weakest precondition
to take termination into account: *}

definition wpt :: "com \<Rightarrow> assn \<Rightarrow> assn" ("wp\<^sub>t") where
"wp\<^sub>t c Q  \<equiv>  \<lambda>s. \<exists>t. (c,s) \<Rightarrow> t \<and> Q t"

lemma [simp]: "wp\<^sub>t SKIP Q = Q"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (x ::= e) Q = (\<lambda>s. Q(s(x := aval e s)))"
by(auto intro!: ext simp: wpt_def)

lemma [simp]: "wp\<^sub>t (c\<^isub>1;;c\<^isub>2) Q = wp\<^sub>t c\<^isub>1 (wp\<^sub>t c\<^isub>2 Q)"
unfolding wpt_def
apply(rule ext)
apply auto
done

lemma [simp]:
 "wp\<^sub>t (IF b THEN c\<^isub>1 ELSE c\<^isub>2) Q = (\<lambda>s. wp\<^sub>t (if bval b s then c\<^isub>1 else c\<^isub>2) Q s)"
apply(unfold wpt_def)
apply(rule ext)
apply auto
done


text{* Now we define the number of iterations @{term "WHILE b DO c"} needs to
terminate when started in state @{text s}. Because this is a truly partial
function, we define it as an (inductive) relation first: *}

inductive Its :: "bexp \<Rightarrow> com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool" where
Its_0: "\<not> bval b s \<Longrightarrow> Its b c s 0" |
Its_Suc: "\<lbrakk> bval b s;  (c,s) \<Rightarrow> s';  Its b c s' n \<rbrakk> \<Longrightarrow> Its b c s (Suc n)"

text{* The relation is in fact a function: *}

lemma Its_fun: "Its b c s n \<Longrightarrow> Its b c s n' \<Longrightarrow> n=n'"
proof(induction arbitrary: n' rule:Its.induct)
  case Its_0 thus ?case by(metis Its.cases)
next
  case Its_Suc thus ?case by(metis Its.cases big_step_determ)
qed

text{* For all terminating loops, @{const Its} yields a result: *}

lemma WHILE_Its: "(WHILE b DO c,s) \<Rightarrow> t \<Longrightarrow> \<exists>n. Its b c s n"
proof(induction "WHILE b DO c" s t rule: big_step_induct)
  case WhileFalse thus ?case by (metis Its_0)
next
  case WhileTrue thus ?case by (metis Its_Suc)
qed

lemma wpt_is_pre: "\<turnstile>\<^sub>t {wp\<^sub>t c Q} c {Q}"
proof (induction c arbitrary: Q)
  case SKIP show ?case by simp (blast intro:hoaret.Skip)
next
  case Assign show ?case by simp (blast intro:hoaret.Assign)
next
  case Seq thus ?case by simp (blast intro:hoaret.Seq)
next
  case If thus ?case by simp (blast intro:hoaret.If hoaret.conseq)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  let ?T = "\<lambda>n s. Its b c s n"
  have "\<forall>s. wp\<^sub>t (WHILE b DO c) Q s \<longrightarrow> wp\<^sub>t (WHILE b DO c) Q s \<and> (\<exists>n. Its b c s n)"
    unfolding wpt_def by (metis WHILE_Its)
  moreover
  { fix n
    { fix s t
      assume "bval b s" "?T n s" "(?w, s) \<Rightarrow> t" "Q t"
      from `bval b s` `(?w, s) \<Rightarrow> t` obtain s' where
        "(c,s) \<Rightarrow> s'" "(?w,s') \<Rightarrow> t" by auto      
      from `(?w, s') \<Rightarrow> t` obtain n'' where "?T n'' s'" by (blast dest: WHILE_Its)
      with `bval b s` `(c, s) \<Rightarrow> s'`
      have "?T (Suc n'') s" by (rule Its_Suc)
      with `?T n s` have "n = Suc n''" by (rule Its_fun)
      with `(c,s) \<Rightarrow> s'` `(?w,s') \<Rightarrow> t` `Q t` `?T n'' s'`
      have "wp\<^sub>t c (\<lambda>s'. wp\<^sub>t ?w Q s' \<and> (\<exists>n'. ?T n' s' \<and> n' < n)) s"
        by (auto simp: wpt_def)
    } 
    hence "\<forall>s. wp\<^sub>t ?w Q s \<and> bval b s \<and> ?T n s \<longrightarrow>
              wp\<^sub>t c (\<lambda>s'. wp\<^sub>t ?w Q s' \<and> (\<exists>n'. ?T n' s' \<and> n' < n)) s"
      unfolding wpt_def by auto
      (* by (metis WhileE Its_Suc Its_fun WHILE_Its lessI) *) 
    note strengthen_pre[OF this While]
  } note hoaret.While[OF this]
  moreover have "\<forall>s. wp\<^sub>t ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" by (auto simp add:wpt_def)
  ultimately show ?case by (rule conseq) 
qed


text{*\noindent In the @{term While}-case, @{const Its} provides the obvious
termination argument.

The actual completeness theorem follows directly, in the same manner
as for partial correctness: *}

theorem hoaret_complete: "\<Turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>t {P}c{Q}"
apply(rule strengthen_pre[OF _ wpt_is_pre])
apply(auto simp: hoare_tvalid_def hoare_valid_def wpt_def)
done

end
