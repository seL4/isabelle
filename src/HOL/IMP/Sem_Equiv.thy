header "Semantic Equivalence up to a Condition"

theory Sem_Equiv
imports Hoare_Sound_Complete
begin

definition
  equiv_up_to :: "assn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> bool" ("_ \<Turnstile> _ \<sim> _" [60,0,10] 60)
where
  "P \<Turnstile> c \<sim> c' \<equiv> \<forall>s s'. P s \<longrightarrow> (c,s) \<Rightarrow> s' \<longleftrightarrow> (c',s) \<Rightarrow> s'"

definition 
  bequiv_up_to :: "assn \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bool" ("_ \<Turnstile> _ <\<sim>> _" [60,0,10] 60)
where 
  "P \<Turnstile> b <\<sim>> b' \<equiv> \<forall>s. P s \<longrightarrow> bval b s = bval b' s"

lemma equiv_up_to_True:
  "((\<lambda>_. True) \<Turnstile> c \<sim> c') = (c \<sim> c')"
  by (simp add: equiv_def equiv_up_to_def)

lemma equiv_up_to_weaken:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (\<And>s. P' s \<Longrightarrow> P s) \<Longrightarrow> P' \<Turnstile> c \<sim> c'"
  by (simp add: equiv_up_to_def)

lemma equiv_up_toI:
  "(\<And>s s'. P s \<Longrightarrow> (c, s) \<Rightarrow> s' = (c', s) \<Rightarrow> s') \<Longrightarrow> P \<Turnstile> c \<sim> c'"
  by (unfold equiv_up_to_def) blast

lemma equiv_up_toD1:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> P s \<Longrightarrow> (c, s) \<Rightarrow> s' \<Longrightarrow> (c', s) \<Rightarrow> s'"
  by (unfold equiv_up_to_def) blast

lemma equiv_up_toD2:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> P s \<Longrightarrow> (c', s) \<Rightarrow> s' \<Longrightarrow> (c, s) \<Rightarrow> s'"
  by (unfold equiv_up_to_def) blast


lemma equiv_up_to_refl [simp, intro!]:
  "P \<Turnstile> c \<sim> c"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_sym:
  "(P \<Turnstile> c \<sim> c') = (P \<Turnstile> c' \<sim> c)"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_trans [trans]:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> P \<Turnstile> c' \<sim> c'' \<Longrightarrow> P \<Turnstile> c \<sim> c''"
  by (auto simp: equiv_up_to_def)


lemma bequiv_up_to_refl [simp, intro!]:
  "P \<Turnstile> b <\<sim>> b"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_sym:
  "(P \<Turnstile> b <\<sim>> b') = (P \<Turnstile> b' <\<sim>> b)"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_trans [trans]:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> b' <\<sim>> b'' \<Longrightarrow> P \<Turnstile> b <\<sim>> b''"
  by (auto simp: bequiv_up_to_def)


lemma equiv_up_to_hoare:
  "P' \<Turnstile> c \<sim> c' \<Longrightarrow> (\<And>s. P s \<Longrightarrow> P' s) \<Longrightarrow> (\<Turnstile> {P} c {Q}) = (\<Turnstile> {P} c' {Q})"
  unfolding hoare_valid_def equiv_up_to_def by blast

lemma equiv_up_to_hoare_eq:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (\<Turnstile> {P} c {Q}) = (\<Turnstile> {P} c' {Q})"
  by (rule equiv_up_to_hoare)


lemma equiv_up_to_semi:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> Q \<Turnstile> d \<sim> d' \<Longrightarrow> \<Turnstile> {P} c {Q} \<Longrightarrow>
  P \<Turnstile> (c; d) \<sim> (c'; d')"
  by (clarsimp simp: equiv_up_to_def hoare_valid_def) blast

lemma equiv_up_to_while_lemma:
  shows "(d,s) \<Rightarrow> s' \<Longrightarrow> 
         P \<Turnstile> b <\<sim>> b' \<Longrightarrow>
         (\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c' \<Longrightarrow> 
         \<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow> 
         P s \<Longrightarrow> 
         d = WHILE b DO c \<Longrightarrow> 
         (WHILE b' DO c', s) \<Rightarrow> s'"  
proof (induction rule: big_step_induct)
  case (WhileTrue b s1 c s2 s3)
  note IH = WhileTrue.IH(2) [OF WhileTrue.prems(1-3) _ WhileTrue.prems(5)]
  from WhileTrue.prems
  have "P \<Turnstile> b <\<sim>> b'" by simp
  with `bval b s1` `P s1`
  have "bval b' s1" by (simp add: bequiv_up_to_def)
  moreover
  from WhileTrue.prems
  have "(\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c'" by simp
  with `bval b s1` `P s1` `(c, s1) \<Rightarrow> s2`
  have "(c', s1) \<Rightarrow> s2" by (simp add: equiv_up_to_def)
  moreover
  from WhileTrue.prems
  have "\<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P}" by simp
  with `P s1` `bval b s1` `(c, s1) \<Rightarrow> s2`
  have "P s2" by (simp add: hoare_valid_def)
  hence "(WHILE b' DO c', s2) \<Rightarrow> s3" by (rule IH)
  ultimately 
  show ?case by blast
next
  case WhileFalse
  thus ?case by (auto simp: bequiv_up_to_def)
qed (fastforce simp: equiv_up_to_def bequiv_up_to_def hoare_valid_def)+

lemma bequiv_context_subst:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> (P s \<and> bval b s) = (P s \<and> bval b' s)"
  by (auto simp: bequiv_up_to_def)

lemma equiv_up_to_while:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> (\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c' \<Longrightarrow> 
   \<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow> 
   P \<Turnstile> WHILE b DO c \<sim> WHILE b' DO c'"
  apply (safe intro!: equiv_up_toI)
   apply (auto intro: equiv_up_to_while_lemma)[1]
  apply (simp add: equiv_up_to_hoare_eq bequiv_context_subst)
  apply (drule equiv_up_to_sym [THEN iffD1])
  apply (drule bequiv_up_to_sym [THEN iffD1])
  apply (auto intro: equiv_up_to_while_lemma)[1]
  done

lemma equiv_up_to_while_weak:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> c \<sim> c' \<Longrightarrow> \<Turnstile> {P} c {P} \<Longrightarrow> 
   P \<Turnstile> WHILE b DO c \<sim> WHILE b' DO c'"
  by (fastforce elim!: equiv_up_to_while equiv_up_to_weaken 
               simp: hoare_valid_def)

lemma equiv_up_to_if:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> (\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c' \<Longrightarrow> (\<lambda>s. P s \<and> \<not>bval b s) \<Turnstile> d \<sim> d' \<Longrightarrow>
   P \<Turnstile> IF b THEN c ELSE d \<sim> IF b' THEN c' ELSE d'"
  by (auto simp: bequiv_up_to_def equiv_up_to_def)

lemma equiv_up_to_if_weak:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> c \<sim> c' \<Longrightarrow> P \<Turnstile> d \<sim> d' \<Longrightarrow>
   P \<Turnstile> IF b THEN c ELSE d \<sim> IF b' THEN c' ELSE d'"
  by (fastforce elim!: equiv_up_to_if equiv_up_to_weaken)

lemma equiv_up_to_if_True [intro!]:
  "(\<And>s. P s \<Longrightarrow> bval b s) \<Longrightarrow> P \<Turnstile> IF b THEN c1 ELSE c2 \<sim> c1"
  by (auto simp: equiv_up_to_def) 

lemma equiv_up_to_if_False [intro!]:
  "(\<And>s. P s \<Longrightarrow> \<not> bval b s) \<Longrightarrow> P \<Turnstile> IF b THEN c1 ELSE c2 \<sim> c2"
  by (auto simp: equiv_up_to_def)

lemma equiv_up_to_while_False [intro!]:
  "(\<And>s. P s \<Longrightarrow> \<not> bval b s) \<Longrightarrow> P \<Turnstile> WHILE b DO c \<sim> SKIP"
  by (auto simp: equiv_up_to_def)

lemma while_never: "(c, s) \<Rightarrow> u \<Longrightarrow> c \<noteq> WHILE (Bc True) DO c'"
 by (induct rule: big_step_induct) auto
  
lemma equiv_up_to_while_True [intro!,simp]:
  "P \<Turnstile> WHILE Bc True DO c \<sim> WHILE Bc True DO SKIP"
  unfolding equiv_up_to_def
  by (blast dest: while_never)


end
