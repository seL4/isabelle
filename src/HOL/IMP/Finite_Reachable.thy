theory Finite_Reachable
imports Small_Step
begin

subsection "Finite number of reachable commands"

text\<open>This theory shows that in the small-step semantics one can only reach
a finite number of commands from any given command. Hence one can see the
command component of a small-step configuration as a combination of the
program to be executed and a pc.\<close>

definition reachable :: "com \<Rightarrow> com set" where
"reachable c = {c'. \<exists>s t. (c,s) \<rightarrow>* (c',t)}"

text\<open>Proofs need induction on the length of a small-step reduction sequence.\<close>

fun small_stepsn :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool"
    (\<open>_ \<rightarrow>'(_') _\<close> [55,0,55] 55) where
"(cs \<rightarrow>(0) cs') = (cs' = cs)" |
"cs \<rightarrow>(Suc n) cs'' = (\<exists>cs'. cs \<rightarrow> cs' \<and> cs' \<rightarrow>(n) cs'')"

lemma stepsn_if_star: "cs \<rightarrow>* cs' \<Longrightarrow> \<exists>n. cs \<rightarrow>(n) cs'"
proof(induction rule: star.induct)
  case refl show ?case by (metis small_stepsn.simps(1))
next
  case step thus ?case by (metis small_stepsn.simps(2))
qed

lemma star_if_stepsn: "cs \<rightarrow>(n) cs' \<Longrightarrow> cs \<rightarrow>* cs'"
by(induction n arbitrary: cs) (auto elim: star.step)

lemma SKIP_starD: "(SKIP, s) \<rightarrow>* (c,t) \<Longrightarrow> c = SKIP"
by(induction SKIP s c t rule: star_induct) auto

lemma reachable_SKIP: "reachable SKIP = {SKIP}"
by(auto simp: reachable_def dest: SKIP_starD)


lemma Assign_starD: "(x::=a, s) \<rightarrow>* (c,t) \<Longrightarrow> c \<in> {x::=a, SKIP}"
by (induction "x::=a" s c t rule: star_induct) (auto dest: SKIP_starD)

lemma reachable_Assign: "reachable (x::=a) = {x::=a, SKIP}"
by(auto simp: reachable_def dest:Assign_starD)


lemma Seq_stepsnD: "(c1;; c2, s) \<rightarrow>(n) (c', t) \<Longrightarrow>
  (\<exists>c1' m. c' = c1';; c2 \<and> (c1, s) \<rightarrow>(m) (c1', t) \<and> m \<le> n) \<or>
  (\<exists>s2 m1 m2. (c1,s) \<rightarrow>(m1) (SKIP,s2) \<and> (c2, s2) \<rightarrow>(m2) (c', t) \<and> m1+m2 < n)"
proof(induction n arbitrary: c1 c2 s)
  case 0 thus ?case by auto
next
  case (Suc n)
  from Suc.prems obtain s' c12' where "(c1;;c2, s) \<rightarrow> (c12', s')"
    and n: "(c12',s') \<rightarrow>(n) (c',t)" by auto
  from this(1) show ?case
  proof
    assume "c1 = SKIP" "(c12', s') = (c2, s)"
    hence "(c1,s) \<rightarrow>(0) (SKIP, s') \<and> (c2, s') \<rightarrow>(n) (c', t) \<and> 0 + n < Suc n"
      using n by auto
    thus ?case by blast
  next
    fix c1' s'' assume 1: "(c12', s') = (c1';; c2, s'')" "(c1, s) \<rightarrow> (c1', s'')"
    hence n': "(c1';;c2,s') \<rightarrow>(n) (c',t)" using n by auto
    from Suc.IH[OF n'] show ?case
    proof
      assume "\<exists>c1'' m. c' = c1'';; c2 \<and> (c1', s') \<rightarrow>(m) (c1'', t) \<and> m \<le> n"
        (is "\<exists> a b. ?P a b")
      then obtain c1'' m where 2: "?P c1'' m" by blast
      hence "c' = c1'';;c2 \<and> (c1, s) \<rightarrow>(Suc m) (c1'',t) \<and> Suc m \<le> Suc n"
        using 1 by auto
      thus ?case by blast
    next
      assume "\<exists>s2 m1 m2. (c1',s') \<rightarrow>(m1) (SKIP,s2) \<and>
        (c2,s2) \<rightarrow>(m2) (c',t) \<and> m1+m2 < n" (is "\<exists>a b c. ?P a b c")
      then obtain s2 m1 m2 where "?P s2 m1 m2" by blast
      hence "(c1,s) \<rightarrow>(Suc m1) (SKIP,s2) \<and> (c2,s2) \<rightarrow>(m2) (c',t) \<and>
        Suc m1 + m2 < Suc n"  using 1 by auto
      thus ?case by blast
    qed
  qed
qed

corollary Seq_starD: "(c1;; c2, s) \<rightarrow>* (c', t) \<Longrightarrow>
  (\<exists>c1'. c' = c1';; c2 \<and> (c1, s) \<rightarrow>* (c1', t)) \<or>
  (\<exists>s2. (c1,s) \<rightarrow>* (SKIP,s2) \<and> (c2, s2) \<rightarrow>* (c', t))"
by(metis Seq_stepsnD star_if_stepsn stepsn_if_star)

lemma reachable_Seq: "reachable (c1;;c2) \<subseteq>
  (\<lambda>c1'. c1';;c2) ` reachable c1 \<union> reachable c2"
by(auto simp: reachable_def image_def dest!: Seq_starD)


lemma If_starD: "(IF b THEN c1 ELSE c2, s) \<rightarrow>* (c,t) \<Longrightarrow>
  c = IF b THEN c1 ELSE c2 \<or> (c1,s) \<rightarrow>* (c,t) \<or> (c2,s) \<rightarrow>* (c,t)"
by(induction "IF b THEN c1 ELSE c2" s c t rule: star_induct) auto

lemma reachable_If: "reachable (IF b THEN c1 ELSE c2) \<subseteq>
  {IF b THEN c1 ELSE c2} \<union> reachable c1 \<union> reachable c2"
by(auto simp: reachable_def dest!: If_starD)


lemma While_stepsnD: "(WHILE b DO c, s) \<rightarrow>(n) (c2,t) \<Longrightarrow>
  c2 \<in> {WHILE b DO c, IF b THEN c ;; WHILE b DO c ELSE SKIP, SKIP}
  \<or> (\<exists>c1. c2 = c1 ;; WHILE b DO c \<and> (\<exists> s1 s2. (c,s1) \<rightarrow>* (c1,s2)))"
proof(induction n arbitrary: s rule: less_induct)
  case (less n1)
  show ?case
  proof(cases n1)
    case 0 thus ?thesis using less.prems by (simp)
  next
    case (Suc n2)
    let ?w = "WHILE b DO c"
    let ?iw = "IF b THEN c ;; ?w ELSE SKIP"
    from Suc less.prems have n2: "(?iw,s) \<rightarrow>(n2) (c2,t)" by(auto elim!: WhileE)
    show ?thesis
    proof(cases n2)
      case 0 thus ?thesis using n2 by auto
    next
      case (Suc n3)
      then obtain iw' s' where "(?iw,s) \<rightarrow> (iw',s')"
        and n3: "(iw',s') \<rightarrow>(n3) (c2,t)"  using n2 by auto
      from this(1)
      show ?thesis
      proof
        assume "(iw', s') = (c;; WHILE b DO c, s)"
        with n3 have "(c;;?w, s) \<rightarrow>(n3) (c2,t)" by auto
        from Seq_stepsnD[OF this] show ?thesis
        proof
          assume "\<exists>c1' m. c2 = c1';; ?w \<and> (c,s) \<rightarrow>(m) (c1', t) \<and> m \<le> n3"
          thus ?thesis by (metis star_if_stepsn)
        next
          assume "\<exists>s2 m1 m2. (c, s) \<rightarrow>(m1) (SKIP, s2) \<and>
            (WHILE b DO c, s2) \<rightarrow>(m2) (c2, t) \<and> m1 + m2 < n3" (is "\<exists>x y z. ?P x y z")
          then obtain s2 m1 m2 where "?P s2 m1 m2" by blast
          with \<open>n2 = Suc n3\<close> \<open>n1 = Suc n2\<close>have "m2 < n1" by arith
          from less.IH[OF this] \<open>?P s2 m1 m2\<close> show ?thesis by blast
        qed
      next
        assume "(iw', s') = (SKIP, s)"
        thus ?thesis using star_if_stepsn[OF n3] by(auto dest!: SKIP_starD)
      qed
    qed
  qed
qed

lemma reachable_While: "reachable (WHILE b DO c) \<subseteq>
  {WHILE b DO c, IF b THEN c ;; WHILE b DO c ELSE SKIP, SKIP} \<union>
  (\<lambda>c'. c' ;; WHILE b DO c) ` reachable c"
apply(auto simp: reachable_def image_def)
by (metis While_stepsnD insertE singletonE stepsn_if_star)


theorem finite_reachable: "finite(reachable c)"
apply(induction c)
apply(auto simp: reachable_SKIP reachable_Assign
  finite_subset[OF reachable_Seq] finite_subset[OF reachable_If]
  finite_subset[OF reachable_While])
done


end
