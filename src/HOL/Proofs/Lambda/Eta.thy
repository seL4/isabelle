(*  Title:      HOL/Proofs/Lambda/Eta.thy
    Author:     Tobias Nipkow and Stefan Berghofer
    Copyright   1995, 2005 TU Muenchen
*)

header {* Eta-reduction *}

theory Eta imports ParRed begin


subsection {* Definition of eta-reduction and relatives *}

primrec
  free :: "dB => nat => bool"
where
    "free (Var j) i = (j = i)"
  | "free (s \<degree> t) i = (free s i \<or> free t i)"
  | "free (Abs s) i = free s (i + 1)"

inductive
  eta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<eta>" 50)
where
    eta [simp, intro]: "\<not> free s 0 ==> Abs (s \<degree> Var 0) \<rightarrow>\<^sub>\<eta> s[dummy/0]"
  | appL [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t ==> s \<degree> u \<rightarrow>\<^sub>\<eta> t \<degree> u"
  | appR [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t ==> u \<degree> s \<rightarrow>\<^sub>\<eta> u \<degree> t"
  | abs [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t ==> Abs s \<rightarrow>\<^sub>\<eta> Abs t"

abbreviation
  eta_reds :: "[dB, dB] => bool"   (infixl "-e>>" 50) where
  "s -e>> t == eta^** s t"

abbreviation
  eta_red0 :: "[dB, dB] => bool"   (infixl "-e>=" 50) where
  "s -e>= t == eta^== s t"

notation (xsymbols)
  eta_reds  (infixl "\<rightarrow>\<^sub>\<eta>\<^sup>*" 50) and
  eta_red0  (infixl "\<rightarrow>\<^sub>\<eta>\<^sup>=" 50)

inductive_cases eta_cases [elim!]:
  "Abs s \<rightarrow>\<^sub>\<eta> z"
  "s \<degree> t \<rightarrow>\<^sub>\<eta> u"
  "Var i \<rightarrow>\<^sub>\<eta> t"


subsection {* Properties of @{text "eta"}, @{text "subst"} and @{text "free"} *}

lemma subst_not_free [simp]: "\<not> free s i \<Longrightarrow> s[t/i] = s[u/i]"
  by (induct s arbitrary: i t u) (simp_all add: subst_Var)

lemma free_lift [simp]:
    "free (lift t k) i = (i < k \<and> free t i \<or> k < i \<and> free t (i - 1))"
  apply (induct t arbitrary: i k)
  apply (auto cong: conj_cong)
  done

lemma free_subst [simp]:
    "free (s[t/k]) i =
      (free s k \<and> free t i \<or> free s (if i < k then i else i + 1))"
  apply (induct s arbitrary: i k t)
    prefer 2
    apply simp
    apply blast
   prefer 2
   apply simp
  apply (simp add: diff_Suc subst_Var split: nat.split)
  done

lemma free_eta: "s \<rightarrow>\<^sub>\<eta> t ==> free t i = free s i"
  by (induct arbitrary: i set: eta) (simp_all cong: conj_cong)

lemma not_free_eta:
    "[| s \<rightarrow>\<^sub>\<eta> t; \<not> free s i |] ==> \<not> free t i"
  by (simp add: free_eta)

lemma eta_subst [simp]:
    "s \<rightarrow>\<^sub>\<eta> t ==> s[u/i] \<rightarrow>\<^sub>\<eta> t[u/i]"
  by (induct arbitrary: u i set: eta) (simp_all add: subst_subst [symmetric])

theorem lift_subst_dummy: "\<not> free s i \<Longrightarrow> lift (s[dummy/i]) i = s"
  by (induct s arbitrary: i dummy) simp_all


subsection {* Confluence of @{text "eta"} *}

lemma square_eta: "square eta eta (eta^==) (eta^==)"
  apply (unfold square_def id_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule eta.induct)
     apply (slowsimp intro: subst_not_free eta_subst free_eta [THEN iffD1])
    apply safe
       prefer 5
       apply (blast intro!: eta_subst intro: free_eta [THEN iffD1])
      apply blast+
  done

theorem eta_confluent: "confluent eta"
  apply (rule square_eta [THEN square_reflcl_confluent])
  done


subsection {* Congruence rules for @{text "eta\<^sup>*"} *}

lemma rtrancl_eta_Abs: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' ==> Abs s \<rightarrow>\<^sub>\<eta>\<^sup>* Abs s'"
  by (induct set: rtranclp)
    (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_AppL: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' ==> s \<degree> t \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<degree> t"
  by (induct set: rtranclp)
    (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_AppR: "t \<rightarrow>\<^sub>\<eta>\<^sup>* t' ==> s \<degree> t \<rightarrow>\<^sub>\<eta>\<^sup>* s \<degree> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_App:
    "[| s \<rightarrow>\<^sub>\<eta>\<^sup>* s'; t \<rightarrow>\<^sub>\<eta>\<^sup>* t' |] ==> s \<degree> t \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<degree> t'"
  by (blast intro!: rtrancl_eta_AppL rtrancl_eta_AppR intro: rtranclp_trans)


subsection {* Commutation of @{text "beta"} and @{text "eta"} *}

lemma free_beta:
    "s \<rightarrow>\<^sub>\<beta> t ==> free t i \<Longrightarrow> free s i"
  by (induct arbitrary: i set: beta) auto

lemma beta_subst [intro]: "s \<rightarrow>\<^sub>\<beta> t ==> s[u/i] \<rightarrow>\<^sub>\<beta> t[u/i]"
  by (induct arbitrary: u i set: beta) (simp_all add: subst_subst [symmetric])

lemma subst_Var_Suc [simp]: "t[Var i/i] = t[Var(i)/i + 1]"
  by (induct t arbitrary: i) (auto elim!: linorder_neqE simp: subst_Var)

lemma eta_lift [simp]: "s \<rightarrow>\<^sub>\<eta> t ==> lift s i \<rightarrow>\<^sub>\<eta> lift t i"
  by (induct arbitrary: i set: eta) simp_all

lemma rtrancl_eta_subst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> u[s/i] \<rightarrow>\<^sub>\<eta>\<^sup>* u[t/i]"
  apply (induct u arbitrary: s t i)
    apply (simp_all add: subst_Var)
    apply blast
   apply (blast intro: rtrancl_eta_App)
  apply (blast intro!: rtrancl_eta_Abs eta_lift)
  done

lemma rtrancl_eta_subst':
  fixes s t :: dB
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t"
  shows "s[u/i] \<rightarrow>\<^sub>\<eta>\<^sup>* t[u/i]" using eta
  by induct (iprover intro: eta_subst)+

lemma rtrancl_eta_subst'':
  fixes s t :: dB
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t"
  shows "u[s/i] \<rightarrow>\<^sub>\<eta>\<^sup>* u[t/i]" using eta
  by induct (iprover intro: rtrancl_eta_subst rtranclp_trans)+

lemma square_beta_eta: "square beta eta (eta^**) (beta^==)"
  apply (unfold square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule beta.induct)
     apply (slowsimp intro: rtrancl_eta_subst eta_subst)
    apply (blast intro: rtrancl_eta_AppL)
   apply (blast intro: rtrancl_eta_AppR)
  apply simp
  apply (slowsimp intro: rtrancl_eta_Abs free_beta
    iff del: dB.distinct simp: dB.distinct)    (*23 seconds?*)
  done

lemma confluent_beta_eta: "confluent (sup beta eta)"
  apply (assumption |
    rule square_rtrancl_reflcl_commute confluent_Un
      beta_confluent eta_confluent square_beta_eta)+
  done


subsection {* Implicit definition of @{text "eta"} *}

text {* @{term "Abs (lift s 0 \<degree> Var 0) \<rightarrow>\<^sub>\<eta> s"} *}

lemma not_free_iff_lifted:
    "(\<not> free s i) = (\<exists>t. s = lift t i)"
  apply (induct s arbitrary: i)
    apply simp
    apply (rule iffI)
     apply (erule linorder_neqE)
      apply (rule_tac x = "Var nat" in exI)
      apply simp
     apply (rule_tac x = "Var (nat - 1)" in exI)
     apply simp
    apply clarify
    apply (rule notE)
     prefer 2
     apply assumption
    apply (erule thin_rl)
    apply (case_tac t)
      apply simp
     apply simp
    apply simp
   apply simp
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (rule iffI)
    apply (elim conjE exE)
    apply (rename_tac u1 u2)
    apply (rule_tac x = "u1 \<degree> u2" in exI)
    apply simp
   apply (erule exE)
   apply (erule rev_mp)
   apply (case_tac t)
     apply simp
    apply simp
    apply blast
   apply simp
  apply simp
  apply (erule thin_rl)
  apply (rule iffI)
   apply (erule exE)
   apply (rule_tac x = "Abs t" in exI)
   apply simp
  apply (erule exE)
  apply (erule rev_mp)
  apply (case_tac t)
    apply simp
   apply simp
  apply simp
  apply blast
  done

theorem explicit_is_implicit:
  "(\<forall>s u. (\<not> free s 0) --> R (Abs (s \<degree> Var 0)) (s[u/0])) =
    (\<forall>s. R (Abs (lift s 0 \<degree> Var 0)) s)"
  by (auto simp add: not_free_iff_lifted)


subsection {* Eta-postponement theorem *}

text {*
  Based on a paper proof due to Andreas Abel.
  Unlike the proof by Masako Takahashi \cite{Takahashi-IandC}, it does not
  use parallel eta reduction, which only seems to complicate matters unnecessarily.
*}

theorem eta_case:
  fixes s :: dB
  assumes free: "\<not> free s 0"
  and s: "s[dummy/0] => u"
  shows "\<exists>t'. Abs (s \<degree> Var 0) => t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u"
proof -
  from s have "lift (s[dummy/0]) 0 => lift u 0" by (simp del: lift_subst)
  with free have "s => lift u 0" by (simp add: lift_subst_dummy del: lift_subst)
  hence "Abs (s \<degree> Var 0) => Abs (lift u 0 \<degree> Var 0)" by simp
  moreover have "\<not> free (lift u 0) 0" by simp
  hence "Abs (lift u 0 \<degree> Var 0) \<rightarrow>\<^sub>\<eta> lift u 0[dummy/0]"
    by (rule eta.eta)
  hence "Abs (lift u 0 \<degree> Var 0) \<rightarrow>\<^sub>\<eta>\<^sup>* u" by simp
  ultimately show ?thesis by iprover
qed

theorem eta_par_beta:
  assumes st: "s \<rightarrow>\<^sub>\<eta> t"
  and tu: "t => u"
  shows "\<exists>t'. s => t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u" using tu st
proof (induct arbitrary: s)
  case (var n)
  thus ?case by (iprover intro: par_beta_refl)
next
  case (abs s' t)
  note abs' = this
  from `s \<rightarrow>\<^sub>\<eta> Abs s'` show ?case
  proof cases
    case (eta s'' dummy)
    from abs have "Abs s' => Abs t" by simp
    with eta have "s''[dummy/0] => Abs t" by simp
    with `\<not> free s'' 0` have "\<exists>t'. Abs (s'' \<degree> Var 0) => t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* Abs t"
      by (rule eta_case)
    with eta show ?thesis by simp
  next
    case (abs r)
    from `r \<rightarrow>\<^sub>\<eta> s'`
    obtain t' where r: "r => t'" and t': "t' \<rightarrow>\<^sub>\<eta>\<^sup>* t" by (iprover dest: abs')
    from r have "Abs r => Abs t'" ..
    moreover from t' have "Abs t' \<rightarrow>\<^sub>\<eta>\<^sup>* Abs t" by (rule rtrancl_eta_Abs)
    ultimately show ?thesis using abs by simp iprover
  qed
next
  case (app u u' t t')
  from `s \<rightarrow>\<^sub>\<eta> u \<degree> t` show ?case
  proof cases
    case (eta s' dummy)
    from app have "u \<degree> t => u' \<degree> t'" by simp
    with eta have "s'[dummy/0] => u' \<degree> t'" by simp
    with `\<not> free s' 0` have "\<exists>r. Abs (s' \<degree> Var 0) => r \<and> r \<rightarrow>\<^sub>\<eta>\<^sup>* u' \<degree> t'"
      by (rule eta_case)
    with eta show ?thesis by simp
  next
    case (appL s')
    from `s' \<rightarrow>\<^sub>\<eta> u`
    obtain r where s': "s' => r" and r: "r \<rightarrow>\<^sub>\<eta>\<^sup>* u'" by (iprover dest: app)
    from s' and app have "s' \<degree> t => r \<degree> t'" by simp
    moreover from r have "r \<degree> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u' \<degree> t'" by (simp add: rtrancl_eta_AppL)
    ultimately show ?thesis using appL by simp iprover
  next
    case (appR s')
    from `s' \<rightarrow>\<^sub>\<eta> t`
    obtain r where s': "s' => r" and r: "r \<rightarrow>\<^sub>\<eta>\<^sup>* t'" by (iprover dest: app)
    from s' and app have "u \<degree> s' => u' \<degree> r" by simp
    moreover from r have "u' \<degree> r \<rightarrow>\<^sub>\<eta>\<^sup>* u' \<degree> t'" by (simp add: rtrancl_eta_AppR)
    ultimately show ?thesis using appR by simp iprover
  qed
next
  case (beta u u' t t')
  from `s \<rightarrow>\<^sub>\<eta> Abs u \<degree> t` show ?case
  proof cases
    case (eta s' dummy)
    from beta have "Abs u \<degree> t => u'[t'/0]" by simp
    with eta have "s'[dummy/0] => u'[t'/0]" by simp
    with `\<not> free s' 0` have "\<exists>r. Abs (s' \<degree> Var 0) => r \<and> r \<rightarrow>\<^sub>\<eta>\<^sup>* u'[t'/0]"
      by (rule eta_case)
    with eta show ?thesis by simp
  next
    case (appL s')
    from `s' \<rightarrow>\<^sub>\<eta> Abs u` show ?thesis
    proof cases
      case (eta s'' dummy)
      have "Abs (lift u 1) = lift (Abs u) 0" by simp
      also from eta have "\<dots> = s''" by (simp add: lift_subst_dummy del: lift_subst)
      finally have s: "s = Abs (Abs (lift u 1) \<degree> Var 0) \<degree> t" using appL and eta by simp
      from beta have "lift u 1 => lift u' 1" by simp
      hence "Abs (lift u 1) \<degree> Var 0 => lift u' 1[Var 0/0]"
        using par_beta.var ..
      hence "Abs (Abs (lift u 1) \<degree> Var 0) \<degree> t => lift u' 1[Var 0/0][t'/0]"
        using `t => t'` ..
      with s have "s => u'[t'/0]" by simp
      thus ?thesis by iprover
    next
      case (abs r)
      from `r \<rightarrow>\<^sub>\<eta> u`
      obtain r'' where r: "r => r''" and r'': "r'' \<rightarrow>\<^sub>\<eta>\<^sup>* u'" by (iprover dest: beta)
      from r and beta have "Abs r \<degree> t => r''[t'/0]" by simp
      moreover from r'' have "r''[t'/0] \<rightarrow>\<^sub>\<eta>\<^sup>* u'[t'/0]"
        by (rule rtrancl_eta_subst')
      ultimately show ?thesis using abs and appL by simp iprover
    qed
  next
    case (appR s')
    from `s' \<rightarrow>\<^sub>\<eta> t`
    obtain r where s': "s' => r" and r: "r \<rightarrow>\<^sub>\<eta>\<^sup>* t'" by (iprover dest: beta)
    from s' and beta have "Abs u \<degree> s' => u'[r/0]" by simp
    moreover from r have "u'[r/0] \<rightarrow>\<^sub>\<eta>\<^sup>* u'[t'/0]"
      by (rule rtrancl_eta_subst'')
    ultimately show ?thesis using appR by simp iprover
  qed
qed

theorem eta_postponement':
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t" and beta: "t => u"
  shows "\<exists>t'. s => t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u" using eta beta
proof (induct arbitrary: u)
  case base
  thus ?case by blast
next
  case (step s' s'' s''')
  then obtain t' where s': "s' => t'" and t': "t' \<rightarrow>\<^sub>\<eta>\<^sup>* s'''"
    by (auto dest: eta_par_beta)
  from s' obtain t'' where s: "s => t''" and t'': "t'' \<rightarrow>\<^sub>\<eta>\<^sup>* t'" using step
    by blast
  from t'' and t' have "t'' \<rightarrow>\<^sub>\<eta>\<^sup>* s'''" by (rule rtranclp_trans)
  with s show ?case by iprover
qed

theorem eta_postponement:
  assumes "(sup beta eta)\<^sup>*\<^sup>* s t"
  shows "(beta\<^sup>*\<^sup>* OO eta\<^sup>*\<^sup>*) s t" using assms
proof induct
  case base
  show ?case by blast
next
  case (step s' s'')
  from step(3) obtain t' where s: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and t': "t' \<rightarrow>\<^sub>\<eta>\<^sup>* s'" by blast
  from step(2) show ?case
  proof
    assume "s' \<rightarrow>\<^sub>\<beta> s''"
    with beta_subset_par_beta have "s' => s''" ..
    with t' obtain t'' where st: "t' => t''" and tu: "t'' \<rightarrow>\<^sub>\<eta>\<^sup>* s''"
      by (auto dest: eta_postponement')
    from par_beta_subset_beta st have "t' \<rightarrow>\<^sub>\<beta>\<^sup>* t''" ..
    with s have "s \<rightarrow>\<^sub>\<beta>\<^sup>* t''" by (rule rtranclp_trans)
    thus ?thesis using tu ..
  next
    assume "s' \<rightarrow>\<^sub>\<eta> s''"
    with t' have "t' \<rightarrow>\<^sub>\<eta>\<^sup>* s''" ..
    with s show ?thesis ..
  qed
qed

end
