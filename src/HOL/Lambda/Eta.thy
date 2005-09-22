(*  Title:      HOL/Lambda/Eta.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Stefan Berghofer
    Copyright   1995, 2005 TU Muenchen
*)

header {* Eta-reduction *}

theory Eta imports ParRed begin


subsection {* Definition of eta-reduction and relatives *}

consts
  free :: "dB => nat => bool"
primrec
  "free (Var j) i = (j = i)"
  "free (s \<degree> t) i = (free s i \<or> free t i)"
  "free (Abs s) i = free s (i + 1)"

consts
  eta :: "(dB \<times> dB) set"

syntax 
  "_eta" :: "[dB, dB] => bool"   (infixl "-e>" 50)
  "_eta_rtrancl" :: "[dB, dB] => bool"   (infixl "-e>>" 50)
  "_eta_reflcl" :: "[dB, dB] => bool"   (infixl "-e>=" 50)
translations
  "s -e> t" == "(s, t) \<in> eta"
  "s -e>> t" == "(s, t) \<in> eta^*"
  "s -e>= t" == "(s, t) \<in> eta^="

inductive eta
  intros
    eta [simp, intro]: "\<not> free s 0 ==> Abs (s \<degree> Var 0) -e> s[dummy/0]"
    appL [simp, intro]: "s -e> t ==> s \<degree> u -e> t \<degree> u"
    appR [simp, intro]: "s -e> t ==> u \<degree> s -e> u \<degree> t"
    abs [simp, intro]: "s -e> t ==> Abs s -e> Abs t"

inductive_cases eta_cases [elim!]:
  "Abs s -e> z"
  "s \<degree> t -e> u"
  "Var i -e> t"


subsection "Properties of eta, subst and free"

lemma subst_not_free [rule_format, simp]:
    "\<forall>i t u. \<not> free s i --> s[t/i] = s[u/i]"
  apply (induct_tac s)
    apply (simp_all add: subst_Var)
  done

lemma free_lift [simp]:
    "\<forall>i k. free (lift t k) i =
      (i < k \<and> free t i \<or> k < i \<and> free t (i - 1))"
  apply (induct_tac t)
    apply (auto cong: conj_cong)
  apply arith
  done

lemma free_subst [simp]:
    "\<forall>i k t. free (s[t/k]) i =
      (free s k \<and> free t i \<or> free s (if i < k then i else i + 1))"
  apply (induct_tac s)
    prefer 2
    apply simp
    apply blast
   prefer 2
   apply simp
  apply (simp add: diff_Suc subst_Var split: nat.split)
  done

lemma free_eta [rule_format]:
    "s -e> t ==> \<forall>i. free t i = free s i"
  apply (erule eta.induct)
     apply (simp_all cong: conj_cong)
  done

lemma not_free_eta:
    "[| s -e> t; \<not> free s i |] ==> \<not> free t i"
  apply (simp add: free_eta)
  done

lemma eta_subst [rule_format, simp]:
    "s -e> t ==> \<forall>u i. s[u/i] -e> t[u/i]"
  apply (erule eta.induct)
  apply (simp_all add: subst_subst [symmetric])
  done

theorem lift_subst_dummy: "\<And>i dummy. \<not> free s i \<Longrightarrow> lift (s[dummy/i]) i = s"
  by (induct s) simp_all


subsection "Confluence of eta"

lemma square_eta: "square eta eta (eta^=) (eta^=)"
  apply (unfold square_def id_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply simp
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


subsection "Congruence rules for eta*"

lemma rtrancl_eta_Abs: "s -e>> s' ==> Abs s -e>> Abs s'"
  apply (erule rtrancl_induct)
   apply (blast intro: rtrancl_refl rtrancl_into_rtrancl)+
  done

lemma rtrancl_eta_AppL: "s -e>> s' ==> s \<degree> t -e>> s' \<degree> t"
  apply (erule rtrancl_induct)
   apply (blast intro: rtrancl_refl rtrancl_into_rtrancl)+
  done

lemma rtrancl_eta_AppR: "t -e>> t' ==> s \<degree> t -e>> s \<degree> t'"
  apply (erule rtrancl_induct)
   apply (blast intro: rtrancl_refl rtrancl_into_rtrancl)+
  done

lemma rtrancl_eta_App:
    "[| s -e>> s'; t -e>> t' |] ==> s \<degree> t -e>> s' \<degree> t'"
  apply (blast intro!: rtrancl_eta_AppL rtrancl_eta_AppR intro: rtrancl_trans)
  done


subsection "Commutation of beta and eta"

lemma free_beta [rule_format]:
    "s -> t ==> \<forall>i. free t i --> free s i"
  apply (erule beta.induct)
     apply simp_all
  done

lemma beta_subst [rule_format, intro]:
    "s -> t ==> \<forall>u i. s[u/i] -> t[u/i]"
  apply (erule beta.induct)
     apply (simp_all add: subst_subst [symmetric])
  done

lemma subst_Var_Suc [simp]: "\<forall>i. t[Var i/i] = t[Var(i)/i + 1]"
  apply (induct_tac t)
  apply (auto elim!: linorder_neqE simp: subst_Var)
  done

lemma eta_lift [rule_format, simp]:
    "s -e> t ==> \<forall>i. lift s i -e> lift t i"
  apply (erule eta.induct)
     apply simp_all
  done

lemma rtrancl_eta_subst [rule_format]:
    "\<forall>s t i. s -e> t --> u[s/i] -e>> u[t/i]"
  apply (induct_tac u)
    apply (simp_all add: subst_Var)
    apply (blast)
   apply (blast intro: rtrancl_eta_App)
  apply (blast intro!: rtrancl_eta_Abs eta_lift)
  done

lemma square_beta_eta: "square beta eta (eta^*) (beta^=)"
  apply (unfold square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule beta.induct)
     apply (slowsimp intro: rtrancl_eta_subst eta_subst)
    apply (blast intro: rtrancl_eta_AppL)
   apply (blast intro: rtrancl_eta_AppR)
  apply simp;
  apply (slowsimp intro: rtrancl_eta_Abs free_beta
    iff del: dB.distinct simp: dB.distinct)    (*23 seconds?*)
  done

lemma confluent_beta_eta: "confluent (beta \<union> eta)"
  apply (assumption |
    rule square_rtrancl_reflcl_commute confluent_Un
      beta_confluent eta_confluent square_beta_eta)+
  done


subsection "Implicit definition of eta"

text {* @{term "Abs (lift s 0 \<degree> Var 0) -e> s"} *}

lemma not_free_iff_lifted [rule_format]:
    "\<forall>i. (\<not> free s i) = (\<exists>t. s = lift t i)"
  apply (induct_tac s)
    apply simp
    apply clarify
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
   apply (rule allI)
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
  apply (rule allI)
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
  apply (auto simp add: not_free_iff_lifted)
  done


subsection {* Parallel eta-reduction *}

consts
  par_eta :: "(dB \<times> dB) set"

syntax 
  "_par_eta" :: "[dB, dB] => bool"   (infixl "=e>" 50)
translations
  "s =e> t" == "(s, t) \<in> par_eta"

syntax (xsymbols)
  "_par_eta" :: "[dB, dB] => bool"   (infixl "\<Rightarrow>\<^sub>\<eta>" 50)

inductive par_eta
intros
  var [simp, intro]: "Var x \<Rightarrow>\<^sub>\<eta> Var x"
  eta [simp, intro]: "\<not> free s 0 \<Longrightarrow> s \<Rightarrow>\<^sub>\<eta> s'\<Longrightarrow> Abs (s \<degree> Var 0) \<Rightarrow>\<^sub>\<eta> s'[dummy/0]"
  app [simp, intro]: "s \<Rightarrow>\<^sub>\<eta> s' \<Longrightarrow> t \<Rightarrow>\<^sub>\<eta> t' \<Longrightarrow> s \<degree> t \<Rightarrow>\<^sub>\<eta> s' \<degree> t'"
  abs [simp, intro]: "s \<Rightarrow>\<^sub>\<eta> t \<Longrightarrow> Abs s \<Rightarrow>\<^sub>\<eta> Abs t"

lemma free_par_eta [simp]: assumes eta: "s \<Rightarrow>\<^sub>\<eta> t"
  shows "\<And>i. free t i = free s i" using eta
  by induct (simp_all cong: conj_cong)

lemma par_eta_refl [simp]: "t \<Rightarrow>\<^sub>\<eta> t"
  by (induct t) simp_all

lemma par_eta_lift [simp]:
  assumes eta: "s \<Rightarrow>\<^sub>\<eta> t"
  shows "\<And>i. lift s i \<Rightarrow>\<^sub>\<eta> lift t i" using eta
  by induct simp_all

lemma par_eta_subst [simp]:
  assumes eta: "s \<Rightarrow>\<^sub>\<eta> t"
  shows "\<And>u u' i. u \<Rightarrow>\<^sub>\<eta> u' \<Longrightarrow> s[u/i] \<Rightarrow>\<^sub>\<eta> t[u'/i]" using eta
  by induct (simp_all add: subst_subst [symmetric] subst_Var)

theorem eta_subset_par_eta: "eta \<subseteq> par_eta"
  apply (rule subsetI)
  apply clarify
  apply (erule eta.induct)
  apply (blast intro!: par_eta_refl)+
  done

theorem par_eta_subset_eta: "par_eta \<subseteq> eta\<^sup>*"
  apply (rule subsetI)
  apply clarify
  apply (erule par_eta.induct)
  apply blast
  apply (rule rtrancl_into_rtrancl)
  apply (rule rtrancl_eta_Abs)
  apply (rule rtrancl_eta_AppL)
  apply assumption
  apply (rule eta.eta)
  apply simp
  apply (rule rtrancl_eta_App)
  apply assumption+
  apply (rule rtrancl_eta_Abs)
  apply assumption
  done


subsection {* n-ary eta-expansion *}

consts eta_expand :: "nat \<Rightarrow> dB \<Rightarrow> dB"
primrec
  eta_expand_0: "eta_expand 0 t = t"
  eta_expand_Suc: "eta_expand (Suc n) t = Abs (lift (eta_expand n t) 0 \<degree> Var 0)"

lemma eta_expand_Suc':
  "\<And>t. eta_expand (Suc n) t = eta_expand n (Abs (lift t 0 \<degree> Var 0))"
  by (induct n) simp_all

theorem lift_eta_expand: "lift (eta_expand k t) i = eta_expand k (lift t i)"
  by (induct k) (simp_all add: lift_lift)

theorem eta_expand_beta:
  assumes u: "u => u'"
  shows "\<And>t t'. t => t' \<Longrightarrow> eta_expand k (Abs t) \<degree> u => t'[u'/0]"
proof (induct k)
  case 0 with u show ?case by simp
next
  case (Suc k)
  hence "Abs (lift t (Suc 0)) \<degree> Var 0 => lift t' (Suc 0)[Var 0/0]"
    by (blast intro: par_beta_lift)
  with Suc show ?case by (simp del: eta_expand_Suc add: eta_expand_Suc')
qed

theorem eta_expand_red:
  assumes t: "t => t'"
  shows "eta_expand k t => eta_expand k t'"
  by (induct k) (simp_all add: t)

theorem eta_expand_eta: "\<And>t t'. t \<Rightarrow>\<^sub>\<eta> t' \<Longrightarrow> eta_expand k t \<Rightarrow>\<^sub>\<eta> t'"
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "Abs (lift (eta_expand k t) 0 \<degree> Var 0) \<Rightarrow>\<^sub>\<eta> lift t' 0[arbitrary/0]"
    by (fastsimp intro: par_eta_lift Suc)
  thus ?case by simp
qed


subsection {* Elimination rules for parallel eta reduction *}

theorem par_eta_elim_app: assumes eta: "t \<Rightarrow>\<^sub>\<eta> u"
  shows "\<And>u1' u2'. u = u1' \<degree> u2' \<Longrightarrow>
    \<exists>u1 u2 k. t = eta_expand k (u1 \<degree> u2) \<and> u1 \<Rightarrow>\<^sub>\<eta> u1' \<and> u2 \<Rightarrow>\<^sub>\<eta> u2'" using eta
proof induct
  case (app s s' t t')
  have "s \<degree> t = eta_expand 0 (s \<degree> t)" by simp
  with app show ?case by blast
next
  case (eta dummy s s')
  then obtain u1'' u2'' where s': "s' = u1'' \<degree> u2''"
    by (cases s') (auto simp add: subst_Var free_par_eta [symmetric] split: split_if_asm)
  then have "\<exists>u1 u2 k. s = eta_expand k (u1 \<degree> u2) \<and> u1 \<Rightarrow>\<^sub>\<eta> u1'' \<and> u2 \<Rightarrow>\<^sub>\<eta> u2''" by (rule eta)
  then obtain u1 u2 k where s: "s = eta_expand k (u1 \<degree> u2)"
    and u1: "u1 \<Rightarrow>\<^sub>\<eta> u1''" and u2: "u2 \<Rightarrow>\<^sub>\<eta> u2''" by iprover
  from u1 u2 eta s' have "\<not> free u1 0" and "\<not> free u2 0"
    by (simp_all del: free_par_eta add: free_par_eta [symmetric])
  with s have "Abs (s \<degree> Var 0) = eta_expand (Suc k) (u1[dummy/0] \<degree> u2[dummy/0])"
    by (simp del: lift_subst add: lift_subst_dummy lift_eta_expand)
  moreover from u1 par_eta_refl have "u1[dummy/0] \<Rightarrow>\<^sub>\<eta> u1''[dummy/0]"
    by (rule par_eta_subst)
  moreover from u2 par_eta_refl have "u2[dummy/0] \<Rightarrow>\<^sub>\<eta> u2''[dummy/0]"
    by (rule par_eta_subst)
  ultimately show ?case using eta s'
    by (simp only: subst.simps dB.simps) blast
next
  case var thus ?case by simp
next
  case abs thus ?case by simp
qed

theorem par_eta_elim_abs: assumes eta: "t \<Rightarrow>\<^sub>\<eta> t'"
  shows "\<And>u'. t' = Abs u' \<Longrightarrow>
    \<exists>u k. t = eta_expand k (Abs u) \<and> u \<Rightarrow>\<^sub>\<eta> u'" using eta
proof induct
  case (abs s t)
  have "Abs s = eta_expand 0 (Abs s)" by simp
  with abs show ?case by blast
next
  case (eta dummy s s')
  then obtain u'' where s': "s' = Abs u''"
    by (cases s') (auto simp add: subst_Var free_par_eta [symmetric] split: split_if_asm)
  then have "\<exists>u k. s = eta_expand k (Abs u) \<and> u \<Rightarrow>\<^sub>\<eta> u''" by (rule eta)
  then obtain u k where s: "s = eta_expand k (Abs u)" and u: "u \<Rightarrow>\<^sub>\<eta> u''" by iprover
  from eta u s' have "\<not> free u (Suc 0)"
    by (simp del: free_par_eta add: free_par_eta [symmetric])
  with s have "Abs (s \<degree> Var 0) = eta_expand (Suc k) (Abs (u[lift dummy 0/Suc 0]))"
    by (simp del: lift_subst add: lift_eta_expand lift_subst_dummy)
  moreover from u par_eta_refl have "u[lift dummy 0/Suc 0] \<Rightarrow>\<^sub>\<eta> u''[lift dummy 0/Suc 0]"
    by (rule par_eta_subst)
  ultimately show ?case using eta s' by fastsimp
next
  case var thus ?case by simp
next
  case app thus ?case by simp
qed


subsection {* Eta-postponement theorem *}

text {*
Based on a proof by Masako Takahashi \cite{Takahashi-IandC}.
*}

theorem par_eta_beta: "\<And>s u. s \<Rightarrow>\<^sub>\<eta> t \<Longrightarrow> t => u \<Longrightarrow> \<exists>t'. s => t' \<and> t' \<Rightarrow>\<^sub>\<eta> u"
proof (induct t rule: measure_induct [of size, rule_format])
  case (1 t)
  from 1(3)
  show ?case
  proof cases
    case (var n)
    with 1 show ?thesis
      by (auto intro: par_beta_refl)
  next
    case (abs r' r'')
    with 1 have "s \<Rightarrow>\<^sub>\<eta> Abs r'" by simp
    then obtain r k where s: "s = eta_expand k (Abs r)" and rr: "r \<Rightarrow>\<^sub>\<eta> r'"
      by (blast dest: par_eta_elim_abs)
    from abs have "size r' < size t" by simp
    with abs(2) rr obtain t' where rt: "r => t'" and t': "t' \<Rightarrow>\<^sub>\<eta> r''"
      by (blast dest: 1)
    with s abs show ?thesis
      by (auto intro: eta_expand_red eta_expand_eta)
  next
    case (app q' q'' r' r'')
    with 1 have "s \<Rightarrow>\<^sub>\<eta> q' \<degree> r'" by simp
    then obtain q r k where s: "s = eta_expand k (q \<degree> r)"
      and qq: "q \<Rightarrow>\<^sub>\<eta> q'" and rr: "r \<Rightarrow>\<^sub>\<eta> r'"
      by (blast dest: par_eta_elim_app [OF _ refl])
    from app have "size q' < size t" and "size r' < size t" by simp_all
    with app(2,3) qq rr obtain t' t'' where "q => t'" and
      "t' \<Rightarrow>\<^sub>\<eta> q''" and "r => t''" and "t'' \<Rightarrow>\<^sub>\<eta> r''"
      by (blast dest: 1)
    with s app show ?thesis
      by (fastsimp intro: eta_expand_red eta_expand_eta)
  next
    case (beta q' q'' r' r'')
    with 1 have "s \<Rightarrow>\<^sub>\<eta> Abs q' \<degree> r'" by simp
    then obtain q r k k' where s: "s = eta_expand k (eta_expand k' (Abs q) \<degree> r)"
      and qq: "q \<Rightarrow>\<^sub>\<eta> q'" and rr: "r \<Rightarrow>\<^sub>\<eta> r'"
      by (blast dest: par_eta_elim_app par_eta_elim_abs)
    from beta have "size q' < size t" and "size r' < size t" by simp_all
    with beta(2,3) qq rr obtain t' t'' where "q => t'" and
      "t' \<Rightarrow>\<^sub>\<eta> q''" and "r => t''" and "t'' \<Rightarrow>\<^sub>\<eta> r''"
      by (blast dest: 1)
    with s beta show ?thesis
      by (auto intro: eta_expand_red eta_expand_beta eta_expand_eta par_eta_subst)
  qed
qed

theorem eta_postponement': assumes eta: "s -e>> t"
  shows "\<And>u. t => u \<Longrightarrow> \<exists>t'. s => t' \<and> t' -e>> u"
  using eta [simplified rtrancl_subset
    [OF eta_subset_par_eta par_eta_subset_eta, symmetric]]
proof induct
  case 1
  thus ?case by blast
next
  case (2 s' s'' s''')
  from 2 obtain t' where s': "s' => t'" and t': "t' \<Rightarrow>\<^sub>\<eta> s'''"
    by (auto dest: par_eta_beta)
  from s' obtain t'' where s: "s => t''" and t'': "t'' -e>> t'"
    by (blast dest: 2)
  from par_eta_subset_eta t' have "t' -e>> s'''" ..
  with t'' have "t'' -e>> s'''" by (rule rtrancl_trans)
  with s show ?case by iprover
qed

theorem eta_postponement:
  assumes st: "(s, t) \<in> (beta \<union> eta)\<^sup>*"
  shows "(s, t) \<in> eta\<^sup>* O beta\<^sup>*" using st
proof induct
  case 1
  show ?case by blast
next
  case (2 s' s'')
  from 2(3) obtain t' where s: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and t': "t' -e>> s'" by blast
  from 2(2) show ?case
  proof
    assume "s' -> s''"
    with beta_subset_par_beta have "s' => s''" ..
    with t' obtain t'' where st: "t' => t''" and tu: "t'' -e>> s''"
      by (auto dest: eta_postponement')
    from par_beta_subset_beta st have "t' \<rightarrow>\<^sub>\<beta>\<^sup>* t''" ..
    with s have "s \<rightarrow>\<^sub>\<beta>\<^sup>* t''" by (rule rtrancl_trans)
    thus ?thesis using tu ..
  next
    assume "s' -e> s''"
    with t' have "t' -e>> s''" ..
    with s show ?thesis ..
  qed
qed

end
