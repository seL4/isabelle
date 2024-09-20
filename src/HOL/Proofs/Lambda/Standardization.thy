(*  Title:      HOL/Proofs/Lambda/Standardization.thy
    Author:     Stefan Berghofer
    Copyright   2005 TU Muenchen
*)

section \<open>Standardization\<close>

theory Standardization
imports NormalForm
begin

text \<open>
Based on lecture notes by Ralph Matthes \<^cite>\<open>"Matthes-ESSLLI2000"\<close>,
original proof idea due to Ralph Loader \<^cite>\<open>Loader1998\<close>.
\<close>


subsection \<open>Standard reduction relation\<close>

declare listrel_mono [mono_set]

inductive
  sred :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>s\<close> 50)
  and sredlist :: "dB list \<Rightarrow> dB list \<Rightarrow> bool"  (infixl \<open>[\<rightarrow>\<^sub>s]\<close> 50)
where
  "s [\<rightarrow>\<^sub>s] t \<equiv> listrelp (\<rightarrow>\<^sub>s) s t"
| Var: "rs [\<rightarrow>\<^sub>s] rs' \<Longrightarrow> Var x \<degree>\<degree> rs \<rightarrow>\<^sub>s Var x \<degree>\<degree> rs'"
| Abs: "r \<rightarrow>\<^sub>s r' \<Longrightarrow> ss [\<rightarrow>\<^sub>s] ss' \<Longrightarrow> Abs r \<degree>\<degree> ss \<rightarrow>\<^sub>s Abs r' \<degree>\<degree> ss'"
| Beta: "r[s/0] \<degree>\<degree> ss \<rightarrow>\<^sub>s t \<Longrightarrow> Abs r \<degree> s \<degree>\<degree> ss \<rightarrow>\<^sub>s t"

lemma refl_listrelp: "\<forall>x\<in>set xs. R x x \<Longrightarrow> listrelp R xs xs"
  by (induct xs) (auto intro: listrelp.intros)

lemma refl_sred: "t \<rightarrow>\<^sub>s t"
  by (induct t rule: Apps_dB_induct) (auto intro: refl_listrelp sred.intros)

lemma refl_sreds: "ts [\<rightarrow>\<^sub>s] ts"
  by (simp add: refl_sred refl_listrelp)

lemma listrelp_conj1: "listrelp (\<lambda>x y. R x y \<and> S x y) x y \<Longrightarrow> listrelp R x y"
  by (erule listrelp.induct) (auto intro: listrelp.intros)

lemma listrelp_conj2: "listrelp (\<lambda>x y. R x y \<and> S x y) x y \<Longrightarrow> listrelp S x y"
  by (erule listrelp.induct) (auto intro: listrelp.intros)

lemma listrelp_app:
  assumes xsys: "listrelp R xs ys"
  shows "listrelp R xs' ys' \<Longrightarrow> listrelp R (xs @ xs') (ys @ ys')" using xsys
  by (induct arbitrary: xs' ys') (auto intro: listrelp.intros)

lemma lemma1:
  assumes r: "r \<rightarrow>\<^sub>s r'" and s: "s \<rightarrow>\<^sub>s s'"
  shows "r \<degree> s \<rightarrow>\<^sub>s r' \<degree> s'" using r
proof induct
  case (Var rs rs' x)
  then have "rs [\<rightarrow>\<^sub>s] rs'" by (rule listrelp_conj1)
  moreover have "[s] [\<rightarrow>\<^sub>s] [s']" by (iprover intro: s listrelp.intros)
  ultimately have "rs @ [s] [\<rightarrow>\<^sub>s] rs' @ [s']" by (rule listrelp_app)
  hence "Var x \<degree>\<degree> (rs @ [s]) \<rightarrow>\<^sub>s Var x \<degree>\<degree> (rs' @ [s'])" by (rule sred.Var)
  thus ?case by (simp only: app_last)
next
  case (Abs r r' ss ss')
  from Abs(3) have "ss [\<rightarrow>\<^sub>s] ss'" by (rule listrelp_conj1)
  moreover have "[s] [\<rightarrow>\<^sub>s] [s']" by (iprover intro: s listrelp.intros)
  ultimately have "ss @ [s] [\<rightarrow>\<^sub>s] ss' @ [s']" by (rule listrelp_app)
  with \<open>r \<rightarrow>\<^sub>s r'\<close> have "Abs r \<degree>\<degree> (ss @ [s]) \<rightarrow>\<^sub>s Abs r' \<degree>\<degree> (ss' @ [s'])"
    by (rule sred.Abs)
  thus ?case by (simp only: app_last)
next
  case (Beta r u ss t)
  hence "r[u/0] \<degree>\<degree> (ss @ [s]) \<rightarrow>\<^sub>s t \<degree> s'" by (simp only: app_last)
  hence "Abs r \<degree> u \<degree>\<degree> (ss @ [s]) \<rightarrow>\<^sub>s t \<degree> s'" by (rule sred.Beta)
  thus ?case by (simp only: app_last)
qed

lemma lemma1':
  assumes ts: "ts [\<rightarrow>\<^sub>s] ts'"
  shows "r \<rightarrow>\<^sub>s r' \<Longrightarrow> r \<degree>\<degree> ts \<rightarrow>\<^sub>s r' \<degree>\<degree> ts'" using ts
  by (induct arbitrary: r r') (auto intro: lemma1)

lemma lemma2_1:
  assumes beta: "t \<rightarrow>\<^sub>\<beta> u"
  shows "t \<rightarrow>\<^sub>s u" using beta
proof induct
  case (beta s t)
  have "Abs s \<degree> t \<degree>\<degree> [] \<rightarrow>\<^sub>s s[t/0] \<degree>\<degree> []" by (iprover intro: sred.Beta refl_sred)
  thus ?case by simp
next
  case (appL s t u)
  thus ?case by (iprover intro: lemma1 refl_sred)
next
  case (appR s t u)
  thus ?case by (iprover intro: lemma1 refl_sred)
next
  case (abs s t)
  hence "Abs s \<degree>\<degree> [] \<rightarrow>\<^sub>s Abs t \<degree>\<degree> []" by (iprover intro: sred.Abs listrelp.Nil)
  thus ?case by simp
qed

lemma listrelp_betas:
  assumes ts: "listrelp (\<rightarrow>\<^sub>\<beta>\<^sup>*) ts ts'"
  shows "\<And>t t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> t \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<degree>\<degree> ts'" using ts
  by induct auto

lemma lemma2_2:
  assumes t: "t \<rightarrow>\<^sub>s u"
  shows "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" using t
  by induct (auto dest: listrelp_conj2
    intro: listrelp_betas apps_preserves_beta converse_rtranclp_into_rtranclp)

lemma sred_lift:
  assumes s: "s \<rightarrow>\<^sub>s t"
  shows "lift s i \<rightarrow>\<^sub>s lift t i" using s
proof (induct arbitrary: i)
  case (Var rs rs' x)
  hence "map (\<lambda>t. lift t i) rs [\<rightarrow>\<^sub>s] map (\<lambda>t. lift t i) rs'"
    by induct (auto intro: listrelp.intros)
  thus ?case by (cases "x < i") (auto intro: sred.Var)
next
  case (Abs r r' ss ss')
  from Abs(3) have "map (\<lambda>t. lift t i) ss [\<rightarrow>\<^sub>s] map (\<lambda>t. lift t i) ss'"
    by induct (auto intro: listrelp.intros)
  thus ?case by (auto intro: sred.Abs Abs)
next
  case (Beta r s ss t)
  thus ?case by (auto intro: sred.Beta)
qed

lemma lemma3:
  assumes r: "r \<rightarrow>\<^sub>s r'"
  shows "s \<rightarrow>\<^sub>s s' \<Longrightarrow> r[s/x] \<rightarrow>\<^sub>s r'[s'/x]" using r
proof (induct arbitrary: s s' x)
  case (Var rs rs' y)
  hence "map (\<lambda>t. t[s/x]) rs [\<rightarrow>\<^sub>s] map (\<lambda>t. t[s'/x]) rs'"
    by induct (auto intro: listrelp.intros Var)
  moreover have "Var y[s/x] \<rightarrow>\<^sub>s Var y[s'/x]"
  proof (cases "y < x")
    case True thus ?thesis by simp (rule refl_sred)
  next
    case False
    thus ?thesis
      by (cases "y = x") (auto simp add: Var intro: refl_sred)
  qed
  ultimately show ?case by simp (rule lemma1')
next
  case (Abs r r' ss ss')
  from Abs(4) have "lift s 0 \<rightarrow>\<^sub>s lift s' 0" by (rule sred_lift)
  hence "r[lift s 0/Suc x] \<rightarrow>\<^sub>s r'[lift s' 0/Suc x]" by (fast intro: Abs.hyps)
  moreover from Abs(3) have "map (\<lambda>t. t[s/x]) ss [\<rightarrow>\<^sub>s] map (\<lambda>t. t[s'/x]) ss'"
    by induct (auto intro: listrelp.intros Abs)
  ultimately show ?case by simp (rule sred.Abs)
next
  case (Beta r u ss t)
  thus ?case by (auto simp add: subst_subst intro: sred.Beta)
qed

lemma lemma4_aux:
  assumes rs: "listrelp (\<lambda>t u. t \<rightarrow>\<^sub>s u \<and> (\<forall>r. u \<rightarrow>\<^sub>\<beta> r \<longrightarrow> t \<rightarrow>\<^sub>s r)) rs rs'"
  shows "rs' => ss \<Longrightarrow> rs [\<rightarrow>\<^sub>s] ss" using rs
proof (induct arbitrary: ss)
  case Nil
  thus ?case by cases (auto intro: listrelp.Nil)
next
  case (Cons x y xs ys)
  note Cons' = Cons
  show ?case
  proof (cases ss)
    case Nil with Cons show ?thesis by simp
  next
    case (Cons y' ys')
    hence ss: "ss = y' # ys'" by simp
    from Cons Cons' have "y \<rightarrow>\<^sub>\<beta> y' \<and> ys' = ys \<or> y' = y \<and> ys => ys'" by simp
    hence "x # xs [\<rightarrow>\<^sub>s] y' # ys'"
    proof
      assume H: "y \<rightarrow>\<^sub>\<beta> y' \<and> ys' = ys"
      with Cons' have "x \<rightarrow>\<^sub>s y'" by blast
      moreover from Cons' have "xs [\<rightarrow>\<^sub>s] ys" by (iprover dest: listrelp_conj1)
      ultimately have "x # xs [\<rightarrow>\<^sub>s] y' # ys" by (rule listrelp.Cons)
      with H show ?thesis by simp
    next
      assume H: "y' = y \<and> ys => ys'"
      with Cons' have "x \<rightarrow>\<^sub>s y'" by blast
      moreover from H have "xs [\<rightarrow>\<^sub>s] ys'" by (blast intro: Cons')
      ultimately show ?thesis by (rule listrelp.Cons)
    qed
    with ss show ?thesis by simp
  qed
qed

lemma lemma4:
  assumes r: "r \<rightarrow>\<^sub>s r'"
  shows "r' \<rightarrow>\<^sub>\<beta> r'' \<Longrightarrow> r \<rightarrow>\<^sub>s r''" using r
proof (induct arbitrary: r'')
  case (Var rs rs' x)
  then obtain ss where rs: "rs' => ss" and r'': "r'' = Var x \<degree>\<degree> ss"
    by (blast dest: head_Var_reduction)
  from Var(1) rs have "rs [\<rightarrow>\<^sub>s] ss" by (rule lemma4_aux)
  hence "Var x \<degree>\<degree> rs \<rightarrow>\<^sub>s Var x \<degree>\<degree> ss" by (rule sred.Var)
  with r'' show ?case by simp
next
  case (Abs r r' ss ss')
  from \<open>Abs r' \<degree>\<degree> ss' \<rightarrow>\<^sub>\<beta> r''\<close> show ?case
  proof
    fix s
    assume r'': "r'' = s \<degree>\<degree> ss'"
    assume "Abs r' \<rightarrow>\<^sub>\<beta> s"
    then obtain r''' where s: "s = Abs r'''" and r''': "r' \<rightarrow>\<^sub>\<beta> r'''" by cases auto
    from r''' have "r \<rightarrow>\<^sub>s r'''" by (blast intro: Abs)
    moreover from Abs have "ss [\<rightarrow>\<^sub>s] ss'" by (iprover dest: listrelp_conj1)
    ultimately have "Abs r \<degree>\<degree> ss \<rightarrow>\<^sub>s Abs r''' \<degree>\<degree> ss'" by (rule sred.Abs)
    with r'' s show "Abs r \<degree>\<degree> ss \<rightarrow>\<^sub>s r''" by simp
  next
    fix rs'
    assume "ss' => rs'"
    with Abs(3) have "ss [\<rightarrow>\<^sub>s] rs'" by (rule lemma4_aux)
    with \<open>r \<rightarrow>\<^sub>s r'\<close> have "Abs r \<degree>\<degree> ss \<rightarrow>\<^sub>s Abs r' \<degree>\<degree> rs'" by (rule sred.Abs)
    moreover assume "r'' = Abs r' \<degree>\<degree> rs'"
    ultimately show "Abs r \<degree>\<degree> ss \<rightarrow>\<^sub>s r''" by simp
  next
    fix t u' us'
    assume "ss' = u' # us'"
    with Abs(3) obtain u us where
      ss: "ss = u # us" and u: "u \<rightarrow>\<^sub>s u'" and us: "us [\<rightarrow>\<^sub>s] us'"
      by cases (auto dest!: listrelp_conj1)
    have "r[u/0] \<rightarrow>\<^sub>s r'[u'/0]" using Abs(1) and u by (rule lemma3)
    with us have "r[u/0] \<degree>\<degree> us \<rightarrow>\<^sub>s r'[u'/0] \<degree>\<degree> us'" by (rule lemma1')
    hence "Abs r \<degree> u \<degree>\<degree> us \<rightarrow>\<^sub>s r'[u'/0] \<degree>\<degree> us'" by (rule sred.Beta)
    moreover assume "Abs r' = Abs t" and "r'' = t[u'/0] \<degree>\<degree> us'"
    ultimately show "Abs r \<degree>\<degree> ss \<rightarrow>\<^sub>s r''" using ss by simp
  qed
next
  case (Beta r s ss t)
  show ?case
    by (rule sred.Beta) (rule Beta)+
qed

lemma rtrancl_beta_sred:
  assumes r: "r \<rightarrow>\<^sub>\<beta>\<^sup>* r'"
  shows "r \<rightarrow>\<^sub>s r'" using r
  by induct (iprover intro: refl_sred lemma4)+


subsection \<open>Leftmost reduction and weakly normalizing terms\<close>

inductive
  lred :: "dB \<Rightarrow> dB \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>l\<close> 50)
  and lredlist :: "dB list \<Rightarrow> dB list \<Rightarrow> bool"  (infixl \<open>[\<rightarrow>\<^sub>l]\<close> 50)
where
  "s [\<rightarrow>\<^sub>l] t \<equiv> listrelp (\<rightarrow>\<^sub>l) s t"
| Var: "rs [\<rightarrow>\<^sub>l] rs' \<Longrightarrow> Var x \<degree>\<degree> rs \<rightarrow>\<^sub>l Var x \<degree>\<degree> rs'"
| Abs: "r \<rightarrow>\<^sub>l r' \<Longrightarrow> Abs r \<rightarrow>\<^sub>l Abs r'"
| Beta: "r[s/0] \<degree>\<degree> ss \<rightarrow>\<^sub>l t \<Longrightarrow> Abs r \<degree> s \<degree>\<degree> ss \<rightarrow>\<^sub>l t"

lemma lred_imp_sred:
  assumes lred: "s \<rightarrow>\<^sub>l t"
  shows "s \<rightarrow>\<^sub>s t" using lred
proof induct
  case (Var rs rs' x)
  then have "rs [\<rightarrow>\<^sub>s] rs'"
    by induct (iprover intro: listrelp.intros)+
  then show ?case by (rule sred.Var)
next
  case (Abs r r')
  from \<open>r \<rightarrow>\<^sub>s r'\<close>
  have "Abs r \<degree>\<degree> [] \<rightarrow>\<^sub>s Abs r' \<degree>\<degree> []" using listrelp.Nil
    by (rule sred.Abs)
  then show ?case by simp
next
  case (Beta r s ss t)
  from \<open>r[s/0] \<degree>\<degree> ss \<rightarrow>\<^sub>s t\<close>
  show ?case by (rule sred.Beta)
qed

inductive WN :: "dB => bool"
  where
    Var: "listsp WN rs \<Longrightarrow> WN (Var n \<degree>\<degree> rs)"
  | Lambda: "WN r \<Longrightarrow> WN (Abs r)"
  | Beta: "WN ((r[s/0]) \<degree>\<degree> ss) \<Longrightarrow> WN ((Abs r \<degree> s) \<degree>\<degree> ss)"

lemma listrelp_imp_listsp1:
  assumes H: "listrelp (\<lambda>x y. P x) xs ys"
  shows "listsp P xs" using H
  by induct auto

lemma listrelp_imp_listsp2:
  assumes H: "listrelp (\<lambda>x y. P y) xs ys"
  shows "listsp P ys" using H
  by induct auto

lemma lemma5:
  assumes lred: "r \<rightarrow>\<^sub>l r'"
  shows "WN r" and "NF r'" using lred
  by induct
    (iprover dest: listrelp_conj1 listrelp_conj2
     listrelp_imp_listsp1 listrelp_imp_listsp2 intro: WN.intros
     NF.intros [simplified listall_listsp_eq])+

lemma lemma6:
  assumes wn: "WN r"
  shows "\<exists>r'. r \<rightarrow>\<^sub>l r'" using wn
proof induct
  case (Var rs n)
  then have "\<exists>rs'. rs [\<rightarrow>\<^sub>l] rs'"
    by induct (iprover intro: listrelp.intros)+
  then show ?case by (iprover intro: lred.Var)
qed (iprover intro: lred.intros)+

lemma lemma7:
  assumes r: "r \<rightarrow>\<^sub>s r'"
  shows "NF r' \<Longrightarrow> r \<rightarrow>\<^sub>l r'" using r
proof induct
  case (Var rs rs' x)
  from \<open>NF (Var x \<degree>\<degree> rs')\<close> have "listall NF rs'"
    by cases simp_all
  with Var(1) have "rs [\<rightarrow>\<^sub>l] rs'"
  proof induct
    case Nil
    show ?case by (rule listrelp.Nil)
  next
    case (Cons x y xs ys)
    hence "x \<rightarrow>\<^sub>l y" and "xs [\<rightarrow>\<^sub>l] ys" by simp_all
    thus ?case by (rule listrelp.Cons)
  qed
  thus ?case by (rule lred.Var)
next
  case (Abs r r' ss ss')
  from \<open>NF (Abs r' \<degree>\<degree> ss')\<close>
  have ss': "ss' = []" by (rule Abs_NF)
  from Abs(3) have ss: "ss = []" using ss'
    by cases simp_all
  from ss' Abs have "NF (Abs r')" by simp
  hence "NF r'" by cases simp_all
  with Abs have "r \<rightarrow>\<^sub>l r'" by simp
  hence "Abs r \<rightarrow>\<^sub>l Abs r'" by (rule lred.Abs)
  with ss ss' show ?case by simp
next
  case (Beta r s ss t)
  hence "r[s/0] \<degree>\<degree> ss \<rightarrow>\<^sub>l t" by simp
  thus ?case by (rule lred.Beta)
qed

lemma WN_eq: "WN t = (\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t')"
proof
  assume "WN t"
  then have "\<exists>t'. t \<rightarrow>\<^sub>l t'" by (rule lemma6)
  then obtain t' where t': "t \<rightarrow>\<^sub>l t'" ..
  then have NF: "NF t'" by (rule lemma5)
  from t' have "t \<rightarrow>\<^sub>s t'" by (rule lred_imp_sred)
  then have "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by (rule lemma2_2)
  with NF show "\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'" by iprover
next
  assume "\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'"
  then obtain t' where t': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and NF: "NF t'"
    by iprover
  from t' have "t \<rightarrow>\<^sub>s t'" by (rule rtrancl_beta_sred)
  then have "t \<rightarrow>\<^sub>l t'" using NF by (rule lemma7)
  then show "WN t" by (rule lemma5)
qed

end
