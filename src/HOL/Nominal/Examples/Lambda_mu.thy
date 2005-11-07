
theory lambda_mu 
imports "../nominal" 
begin

section {* Mu-Calculus from Gavin's cilmu-Paper*}

atom_decl var mvar

nominal_datatype trm = Var   "var" 
                     | Lam  "\<guillemotleft>var\<guillemotright>trm"   ("Lam [_]._" [100,100] 100)
                     | App  "trm" "trm" 
                     | Pss  "mvar" "trm"
                     | Act  "\<guillemotleft>mvar\<guillemotright>trm"  ("Act [_]._" [100,100] 100)

section {* strong induction principle *}

lemma trm_induct_aux:
  fixes P :: "trm \<Rightarrow> 'a \<Rightarrow> bool"
  and   f1 :: "'a \<Rightarrow> var set"
  and   f2 :: "'a \<Rightarrow> mvar set"
  assumes fs1: "\<And>x. finite (f1 x)"
      and fs2: "\<And>x. finite (f2 x)"
      and h1: "\<And>k x. P (Var x) k"  
      and h2: "\<And>k x t. x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (Lam [x].t) k" 
      and h3: "\<And>k t1 t2. (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) \<Longrightarrow> P (App t1 t2) k" 
      and h4: "\<And>k a t1. (\<forall>l. P t1 l) \<Longrightarrow> P (Pss a t1) k" 
      and h5: "\<And>k a t1. a\<notin>f2 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> P (Act [a].t1) k"
  shows "\<forall>(pi1::var prm) (pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k"
proof (induct rule: trm.induct_weak)
  case (goal1 a)
  show ?case using h1 by simp
next
  case (goal2 x t)
  assume i1: "\<forall>(pi1::var prm)(pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k" 
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix pi1::"var prm" and pi2::"mvar prm" and k::"'a"
    have f: "\<exists>c::var. c\<sharp>(f1 k,pi1\<bullet>(pi2\<bullet>x),pi1\<bullet>(pi2\<bullet>t))"
      by (rule at_exists_fresh[OF at_var_inst], simp add: supp_prod fs_var1 
          at_fin_set_supp[OF at_var_inst, OF fs1] fs1)
    then obtain c::"var" 
      where f1: "c\<noteq>(pi1\<bullet>(pi2\<bullet>x))" and f2: "c\<sharp>(f1 k)" and f3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t))" 
      by (force simp add: fresh_prod at_fresh[OF at_var_inst])
    have g: "Lam [c].([(c,pi1\<bullet>(pi2\<bullet>x))]\<bullet>(pi1\<bullet>(pi2\<bullet>t))) = Lam [(pi1\<bullet>(pi2\<bullet>x))].(pi1\<bullet>(pi2\<bullet>t))" using f1 f3
      by (simp add: trm.inject alpha)
    from i1 have "\<forall>k. P (([(c,pi1\<bullet>(pi2\<bullet>x))]@pi1)\<bullet>(pi2\<bullet>t)) k" by force
    hence i1b: "\<forall>k. P ([(c,pi1\<bullet>(pi2\<bullet>x))]\<bullet>(pi1\<bullet>(pi2\<bullet>t))) k" by (simp add: pt_var2[symmetric])
    with h3 f2 have "P (Lam [c].([(c,pi1\<bullet>(pi2\<bullet>x))]\<bullet>(pi1\<bullet>(pi2\<bullet>t)))) k" 
      by (auto simp add: fresh_def at_fin_set_supp[OF at_var_inst, OF fs1])
    with g show "P (Lam [(pi1\<bullet>(pi2\<bullet>x))].(pi1\<bullet>(pi2\<bullet>t))) k" by simp 
  qed
next 
  case (goal3 t1 t2)
  assume i1: "\<forall>(pi1::var prm)(pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t1)) k" 
  assume i2: "\<forall>(pi1::var prm)(pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t2)) k"
  show ?case 
  proof (intro strip)
    fix pi1::"var prm" and pi2::"mvar prm" and k::"'a"
    from h3 i1 i2 have "P (App (pi1\<bullet>(pi2\<bullet>t1)) (pi1\<bullet>(pi2\<bullet>t2))) k" by force
    thus "P (pi1\<bullet>(pi2\<bullet>(App t1 t2))) k" by simp
  qed
next
  case (goal4 b t)
  assume i1: "\<forall>(pi1::var prm)(pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k" 
  show ?case 
  proof (intro strip)
    fix pi1::"var prm" and pi2::"mvar prm" and k::"'a"
    from h4 i1 have "P (Pss (pi1\<bullet>(pi2\<bullet>b)) (pi1\<bullet>(pi2\<bullet>t))) k" by force
    thus "P (pi1\<bullet>(pi2\<bullet>(Pss b t))) k" by simp
  qed
next
  case (goal5 b t)
  assume i1: "\<forall>(pi1::var prm)(pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k" 
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix pi1::"var prm" and pi2::"mvar prm" and k::"'a"
    have f: "\<exists>c::mvar. c\<sharp>(f2 k,pi1\<bullet>(pi2\<bullet>b),pi1\<bullet>(pi2\<bullet>t))"
      by (rule at_exists_fresh[OF at_mvar_inst], simp add: supp_prod fs_mvar1 
          at_fin_set_supp[OF at_mvar_inst, OF fs2] fs2)
    then obtain c::"mvar" 
      where f1: "c\<noteq>(pi1\<bullet>(pi2\<bullet>b))" and f2: "c\<sharp>(f2 k)" and f3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t))" 
      by (force simp add: fresh_prod at_fresh[OF at_mvar_inst])
    have g: "Act [c].(pi1\<bullet>([(c,pi1\<bullet>(pi2\<bullet>b))]\<bullet>(pi2\<bullet>t))) = Act [(pi1\<bullet>(pi2\<bullet>b))].(pi1\<bullet>(pi2\<bullet>t))" using f1 f3
      by (simp add: trm.inject alpha, simp add: dj_cp[OF cp_mvar_var_inst, OF dj_var_mvar])
    from i1 have "\<forall>k. P (pi1\<bullet>(([(c,pi1\<bullet>(pi2\<bullet>b))]@pi2)\<bullet>t)) k" by force
    hence i1b: "\<forall>k. P (pi1\<bullet>([(c,pi1\<bullet>(pi2\<bullet>b))]\<bullet>(pi2\<bullet>t))) k" by (simp add: pt_mvar2[symmetric])
    with h5 f2 have "P (Act [c].(pi1\<bullet>([(c,pi1\<bullet>(pi2\<bullet>b))]\<bullet>(pi2\<bullet>t)))) k" 
      by (auto simp add: fresh_def at_fin_set_supp[OF at_mvar_inst, OF fs2])
    with g show "P (Act [(pi1\<bullet>(pi2\<bullet>b))].(pi1\<bullet>(pi2\<bullet>t))) k" by simp 
  qed
qed

lemma trm_induct'[case_names Var Lam App Pss Act]:
  fixes P :: "trm \<Rightarrow> 'a \<Rightarrow> bool"
  and   f1 :: "'a \<Rightarrow> var set"
  and   f2 :: "'a \<Rightarrow> mvar set"
  assumes fs1: "\<And>x. finite (f1 x)"
      and fs2: "\<And>x. finite (f2 x)"
      and h1: "\<And>k x. P (Var x) k"  
      and h2: "\<And>k x t. x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (Lam [x].t) k" 
      and h3: "\<And>k t1 t2. (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) \<Longrightarrow> P (App t1 t2) k" 
      and h4: "\<And>k a t1. (\<forall>l. P t1 l) \<Longrightarrow> P (Pss a t1) k" 
      and h5: "\<And>k a t1. a\<notin>f2 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> P (Act [a].t1) k"
  shows "P t k"
proof -
  have "\<forall>(pi1::var prm)(pi2::mvar prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k"
  using fs1 fs2 h1 h2 h3 h4 h5 by (rule trm_induct_aux, auto)
  hence "P (([]::var prm)\<bullet>(([]::mvar prm)\<bullet>t)) k" by blast
  thus "P t k" by simp
qed

lemma trm_induct[case_names Var Lam App Pss Act]: 
  fixes P :: "trm \<Rightarrow> ('a::{fs_var,fs_mvar}) \<Rightarrow> bool"
  assumes h1: "\<And>k x. P (Var x) k"  
      and h2: "\<And>k x t. x\<sharp>k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (Lam [x].t) k" 
      and h3: "\<And>k t1 t2. (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) \<Longrightarrow> P (App t1 t2) k" 
      and h4: "\<And>k a t1. (\<forall>l. P t1 l) \<Longrightarrow> P (Pss a t1) k" 
      and h5: "\<And>k a t1. a\<sharp>k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> P (Act [a].t1) k"
  shows  "P t k"
by (rule trm_induct'[of "\<lambda>x. ((supp x)::var set)" "\<lambda>x. ((supp x)::mvar set)" "P"], 
    simp_all add: fs_var1 fs_mvar1 fresh_def[symmetric], auto intro: h1 h2 h3 h4 h5)
