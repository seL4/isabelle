
theory class 
imports "../nominal" 
begin

atom_decl name coname

section {* Term-Calculus from my PHD *}

nominal_datatype trm = Ax  "name" "coname"
                 | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"  ("ImpR [_].[_]._ _" [100,100,100,100] 100)
                 | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"("ImpL [_]._ [_]._ _" [100,100,100,100,100] 100)
                 | Cut "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"        ("Cut [_]._ [_]._" [100,100,100,100] 100)

lemma trm_induct_aux:
  fixes P :: "trm \<Rightarrow> 'a \<Rightarrow> bool"
  and   f1 :: "'a \<Rightarrow> name set"
  and   f2 :: "'a \<Rightarrow> coname set"
  assumes fs1: "\<And>x. finite (f1 x)"
      and fs2: "\<And>x. finite (f2 x)"
      and h1: "\<And>k x a. P (Ax x a) k"  
      and h2: "\<And>k x a t b. x\<notin>f1 k \<Longrightarrow> a\<notin>f2 k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (ImpR [x].[a].t b) k" 
      and h3: "\<And>k a t1 x t2 y. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (ImpL [a].t1 [x].t2 y) k" 
      and h4: "\<And>k a t1 x t2. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (Cut [a].t1 [x].t2) k" 
  shows "\<forall>(pi1::name prm) (pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k"
proof (induct rule: trm.induct_weak)
  case (goal1 a)
  show ?case using h1 by simp
next
  case (goal2 x a t b)
  assume i1: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k" 
  show ?case 
  proof (intro strip, simp add: abs_perm perm_dj)
    fix pi1::"name prm" and pi2::"coname prm" and k::"'a"
    have "\<exists>u::name. u\<sharp>(f1 k,pi1\<bullet>x,pi1\<bullet>(pi2\<bullet>t))"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
               at_fin_set_supp[OF at_name_inst, OF fs1] fs1)
    then obtain u::"name" 
      where f1: "u\<noteq>(pi1\<bullet>x)" and f2: "u\<sharp>(f1 k)" and f3: "u\<sharp>(pi1\<bullet>(pi2\<bullet>t))" 
      by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
    have "\<exists>c::coname. c\<sharp>(f2 k,pi2\<bullet>a,pi1\<bullet>(pi2\<bullet>t))"
      by (rule at_exists_fresh[OF at_coname_inst], simp add: supp_prod fs_coname1 
               at_fin_set_supp[OF at_coname_inst, OF fs2] fs2)
    then obtain c::"coname" 
      where e1: "c\<noteq>(pi2\<bullet>a)" and e2: "c\<sharp>(f2 k)" and e3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t))" 
      by (auto simp add: fresh_prod at_fresh[OF at_coname_inst])
    have g: "ImpR [u].[c].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>([(c,pi2\<bullet>a)]\<bullet>(pi2\<bullet>t)))) (pi2\<bullet>b)
            =ImpR [(pi1\<bullet>x)].[(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t)) (pi2\<bullet>b)" using f1 f3 e1 e3
      apply (auto simp add: ImpR_inject alpha abs_fresh abs_perm perm_dj,
                  simp add: dj_cp[OF cp_name_coname_inst, OF dj_coname_name])
      apply(simp add:  pt_fresh_left_ineq[OF pt_name_inst, OF pt_name_inst, 
                                          OF at_name_inst, OF cp_name_coname_inst] perm_dj)
      done
    from i1 have "\<forall>k. P (([(u,pi1\<bullet>x)]@pi1)\<bullet>(([(c,pi2\<bullet>a)]@pi2)\<bullet>t)) k" by force
    hence i1b: "\<forall>k. P ([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>([(c,pi2\<bullet>a)]\<bullet>(pi2\<bullet>t)))) k" 
      by (simp add: pt_name2[symmetric] pt_coname2[symmetric])
    with h2 f2 e2 have "P (ImpR [u].[c].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>([(c,pi2\<bullet>a)]\<bullet>(pi2\<bullet>t)))) (pi2\<bullet>b)) k" 
      by (simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs1]
                                   at_fin_set_supp[OF at_coname_inst, OF fs2])
    with g show "P (ImpR [(pi1\<bullet>x)].[(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t)) (pi2\<bullet>b)) k" by simp 
  qed
next
  case (goal3 a t1 x t2 y)
  assume i1: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t1)) k" 
  and    i2: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t2)) k"
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix pi1::"name prm" and pi2::"coname prm" and k::"'a"
    have "\<exists>u::name. u\<sharp>(f1 k,pi1\<bullet>x,pi1\<bullet>(pi2\<bullet>t2))"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
               at_fin_set_supp[OF at_name_inst, OF fs1] fs1)
    then obtain u::"name" 
      where f1: "u\<noteq>(pi1\<bullet>x)" and f2: "u\<sharp>(f1 k)" and f3: "u\<sharp>(pi1\<bullet>(pi2\<bullet>t2))" 
      by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
    have "\<exists>c::coname. c\<sharp>(f2 k,pi2\<bullet>a,pi1\<bullet>(pi2\<bullet>t1))"
      by (rule at_exists_fresh[OF at_coname_inst], simp add: supp_prod fs_coname1 
               at_fin_set_supp[OF at_coname_inst, OF fs2] fs2)
    then obtain c::"coname" 
      where e1: "c\<noteq>(pi2\<bullet>a)" and e2: "c\<sharp>(f2 k)" and e3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t1))" 
      by (auto simp add: fresh_prod at_fresh[OF at_coname_inst])
    have g: "ImpL [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) (pi1\<bullet>y)
            =ImpL [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2)) (pi1\<bullet>y)" using f1 f3 e1 e3
      by (simp add: ImpL_inject alpha abs_fresh abs_perm perm_dj)
    from i2 have "\<forall>k. P (([(u,pi1\<bullet>x)]@pi1)\<bullet>(pi2\<bullet>t2)) k" by force
    hence i2b: "\<forall>k. P ([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) k" 
      by (simp add: pt_name2[symmetric])
    from i1 have "\<forall>k. P (pi1\<bullet>(([(c,pi2\<bullet>a)]@pi2)\<bullet>t1)) k" by force
    hence i1b: "\<forall>k. P ([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) k" 
      by (simp add: pt_coname2[symmetric] dj_cp[OF cp_name_coname_inst, OF dj_coname_name])
    from h3 f2 e2 i1b i2b 
    have "P (ImpL [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) (pi1\<bullet>y)) k" 
      by (simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs1]
                                   at_fin_set_supp[OF at_coname_inst, OF fs2])
    with g show "P (ImpL [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2)) (pi1\<bullet>y)) k" by simp 
  qed
next
  case (goal4 a t1 x t2)
  assume i1: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t1)) k" 
  and    i2: "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t2)) k"
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix pi1::"name prm" and pi2::"coname prm" and k::"'a"
    have "\<exists>u::name. u\<sharp>(f1 k,pi1\<bullet>x,pi1\<bullet>(pi2\<bullet>t2))"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
               at_fin_set_supp[OF at_name_inst, OF fs1] fs1)
    then obtain u::"name" 
      where f1: "u\<noteq>(pi1\<bullet>x)" and f2: "u\<sharp>(f1 k)" and f3: "u\<sharp>(pi1\<bullet>(pi2\<bullet>t2))" 
      by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
    have "\<exists>c::coname. c\<sharp>(f2 k,pi2\<bullet>a,pi1\<bullet>(pi2\<bullet>t1))"
      by (rule at_exists_fresh[OF at_coname_inst], simp add: supp_prod fs_coname1 
               at_fin_set_supp[OF at_coname_inst, OF fs2] fs2)
    then obtain c::"coname" 
      where e1: "c\<noteq>(pi2\<bullet>a)" and e2: "c\<sharp>(f2 k)" and e3: "c\<sharp>(pi1\<bullet>(pi2\<bullet>t1))" 
      by (auto simp add: fresh_prod at_fresh[OF at_coname_inst])
    have g: "Cut [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2)))
            =Cut [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2))" using f1 f3 e1 e3
      by (simp add: Cut_inject alpha abs_fresh abs_perm perm_dj)
    from i2 have "\<forall>k. P (([(u,pi1\<bullet>x)]@pi1)\<bullet>(pi2\<bullet>t2)) k" by force
    hence i2b: "\<forall>k. P ([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2))) k" 
      by (simp add: pt_name2[symmetric])
    from i1 have "\<forall>k. P (pi1\<bullet>(([(c,pi2\<bullet>a)]@pi2)\<bullet>t1)) k" by force
    hence i1b: "\<forall>k. P ([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) k" 
      by (simp add: pt_coname2[symmetric] dj_cp[OF cp_name_coname_inst, OF dj_coname_name])
    from h3 f2 e2 i1b i2b 
    have "P (Cut [c].([(c,pi2\<bullet>a)]\<bullet>(pi1\<bullet>(pi2\<bullet>t1))) [u].([(u,pi1\<bullet>x)]\<bullet>(pi1\<bullet>(pi2\<bullet>t2)))) k" 
      by (simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs1]
                                   at_fin_set_supp[OF at_coname_inst, OF fs2])
    with g show "P (Cut [(pi2\<bullet>a)].(pi1\<bullet>(pi2\<bullet>t1)) [(pi1\<bullet>x)].(pi1\<bullet>(pi2\<bullet>t2))) k" by simp 
  qed
qed

lemma trm_induct'[case_names Ax ImpR ImpL Cut]: 
  fixes P :: "trm \<Rightarrow> 'a \<Rightarrow> bool"
  and   f1 :: "'a \<Rightarrow> name set"
  and   f2 :: "'a \<Rightarrow> coname set"
  assumes fs1: "\<And>x. finite (f1 x)"
      and fs2: "\<And>x. finite (f2 x)"
      and h1: "\<And>k x a. P (Ax x a) k"  
      and h2: "\<And>k x a t b. x\<notin>f1 k \<Longrightarrow> a\<notin>f2 k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (ImpR [x].[a].t b) k" 
      and h3: "\<And>k a t1 x t2 y. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (ImpL [a].t1 [x].t2 y) k" 
      and h4: "\<And>k a t1 x t2. a\<notin>f2 k \<Longrightarrow> x\<notin>f1 k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (Cut [a].t1 [x].t2) k" 
  shows  "P t k"
proof -
  have "\<forall>(pi1::name prm)(pi2::coname prm) k. P (pi1\<bullet>(pi2\<bullet>t)) k"
  using fs1 fs2 h1 h2 h3 h4 by (rule trm_induct_aux, auto)
  hence "P (([]::name prm)\<bullet>(([]::coname prm)\<bullet>t)) k" by blast
  thus "P t k" by simp
qed

lemma trm_induct[case_names Ax ImpR ImpL Cut]: 
  fixes P :: "trm \<Rightarrow> ('a::{fs_name,fs_coname}) \<Rightarrow> bool"
  assumes h1: "\<And>k x a. P (Ax x a) k"  
      and h2: "\<And>k x a t b. x\<sharp>k \<Longrightarrow> a\<sharp>k \<Longrightarrow> (\<forall>l. P t l) \<Longrightarrow> P (ImpR [x].[a].t b) k" 
      and h3: "\<And>k a t1 x t2 y. a\<sharp>k \<Longrightarrow> x\<sharp>k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (ImpL [a].t1 [x].t2 y) k" 
      and h4: "\<And>k a t1 x t2. a\<sharp>k \<Longrightarrow> x\<sharp>k \<Longrightarrow> (\<forall>l. P t1 l) \<Longrightarrow> (\<forall>l. P t2 l) 
               \<Longrightarrow> P (Cut [a].t1 [x].t2) k" 
  shows  "P t k"
by (rule trm_induct'[of "\<lambda>x. ((supp x)::name set)" "\<lambda>x. ((supp x)::coname set)" "P"], 
    simp_all add: fs_name1 fs_coname1 fresh_def[symmetric], auto intro: h1 h2 h3 h4)
