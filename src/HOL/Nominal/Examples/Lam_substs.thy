
theory lam_substs
imports "../nominal" 
begin

atom_decl name 

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

section {* strong induction principles for lam *}

lemma lam_induct_aux:
  fixes P :: "lam \<Rightarrow> 'a \<Rightarrow> bool"
  and   f :: "'a \<Rightarrow> name set"
  assumes fs: "\<And>x. finite (f x)"
      and h1: "\<And>x a. P (Var  a) x"  
      and h2: "\<And>x t1 t2. (\<forall>z. P t1 z) \<Longrightarrow> (\<forall>z. P t2 z) \<Longrightarrow> P (App t1 t2) x" 
      and h3: "\<And>x a t. a\<notin>f x \<Longrightarrow> (\<forall>z. P t z) \<Longrightarrow> P (Lam [a].t) x"
  shows "\<forall>(pi::name prm) x. P (pi\<bullet>t) x"
proof (induct rule: lam.induct_weak)
  case (Lam a t)
  assume i1: "\<forall>(pi::name prm) x. P (pi\<bullet>t) x" 
  show ?case
  proof (intro strip, simp add: abs_perm)
    fix x::"'a" and pi::"name prm"
    have f: "\<exists>c::name. c\<sharp>(f x,pi\<bullet>a,pi\<bullet>t)"
      by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1 
          at_fin_set_supp[OF at_name_inst, OF fs] fs)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>(f x)" and f3: "c\<sharp>(pi\<bullet>t)" 
      by (force simp add: fresh_prod at_fresh[OF at_name_inst])
    have g: "Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t)) = Lam [(pi\<bullet>a)].(pi\<bullet>t)" using f1 f3
      by (simp add: lam.inject alpha)
    from i1 have "\<forall>x. P (([(c,pi\<bullet>a)]@pi)\<bullet>t) x" by force
    hence i1b: "\<forall>x. P ([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t)) x" by (simp add: pt_name2[symmetric])
    with h3 f2 have "P (Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t))) x" 
      by (auto simp add: fresh_def at_fin_set_supp[OF at_name_inst, OF fs])
    with g show "P (Lam [(pi\<bullet>a)].(pi\<bullet>t)) x" by simp
  qed
qed (auto intro: h1 h2)

lemma lam_induct'[case_names Fin Var App Lam]: 
  fixes P :: "lam \<Rightarrow> 'a \<Rightarrow> bool"
  and   x :: "'a"
  and   t :: "lam"
  and   f :: "'a \<Rightarrow> name set"
  assumes fs: "\<And>x. finite (f x)"
  and     h1: "\<And>x a. P (Var  a) x" 
  and     h2: "\<And>x t1 t2. (\<forall>z. P t1 z)\<Longrightarrow>(\<forall>z. P t2 z)\<Longrightarrow>P (App t1 t2) x" 
  and     h3: "\<And>x a t. a\<notin>f x \<Longrightarrow> (\<forall>z. P t z)\<Longrightarrow> P (Lam [a].t) x"
  shows  "P t x"
proof - 
  from fs h1 h2 h3 have "\<forall>(pi::name prm) x. P (pi\<bullet>t) x" by (rule lam_induct_aux, auto)
  hence "P (([]::name prm)\<bullet>t) x" by blast
  thus "P t x" by simp
qed

lemma lam_induct[case_names Var App Lam]: 
  fixes P :: "lam \<Rightarrow> ('a::fs_name) \<Rightarrow> bool"
  and   x :: "'a::fs_name"
  and   t :: "lam"
  assumes h1: "\<And>x a. P (Var  a) x" 
  and     h2: "\<And>x t1 t2. (\<forall>z. P t1 z)\<Longrightarrow>(\<forall>z. P t2 z)\<Longrightarrow>P (App t1 t2) x" 
  and     h3: "\<And>x a t. a\<sharp>x \<Longrightarrow> (\<forall>z. P t z)\<Longrightarrow> P (Lam [a].t) x"
  shows  "P t x"
by (rule lam_induct'[of "\<lambda>x. ((supp x)::name set)" "P"], 
    simp_all add: fs_name1 fresh_def[symmetric], auto intro: h1 h2 h3)

types 'a f1_ty  = "name\<Rightarrow>('a::pt_name)"
      'a f2_ty  = "'a\<Rightarrow>'a\<Rightarrow>('a::pt_name)"
      'a f3_ty  = "name\<Rightarrow>'a\<Rightarrow>('a::pt_name)"

lemma f3_freshness_conditions:
  fixes f3::"('a::pt_name) f3_ty"
  and   y ::"name prm \<Rightarrow> 'a::pt_name"
  and   a ::"name"
  and   pi1::"name prm"
  and   pi2::"name prm"
  assumes a: "finite ((supp f3)::name set)"
  and     b: "finite ((supp y)::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>(a''::name). a''\<sharp>(\<lambda>a'. f3 a' (y (pi1@[(a,pi2\<bullet>a')]))) \<and> 
                       a''\<sharp>(\<lambda>a'. f3 a' (y (pi1@[(a,pi2\<bullet>a')]))) a''" 
proof -
  from c obtain a' where d0: "a'\<sharp>f3" and d1: "\<forall>(y::'a::pt_name). a'\<sharp>f3 a' y" by force
  have "\<exists>(a''::name). a''\<sharp>(f3,a,a',pi1,pi2,y)" 
    by (rule at_exists_fresh[OF at_name_inst],  simp add: supp_prod fs_name1 a b)
  then obtain a'' where d2: "a''\<sharp>f3" and d3: "a''\<noteq>a'" and d3b: "a''\<sharp>(f3,a,pi1,pi2,y)" 
    by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
  have d3c: "a''\<notin>((supp (f3,a,pi1,pi2,y))::name set)" using d3b by (simp add: fresh_def)
  have d4: "a''\<sharp>f3 a'' (y (pi1@[(a,pi2\<bullet>a'')]))"
  proof -
    have d5: "[(a'',a')]\<bullet>f3 = f3" 
      by (rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst, OF d2, OF d0]) 
    from d1 have "\<forall>(y::'a::pt_name). ([(a'',a')]\<bullet>a')\<sharp>([(a'',a')]\<bullet>(f3 a' y))"
      by (simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
    hence "\<forall>(y::'a::pt_name). a''\<sharp>(f3 a'' ([(a'',a')]\<bullet>y))" using d3 d5 
      by (simp add: at_calc[OF at_name_inst] pt_fun_app_eq[OF pt_name_inst, OF at_name_inst])
    hence "a''\<sharp>(f3 a'' ([(a'',a')]\<bullet>((rev [(a'',a')])\<bullet>(y (pi1@[(a,pi2\<bullet>a'')])))))" by force
    thus ?thesis by (simp only: pt_pi_rev[OF pt_name_inst, OF at_name_inst])
  qed
  have d6: "a''\<sharp>(\<lambda>a'. f3 a' (y (pi1@[(a,pi2\<bullet>a')])))"
  proof -
    from a b have d7: "finite ((supp (f3,a,pi1,pi2,y))::name set)" by (simp add: supp_prod fs_name1)
    have e: "((supp (f3,a,pi1,pi2,y))::name set) supports (\<lambda>a'. f3 a' (y (pi1@[(a,pi2\<bullet>a')])))" 
      by (supports_simp add: perm_append)
    from e d7 d3c show ?thesis by (rule supports_fresh)
  qed
  from d6 d4 show ?thesis by force
qed

lemma f3_freshness_conditions_simple:
  fixes f3::"('a::pt_name) f3_ty"
  and   y ::"name prm \<Rightarrow> 'a::pt_name"
  and   a ::"name"
  and   pi::"name prm"
  assumes a: "finite ((supp f3)::name set)"
  and     b: "finite ((supp y)::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>(a''::name). a''\<sharp>(\<lambda>a'. f3 a' (y (pi@[(a,a')]))) \<and> a''\<sharp>(\<lambda>a'. f3 a' (y (pi@[(a,a')]))) a''" 
proof -
  from c obtain a' where d0: "a'\<sharp>f3" and d1: "\<forall>(y::'a::pt_name). a'\<sharp>f3 a' y" by force
  have "\<exists>(a''::name). a''\<sharp>(f3,a,a',pi,y)" 
    by (rule at_exists_fresh[OF at_name_inst],  simp add: supp_prod fs_name1 a b)
  then obtain a'' where d2: "a''\<sharp>f3" and d3: "a''\<noteq>a'" and d3b: "a''\<sharp>(f3,a,pi,y)" 
    by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
  have d3c: "a''\<notin>((supp (f3,a,pi,y))::name set)" using d3b by (simp add: fresh_def)
  have d4: "a''\<sharp>f3 a'' (y (pi@[(a,a'')]))"
  proof -
    have d5: "[(a'',a')]\<bullet>f3 = f3" 
      by (rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst, OF d2, OF d0]) 
    from d1 have "\<forall>(y::'a::pt_name). ([(a'',a')]\<bullet>a')\<sharp>([(a'',a')]\<bullet>(f3 a' y))"
      by (simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
    hence "\<forall>(y::'a::pt_name). a''\<sharp>(f3 a'' ([(a'',a')]\<bullet>y))" using d3 d5 
      by (simp add: at_calc[OF at_name_inst] pt_fun_app_eq[OF pt_name_inst, OF at_name_inst])
    hence "a''\<sharp>(f3 a'' ([(a'',a')]\<bullet>((rev [(a'',a')])\<bullet>(y (pi@[(a,a'')])))))" by force
    thus ?thesis by (simp only: pt_pi_rev[OF pt_name_inst, OF at_name_inst])
  qed
  have d6: "a''\<sharp>(\<lambda>a'. f3 a' (y (pi@[(a,a')])))"
  proof -
    from a b have d7: "finite ((supp (f3,a,pi,y))::name set)" by (simp add: supp_prod fs_name1)
    have "((supp (f3,a,pi,y))::name set) supports (\<lambda>a'. f3 a' (y (pi@[(a,a')])))" 
      by (supports_simp add: perm_append)
    with d7 d3c show ?thesis by (simp add: supports_fresh)
  qed
  from d6 d4 show ?thesis by force
qed

lemma f3_fresh_fun_supports:
  fixes f3::"('a::pt_name) f3_ty"
  and   a ::"name"
  and   pi1::"name prm"
  and   y ::"name prm \<Rightarrow> 'a::pt_name"
  assumes a: "finite ((supp f3)::name set)"
  and     b: "finite ((supp y)::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "((supp (f3,a,y))::name set) supports (\<lambda>pi. fresh_fun (\<lambda>a'. f3 a' (y (pi@[(a,a')]))))"
proof (auto simp add: "op supports_def" perm_fun_def expand_fun_eq fresh_def[symmetric])
  fix b::"name" and c::"name" and pi::"name prm"
  assume b1: "b\<sharp>(f3,a,y)"
  and    b2: "c\<sharp>(f3,a,y)"
  from b1 b2 have b3: "[(b,c)]\<bullet>f3=f3" and t4: "[(b,c)]\<bullet>a=a" and t5: "[(b,c)]\<bullet>y=y"
    by (simp_all add: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst] fresh_prod)
  let ?g = "\<lambda>a'. f3 a' (y (([(b,c)]\<bullet>pi)@[(a,a')]))"
  and ?h = "\<lambda>a'. f3 a' (y (pi@[(a,a')]))"
  have a0: "finite ((supp (f3,a,[(b,c)]\<bullet>pi,y))::name set)" using a b 
    by (simp add: supp_prod fs_name1)
  have a1: "((supp (f3,a,[(b,c)]\<bullet>pi,y))::name set) supports ?g" by (supports_simp add: perm_append)
  hence a2: "finite ((supp ?g)::name set)" using a0 by (rule supports_finite)
  have a3: "\<exists>(a''::name). a''\<sharp>?g \<and> a''\<sharp>(?g a'')"
    by (rule f3_freshness_conditions_simple[OF a, OF b, OF c])
  have "((supp (f3,a,y))::name set) \<subseteq> (supp (f3,a,[(b,c)]\<bullet>pi,y))" by (force simp add: supp_prod)
  have a4: "[(b,c)]\<bullet>?g = ?h" using b1 b2
    by (simp add: fresh_prod, perm_simp add: perm_append)
  have "[(b,c)]\<bullet>(fresh_fun ?g) = fresh_fun ([(b,c)]\<bullet>?g)" 
    by (simp add: fresh_fun_equiv[OF pt_name_inst, OF at_name_inst, OF a2, OF a3])
  also have "\<dots> = fresh_fun ?h" using a4 by simp
  finally show "[(b,c)]\<bullet>(fresh_fun ?g) = fresh_fun ?h" .
qed

lemma f3_fresh_fun_supp_finite:
  fixes f3::"('a::pt_name) f3_ty"
  and   a ::"name"
  and   pi1::"name prm"
  and   y ::"name prm \<Rightarrow> 'a::pt_name"
  assumes a: "finite ((supp f3)::name set)"
  and     b: "finite ((supp y)::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "finite ((supp (\<lambda>pi. fresh_fun (\<lambda>a'. f3 a' (y (pi@[(a,a')])))))::name set)"
proof -
  have "((supp (f3,a,y))::name set) supports (\<lambda>pi. fresh_fun (\<lambda>a'. f3 a' (y (pi@[(a,a')]))))"
    using a b c by (rule f3_fresh_fun_supports)
  moreover
  have "finite ((supp (f3,a,y))::name set)" using a b by (simp add: supp_prod fs_name1) 
  ultimately show ?thesis by (rule supports_finite)
qed

(*
types 'a recT  = "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> ((lam\<times>name prm\<times>('a::pt_name)) set)"

consts
  rec :: "('a::pt_name) recT"

inductive "rec f1 f2 f3"
intros
r1: "(Var a,pi,f1 (pi\<bullet>a))\<in>rec f1 f2 f3" 
r2: "\<lbrakk>finite ((supp y1)::name set);(t1,pi,y1)\<in>rec f1 f2 f3; 
      finite ((supp y2)::name set);(t2,pi,y2)\<in>rec f1 f2 f3\<rbrakk> 
      \<Longrightarrow> (App t1 t2,pi,f2 y1 y2)\<in>rec f1 f2 f3"
r3: "\<lbrakk>finite ((supp y)::name set);\<forall>a'. ((t,pi@[(a,a')],y)\<in>rec f1 f2 f3)\<rbrakk> 
      \<Longrightarrow> (Lam [a].t,pi,fresh_fun (\<lambda>a'. f3 a' y))\<in>rec f1 f2 f3"

*)

(*
types 'a recT  = "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> (lam\<times>(name prm \<Rightarrow> ('a::pt_name))) set"

consts
  rec :: "('a::pt_name) recT"

inductive "rec f1 f2 f3"
intros
r1: "(Var a,\<lambda>pi. f1 (pi\<bullet>a))\<in>rec f1 f2 f3" 
r2: "\<lbrakk>finite ((supp y1)::name set);(t1,y1)\<in>rec f1 f2 f3; 
      finite ((supp y2)::name set);(t2,y2)\<in>rec f1 f2 f3\<rbrakk> 
      \<Longrightarrow> (App t1 t2,\<lambda>pi. f2 (y1 pi) (y2 pi))\<in>rec f1 f2 f3"
r3: "\<lbrakk>finite ((supp y)::name set);(t,y)\<in>rec f1 f2 f3\<rbrakk> 
      \<Longrightarrow> (Lam [a].t,fresh_fun (\<lambda>a' pi. f3 a' (y (pi@[(a,a')]))))\<in>rec f1 f2 f3"
*)

term lam_Rep.Var
term lam_Rep.Lam

consts nthe :: "'a nOption \<Rightarrow> 'a"
primrec
 "nthe (nSome x) = x"

types 'a recT  = "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> (lam\<times>(name prm \<Rightarrow> ('a::pt_name))) set"

(*
consts fn :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> lam_Rep \<Rightarrow> ('a::pt_name)"

primrec
"fn f1 f2 f3 (lam_Rep.Var a)     = f1 a"
"fn f1 f2 f3 (lam_Rep.App t1 t2) = f2 (fn f1 f2 f3 t1) (fn f1 f2 f3 t2)"
"fn f1 f2 f3 (lam_Rep.Lam f)     = fresh_fun (\<lambda>a'. f3 a' (fn f1 f2 f3 (fn' (f a'))))"
*)

consts
  rec :: "('a::pt_name) recT"

inductive "rec f1 f2 f3"
intros
r1: "(Var a,\<lambda>pi. f1 (pi\<bullet>a))\<in>rec f1 f2 f3" 
r2: "\<lbrakk>finite ((supp y1)::name set);(t1,y1)\<in>rec f1 f2 f3; 
      finite ((supp y2)::name set);(t2,y2)\<in>rec f1 f2 f3\<rbrakk> 
      \<Longrightarrow> (App t1 t2,\<lambda>pi. f2 (y1 pi) (y2 pi))\<in>rec f1 f2 f3"
r3: "\<lbrakk>finite ((supp y)::name set);(t,y)\<in>rec f1 f2 f3\<rbrakk> 
      \<Longrightarrow> (Lam [a].t,\<lambda>pi. fresh_fun (\<lambda>a'. f3 a' (y (pi@[(a,a')]))))\<in>rec f1 f2 f3"

constdefs
  rfun' :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> lam \<Rightarrow> name prm \<Rightarrow> ('a::pt_name)" 
  "rfun' f1 f2 f3 t \<equiv> (THE y. (t,y)\<in>rec f1 f2 f3)"

  rfun :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> lam \<Rightarrow> ('a::pt_name)" 
  "rfun f1 f2 f3 t \<equiv> rfun' f1 f2 f3 t ([]::name prm)"

lemma rec_prm_eq[rule_format]:
  fixes f1 ::"('a::pt_name) f1_ty"
  and   f2 ::"('a::pt_name) f2_ty"
  and   f3 ::"('a::pt_name) f3_ty"
  and   t  ::"lam"
  and   y  ::"name prm \<Rightarrow> ('a::pt_name)"
  shows "(t,y)\<in>rec f1 f2 f3 \<Longrightarrow> (\<forall>(pi1::name prm) (pi2::name prm). pi1 \<sim> pi2 \<longrightarrow> (y pi1 = y pi2))"
apply(erule rec.induct)
apply(auto simp add: pt3[OF pt_name_inst])
apply(rule_tac f="fresh_fun" in arg_cong)
apply(auto simp add: expand_fun_eq)
apply(drule_tac x="pi1@[(a,x)]" in spec)
apply(drule_tac x="pi2@[(a,x)]" in spec)
apply(force simp add: prm_eq_def pt2[OF pt_name_inst])
done

(* silly helper lemma *)
lemma rec_trans: 
  fixes f1 ::"('a::pt_name) f1_ty"
  and   f2 ::"('a::pt_name) f2_ty"
  and   f3 ::"('a::pt_name) f3_ty"
  and   t  ::"lam"
  and   y  ::"name prm \<Rightarrow> ('a::pt_name)"
  assumes a: "(t,y)\<in>rec f1 f2 f3"
  and     b: "y=y'"
  shows   "(t,y')\<in>rec f1 f2 f3"
using a b by simp


lemma rec_prm_equiv:
  fixes f1 ::"('a::pt_name) f1_ty"
  and   f2 ::"('a::pt_name) f2_ty"
  and   f3 ::"('a::pt_name) f3_ty"
  and   t  ::"lam"
  and   y  ::"name prm \<Rightarrow> ('a::pt_name)"
  and   pi ::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(t,y)\<in>rec f1 f2 f3"
  shows "(pi\<bullet>t,pi\<bullet>y)\<in>rec (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
using a
proof (induct)
  case (r1 c)
  let ?g ="pi\<bullet>(\<lambda>(pi'::name prm). f1 (pi'\<bullet>c))"
  and ?g'="\<lambda>(pi'::name prm). (pi\<bullet>f1) (pi'\<bullet>(pi\<bullet>c))"
  have "?g'=?g" 
  proof (auto simp only: expand_fun_eq perm_fun_def)
    fix pi'::"name prm"
    let ?h = "((rev pi)\<bullet>(pi'\<bullet>(pi\<bullet>c)))"
    and ?h'= "(((rev pi)\<bullet>pi')\<bullet>c)"
    have "?h' = ((rev pi)\<bullet>pi')\<bullet>((rev pi)\<bullet>(pi\<bullet>c))" 
      by (simp add: pt_rev_pi[OF pt_name_inst, OF at_name_inst])
    also have "\<dots> = ?h"
      by (simp add: pt_perm_compose[OF pt_name_inst, OF at_name_inst,symmetric])
    finally show "pi\<bullet>(f1 ?h) = pi\<bullet>(f1 ?h')" by simp
  qed
  thus ?case by (force intro: rec_trans rec.r1)
next
  case (r2 t1 t2 y1 y2)
  assume a1: "finite ((supp y1)::name set)"
  and    a2: "finite ((supp y2)::name set)"
  and    a3: "(pi\<bullet>t1,pi\<bullet>y1) \<in> rec (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
  and    a4: "(pi\<bullet>t2,pi\<bullet>y2) \<in> rec (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
  from a1 a2 have a1': "finite ((supp (pi\<bullet>y1))::name set)" and a2': "finite ((supp (pi\<bullet>y2))::name set)"
    by (simp_all add: pt_supp_finite_pi[OF pt_name_inst, OF at_name_inst])
  let ?g ="pi\<bullet>(\<lambda>(pi'::name prm). f2 (y1 pi') (y2 pi'))"
  and ?g'="\<lambda>(pi'::name prm). (pi\<bullet>f2) ((pi\<bullet>y1) pi') ((pi\<bullet>y2) pi')"
  have "?g'=?g" by  (simp add: expand_fun_eq perm_fun_def pt_rev_pi[OF pt_name_inst, OF at_name_inst])
  thus ?case using a1' a2' a3 a4 by (force intro: rec.r2 rec_trans)
next
  case (r3 a t y)
  assume a1: "finite ((supp y)::name set)"
  and    a2: "(pi\<bullet>t,pi\<bullet>y) \<in> rec (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
  from a1 have a1': "finite ((supp (pi\<bullet>y))::name set)" 
    by (simp add: pt_supp_finite_pi[OF pt_name_inst, OF at_name_inst])
  let ?g ="pi\<bullet>(\<lambda>(pi'::name prm). fresh_fun (\<lambda>a'. f3 a' (y (pi'@[(a,a')]))))"
  and ?g'="(\<lambda>(pi'::name prm). fresh_fun (\<lambda>a'. (pi\<bullet>f3) a' ((pi\<bullet>y) (pi'@[((pi\<bullet>a),a')]))))"
  have "?g'=?g" 
  proof (auto simp add: expand_fun_eq perm_fun_def pt_rev_pi[OF pt_name_inst, OF at_name_inst] 
                        perm_append)
    fix pi'::"name prm"
    let ?h  = "\<lambda>a'. pi\<bullet>(f3 ((rev pi)\<bullet>a') (y (((rev pi)\<bullet>pi')@[(a,(rev pi)\<bullet>a')])))"
    and ?h' = "\<lambda>a'. f3 a' (y (((rev pi)\<bullet>pi')@[(a,a')]))"
    have fs_f3: "finite ((supp f3)::name set)" using f by (simp add: supp_prod)
    have fs_h': "finite ((supp ?h')::name set)"
    proof -
      have "((supp (f3,a,(rev pi)\<bullet>pi',y))::name set) supports ?h'" 
	by (supports_simp add: perm_append)
      moreover
      have "finite ((supp (f3,a,(rev pi)\<bullet>pi',y))::name set)" using a1 fs_f3 
	by (simp add: supp_prod fs_name1)
      ultimately show ?thesis by (rule supports_finite)
    qed
    have fcond: "\<exists>(a''::name). a''\<sharp>?h' \<and> a''\<sharp>(?h' a'')"
      by (rule f3_freshness_conditions_simple[OF fs_f3, OF a1, OF c])
    have "fresh_fun ?h = fresh_fun (pi\<bullet>?h')"
      by (simp add: perm_fun_def pt_rev_pi[OF pt_name_inst, OF at_name_inst])
    also have "\<dots> = pi\<bullet>(fresh_fun ?h')"
      by (simp add: fresh_fun_equiv[OF pt_name_inst, OF at_name_inst, OF fs_h', OF fcond])
    finally show "fresh_fun ?h = pi\<bullet>(fresh_fun ?h')" .
  qed
  thus ?case using a1' a2 by (force intro: rec.r3 rec_trans)
qed

lemma rec_perm:
  fixes f1 ::"('a::pt_name) f1_ty"
  and   f2 ::"('a::pt_name) f2_ty"
  and   f3 ::"('a::pt_name) f3_ty"
  and   pi1::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(t,y)\<in>rec f1 f2 f3"
  shows "(pi1\<bullet>t, \<lambda>pi2. y (pi2@pi1))\<in>rec f1 f2 f3"
proof -
  have lem: "\<forall>(y::name prm\<Rightarrow>('a::pt_name))(pi::name prm). 
             finite ((supp y)::name set) \<longrightarrow> finite ((supp (\<lambda>pi'. y (pi'@pi)))::name set)"
  proof (intro strip)
    fix y::"name prm\<Rightarrow>('a::pt_name)" and pi::"name prm"
    assume  "finite ((supp y)::name set)"
    hence "finite ((supp (y,pi))::name set)" by (simp add: supp_prod fs_name1)      
    moreover
    have  "((supp (y,pi))::name set) supports (\<lambda>pi'. y (pi'@pi))" 
      by (supports_simp add: perm_append)
    ultimately show "finite ((supp (\<lambda>pi'. y (pi'@pi)))::name set)" by (simp add: supports_finite)
  qed
from a
show ?thesis
proof (induct)
  case (r1 c)
  show ?case
    by (auto simp add: pt2[OF pt_name_inst], rule rec.r1)
next
  case (r2 t1 t2 y1 y2)
  thus ?case using lem by (auto intro!: rec.r2) 
next
  case (r3 c t y)
  assume a0: "(t,y)\<in>rec f1 f2 f3"
  and    a1: "finite ((supp y)::name set)"
  and    a2: "(pi1\<bullet>t,\<lambda>pi2. y (pi2@pi1))\<in>rec f1 f2 f3"
  from f have f': "finite ((supp f3)::name set)" by (simp add: supp_prod)
  show ?case
  proof(simp)
    have a3: "finite ((supp (\<lambda>pi2. y (pi2@pi1)))::name set)" using lem a1 by force
    let ?g' = "\<lambda>(pi::name prm). fresh_fun (\<lambda>a'. f3 a' ((\<lambda>pi2. y (pi2@pi1)) (pi@[(pi1\<bullet>c,a')])))"
    and ?g  = "\<lambda>(pi::name prm). fresh_fun (\<lambda>a'. f3 a' (y (pi@[(pi1\<bullet>c,a')]@pi1)))"
    and ?h  = "\<lambda>(pi::name prm). fresh_fun (\<lambda>a'. f3 a' (y (pi@pi1@[(c,a')])))"
    have eq1: "?g = ?g'" by simp
    have eq2: "?g'= ?h" 
    proof (auto simp only: expand_fun_eq)
      fix pi::"name prm"
      let ?q  = "\<lambda>a'. f3 a' (y ((pi@[(pi1\<bullet>c,a')])@pi1))"
      and ?q' = "\<lambda>a'. f3 a' (y (((pi@pi1)@[(c,(rev pi1)\<bullet>a')])))"
      and ?r  = "\<lambda>a'. f3 a' (y ((pi@pi1)@[(c,a')]))"
      and ?r' = "\<lambda>a'. f3 a' (y (pi@(pi1@[(c,a')])))"
      have eq3a: "?r = ?r'" by simp
      have eq3: "?q = ?q'"
      proof (auto simp only: expand_fun_eq)
	fix a'::"name"
	have "(y ((pi@[(pi1\<bullet>c,a')])@pi1)) =  (y (((pi@pi1)@[(c,(rev pi1)\<bullet>a')])))" 
	  proof -
	    have "((pi@[(pi1\<bullet>c,a')])@pi1) \<sim> ((pi@pi1)@[(c,(rev pi1)\<bullet>a')])"
	    by (force simp add: prm_eq_def at_append[OF at_name_inst] 
                   at_calc[OF at_name_inst] at_bij[OF at_name_inst] 
                   at_pi_rev[OF at_name_inst] at_rev_pi[OF at_name_inst])
	    with a0 show ?thesis by (rule rec_prm_eq)
	  qed
	thus "f3 a' (y ((pi@[(pi1\<bullet>c,a')])@pi1)) = f3 a' (y (((pi@pi1)@[(c,(rev pi1)\<bullet>a')])))" by simp
      qed
      have fs_a: "finite ((supp ?q')::name set)"
      proof -
	have "((supp (f3,c,(pi@pi1),(rev pi1),y))::name set) supports ?q'" 
	  by (supports_simp add: perm_append fresh_list_append fresh_list_rev)
	moreover
	have "finite ((supp (f3,c,(pi@pi1),(rev pi1),y))::name set)" using f' a1
	  by (simp add: supp_prod fs_name1)
	ultimately show ?thesis by (rule supports_finite)
      qed
      have fs_b: "finite ((supp ?r)::name set)"
      proof -
	have "((supp (f3,c,(pi@pi1),y))::name set) supports ?r" 
	  by (supports_simp add: perm_append fresh_list_append)
	moreover
	have "finite ((supp (f3,c,(pi@pi1),y))::name set)" using f' a1
	  by (simp add: supp_prod fs_name1)
	ultimately show ?thesis by (rule supports_finite)
      qed
      have c1: "\<exists>(a''::name). a''\<sharp>?q' \<and> a''\<sharp>(?q' a'')"
	by (rule f3_freshness_conditions[OF f', OF a1, OF c])
      have c2: "\<exists>(a''::name). a''\<sharp>?r \<and> a''\<sharp>(?r a'')"
	by (rule f3_freshness_conditions_simple[OF f', OF a1, OF c])
      have c3: "\<exists>(d::name). d\<sharp>(?q',?r,(rev pi1))" 
	by (rule at_exists_fresh[OF at_name_inst], 
            simp only: finite_Un supp_prod fs_a fs_b fs_name1, simp)
      then obtain d::"name" where d1: "d\<sharp>?q'" and d2: "d\<sharp>?r" and d3: "d\<sharp>(rev pi1)" 
	by (auto simp only: fresh_prod)
      have eq4: "(rev pi1)\<bullet>d = d" using d3 by (simp add: at_prm_fresh[OF at_name_inst])
      have "fresh_fun ?q = fresh_fun ?q'" using eq3 by simp
      also have "\<dots> = ?q' d" using fs_a c1 d1 
	by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
      also have "\<dots> = ?r d" using fs_b c2 d2 eq4
	by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
      also have "\<dots> = fresh_fun ?r" using fs_b c2 d2 
	by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
      finally show "fresh_fun ?q = fresh_fun ?r'" by simp
    qed
    from a3 a2 have "(Lam [(pi1\<bullet>c)].(pi1\<bullet>t), ?g')\<in>rec f1 f2 f3" by (rule rec.r3)
    thus "(Lam [(pi1\<bullet>c)].(pi1\<bullet>t), ?h)\<in>rec f1 f2 f3" using eq2 by simp
  qed
qed
qed    

lemma rec_perm_rev:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(pi\<bullet>t,y)\<in>rec f1 f2 f3"
  shows "(t, \<lambda>pi2. y (pi2@(rev pi)))\<in>rec f1 f2 f3"
proof - 
  from a have "((rev pi)\<bullet>(pi\<bullet>t),\<lambda>pi2. y (pi2@(rev pi)))\<in>rec f1 f2 f3"
    by (rule rec_perm[OF f, OF c])
  thus ?thesis by (simp add: pt_rev_pi[OF pt_name_inst, OF at_name_inst])
qed


lemma rec_unique:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(t,y)\<in>rec f1 f2 f3"
  shows "\<forall>(y'::name prm\<Rightarrow>('a::pt_name))(pi::name prm).
         (t,y')\<in>rec f1 f2 f3 \<longrightarrow> y pi = y' pi"
using a
proof (induct)
  case (r1 c)
  show ?case 
   apply(auto)
   apply(ind_cases "(Var c, y') \<in> rec f1 f2 f3")
   apply(simp_all add: lam.distinct lam.inject)
   done
next
  case (r2 t1 t2 y1 y2)
  thus ?case 
    apply(clarify)
    apply(ind_cases "(App t1 t2, y') \<in> rec f1 f2 f3") 
    apply(simp_all (no_asm_use) only: lam.distinct lam.inject) 
    apply(clarify)
    apply(drule_tac x="y1" in spec)
    apply(drule_tac x="y2" in spec)
    apply(auto)
    done
next
  case (r3 c t y)
  assume i1: "finite ((supp y)::name set)"
  and    i2: "(t,y)\<in>rec f1 f2 f3"
  and    i3: "\<forall>(y'::name prm\<Rightarrow>('a::pt_name))(pi::name prm).
              (t,y')\<in>rec f1 f2 f3 \<longrightarrow> y pi = y' pi"
  from f have f': "finite ((supp f3)::name set)" by (simp add: supp_prod)
  show ?case 
  proof (auto)
    fix y'::"name prm\<Rightarrow>('a::pt_name)" and pi::"name prm"
    assume i4: "(Lam [c].t, y') \<in> rec f1 f2 f3"
    from i4 show "fresh_fun (\<lambda>a'. f3 a' (y (pi@[(c,a')]))) = y' pi"
    proof (cases, simp_all add: lam.distinct lam.inject, auto)
      fix a::"name" and t'::"lam" and y''::"name prm\<Rightarrow>('a::pt_name)"
      assume i5: "[c].t = [a].t'"
      and    i6: "(t',y'')\<in>rec f1 f2 f3"
      and    i6':"finite ((supp y'')::name set)"
      let ?g = "\<lambda>a'. f3 a' (y  (pi@[(c,a')]))"
      and ?h = "\<lambda>a'. f3 a' (y'' (pi@[(a,a')]))"
      show "fresh_fun ?g = fresh_fun ?h" using i5
      proof (cases "a=c")
	case True
	assume i7: "a=c"
	with i5 have i8: "t=t'" by (simp add: alpha)
	show "fresh_fun ?g = fresh_fun ?h" using i3 i6 i7 i8 by simp
      next
	case False
	assume i9: "a\<noteq>c"
	with i5[symmetric] have i10: "t'=[(a,c)]\<bullet>t" and i11: "a\<sharp>t" by (simp_all add: alpha)
	have r1: "finite ((supp ?g)::name set)" 
	proof -
	  have "((supp (f3,c,pi,y))::name set) supports ?g" 
	    by (supports_simp add: perm_append)
	  moreover
	  have "finite ((supp (f3,c,pi,y))::name set)" using f' i1
	    by (simp add: supp_prod fs_name1)
	  ultimately show ?thesis by (rule supports_finite)
	qed
	have r2: "finite ((supp ?h)::name set)" 
	proof -
	  have "((supp (f3,a,pi,y''))::name set) supports ?h" 
	    by (supports_simp add: perm_append)
	  moreover
	  have "finite ((supp (f3,a,pi,y''))::name set)" using f' i6'
	    by (simp add: supp_prod fs_name1)
	  ultimately show ?thesis by (rule supports_finite)
	qed
	have c1: "\<exists>(a''::name). a''\<sharp>?g \<and> a''\<sharp>(?g a'')"
	  by (rule f3_freshness_conditions_simple[OF f', OF i1, OF c])
	have c2: "\<exists>(a''::name). a''\<sharp>?h \<and> a''\<sharp>(?h a'')"
	  by (rule f3_freshness_conditions_simple[OF f', OF i6', OF c])
	have "\<exists>(d::name). d\<sharp>(?g,?h,t,a,c)" 
	  by (rule at_exists_fresh[OF at_name_inst], 
              simp only: finite_Un supp_prod r1 r2 fs_name1, simp)
	then obtain d::"name" 
	  where f1: "d\<sharp>?g" and f2: "d\<sharp>?h" and f3: "d\<sharp>t" and f4: "d\<noteq>a" and f5: "d\<noteq>c" 
	  by (force simp add: fresh_prod at_fresh[OF at_name_inst] at_fresh[OF at_name_inst])
	have g1: "[(a,d)]\<bullet>t = t" 
	  by (rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst, OF i11, OF f3]) 
	from i6 have "(([(a,c)]@[(a,d)])\<bullet>t,y'')\<in>rec f1 f2 f3" using g1 i10 by (simp only: pt_name2)
	hence "(t, \<lambda>pi2. y'' (pi2@(rev ([(a,c)]@[(a,d)]))))\<in>rec f1 f2 f3"
	  by (simp only: rec_perm_rev[OF f, OF c])
	hence g2: "(t, \<lambda>pi2. y'' (pi2@([(a,d)]@[(a,c)])))\<in>rec f1 f2 f3" by simp
	have "distinct [a,c,d]" using i9 f4 f5 by force
	hence g3: "(pi@[(c,d)]@[(a,d)]@[(a,c)]) \<sim> (pi@[(a,d)])"
	  by (force simp add: prm_eq_def at_calc[OF at_name_inst] at_append[OF at_name_inst])
	have "fresh_fun ?g = ?g d" using r1 c1 f1
	  by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
	also have "\<dots> = f3 d ((\<lambda>pi2. y'' (pi2@([(a,d)]@[(a,c)]))) (pi@[(c,d)]))" using i3 g2 by simp 
	also have "\<dots> = f3 d (y'' (pi@[(c,d)]@[(a,d)]@[(a,c)]))" by simp
	also have "\<dots> = f3 d (y'' (pi@[(a,d)]))" using i6 g3 by (simp add: rec_prm_eq)
	also have "\<dots> = fresh_fun ?h" using r2 c2 f2
	  by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
	finally show "fresh_fun ?g = fresh_fun ?h" .
      qed
    qed
  qed
qed

lemma rec_total_aux:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>(y::name prm\<Rightarrow>('a::pt_name)). ((t,y)\<in>rec f1 f2 f3) \<and> (finite ((supp y)::name set))"
proof (induct t rule: lam.induct_weak)
  case (Var c)
  have a1: "(Var c,\<lambda>(pi::name prm). f1 (pi\<bullet>c))\<in>rec f1 f2 f3" by (rule rec.r1)
  have a2: "finite ((supp (\<lambda>(pi::name prm). f1 (pi\<bullet>c)))::name set)"
  proof -
    have "((supp (f1,c))::name set) supports (\<lambda>(pi::name prm). f1 (pi\<bullet>c))" by (supports_simp)
    moreover have "finite ((supp (f1,c))::name set)" using f by (simp add: supp_prod fs_name1)
    ultimately show ?thesis by (rule supports_finite)
  qed
  from a1 a2 show ?case by force
next
  case (App t1 t2)
  assume "\<exists>y1. (t1,y1)\<in>rec f1 f2 f3 \<and> finite ((supp y1)::name set)"
  then obtain y1::"name prm \<Rightarrow> ('a::pt_name)"
    where a11: "(t1,y1)\<in>rec f1 f2 f3" and a12: "finite ((supp y1)::name set)" by force
  assume "\<exists>y2. (t2,y2)\<in>rec f1 f2 f3 \<and> finite ((supp y2)::name set)"
  then obtain y2::"name prm \<Rightarrow> ('a::pt_name)"
    where a21: "(t2,y2)\<in>rec f1 f2 f3" and a22: "finite ((supp y2)::name set)" by force
  
  have a1: "(App t1 t2,\<lambda>(pi::name prm). f2 (y1 pi) (y2 pi))\<in>rec f1 f2 f3"
    using a12 a11 a22 a21 by (rule rec.r2)
  have a2: "finite ((supp (\<lambda>(pi::name prm). f2 (y1 pi) (y2 pi)))::name set)"
  proof -
    have "((supp (f2,y1,y2))::name set) supports (\<lambda>(pi::name prm). f2 (y1 pi) (y2 pi))" 
      by (supports_simp)
    moreover have "finite ((supp (f2,y1,y2))::name set)" using f a21 a22 
      by (simp add: supp_prod fs_name1)
    ultimately show ?thesis by (rule supports_finite)
  qed
  from a1 a2 show ?case by force
next
  case (Lam a t)
  assume "\<exists>y. (t,y)\<in>rec f1 f2 f3 \<and> finite ((supp y)::name set)"
  then obtain y::"name prm \<Rightarrow> ('a::pt_name)"
    where a11: "(t,y)\<in>rec f1 f2 f3" and a12: "finite ((supp y)::name set)" by force
  from f have f': "finite ((supp f3)::name set)" by (simp add: supp_prod)
  have a1: "(Lam [a].t,\<lambda>(pi::name prm). fresh_fun (\<lambda>a'. f3 a' (y (pi@[(a,a')]))))\<in>rec f1 f2 f3"
    using a12 a11 by (rule rec.r3)
  have a2: "finite ((supp (\<lambda>pi. fresh_fun (\<lambda>a'. f3 a' (y (pi@[(a,a')])))))::name set)" 
    using f' a12 c by (rule f3_fresh_fun_supp_finite)
  from a1 a2 show ?case by force
qed

lemma rec_total:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>(y::name prm\<Rightarrow>('a::pt_name)). ((t,y)\<in>rec f1 f2 f3)"
proof -
  have "\<exists>y. ((t,y)\<in>rec f1 f2 f3) \<and> (finite ((supp y)::name set))"
    by (rule rec_total_aux[OF f, OF c])
  thus ?thesis by force
qed

lemma rec_function:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>!y. (t,y)\<in>rec f1 f2 f3"
proof 
  case goal1
  show ?case by (rule rec_total[OF f, OF c])
next
  case (goal2 y1 y2)
  assume a1: "(t,y1)\<in>rec f1 f2 f3" and a2: "(t,y2)\<in>rec f1 f2 f3"
  hence "\<forall>pi. y1 pi = y2 pi" using rec_unique[OF f, OF c] by force
  thus ?case by (force simp add: expand_fun_eq) 
qed
  
lemma theI2':
  assumes a1: "P a" 
  and     a2: "\<exists>!x. P x" 
  and     a3: "P a \<Longrightarrow> Q a"
  shows "Q (THE x. P x)"
apply(rule theI2)
apply(rule a1)
apply(subgoal_tac "\<exists>!x. P x")
apply(auto intro: a1 simp add: Ex1_def)
apply(fold Ex1_def)
apply(rule a2)
apply(subgoal_tac "x=a")
apply(simp)
apply(rule a3)
apply(assumption)
apply(subgoal_tac "\<exists>!x. P x")
apply(auto intro: a1 simp add: Ex1_def)
apply(fold Ex1_def)
apply(rule a2)
done

lemma rfun'_equiv:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  and   pi::"name prm"
  and   t ::"lam"  
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "pi\<bullet>(rfun' f1 f2 f3 t) = rfun' (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3) (pi\<bullet>t)"
apply(auto simp add: rfun'_def)
apply(subgoal_tac "\<exists>y. (t,y)\<in>rec f1 f2 f3 \<and> finite ((supp y)::name set)")
apply(auto)
apply(rule sym)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule rec_function[OF f, OF c])
apply(rule the1_equality)
apply(rule rec_function)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(simp add: pt_supp_finite_pi[OF pt_name_inst, OF at_name_inst])
apply(rule f)
apply(subgoal_tac "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)")
apply(auto)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(auto)
apply(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
apply(drule_tac x="(rev pi)\<bullet>x" in spec)
apply(subgoal_tac "(pi\<bullet>f3) (pi\<bullet>a) x  = pi\<bullet>(f3 a ((rev pi)\<bullet>x))")
apply(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
apply(subgoal_tac "pi\<bullet>(f3 a ((rev pi)\<bullet>x)) = (pi\<bullet>f3) (pi\<bullet>a) (pi\<bullet>((rev pi)\<bullet>x))")
apply(simp)
apply(simp add: pt_pi_rev[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_fun_app_eq[OF pt_name_inst, OF at_name_inst])
apply(rule c)
apply(rule rec_prm_equiv)
apply(rule f, rule c, assumption)
apply(rule rec_total_aux)
apply(rule f)
apply(rule c)
done

lemma rfun'_supports:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "((supp (f1,f2,f3,t))::name set) supports (rfun' f1 f2 f3 t)"
proof (auto simp add: "op supports_def" fresh_def[symmetric])
  fix a::"name" and b::"name"
  assume a1: "a\<sharp>(f1,f2,f3,t)"
  and    a2: "b\<sharp>(f1,f2,f3,t)"
  from a1 a2 have "[(a,b)]\<bullet>f1=f1" and "[(a,b)]\<bullet>f2=f2" and "[(a,b)]\<bullet>f3=f3" and "[(a,b)]\<bullet>t=t"
    by (simp_all add: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst] fresh_prod)
  thus "[(a,b)]\<bullet>(rfun' f1 f2 f3 t) = rfun' f1 f2 f3 t"
    by (simp add: rfun'_equiv[OF f, OF c])
qed

lemma rfun'_finite_supp:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "finite ((supp (rfun' f1 f2 f3 t))::name set)"
apply(rule supports_finite)
apply(rule rfun'_supports[OF f, OF c])
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod fs_name1)
apply(rule f)
done

lemma rfun'_prm:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  and   pi1::"name prm"
  and   pi2::"name prm"
  and   t ::"lam"  
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "rfun' f1 f2 f3 (pi1\<bullet>t) pi2 = rfun' f1 f2 f3 t (pi2@pi1)"
apply(auto simp add: rfun'_def)
apply(subgoal_tac "\<exists>y. (t,y)\<in>rec f1 f2 f3 \<and> finite ((supp y)::name set)")
apply(auto)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule rec_function[OF f, OF c])
apply(rule_tac a="\<lambda>pi2. y (pi2@pi1)" in theI2')
apply(rule rec_perm)
apply(rule f, rule c)
apply(assumption)
apply(rule rec_function)
apply(rule f)
apply(rule c)
apply(simp)
apply(rule rec_total_aux)
apply(rule f)
apply(rule c)
done

lemma rfun_Var:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "rfun f1 f2 f3 (Var c) = (f1 c)"
apply(auto simp add: rfun_def rfun'_def)
apply(subgoal_tac "(THE y. (Var c, y) \<in> rec f1 f2 f3) = (\<lambda>(pi::name prm). f1 (pi\<bullet>c))")(*A*)
apply(simp)
apply(rule the1_equality)
apply(rule rec_function)
apply(rule f)
apply(rule c)
apply(rule rec.r1)
done

lemma rfun_App:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "rfun f1 f2 f3 (App t1 t2) = (f2 (rfun f1 f2 f3 t1) (rfun f1 f2 f3 t2))"
apply(auto simp add: rfun_def rfun'_def)
apply(subgoal_tac "(THE y. (App t1 t2, y)\<in>rec f1 f2 f3) = 
      (\<lambda>(pi::name prm). f2 ((rfun' f1 f2 f3 t1) pi) ((rfun' f1 f2 f3 t2) pi))")(*A*)
apply(simp add: rfun'_def)
apply(rule the1_equality)
apply(rule rec_function[OF f, OF c])
apply(rule rec.r2)
apply(rule rfun'_finite_supp[OF f, OF c])
apply(subgoal_tac "\<exists>y. (t1,y)\<in>rec f1 f2 f3")
apply(erule exE, simp add: rfun'_def)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule rec_function[OF f, OF c])
apply(assumption)
apply(rule rec_total[OF f, OF c])
apply(rule rfun'_finite_supp[OF f, OF c])
apply(subgoal_tac "\<exists>y. (t2,y)\<in>rec f1 f2 f3")
apply(auto simp add: rfun'_def)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule rec_function[OF f, OF c])
apply(assumption)
apply(rule rec_total[OF f, OF c])
done 

lemma rfun_Lam_aux1:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "rfun f1 f2 f3 (Lam [a].t) = fresh_fun (\<lambda>a'. f3 a' (rfun' f1 f2 f3 t ([]@[(a,a')])))"
apply(simp add: rfun_def rfun'_def)
apply(subgoal_tac "(THE y. (Lam [a].t, y)\<in>rec f1 f2 f3) = 
        (\<lambda>(pi::name prm). fresh_fun(\<lambda>a'. f3 a' ((rfun' f1 f2 f3 t) (pi@[(a,a')]))))")(*A*)
apply(simp add: rfun'_def[symmetric])
apply(rule the1_equality)
apply(rule rec_function[OF f, OF c])
apply(rule rec.r3)
apply(rule rfun'_finite_supp[OF f, OF c])
apply(subgoal_tac "\<exists>y. (t,y)\<in>rec f1 f2 f3")
apply(erule exE, simp add: rfun'_def)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule rec_function[OF f, OF c])
apply(assumption)
apply(rule rec_total[OF f, OF c])
done

lemma rfun_Lam_aux2:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "b\<sharp>(a,t,f1,f2,f3)"
  shows "rfun f1 f2 f3 (Lam [b].([(a,b)]\<bullet>t)) = f3 b (rfun f1 f2 f3 ([(a,b)]\<bullet>t))"
proof -
  from f have f': "finite ((supp f3)::name set)" by (simp add: supp_prod)
  have eq1: "rfun f1 f2 f3 (Lam [b].([(a,b)]\<bullet>t)) = rfun f1 f2 f3 (Lam [a].t)"
  proof -
    have "Lam [a].t = Lam [b].([(a,b)]\<bullet>t)" using a
      by (force simp add: lam.inject alpha fresh_prod at_fresh[OF at_name_inst]
             pt_swap_bij[OF pt_name_inst, OF at_name_inst] 
             pt_fresh_left[OF pt_name_inst, OF at_name_inst] at_calc[OF at_name_inst])
    thus ?thesis by simp
  qed
  let ?g = "(\<lambda>a'. f3 a' (rfun' f1 f2 f3 t ([]@[(a,a')])))"
  have a0: "((supp (f3,a,([]::name prm),rfun' f1 f2 f3 t))::name set) supports ?g"
    by (supports_simp add: perm_append)
  have a1: "finite ((supp (f3,a,([]::name prm),rfun' f1 f2 f3 t))::name set)"
    using f' by (simp add: supp_prod fs_name1 rfun'_finite_supp[OF f, OF c])
  from a0 a1 have a2: "finite ((supp ?g)::name set)"
    by (rule supports_finite)
  have c0: "finite ((supp (rfun' f1 f2 f3 t))::name set)"
    by (rule rfun'_finite_supp[OF f, OF c])
  have c1: "\<exists>(a''::name). a''\<sharp>?g \<and> a''\<sharp>(?g a'')"
    by (rule f3_freshness_conditions_simple[OF f', OF c0, OF c])
  have c2: "b\<sharp>?g"
  proof -
    have fs_g: "finite ((supp (f1,f2,f3,t))::name set)" using f
      by (simp add: supp_prod fs_name1)
    have "((supp (f1,f2,f3,t))::name set) supports (rfun' f1 f2 f3 t)"
      by (simp add: rfun'_supports[OF f, OF c])
    hence c3: "b\<sharp>(rfun' f1 f2 f3 t)" using fs_g 
    proof(rule supports_fresh, simp add: fresh_def[symmetric])
      show "b\<sharp>(f1,f2,f3,t)" using a by (simp add: fresh_prod)
    qed
    show ?thesis 
    proof(rule supports_fresh[OF a0, OF a1], simp add: fresh_def[symmetric])
      show "b\<sharp>(f3,a,([]::name prm),rfun' f1 f2 f3 t)" using a c3
	by (simp add: fresh_prod fresh_list_nil)
    qed
  qed
  (* main proof *)
  have "rfun f1 f2 f3 (Lam [b].([(a,b)]\<bullet>t)) = rfun f1 f2 f3 (Lam [a].t)" by (simp add: eq1)
  also have "\<dots> = fresh_fun ?g" by (rule rfun_Lam_aux1[OF f, OF c])
  also have "\<dots> = ?g b" using c2
    by (rule fresh_fun_app[OF pt_name_inst, OF at_name_inst, OF a2, OF c1])
  also have "\<dots> = f3 b (rfun f1 f2 f3 ([(a,b)]\<bullet>t))"
    by (simp add: rfun_def rfun'_prm[OF f, OF c])
  finally show "rfun f1 f2 f3 (Lam [b].([(a,b)]\<bullet>t)) = f3 b (rfun f1 f2 f3 ([(a,b)]\<bullet>t))" .
qed


lemma rfun_Lam:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "b\<sharp>(f1,f2,f3)"
  shows "rfun f1 f2 f3 (Lam [b].t) = f3 b (rfun f1 f2 f3 t)"
proof -
  have "\<exists>(a::name). a\<sharp>(b,t)"
    by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1)
  then obtain a::"name" where a1: "a\<sharp>b" and a2: "a\<sharp>t" by (force simp add: fresh_prod)
  have "rfun f1 f2 f3 (Lam [b].t) = rfun f1 f2 f3 (Lam [b].(([(a,b)])\<bullet>([(a,b)]\<bullet>t)))"
    by (simp add: pt_swap_bij[OF pt_name_inst, OF at_name_inst])
  also have "\<dots> = f3 b (rfun f1 f2 f3 (([(a,b)])\<bullet>([(a,b)]\<bullet>t)))" 
  proof(rule rfun_Lam_aux2[OF f, OF c])
    have "b\<sharp>([(a,b)]\<bullet>t)" using a1 a2
      by (simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst] at_calc[OF at_name_inst] 
        at_fresh[OF at_name_inst])
    thus "b\<sharp>(a,[(a,b)]\<bullet>t,f1,f2,f3)" using a a1 by (force simp add: fresh_prod at_fresh[OF at_name_inst])
  qed
  also have "\<dots> = f3 b (rfun f1 f2 f3 t)" by (simp add: pt_swap_bij[OF pt_name_inst, OF at_name_inst])
  finally show ?thesis .
qed
  
lemma rec_unique:
  fixes fun::"lam \<Rightarrow> ('a::pt_name)"
  and   f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a1: "\<forall>c. fun (Var c) = f1 c" 
  and     a2: "\<forall>t1 t2. fun (App t1 t2) = f2 (fun t1) (fun t2)" 
  and     a3: "\<forall>a t. a\<sharp>(f1,f2,f3) \<longrightarrow> fun (Lam [a].t) = f3 a (fun t)"
  shows "fun t = rfun f1 f2 f3 t"
(*apply(nominal_induct t rule: lam_induct')*)
apply (rule lam_induct'[of "\<lambda>_. ((supp (f1,f2,f3))::name set)" "\<lambda>t _. fun t = rfun f1 f2 f3 t"])
(* finite support *)
apply(rule f)
(* VAR *)
apply(simp add: a1 rfun_Var[OF f, OF c, symmetric])
(* APP *)
apply(simp add: a2 rfun_App[OF f, OF c, symmetric])
(* LAM *)
apply(fold fresh_def)
apply(simp add: a3 rfun_Lam[OF f, OF c, symmetric])
done

lemma rec_function:
  fixes f1::"('a::pt_name) f1_ty"
  and   f2::"('a::pt_name) f2_ty"
  and   f3::"('a::pt_name) f3_ty"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "(\<exists>!(fun::lam \<Rightarrow> ('a::pt_name)).
              (\<forall>c.     fun (Var c)     = f1 c) \<and> 
              (\<forall>t1 t2. fun (App t1 t2) = f2 (fun t1) (fun t2)) \<and> 
              (\<forall>a t.   a\<sharp>(f1,f2,f3) \<longrightarrow> fun (Lam [a].t) = f3 a (fun t)))"
apply(rule_tac a="\<lambda>t. rfun f1 f2 f3 t" in ex1I)
(* existence *)
apply(simp add: rfun_Var[OF f, OF c])
apply(simp add: rfun_App[OF f, OF c])
apply(simp add: rfun_Lam[OF f, OF c])
(* uniqueness *)
apply(auto simp add: expand_fun_eq)
apply(rule rec_unique[OF f, OF c])
apply(force)+
done

(* "real" recursion *)

types 'a f1_ty' = "name\<Rightarrow>('a::pt_name)"
      'a f2_ty' = "lam\<Rightarrow>lam\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>('a::pt_name)"
      'a f3_ty' = "lam\<Rightarrow>name\<Rightarrow>'a\<Rightarrow>('a::pt_name)"

constdefs
  rfun_gen' :: "'a f1_ty' \<Rightarrow> 'a f2_ty' \<Rightarrow> 'a f3_ty' \<Rightarrow> lam \<Rightarrow> (lam\<times>'a::pt_name)" 
  "rfun_gen' f1 f2 f3 t \<equiv> (rfun 
                             (\<lambda>(a::name). (Var a,f1 a)) 
                             (\<lambda>r1 r2. (App (fst r1) (fst r2), f2 (fst r1) (fst r2) (snd r1) (snd r2))) 
                             (\<lambda>(a::name) r. (Lam [a].(fst r),f3 (fst r) a (snd r)))
                           t)"

  rfun_gen :: "'a f1_ty' \<Rightarrow> 'a f2_ty' \<Rightarrow> 'a f3_ty' \<Rightarrow> lam \<Rightarrow> 'a::pt_name" 
  "rfun_gen f1 f2 f3 t \<equiv> snd(rfun_gen' f1 f2 f3 t)"



lemma f1'_supports:
  fixes f1::"('a::pt_name) f1_ty'"
  shows "((supp f1)::name set) supports (\<lambda>(a::name). (Var a,f1 a))"
  by (supports_simp)

lemma f2'_supports:
  fixes f2::"('a::pt_name) f2_ty'"
  shows "((supp f2)::name set) supports 
                         (\<lambda>r1 r2. (App (fst r1) (fst r2), f2 (fst r1) (fst r2) (snd r1) (snd r2)))"
  by (supports_simp add: perm_fst perm_snd)  

lemma f3'_supports:
  fixes f3::"('a::pt_name) f3_ty'"
  shows "((supp f3)::name set) supports (\<lambda>(a::name) r. (Lam [a].(fst r),f3 (fst r) a (snd r)))"
by (supports_simp add: perm_fst perm_snd)

lemma fcb': 
  fixes f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows  "\<exists>a.  a \<sharp> (\<lambda>a r. (Lam [a].fst r, f3 (fst r) a (snd r))) \<and>
                (\<forall>y.  a \<sharp> (Lam [a].fst y, f3 (fst y) a (snd y)))"
using c f
apply(auto)
apply(rule_tac x="a" in exI)
apply(auto simp add: abs_fresh fresh_prod)
apply(rule supports_fresh)
apply(rule f3'_supports)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
done

lemma fsupp':
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  shows "finite((supp
          (\<lambda>a. (Var a, f1 a),
           \<lambda>r1 r2.
              (App (fst r1) (fst r2),
               f2 (fst r1) (fst r2) (snd r1) (snd r2)),
           \<lambda>a r. (Lam [a].fst r, f3 (fst r) a (snd r))))::name set)"
using f
apply(auto simp add: supp_prod)
apply(rule supports_finite)
apply(rule f1'_supports)
apply(assumption)
apply(rule supports_finite)
apply(rule f2'_supports)
apply(assumption)
apply(rule supports_finite)
apply(rule f3'_supports)
apply(assumption)
done

lemma rfun_gen'_fst:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)" 
  and     c: "(\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y))"
  shows "fst (rfun_gen' f1 f2 f3 t) = t"
apply (rule lam_induct'[of "\<lambda>_. ((supp (f1,f2,f3))::name set)" "\<lambda>t _. fst (rfun_gen' f1 f2 f3 t) = t"])
apply(simp add: f)
apply(unfold rfun_gen'_def)
apply(simp only: rfun_Var[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(simp)
apply(simp only: rfun_App[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(simp)
apply(fold fresh_def)
apply(auto)
apply(rule trans)
apply(rule_tac f="fst" in arg_cong)
apply(rule rfun_Lam[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(auto simp add: fresh_prod)
apply(rule supports_fresh)
apply(rule f1'_supports)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(rule f)
apply(simp add: fresh_def)
apply(rule supports_fresh)
apply(rule f2'_supports)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(rule f)
apply(simp add: fresh_def)
apply(rule supports_fresh)
apply(rule f3'_supports)
apply(subgoal_tac "finite ((supp (f1,f2,f3))::name set)")
apply(simp add: supp_prod)
apply(rule f)
apply(simp add: fresh_def)
done

lemma rfun_gen'_Var:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun_gen' f1 f2 f3 (Var c) = (Var c, f1 c)"
apply(simp add: rfun_gen'_def)
apply(simp add: rfun_Var[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
done

lemma rfun_gen'_App:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun_gen' f1 f2 f3 (App t1 t2) = 
                (App t1 t2, f2 t1 t2 (rfun_gen f1 f2 f3 t1) (rfun_gen f1 f2 f3 t2))"
apply(simp add: rfun_gen'_def)
apply(rule trans)
apply(rule rfun_App[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(fold rfun_gen'_def)
apply(simp_all add: rfun_gen'_fst[OF f, OF c])
apply(simp_all add: rfun_gen_def)
done

lemma rfun_gen'_Lam:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  and     a: "b\<sharp>(f1,f2,f3)"
  shows "rfun_gen' f1 f2 f3 (Lam [b].t) = (Lam [b].t, f3 t b (rfun_gen f1 f2 f3 t))"
using a f
apply(simp add: rfun_gen'_def)
apply(rule trans)
apply(rule rfun_Lam[OF fsupp'[OF f],OF fcb'[OF f, OF c]])
apply(auto simp add: fresh_prod)
apply(rule supports_fresh)
apply(rule f1'_supports)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
apply(rule supports_fresh)
apply(rule f2'_supports)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
apply(rule supports_fresh)
apply(rule f3'_supports)
apply(simp add: supp_prod)
apply(simp add: fresh_def)
apply(fold rfun_gen'_def)
apply(simp_all add: rfun_gen'_fst[OF f, OF c])
apply(simp_all add: rfun_gen_def)
done

lemma rfun_gen_Var:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun_gen f1 f2 f3 (Var c) = f1 c"
apply(unfold rfun_gen_def)
apply(simp add: rfun_gen'_Var[OF f, OF c])
done

lemma rfun_gen_App:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  shows "rfun_gen f1 f2 f3 (App t1 t2) = f2 t1 t2 (rfun_gen f1 f2 f3 t1) (rfun_gen f1 f2 f3 t2)"
apply(unfold rfun_gen_def)
apply(simp add: rfun_gen'_App[OF f, OF c])
apply(simp add: rfun_gen_def)
done

lemma rfun_gen_Lam:
  fixes f1::"('a::pt_name) f1_ty'"
  and   f2::"('a::pt_name) f2_ty'"
  and   f3::"('a::pt_name) f3_ty'"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name) t. a\<sharp>f3 t a y)"
  and     a: "b\<sharp>(f1,f2,f3)"
  shows "rfun_gen f1 f2 f3 (Lam [b].t) = f3 t b (rfun_gen f1 f2 f3 t)"
using a
apply(unfold rfun_gen_def)
apply(simp add: rfun_gen'_Lam[OF f, OF c])
apply(simp add: rfun_gen_def)
done

instance nat :: pt_name
apply(intro_classes)
apply(simp_all add: perm_nat_def)
done

constdefs 
  depth_Var :: "name \<Rightarrow> nat"
  "depth_Var \<equiv> \<lambda>(a::name). 1"
  
  depth_App :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "depth_App \<equiv> \<lambda>n1 n2. (max n1 n2)+1"

  depth_Lam :: "name \<Rightarrow> nat \<Rightarrow> nat"
  "depth_Lam \<equiv> \<lambda>(a::name) n. n+1"

  depth_lam :: "lam \<Rightarrow> nat"
  "depth_lam \<equiv> rfun depth_Var depth_App depth_Lam"

lemma supp_depth_Var:
  shows "((supp depth_Var)::name set)={}"
  apply(simp add: depth_Var_def)
  apply(simp add: supp_def)
  apply(simp add: perm_fun_def)
  apply(simp add: perm_nat_def)
  done

lemma supp_depth_App:
  shows "((supp depth_App)::name set)={}"
  apply(simp add: depth_App_def)
  apply(simp add: supp_def)
  apply(simp add: perm_fun_def)
  apply(simp add: perm_nat_def)
  done

lemma supp_depth_Lam:
  shows "((supp depth_Lam)::name set)={}"
  apply(simp add: depth_Lam_def)
  apply(simp add: supp_def)
  apply(simp add: perm_fun_def)
  apply(simp add: perm_nat_def)
  done
 

lemma fin_supp_depth:
  shows "finite ((supp (depth_Var,depth_App,depth_Lam))::name set)"
  using supp_depth_Var supp_depth_Lam supp_depth_App
by (simp add: supp_prod)

lemma fresh_depth_Lam:
  shows "\<exists>(a::name). a\<sharp>depth_Lam \<and> (\<forall>n. a\<sharp>depth_Lam a n)"
apply(rule exI)
apply(rule conjI)
apply(simp add: fresh_def supp_depth_Lam)
apply(auto simp add: depth_Lam_def)
apply(unfold fresh_def)
apply(simp add: supp_def)
apply(simp add: perm_nat_def)
done

lemma depth_Var:
  shows "depth_lam (Var c) = 1"
apply(simp add: depth_lam_def)
apply(simp add: rfun_Var[OF fin_supp_depth, OF fresh_depth_Lam])
apply(simp add: depth_Var_def)
done

lemma depth_App:
  shows "depth_lam (App t1 t2) = (max (depth_lam t1) (depth_lam t2))+1"
apply(simp add: depth_lam_def)
apply(simp add: rfun_App[OF fin_supp_depth, OF fresh_depth_Lam])
apply(simp add: depth_App_def)
done

lemma depth_Lam:
  shows "depth_lam (Lam [a].t) = (depth_lam t)+1"
apply(simp add: depth_lam_def)
apply(rule trans)
apply(rule rfun_Lam[OF fin_supp_depth, OF fresh_depth_Lam])
apply(simp add: fresh_def supp_prod supp_depth_Var supp_depth_App supp_depth_Lam)
apply(simp add: depth_Lam_def)
done


(* substitution *)

constdefs 
  subst_Var :: "name \<Rightarrow>lam \<Rightarrow> name \<Rightarrow> lam"
  "subst_Var b t \<equiv> \<lambda>a. (if a=b then t else (Var a))"
  
  subst_App :: "name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_App b t \<equiv> \<lambda>r1 r2. App r1 r2"

  subst_Lam :: "name \<Rightarrow> lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"
  "subst_Lam b t \<equiv> \<lambda>a r. Lam [a].r"

  subst_lam :: "name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_lam b t \<equiv> rfun (subst_Var b t) (subst_App b t) (subst_Lam b t)"


lemma supports_subst_Var:
  shows "((supp (b,t))::name set) supports (subst_Var b t)"
apply(supports_simp add: subst_Var_def)
apply(rule impI)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
done

lemma supports_subst_App:
  shows "((supp (b,t))::name set) supports subst_App b t"
by (supports_simp add: subst_App_def)

lemma supports_subst_Lam:
  shows "((supp (b,t))::name set) supports subst_Lam b t"
  by (supports_simp add: subst_Lam_def)


lemma fin_supp_subst:
  shows "finite ((supp (subst_Var b t,subst_App b t,subst_Lam b t))::name set)"
apply(auto simp add: supp_prod)
apply(rule supports_finite)
apply(rule supports_subst_Var)
apply(simp add: fs_name1)
apply(rule supports_finite)
apply(rule supports_subst_App)
apply(simp add: fs_name1)
apply(rule supports_finite)
apply(rule supports_subst_Lam)
apply(simp add: fs_name1)
done

lemma fresh_subst_Lam:
  shows "\<exists>(a::name). a\<sharp>(subst_Lam b t)\<and> (\<forall>y. a\<sharp>(subst_Lam b t) a y)"
apply(subgoal_tac "\<exists>(c::name). c\<sharp>(b,t)")
apply(auto)
apply(rule_tac x="c" in exI)
apply(auto)
apply(rule supports_fresh)
apply(rule supports_subst_Lam)
apply(simp_all add: fresh_def[symmetric] fs_name1)
apply(simp add: subst_Lam_def)
apply(simp add: abs_fresh)
apply(rule at_exists_fresh[OF at_name_inst])
apply(simp add: fs_name1)
done

lemma subst_Var:
  shows "subst_lam b t (Var a) = (if a=b then t else (Var a))"
apply(simp add: subst_lam_def)
apply(auto simp add: rfun_Var[OF fin_supp_subst, OF fresh_subst_Lam])
apply(auto simp add: subst_Var_def)
done

lemma subst_App:
  shows "subst_lam b t (App t1 t2) = App (subst_lam b t t1) (subst_lam b t t2)"
apply(simp add: subst_lam_def)
apply(auto simp add: rfun_App[OF fin_supp_subst, OF fresh_subst_Lam])
apply(auto simp add: subst_App_def)
done

lemma subst_Lam:
  assumes a: "a\<sharp>(b,t)"
  shows "subst_lam b t (Lam [a].t1) = Lam [a].(subst_lam b t t1)"
using a
apply(simp add: subst_lam_def)
apply(subgoal_tac "a\<sharp>(subst_Var b t,subst_App b t,subst_Lam b t)")
apply(auto simp add: rfun_Lam[OF fin_supp_subst, OF fresh_subst_Lam])
apply(simp (no_asm) add: subst_Lam_def)
apply(auto simp add: fresh_prod)
apply(rule supports_fresh)
apply(rule supports_subst_Var)
apply(simp_all add: fs_name1 fresh_def[symmetric] fresh_prod)
apply(rule supports_fresh)
apply(rule supports_subst_App)
apply(simp_all add: fs_name1 fresh_def[symmetric] fresh_prod)
apply(rule supports_fresh)
apply(rule supports_subst_Lam)
apply(simp_all add: fs_name1 fresh_def[symmetric] fresh_prod)
done

lemma subst_Lam':
  assumes a: "a\<noteq>b"
  and     b: "a\<sharp>t"
  shows "subst_lam b t (Lam [a].t1) = Lam [a].(subst_lam b t t1)"
apply(rule subst_Lam)
apply(simp add: fresh_prod a b fresh_atm)
done

consts
  subst_syn  :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [100,100,100] 900)
translations 
  "t1[a::=t2]" \<rightleftharpoons> "subst_lam a t2 t1"

declare subst_Var[simp]
declare subst_App[simp]
declare subst_Lam[simp]
declare subst_Lam'[simp]

lemma subst_eqvt[simp]:
  fixes pi:: "name prm"
  and   t1:: "lam"
  and   t2:: "lam"
  and   a :: "name"
  shows "pi\<bullet>(t1[a::=t2]) = (pi\<bullet>t1)[(pi\<bullet>a)::=(pi\<bullet>t2)]"
apply(nominal_induct t1 rule: lam_induct)
apply(auto)
apply(auto simp add: perm_bij fresh_prod fresh_atm)
apply(subgoal_tac "(aa\<bullet>ab)\<sharp>(aa\<bullet>a,aa\<bullet>b)")(*A*)
apply(simp) 
apply(simp add: perm_bij fresh_prod fresh_atm pt_fresh_bij[OF pt_name_inst, OF at_name_inst]) 
done

lemma subst_supp: "supp(t1[a::=t2])\<subseteq>(((supp(t1)-{a})\<union>supp(t2))::name set)"
apply(nominal_induct t1 rule: lam_induct)
apply(auto simp add: lam.supp supp_atm fresh_prod abs_supp)
apply(blast)
apply(blast)
done

(* parallel substitution *)


consts
  "dom_sss" :: "(name\<times>lam) list \<Rightarrow> (name list)"
primrec
  "dom_sss []    = []"
  "dom_sss (x#\<theta>) = (fst x)#(dom_sss \<theta>)" 

consts
  "apply_sss"  :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam" (" _ < _ >" [80,80] 80)
primrec  
"(x#\<theta>)<a>  = (if (a = fst x) then (snd x) else \<theta><a>)" 


lemma apply_sss_eqvt[rule_format]:
  fixes pi::"name prm"
  shows "a\<in>set (dom_sss \<theta>) \<longrightarrow> pi\<bullet>(\<theta><a>) = (pi\<bullet>\<theta>)<pi\<bullet>a>"
apply(induct_tac \<theta>)
apply(auto)
apply(simp add: pt_bij[OF pt_name_inst, OF at_name_inst])
done

lemma dom_sss_eqvt[rule_format]:
  fixes pi::"name prm"
  shows "((pi\<bullet>a)\<in>set (dom_sss \<theta>)) =  (a\<in>set (dom_sss ((rev pi)\<bullet>\<theta>)))"
apply(induct_tac \<theta>)
apply(auto)
apply(simp_all add: pt_rev_pi[OF pt_name_inst, OF at_name_inst])
apply(simp_all add: pt_pi_rev[OF pt_name_inst, OF at_name_inst])
done

constdefs 
  psubst_Var :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam"
  "psubst_Var \<theta> \<equiv> \<lambda>a. (if a\<in>set (dom_sss \<theta>) then \<theta><a> else (Var a))"
  
  psubst_App :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_App \<theta> \<equiv> \<lambda>r1 r2. App r1 r2"

  psubst_Lam :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_Lam \<theta> \<equiv> \<lambda>a r. Lam [a].r"

  psubst_lam :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_lam \<theta> \<equiv> rfun (psubst_Var \<theta>) (psubst_App \<theta>) (psubst_Lam \<theta>)"

lemma supports_psubst_Var:
  shows "((supp \<theta>)::name set) supports (psubst_Var \<theta>)"
  by (supports_simp add: psubst_Var_def apply_sss_eqvt dom_sss_eqvt)

lemma supports_psubst_App:
  shows "((supp \<theta>)::name set) supports psubst_App \<theta>"
  by (supports_simp add: psubst_App_def)

lemma supports_psubst_Lam:
  shows "((supp \<theta>)::name set) supports psubst_Lam \<theta>"
  by (supports_simp add: psubst_Lam_def)

lemma fin_supp_psubst:
  shows "finite ((supp (psubst_Var \<theta>,psubst_App \<theta>,psubst_Lam \<theta>))::name set)"
apply(auto simp add: supp_prod)
apply(rule supports_finite)
apply(rule supports_psubst_Var)
apply(simp add: fs_name1)
apply(rule supports_finite)
apply(rule supports_psubst_App)
apply(simp add: fs_name1)
apply(rule supports_finite)
apply(rule supports_psubst_Lam)
apply(simp add: fs_name1)
done

lemma fresh_psubst_Lam:
  shows "\<exists>(a::name). a\<sharp>(psubst_Lam \<theta>)\<and> (\<forall>y. a\<sharp>(psubst_Lam \<theta>) a y)"
apply(subgoal_tac "\<exists>(c::name). c\<sharp>\<theta>")
apply(auto)
apply(rule_tac x="c" in exI)
apply(auto)
apply(rule supports_fresh)
apply(rule supports_psubst_Lam)
apply(simp_all add: fresh_def[symmetric] fs_name1)
apply(simp add: psubst_Lam_def)
apply(simp add: abs_fresh)
apply(rule at_exists_fresh[OF at_name_inst])
apply(simp add: fs_name1)
done

lemma psubst_Var:
  shows "psubst_lam \<theta> (Var a) = (if a\<in>set (dom_sss \<theta>) then \<theta><a> else (Var a))"
apply(simp add: psubst_lam_def)
apply(auto simp add: rfun_Var[OF fin_supp_psubst, OF fresh_psubst_Lam])
apply(auto simp add: psubst_Var_def)
done

lemma psubst_App:
  shows "psubst_lam \<theta> (App t1 t2) = App (psubst_lam \<theta> t1) (psubst_lam \<theta> t2)"
apply(simp add: psubst_lam_def)
apply(auto simp add: rfun_App[OF fin_supp_psubst, OF fresh_psubst_Lam])
apply(auto simp add: psubst_App_def)
done

lemma psubst_Lam:
  assumes a: "a\<sharp>\<theta>"
  shows "psubst_lam \<theta> (Lam [a].t1) = Lam [a].(psubst_lam \<theta> t1)"
using a
apply(simp add: psubst_lam_def)
apply(subgoal_tac "a\<sharp>(psubst_Var \<theta>,psubst_App \<theta>,psubst_Lam \<theta>)")
apply(auto simp add: rfun_Lam[OF fin_supp_psubst, OF fresh_psubst_Lam])
apply(simp (no_asm) add: psubst_Lam_def)
apply(auto simp add: fresh_prod)
apply(rule supports_fresh)
apply(rule supports_psubst_Var)
apply(simp_all add: fs_name1 fresh_def[symmetric] fresh_prod)
apply(rule supports_fresh)
apply(rule supports_psubst_App)
apply(simp_all add: fs_name1 fresh_def[symmetric] fresh_prod)
apply(rule supports_fresh)
apply(rule supports_psubst_Lam)
apply(simp_all add: fs_name1 fresh_def[symmetric] fresh_prod)
done

declare psubst_Var[simp]
declare psubst_App[simp]
declare psubst_Lam[simp]

consts
  psubst_syn  :: "lam \<Rightarrow> (name\<times>lam) list \<Rightarrow> lam" ("_[<_>]" [100,100] 900)
translations 
  "t[<\<theta>>]" \<rightleftharpoons> "psubst_lam \<theta> t"

end