(* $Id$ *)
theory Iteration
imports "../nominal"
begin

atom_decl name

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)
 
types 'a f1_ty  = "name\<Rightarrow>('a::pt_name)"
      'a f2_ty  = "'a\<Rightarrow>'a\<Rightarrow>('a::pt_name)"
      'a f3_ty  = "name\<Rightarrow>'a\<Rightarrow>('a::pt_name)"

consts
  it :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> (lam \<times> (name prm \<Rightarrow> 'a::pt_name)) set"

inductive "it f1 f2 f3"
intros
it1: "(Var a,\<lambda>pi. f1(pi\<bullet>a)) \<in> it f1 f2 f3"
it2: "\<lbrakk>(t1,r1) \<in> it f1 f2 f3; (t2,r2) \<in> it f1 f2 f3\<rbrakk> \<Longrightarrow> 
      (App t1 t2,\<lambda>pi. f2 (r1 pi) (r2 pi)) \<in> it f1 f2 f3"
it3: "(t,r) \<in> it f1 f2 f3 \<Longrightarrow> 
      (Lam [a].t,\<lambda>pi. fresh_fun (\<lambda>a'. f3 a' (r (pi@[(a,a')])))) \<in> it f1 f2 f3"

constdefs
  itfun' :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> lam \<Rightarrow> name prm \<Rightarrow> ('a::pt_name)" 
  "itfun' f1 f2 f3 t \<equiv> (THE y. (t,y) \<in> it f1 f2 f3)"

  itfun :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> lam \<Rightarrow> ('a::pt_name)" 
  "itfun f1 f2 f3 t \<equiv> itfun' f1 f2 f3 t ([]::name prm)"

lemma it_total:
  shows "\<exists>r. (t,r) \<in> it f1 f2 f3"
  apply(induct t rule: lam.induct_weak)
  apply(auto intro: it.intros)
  done

lemma it_prm_eq:
  assumes a: "(t,y) \<in> it f1 f2 f3"
  and     b: "pi1 \<triangleq> pi2"
  shows "y pi1 = y pi2"
using a b
apply(induct fixing: pi1 pi2)
apply(auto simp add: pt3[OF pt_name_inst])
apply(rule_tac f="fresh_fun" in arg_cong)
apply(auto simp add: expand_fun_eq)
apply(drule_tac x="pi1@[(a,x)]" in meta_spec)
apply(drule_tac x="pi2@[(a,x)]" in meta_spec)
apply(force simp add: prm_eq_def pt2[OF pt_name_inst])
done

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

text {* FIXME: this lemma should be thrown out somehow *}
lemma f3_freshness_conditions:
  fixes f3::"('a::pt_name) f3_ty"
  and   y ::"name prm \<Rightarrow> 'a::pt_name"
  and   a ::"name"
  and   pi1::"name prm"
  and   pi2::"name prm"
  assumes a: "finite ((supp f3)::name set)"
  and     b: "finite ((supp y)::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>(a''::name). a''\<sharp>(\<lambda>a'. f3 a' (y (pi1@[(a,a')]@pi2))) \<and> 
                       a''\<sharp>(\<lambda>a'. f3 a' (y (pi1@[(a,a')]@pi2))) a''" 
proof -
  from c obtain a' where d0: "a'\<sharp>f3" and d1: "\<forall>(y::'a::pt_name). a'\<sharp>f3 a' y" by force
  have "\<exists>(a''::name). a''\<sharp>(f3,a,a',pi1,pi2,y)" 
    by (rule at_exists_fresh[OF at_name_inst],  simp add: supp_prod fs_name1 a b)
  then obtain a'' where d2: "a''\<sharp>f3" and d3: "a''\<noteq>a'" and d3b: "a''\<sharp>(f3,a,pi1,pi2,y)" 
    by (auto simp add: fresh_prod at_fresh[OF at_name_inst])
  have d3c: "a''\<notin>((supp (f3,a,pi1,pi2,y))::name set)" using d3b by (simp add: fresh_def)
  have d4: "a''\<sharp>f3 a'' (y (pi1@[(a,a'')]@pi2))"
  proof -
    have d5: "[(a'',a')]\<bullet>f3 = f3" 
      by (rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst, OF d2, OF d0]) 
    from d1 have "\<forall>(y::'a::pt_name). ([(a'',a')]\<bullet>a')\<sharp>([(a'',a')]\<bullet>(f3 a' y))"
      by (simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
    hence "\<forall>(y::'a::pt_name). a''\<sharp>(f3 a'' ([(a'',a')]\<bullet>y))" using d3 d5 
      by (simp add: at_calc[OF at_name_inst] pt_fun_app_eq[OF pt_name_inst, OF at_name_inst])
    hence "a''\<sharp>(f3 a'' ([(a'',a')]\<bullet>((rev [(a'',a')])\<bullet>(y (pi1@[(a,a'')]@pi2)))))" by force
    thus ?thesis by (simp only: pt_pi_rev[OF pt_name_inst, OF at_name_inst])
  qed
  have d6: "a''\<sharp>(\<lambda>a'. f3 a' (y (pi1@[(a,a')]@pi2)))"
  proof -
    from a b have d7: "finite ((supp (f3,a,pi1,pi2,y))::name set)" by (simp add: supp_prod fs_name1)
    have e: "((supp (f3,a,pi1,pi2,y))::name set) supports (\<lambda>a'. f3 a' (y (pi1@[(a,a')]@pi2)))" 
      by (supports_simp add: perm_append)
    from e d7 d3c show ?thesis by (rule supports_fresh)
  qed
  from d6 d4 show ?thesis by force
qed

lemma it_fin_supp: 
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  and     a: "(t,r) \<in> it f1 f2 f3"
  shows "finite ((supp r)::name set)"
using a 
proof (induct)
  case it1 thus ?case using f by (finite_guess add: supp_prod fs_name1)
next
  case it2 thus ?case using f by (finite_guess add: supp_prod fs_name1)
next
  case (it3 c r t)
  have ih: "finite ((supp r)::name set)" by fact
  let ?g' = "\<lambda>pi a'. f3 a' (r (pi@[(c,a')]))"     --"helper function"
  have fact1: "\<forall>pi. finite ((supp (?g' pi))::name set)" using f ih
    by (rule_tac allI, finite_guess add: perm_append supp_prod fs_name1)
  have fact2: "\<forall>pi. \<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" 
  proof 
    fix pi::"name prm"
    show "\<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" using f c ih
      by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
  qed
  show ?case using fact1 fact2 ih f
    by (finite_guess add: fresh_fun_eqvt perm_append supp_prod fs_name1)
qed 

lemma it_trans: 
  shows "\<lbrakk>(t,r)\<in>rec f1 f2 f3; r=r'\<rbrakk> \<Longrightarrow> (t,r')\<in>rec f1 f2 f3" by simp

lemma it_perm_aux:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(t,y) \<in> it f1 f2 f3"
  shows "(pi1\<bullet>t, \<lambda>pi2. y (pi2@pi1)) \<in> it f1 f2 f3"
using a
proof (induct)
  case (it1 c) show ?case by (auto simp add: pt_name2, rule it.intros)
next
  case (it2 t1 t2 r1 r2) thus ?case by (auto intro: it.intros) 
next
  case (it3 c r t)
  let ?g  = "\<lambda>pi' a'. f3 a' (r (pi'@[(pi1\<bullet>c,a')]@pi1))"
  and ?h  = "\<lambda>pi' a'. f3 a' (r ((pi'@pi1)@[(c,a')]))" 
  have ih': "(t,r) \<in> it f1 f2 f3" by fact
  hence fin_r: "finite ((supp r)::name set)" using f c by (auto intro: it_fin_supp)
  have ih: "(pi1\<bullet>t,\<lambda>pi2. r (pi2@pi1)) \<in> it f1 f2 f3" by fact
  hence "(Lam [(pi1\<bullet>c)].(pi1\<bullet>t),\<lambda>pi'. fresh_fun (?g pi')) \<in> it f1 f2 f3"
    by (auto intro: it_trans it.intros) 
  moreover
  have "\<forall>pi'. (fresh_fun (?g pi')) = (fresh_fun (?h pi'))" 
  proof 
    fix pi'::"name prm"
    have fin_g: "finite ((supp (?g pi'))::name set)"
      using f fin_r by (finite_guess add: perm_append supp_prod fs_name1)
    have fr_g: "\<exists>(a::name). (a\<sharp>(?g pi')\<and> a\<sharp>(?g pi' a))" 
      using f c fin_r by (rule_tac f3_freshness_conditions, simp_all add: supp_prod)
    have fin_h: "finite ((supp (?h pi'))::name set)"
      using f fin_r by (finite_guess add: perm_append supp_prod fs_name1)
    have fr_h: "\<exists>(a::name). (a\<sharp>(?h pi')\<and> a\<sharp>(?h pi' a))" 
      using f c fin_r by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
    show "fresh_fun (?g pi') = fresh_fun (?h pi')" 
    proof -
      have "\<exists>(d::name). d\<sharp>(?g pi', ?h pi', pi1)" using fin_g fin_h
	by (rule_tac at_exists_fresh[OF at_name_inst], simp only: supp_prod finite_Un fs_name1, simp)
      then obtain d::"name" where f1: "d\<sharp>?g pi'" and f2: "d\<sharp>?h pi'" and f3: "d\<sharp>(rev pi1)"
	by (auto simp only: fresh_prod fresh_list_rev)
      have "?g pi' d = ?h pi' d" 
      proof -
	have "r (pi'@[(pi1\<bullet>c,d)]@pi1) = r ((pi'@pi1)@[(c,d)])" using f3 ih'
	  by (auto intro!: it_prm_eq at_prm_eq_append[OF at_name_inst]
              simp only: append_assoc at_ds10[OF at_name_inst])
	then show ?thesis by simp
      qed
      then show "fresh_fun (?g pi') = fresh_fun (?h pi')"
	using f1 fin_g fr_g f2 fin_h fr_h
	by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
    qed
  qed
  hence "(\<lambda>pi'. (fresh_fun (?g pi'))) = (\<lambda>pi'. (fresh_fun (?h pi')))" by (simp add: expand_fun_eq)
  ultimately show ?case by simp
qed

lemma it_perm:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(pi\<bullet>t,y) \<in> it f1 f2 f3"
  shows "(t, \<lambda>pi2. y (pi2@(rev pi))) \<in> it f1 f2 f3"
proof - 
  from a have "((rev pi)\<bullet>(pi\<bullet>t),\<lambda>pi2. y (pi2@(rev pi))) \<in> it f1 f2 f3" 
    using f c by (simp add: it_perm_aux)
  thus ?thesis by perm_simp
qed

lemma it_unique:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(t,y) \<in> it f1 f2 f3"
  and     b: "(t,y') \<in> it f1 f2 f3"
  shows "y pi = y' pi"
using a b
proof (induct fixing: y' pi)
  case (it1 c) thus ?case by (cases, simp_all add: lam.inject)
next
  case (it2 r1 r2 t1 t2)
  with `(App t1 t2, y') \<in> it f1 f2 f3` show ?case 
    by (cases, simp_all (no_asm_use) add: lam.inject, force)
next
  case (it3 c r t r')
  have "(t,r) \<in> it f1 f2 f3" by fact
  hence fin_r: "finite ((supp r)::name set)" using f c by (simp only: it_fin_supp)
  have ih: "\<And>r' pi. (t,r') \<in> it f1 f2 f3 \<Longrightarrow> r pi = r' pi" by fact
  have "(Lam [c].t, r') \<in> it f1 f2 f3" by fact
  then show "fresh_fun (\<lambda>a'. f3 a' (r (pi@[(c,a')]))) = r' pi"
  proof (cases, auto simp add: lam.inject)
    fix a::"name" and t'::"lam" and r''::"name prm\<Rightarrow>'a::pt_name"
    assume i5: "[c].t = [a].t'"
    and    i6: "(t',r'') \<in> it f1 f2 f3"
    hence fin_r'': "finite ((supp r'')::name set)" using f c by (auto intro: it_fin_supp)
    let ?g = "\<lambda>a'. f3 a' (r (pi@[(c,a')]))"
    and ?h = "\<lambda>a'. f3 a' (r'' (pi@[(a,a')]))"
    show "fresh_fun ?g = fresh_fun ?h" using i5
    proof (cases "a=c")
      case True
      have i7: "a=c" by fact
      with i5 have i8: "t=t'" by (simp add: alpha)
      show "fresh_fun ?g = fresh_fun ?h" using i6 i7 i8 ih by simp
    next
      case False
      assume i9: "a\<noteq>c"
      with i5[symmetric] have i10: "t'=[(a,c)]\<bullet>t" and i11: "a\<sharp>t" by (simp_all add: alpha)
      have fin_g: "finite ((supp ?g)::name set)"
	using f fin_r by (finite_guess add: perm_append supp_prod fs_name1)
      have fin_h: "finite ((supp ?h)::name set)" 
	using f fin_r'' by (finite_guess add: perm_append supp_prod fs_name1)
      have fr_g: "\<exists>(a''::name). a''\<sharp>?g \<and> a''\<sharp>(?g a'')"
	using f c fin_r by (simp add:  f3_freshness_conditions_simple supp_prod)
      have fr_h: "\<exists>(a''::name). a''\<sharp>?h \<and> a''\<sharp>(?h a'')"
	using f c fin_r'' by (simp add: f3_freshness_conditions_simple supp_prod)
      have "\<exists>(d::name). d\<sharp>(?g,?h,t,a,c)" using fin_g fin_h
	by (rule_tac at_exists_fresh[OF at_name_inst], simp only: finite_Un supp_prod fs_name1, simp)
      then obtain d::"name" 
	where f1: "d\<sharp>?g" and f2: "d\<sharp>?h" and f3: "d\<sharp>t" and f4: "d\<noteq>a" and f5: "d\<noteq>c" 
	by (force simp add: fresh_prod fresh_atm)
      have g1: "[(a,d)]\<bullet>t = t" 
	by (rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst, OF i11, OF f3]) 
      from i6 have "(([(a,c)]@[(a,d)])\<bullet>t,r'') \<in> it f1 f2 f3" using g1 i10 by (simp only: pt_name2)
      hence "(t, \<lambda>pi2. r'' (pi2@(rev ([(a,c)]@[(a,d)])))) \<in> it f1 f2 f3"
	by (simp only: it_perm[OF f, OF c])
      hence g2: "(t, \<lambda>pi2. r'' (pi2@([(a,d)]@[(a,c)]))) \<in> it f1 f2 f3" by simp
      have "distinct [a,c,d]" using i9 f4 f5 by force
      hence g3: "(pi@[(c,d)]@[(a,d)]@[(a,c)]) \<triangleq> (pi@[(a,d)])"
	by (rule_tac at_prm_eq_append[OF at_name_inst], 
            force simp add: prm_eq_def at_calc[OF at_name_inst])
      have "fresh_fun ?g = ?g d" using fin_g fr_g f1
	by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
      also have "\<dots> = f3 d ((\<lambda>pi2. r'' (pi2@([(a,d)]@[(a,c)]))) (pi@[(c,d)]))" using ih g2 by simp 
      also have "\<dots> = f3 d (r'' (pi@[(c,d)]@[(a,d)]@[(a,c)]))" by simp
      also have "\<dots> = f3 d (r'' (pi@[(a,d)]))" using i6 g3 by (simp add: it_prm_eq)
      also have "\<dots> = fresh_fun ?h" using fin_h fr_h f2
	by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
      finally show "fresh_fun ?g = fresh_fun ?h" by simp
    qed
  qed
qed

lemma it_function:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  shows "\<exists>!r. (t,r) \<in> it f1 f2 f3"
proof (rule ex_ex1I)
  case goal1 show "\<exists>r. (t,r) \<in> it f1 f2 f3" by (rule it_total)
next
  case (goal2 r1 r2)
  have a1: "(t,r1) \<in> it f1 f2 f3" and a2: "(t,r2) \<in> it f1 f2 f3" by fact
  hence "\<forall>pi. r1 pi = r2 pi" using it_unique[OF f, OF c] by simp
  thus "r1=r2" by (simp add: expand_fun_eq) 
qed
  
lemma it_eqvt:
  fixes pi::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  and     a: "(t,r) \<in> it f1 f2 f3"
  shows "(pi\<bullet>t,pi\<bullet>r) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
using a proof(induct)
  case it1 show ?case by (perm_simp add: it.intros)
next
  case it2 thus ?case by (perm_simp add: it.intros)
next
  case (it3 c r t) (* lam case *)
  let ?g = "pi\<bullet>(\<lambda>pi'. fresh_fun (\<lambda>a'. f3 a' (r (pi'@[(c,a')]))))"
  and ?h = "\<lambda>pi'. fresh_fun (\<lambda>a'. (pi\<bullet>f3) a' ((pi\<bullet>r) (pi'@[((pi\<bullet>c),a')])))"
  have "(t,r) \<in> it f1 f2 f3" by fact
  hence fin_r: "finite ((supp r)::name set)" using f c by (auto intro: it_fin_supp)
  have ih: "(pi\<bullet>t,pi\<bullet>r) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)" by fact
  hence "(Lam [(pi\<bullet>c)].(pi\<bullet>t),?h) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)" by (simp add: it.intros)
  moreover 
  have "?g = ?h"
  proof -
    let ?g' = "\<lambda>pi a'. f3 a' (r (pi@[(c,a')]))"
    have fact1: "\<forall>pi. finite ((supp (?g' pi))::name set)" using fin_r f
      by (rule_tac allI, finite_guess add: perm_append supp_prod fs_name1)
    have fact2: "\<forall>pi. \<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" 
    proof 
      fix pi::"name prm"
      show "\<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" using f c fin_r
	by (simp add: f3_freshness_conditions_simple supp_prod)
    qed
    from fact1 fact2 show "?g = ?h" by (perm_simp add: fresh_fun_eqvt perm_append)
  qed
  ultimately show "(pi\<bullet>Lam [c].t,?g) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)" by simp
qed

lemma the1_equality': 
  assumes a: "\<exists>!r. P r"
  and     b: "P b" 
  and     c: "b y = a"
  shows "(THE r. P r) y = a"
apply(simp add: c[symmetric])
apply(rule fun_cong[OF the1_equality, OF a, OF b])
done

lemma itfun'_prm:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun' f1 f2 f3 (pi1\<bullet>t) pi2 = itfun' f1 f2 f3 t (pi2@pi1)"
apply(auto simp add: itfun_def itfun'_def)
apply(rule the1_equality'[OF it_function, OF f, OF c])
apply(rule it_perm_aux[OF f, OF c])
apply(rule theI'[OF it_function,OF f, OF c])
apply(simp)
done

lemma itfun'_eqvt:
  fixes pi1::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "pi1\<bullet>(itfun' f1 f2 f3 t pi2) = itfun' (pi1\<bullet>f1) (pi1\<bullet>f2) (pi1\<bullet>f3) (pi1\<bullet>t) (pi1\<bullet>pi2)"
proof -
  have f_pi: "finite ((supp (pi1\<bullet>f1,pi1\<bullet>f2,pi1\<bullet>f3))::name set)" using f
    (* FIXME: check why proof (finite_guess_debug add: perm_append fs_name1) does not work *)
    by (simp add: supp_prod pt_supp_finite_pi[OF pt_name_inst, OF at_name_inst])
  have fs_pi: "\<exists>(a::name). a\<sharp>(pi1\<bullet>f3) \<and> (\<forall>(y::'a::pt_name). a\<sharp>(pi1\<bullet>f3) a y)" 
  proof -
    from c obtain a where fs1: "a\<sharp>f3" and fs2: "(\<forall>(y::'a::pt_name). a\<sharp>f3 a y)" by force
    have "(pi1\<bullet>a)\<sharp>(pi1\<bullet>f3)" using fs1 by (simp add: fresh_eqvt)
    moreover
    have "\<forall>(y::'a::pt_name). (pi1\<bullet>a)\<sharp>((pi1\<bullet>f3) (pi1\<bullet>a) y)" 
    proof
      fix y::"'a::pt_name"
      from fs2 have "a\<sharp>f3 a ((rev pi1)\<bullet>y)" by simp
      then show "(pi1\<bullet>a)\<sharp>((pi1\<bullet>f3) (pi1\<bullet>a) y)"
	by (perm_simp add: pt_fresh_right[OF pt_name_inst, OF at_name_inst])
    qed
    ultimately show "\<exists>(a::name). a\<sharp>(pi1\<bullet>f3) \<and> (\<forall>(y::'a::pt_name). a\<sharp>(pi1\<bullet>f3) a y)" by blast
  qed
  show ?thesis
    apply(rule sym)
    apply(auto simp add: itfun_def itfun'_def)
    apply(rule the1_equality'[OF it_function, OF f_pi, OF fs_pi])
    apply(rule it_eqvt[OF f, OF c])
    apply(rule theI'[OF it_function,OF f, OF c])
    apply(rule sym)
    apply(rule pt_bij2[OF pt_name_inst, OF at_name_inst])
    apply(perm_simp)
    done
qed

lemma itfun_Var:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun f1 f2 f3 (Var c) = (f1 c)"
using f c by (auto intro!: the1_equality' it_function it.intros simp add: itfun_def itfun'_def)

lemma itfun_App:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun f1 f2 f3 (App t1 t2) = (f2 (itfun f1 f2 f3 t1) (itfun f1 f2 f3 t2))"
by (auto intro!: the1_equality' it_function[OF f, OF c] it.intros 
         intro: theI'[OF it_function, OF f, OF c] simp add: itfun_def itfun'_def)

lemma itfun_Lam_aux1:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun f1 f2 f3 (Lam [a].t) = fresh_fun (\<lambda>a'. f3 a' (itfun' f1 f2 f3 t ([]@[(a,a')])))"
by (auto intro!: the1_equality' it_function[OF f, OF c] it.intros 
         intro: theI'[OF it_function, OF f, OF c] simp add: itfun_def itfun'_def)

lemma itfun_Lam_aux2:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "b\<sharp>(a,t,f1,f2,f3)"
  shows "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = f3 b (itfun f1 f2 f3 ([(a,b)]\<bullet>t))"
proof -
  have eq1: "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = itfun f1 f2 f3 (Lam [a].t)"
  proof -
    have "Lam [b].([(b,a)]\<bullet>t) = Lam [a].t" using a
      by (simp add: lam.inject alpha fresh_prod fresh_atm)
    thus ?thesis by simp
  qed
  let ?g = "(\<lambda>a'. f3 a' (itfun' f1 f2 f3 t ([]@[(a,a')])))"
  have fin_g: "finite ((supp ?g)::name set)" 
    using f by (finite_guess add: itfun'_eqvt[OF f, OF c] supp_prod fs_name1)
  have fr_g: "\<exists>(a''::name). a''\<sharp>?g \<and> a''\<sharp>(?g a'')" using f c 
    by (rule_tac f3_freshness_conditions_simple, auto simp add: supp_prod, 
        finite_guess add: itfun'_eqvt[OF f, OF c] supp_prod fs_name1)
  have fresh_b: "b\<sharp>?g" 
  proof -
    have "finite ((supp (a,t,f1,f2,f3))::name set)" using f
      by (simp add: supp_prod fs_name1)
    moreover 
    have "((supp (a,t,f1,f2,f3))::name set) supports ?g"
      by (supports_simp add: itfun'_eqvt[OF f, OF c] perm_append)
    ultimately show ?thesis using a
      by (auto intro!: supports_fresh, simp add: fresh_def)
  qed
  have "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = itfun f1 f2 f3 (Lam [a].t)" by (simp add: eq1)
  also have "\<dots> = fresh_fun ?g" by (rule itfun_Lam_aux1[OF f, OF c])
  also have "\<dots> = ?g b" using fresh_b fin_g fr_g
    by (simp add: fresh_fun_app[OF pt_name_inst, OF at_name_inst])
  also have "\<dots> = f3 b (itfun f1 f2 f3 ([(a,b)]\<bullet>t))"
    by (simp add: itfun_def itfun'_prm[OF f, OF c]) 
  finally show "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = f3 b (itfun f1 f2 f3 ([(a,b)]\<bullet>t))" by simp 
qed

lemma itfun_Lam:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "b\<sharp>(f1,f2,f3)"
  shows "itfun f1 f2 f3 (Lam [b].t) = f3 b (itfun f1 f2 f3 t)"
proof -
  have "\<exists>(a::name). a\<sharp>(b,t)"
    by (rule at_exists_fresh[OF at_name_inst], simp add: supp_prod fs_name1)
  then obtain a::"name" where a1: "a\<sharp>b" and a2: "a\<sharp>t" by (force simp add: fresh_prod)
  have fresh_b: "b\<sharp>(a,[(b,a)]\<bullet>t,f1,f2,f3)" using a a1 a2
    by (simp add: fresh_prod fresh_atm fresh_left calc_atm)
  have "itfun f1 f2 f3 (Lam [b].t) = itfun f1 f2 f3 (Lam [b].(([(b,a)])\<bullet>([(b,a)]\<bullet>t)))" by (perm_simp)
  also have "\<dots> = f3 b (itfun f1 f2 f3 (([(a,b)])\<bullet>([(b,a)]\<bullet>t)))" using fresh_b
    by (rule itfun_Lam_aux2[OF f, OF c])
  also have "\<dots> = f3 b (itfun f1 f2 f3 t)" by (simp add: pt_swap_bij'[OF pt_name_inst, OF at_name_inst])
  finally show ?thesis by simp
qed

end
