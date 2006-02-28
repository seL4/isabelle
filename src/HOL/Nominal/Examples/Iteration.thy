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
  --"two facts used by fresh_fun_equiv"
  have fact1: "\<forall>pi. finite ((supp (?g' pi))::name set)" using f ih
    by (rule_tac allI, finite_guess add: perm_append supp_prod fs_name1)
  have fact2: "\<forall>pi. \<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" 
  proof 
    fix pi::"name prm"
    show "\<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" using f c ih
      by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
  qed
  show ?case using fact1 fact2 ih f
    by (finite_guess add: fresh_fun_equiv[OF pt_name_inst, OF at_name_inst] 
                          perm_append supp_prod fs_name1)
qed 

lemma it_trans: 
  shows "\<lbrakk>(t,r)\<in>rec f1 f2 f3; r=r'\<rbrakk> \<Longrightarrow> (t,r')\<in>rec f1 f2 f3" by simp

lemma it_perm:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(t,y) \<in> it f1 f2 f3"
  shows "(pi1\<bullet>t, \<lambda>pi2. y (pi2@pi1)) \<in> it f1 f2 f3"
using a
proof (induct)
  case (it1 c)
  show ?case by (auto simp add: pt2[OF pt_name_inst], rule it.intros)
next
  case (it2 t1 t2 r1 r2)
  thus ?case by (auto intro: it.intros) 
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

lemma it_perm_rev:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "(pi\<bullet>t,y) \<in> it f1 f2 f3"
  shows "(t, \<lambda>pi2. y (pi2@(rev pi))) \<in> it f1 f2 f3"
proof - 
  from a have "((rev pi)\<bullet>(pi\<bullet>t),\<lambda>pi2. y (pi2@(rev pi))) \<in> it f1 f2 f3"
    by (rule it_perm[OF f, OF c])
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
  case (it1 c)
  thus ?case by (cases, simp_all add: lam.inject)
next
  case (it2 r1 r2 t1 t2)
  with prems(9) show ?case 
    by (cases, simp_all (no_asm_use) add: lam.inject, force)
next
  case (it3 c r t r')
  have "(t,r) \<in> it f1 f2 f3" by fact
  hence fin_r: "finite ((supp r)::name set)" using f c by (auto intro: it_fin_supp)
  have ih: "\<And>r' pi. (t,r') \<in> it f1 f2 f3 \<Longrightarrow> r pi = r' pi" by fact
  have "(Lam [c].t, r') \<in> it f1 f2 f3" by fact
  then show "fresh_fun (\<lambda>a'. f3 a' (r (pi@[(c,a')]))) = r' pi"
  proof (cases, simp_all add: lam.inject, auto)
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
	using f c fin_r by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
      have fr_h: "\<exists>(a''::name). a''\<sharp>?h \<and> a''\<sharp>(?h a'')"
	using f c fin_r'' by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
      have "\<exists>(d::name). d\<sharp>(?g,?h,t,a,c)" using fin_g fin_h
	by (rule_tac at_exists_fresh[OF at_name_inst], simp only: finite_Un supp_prod fs_name1, simp)
      then obtain d::"name" 
	where f1: "d\<sharp>?g" and f2: "d\<sharp>?h" and f3: "d\<sharp>t" and f4: "d\<noteq>a" and f5: "d\<noteq>c" 
	by (force simp add: fresh_prod at_fresh[OF at_name_inst] at_fresh[OF at_name_inst])
      have g1: "[(a,d)]\<bullet>t = t" 
	by (rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst, OF i11, OF f3]) 
      from i6 have "(([(a,c)]@[(a,d)])\<bullet>t,r'') \<in> it f1 f2 f3" using g1 i10 by (simp only: pt_name2)
      hence "(t, \<lambda>pi2. r'' (pi2@(rev ([(a,c)]@[(a,d)])))) \<in> it f1 f2 f3"
	by (simp only: it_perm_rev[OF f, OF c])
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
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>!y. (t,y) \<in> it f1 f2 f3"
proof (rule ex_ex1I)
  case goal1
  show ?case by (rule it_total)
next
  case (goal2 y1 y2)
  have a1: "(t,y1) \<in> it f1 f2 f3" and a2: "(t,y2) \<in> it f1 f2 f3" by fact
  hence "\<forall>pi. y1 pi = y2 pi" using it_unique[OF f, OF c] by force
  thus ?case by (simp add: expand_fun_eq) 
qed
  
lemma it_eqvt:
  fixes pi::"name prm"
  assumes a: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  and     b: "(t,r) \<in> it f1 f2 f3"
  shows "(pi\<bullet>t,pi\<bullet>r) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
using b
proof(induct)
  case it1 show ?case by (perm_simp add: it.intros)
next
  case it2 thus ?case by (perm_simp add: it.intros)
next
  case (it3 c r t) (* lam case *)
  let ?g = "pi\<bullet>(\<lambda>pi'. fresh_fun (\<lambda>a'. f3 a' (r (pi'@[(c,a')]))))"
  and ?h = "\<lambda>pi'. fresh_fun (\<lambda>a'. (pi\<bullet>f3) a' ((pi\<bullet>r) (pi'@[((pi\<bullet>c),a')])))"
  have "(t,r) \<in> it f1 f2 f3" by fact
  hence fin_r: "finite ((supp r)::name set)" using a c by (auto intro: it_fin_supp)
  have ih: "(pi\<bullet>t,pi\<bullet>r) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)" by fact
  hence "(Lam [(pi\<bullet>c)].(pi\<bullet>t),?h) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)" by (simp add: it.intros)
  moreover 
  have "?g = ?h"
  proof -
    let ?g' = "\<lambda>pi a'. f3 a' (r (pi@[(c,a')]))"
    have fact1: "\<forall>pi. finite ((supp (?g' pi))::name set)" using fin_r a
      by (rule_tac allI, finite_guess add: perm_append supp_prod fs_name1)
    have fact2: "\<forall>pi. \<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" 
    proof 
      fix pi::"name prm"
      show "\<exists>(a''::name). a''\<sharp>(?g' pi) \<and> a''\<sharp>((?g' pi) a'')" using a c fin_r
	by (rule_tac f3_freshness_conditions_simple, simp_all add: supp_prod)
    qed
    show ?thesis using fact1 fact2
      by (perm_simp add: fresh_fun_equiv[OF pt_name_inst, OF at_name_inst] perm_append)
  qed
  ultimately show "(pi\<bullet>Lam [c].t,?g) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)" by simp
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

lemma itfun'_equiv:
  fixes pi::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "pi\<bullet>(itfun' f1 f2 f3 t) = itfun' (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3) (pi\<bullet>t)"
using f
apply(auto simp add: itfun'_def)
apply(subgoal_tac "\<exists>y. (t,y) \<in> it f1 f2 f3")(*A*)
apply(auto)
apply(rule sym)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule it_function[OF f, OF c])
apply(rule the1_equality)
apply(rule it_function)
apply(simp add: supp_prod)
apply(simp add: pt_supp_finite_pi[OF pt_name_inst, OF at_name_inst])
apply(subgoal_tac "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)")
apply(auto)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(auto)
apply(simp add: fresh_eqvt)
apply(drule_tac x="(rev pi)\<bullet>x" in spec)
apply(subgoal_tac "(pi\<bullet>f3) (pi\<bullet>a) x  = pi\<bullet>(f3 a ((rev pi)\<bullet>x))")
apply(simp add: fresh_eqvt)
apply(subgoal_tac "pi\<bullet>(f3 a ((rev pi)\<bullet>x)) = (pi\<bullet>f3) (pi\<bullet>a) (pi\<bullet>((rev pi)\<bullet>x))")
apply(simp)
apply(perm_simp)
apply(perm_simp)
apply(rule c)
apply(rule it_eqvt)
apply(rule f, rule c, assumption)
(*A*)
apply(rule it_total)
done

lemma itfun'_equiv_aux:
  fixes pi::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "pi\<bullet>(itfun' f1 f2 f3 t pi') = itfun' (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3) (pi\<bullet>t) (pi\<bullet>pi')" (is "?LHS=?RHS")
proof -
  have "?LHS = (pi\<bullet>itfun' f1 f2 f3 t) (pi\<bullet>pi')" by (simp add: perm_app)
  also have "\<dots> = ?RHS" by (simp add: itfun'_equiv[OF f, OF c])
  finally show "?LHS = ?RHS" by simp
qed

lemma itfun'_finite_supp:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "finite ((supp (itfun' f1 f2 f3 t))::name set)"
  using f by (finite_guess add: itfun'_equiv[OF f, OF c] supp_prod fs_name1)

lemma itfun'_prm:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun' f1 f2 f3 (pi1\<bullet>t) pi2 = itfun' f1 f2 f3 t (pi2@pi1)"
apply(auto simp add: itfun'_def)
apply(subgoal_tac "\<exists>y. (t,y) \<in> it f1 f2 f3")(*A*)
apply(auto)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule it_function[OF f, OF c])
apply(rule_tac a="\<lambda>pi2. y (pi2@pi1)" in theI2')
apply(rule it_perm)
apply(rule f, rule c)
apply(assumption)
apply(rule it_function[OF f, OF c])
apply(simp)
(*A*)
apply(rule it_total)
done

lemma itfun_Var:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun f1 f2 f3 (Var c) = (f1 c)"
apply(auto simp add: itfun_def itfun'_def)
apply(subgoal_tac "(THE y. (Var c, y) \<in> it f1 f2 f3) = (\<lambda>(pi::name prm). f1 (pi\<bullet>c))")(*A*)
apply(simp)
apply(rule the1_equality)
apply(rule it_function[OF f, OF c])
apply(rule it.intros)
done

lemma itfun_App:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun f1 f2 f3 (App t1 t2) = (f2 (itfun f1 f2 f3 t1) (itfun f1 f2 f3 t2))"
apply(auto simp add: itfun_def itfun'_def)
apply(subgoal_tac "(THE y. (App t1 t2, y) \<in> it f1 f2 f3) = 
      (\<lambda>(pi::name prm). f2 ((itfun' f1 f2 f3 t1) pi) ((itfun' f1 f2 f3 t2) pi))")(*A*)
apply(simp add: itfun'_def)
apply(rule the1_equality)
apply(rule it_function[OF f, OF c])
apply(rule it.intros)
apply(subgoal_tac "\<exists>y. (t1,y) \<in> it f1 f2 f3")(*A*)
apply(erule exE, simp add: itfun'_def)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule it_function[OF f, OF c])
apply(assumption)
(*A*)
apply(rule it_total)
apply(subgoal_tac "\<exists>y. (t2,y) \<in> it f1 f2 f3")(*B*)
apply(auto simp add: itfun'_def)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule it_function[OF f, OF c])
apply(assumption)
(*B*)
apply(rule it_total)
done 

lemma itfun_Lam_aux1:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "itfun f1 f2 f3 (Lam [a].t) = fresh_fun (\<lambda>a'. f3 a' (itfun' f1 f2 f3 t ([]@[(a,a')])))"
apply(simp add: itfun_def itfun'_def)
apply(subgoal_tac "(THE y. (Lam [a].t, y) \<in> it f1 f2 f3) = 
        (\<lambda>(pi::name prm). fresh_fun(\<lambda>a'. f3 a' ((itfun' f1 f2 f3 t) (pi@[(a,a')]))))")(*A*)
apply(simp add: itfun'_def[symmetric])
apply(rule the1_equality)
apply(rule it_function[OF f, OF c])
apply(rule it.intros)
apply(subgoal_tac "\<exists>y. (t,y) \<in> it f1 f2 f3")(*B*)
apply(erule exE, simp add: itfun'_def)
apply(rule_tac a="y" in theI2')
apply(assumption)
apply(rule it_function[OF f, OF c])
apply(assumption)
(*B*)
apply(rule it_total)
done

lemma itfun_Lam_aux2:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     a: "b\<sharp>(a,t,f1,f2,f3)"
  shows "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = f3 b (itfun f1 f2 f3 ([(a,b)]\<bullet>t))"
proof -
  from f have f': "finite ((supp f3)::name set)" by (simp add: supp_prod)
  have eq1: "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = itfun f1 f2 f3 (Lam [a].t)"
  proof -
    have "Lam [b].([(b,a)]\<bullet>t) = Lam [a].t" using a
      by (simp add: lam.inject alpha fresh_prod fresh_atm)
    thus ?thesis by simp
  qed
  let ?g = "(\<lambda>a'. f3 a' (itfun' f1 f2 f3 t ([]@[(a,a')])))"
  (* FIXME: cleanup*)
  have a0: "((supp (f1,f3,f2,t,a))::name set) supports ?g"
    by (supports_simp add: itfun'_equiv_aux[OF f, OF c] perm_append)
  have a1: "finite ((supp (f1,f3,f2,t,a))::name set)" using f
    by (simp add: supp_prod fs_name1)
  have a2: "finite ((supp ?g)::name set)"
    using f by (finite_guess add: itfun'_equiv_aux[OF f, OF c] supp_prod fs_name1)
  have c0: "finite ((supp (itfun' f1 f2 f3 t))::name set)"
    by (rule itfun'_finite_supp[OF f, OF c])
  have c1: "\<exists>(a''::name). a''\<sharp>?g \<and> a''\<sharp>(?g a'')"
    by (rule f3_freshness_conditions_simple[OF f', OF c0, OF c])
  have c2: "b\<sharp>?g"
  proof -
    have fs_g: "finite ((supp (f1,f2,f3,t))::name set)" using f
      by (simp add: supp_prod fs_name1)
    have "((supp (f1,f2,f3,t))::name set) supports (itfun' f1 f2 f3 t)"
      by (supports_simp add: itfun'_equiv[OF f, OF c])
    hence c3: "b\<sharp>(itfun' f1 f2 f3 t)" using fs_g 
    proof(rule supports_fresh, simp add: fresh_def[symmetric])
      show "b\<sharp>(f1,f2,f3,t)" using a by (simp add: fresh_prod)
    qed
    show ?thesis using a
      by (rule_tac supports_fresh[OF a0, OF a1], simp add: fresh_def[symmetric], simp add: fresh_prod)
  qed
  (* main proof *)
  have "itfun f1 f2 f3 (Lam [b].([(b,a)]\<bullet>t)) = itfun f1 f2 f3 (Lam [a].t)" by (simp add: eq1)
  also have "\<dots> = fresh_fun ?g" by (rule itfun_Lam_aux1[OF f, OF c])
  also have "\<dots> = ?g b" using c2
    by (rule fresh_fun_app[OF pt_name_inst, OF at_name_inst, OF a2, OF c1])
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
  have "itfun f1 f2 f3 (Lam [b].t) = itfun f1 f2 f3 (Lam [b].(([(b,a)])\<bullet>([(b,a)]\<bullet>t)))"
    by (simp add: pt_swap_bij[OF pt_name_inst, OF at_name_inst])
  also have "\<dots> = f3 b (itfun f1 f2 f3 (([(a,b)])\<bullet>([(b,a)]\<bullet>t)))" 
  proof(rule itfun_Lam_aux2[OF f, OF c])
    have "b\<sharp>([(b,a)]\<bullet>t)" using a1 a2
      by (simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst] at_calc[OF at_name_inst] 
        at_fresh[OF at_name_inst])
    thus "b\<sharp>(a,[(b,a)]\<bullet>t,f1,f2,f3)" using a a1 by (force simp add: fresh_prod at_fresh[OF at_name_inst])
  qed
  also have "\<dots> = f3 b (itfun f1 f2 f3 t)" by (simp add: pt_swap_bij'[OF pt_name_inst, OF at_name_inst])
  finally show ?thesis .
qed
  
constdefs 
  depth_Var :: "name \<Rightarrow> nat"
  "depth_Var \<equiv> \<lambda>(a::name). 1"
  
  depth_App :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  "depth_App \<equiv> \<lambda>n1 n2. (max n1 n2)+1"

  depth_Lam :: "name \<Rightarrow> nat \<Rightarrow> nat"
  "depth_Lam \<equiv> \<lambda>(a::name) n. n+1"

  depth_lam :: "lam \<Rightarrow> nat"
  "depth_lam \<equiv> itfun depth_Var depth_App depth_Lam"

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
apply(simp add: fresh_def)
apply(force simp add: supp_depth_Lam)
apply(unfold fresh_def)
apply(simp add: supp_def)
apply(simp add: perm_nat_def)
done

lemma depth_Var:
  shows "depth_lam (Var c) = 1"
apply(simp add: depth_lam_def)
apply(simp add: itfun_Var[OF fin_supp_depth, OF fresh_depth_Lam])
apply(simp add: depth_Var_def)
done

lemma depth_App:
  shows "depth_lam (App t1 t2) = (max (depth_lam t1) (depth_lam t2))+1"
apply(simp add: depth_lam_def)
apply(simp add: itfun_App[OF fin_supp_depth, OF fresh_depth_Lam])
apply(simp add: depth_App_def)
done

lemma depth_Lam:
  shows "depth_lam (Lam [a].t) = (depth_lam t)+1"
apply(simp add: depth_lam_def)
apply(rule trans)
apply(rule itfun_Lam[OF fin_supp_depth, OF fresh_depth_Lam])
apply(simp add: fresh_def supp_prod supp_depth_Var supp_depth_App supp_depth_Lam)
apply(simp add: depth_Lam_def)
done

text {* substitution *}
constdefs 
  subst_Var :: "name \<Rightarrow>lam \<Rightarrow> name \<Rightarrow> lam"
  "subst_Var b t \<equiv> \<lambda>a. (if a=b then t else (Var a))"
  
  subst_App :: "name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_App b t \<equiv> \<lambda>r1 r2. App r1 r2"

  subst_Lam :: "name \<Rightarrow> lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"
  "subst_Lam b t \<equiv> \<lambda>a r. Lam [a].r"

  subst_lam :: "name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_lam b t \<equiv> itfun (subst_Var b t) (subst_App b t) (subst_Lam b t)"

lemma supports_subst_Var:
  shows "((supp (b,t))::name set) supports (subst_Var b t)"
apply(supports_simp add: subst_Var_def)
apply(rule impI)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
done

lemma supports_subst_App:
  shows "((supp (b,t))::name set) supports subst_App b t"
by  (supports_simp add: subst_App_def)

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
apply(auto simp add: itfun_Var[OF fin_supp_subst, OF fresh_subst_Lam])
apply(auto simp add: subst_Var_def)
done

lemma subst_App:
  shows "subst_lam b t (App t1 t2) = App (subst_lam b t t1) (subst_lam b t t2)"
apply(simp add: subst_lam_def)
apply(auto simp add: itfun_App[OF fin_supp_subst, OF fresh_subst_Lam])
apply(auto simp add: subst_App_def)
done

lemma subst_Lam:
  assumes a: "a\<sharp>(b,t)"
  shows "subst_lam b t (Lam [a].t1) = Lam [a].(subst_lam b t t1)"
using a
apply(simp add: subst_lam_def)
apply(subgoal_tac "a\<sharp>(subst_Var b t,subst_App b t,subst_Lam b t)")
apply(auto simp add: itfun_Lam[OF fin_supp_subst, OF fresh_subst_Lam])
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

lemma subst_Lam'':
  assumes a: "a\<sharp>b"
  and     b: "a\<sharp>t"
  shows "subst_lam b t (Lam [a].t1) = Lam [a].(subst_lam b t t1)"
apply(rule subst_Lam)
apply(simp add: fresh_prod a b)
done

consts
  subst_syn  :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [100,100,100] 900)
translations 
  "t1[a::=t2]" \<rightleftharpoons> "subst_lam a t2 t1"

declare subst_Var[simp]
declare subst_App[simp]
declare subst_Lam[simp]
declare subst_Lam'[simp]
declare subst_Lam''[simp]

lemma subst_eqvt[simp]:
  fixes pi:: "name prm"
  and   t1:: "lam"
  and   t2:: "lam"
  and   a :: "name"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
apply(nominal_induct t1 avoiding: b t2 rule: lam.induct)
apply(auto simp add: perm_bij fresh_prod fresh_atm)
apply(subgoal_tac "(pi\<bullet>name)\<sharp>(pi\<bullet>b,pi\<bullet>t2)")(*A*)
apply(simp)
(*A*) 
apply(simp add: perm_bij fresh_prod fresh_atm pt_fresh_bij[OF pt_name_inst, OF at_name_inst]) 
done

lemma subst_supp: "supp(t1[a::=t2])\<subseteq>(((supp(t1)-{a})\<union>supp(t2))::name set)"
apply(nominal_induct t1 avoiding: a t2 rule: lam.induct)
apply(auto simp add: lam.supp supp_atm fresh_prod abs_supp)
apply(blast)
apply(blast)
done

end
