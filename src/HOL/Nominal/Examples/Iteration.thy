(* $Id$ *)

theory Iteration
imports "../Nominal"
begin

atom_decl name

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

types 'a f1_ty  = "name\<Rightarrow>('a::pt_name)"
      'a f2_ty  = "'a\<Rightarrow>'a\<Rightarrow>('a::pt_name)"
      'a f3_ty  = "name\<Rightarrow>'a\<Rightarrow>('a::pt_name)"

consts
  it :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> (lam \<times> 'a::pt_name) set"

inductive "it f1 f2 f3"
intros
it1: "(Var a, f1 a) \<in> it f1 f2 f3"
it2: "\<lbrakk>(t1,r1) \<in> it f1 f2 f3; (t2,r2) \<in> it f1 f2 f3\<rbrakk> \<Longrightarrow> (App t1 t2, f2 r1 r2) \<in> it f1 f2 f3"
it3: "\<lbrakk>a\<sharp>(f1,f2,f3); (t,r) \<in> it f1 f2 f3\<rbrakk> \<Longrightarrow> (Lam [a].t,f3 a r) \<in> it f1 f2 f3"

lemma it_equiv:
  fixes pi::"name prm"
  assumes a: "(t,r) \<in> it f1 f2 f3"
  shows "(pi\<bullet>t,pi\<bullet>r) \<in> it (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3)"
  using a
  apply(induct)
  apply(perm_simp | auto intro!: it.intros simp add: fresh_right)+
  done

lemma it_fin_supp:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     a: "(t,r) \<in> it f1 f2 f3"
  shows "finite ((supp r)::name set)" 
  using a f
  apply(induct)
  apply(finite_guess, simp add: supp_prod fs_name1)+
  done

lemma it_total:
  assumes a: "finite ((supp (f1,f2,f3))::name set)"
  and     b: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  shows "\<exists>r. (t,r)\<in>it f1 f2 f3"
apply(rule_tac lam.induct'[of "\<lambda>_. (supp (f1,f2,f3))" "\<lambda>z. \<lambda>t. \<exists>r. (t,r)\<in>it f1 f2 f3", simplified])
apply(fold fresh_def)
apply(auto intro: it.intros a)
done

lemma it_unique: 
  assumes a: "finite ((supp (f1,f2,f3))::name set)"
  and     b: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(y::'a::pt_name). a\<sharp>f3 a y)"
  and     c1: "(t,r)\<in>it f1 f2 f3"
  and     c2: "(t,r')\<in>it f1 f2 f3"
  shows   "r=r'"
using c1 c2
proof (induct fixing: r')
  case it1
  then show ?case by cases (simp_all add: lam.inject)
next
  case (it2 r1 r2 t1 t2)
  have ih1: "\<And>r'. (t1,r') \<in> it f1 f2 f3 \<Longrightarrow> r1 = r'" by fact
  have ih2: "\<And>r'. (t2,r') \<in> it f1 f2 f3 \<Longrightarrow> r2 = r'" by fact
  have "(App t1 t2, r') \<in>it f1 f2 f3" by fact
  then show ?case
  proof cases
    case it2
    then show ?thesis using ih1 ih2 by (simp add: lam.inject) 
  qed (simp_all (no_asm_use))
next
  case (it3 a1 r1 t1)
  have f1: "a1\<sharp>(f1,f2,f3)" by fact
  have ih: "\<And>r'. (t1,r') \<in> it f1 f2 f3 \<Longrightarrow> r1 = r'" by fact
  have it1: "(t1,r1) \<in> it f1 f2 f3" by fact
  have "(Lam [a1].t1, r') \<in> it f1 f2 f3" by fact
  then show ?case
  proof cases
    case (it3 a2 r2 t2)
    then have f2: "a2\<sharp>(f1,f2,f3)" 
         and  it2: "(t2,r2) \<in> it f1 f2 f3"
         and  eq1: "[a1].t1 = [a2].t2" and eq2: "r' = f3 a2 r2" by (simp_all add: lam.inject) 
    have "\<exists>(c::name). c\<sharp>(f1,f2,f3,a1,a2,t1,t2,r1,r2)" using a it1 it2
      by (auto intro!: at_exists_fresh[OF at_name_inst] simp add: supp_prod fs_name1 it_fin_supp[OF a])
    then obtain c where fresh: "c\<sharp>f1" "c\<sharp>f2" "c\<sharp>f3" "c\<noteq>a1" "c\<noteq>a2" "c\<sharp>t1" "c\<sharp>t2" "c\<sharp>r1" "c\<sharp>r2"
      by (force simp add: fresh_prod fresh_atm)
    have eq3: "[(a1,c)]\<bullet>t1 = [(a2,c)]\<bullet>t2" using eq1 fresh
      apply(auto simp add: alpha)
      apply(rule trans)
      apply(rule perm_compose)
      apply(simp add: calc_atm perm_fresh_fresh)
      apply(rule pt_name3, rule at_ds5[OF at_name_inst])
      done
    have eq4: "[(a1,c)]\<bullet>r1 = [(a2,c)]\<bullet>r2" using eq3 it2 f1 f2 fresh
      apply(drule_tac sym)
      apply(rule_tac pt_bij2[OF pt_name_inst, OF at_name_inst])
      apply(rule ih)
      apply(drule_tac pi="[(a2,c)]" in it_equiv)
      apply(perm_simp only: fresh_prod)
      apply(drule_tac pi="[(a1,c)]" in it_equiv)
      apply(perm_simp)
      done
    have fs1: "a1\<sharp>f3 a1 r1" using b f1
      apply(auto)
      apply(case_tac "a=a1")
      apply(simp)
      apply(rule_tac pi="[(a1,a)]" in pt_fresh_bij2[OF pt_name_inst, OF at_name_inst])
      apply(perm_simp add: calc_atm fresh_prod)
      done      
    have fs2: "a2\<sharp>f3 a2 r2" using b f2
      apply(auto)
      apply(case_tac "a=a2")
      apply(simp)
      apply(rule_tac pi="[(a2,a)]" in pt_fresh_bij2[OF pt_name_inst, OF at_name_inst])
      apply(perm_simp add: calc_atm fresh_prod)
      done      
    have fs3: "c\<sharp>f3 a1 r1" using fresh it1 a
      by (fresh_guess add: supp_prod fs_name1 it_fin_supp[OF a] fresh_atm)
    have fs4: "c\<sharp>f3 a2 r2" using fresh it2 a
      by (fresh_guess add: supp_prod fs_name1 it_fin_supp[OF a] fresh_atm)
    have "f3 a1 r1 = [(a1,c)]\<bullet>(f3 a1 r1)" using fs1 fs3 by perm_simp
    also have "\<dots> = f3 c ([(a1,c)]\<bullet>r1)" using f1 fresh by (perm_simp add: calc_atm fresh_prod)
    also have "\<dots> = f3 c ([(a2,c)]\<bullet>r2)" using eq4 by simp
    also have "\<dots> = [(a2,c)]\<bullet>(f3 a2 r2)" using f2 fresh by (perm_simp add: calc_atm fresh_prod)
    also have "\<dots> = f3 a2 r2" using fs2 fs4 by perm_simp
    finally have eq4: "f3 a1 r1 = f3 a2 r2" by simp
    then show ?thesis using eq2 by simp
  qed (simp_all (no_asm_use))
qed

lemma it_function:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  shows "\<exists>!r. (t,r) \<in> it f1 f2 f3"
proof (rule ex_ex1I, rule it_total[OF f, OF c])
  case (goal1 r1 r2)
  have a1: "(t,r1) \<in> it f1 f2 f3" and a2: "(t,r2) \<in> it f1 f2 f3" by fact
  thus "r1 = r2" using it_unique[OF f, OF c] by simp
qed

constdefs
  itfun :: "'a f1_ty \<Rightarrow> 'a f2_ty \<Rightarrow> 'a f3_ty \<Rightarrow> lam \<Rightarrow> ('a::pt_name)" 
  "itfun f1 f2 f3 t \<equiv> (THE r. (t,r) \<in> it f1 f2 f3)"

lemma itfun_eqvt:
  fixes pi::"name prm"
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  shows "pi\<bullet>(itfun f1 f2 f3 t) = itfun (pi\<bullet>f1) (pi\<bullet>f2) (pi\<bullet>f3) (pi\<bullet>t)"
proof -
  have f_pi: "finite ((supp (pi\<bullet>f1,pi\<bullet>f2,pi\<bullet>f3))::name set)" using f
    by (simp add: supp_prod pt_supp_finite_pi[OF pt_name_inst, OF at_name_inst])
  have fs_pi: "\<exists>(a::name). a\<sharp>(pi\<bullet>f3) \<and> (\<forall>(r::'a::pt_name). a\<sharp>(pi\<bullet>f3) a r)" 
  proof -
    from c obtain a where fs1: "a\<sharp>f3" and fs2: "\<forall>(r::'a::pt_name). a\<sharp>f3 a r" by force
    have "(pi\<bullet>a)\<sharp>(pi\<bullet>f3)" using fs1 by (simp add: fresh_eqvt)
    moreover
    have "\<forall>(r::'a::pt_name). (pi\<bullet>a)\<sharp>((pi\<bullet>f3) (pi\<bullet>a) r)" using fs2 by (perm_simp add: fresh_right)
    ultimately show "\<exists>(a::name). a\<sharp>(pi\<bullet>f3) \<and> (\<forall>(r::'a::pt_name). a\<sharp>(pi\<bullet>f3) a r)" by blast
  qed
  show ?thesis
    apply(rule sym)
    apply(auto simp add: itfun_def)
    apply(rule the1_equality[OF it_function, OF f_pi, OF fs_pi])
    apply(rule it_equiv)
    apply(rule theI'[OF it_function,OF f, OF c])
    done
qed

lemma itfun_Var:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  shows "itfun f1 f2 f3 (Var c) = (f1 c)"
using f c by (auto intro!: the1_equality it_function it.intros simp add: itfun_def)

lemma itfun_App:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  shows "itfun f1 f2 f3 (App t1 t2) = (f2 (itfun f1 f2 f3 t1) (itfun f1 f2 f3 t2))"
by (auto intro!: the1_equality it_function[OF f, OF c] it.intros 
         intro: theI'[OF it_function, OF f, OF c] simp add: itfun_def)

lemma itfun_Lam:
  assumes f: "finite ((supp (f1,f2,f3))::name set)"
  and     c: "\<exists>(a::name). a\<sharp>f3 \<and> (\<forall>(r::'a::pt_name). a\<sharp>f3 a r)"
  and     a: "a\<sharp>(f1,f2,f3)"
  shows "itfun f1 f2 f3 (Lam [a].t) = f3 a (itfun f1 f2 f3 t)"
using a
by (auto intro!: the1_equality it_function[OF f, OF c] it.intros 
         intro: theI'[OF it_function, OF f, OF c] simp add: itfun_def)

end
