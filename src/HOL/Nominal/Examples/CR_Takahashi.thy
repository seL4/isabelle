(* $Id$ *)

theory CR_Takahashi
imports Lam_Funs
begin

text {* The Church-Rosser proof from a paper by Masako Takahashi;
        our formalisation follows with some slight exceptions the one 
        done by Randy Pollack and James McKinna from their 1993 
        TLCA-paper; the proof is simpler by using an auxiliary
        reduction relation called complete development reduction.
      
        Authors: Mathilde Arnaud and Christian Urban
     *}

lemma forget:
  assumes asm: "x\<sharp>L"
  shows "L[x::=P] = L"
  using asm 
by (nominal_induct L avoiding: x P rule: lam.induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact:
  fixes z::"name"
  assumes asms: "z\<sharp>N" "z\<sharp>L"
  shows "z\<sharp>(N[y::=L])"
  using asms 
by (nominal_induct N avoiding: z y L rule: lam.induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact': 
  fixes a::"name"
  assumes a: "a\<sharp>t2"
  shows "a\<sharp>t1[a::=t2]"
using a 
by (nominal_induct t1 avoiding: a t2 rule: lam.induct)
   (auto simp add: abs_fresh fresh_atm)

lemma substitution_lemma:  
  assumes asm: "x\<noteq>y" "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
  using asm 
by (nominal_induct M avoiding: x y N L rule: lam.induct)
   (auto simp add: fresh_fact forget)

section {* Beta Reduction *}

inductive2
  "Beta" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
where
    b1[intro]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (App s1 t)\<longrightarrow>\<^isub>\<beta>(App s2 t)"
  | b2[intro]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (App t s1)\<longrightarrow>\<^isub>\<beta>(App t s2)"
  | b3[intro]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (Lam [a].s1)\<longrightarrow>\<^isub>\<beta> (Lam [a].s2)"
  | b4[intro]: "a\<sharp>s2 \<Longrightarrow> (App (Lam [a].s1) s2)\<longrightarrow>\<^isub>\<beta>(s1[a::=s2])"

equivariance Beta

nominal_inductive Beta
  by (simp_all add: abs_fresh fresh_fact')

inductive2
  "Beta_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta>\<^sup>* _" [80,80] 80)
where
    bs1[intro, simp]: "M \<longrightarrow>\<^isub>\<beta>\<^sup>* M"
  | bs2[intro]: "\<lbrakk>M1\<longrightarrow>\<^isub>\<beta>\<^sup>* M2; M2 \<longrightarrow>\<^isub>\<beta> M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>\<^isub>\<beta>\<^sup>* M3"

equivariance Beta_star

lemma beta_star_trans:
  assumes a1: "M1\<longrightarrow>\<^isub>\<beta>\<^sup>* M2"
  and     a2: "M2\<longrightarrow>\<^isub>\<beta>\<^sup>* M3"
  shows "M1 \<longrightarrow>\<^isub>\<beta>\<^sup>* M3"
using a2 a1
by (induct) (auto)

section {* One-Reduction *}

inductive2
  One :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1 _" [80,80] 80)
where
    o1[intro!]:      "M\<longrightarrow>\<^isub>1M"
  | o2[simp,intro!]: "\<lbrakk>t1\<longrightarrow>\<^isub>1t2;s1\<longrightarrow>\<^isub>1s2\<rbrakk> \<Longrightarrow> (App t1 s1)\<longrightarrow>\<^isub>1(App t2 s2)"
  | o3[simp,intro!]: "s1\<longrightarrow>\<^isub>1s2 \<Longrightarrow> (Lam [a].s1)\<longrightarrow>\<^isub>1(Lam [a].s2)"
  | o4[simp,intro!]: "\<lbrakk>a\<sharp>(s1,s2); s1\<longrightarrow>\<^isub>1s2;t1\<longrightarrow>\<^isub>1t2\<rbrakk> \<Longrightarrow> (App (Lam [a].t1) s1)\<longrightarrow>\<^isub>1(t2[a::=s2])"

equivariance One

nominal_inductive One
  by (simp_all add: abs_fresh fresh_fact')

lemma one_subst_aux:
  assumes a: "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N] \<longrightarrow>\<^isub>1 M[x::=N']"
using a
by (nominal_induct M avoiding: x N N' rule: lam.induct)
   (auto simp add: fresh_prod fresh_atm)

lemma one_subst: 
  assumes a: "M\<longrightarrow>\<^isub>1M'" 
  and     b: "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N]\<longrightarrow>\<^isub>1M'[x::=N']" 
using a b
by (nominal_induct M M' avoiding: N N' x rule: One.strong_induct)
   (auto simp add: one_subst_aux substitution_lemma fresh_atm fresh_fact)

inductive2
  "One_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1\<^sup>* _" [80,80] 80)
where
    os1[intro, simp]: "M \<longrightarrow>\<^isub>1\<^sup>* M"
  | os2[intro]: "\<lbrakk>M1\<longrightarrow>\<^isub>1\<^sup>* M2; M2 \<longrightarrow>\<^isub>1 M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>\<^isub>1\<^sup>* M3"

equivariance One_star 

lemma one_star_trans:
  assumes a1: "M1\<longrightarrow>\<^isub>1\<^sup>* M2" 
  and     a2: "M2\<longrightarrow>\<^isub>1\<^sup>* M3"
  shows "M1\<longrightarrow>\<^isub>1\<^sup>* M3"
using a2 a1
by (induct) (auto)

lemma one_fresh_preserv:
  fixes a :: "name"
  assumes a: "t\<longrightarrow>\<^isub>1s"
  and     b: "a\<sharp>t"
  shows "a\<sharp>s"
using a b
by (nominal_induct avoiding: a rule: One.strong_induct)
   (auto simp add: abs_fresh fresh_atm fresh_fact)

lemma subst_rename: 
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
using a
by (nominal_induct t1 avoiding: a c t2 rule: lam.induct)
   (auto simp add: calc_atm fresh_atm abs_fresh)

lemma one_var:
  assumes a: "Var x \<longrightarrow>\<^isub>1 t"
  shows "t = Var x"
using a
by - (ind_cases2 "Var x \<longrightarrow>\<^isub>1 t", simp)

lemma one_abs: 
  fixes    t :: "lam"
  and      t':: "lam"
  and      a :: "name"
  assumes a: "(Lam [a].t)\<longrightarrow>\<^isub>1t'"
  shows "\<exists>t''. t'=Lam [a].t'' \<and> t\<longrightarrow>\<^isub>1t''"
  using a
  apply -
  apply(ind_cases2 "(Lam [a].t)\<longrightarrow>\<^isub>1t'")
  apply(auto simp add: lam.inject alpha)
  apply(rule_tac x="[(a,aa)]\<bullet>s2" in exI)
  apply(rule conjI)
  apply(perm_simp)
  apply(simp add: fresh_left calc_atm)
  apply(simp add: One.eqvt)
  apply(simp add: one_fresh_preserv)
done  

lemma one_app: 
  assumes a: "App t1 t2 \<longrightarrow>\<^isub>1 t'"
  shows "(\<exists>s1 s2. t' = App s1 s2 \<and> t1 \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2) \<or> 
         (\<exists>a s s1 s2. t1 = Lam [a].s \<and> a\<sharp>(t2,s2) \<and> t' = s1[a::=s2] \<and> s \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2)" 
  using a
  apply -
  apply(ind_cases2 "App t1 t2 \<longrightarrow>\<^isub>1 t'")
  apply(auto simp add: lam.distinct lam.inject)
  done

lemma one_red: 
  assumes a: "App (Lam [a].t1) t2 \<longrightarrow>\<^isub>1 M"
  shows "(\<exists>s1 s2. M = App (Lam [a].s1) s2 \<and> t1 \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2) \<or> 
         (\<exists>s1 s2. M = s1[a::=s2] \<and> t1 \<longrightarrow>\<^isub>1 s1 \<and> t2 \<longrightarrow>\<^isub>1 s2)" 
  using a
  apply -
  apply(ind_cases2 "App (Lam [a].t1) t2 \<longrightarrow>\<^isub>1 M")
  apply(simp_all add: lam.inject)
  apply(force)
  apply(erule conjE)
  apply(drule sym[of "Lam [a].t1"])
  apply(simp)
  apply(drule one_abs)
  apply(erule exE)
  apply(simp)
  apply(force simp add: alpha)
  apply(erule conjE)
  apply(simp add: lam.inject alpha)
  apply(erule disjE)
  apply(simp)
  apply(force)
  apply(simp)
  apply(rule disjI2)
  apply(rule_tac x="[(a,aa)]\<bullet>t2a" in exI)
  apply(rule_tac x="s2" in exI)
  apply(auto)
  apply(subgoal_tac "a\<sharp>t2a")(*A*)
  apply(simp add: subst_rename)
  (*A*)
  apply(force intro: one_fresh_preserv)
  apply(simp add: One.eqvt)
  done

text {* complete development reduction *}

inductive2
  cd1 :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ >c _" [80,80]80)
where
  cd1v[intro!]:      "Var x >c Var x"
  | cd1l[simp,intro!]: "s1 >c s2 \<Longrightarrow> Lam [a].s1 >c Lam[a].s2"
  | cd1a[simp,intro!]: "\<lbrakk>\<not>(\<exists> a s. s1 = Lam [a].s); s1 >c s2; t1 >c t2\<rbrakk> \<Longrightarrow> App s1 t1 >c App s2 t2"
  | cd1r[simp,intro!]: "\<lbrakk>a\<sharp>(s1,s2); s1 >c s2; t1 >c t2\<rbrakk> \<Longrightarrow> App (Lam [a].t1) s1 >c (t2[a::=s2])"

(* FIXME: needs to be in nominal_inductive *)
declare perm_pi_simp[eqvt_force]

equivariance cd1

nominal_inductive cd1
  by (simp_all add: abs_fresh fresh_fact')

lemma better_cd1r_intro[intro]:
  assumes a: "s1 >c s2"
  and     b: "t1 >c t2"
  shows "App (Lam [a].t1) s1 >c (t2[a::=s2])"
proof -
  obtain c::"name" where fs: "c\<sharp>(a,t1,s1,t2,s2)" by (rule exists_fresh, rule fin_supp,blast)
  have eq1: "Lam [a].t1 = Lam [c].([(c,a)]\<bullet>t1)" using fs
    by (rule_tac sym, auto simp add: lam.inject alpha fresh_prod fresh_atm)
  have "App (Lam [a].t1) s1 = App (Lam [c].([(c,a)]\<bullet>t1)) s1"
    using eq1 by simp
  also have "\<dots> >c  ([(c,a)]\<bullet>t2)[c::=s2]" using fs a b
    by (rule_tac cd1r, simp_all add: cd1.eqvt)
  also have "\<dots> = t2[a::=s2]" using fs 
    by (rule_tac subst_rename[symmetric], simp)
  finally show "App (Lam [a].t1) s1 >c (t2[a::=s2])" by simp
qed

lemma cd1_fresh_preserve:
  fixes a::"name"
  assumes a: "a\<sharp>s1" 
  and     b: "s1 >c s2"
  shows "a\<sharp>s2"
using b a
by (induct) (auto simp add: abs_fresh fresh_fact fresh_fact')

  
lemma cd1_lam:
  fixes c::"'a::fs_name"
  assumes a: "Lam [a].t >c t'"
  shows "\<exists>s. t'=Lam [a].s \<and> t >c s"
using a
apply -
apply(erule cd1.cases)
apply(simp_all)
apply(simp add: lam.inject)
apply(simp add: alpha)
apply(auto)
apply(rule_tac x="[(a,aa)]\<bullet>s2" in exI)
apply(perm_simp add: fresh_left cd1.eqvt cd1_fresh_preserve)
done

lemma develop_existence:
  shows "\<exists>M'. M >c M'"
by (nominal_induct M rule: lam.induct)
   (auto dest!: cd1_lam)

lemma triangle:
  assumes a: "M >c M'"
  and     b: "M \<longrightarrow>\<^isub>1 M''"
  shows "M'' \<longrightarrow>\<^isub>1 M'"
using a b
by (nominal_induct avoiding: M'' rule: cd1.strong_induct)
   (auto dest!: one_var one_app one_abs one_red intro: one_subst)

lemma diamond:
  assumes a: "M1 \<longrightarrow>\<^isub>1 M2"
  and     b: "M1 \<longrightarrow>\<^isub>1 M3"
  shows "\<exists>M4. M2 \<longrightarrow>\<^isub>1 M4 \<and> M3 \<longrightarrow>\<^isub>1 M4"
proof -
  obtain Mc where c: "M1 >c Mc" using develop_existence by blast
  have "M2 \<longrightarrow>\<^isub>1 Mc" using a c by (simp add: triangle)
  moreover
  have "M3 \<longrightarrow>\<^isub>1 Mc" using b c by (simp add: triangle)
  ultimately show "\<exists>M4. M2 \<longrightarrow>\<^isub>1 M4 \<and> M3 \<longrightarrow>\<^isub>1 M4" by blast
qed
  
lemma one_lam_cong: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "(Lam [a].t1)\<longrightarrow>\<^isub>\<beta>\<^sup>*(Lam [a].t2)"
  using a
proof induct
  case bs1 thus ?case by simp
next
  case (bs2 y z) 
  thus ?case by (blast dest: b3)
qed

lemma one_app_congL: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "App t1 s\<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s"
  using a
proof induct
  case bs1 thus ?case by simp
next
  case bs2 thus ?case by (blast dest: b1)
qed
  
lemma one_app_congR: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App s t2"
using a
proof induct
  case bs1 thus ?case by simp
next 
  case bs2 thus ?case by (blast dest: b2)
qed

lemma one_app_cong: 
  assumes a1: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  and     a2: "s1\<longrightarrow>\<^isub>\<beta>\<^sup>*s2" 
  shows "App t1 s1\<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s2"
proof -
  have "App t1 s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s1" using a1 by (rule one_app_congL)
  moreover
  have "App t2 s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s2" using a2 by (rule one_app_congR)
  ultimately show ?thesis by (rule beta_star_trans)
qed

lemma one_beta_star: 
  assumes a: "(t1\<longrightarrow>\<^isub>1t2)" 
  shows "(t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2)"
  using a
proof(nominal_induct rule: One.strong_induct)
  case (o4 a s1 s2 t1 t2)
  have vc: "a\<sharp>s1" "a\<sharp>s2" by fact
  have a1: "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" and a2: "s1\<longrightarrow>\<^isub>\<beta>\<^sup>*s2" by fact
  have c1: "(App (Lam [a].t2) s2) \<longrightarrow>\<^isub>\<beta> (t2 [a::= s2])" using vc by (simp add: b4)
  from a1 a2 have c2: "App (Lam [a].t1 ) s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App (Lam [a].t2 ) s2" 
    by (blast intro!: one_app_cong one_lam_cong)
  show ?case using c2 c1 by (blast intro: beta_star_trans)
qed (auto intro!: one_app_cong one_lam_cong)

lemma one_star_lam_cong: 
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "(Lam  [a].t1)\<longrightarrow>\<^isub>1\<^sup>* (Lam [a].t2)"
  using a
by (induct) (auto intro: one_star_trans)

lemma one_star_app_congL: 
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "App t1 s\<longrightarrow>\<^isub>1\<^sup>* App t2 s"
  using a
by (induct) (auto intro: one_star_trans)

lemma one_star_app_congR: 
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^isub>1\<^sup>* App s t2"
  using a
by (induct) (auto intro: one_star_trans)

lemma beta_one_star: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>t2" 
  shows "t1\<longrightarrow>\<^isub>1\<^sup>*t2"
  using a
by (induct)
   (auto intro!: one_star_app_congL one_star_app_congR one_star_lam_cong)

lemma rectangle_for_one:
  assumes a: "t\<longrightarrow>\<^isub>1\<^sup>*t1" 
  and     b: "t\<longrightarrow>\<^isub>1t2"
  shows "\<exists>t3. t1\<longrightarrow>\<^isub>1t3 \<and> t2\<longrightarrow>\<^isub>1\<^sup>*t3"
  using a b
proof (induct arbitrary: t2)
  case os1 thus ?case by force
next
  case (os2 t s1 s2 t2)  
  have b: "s1 \<longrightarrow>\<^isub>1 s2" by fact
  have h: "\<And>t2. t \<longrightarrow>\<^isub>1 t2 \<Longrightarrow> (\<exists>t3. s1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3)" by fact
  have c: "t \<longrightarrow>\<^isub>1 t2" by fact
  show "\<exists>t3. s2 \<longrightarrow>\<^isub>1 t3 \<and>  t2 \<longrightarrow>\<^isub>1\<^sup>* t3" 
  proof -
    from c h have "\<exists>t3. s1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3" by blast
    then obtain t3 where c1: "s1 \<longrightarrow>\<^isub>1 t3" and c2: "t2 \<longrightarrow>\<^isub>1\<^sup>* t3" by blast
    have "\<exists>t4. s2 \<longrightarrow>\<^isub>1 t4 \<and> t3 \<longrightarrow>\<^isub>1 t4" using b c1 by (blast intro: diamond)
    thus ?thesis using c2 by (blast intro: one_star_trans)
  qed
qed

lemma cr_for_one_star: 
  assumes a: "t\<longrightarrow>\<^isub>1\<^sup>*t2"
      and b: "t\<longrightarrow>\<^isub>1\<^sup>*t1"
    shows "\<exists>t3. t1\<longrightarrow>\<^isub>1\<^sup>*t3\<and>t2\<longrightarrow>\<^isub>1\<^sup>*t3"
using a b
proof (induct arbitrary: t1)
  case (os1 t) then show ?case by force
next 
  case (os2 t s1 s2 t1)
  have c: "t \<longrightarrow>\<^isub>1\<^sup>* s1" by fact
  have c': "t \<longrightarrow>\<^isub>1\<^sup>* t1" by fact
  have d: "s1 \<longrightarrow>\<^isub>1 s2" by fact
  have "t \<longrightarrow>\<^isub>1\<^sup>* t1 \<Longrightarrow> (\<exists>t3.  t1 \<longrightarrow>\<^isub>1\<^sup>* t3 \<and> s1 \<longrightarrow>\<^isub>1\<^sup>* t3)" by fact
  then obtain t3 where f1: "t1 \<longrightarrow>\<^isub>1\<^sup>* t3"
                   and f2: "s1 \<longrightarrow>\<^isub>1\<^sup>* t3" using c' by blast
  from rectangle_for_one d f2 have "\<exists>t4. t3\<longrightarrow>\<^isub>1t4 \<and> s2\<longrightarrow>\<^isub>1\<^sup>*t4" by blast
  then obtain t4 where g1: "t3\<longrightarrow>\<^isub>1t4"
                   and g2: "s2\<longrightarrow>\<^isub>1\<^sup>*t4" by blast
  have "t1\<longrightarrow>\<^isub>1\<^sup>*t4" using f1 g1 by (blast intro: one_star_trans)
  thus ?case using g2 by blast
qed

lemma beta_star_and_one_star: 
  shows "(M1\<longrightarrow>\<^isub>1\<^sup>*M2) = (M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2)"
proof
  assume "M1 \<longrightarrow>\<^isub>1\<^sup>* M2"
  then show "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2"
  proof induct
    case (os1 M1) thus "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M1" by simp
  next
    case (os2 M1 M2 M3)
    have "M2\<longrightarrow>\<^isub>1M3" by fact
    then have "M2\<longrightarrow>\<^isub>\<beta>\<^sup>*M3" by (rule one_beta_star)
    moreover have "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2" by fact
    ultimately show "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M3" by (auto intro: beta_star_trans)
  qed
next
  assume "M1 \<longrightarrow>\<^isub>\<beta>\<^sup>* M2" 
  then show "M1\<longrightarrow>\<^isub>1\<^sup>*M2"
  proof induct
    case (bs1 M1) thus  "M1\<longrightarrow>\<^isub>1\<^sup>*M1" by simp
  next
    case (bs2 M1 M2 M3) 
    have "M2\<longrightarrow>\<^isub>\<beta>M3" by fact
    then have "M2\<longrightarrow>\<^isub>1\<^sup>*M3" by (rule beta_one_star)
    moreover have "M1\<longrightarrow>\<^isub>1\<^sup>*M2" by fact
    ultimately show "M1\<longrightarrow>\<^isub>1\<^sup>*M3" by (auto intro: one_star_trans)
  qed
qed

lemma cr_for_beta_star: 
  assumes a1: "t\<longrightarrow>\<^isub>\<beta>\<^sup>*t1" 
  and     a2: "t\<longrightarrow>\<^isub>\<beta>\<^sup>*t2" 
  shows "\<exists>t3. t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t3\<and>t2\<longrightarrow>\<^isub>\<beta>\<^sup>*t3"
proof -
  from a1 have "t\<longrightarrow>\<^isub>1\<^sup>*t1" by (simp only: beta_star_and_one_star)
  moreover
  from a2 have "t\<longrightarrow>\<^isub>1\<^sup>*t2" by (simp only: beta_star_and_one_star)
  ultimately have "\<exists>t3. t1\<longrightarrow>\<^isub>1\<^sup>*t3 \<and> t2\<longrightarrow>\<^isub>1\<^sup>*t3" by (blast intro: cr_for_one_star) 
  then obtain t3 where "t1\<longrightarrow>\<^isub>1\<^sup>*t3" and "t2\<longrightarrow>\<^isub>1\<^sup>*t3" by (blast intro: cr_for_one_star)
  hence "t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t3" and "t2\<longrightarrow>\<^isub>\<beta>\<^sup>*t3" by (simp_all only: beta_star_and_one_star)
  then show "\<exists>t3. t1\<longrightarrow>\<^isub>\<beta>\<^sup>*t3\<and>t2\<longrightarrow>\<^isub>\<beta>\<^sup>*t3" by blast
qed

end
