(* $Id$ *)

theory CR_Takahashi
imports "../Nominal"
begin

text {* Authors: Mathilde Arnaud and Christian Urban

        The Church-Rosser proof from a paper by Masako Takahashi.
        This formalisation follows with some very slight exceptions 
        the one given by Randy Pollack in the paper:

           Polishing Up the Tait-Martin Löf Proof of the 
           Church-Rosser Theorem (1995).

  *}

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

consts subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [100,100,100] 100)

nominal_primrec
  "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

section {* Lemmas about Capture-Avoiding Substitution *}
 
lemma subst_eqvt[eqvt]:
  fixes pi:: "name prm"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: b t2 rule: lam.induct)
   (auto simp add: perm_bij fresh_atm fresh_bij)

lemma forget:
  assumes a: "x\<sharp>L"
  shows "L[x::=P] = L"
using a by (nominal_induct L avoiding: x P rule: lam.induct)
           (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact:
  fixes z::"name"
  assumes a: "z\<sharp>N" "z\<sharp>L"
  shows "z\<sharp>(N[y::=L])"
using a by (nominal_induct N avoiding: z y L rule: lam.induct)
           (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact': 
  fixes x::"name"
  assumes a: "x\<sharp>N"
  shows "x\<sharp>M[x::=N]"
using a by (nominal_induct M avoiding: x N rule: lam.induct)
           (auto simp add: abs_fresh fresh_atm)

lemma substitution_lemma:  
  assumes a: "x\<noteq>y" "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a by (nominal_induct M avoiding: x y N L rule: lam.induct)
           (auto simp add: fresh_fact forget)

lemma subst_rename: 
  assumes a: "y\<sharp>M"
  shows "M[x::=N] = ([(y,x)]\<bullet>M)[y::=N]"
using a by (nominal_induct M avoiding: x y N rule: lam.induct)
           (auto simp add: calc_atm fresh_atm abs_fresh)

section {* Beta-Reduction *}

inductive2
  "Beta" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
where
  b1[intro]: "M1\<longrightarrow>\<^isub>\<beta>M2 \<Longrightarrow> App M1 N \<longrightarrow>\<^isub>\<beta> App M2 N"
| b2[intro]: "N1\<longrightarrow>\<^isub>\<beta>N2 \<Longrightarrow> App M N1 \<longrightarrow>\<^isub>\<beta> App M N2"
| b3[intro]: "M1\<longrightarrow>\<^isub>\<beta>M2 \<Longrightarrow> Lam [x].M1 \<longrightarrow>\<^isub>\<beta> Lam [x].M2"
| b4[intro]: "(App (Lam [x].M) N)\<longrightarrow>\<^isub>\<beta> M[x::=N]"

section {* Transitive Closure of Beta *}

inductive2
  "Beta_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta>\<^sup>* _" [80,80] 80)
where
  bs1[intro]: "M \<longrightarrow>\<^isub>\<beta>\<^sup>* M"
| bs2[intro]: "\<lbrakk>M1\<longrightarrow>\<^isub>\<beta>\<^sup>* M2; M2 \<longrightarrow>\<^isub>\<beta> M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>\<^isub>\<beta>\<^sup>* M3"

lemma Beta_star_trans[trans]:
  assumes a1: "M1\<longrightarrow>\<^isub>\<beta>\<^sup>* M2"
  and     a2: "M2\<longrightarrow>\<^isub>\<beta>\<^sup>* M3"
  shows "M1 \<longrightarrow>\<^isub>\<beta>\<^sup>* M3"
using a2 a1 by (induct) (auto)

section {* One-Reduction *}

inductive2
  One :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1 _" [80,80] 80)
where
  o1[intro]: "Var x\<longrightarrow>\<^isub>1 Var x"
| o2[intro]: "\<lbrakk>M1\<longrightarrow>\<^isub>1M2; N1\<longrightarrow>\<^isub>1N2\<rbrakk> \<Longrightarrow> (App M1 N1)\<longrightarrow>\<^isub>1(App M2 N2)"
| o3[intro]: "M1\<longrightarrow>\<^isub>1M2 \<Longrightarrow> (Lam [x].M1)\<longrightarrow>\<^isub>1(Lam [x].M2)"
| o4[intro]: "\<lbrakk>x\<sharp>(N1,N2); M1\<longrightarrow>\<^isub>1M2; N1\<longrightarrow>\<^isub>1N2\<rbrakk> \<Longrightarrow> (App (Lam [x].M1) N1)\<longrightarrow>\<^isub>1M2[x::=N2]"

equivariance One

nominal_inductive One by (simp_all add: abs_fresh fresh_fact')

lemma One_refl:
  shows "M\<longrightarrow>\<^isub>1M"
by (nominal_induct M rule: lam.induct) (auto)

lemma One_subst: 
  assumes a: "M\<longrightarrow>\<^isub>1M'" "N\<longrightarrow>\<^isub>1N'"
  shows "M[x::=N]\<longrightarrow>\<^isub>1M'[x::=N']" 
using a by (nominal_induct M M' avoiding: N N' x rule: One.strong_induct)
           (auto simp add: substitution_lemma fresh_atm fresh_fact)

lemma better_o4_intro:
  assumes a: "M1 \<longrightarrow>\<^isub>1 M2" "N1 \<longrightarrow>\<^isub>1 N2"
  shows "App (Lam [x].M1) N1 \<longrightarrow>\<^isub>1 M2[x::=N2]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,M1,N1,M2,N2)" by (rule exists_fresh, rule fin_supp,blast)
  have "App (Lam [x].M1) N1 = App (Lam [y].([(y,x)]\<bullet>M1)) N1" using fs
    by (rule_tac sym, auto simp add: lam.inject alpha fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>\<^isub>1  ([(y,x)]\<bullet>M2)[y::=N2]" using fs a by (auto simp add: One.eqvt)
  also have "\<dots> = M2[x::=N2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].M1) N1 \<longrightarrow>\<^isub>1 M2[x::=N2]" by simp
qed

lemma One_fresh_preserved:
  fixes a :: "name"
  assumes a: "M\<longrightarrow>\<^isub>1N" 
  shows "a\<sharp>M \<Longrightarrow> a\<sharp>N"
using a by (nominal_induct avoiding: a rule: One.strong_induct)
           (auto simp add: abs_fresh fresh_atm fresh_fact)

lemma One_Var:
  assumes a: "Var x \<longrightarrow>\<^isub>1 M"
  shows "M = Var x"
using a by (erule_tac One.cases) (simp_all) 

lemma One_Lam: 
  assumes a: "(Lam [x].N)\<longrightarrow>\<^isub>1 M"
  shows "\<exists>M'. M = Lam [x].M' \<and> N \<longrightarrow>\<^isub>1 M'"
using a
  apply(erule_tac One.cases)
  apply(auto simp add: lam.inject alpha)
  apply(rule_tac x="[(x,xa)]\<bullet>M2" in exI)
  apply(perm_simp add: fresh_left calc_atm)
  apply(auto simp add: One.eqvt One_fresh_preserved)
done  

lemma One_App: 
  assumes a: "App M N \<longrightarrow>\<^isub>1 R"
  shows "(\<exists>M' N'. R = App M' N' \<and> M \<longrightarrow>\<^isub>1 M' \<and> N \<longrightarrow>\<^isub>1 N') \<or> 
         (\<exists>x P P' N'. M = Lam [x].P \<and> x\<sharp>(N,N') \<and> R = P'[x::=N'] \<and> P \<longrightarrow>\<^isub>1 P' \<and> N \<longrightarrow>\<^isub>1 N')" 
using a by (erule_tac One.cases) (auto simp add: lam.inject)

lemma One_Redex: 
  assumes a: "App (Lam [x].M) N \<longrightarrow>\<^isub>1 R"
  shows "(\<exists>M' N'. R = App (Lam [x].M') N' \<and> M \<longrightarrow>\<^isub>1 M' \<and> N \<longrightarrow>\<^isub>1 N') \<or> 
         (\<exists>M' N'. R = M'[x::=N'] \<and> M \<longrightarrow>\<^isub>1 M' \<and> N \<longrightarrow>\<^isub>1 N')" 
  using a
  apply(erule_tac One.cases)
  apply(simp_all)
  apply(rule disjI1)
  apply(auto simp add: lam.inject)[1]
  apply(drule One_Lam)
  apply(simp)
  apply(rule disjI2)
  apply(auto simp add: lam.inject alpha)
  apply(rule_tac x="[(x,xa)]\<bullet>M2" in exI)
  apply(rule_tac x="N2" in exI)
  apply(simp add: subst_rename One_fresh_preserved One.eqvt)
  done

section {* Transitive Closure of One *}

inductive2
  "One_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1\<^sup>* _" [80,80] 80)
where
  os1[intro]: "M \<longrightarrow>\<^isub>1\<^sup>* M"
| os2[intro]: "\<lbrakk>M1\<longrightarrow>\<^isub>1\<^sup>* M2; M2 \<longrightarrow>\<^isub>1 M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>\<^isub>1\<^sup>* M3"

lemma One_star_trans:
  assumes a1: "M1\<longrightarrow>\<^isub>1\<^sup>* M2" 
  and     a2: "M2\<longrightarrow>\<^isub>1\<^sup>* M3"
  shows "M1\<longrightarrow>\<^isub>1\<^sup>* M3"
using a2 a1 by (induct) (auto)

text {* Complete Development Reduction *}

inductive2
  Dev :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>\<^isub>d _" [80,80]80)
where
    d1[intro]: "Var x \<longrightarrow>\<^isub>d Var x"
  | d2[intro]: "M \<longrightarrow>\<^isub>d N \<Longrightarrow> Lam [x].M \<longrightarrow>\<^isub>d Lam[x].N"
  | d3[intro]: "\<lbrakk>\<not>(\<exists>y M'. M1 = Lam [y].M'); M1 \<longrightarrow>\<^isub>d M2; N1 \<longrightarrow>\<^isub>d N2\<rbrakk> \<Longrightarrow> App M1 N1 \<longrightarrow>\<^isub>d App M2 N2"
  | d4[intro]: "\<lbrakk>x\<sharp>(N1,N2); M1 \<longrightarrow>\<^isub>d M2; N1 \<longrightarrow>\<^isub>d N2\<rbrakk> \<Longrightarrow> App (Lam [x].M1) N1 \<longrightarrow>\<^isub>d M2[x::=N2]"

(* FIXME: needs to be in nominal_inductive *)
declare perm_pi_simp[eqvt_force]

equivariance Dev

nominal_inductive Dev by (simp_all add: abs_fresh fresh_fact')

lemma better_d4_intro:
  assumes a: "M1 \<longrightarrow>\<^isub>d M2" "N1 \<longrightarrow>\<^isub>d N2"
  shows "App (Lam [x].M1) N1 \<longrightarrow>\<^isub>d M2[x::=N2]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,M1,N1,M2,N2)" by (rule exists_fresh, rule fin_supp,blast)
  have "App (Lam [x].M1) N1 = App (Lam [y].([(y,x)]\<bullet>M1)) N1" using fs
    by (rule_tac sym, auto simp add: lam.inject alpha fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>\<^isub>d  ([(y,x)]\<bullet>M2)[y::=N2]" using fs a by (auto simp add: Dev.eqvt)
  also have "\<dots> = M2[x::=N2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].M1) N1 \<longrightarrow>\<^isub>d M2[x::=N2]" by simp
qed

lemma Dev_fresh_preserved:
  fixes x::"name"
  assumes a: "M\<longrightarrow>\<^isub>d N"  
  shows "x\<sharp>M \<Longrightarrow> x\<sharp>N"
using a by (induct) (auto simp add: abs_fresh fresh_fact fresh_fact')
  
lemma Dev_Lam:
  assumes a: "Lam [x].M \<longrightarrow>\<^isub>d N"
  shows "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>\<^isub>d N'"
using a
apply(erule_tac Dev.cases)
apply(auto simp add: lam.inject alpha)
apply(rule_tac x="[(x,xa)]\<bullet>N" in exI)
apply(perm_simp add: fresh_left Dev.eqvt Dev_fresh_preserved)
done

lemma Development_existence:
  shows "\<exists>M'. M \<longrightarrow>\<^isub>d M'"
by (nominal_induct M rule: lam.induct)
   (auto dest!: Dev_Lam intro: better_d4_intro)

lemma Triangle:
  assumes a: "M \<longrightarrow>\<^isub>d M1" "M \<longrightarrow>\<^isub>1 M2"
  shows "M2 \<longrightarrow>\<^isub>1 M1"
using a by (nominal_induct avoiding: M2 rule: Dev.strong_induct)
           (auto dest!: One_Var One_App One_Redex One_Lam intro: One_subst)
(* Remark: we could here get away with a normal induction and appealing to One_fresh_preserved *)

lemma Diamond_for_One:
  assumes a: "M \<longrightarrow>\<^isub>1 M1" "M \<longrightarrow>\<^isub>1 M2"
  shows "\<exists>M3. M1 \<longrightarrow>\<^isub>1 M3 \<and> M2 \<longrightarrow>\<^isub>1 M3"
proof -
  obtain Mc where "M \<longrightarrow>\<^isub>d Mc" using Development_existence by blast
  with a have "M1 \<longrightarrow>\<^isub>1 Mc" and "M2 \<longrightarrow>\<^isub>1 Mc" by (simp_all add: Triangle)
  then show "\<exists>M3. M1 \<longrightarrow>\<^isub>1 M3 \<and> M2 \<longrightarrow>\<^isub>1 M3" by blast
qed

lemma Rectangle_for_One:
  assumes a: "M\<longrightarrow>\<^isub>1\<^sup>*M1" "M\<longrightarrow>\<^isub>1M2"
  shows "\<exists>M3. M1\<longrightarrow>\<^isub>1M3 \<and> M2\<longrightarrow>\<^isub>1\<^sup>*M3"
  using a
proof (induct arbitrary: M2)
  case (os2 M1 M2 M3 M')  
  have a1: "M1 \<longrightarrow>\<^isub>1 M'" by fact
  have a2: "M2 \<longrightarrow>\<^isub>1 M3" by fact
  have ih: "M1 \<longrightarrow>\<^isub>1 M' \<Longrightarrow> (\<exists>M3'. M2 \<longrightarrow>\<^isub>1 M3' \<and> M' \<longrightarrow>\<^isub>1\<^sup>* M3')" by fact
  from a1 ih obtain M3' where b1: "M2 \<longrightarrow>\<^isub>1 M3'" and b2: "M' \<longrightarrow>\<^isub>1\<^sup>* M3'" by blast
  from a2 b1 obtain M4 where c1: "M3 \<longrightarrow>\<^isub>1 M4" and c2: "M3' \<longrightarrow>\<^isub>1 M4" by (auto dest: Diamond_for_One)  
  from b2 c2 have "M' \<longrightarrow>\<^isub>1\<^sup>* M4" by (blast intro: One_star.os2)
  then show "\<exists>M4. M3 \<longrightarrow>\<^isub>1 M4 \<and>  M' \<longrightarrow>\<^isub>1\<^sup>* M4" using c1 by blast 
qed (auto)
  
lemma CR_for_One_star: 
  assumes a: "M\<longrightarrow>\<^isub>1\<^sup>*M1" "M\<longrightarrow>\<^isub>1\<^sup>*M2"
    shows "\<exists>M3. M1\<longrightarrow>\<^isub>1\<^sup>*M3 \<and> M2\<longrightarrow>\<^isub>1\<^sup>*M3"
using a 
proof (induct arbitrary: M2)
  case (os2 M1 M2 M3 M')
  have a1: "M1 \<longrightarrow>\<^isub>1\<^sup>* M'" by fact
  have a2: "M2 \<longrightarrow>\<^isub>1 M3" by fact
  have ih: "M1 \<longrightarrow>\<^isub>1\<^sup>* M' \<Longrightarrow> (\<exists>M3'. M2 \<longrightarrow>\<^isub>1\<^sup>* M3' \<and> M' \<longrightarrow>\<^isub>1\<^sup>* M3')" by fact
  from a1 ih obtain M3' where b1: "M2 \<longrightarrow>\<^isub>1\<^sup>* M3'" and b2: "M' \<longrightarrow>\<^isub>1\<^sup>* M3'" by blast
  from a2 b1 obtain M4 where c1: "M3 \<longrightarrow>\<^isub>1\<^sup>* M4" and c2: "M3' \<longrightarrow>\<^isub>1 M4" by (auto dest: Rectangle_for_One)  
  from b2 c2 have "M' \<longrightarrow>\<^isub>1\<^sup>* M4" by (blast intro: One_star.os2)
  then show "\<exists>M4. M3 \<longrightarrow>\<^isub>1\<^sup>* M4 \<and>  M' \<longrightarrow>\<^isub>1\<^sup>* M4" using c1 by blast 
qed (auto)

section {* Establishing the Equivalence of Beta-star and One-star *}

lemma Beta_Lam_cong: 
  assumes a: "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2" 
  shows "(Lam [x].M1)\<longrightarrow>\<^isub>\<beta>\<^sup>*(Lam [x].M2)"
using a by (induct) (blast)+

lemma Beta_App_congL: 
  assumes a: "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2" 
  shows "App M1 N\<longrightarrow>\<^isub>\<beta>\<^sup>* App M2 N"
using a by (induct) (blast)+
  
lemma Beta_App_congR: 
  assumes a: "N1\<longrightarrow>\<^isub>\<beta>\<^sup>*N2" 
  shows "App M N1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App M N2"
using a by (induct) (blast)+

lemma Beta_App_cong: 
  assumes a: "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2" "N1\<longrightarrow>\<^isub>\<beta>\<^sup>*N2" 
  shows "App M1 N1\<longrightarrow>\<^isub>\<beta>\<^sup>* App M2 N2"
proof -
  have "App M1 N1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App M2 N1" using a by (rule_tac Beta_App_congL)
  also have "\<dots> \<longrightarrow>\<^isub>\<beta>\<^sup>* App M2 N2" using a by (rule_tac Beta_App_congR)
  finally show "App M1 N1\<longrightarrow>\<^isub>\<beta>\<^sup>* App M2 N2" by simp
qed

lemmas Beta_congs = Beta_Lam_cong Beta_App_cong

lemma One_implies_Beta_star: 
  assumes a: "M\<longrightarrow>\<^isub>1N" 
  shows "M\<longrightarrow>\<^isub>\<beta>\<^sup>*N"
using a by (induct) (auto intro: Beta_congs)

lemma One_star_Lam_cong: 
  assumes a: "M1\<longrightarrow>\<^isub>1\<^sup>*M2" 
  shows "(Lam  [x].M1)\<longrightarrow>\<^isub>1\<^sup>* (Lam [x].M2)"
using a by (induct) (auto intro: One_star_trans)

lemma One_star_App_congL: 
  assumes a: "M1\<longrightarrow>\<^isub>1\<^sup>*M2" 
  shows "App M1 N\<longrightarrow>\<^isub>1\<^sup>* App M2 N"
using a 
by (induct) (auto intro: One_star_trans One_refl)

lemma One_star_App_congR: 
  assumes a: "t1\<longrightarrow>\<^isub>1\<^sup>*t2" 
  shows "App s t1 \<longrightarrow>\<^isub>1\<^sup>* App s t2"
using a by (induct) (auto intro: One_refl One_star_trans)

lemmas One_congs = One_star_App_congL One_star_App_congR One_star_Lam_cong

lemma Beta_implies_One_star: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>t2" 
  shows "t1\<longrightarrow>\<^isub>1\<^sup>*t2"
using a by (induct) (auto intro: One_refl One_congs better_o4_intro)

lemma Beta_star_equals_One_star: 
  shows "M1\<longrightarrow>\<^isub>1\<^sup>*M2 = M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2"
proof
  assume "M1 \<longrightarrow>\<^isub>1\<^sup>* M2"
  then show "M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M2" by (induct) (auto intro: One_implies_Beta_star Beta_star_trans)
next
  assume "M1 \<longrightarrow>\<^isub>\<beta>\<^sup>* M2" 
  then show "M1\<longrightarrow>\<^isub>1\<^sup>*M2" by (induct) (auto intro: Beta_implies_One_star One_star_trans)
qed

section {* The Church-Rosser Theorem *}

theorem CR_for_Beta_star: 
  assumes a: "M\<longrightarrow>\<^isub>\<beta>\<^sup>*M1" "M\<longrightarrow>\<^isub>\<beta>\<^sup>*M2" 
  shows "\<exists>M3. M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M3 \<and> M2\<longrightarrow>\<^isub>\<beta>\<^sup>*M3"
proof -
  from a have "M\<longrightarrow>\<^isub>1\<^sup>*M1" and "M\<longrightarrow>\<^isub>1\<^sup>*M2" by (simp_all only: Beta_star_equals_One_star)
  then have "\<exists>M3. M1\<longrightarrow>\<^isub>1\<^sup>*M3 \<and> M2\<longrightarrow>\<^isub>1\<^sup>*M3" by (rule_tac CR_for_One_star) 
  then show "\<exists>M3. M1\<longrightarrow>\<^isub>\<beta>\<^sup>*M3 \<and> M2\<longrightarrow>\<^isub>\<beta>\<^sup>*M3" by (simp only: Beta_star_equals_One_star)
qed

end
