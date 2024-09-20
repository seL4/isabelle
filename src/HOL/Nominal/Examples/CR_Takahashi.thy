(* Authors: Christian Urban and Mathilde Arnaud                   *)
(*                                                                *)
(* A formalisation of the Church-Rosser proof by Masako Takahashi.*)
(* This formalisation follows with some very slight exceptions    *)
(* the version of this proof given by Randy Pollack in the paper: *)
(*                                                                *)
(*  Polishing Up the Tait-Martin Löf Proof of the                 *)
(*  Church-Rosser Theorem (1995).                                 *)

theory CR_Takahashi
  imports "HOL-Nominal.Nominal"
begin

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" (\<open>Lam [_]._\<close> [100,100] 100)

nominal_primrec
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  (\<open>_[_::=_]\<close> [100,100,100] 100)
where
  "(Var x)[y::=s] = (if x=y then s else (Var x))"
| "(App t\<^sub>1 t\<^sub>2)[y::=s] = App (t\<^sub>1[y::=s]) (t\<^sub>2[y::=s])"
| "x\<sharp>(y,s) \<Longrightarrow> (Lam [x].t)[y::=s] = Lam [x].(t[y::=s])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

section \<open>Lemmas about Capture-Avoiding Substitution\<close>
 
lemma  subst_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(t1[x::=t2]) = (pi\<bullet>t1)[(pi\<bullet>x)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: x t2 rule: lam.strong_induct)
   (auto simp add: perm_bij fresh_atm fresh_bij)

lemma forget:
  shows "x\<sharp>t \<Longrightarrow> t[x::=s] = t"
by (nominal_induct t avoiding: x s rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact:
  fixes z::"name"
  shows "\<lbrakk>z\<sharp>s; (z=y \<or> z\<sharp>t)\<rbrakk> \<Longrightarrow> z\<sharp>t[y::=s]"
by (nominal_induct t avoiding: z y s rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_prod fresh_atm)

lemma substitution_lemma:  
  assumes a: "x\<noteq>y" "x\<sharp>u"
  shows "t[x::=s][y::=u] = t[y::=u][x::=s[y::=u]]"
using a 
by (nominal_induct t avoiding: x y s u rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

lemma subst_rename: 
  assumes a: "y\<sharp>t"
  shows "t[x::=s] = ([(y,x)]\<bullet>t)[y::=s]"
using a 
by (nominal_induct t avoiding: x y s rule: lam.strong_induct)
   (auto simp add: swap_simps fresh_atm abs_fresh)

section \<open>Beta-Reduction\<close>

inductive 
  "Beta" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>\<beta> _\<close> [80,80] 80)
where
  b1[intro]: "t1 \<longrightarrow>\<^sub>\<beta> t2 \<Longrightarrow> App t1 s \<longrightarrow>\<^sub>\<beta> App t2 s"
| b2[intro]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> App t s1 \<longrightarrow>\<^sub>\<beta> App t s2"
| b3[intro]: "t1 \<longrightarrow>\<^sub>\<beta> t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>\<^sub>\<beta> Lam [x].t2"
| b4[intro]: "App (Lam [x].t) s \<longrightarrow>\<^sub>\<beta> t[x::=s]"

section \<open>Transitive Closure of Beta\<close>

inductive 
  "Beta_star" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>\<beta>\<^sup>* _\<close> [80,80] 80)
where
  bs1[intro]: "t \<longrightarrow>\<^sub>\<beta>\<^sup>* t"
| bs2[intro]: "t \<longrightarrow>\<^sub>\<beta> s \<Longrightarrow> t \<longrightarrow>\<^sub>\<beta>\<^sup>* s"
| bs3[intro,trans]: "\<lbrakk>t1\<longrightarrow>\<^sub>\<beta>\<^sup>* t2; t2 \<longrightarrow>\<^sub>\<beta>\<^sup>* t3\<rbrakk> \<Longrightarrow> t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t3"

section \<open>One-Reduction\<close>

inductive 
  One :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>1 _\<close> [80,80] 80)
where
  o1[intro]: "Var x\<longrightarrow>\<^sub>1 Var x"
| o2[intro]: "\<lbrakk>t1\<longrightarrow>\<^sub>1t2; s1\<longrightarrow>\<^sub>1s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>\<^sub>1 App t2 s2"
| o3[intro]: "t1\<longrightarrow>\<^sub>1t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>\<^sub>1 Lam [x].t2"
| o4[intro]: "\<lbrakk>x\<sharp>(s1,s2); t1\<longrightarrow>\<^sub>1t2; s1\<longrightarrow>\<^sub>1s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>\<^sub>1 t2[x::=s2]"

equivariance One
nominal_inductive One 
  by (simp_all add: abs_fresh fresh_fact)

lemma One_refl:
  shows "t \<longrightarrow>\<^sub>1 t"
by (nominal_induct t rule: lam.strong_induct) (auto)

lemma One_subst: 
  assumes a: "t1 \<longrightarrow>\<^sub>1 t2" "s1 \<longrightarrow>\<^sub>1 s2"
  shows "t1[x::=s1] \<longrightarrow>\<^sub>1 t2[x::=s2]" 
using a 
by (nominal_induct t1 t2 avoiding: s1 s2 x rule: One.strong_induct)
   (auto simp add: substitution_lemma fresh_atm fresh_fact)

lemma better_o4_intro:
  assumes a: "t1 \<longrightarrow>\<^sub>1 t2" "s1 \<longrightarrow>\<^sub>1 s2"
  shows "App (Lam [x].t1) s1 \<longrightarrow>\<^sub>1 t2[x::=s2]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,t1,s1,t2,s2)" by (rule exists_fresh, rule fin_supp, blast)
  have "App (Lam [x].t1) s1 = App (Lam [y].([(y,x)]\<bullet>t1)) s1" using fs
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>\<^sub>1  ([(y,x)]\<bullet>t2)[y::=s2]" using fs a by (auto simp add: One.eqvt)
  also have "\<dots> = t2[x::=s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>\<^sub>1 t2[x::=s2]" by simp
qed

lemma One_Var:
  assumes a: "Var x \<longrightarrow>\<^sub>1 M"
  shows "M = Var x"
using a by (cases rule: One.cases) (simp_all) 

lemma One_Lam: 
  assumes a: "Lam [x].t \<longrightarrow>\<^sub>1 s" "x\<sharp>s"
  shows "\<exists>t'. s = Lam [x].t' \<and> t \<longrightarrow>\<^sub>1 t'"
using a
by (cases rule: One.strong_cases)
   (auto simp add: lam.inject abs_fresh alpha)

lemma One_App: 
  assumes a: "App t s \<longrightarrow>\<^sub>1 r"
  shows "(\<exists>t' s'. r = App t' s' \<and> t \<longrightarrow>\<^sub>1 t' \<and> s \<longrightarrow>\<^sub>1 s') \<or> 
         (\<exists>x p p' s'. r = p'[x::=s'] \<and> t = Lam [x].p \<and> p \<longrightarrow>\<^sub>1 p' \<and> s \<longrightarrow>\<^sub>1 s' \<and> x\<sharp>(s,s'))" 
using a by (cases rule: One.cases) (auto simp add: lam.inject)

lemma One_Redex: 
  assumes a: "App (Lam [x].t) s \<longrightarrow>\<^sub>1 r" "x\<sharp>(s,r)"
  shows "(\<exists>t' s'. r = App (Lam [x].t') s' \<and> t \<longrightarrow>\<^sub>1 t' \<and> s \<longrightarrow>\<^sub>1 s') \<or> 
         (\<exists>t' s'. r = t'[x::=s'] \<and> t \<longrightarrow>\<^sub>1 t' \<and> s \<longrightarrow>\<^sub>1 s')" 
using a
by (cases rule: One.strong_cases)
   (auto dest: One_Lam simp add: lam.inject abs_fresh alpha fresh_prod)

section \<open>Transitive Closure of One\<close>

inductive 
  "One_star" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>\<^sub>1\<^sup>* _\<close> [80,80] 80)
where
  os1[intro]: "t \<longrightarrow>\<^sub>1\<^sup>* t"
| os2[intro]: "t \<longrightarrow>\<^sub>1 s \<Longrightarrow> t \<longrightarrow>\<^sub>1\<^sup>* s"
| os3[intro]: "\<lbrakk>t1\<longrightarrow>\<^sub>1\<^sup>* t2; t2 \<longrightarrow>\<^sub>1\<^sup>* t3\<rbrakk> \<Longrightarrow> t1 \<longrightarrow>\<^sub>1\<^sup>* t3"

section \<open>Complete Development Reduction\<close>

inductive 
  Dev :: "lam \<Rightarrow> lam \<Rightarrow> bool" (\<open> _ \<longrightarrow>\<^sub>d _\<close> [80,80]80)
where
  d1[intro]: "Var x \<longrightarrow>\<^sub>d Var x"
| d2[intro]: "t \<longrightarrow>\<^sub>d s \<Longrightarrow> Lam [x].t \<longrightarrow>\<^sub>d Lam[x].s"
| d3[intro]: "\<lbrakk>\<not>(\<exists>y t'. t1 = Lam [y].t'); t1 \<longrightarrow>\<^sub>d t2; s1 \<longrightarrow>\<^sub>d s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>\<^sub>d App t2 s2"
| d4[intro]: "\<lbrakk>x\<sharp>(s1,s2); t1 \<longrightarrow>\<^sub>d t2; s1 \<longrightarrow>\<^sub>d s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>\<^sub>d t2[x::=s2]"

equivariance Dev
nominal_inductive Dev 
  by (simp_all add: abs_fresh fresh_fact)

lemma better_d4_intro:
  assumes a: "t1 \<longrightarrow>\<^sub>d t2" "s1 \<longrightarrow>\<^sub>d s2"
  shows "App (Lam [x].t1) s1 \<longrightarrow>\<^sub>d t2[x::=s2]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,t1,s1,t2,s2)" by (rule exists_fresh, rule fin_supp,blast)
  have "App (Lam [x].t1) s1 = App (Lam [y].([(y,x)]\<bullet>t1)) s1" using fs
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>\<^sub>d  ([(y,x)]\<bullet>t2)[y::=s2]" using fs a by (auto simp add: Dev.eqvt)
  also have "\<dots> = t2[x::=s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>\<^sub>d t2[x::=s2]" by simp
qed

lemma Dev_preserves_fresh:
  fixes x::"name"
  assumes a: "M\<longrightarrow>\<^sub>d N"  
  shows "x\<sharp>M \<Longrightarrow> x\<sharp>N"
using a
by (induct) (auto simp add: abs_fresh fresh_fact)

lemma Dev_Lam:
  assumes a: "Lam [x].M \<longrightarrow>\<^sub>d N" 
  shows "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>\<^sub>d N'"
proof -
  from a have "x\<sharp>Lam [x].M" by (simp add: abs_fresh)
  with a have "x\<sharp>N" by (simp add: Dev_preserves_fresh)
  with a show "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>\<^sub>d N'"
    by (cases rule: Dev.strong_cases)
       (auto simp add: lam.inject abs_fresh alpha)
qed

lemma Development_existence:
  shows "\<exists>M'. M \<longrightarrow>\<^sub>d M'"
by (nominal_induct M rule: lam.strong_induct)
   (auto dest!: Dev_Lam intro: better_d4_intro)

lemma Triangle:
  assumes a: "t \<longrightarrow>\<^sub>d t1" "t \<longrightarrow>\<^sub>1 t2"
  shows "t2 \<longrightarrow>\<^sub>1 t1"
using a 
proof(nominal_induct avoiding: t2 rule: Dev.strong_induct)
  case (d4 x s1 s2 t1 t1' t2) 
  have  fc: "x\<sharp>t2" "x\<sharp>s1" by fact+ 
  have "App (Lam [x].t1) s1 \<longrightarrow>\<^sub>1 t2" by fact
  then obtain t' s' where reds: 
             "(t2 = App (Lam [x].t') s' \<and> t1 \<longrightarrow>\<^sub>1 t' \<and> s1 \<longrightarrow>\<^sub>1 s') \<or> 
              (t2 = t'[x::=s'] \<and> t1 \<longrightarrow>\<^sub>1 t' \<and> s1 \<longrightarrow>\<^sub>1 s')"
  using fc by (auto dest!: One_Redex)
  have ih1: "t1 \<longrightarrow>\<^sub>1 t' \<Longrightarrow>  t' \<longrightarrow>\<^sub>1 t1'" by fact
  have ih2: "s1 \<longrightarrow>\<^sub>1 s' \<Longrightarrow>  s' \<longrightarrow>\<^sub>1 s2" by fact
  { assume "t1 \<longrightarrow>\<^sub>1 t'" "s1 \<longrightarrow>\<^sub>1 s'"
    then have "App (Lam [x].t') s' \<longrightarrow>\<^sub>1 t1'[x::=s2]" 
      using ih1 ih2 by (auto intro: better_o4_intro)
  }
  moreover
  { assume "t1 \<longrightarrow>\<^sub>1 t'" "s1 \<longrightarrow>\<^sub>1 s'"
    then have "t'[x::=s'] \<longrightarrow>\<^sub>1 t1'[x::=s2]" 
      using ih1 ih2 by (auto intro: One_subst)
  }
  ultimately show "t2 \<longrightarrow>\<^sub>1 t1'[x::=s2]" using reds by auto 
qed (auto dest!: One_Lam One_Var One_App)

lemma Diamond_for_One:
  assumes a: "t \<longrightarrow>\<^sub>1 t1" "t \<longrightarrow>\<^sub>1 t2"
  shows "\<exists>t3. t2 \<longrightarrow>\<^sub>1 t3 \<and> t1 \<longrightarrow>\<^sub>1 t3"
proof -
  obtain tc where "t \<longrightarrow>\<^sub>d tc" using Development_existence by blast
  with a have "t2 \<longrightarrow>\<^sub>1 tc" and "t1 \<longrightarrow>\<^sub>1 tc" by (simp_all add: Triangle)
  then show "\<exists>t3. t2 \<longrightarrow>\<^sub>1 t3 \<and> t1 \<longrightarrow>\<^sub>1 t3" by blast
qed

lemma Rectangle_for_One:
  assumes a:  "t \<longrightarrow>\<^sub>1\<^sup>* t1" "t \<longrightarrow>\<^sub>1 t2" 
  shows "\<exists>t3. t1 \<longrightarrow>\<^sub>1 t3 \<and> t2 \<longrightarrow>\<^sub>1\<^sup>* t3"
using a Diamond_for_One by (induct arbitrary: t2) (blast)+

lemma CR_for_One_star: 
  assumes a: "t \<longrightarrow>\<^sub>1\<^sup>* t1" "t \<longrightarrow>\<^sub>1\<^sup>* t2"
    shows "\<exists>t3. t2 \<longrightarrow>\<^sub>1\<^sup>* t3 \<and> t1 \<longrightarrow>\<^sub>1\<^sup>* t3"
using a Rectangle_for_One by (induct arbitrary: t2) (blast)+

section \<open>Establishing the Equivalence of Beta-star and One-star\<close>

lemma Beta_Lam_cong: 
  assumes a: "t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t2" 
  shows "Lam [x].t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* Lam [x].t2"
using a by (induct) (blast)+

lemma Beta_App_cong_aux: 
  assumes a: "t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t2" 
  shows "App t1 s\<longrightarrow>\<^sub>\<beta>\<^sup>* App t2 s"
    and "App s t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* App s t2"
using a by (induct) (blast)+

lemma Beta_App_cong: 
  assumes a: "t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t2" "s1 \<longrightarrow>\<^sub>\<beta>\<^sup>* s2" 
  shows "App t1 s1 \<longrightarrow>\<^sub>\<beta>\<^sup>* App t2 s2"
using a by (blast intro: Beta_App_cong_aux)

lemmas Beta_congs = Beta_Lam_cong Beta_App_cong

lemma One_implies_Beta_star: 
  assumes a: "t \<longrightarrow>\<^sub>1 s"
  shows "t \<longrightarrow>\<^sub>\<beta>\<^sup>* s"
using a by (induct) (auto intro!: Beta_congs)

lemma One_congs: 
  assumes a: "t1 \<longrightarrow>\<^sub>1\<^sup>* t2" 
  shows "Lam [x].t1 \<longrightarrow>\<^sub>1\<^sup>* Lam [x].t2"
  and   "App t1 s \<longrightarrow>\<^sub>1\<^sup>* App t2 s"
  and   "App s t1 \<longrightarrow>\<^sub>1\<^sup>* App s t2"
using a by (induct) (auto intro: One_refl)

lemma Beta_implies_One_star: 
  assumes a: "t1 \<longrightarrow>\<^sub>\<beta> t2" 
  shows "t1 \<longrightarrow>\<^sub>1\<^sup>* t2"
using a by (induct) (auto intro: One_refl One_congs better_o4_intro)

lemma Beta_star_equals_One_star: 
  shows "t1 \<longrightarrow>\<^sub>1\<^sup>* t2 = t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t2"
proof
  assume "t1 \<longrightarrow>\<^sub>1\<^sup>* t2"
  then show "t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t2" by (induct) (auto intro: One_implies_Beta_star)
next
  assume "t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t2" 
  then show "t1 \<longrightarrow>\<^sub>1\<^sup>* t2" by (induct) (auto intro: Beta_implies_One_star)
qed

section \<open>The Church-Rosser Theorem\<close>

theorem CR_for_Beta_star: 
  assumes a: "t \<longrightarrow>\<^sub>\<beta>\<^sup>* t1" "t\<longrightarrow>\<^sub>\<beta>\<^sup>* t2" 
  shows "\<exists>t3. t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t3 \<and> t2 \<longrightarrow>\<^sub>\<beta>\<^sup>* t3"
proof -
  from a have "t \<longrightarrow>\<^sub>1\<^sup>* t1" and "t\<longrightarrow>\<^sub>1\<^sup>* t2" by (simp_all add: Beta_star_equals_One_star)
  then have "\<exists>t3. t1 \<longrightarrow>\<^sub>1\<^sup>* t3 \<and> t2 \<longrightarrow>\<^sub>1\<^sup>* t3" by (simp add: CR_for_One_star) 
  then show "\<exists>t3. t1 \<longrightarrow>\<^sub>\<beta>\<^sup>* t3 \<and> t2 \<longrightarrow>\<^sub>\<beta>\<^sup>* t3" by (simp add: Beta_star_equals_One_star)
qed



end
