(* $Id$ *)

(* Authors: Christian Urban and Mathilde Arnaud                   *)
(*                                                                *)
(* A formalisation of the Church-Rosser proof by Masako Takahashi.*)
(* This formalisation follows with some very slight exceptions    *)
(* the version of this proof given by Randy Pollack in the paper: *)
(*                                                                *)
(*  Polishing Up the Tait-Martin Löf Proof of the                 *)
(*  Church-Rosser Theorem (1995).                                 *)

theory CR_Takahashi
  imports "../Nominal"
begin

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

consts subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [100,100,100] 100)

nominal_primrec
  "(Var x)[y::=s] = (if x=y then s else (Var x))"
  "(App t\<^isub>1 t\<^isub>2)[y::=s] = App (t\<^isub>1[y::=s]) (t\<^isub>2[y::=s])"
  "x\<sharp>(y,s) \<Longrightarrow> (Lam [x].t)[y::=s] = Lam [x].(t[y::=s])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

section {* Lemmas about Capture-Avoiding Substitution *}
 
lemma  subst_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>t1[x::=t2] = (pi\<bullet>t1)[(pi\<bullet>x)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: x t2 rule: lam.induct)
   (auto simp add: perm_bij fresh_atm fresh_bij)

lemma forget:
  shows "x\<sharp>t \<Longrightarrow> t[x::=s] = t"
by (nominal_induct t avoiding: x s rule: lam.induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact:
  fixes z::"name"
  shows "z\<sharp>s \<and> (z=y \<or> z\<sharp>t) \<Longrightarrow> z\<sharp>t[y::=s]"
by (nominal_induct t avoiding: z y s rule: lam.induct)
   (auto simp add: abs_fresh fresh_prod fresh_atm)

lemma substitution_lemma:  
  assumes a: "x\<noteq>y" "x\<sharp>u"
  shows "t[x::=s][y::=u] = t[y::=u][x::=s[y::=u]]"
using a by (nominal_induct t avoiding: x y s u rule: lam.induct)
           (auto simp add: fresh_fact forget)

lemma subst_rename: 
  assumes a: "y\<sharp>t"
  shows "t[x::=s] = ([(y,x)]\<bullet>t)[y::=s]"
using a by (nominal_induct t avoiding: x y s rule: lam.induct)
           (auto simp add: calc_atm fresh_atm abs_fresh)

section {* Beta-Reduction *}

inductive 
  "Beta" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
where
  b1[intro]: "t1 \<longrightarrow>\<^isub>\<beta> t2 \<Longrightarrow> App t1 s \<longrightarrow>\<^isub>\<beta> App t2 s"
| b2[intro]: "s1 \<longrightarrow>\<^isub>\<beta> s2 \<Longrightarrow> App t s1 \<longrightarrow>\<^isub>\<beta> App t s2"
| b3[intro]: "t1 \<longrightarrow>\<^isub>\<beta> t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>\<^isub>\<beta> Lam [x].t2"
| b4[intro]: "App (Lam [x].t) s \<longrightarrow>\<^isub>\<beta> t[x::=s]"

section {* Transitive Closure of Beta *}

inductive 
  "Beta_star" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta>\<^sup>* _" [80,80] 80)
where
  bs1[intro]: "t \<longrightarrow>\<^isub>\<beta>\<^sup>* t"
| bs2[intro]: "t \<longrightarrow>\<^isub>\<beta> s \<Longrightarrow> t \<longrightarrow>\<^isub>\<beta>\<^sup>* s"
| bs3[intro,trans]: "\<lbrakk>t1\<longrightarrow>\<^isub>\<beta>\<^sup>* t2; t2 \<longrightarrow>\<^isub>\<beta>\<^sup>* t3\<rbrakk> \<Longrightarrow> t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t3"

section {* One-Reduction *}

inductive 
  One :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1 _" [80,80] 80)
where
  o1[intro]: "Var x\<longrightarrow>\<^isub>1 Var x"
| o2[intro]: "\<lbrakk>t1\<longrightarrow>\<^isub>1t2; s1\<longrightarrow>\<^isub>1s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>\<^isub>1 App t2 s2"
| o3[intro]: "t1\<longrightarrow>\<^isub>1t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>\<^isub>1 Lam [x].t2"
| o4[intro]: "\<lbrakk>x\<sharp>(s1,s2); t1\<longrightarrow>\<^isub>1t2; s1\<longrightarrow>\<^isub>1s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>\<^isub>1 t2[x::=s2]"

equivariance One
nominal_inductive One 
  by (simp_all add: abs_fresh fresh_fact)

lemma One_refl:
  shows "t \<longrightarrow>\<^isub>1 t"
by (nominal_induct t rule: lam.induct) (auto)

lemma One_subst: 
  assumes a: "t1 \<longrightarrow>\<^isub>1 t2" "s1 \<longrightarrow>\<^isub>1 s2"
  shows "t1[x::=s1] \<longrightarrow>\<^isub>1 t2[x::=s2]" 
using a by (nominal_induct t1 t2 avoiding: s1 s2 x rule: One.strong_induct)
           (auto simp add: substitution_lemma fresh_atm fresh_fact)

lemma better_o4_intro:
  assumes a: "t1 \<longrightarrow>\<^isub>1 t2" "s1 \<longrightarrow>\<^isub>1 s2"
  shows "App (Lam [x].t1) s1 \<longrightarrow>\<^isub>1 t2[x::=s2]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,t1,s1,t2,s2)" by (rule exists_fresh, rule fin_supp, blast)
  have "App (Lam [x].t1) s1 = App (Lam [y].([(y,x)]\<bullet>t1)) s1" using fs
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>\<^isub>1  ([(y,x)]\<bullet>t2)[y::=s2]" using fs a by (auto simp add: One.eqvt)
  also have "\<dots> = t2[x::=s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>\<^isub>1 t2[x::=s2]" by simp
qed

lemma One_Var:
  assumes a: "Var x \<longrightarrow>\<^isub>1 M"
  shows "M = Var x"
using a by (cases rule: One.cases) (simp_all) 

lemma One_Lam: 
  assumes a: "Lam [x].t \<longrightarrow>\<^isub>1 s" "x\<sharp>s"
  shows "\<exists>t'. s = Lam [x].t' \<and> t \<longrightarrow>\<^isub>1 t'"
using a
by (cases rule: One.strong_cases)
   (auto simp add: lam.inject abs_fresh alpha)

lemma One_App: 
  assumes a: "App t s \<longrightarrow>\<^isub>1 r"
  shows "(\<exists>t' s'. r = App t' s' \<and> t \<longrightarrow>\<^isub>1 t' \<and> s \<longrightarrow>\<^isub>1 s') \<or> 
         (\<exists>x p p' s'. r = p'[x::=s'] \<and> t = Lam [x].p \<and> p \<longrightarrow>\<^isub>1 p' \<and> s \<longrightarrow>\<^isub>1 s' \<and> x\<sharp>(s,s'))" 
using a by (cases rule: One.cases) (auto simp add: lam.inject)

lemma One_App_: 
  assumes a: "App t s \<longrightarrow>\<^isub>1 r"
  obtains t' s' where "r = App t' s'" "t \<longrightarrow>\<^isub>1 t'" "s \<longrightarrow>\<^isub>1 s'" 
        | x p p' s' where "r = p'[x::=s']" "t = Lam [x].p" "p \<longrightarrow>\<^isub>1 p'" "s \<longrightarrow>\<^isub>1 s'" "x\<sharp>(s,s')"
using a by (cases rule: One.cases) (auto simp add: lam.inject)

lemma One_Redex: 
  assumes a: "App (Lam [x].t) s \<longrightarrow>\<^isub>1 r" "x\<sharp>(s,r)"
  shows "(\<exists>t' s'. r = App (Lam [x].t') s' \<and> t \<longrightarrow>\<^isub>1 t' \<and> s \<longrightarrow>\<^isub>1 s') \<or> 
         (\<exists>t' s'. r = t'[x::=s'] \<and> t \<longrightarrow>\<^isub>1 t' \<and> s \<longrightarrow>\<^isub>1 s')" 
using a
by (cases rule: One.strong_cases)
   (auto dest: One_Lam simp add: lam.inject abs_fresh alpha fresh_prod)

section {* Transitive Closure of One *}

inductive 
  "One_star" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>1\<^sup>* _" [80,80] 80)
where
  os1[intro]: "t \<longrightarrow>\<^isub>1\<^sup>* t"
| os2[intro]: "t \<longrightarrow>\<^isub>1 s \<Longrightarrow> t \<longrightarrow>\<^isub>1\<^sup>* s"
| os3[intro]: "\<lbrakk>t1\<longrightarrow>\<^isub>1\<^sup>* t2; t2 \<longrightarrow>\<^isub>1\<^sup>* t3\<rbrakk> \<Longrightarrow> t1 \<longrightarrow>\<^isub>1\<^sup>* t3"

section {* Complete Development Reduction *}

inductive 
  Dev :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>\<^isub>d _" [80,80]80)
where
  d1[intro]: "Var x \<longrightarrow>\<^isub>d Var x"
| d2[intro]: "t \<longrightarrow>\<^isub>d s \<Longrightarrow> Lam [x].t \<longrightarrow>\<^isub>d Lam[x].s"
| d3[intro]: "\<lbrakk>\<not>(\<exists>y t'. t1 = Lam [y].t'); t1 \<longrightarrow>\<^isub>d t2; s1 \<longrightarrow>\<^isub>d s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>\<^isub>d App t2 s2"
| d4[intro]: "\<lbrakk>x\<sharp>(s1,s2); t1 \<longrightarrow>\<^isub>d t2; s1 \<longrightarrow>\<^isub>d s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>\<^isub>d t2[x::=s2]"

equivariance Dev
nominal_inductive Dev 
  by (simp_all add: abs_fresh fresh_fact)

lemma better_d4_intro:
  assumes a: "t1 \<longrightarrow>\<^isub>d t2" "s1 \<longrightarrow>\<^isub>d s2"
  shows "App (Lam [x].t1) s1 \<longrightarrow>\<^isub>d t2[x::=s2]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,t1,s1,t2,s2)" by (rule exists_fresh, rule fin_supp,blast)
  have "App (Lam [x].t1) s1 = App (Lam [y].([(y,x)]\<bullet>t1)) s1" using fs
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>\<^isub>d  ([(y,x)]\<bullet>t2)[y::=s2]" using fs a by (auto simp add: Dev.eqvt)
  also have "\<dots> = t2[x::=s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>\<^isub>d t2[x::=s2]" by simp
qed

lemma Dev_preserves_fresh:
  fixes x::"name"
  assumes a: "M\<longrightarrow>\<^isub>d N"  
  shows "x\<sharp>M \<Longrightarrow> x\<sharp>N"
using a
by (induct) (auto simp add: abs_fresh fresh_fact)

lemma Dev_Lam:
  assumes a: "Lam [x].M \<longrightarrow>\<^isub>d N" 
  shows "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>\<^isub>d N'"
proof -
  from a have "x\<sharp>Lam [x].M" by (simp add: abs_fresh)
  with a have "x\<sharp>N" by (simp add: Dev_preserves_fresh)
  with a show "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>\<^isub>d N'"
    by (cases rule: Dev.strong_cases)
       (auto simp add: lam.inject abs_fresh alpha)
qed

lemma Development_existence:
  shows "\<exists>M'. M \<longrightarrow>\<^isub>d M'"
by (nominal_induct M rule: lam.induct)
   (auto dest!: Dev_Lam intro: better_d4_intro)

lemma Triangle:
  assumes a: "t \<longrightarrow>\<^isub>d t1" "t \<longrightarrow>\<^isub>1 t2"
  shows "t2 \<longrightarrow>\<^isub>1 t1"
using a 
proof(nominal_induct avoiding: t2 rule: Dev.strong_induct)
  case (d4 x s1 s2 t1 t1' t2) 
  have ih1: "\<And>t. t1 \<longrightarrow>\<^isub>1 t \<Longrightarrow>  t \<longrightarrow>\<^isub>1 t1'"
  and  ih2: "\<And>s. s1 \<longrightarrow>\<^isub>1 s \<Longrightarrow>  s \<longrightarrow>\<^isub>1 s2"
  and  fc: "x\<sharp>t2" "x\<sharp>s1" "x\<sharp>s2" by fact+ 
  have "App (Lam [x].t1) s1 \<longrightarrow>\<^isub>1 t2" by fact
  then obtain t' s' where "(t2 = App (Lam [x].t') s' \<and> t1 \<longrightarrow>\<^isub>1 t' \<and> s1 \<longrightarrow>\<^isub>1 s') \<or> 
                           (t2 = t'[x::=s'] \<and> t1 \<longrightarrow>\<^isub>1 t' \<and> s1 \<longrightarrow>\<^isub>1 s')"
    (* MARKUS: How does I do this better *) using fc by (auto dest!: One_Redex)
  then show "t2 \<longrightarrow>\<^isub>1 t1'[x::=s2]"
    apply -
    apply(erule disjE)
    apply(erule conjE)+
    apply(simp)
    apply(rule o4)
    using fc apply(simp)
    using ih1 apply(simp)
    using ih2 apply(simp)
    apply(erule conjE)+
    apply(simp)
    apply(rule One_subst)
    using ih1 apply(simp)
    using ih2 apply(simp)    
    done
qed (auto dest!: One_Lam One_Var One_App)

lemma Diamond_for_One:
  assumes a: "t \<longrightarrow>\<^isub>1 t1" "t \<longrightarrow>\<^isub>1 t2"
  shows "\<exists>t3. t2 \<longrightarrow>\<^isub>1 t3 \<and> t1 \<longrightarrow>\<^isub>1 t3"
proof -
  obtain tc where "t \<longrightarrow>\<^isub>d tc" using Development_existence by blast
  with a have "t2 \<longrightarrow>\<^isub>1 tc" and "t1 \<longrightarrow>\<^isub>1 tc" by (simp_all add: Triangle)
  then show "\<exists>t3. t2 \<longrightarrow>\<^isub>1 t3 \<and> t1 \<longrightarrow>\<^isub>1 t3" by blast
qed

lemma Rectangle_for_One:
  assumes a:  "t \<longrightarrow>\<^isub>1\<^sup>* t1" "t \<longrightarrow>\<^isub>1 t2" 
  shows "\<exists>t3. t1 \<longrightarrow>\<^isub>1 t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3"
using a Diamond_for_One by (induct arbitrary: t2) (blast)+

lemma CR_for_One_star: 
  assumes a: "t \<longrightarrow>\<^isub>1\<^sup>* t1" "t \<longrightarrow>\<^isub>1\<^sup>* t2"
    shows "\<exists>t3. t2 \<longrightarrow>\<^isub>1\<^sup>* t3 \<and> t1 \<longrightarrow>\<^isub>1\<^sup>* t3"
using a Rectangle_for_One by (induct arbitrary: t2) (blast)+

section {* Establishing the Equivalence of Beta-star and One-star *}

lemma Beta_Lam_cong: 
  assumes a: "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" 
  shows "Lam [x].t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* Lam [x].t2"
using a by (induct) (blast)+

lemma Beta_App_cong_aux: 
  assumes a: "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" 
  shows "App t1 s\<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s"
    and "App s t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App s t2"
using a by (induct) (blast)+

lemma Beta_App_cong: 
  assumes a: "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" "s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* s2" 
  shows "App t1 s1 \<longrightarrow>\<^isub>\<beta>\<^sup>* App t2 s2"
using a by (blast intro: Beta_App_cong_aux)

lemmas Beta_congs = Beta_Lam_cong Beta_App_cong

lemma One_implies_Beta_star: 
  assumes a: "t \<longrightarrow>\<^isub>1 s"
  shows "t \<longrightarrow>\<^isub>\<beta>\<^sup>* s"
using a by (induct) (auto intro!: Beta_congs)

lemma One_star_Lam_cong: 
  assumes a: "t1 \<longrightarrow>\<^isub>1\<^sup>* t2" 
  shows "Lam [x].t1 \<longrightarrow>\<^isub>1\<^sup>* Lam [x].t2"
using a by (induct) (auto)

lemma One_star_App_cong: 
  assumes a: "t1 \<longrightarrow>\<^isub>1\<^sup>* t2" 
  shows "App t1 s \<longrightarrow>\<^isub>1\<^sup>* App t2 s"
  and   "App s t1 \<longrightarrow>\<^isub>1\<^sup>* App s t2"
using a by (induct) (auto intro: One_refl)

lemmas One_congs = One_star_App_cong One_star_Lam_cong

lemma Beta_implies_One_star: 
  assumes a: "t1 \<longrightarrow>\<^isub>\<beta> t2" 
  shows "t1 \<longrightarrow>\<^isub>1\<^sup>* t2"
using a by (induct) (auto intro: One_refl One_congs better_o4_intro)

lemma Beta_star_equals_One_star: 
  shows "t1 \<longrightarrow>\<^isub>1\<^sup>* t2 = t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2"
proof
  assume "t1 \<longrightarrow>\<^isub>1\<^sup>* t2"
  then show "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" by (induct) (auto intro: One_implies_Beta_star)
next
  assume "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" 
  then show "t1 \<longrightarrow>\<^isub>1\<^sup>* t2" by (induct) (auto intro: Beta_implies_One_star)
qed

section {* The Church-Rosser Theorem *}

theorem CR_for_Beta_star: 
  assumes a: "t \<longrightarrow>\<^isub>\<beta>\<^sup>* t1" "t\<longrightarrow>\<^isub>\<beta>\<^sup>* t2" 
  shows "\<exists>t3. t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t3 \<and> t2 \<longrightarrow>\<^isub>\<beta>\<^sup>* t3"
proof -
  from a have "t \<longrightarrow>\<^isub>1\<^sup>* t1" and "t\<longrightarrow>\<^isub>1\<^sup>* t2" by (simp_all add: Beta_star_equals_One_star)
  then have "\<exists>t3. t1 \<longrightarrow>\<^isub>1\<^sup>* t3 \<and> t2 \<longrightarrow>\<^isub>1\<^sup>* t3" by (simp add: CR_for_One_star) 
  then show "\<exists>t3. t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t3 \<and> t2 \<longrightarrow>\<^isub>\<beta>\<^sup>* t3" by (simp add: Beta_star_equals_One_star)
qed

end
