(* $Id$ *)

theory Lam_Funs
imports Nominal
begin

atom_decl name

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)


constdefs 
  depth_Var :: "name \<Rightarrow> nat"
  "depth_Var \<equiv> \<lambda>(a::name). 1"
  
  depth_App :: "lam \<Rightarrow> lam \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  "depth_App \<equiv> \<lambda>_ _ n1 n2. (max n1 n2)+1"

  depth_Lam :: "name \<Rightarrow> lam \<Rightarrow> nat \<Rightarrow> nat"
  "depth_Lam \<equiv> \<lambda>_ _ n. n+1"

  depth_lam :: "lam \<Rightarrow> nat"
  "depth_lam t \<equiv> (lam_rec depth_Var depth_App depth_Lam) t"

lemma fin_supp_depth_lam:
  shows "finite ((supp depth_Var)::name set)"
  and   "finite ((supp depth_Lam)::name set)"
  and   "finite ((supp depth_App)::name set)"
  by (finite_guess add: depth_Var_def depth_Lam_def depth_App_def perm_nat_def)+

lemma fcb_depth_lam:
  fixes a::"name"
  shows "a\<sharp>(depth_Lam a t n)"
  by (simp add: fresh_nat)

lemma depth_lam:
  shows "depth_lam (Var a)     = 1"
  and   "depth_lam (App t1 t2) = (max (depth_lam t1) (depth_lam t2))+1"
  and   "depth_lam (Lam [a].t) = (depth_lam t)+1"
apply -
apply(unfold depth_lam_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp_all add: fin_supp_depth_lam supp_unit)
apply(simp add: fcb_depth_lam)
apply(simp add: depth_Var_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp_all add: fin_supp_depth_lam supp_unit)
apply(simp add: fcb_depth_lam)
apply(simp add: depth_App_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp_all add: fin_supp_depth_lam supp_unit)
apply(simp add: fcb_depth_lam)
apply(simp add: depth_Var_def, fresh_guess add: perm_nat_def)
apply(simp add: depth_App_def, fresh_guess add: perm_nat_def)
apply(simp add: depth_Lam_def, fresh_guess add: perm_nat_def)
apply(simp add: depth_Lam_def)
done

text {* capture-avoiding substitution *}
constdefs 
  subst_Var :: "name \<Rightarrow>lam \<Rightarrow> name \<Rightarrow> lam"
  "subst_Var b t \<equiv> \<lambda>a. (if a=b then t else (Var a))"
  
  subst_App :: "name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_App b t \<equiv> \<lambda>_ _ r1 r2. App r1 r2"

  subst_Lam :: "name \<Rightarrow> lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "subst_Lam b t \<equiv> \<lambda>a _ r. Lam [a].r"

abbreviation
  subst_syn  :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [100,100,100] 900) where
  "t'[b::=t] \<equiv> (lam_rec (subst_Var b t) (subst_App b t) (subst_Lam b t)) t'"

(* FIXME: this lemma needs to be in Nominal.thy *)
lemma eq_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
  apply(simp add: perm_bool perm_bij)
  done

lemma fin_supp_subst:
  shows "finite ((supp (subst_Var b t))::name set)"
  and   "finite ((supp (subst_Lam b t))::name set)"
  and   "finite ((supp (subst_App b t))::name set)"
apply -
apply(finite_guess add: subst_Var_def perm_if eq_eqvt fs_name1)
apply(finite_guess add: subst_Lam_def fs_name1)
apply(finite_guess add: subst_App_def fs_name1)
done

lemma fcb_subst:
  fixes a::"name"
  shows "a\<sharp>(subst_Lam b t) a t' r"
  by (simp add: subst_Lam_def abs_fresh)

lemma subst[simp]:
  shows "(Var a)[b::=t] = (if a=b then t else (Var a))"
  and   "(App t1 t2)[b::=t] = App (t1[b::=t]) (t2[b::=t])"
  and   "a\<sharp>(b,t)    \<Longrightarrow> (Lam [a].t1)[b::=t] = Lam [a].(t1[b::=t])"
  and   "\<lbrakk>a\<noteq>b; a\<sharp>t\<rbrakk> \<Longrightarrow> (Lam [a].t1)[b::=t] = Lam [a].(t1[b::=t])"
  and   "\<lbrakk>a\<sharp>b; a\<sharp>t\<rbrakk> \<Longrightarrow> (Lam [a].t1)[b::=t] = Lam [a].(t1[b::=t])"
apply -
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp add: fs_name1 fin_supp_subst)+
apply(simp add: fcb_subst)
apply(simp add: subst_Var_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp add: fs_name1 fin_supp_subst)+
apply(simp add: fcb_subst)
apply(simp add: subst_App_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp add: fs_name1 fin_supp_subst)+
apply(simp add: fcb_subst)
apply(fresh_guess add: subst_Var_def perm_if eq_eqvt fs_name1)
apply(fresh_guess add: subst_App_def fs_name1)
apply(fresh_guess add: subst_Lam_def fs_name1)
apply(simp add: subst_Lam_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp add: fs_name1 fin_supp_subst)+
apply(simp add: fcb_subst)
apply(fresh_guess add: subst_Var_def perm_if eq_eqvt fs_name1 fresh_atm)
apply(fresh_guess add: subst_App_def fs_name1 fresh_atm)
apply(fresh_guess add: subst_Lam_def fs_name1 fresh_atm)
apply(simp add: subst_Lam_def)
apply(rule trans)
apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
apply(simp add: fs_name1 fin_supp_subst)+
apply(simp add: fcb_subst)
apply(fresh_guess add: subst_Var_def perm_if eq_eqvt fs_name1)
apply(fresh_guess add: subst_App_def fs_name1)
apply(fresh_guess add: subst_Lam_def fs_name1)
apply(simp add: subst_Lam_def)
done

lemma subst_eqvt[simp]:
  fixes pi:: "name prm"
  and   t1:: "lam"
  and   t2:: "lam"
  and   a :: "name"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
apply(nominal_induct t1 avoiding: b t2 rule: lam.induct)
apply(auto simp add: perm_bij fresh_prod fresh_atm fresh_bij)
done

lemma subst_supp: 
  shows "supp(t1[a::=t2]) \<subseteq> (((supp(t1)-{a})\<union>supp(t2))::name set)"
apply(nominal_induct t1 avoiding: a t2 rule: lam.induct)
apply(auto simp add: lam.supp supp_atm fresh_prod abs_supp)
apply(blast)+
done

(* parallel substitution *)

(* simultaneous substitution *)
consts
  "domain" :: "(name\<times>lam) list \<Rightarrow> (name list)"
primrec
  "domain []    = []"
  "domain (x#\<theta>) = (fst x)#(domain \<theta>)" 

consts
  "apply_sss"  :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam" (" _ < _ >" [80,80] 80)
primrec  
"(x#\<theta>)<a>  = (if (a = fst x) then (snd x) else \<theta><a>)" 

lemma apply_sss_eqvt:
  fixes pi::"name prm"
  assumes a: "a\<in>set (domain \<theta>)"
  shows "pi\<bullet>(\<theta><a>) = (pi\<bullet>\<theta>)<pi\<bullet>a>"
using a
by (induct \<theta>)
   (auto simp add: perm_bij)

lemma domain_eqvt:
  fixes pi::"name prm"
  shows "((pi\<bullet>a)\<in>set (domain \<theta>)) = (a\<in>set (domain ((rev pi)\<bullet>\<theta>)))"
apply(induct \<theta>)
apply(auto)
apply(perm_simp)+
done

constdefs 
  psubst_Var :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam"
  "psubst_Var \<theta> \<equiv> \<lambda>a. (if a\<in>set (domain \<theta>) then \<theta><a> else (Var a))"
  
  psubst_App :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_App \<theta> \<equiv> \<lambda>_ _ r1 r2. App r1 r2"

  psubst_Lam :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_Lam \<theta> \<equiv> \<lambda>a _ r. Lam [a].r"

abbreviation
  psubst_lam :: "lam \<Rightarrow> (name\<times>lam) list \<Rightarrow> lam" ("_[<_>]" [100,100] 900) where
  "t[<\<theta>>] \<equiv> (lam_rec (psubst_Var \<theta>) (psubst_App \<theta>) (psubst_Lam \<theta>)) t"

lemma fin_supp_psubst:
  shows "finite ((supp (psubst_Var \<theta>))::name set)"
  and   "finite ((supp (psubst_Lam \<theta>))::name set)"
  and   "finite ((supp (psubst_App \<theta>))::name set)"
  apply -
  apply(finite_guess add: fs_name1 psubst_Var_def domain_eqvt apply_sss_eqvt)
  apply(finite_guess add: fs_name1 psubst_Lam_def)
  apply(finite_guess add: fs_name1 psubst_App_def)
done

lemma fcb_psubst_Lam:
  shows "x\<sharp>(psubst_Lam \<theta>) x t r"
  by (simp add: psubst_Lam_def abs_fresh)

lemma psubst[simp]:
  shows "(Var a)[<\<theta>>] = (if a\<in>set (domain \<theta>) then \<theta><a> else (Var a))"
  and   "(App t1 t2)[<\<theta>>] = App (t1[<\<theta>>]) (t2[<\<theta>>])"
  and   "a\<sharp>\<theta> \<Longrightarrow> (Lam [a].t1)[<\<theta>>] = Lam [a].(t1[<\<theta>>])"
  apply(rule trans)
  apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
  apply(simp add: fin_supp_psubst fs_name1)+
  apply(simp add: fcb_psubst_Lam)
  apply(simp add: psubst_Var_def)
  apply(rule trans)
  apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
  apply(simp add: fin_supp_psubst fs_name1)+
  apply(simp add: fcb_psubst_Lam)
  apply(simp add: psubst_App_def)
  apply(rule trans)
  apply(rule lam.recs[where P="\<lambda>_. True" and z="()", simplified])
  apply(simp add: fin_supp_psubst fs_name1)+
  apply(simp add: fcb_psubst_Lam)
  apply(fresh_guess add: psubst_Var_def domain_eqvt apply_sss_eqvt fs_name1)
  apply(fresh_guess add: psubst_App_def fs_name1)
  apply(fresh_guess add: psubst_Lam_def fs_name1)
  apply(simp add: psubst_Lam_def)
done

end
