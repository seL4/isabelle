(* $Id$ *)

theory lam_substs
imports "Iteration" 
begin


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
  by (finite_guess add: depth_Var_def depth_App_def depth_Lam_def perm_nat_def fs_name1)

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
by (simp add: subst_Lam fresh_prod a b fresh_atm)

lemma subst_Lam'':
  assumes a: "a\<sharp>b"
  and     b: "a\<sharp>t"
  shows "subst_lam b t (Lam [a].t1) = Lam [a].(subst_lam b t t1)"
by (simp add: subst_Lam fresh_prod a b)

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
apply(simp add: pt_fresh_right[OF pt_name_inst, OF at_name_inst], perm_simp add: fresh_prod fresh_atm) 
done

lemma subst_supp: 
  shows "supp(t1[a::=t2]) \<subseteq> (((supp(t1)-{a})\<union>supp(t2))::name set)"
apply(nominal_induct t1 avoiding: a t2 rule: lam.induct)
apply(auto simp add: lam.supp supp_atm fresh_prod abs_supp)
apply(blast)+
done

(* parallel substitution *)

consts
  "domain" :: "(name\<times>lam) list \<Rightarrow> (name list)"
primrec
  "domain []    = []"
  "domain (x#\<theta>) = (fst x)#(domain \<theta>)" 

consts
  "apply_sss"  :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam" (" _ < _ >" [80,80] 80)
primrec  
"(x#\<theta>)<a>  = (if (a = fst x) then (snd x) else \<theta><a>)" 


lemma apply_sss_eqvt[rule_format]:
  fixes pi::"name prm"
  shows "a\<in>set (domain \<theta>) \<longrightarrow> pi\<bullet>(\<theta><a>) = (pi\<bullet>\<theta>)<pi\<bullet>a>"
apply(induct_tac \<theta>)
apply(auto)
apply(simp add: pt_bij[OF pt_name_inst, OF at_name_inst])
done

lemma domain_eqvt[rule_format]:
  fixes pi::"name prm"
  shows "((pi\<bullet>a)\<in>set (domain \<theta>)) =  (a\<in>set (domain ((rev pi)\<bullet>\<theta>)))"
apply(induct_tac \<theta>)
apply(auto)
apply(simp_all add: pt_rev_pi[OF pt_name_inst, OF at_name_inst])
apply(simp_all add: pt_pi_rev[OF pt_name_inst, OF at_name_inst])
done

constdefs 
  psubst_Var :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam"
  "psubst_Var \<theta> \<equiv> \<lambda>a. (if a\<in>set (domain \<theta>) then \<theta><a> else (Var a))"
  
  psubst_App :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_App \<theta> \<equiv> \<lambda>r1 r2. App r1 r2"

  psubst_Lam :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_Lam \<theta> \<equiv> \<lambda>a r. Lam [a].r"

  psubst_lam :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam"
  "psubst_lam \<theta> \<equiv> itfun (psubst_Var \<theta>) (psubst_App \<theta>) (psubst_Lam \<theta>)"

lemma supports_psubst_Var:
  shows "((supp \<theta>)::name set) supports (psubst_Var \<theta>)"
  by (supports_simp add: psubst_Var_def apply_sss_eqvt domain_eqvt)

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
  shows "psubst_lam \<theta> (Var a) = (if a\<in>set (domain \<theta>) then \<theta><a> else (Var a))"
apply(simp add: psubst_lam_def)
apply(auto simp add: itfun_Var[OF fin_supp_psubst, OF fresh_psubst_Lam])
apply(auto simp add: psubst_Var_def)
done

lemma psubst_App:
  shows "psubst_lam \<theta> (App t1 t2) = App (psubst_lam \<theta> t1) (psubst_lam \<theta> t2)"
apply(simp add: psubst_lam_def)
apply(auto simp add: itfun_App[OF fin_supp_psubst, OF fresh_psubst_Lam])
apply(auto simp add: psubst_App_def)
done

lemma psubst_Lam:
  assumes a: "a\<sharp>\<theta>"
  shows "psubst_lam \<theta> (Lam [a].t1) = Lam [a].(psubst_lam \<theta> t1)"
using a
apply(simp add: psubst_lam_def)
apply(subgoal_tac "a\<sharp>(psubst_Var \<theta>,psubst_App \<theta>,psubst_Lam \<theta>)")
apply(auto simp add: itfun_Lam[OF fin_supp_psubst, OF fresh_psubst_Lam])
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