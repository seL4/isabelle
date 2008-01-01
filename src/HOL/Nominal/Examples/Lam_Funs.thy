(* $Id$ *)

theory Lam_Funs
  imports "../Nominal"
begin

text {* Defines some functions over lambda-terms *}

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {* Depth of a lambda-term *}

consts 
  depth :: "lam \<Rightarrow> nat"

nominal_primrec
  "depth (Var x) = (1::nat)"
  "depth (App t1 t2) = (max (depth t1) (depth t2)) + 1"
  "depth (Lam [a].t) = (depth t) + (1::nat)"
  apply(finite_guess)+
  apply(rule TrueI)+
  apply(simp add: fresh_nat)
  apply(fresh_guess)+
  done

text {* 
  Free variables of a lambda-term. The complication of this
  function is the fact that it returns a name set, which is
  not automatically a finitely supported type. So we have to
  prove the invariant that frees always returns a finite set
  of names. 
*}

consts 
  frees :: "lam \<Rightarrow> name set"

nominal_primrec (invariant: "\<lambda>s::name set. finite s")
  "frees (Var a) = {a}"
  "frees (App t1 t2) = (frees t1) \<union> (frees t2)"
  "frees (Lam [a].t) = (frees t) - {a}"
apply(finite_guess)+
apply(simp)+ 
apply(simp add: fresh_def)
apply(simp add: supp_of_fin_sets[OF pt_name_inst, OF at_name_inst, OF fs_at_inst[OF at_name_inst]])
apply(simp add: supp_atm)
apply(force)
apply(fresh_guess)+
done

lemma frees_equals_support:
  shows "frees t = supp t"
by (nominal_induct t rule: lam.induct)
   (simp_all add: lam.supp supp_atm abs_supp)

text {* Capture-avoiding substitution *}

consts
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [100,100,100] 100)

nominal_primrec
  "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

lemma subst_eqvt[eqvt]:
  fixes pi:: "name prm"
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

text{* Parallel substitution *}

consts
 psubst :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam" ("_<_>" [100,100] 900)

fun
  lookup :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam"   
where
  "lookup [] x        = Var x"
| "lookup ((y,T)#\<theta>) x = (if x=y then T else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(lookup \<theta> x) = lookup (pi\<bullet>\<theta>) (pi\<bullet>x)"
by (induct \<theta>) (auto simp add: perm_bij)

lemma lookup_fresh:
  fixes z::"name"
  assumes "z\<sharp>\<theta>" "z\<sharp>x"
  shows "z\<sharp> lookup \<theta> x"
using assms 
by (induct rule: lookup.induct) (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using assms 
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

nominal_primrec
  "\<theta><(Var x)> = (lookup \<theta> x)"
  "\<theta><(App t1 t2)> = App (\<theta><t1>) (\<theta><t2>)"
  "x\<sharp>\<theta>\<Longrightarrow>\<theta><(Lam [x].t)> = Lam [x].(\<theta><t>)"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

end
