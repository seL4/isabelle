(*                                                        *)
(* Formalisation of some typical SOS-proofs.              *)
(*                                                        *) 
(* This work was inspired by challenge suggested by Adam  *)
(* Chlipala on the POPLmark mailing list.                 *)
(*                                                        *) 
(* We thank Nick Benton for helping us with the           *) 
(* termination-proof for evaluation.                      *)
(*                                                        *)
(* The formalisation was done by Julien Narboux and       *)
(* Christian Urban.                                       *)

theory SOS
  imports "Nominal"
begin

atom_decl name

text {* types and terms *}
nominal_datatype ty = 
    TVar "nat"
  | Arrow "ty" "ty" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype trm = 
    Var "name"
  | Lam "\<guillemotleft>name\<guillemotright>trm" ("Lam [_]._" [100,100] 100)
  | App "trm" "trm"

lemma fresh_ty:
  fixes x::"name" 
  and   T::"ty"
  shows "x\<sharp>T"
by (induct T rule: ty.induct)
   (auto simp add: fresh_nat)

text {* Parallel and single substitution. *}
fun
  lookup :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm"   
where
  "lookup [] x        = Var x"
| "lookup ((y,e)#\<theta>) x = (if x=y then e else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>) (auto simp add: eqvts)

lemma lookup_fresh:
  fixes z::"name"
  assumes a: "z\<sharp>\<theta>" and b: "z\<sharp>x"
  shows "z \<sharp>lookup \<theta> x"
using a b
by (induct rule: lookup.induct) (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using assms 
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

(* parallel substitution *)

nominal_primrec
  psubst :: "(name\<times>trm) list \<Rightarrow> trm \<Rightarrow> trm"  ("_<_>" [95,95] 105)
where
  "\<theta><(Var x)> = (lookup \<theta> x)"
| "\<theta><(App e\<^isub>1 e\<^isub>2)> = App (\<theta><e\<^isub>1>) (\<theta><e\<^isub>2>)"
| "x\<sharp>\<theta> \<Longrightarrow> \<theta><(Lam [x].e)> = Lam [x].(\<theta><e>)"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess)+
done

lemma psubst_eqvt[eqvt]:
  fixes pi::"name prm" 
  and   t::"trm"
  shows "pi\<bullet>(\<theta><t>) = (pi\<bullet>\<theta>)<(pi\<bullet>t)>"
by (nominal_induct t avoiding: \<theta> rule: trm.strong_induct)
   (perm_simp add: fresh_bij lookup_eqvt)+

lemma fresh_psubst: 
  fixes z::"name"
  and   t::"trm"
  assumes "z\<sharp>t" and "z\<sharp>\<theta>"
  shows "z\<sharp>(\<theta><t>)"
using assms
by (nominal_induct t avoiding: z \<theta> t rule: trm.strong_induct)
   (auto simp add: abs_fresh lookup_fresh)

lemma psubst_empty[simp]:
  shows "[]<t> = t"
  by (nominal_induct t rule: trm.strong_induct) 
     (auto simp add: fresh_list_nil)

text {* Single substitution *}
abbreviation 
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)
where 
  "t[x::=t']  \<equiv> ([(x,t')])<t>" 

lemma subst[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t\<^isub>1 t\<^isub>2)[y::=t'] = App (t\<^isub>1[y::=t']) (t\<^isub>2[y::=t'])"
  and   "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
by (simp_all add: fresh_list_cons fresh_list_nil)

lemma fresh_subst:
  fixes z::"name"
  shows "\<lbrakk>z\<sharp>s; (z=y \<or> z\<sharp>t)\<rbrakk> \<Longrightarrow> z\<sharp>t[y::=s]"
by (nominal_induct t avoiding: z y s rule: trm.strong_induct)
   (auto simp add: abs_fresh fresh_prod fresh_atm)

lemma forget: 
  assumes a: "x\<sharp>e" 
  shows "e[x::=e'] = e"
using a
by (nominal_induct e avoiding: x e' rule: trm.strong_induct)
   (auto simp add: fresh_atm abs_fresh)

lemma psubst_subst_psubst:
  assumes h: "x\<sharp>\<theta>"
  shows "\<theta><e>[x::=e'] = ((x,e')#\<theta>)<e>"
  using h
by (nominal_induct e avoiding: \<theta> x e' rule: trm.strong_induct)
   (auto simp add: fresh_list_cons fresh_atm forget lookup_fresh lookup_fresh')

text {* Typing Judgements *}

inductive
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
  v_nil[intro]:  "valid []"
| v_cons[intro]: "\<lbrakk>valid \<Gamma>;x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> valid ((x,T)#\<Gamma>)"

equivariance valid 

inductive_cases
  valid_elim[elim]: "valid ((x,T)#\<Gamma>)"

lemma valid_insert:
  assumes a: "valid (\<Delta>@[(x,T)]@\<Gamma>)"
  shows "valid (\<Delta> @ \<Gamma>)" 
using a
by (induct \<Delta>)
   (auto simp add:  fresh_list_append fresh_list_cons elim!: valid_elim)

lemma fresh_set: 
  shows "y\<sharp>xs = (\<forall>x\<in>set xs. y\<sharp>x)"
by (induct xs) (simp_all add: fresh_list_nil fresh_list_cons)

lemma context_unique:
  assumes a1: "valid \<Gamma>"
  and     a2: "(x,T) \<in> set \<Gamma>"
  and     a3: "(x,U) \<in> set \<Gamma>"
  shows "T = U" 
using a1 a2 a3
by (induct) (auto simp add: fresh_set fresh_prod fresh_atm)

text {* Typing Relation *}

inductive
  typing :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60) 
where
  t_Var[intro]:   "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| t_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e\<^isub>1 : T\<^isub>1\<rightarrow>T\<^isub>2; \<Gamma> \<turnstile> e\<^isub>2 : T\<^isub>1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T\<^isub>2"
| t_Lam[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T\<^isub>1)#\<Gamma> \<turnstile> e : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].e : T\<^isub>1\<rightarrow>T\<^isub>2"

equivariance typing

nominal_inductive typing
  by (simp_all add: abs_fresh fresh_ty)

lemma typing_implies_valid:
  assumes a: "\<Gamma> \<turnstile> t : T"
  shows "valid \<Gamma>"
using a by (induct) (auto)


lemma t_App_elim:
  assumes a: "\<Gamma> \<turnstile> App t1 t2 : T"
  obtains T' where "\<Gamma> \<turnstile> t1 : T' \<rightarrow> T" and "\<Gamma> \<turnstile> t2 : T'"
using a
by (cases) (auto simp add: trm.inject)

lemma t_Lam_elim: 
  assumes a: "\<Gamma> \<turnstile> Lam [x].t : T" "x\<sharp>\<Gamma>"
  obtains T\<^isub>1 and T\<^isub>2 where "(x,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2" and "T=T\<^isub>1\<rightarrow>T\<^isub>2"
using a
by (cases rule: typing.strong_cases [where x="x"])
   (auto simp add: abs_fresh fresh_ty alpha trm.inject)

abbreviation
  "sub_context" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ \<subseteq> _" [55,55] 55)
where
  "\<Gamma>\<^isub>1 \<subseteq> \<Gamma>\<^isub>2 \<equiv> \<forall>x T. (x,T)\<in>set \<Gamma>\<^isub>1 \<longrightarrow> (x,T)\<in>set \<Gamma>\<^isub>2"

lemma weakening: 
  fixes \<Gamma>\<^isub>1 \<Gamma>\<^isub>2::"(name\<times>ty) list"
  assumes "\<Gamma>\<^isub>1 \<turnstile> e: T" and "valid \<Gamma>\<^isub>2" and "\<Gamma>\<^isub>1 \<subseteq> \<Gamma>\<^isub>2"
  shows "\<Gamma>\<^isub>2 \<turnstile> e: T"
  using assms
proof(nominal_induct \<Gamma>\<^isub>1 e T avoiding: \<Gamma>\<^isub>2 rule: typing.strong_induct)
  case (t_Lam x \<Gamma>\<^isub>1 T\<^isub>1 t T\<^isub>2 \<Gamma>\<^isub>2)
  have vc: "x\<sharp>\<Gamma>\<^isub>2" by fact
  have ih: "\<lbrakk>valid ((x,T\<^isub>1)#\<Gamma>\<^isub>2); (x,T\<^isub>1)#\<Gamma>\<^isub>1 \<subseteq> (x,T\<^isub>1)#\<Gamma>\<^isub>2\<rbrakk> \<Longrightarrow> (x,T\<^isub>1)#\<Gamma>\<^isub>2 \<turnstile> t : T\<^isub>2" by fact
  have "valid \<Gamma>\<^isub>2" by fact
  then have "valid ((x,T\<^isub>1)#\<Gamma>\<^isub>2)" using vc by auto
  moreover
  have "\<Gamma>\<^isub>1 \<subseteq> \<Gamma>\<^isub>2" by fact
  then have "(x,T\<^isub>1)#\<Gamma>\<^isub>1 \<subseteq> (x,T\<^isub>1)#\<Gamma>\<^isub>2" by simp
  ultimately have "(x,T\<^isub>1)#\<Gamma>\<^isub>2 \<turnstile> t : T\<^isub>2" using ih by simp 
  with vc show "\<Gamma>\<^isub>2 \<turnstile> Lam [x].t : T\<^isub>1\<rightarrow>T\<^isub>2" by auto
qed (auto)

lemma type_substitutivity_aux:
  assumes a: "(\<Delta>@[(x,T')]@\<Gamma>) \<turnstile> e : T"
  and     b: "\<Gamma> \<turnstile> e' : T'"
  shows "(\<Delta>@\<Gamma>) \<turnstile> e[x::=e'] : T" 
using a b 
proof (nominal_induct \<Gamma>\<equiv>"\<Delta>@[(x,T')]@\<Gamma>" e T avoiding: e' \<Delta> rule: typing.strong_induct)
  case (t_Var y T e' \<Delta>)
  then have a1: "valid (\<Delta>@[(x,T')]@\<Gamma>)" 
       and  a2: "(y,T) \<in> set (\<Delta>@[(x,T')]@\<Gamma>)" 
       and  a3: "\<Gamma> \<turnstile> e' : T'" .
  from a1 have a4: "valid (\<Delta>@\<Gamma>)" by (rule valid_insert)
  { assume eq: "x=y"
    from a1 a2 have "T=T'" using eq by (auto intro: context_unique)
    with a3 have "\<Delta>@\<Gamma> \<turnstile> Var y[x::=e'] : T" using eq a4 by (auto intro: weakening)
  }
  moreover
  { assume ineq: "x\<noteq>y"
    from a2 have "(y,T) \<in> set (\<Delta>@\<Gamma>)" using ineq by simp
    then have "\<Delta>@\<Gamma> \<turnstile> Var y[x::=e'] : T" using ineq a4 by auto
  }
  ultimately show "\<Delta>@\<Gamma> \<turnstile> Var y[x::=e'] : T" by blast
qed (force simp add: fresh_list_append fresh_list_cons)+

corollary type_substitutivity:
  assumes a: "(x,T')#\<Gamma> \<turnstile> e : T"
  and     b: "\<Gamma> \<turnstile> e' : T'"
  shows "\<Gamma> \<turnstile> e[x::=e'] : T"
using a b type_substitutivity_aux[where \<Delta>="[]"]
by (auto)

text {* Values *}
inductive
  val :: "trm\<Rightarrow>bool" 
where
  v_Lam[intro]:   "val (Lam [x].e)"

equivariance val 

lemma not_val_App[simp]:
  shows 
  "\<not> val (App e\<^isub>1 e\<^isub>2)" 
  "\<not> val (Var x)"
  by (auto elim: val.cases)

text {* Big-Step Evaluation *}

inductive
  big :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<Down> _" [80,80] 80) 
where
  b_Lam[intro]:   "Lam [x].e \<Down> Lam [x].e"
| b_App[intro]:   "\<lbrakk>x\<sharp>(e\<^isub>1,e\<^isub>2,e'); e\<^isub>1\<Down>Lam [x].e; e\<^isub>2\<Down>e\<^isub>2'; e[x::=e\<^isub>2']\<Down>e'\<rbrakk> \<Longrightarrow> App e\<^isub>1 e\<^isub>2 \<Down> e'"

equivariance big

nominal_inductive big
  by (simp_all add: abs_fresh)

lemma big_preserves_fresh:
  fixes x::"name"
  assumes a: "e \<Down> e'" "x\<sharp>e" 
  shows "x\<sharp>e'"
  using a by (induct) (auto simp add: abs_fresh fresh_subst)

lemma b_App_elim:
  assumes a: "App e\<^isub>1 e\<^isub>2 \<Down> e'" "x\<sharp>(e\<^isub>1,e\<^isub>2,e')"
  obtains f\<^isub>1 and f\<^isub>2 where "e\<^isub>1 \<Down> Lam [x]. f\<^isub>1" "e\<^isub>2 \<Down> f\<^isub>2" "f\<^isub>1[x::=f\<^isub>2] \<Down> e'"
  using a
by (cases rule: big.strong_cases[where x="x" and xa="x"])
   (auto simp add: trm.inject)

lemma subject_reduction:
  assumes a: "e \<Down> e'" and b: "\<Gamma> \<turnstile> e : T"
  shows "\<Gamma> \<turnstile> e' : T"
  using a b
proof (nominal_induct avoiding: \<Gamma> arbitrary: T rule: big.strong_induct) 
  case (b_App x e\<^isub>1 e\<^isub>2 e' e e\<^isub>2' \<Gamma> T)
  have vc: "x\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T" by fact
  then obtain T' where a1: "\<Gamma> \<turnstile> e\<^isub>1 : T'\<rightarrow>T" and a2: "\<Gamma> \<turnstile> e\<^isub>2 : T'" 
    by (cases) (auto simp add: trm.inject)
  have ih1: "\<Gamma> \<turnstile> e\<^isub>1 : T' \<rightarrow> T \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].e : T' \<rightarrow> T" by fact
  have ih2: "\<Gamma> \<turnstile> e\<^isub>2 : T' \<Longrightarrow> \<Gamma> \<turnstile> e\<^isub>2' : T'" by fact 
  have ih3: "\<Gamma> \<turnstile> e[x::=e\<^isub>2'] : T \<Longrightarrow> \<Gamma> \<turnstile> e' : T" by fact
  have "\<Gamma> \<turnstile> Lam [x].e : T'\<rightarrow>T" using ih1 a1 by simp 
  then have "((x,T')#\<Gamma>) \<turnstile> e : T" using vc  
    by (auto elim: t_Lam_elim simp add: ty.inject)
  moreover
  have "\<Gamma> \<turnstile> e\<^isub>2': T'" using ih2 a2 by simp
  ultimately have "\<Gamma> \<turnstile> e[x::=e\<^isub>2'] : T" by (simp add: type_substitutivity)
  thus "\<Gamma> \<turnstile> e' : T" using ih3 by simp
qed (blast)

lemma subject_reduction2:
  assumes a: "e \<Down> e'" and b: "\<Gamma> \<turnstile> e : T"
  shows "\<Gamma> \<turnstile> e' : T"
  using a b
by (nominal_induct avoiding: \<Gamma> T rule: big.strong_induct)
   (force elim: t_App_elim t_Lam_elim simp add: ty.inject type_substitutivity)+

lemma unicity_of_evaluation:
  assumes a: "e \<Down> e\<^isub>1" 
  and     b: "e \<Down> e\<^isub>2"
  shows "e\<^isub>1 = e\<^isub>2"
  using a b
proof (nominal_induct e e\<^isub>1 avoiding: e\<^isub>2 rule: big.strong_induct)
  case (b_Lam x e t\<^isub>2)
  have "Lam [x].e \<Down> t\<^isub>2" by fact
  thus "Lam [x].e = t\<^isub>2" by cases (simp_all add: trm.inject)
next
  case (b_App x e\<^isub>1 e\<^isub>2 e' e\<^isub>1' e\<^isub>2' t\<^isub>2)
  have ih1: "\<And>t. e\<^isub>1 \<Down> t \<Longrightarrow> Lam [x].e\<^isub>1' = t" by fact
  have ih2:"\<And>t. e\<^isub>2 \<Down> t \<Longrightarrow> e\<^isub>2' = t" by fact
  have ih3: "\<And>t. e\<^isub>1'[x::=e\<^isub>2'] \<Down> t \<Longrightarrow> e' = t" by fact
  have app: "App e\<^isub>1 e\<^isub>2 \<Down> t\<^isub>2" by fact
  have vc: "x\<sharp>e\<^isub>1" "x\<sharp>e\<^isub>2" "x\<sharp>t\<^isub>2" by fact+
  then have "x\<sharp>App e\<^isub>1 e\<^isub>2" by auto
  from app vc obtain f\<^isub>1 f\<^isub>2 where x1: "e\<^isub>1 \<Down> Lam [x]. f\<^isub>1" and x2: "e\<^isub>2 \<Down> f\<^isub>2" and x3: "f\<^isub>1[x::=f\<^isub>2] \<Down> t\<^isub>2"
    by (auto elim!: b_App_elim)
  then have "Lam [x]. f\<^isub>1 = Lam [x]. e\<^isub>1'" using ih1 by simp
  then 
  have "f\<^isub>1 = e\<^isub>1'" by (auto simp add: trm.inject alpha) 
  moreover 
  have "f\<^isub>2 = e\<^isub>2'" using x2 ih2 by simp
  ultimately have "e\<^isub>1'[x::=e\<^isub>2'] \<Down> t\<^isub>2" using x3 by simp
  thus "e' = t\<^isub>2" using ih3 by simp
qed

lemma reduces_evaluates_to_values:
  assumes h: "t \<Down> t'"
  shows "val t'"
using h by (induct) (auto)

(* Valuation *)

nominal_primrec
  V :: "ty \<Rightarrow> trm set" 
where
  "V (TVar x) = {e. val e}"
| "V (T\<^isub>1 \<rightarrow> T\<^isub>2) = {Lam [x].e | x e. \<forall> v \<in> (V T\<^isub>1). \<exists> v'. e[x::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2}"
  by (rule TrueI)+ 

lemma V_eqvt:
  fixes pi::"name prm"
  assumes a: "x\<in>V T"
  shows "(pi\<bullet>x)\<in>V T"
using a
apply(nominal_induct T arbitrary: pi x rule: ty.strong_induct)
apply(auto simp add: trm.inject)
apply(simp add: eqvts)
apply(rule_tac x="pi\<bullet>xa" in exI)
apply(rule_tac x="pi\<bullet>e" in exI)
apply(simp)
apply(auto)
apply(drule_tac x="(rev pi)\<bullet>v" in bspec)
apply(force)
apply(auto)
apply(rule_tac x="pi\<bullet>v'" in exI)
apply(auto)
apply(drule_tac pi="pi" in big.eqvt)
apply(perm_simp add: eqvts)
done

lemma V_arrow_elim_weak:
  assumes h:"u \<in> V (T\<^isub>1 \<rightarrow> T\<^isub>2)"
  obtains a t where "u = Lam [a].t" and "\<forall> v \<in> (V T\<^isub>1). \<exists> v'. t[a::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2"
using h by (auto)

lemma V_arrow_elim_strong:
  fixes c::"'a::fs_name"
  assumes h: "u \<in> V (T\<^isub>1 \<rightarrow> T\<^isub>2)"
  obtains a t where "a\<sharp>c" "u = Lam [a].t" "\<forall>v \<in> (V T\<^isub>1). \<exists> v'. t[a::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2"
using h
apply -
apply(erule V_arrow_elim_weak)
apply(subgoal_tac "\<exists>a'::name. a'\<sharp>(a,t,c)") (*A*)
apply(erule exE)
apply(drule_tac x="a'" in meta_spec)
apply(drule_tac x="[(a,a')]\<bullet>t" in meta_spec)
apply(drule meta_mp)
apply(simp)
apply(drule meta_mp)
apply(simp add: trm.inject alpha fresh_left fresh_prod calc_atm fresh_atm)
apply(perm_simp)
apply(force)
apply(drule meta_mp)
apply(rule ballI)
apply(drule_tac x="[(a,a')]\<bullet>v" in bspec)
apply(simp add: V_eqvt)
apply(auto)
apply(rule_tac x="[(a,a')]\<bullet>v'" in exI)
apply(auto)
apply(drule_tac pi="[(a,a')]" in big.eqvt)
apply(perm_simp add: eqvts calc_atm)
apply(simp add: V_eqvt)
(*A*)
apply(rule exists_fresh')
apply(simp add: fin_supp)
done

lemma Vs_are_values:
  assumes a: "e \<in> V T"
  shows "val e"
using a by (nominal_induct T arbitrary: e rule: ty.strong_induct) (auto)

lemma values_reduce_to_themselves:
  assumes a: "val v"
  shows "v \<Down> v"
using a by (induct) (auto)

lemma Vs_reduce_to_themselves:
  assumes a: "v \<in> V T"
  shows "v \<Down> v"
using a by (simp add: values_reduce_to_themselves Vs_are_values)

text {* '\<theta> maps x to e' asserts that \<theta> substitutes x with e *}
abbreviation 
  mapsto :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> bool" ("_ maps _ to _" [55,55,55] 55) 
where
 "\<theta> maps x to e \<equiv> (lookup \<theta> x) = e"

abbreviation 
  v_closes :: "(name\<times>trm) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ Vcloses _" [55,55] 55) 
where
  "\<theta> Vcloses \<Gamma> \<equiv> \<forall>x T. (x,T) \<in> set \<Gamma> \<longrightarrow> (\<exists>v. \<theta> maps x to v \<and> v \<in> V T)"

lemma case_distinction_on_context:
  fixes \<Gamma>::"(name\<times>ty) list"
  assumes asm1: "valid ((m,t)#\<Gamma>)" 
  and     asm2: "(n,U) \<in> set ((m,T)#\<Gamma>)"
  shows "(n,U) = (m,T) \<or> ((n,U) \<in> set \<Gamma> \<and> n \<noteq> m)"
proof -
  from asm2 have "(n,U) \<in> set [(m,T)] \<or> (n,U) \<in> set \<Gamma>" by auto
  moreover
  { assume eq: "m=n"
    assume "(n,U) \<in> set \<Gamma>" 
    then have "\<not> n\<sharp>\<Gamma>" 
      by (induct \<Gamma>) (auto simp add: fresh_list_cons fresh_prod fresh_atm)
    moreover have "m\<sharp>\<Gamma>" using asm1 by auto
    ultimately have False using eq by auto
  }
  ultimately show ?thesis by auto
qed

lemma monotonicity:
  fixes m::"name"
  fixes \<theta>::"(name \<times> trm) list" 
  assumes h1: "\<theta> Vcloses \<Gamma>"
  and     h2: "e \<in> V T" 
  and     h3: "valid ((x,T)#\<Gamma>)"
  shows "(x,e)#\<theta> Vcloses (x,T)#\<Gamma>"
proof(intro strip)
  fix x' T'
  assume "(x',T') \<in> set ((x,T)#\<Gamma>)"
  then have "((x',T')=(x,T)) \<or> ((x',T')\<in>set \<Gamma> \<and> x'\<noteq>x)" using h3 
    by (rule_tac case_distinction_on_context)
  moreover
  { (* first case *)
    assume "(x',T') = (x,T)"
    then have "\<exists>e'. ((x,e)#\<theta>) maps x to e' \<and> e' \<in> V T'" using h2 by auto
  }
  moreover
  { (* second case *)
    assume "(x',T') \<in> set \<Gamma>" and neq:"x' \<noteq> x"
      then have "\<exists>e'. \<theta> maps x' to e' \<and> e' \<in> V T'" using h1 by auto
      then have "\<exists>e'. ((x,e)#\<theta>) maps x' to e' \<and> e' \<in> V T'" using neq by auto
  }
  ultimately show "\<exists>e'.  ((x,e)#\<theta>) maps x' to e'  \<and> e' \<in> V T'" by blast
qed

lemma termination_aux:
  assumes h1: "\<Gamma> \<turnstile> e : T"
  and     h2: "\<theta> Vcloses \<Gamma>"
  shows "\<exists>v. \<theta><e> \<Down> v \<and> v \<in> V T" 
using h2 h1
proof(nominal_induct e avoiding: \<Gamma> \<theta> arbitrary: T rule: trm.strong_induct)
  case (App e\<^isub>1 e\<^isub>2 \<Gamma> \<theta> T)
  have ih\<^isub>1: "\<And>\<theta> \<Gamma> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> e\<^isub>1 : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><e\<^isub>1> \<Down> v \<and> v \<in> V T" by fact
  have ih\<^isub>2: "\<And>\<theta> \<Gamma> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> e\<^isub>2 : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><e\<^isub>2> \<Down> v \<and> v \<in> V T" by fact
  have as\<^isub>1: "\<theta> Vcloses \<Gamma>" by fact 
  have as\<^isub>2: "\<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T" by fact
  then obtain T' where "\<Gamma> \<turnstile> e\<^isub>1 : T' \<rightarrow> T" and "\<Gamma> \<turnstile> e\<^isub>2 : T'" by (auto elim: t_App_elim)
  then obtain v\<^isub>1 v\<^isub>2 where "(i)": "\<theta><e\<^isub>1> \<Down> v\<^isub>1" "v\<^isub>1 \<in> V (T' \<rightarrow> T)"
                      and "(ii)": "\<theta><e\<^isub>2> \<Down> v\<^isub>2" "v\<^isub>2 \<in> V T'" using ih\<^isub>1 ih\<^isub>2 as\<^isub>1 by blast
  from "(i)" obtain x e' 
            where "v\<^isub>1 = Lam [x].e'" 
            and "(iii)": "(\<forall>v \<in> (V T').\<exists> v'. e'[x::=v] \<Down> v' \<and> v' \<in> V T)"
            and "(iv)":  "\<theta><e\<^isub>1> \<Down> Lam [x].e'" 
            and fr: "x\<sharp>(\<theta>,e\<^isub>1,e\<^isub>2)" by (blast elim: V_arrow_elim_strong)
  from fr have fr\<^isub>1: "x\<sharp>\<theta><e\<^isub>1>" and fr\<^isub>2: "x\<sharp>\<theta><e\<^isub>2>" by (simp_all add: fresh_psubst)
  from "(ii)" "(iii)" obtain v\<^isub>3 where "(v)": "e'[x::=v\<^isub>2] \<Down> v\<^isub>3" "v\<^isub>3 \<in> V T" by auto
  from fr\<^isub>2 "(ii)" have "x\<sharp>v\<^isub>2" by (simp add: big_preserves_fresh)
  then have "x\<sharp>e'[x::=v\<^isub>2]" by (simp add: fresh_subst)
  then have fr\<^isub>3: "x\<sharp>v\<^isub>3" using "(v)" by (simp add: big_preserves_fresh)
  from fr\<^isub>1 fr\<^isub>2 fr\<^isub>3 have "x\<sharp>(\<theta><e\<^isub>1>,\<theta><e\<^isub>2>,v\<^isub>3)" by simp
  with "(iv)" "(ii)" "(v)" have "App (\<theta><e\<^isub>1>) (\<theta><e\<^isub>2>) \<Down> v\<^isub>3" by auto
  then show "\<exists>v. \<theta><App e\<^isub>1 e\<^isub>2> \<Down> v \<and> v \<in> V T" using "(v)" by auto
next
  case (Lam x e \<Gamma> \<theta> T)
  have ih:"\<And>\<theta> \<Gamma> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><e> \<Down> v \<and> v \<in> V T" by fact
  have as\<^isub>1: "\<theta> Vcloses \<Gamma>" by fact
  have as\<^isub>2: "\<Gamma> \<turnstile> Lam [x].e : T" by fact
  have fs: "x\<sharp>\<Gamma>" "x\<sharp>\<theta>" by fact+
  from as\<^isub>2 fs obtain T\<^isub>1 T\<^isub>2 
    where "(i)": "(x,T\<^isub>1)#\<Gamma> \<turnstile> e:T\<^isub>2" and "(ii)": "T = T\<^isub>1 \<rightarrow> T\<^isub>2" using fs
    by (auto elim: t_Lam_elim)
  from "(i)" have "(iii)": "valid ((x,T\<^isub>1)#\<Gamma>)" by (simp add: typing_implies_valid)
  have "\<forall>v \<in> (V T\<^isub>1). \<exists>v'. (\<theta><e>)[x::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2"
  proof
    fix v
    assume "v \<in> (V T\<^isub>1)"
    with "(iii)" as\<^isub>1 have "(x,v)#\<theta> Vcloses (x,T\<^isub>1)#\<Gamma>" using monotonicity by auto
    with ih "(i)" obtain v' where "((x,v)#\<theta>)<e> \<Down> v' \<and> v' \<in> V T\<^isub>2" by blast
    then have "\<theta><e>[x::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2" using fs by (simp add: psubst_subst_psubst)
    then show "\<exists>v'. \<theta><e>[x::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2" by auto
  qed
  then have "Lam[x].\<theta><e> \<in> V (T\<^isub>1 \<rightarrow> T\<^isub>2)" by auto
  then have "\<theta><Lam [x].e> \<Down> Lam [x].\<theta><e> \<and> Lam [x].\<theta><e> \<in> V (T\<^isub>1\<rightarrow>T\<^isub>2)" using fs by auto
  thus "\<exists>v. \<theta><Lam [x].e> \<Down> v \<and> v \<in> V T" using "(ii)" by auto
next
  case (Var x \<Gamma> \<theta> T)
  have "\<Gamma> \<turnstile> (Var x) : T" by fact
  then have "(x,T)\<in>set \<Gamma>" by (cases) (auto simp add: trm.inject)
  with Var have "\<theta><Var x> \<Down> \<theta><Var x> \<and> \<theta><Var x>\<in> V T" 
    by (auto intro!: Vs_reduce_to_themselves)
  then show "\<exists>v. \<theta><Var x> \<Down> v \<and> v \<in> V T" by auto
qed 

theorem termination_of_evaluation:
  assumes a: "[] \<turnstile> e : T"
  shows "\<exists>v. e \<Down> v \<and> val v"
proof -
  from a have "\<exists>v. []<e> \<Down> v \<and> v \<in> V T" by (rule termination_aux) (auto)
  thus "\<exists>v. e \<Down> v \<and> val v" using Vs_are_values by auto
qed 

end
