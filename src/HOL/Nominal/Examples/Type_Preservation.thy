(* $Id$ *)

theory Type_Preservation
  imports Nominal
begin

text {*

  This theory shows how to prove the type preservation
  property for the simply-typed lambda-calculus and 
  beta-reduction.
 
*}

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam" 
| Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._")

text {* Capture-Avoiding Substitution *}

consts 
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]")

nominal_primrec
  "(Var x)[y::=s] = (if x=y then s else (Var x))"
  "(App t\<^isub>1 t\<^isub>2)[y::=s] = App (t\<^isub>1[y::=s]) (t\<^isub>2[y::=s])"
  "x\<sharp>(y,s) \<Longrightarrow> (Lam [x].t)[y::=s] = Lam [x].(t[y::=s])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

lemma  subst_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(t1[x::=t2]) = (pi\<bullet>t1)[(pi\<bullet>x)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: x t2 rule: lam.strong_induct)
   (auto simp add: perm_bij fresh_atm fresh_bij)

lemma fresh_fact:
  fixes z::"name"
  shows "\<lbrakk>z\<sharp>s; (z=y \<or> z\<sharp>t)\<rbrakk> \<Longrightarrow> z\<sharp>t[y::=s]"
by (nominal_induct t avoiding: z y s rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_prod fresh_atm)

text {* Types *}

nominal_datatype ty =
    TVar "string"
  | TArr "ty" "ty" ("_ \<rightarrow> _")

lemma ty_fresh:
  fixes x::"name"
  and   T::"ty"
  shows "x\<sharp>T"
by (induct T rule: ty.induct)
   (auto simp add: fresh_string)

text {* Typing Contexts *}

types ctx = "(name\<times>ty) list"

abbreviation
  "sub_ctx" :: "ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<subseteq> _") 
where
  "\<Gamma>\<^isub>1 \<subseteq> \<Gamma>\<^isub>2 \<equiv> \<forall>x. x \<in> set \<Gamma>\<^isub>1 \<longrightarrow> x \<in> set \<Gamma>\<^isub>2"

text {* Validity of Typing Contexts *}

inductive
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>; x\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((x,T)#\<Gamma>)"

equivariance valid

lemma valid_elim[dest]:
  assumes a: "valid ((x,T)#\<Gamma>)"
  shows "x\<sharp>\<Gamma> \<and> valid \<Gamma>"
using a by (cases) (auto)

lemma valid_insert:
  assumes a: "valid (\<Delta>@[(x,T)]@\<Gamma>)"
  shows "valid (\<Delta> @ \<Gamma>)" 
using a
by (induct \<Delta>)
   (auto simp add:  fresh_list_append fresh_list_cons dest!: valid_elim)

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
  typing :: "ctx \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _") 
where
  t_Var[intro]: "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| t_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1\<rightarrow>T\<^isub>2; \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t\<^isub>1 t\<^isub>2 : T\<^isub>2"
| t_Lam[intro]: "\<lbrakk>x\<sharp>\<Gamma>; (x,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T\<^isub>1\<rightarrow>T\<^isub>2"

equivariance typing
nominal_inductive typing
  by (simp_all add: abs_fresh ty_fresh)

lemma t_Lam_inversion[dest]:
  assumes ty: "\<Gamma> \<turnstile> Lam [x].t : T" 
  and     fc: "x\<sharp>\<Gamma>" 
  shows "\<exists>T\<^isub>1 T\<^isub>2. T = T\<^isub>1 \<rightarrow> T\<^isub>2 \<and> (x,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2"
using ty fc 
by (cases rule: typing.strong_cases) 
   (auto simp add: alpha lam.inject abs_fresh ty_fresh)

lemma t_App_inversion[dest]:
  assumes ty: "\<Gamma> \<turnstile> App t1 t2 : T" 
  shows "\<exists>T'. \<Gamma> \<turnstile> t1 : T' \<rightarrow> T \<and> \<Gamma> \<turnstile> t2 : T'"
using ty 
by (cases) (auto simp add: lam.inject)

lemma weakening: 
  fixes \<Gamma>1 \<Gamma>2::"ctx"
  assumes a: "\<Gamma>1 \<turnstile> t : T" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
by (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
   (auto | atomize)+

lemma type_substitution_aux:
  assumes a: "(\<Delta>@[(x,T')]@\<Gamma>) \<turnstile> e : T"
  and     b: "\<Gamma> \<turnstile> e' : T'"
  shows "(\<Delta>@\<Gamma>) \<turnstile> e[x::=e'] : T" 
using a b 
proof (nominal_induct \<Gamma>'\<equiv>"\<Delta>@[(x,T')]@\<Gamma>" e T avoiding: x e' \<Delta> rule: typing.strong_induct)
  case (t_Var \<Gamma>' y T x e' \<Delta>)
  then have a1: "valid (\<Delta>@[(x,T')]@\<Gamma>)" 
       and  a2: "(y,T) \<in> set (\<Delta>@[(x,T')]@\<Gamma>)" 
       and  a3: "\<Gamma> \<turnstile> e' : T'" by simp_all
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

corollary type_substitution:
  assumes a: "(x,T')#\<Gamma> \<turnstile> e : T"
  and     b: "\<Gamma> \<turnstile> e' : T'"
  shows "\<Gamma> \<turnstile> e[x::=e'] : T"
using a b
by (auto intro: type_substitution_aux[where \<Delta>="[]",simplified])

text {* Beta Reduction *}

inductive 
  "beta" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _")
where
  b1[intro]: "t1 \<longrightarrow>\<^isub>\<beta> t2 \<Longrightarrow> App t1 s \<longrightarrow>\<^isub>\<beta> App t2 s"
| b2[intro]: "s1 \<longrightarrow>\<^isub>\<beta> s2 \<Longrightarrow> App t s1 \<longrightarrow>\<^isub>\<beta> App t s2"
| b3[intro]: "t1 \<longrightarrow>\<^isub>\<beta> t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>\<^isub>\<beta> Lam [x].t2"
| b4[intro]: "x\<sharp>s \<Longrightarrow> App (Lam [x].t) s \<longrightarrow>\<^isub>\<beta> t[x::=s]"

equivariance beta
nominal_inductive beta
  by (auto simp add: abs_fresh fresh_fact)


theorem type_preservation:
  assumes a: "t \<longrightarrow>\<^isub>\<beta> t'"
  and     b: "\<Gamma> \<turnstile> t : T" 
  shows "\<Gamma> \<turnstile> t' : T" 
using a b
proof (nominal_induct avoiding: \<Gamma> T rule: beta.strong_induct)
  case (b1 t1 t2 s \<Gamma> T)
  have "\<Gamma> \<turnstile> App t1 s : T" by fact
  then obtain T' where a1: "\<Gamma> \<turnstile> t1 : T' \<rightarrow> T" and a2: "\<Gamma> \<turnstile> s : T'" by auto
  have ih: "\<Gamma> \<turnstile> t1 : T' \<rightarrow> T \<Longrightarrow> \<Gamma> \<turnstile> t2 : T' \<rightarrow> T" by fact
  with a1 a2 show "\<Gamma> \<turnstile> App t2 s : T" by auto
next 
  case (b2 s1 s2 t \<Gamma> T)
  have "\<Gamma> \<turnstile> App t s1 : T" by fact
  then obtain T' where a1: "\<Gamma> \<turnstile> t : T' \<rightarrow> T" and a2: "\<Gamma> \<turnstile> s1 : T'" by auto
  have ih: "\<Gamma> \<turnstile> s1 : T' \<Longrightarrow> \<Gamma> \<turnstile> s2 : T'" by fact
  with a1 a2 show "\<Gamma> \<turnstile> App t s2 : T" by auto
next 
  case (b3 t1 t2 x \<Gamma> T)
  have vc: "x\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> Lam [x].t1 : T" by fact
  then obtain T1 T2 where a1: "(x,T1)#\<Gamma> \<turnstile> t1 : T2" and a2: "T = T1 \<rightarrow> T2" using vc by auto
  have ih: "(x,T1)#\<Gamma> \<turnstile> t1 : T2 \<Longrightarrow> (x,T1)#\<Gamma> \<turnstile> t2 : T2" by fact
  with a1 a2 show "\<Gamma> \<turnstile> Lam [x].t2 : T" using vc by auto
next
  case (b4 x s t \<Gamma> T)
  have vc: "x\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> App (Lam [x].t) s : T" by fact
  then obtain T' where a1: "\<Gamma> \<turnstile> Lam [x].t : T' \<rightarrow> T" and a2: "\<Gamma> \<turnstile> s : T'" by auto
  from a1 obtain T1 T2 where a3: "(x,T')#\<Gamma> \<turnstile> t : T" using vc by (auto simp add: ty.inject)
  from a3 a2 show "\<Gamma> \<turnstile> t[x::=s] : T" by (simp add: type_substitution)
qed


theorem type_preservation_automatic:
  assumes a: "t \<longrightarrow>\<^isub>\<beta> t'"
  and     b: "\<Gamma> \<turnstile> t : T" 
  shows "\<Gamma> \<turnstile> t' : T"
using a b
by (nominal_induct avoiding: \<Gamma> T rule: beta.strong_induct)
   (auto dest!: t_Lam_inversion t_App_inversion simp add: ty.inject type_substitution)

end
