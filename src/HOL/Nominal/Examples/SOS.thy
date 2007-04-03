(* "$Id$" *)
(*                                                   *)
(* Formalisation of some typical SOS-proofs          *)
(*                                                   *) 
(* This work arose from challenge suggested by Adam  *)
(* Chlipala suggested on the POPLmark mailing list.  *)
(*                                                   *) 
(* We thank Nick Benton for helping us with the      *) 
(* termination-proof for evaluation.                 *)

theory SOS
  imports "../Nominal"
begin

atom_decl name 

nominal_datatype data = 
    DNat
  | DProd "data" "data"
  | DSum "data" "data"

nominal_datatype ty = 
    Data "data"
  | Arrow "ty" "ty" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype trm = 
    Var "name"
  | Lam "\<guillemotleft>name\<guillemotright>trm" ("Lam [_]._" [100,100] 100)
  | App "trm" "trm"
  | Const "nat"
  | Pr "trm" "trm"
  | Fst "trm"
  | Snd "trm"
  | InL "trm"
  | InR "trm"
  | Case "trm" "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" ("Case _ of inl _ \<rightarrow> _ | inr _ \<rightarrow> _" [100,100,100,100,100] 100)

lemma in_eqvt[eqvt]:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  assumes "x\<in>X"
  shows "pi\<bullet>x \<in> pi\<bullet>X"
  using assms by (perm_simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])

lemma perm_data[simp]: 
  fixes D::"data"
  and   pi::"name prm"
  shows "pi\<bullet>D = D"
  by (induct D rule: data.weak_induct) (simp_all)

lemma perm_ty[simp]: 
  fixes T::"ty"
  and   pi::"name prm"
  shows "pi\<bullet>T = T"
  by (induct T rule: ty.weak_induct) (simp_all)

lemma fresh_ty[simp]:
  fixes x::"name" 
  and   T::"ty"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

text {* substitution *}

fun
  lookup :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm"   
where
  "lookup [] x        = Var x"
| "lookup ((y,e)#\<theta>) x = (if x=y then e else lookup \<theta> x)"

lemma lookup_eqvt:
  fixes pi::"name prm"
  and   \<theta>::"(name\<times>trm) list"
  and   X::"name"
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>, auto simp add: perm_bij)

lemma lookup_fresh:
  fixes z::"name"
  assumes "z\<sharp>\<theta>" and "z\<sharp>x"
  shows "z \<sharp>lookup \<theta> x"
using assms 
by (induct rule: lookup.induct) (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using assms 
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

text {* Parallel Substitution *}

consts
  psubst :: "(name\<times>trm) list \<Rightarrow> trm \<Rightarrow> trm"  ("_<_>" [95,95] 105)
 
nominal_primrec
  "\<theta><(Var x)> = (lookup \<theta> x)"
  "\<theta><(App e\<^isub>1 e\<^isub>2)> = App (\<theta><e\<^isub>1>) (\<theta><e\<^isub>2>)"
  "x\<sharp>\<theta> \<Longrightarrow> \<theta><(Lam [x].e)> = Lam [x].(\<theta><e>)"
  "\<theta><(Const n)> = Const n"
  "\<theta><(Pr e\<^isub>1 e\<^isub>2)> = Pr (\<theta><e\<^isub>1>) (\<theta><e\<^isub>2>)"
  "\<theta><(Fst e)> = Fst (\<theta><e>)"
  "\<theta><(Snd e)> = Snd (\<theta><e>)"
  "\<theta><(InL e)> = InL (\<theta><e>)"
  "\<theta><(InR e)> = InR (\<theta><e>)"
  "\<lbrakk>y\<noteq>x; x\<sharp>(e,e\<^isub>2,\<theta>); y\<sharp>(e,e\<^isub>1,\<theta>)\<rbrakk> 
   \<Longrightarrow> \<theta><Case e of inl x \<rightarrow> e\<^isub>1 | inr y \<rightarrow> e\<^isub>2> = (Case (\<theta><e>) of inl x \<rightarrow> (\<theta><e\<^isub>1>) | inr y \<rightarrow> (\<theta><e\<^isub>2>))"
apply(finite_guess add: lookup_eqvt)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess add: fs_name1 lookup_eqvt)+
done

lemma psubst_eqvt[eqvt]:
  fixes pi::"name prm" 
  and   t::"trm"
  shows "pi\<bullet>(\<theta><t>) = (pi\<bullet>\<theta>)<(pi\<bullet>t)>"
by (nominal_induct t avoiding: \<theta> rule: trm.induct)
   (perm_simp add: fresh_bij lookup_eqvt)+

lemma fresh_psubst: 
  fixes z::"name"
  and   t::"trm"
  assumes "z\<sharp>t" and "z\<sharp>\<theta>"
  shows "z\<sharp>(\<theta><t>)"
using assms
by (nominal_induct t avoiding: z \<theta> t rule: trm.induct)
   (auto simp add: abs_fresh lookup_fresh)

abbreviation 
 subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)
  where "t[x::=t']  \<equiv> ([(x,t')])<t>" 

lemma subst[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t\<^isub>1 t\<^isub>2)[y::=t'] = App (t\<^isub>1[y::=t']) (t\<^isub>2[y::=t'])"
  and   "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
  and   "(Const n)[y::=t'] = Const n"
  and   "(Pr e\<^isub>1 e\<^isub>2)[y::=t'] = Pr (e\<^isub>1[y::=t']) (e\<^isub>2[y::=t'])"
  and   "(Fst e)[y::=t'] = Fst (e[y::=t'])"
  and   "(Snd e)[y::=t'] = Snd (e[y::=t'])"
  and   "(InL e)[y::=t'] = InL (e[y::=t'])"
  and   "(InR e)[y::=t'] = InR (e[y::=t'])"
  and   "\<lbrakk>z\<noteq>x; x\<sharp>(y,e,e\<^isub>2,t'); z\<sharp>(y,e,e\<^isub>1,t')\<rbrakk> 
         \<Longrightarrow> (Case e of inl x \<rightarrow> e\<^isub>1 | inr z \<rightarrow> e\<^isub>2)[y::=t'] =
                   (Case (e[y::=t']) of inl x \<rightarrow> (e\<^isub>1[y::=t']) | inr z \<rightarrow> (e\<^isub>2[y::=t']))"
by (simp_all add: fresh_list_cons fresh_list_nil)

lemma subst_eqvt[eqvt]:
  fixes pi::"name prm" 
  and   t::"trm"
  shows "pi\<bullet>(t[x::=t']) = (pi\<bullet>t)[(pi\<bullet>x)::=(pi\<bullet>t')]"
  by (nominal_induct t avoiding: x t' rule: trm.induct)
     (perm_simp add: fresh_bij)+

lemma fresh_subst:
  fixes z::"name"
  and   t\<^isub>1::"trm"
  and   t2::"trm"
  assumes "z\<sharp>t\<^isub>1" and "z\<sharp>t\<^isub>2"
  shows "z\<sharp>t\<^isub>1[y::=t\<^isub>2]"
using assms 
by (nominal_induct t\<^isub>1 avoiding: z y t\<^isub>2 rule: trm.induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_subst':
  fixes z::"name"
  and   t\<^isub>1::"trm"
  and   t2::"trm"
  assumes "z\<sharp>[y].t\<^isub>1" and "z\<sharp>t\<^isub>2"
  shows "z\<sharp>t\<^isub>1[y::=t\<^isub>2]"
using assms 
by (nominal_induct t\<^isub>1 avoiding: y t\<^isub>2 z  rule: trm.induct)
   (auto simp add: abs_fresh fresh_nat fresh_atm)

lemma forget: 
  fixes x::"name"
  and   L::"trm"
  assumes "x\<sharp>L" 
  shows "L[x::=P] = L"
  using assms
  by (nominal_induct L avoiding: x P rule: trm.induct)
     (auto simp add: fresh_atm abs_fresh)

lemma psubst_empty[simp]:
  shows "[]<t> = t"
  by (nominal_induct t rule: trm.induct, auto simp add:fresh_list_nil)

lemma psubst_subst_psubst:
assumes h:"x\<sharp>\<theta>"
shows "\<theta><e>[x::=e'] = ((x,e')#\<theta>)<e>"
using h
apply(nominal_induct e avoiding: \<theta> x e' rule: trm.induct)
apply(auto simp add: fresh_list_cons fresh_atm forget lookup_fresh lookup_fresh' fresh_psubst)
done

lemma fresh_subst_fresh:
    assumes "a\<sharp>e"
    shows "a\<sharp>t[a::=e]"
using assms 
by (nominal_induct t avoiding: a e rule: trm.induct)
   (auto simp add: fresh_atm abs_fresh fresh_nat) 

text {* Typing-Judgements *}

inductive2
  valid :: "(name \<times> 'a::pt_name) list \<Rightarrow> bool"
where
    v_nil[intro]:  "valid []"
  | v_cons[intro]: "\<lbrakk>valid \<Gamma>;x\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> valid ((x,T)#\<Gamma>)"

equivariance valid 

inductive_cases2  
  valid_cons_inv_auto[elim]:"valid ((x,T)#\<Gamma>)"

abbreviation
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ \<lless> _" [55,55] 55)
where
  "\<Gamma>\<^isub>1 \<lless> \<Gamma>\<^isub>2 \<equiv> \<forall>x T. (x,T)\<in>set \<Gamma>\<^isub>1 \<longrightarrow> (x,T)\<in>set \<Gamma>\<^isub>2"

lemma type_unicity_in_context:
  assumes asm1: "(x,t\<^isub>2) \<in> set ((x,t\<^isub>1)#\<Gamma>)" 
  and     asm2: "valid ((x,t\<^isub>1)#\<Gamma>)"
  shows "t\<^isub>1=t\<^isub>2"
proof -
  from asm2 have "x\<sharp>\<Gamma>" by (cases, auto)
  then have "(x,t\<^isub>2) \<notin> set \<Gamma>"
    by (induct \<Gamma>) (auto simp add: fresh_list_cons fresh_prod fresh_atm)
  then have "(x,t\<^isub>2) = (x,t\<^isub>1)" using asm1 by auto
  then show "t\<^isub>1 = t\<^isub>2" by auto
qed

lemma case_distinction_on_context:
  fixes \<Gamma>::"(name \<times> ty) list"
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

inductive2
  typing :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60) 
where
  t_Var[intro]:   "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| t_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e\<^isub>1 : T\<^isub>1\<rightarrow>T\<^isub>2; \<Gamma> \<turnstile> e\<^isub>2 : T\<^isub>1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T\<^isub>2"
| t_Lam[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T\<^isub>1)#\<Gamma> \<turnstile> e : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].e : T\<^isub>1\<rightarrow>T\<^isub>2"
| t_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n : Data(DNat)"
| t_Pr[intro]:    "\<lbrakk>\<Gamma> \<turnstile> e\<^isub>1 : Data(S\<^isub>1); \<Gamma> \<turnstile> e\<^isub>2 : Data(S\<^isub>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Pr e\<^isub>1 e\<^isub>2 : Data (DProd S\<^isub>1 S\<^isub>2)"
| t_Fst[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e : Data(DProd S\<^isub>1 S\<^isub>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Fst e : Data(S\<^isub>1)"
| t_Snd[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e : Data(DProd S\<^isub>1 S\<^isub>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Snd e : Data(S\<^isub>2)"
| t_InL[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e : Data(S\<^isub>1)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> InL e : Data(DSum S\<^isub>1 S\<^isub>2)"
| t_InR[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e : Data(S\<^isub>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> InR e : Data(DSum S\<^isub>1 S\<^isub>2)"
| t_Case[intro]:  "\<lbrakk>x\<^isub>1\<sharp>(\<Gamma>,e,e\<^isub>2,x\<^isub>2); x\<^isub>2\<sharp>(\<Gamma>,e,e\<^isub>1,x\<^isub>1); \<Gamma> \<turnstile> e: Data(DSum S\<^isub>1 S\<^isub>2); 
                   (x\<^isub>1,Data(S\<^isub>1))#\<Gamma> \<turnstile> e\<^isub>1 : T; (x\<^isub>2,Data(S\<^isub>2))#\<Gamma> \<turnstile> e\<^isub>2 : T\<rbrakk> 
                   \<Longrightarrow> \<Gamma> \<turnstile> (Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2) : T"

nominal_inductive typing
  by (simp_all add: abs_fresh fresh_prod fresh_atm)

lemmas typing_eqvt' = typing.eqvt[simplified]

lemma typing_implies_valid:
  assumes "\<Gamma> \<turnstile> t : T"
  shows "valid \<Gamma>"
  using assms
  by (induct) (auto)

declare trm.inject [simp add]
declare ty.inject  [simp add]
declare data.inject [simp add]

inductive_cases2 t_Lam_inv_auto[elim]: "\<Gamma> \<turnstile> Lam [x].t : T"
inductive_cases2 t_Var_inv_auto[elim]: "\<Gamma> \<turnstile> Var x : T"
inductive_cases2 t_App_inv_auto[elim]: "\<Gamma> \<turnstile> App x y : T"
inductive_cases2 t_Const_inv_auto[elim]: "\<Gamma> \<turnstile> Const n : T"
inductive_cases2 t_Fst_inv_auto[elim]: "\<Gamma> \<turnstile> Fst x : T"
inductive_cases2 t_Snd_inv_auto[elim]: "\<Gamma> \<turnstile> Snd x : T"
inductive_cases2 t_InL_inv_auto[elim]: "\<Gamma> \<turnstile> InL x : T"
inductive_cases2 t_InL_inv_auto'[elim]: "\<Gamma> \<turnstile> InL x : Data (DSum T\<^isub>1 T2)"
inductive_cases2 t_InR_inv_auto[elim]: "\<Gamma> \<turnstile> InR x : T"
inductive_cases2 t_InR_inv_auto'[elim]: "\<Gamma> \<turnstile> InR x : Data (DSum T\<^isub>1 T2)"
inductive_cases2 t_Pr_inv_auto[elim]:  "\<Gamma> \<turnstile> Pr x y : T"
inductive_cases2 t_Pr_inv_auto'[elim]: "\<Gamma> \<turnstile> Pr e\<^isub>1 e\<^isub>2 : Data (DProd \<sigma>1 \<sigma>\<^isub>2)"
inductive_cases2 t_Case_inv_auto[elim]: "\<Gamma> \<turnstile> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 : T"

declare trm.inject [simp del]
declare ty.inject [simp del]
declare data.inject [simp del]

lemma t_Lam_elim[elim]: 
  assumes a1:"\<Gamma> \<turnstile> Lam [x].t : T" 
  and     a2: "x\<sharp>\<Gamma>"
  obtains T\<^isub>1 and T\<^isub>2 where "(x,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2" and "T=T\<^isub>1\<rightarrow>T\<^isub>2"
proof -
  from a1 obtain x' t' T\<^isub>1 T\<^isub>2 
    where b1: "x'\<sharp>\<Gamma>" and b2: "(x',T\<^isub>1)#\<Gamma> \<turnstile> t' : T\<^isub>2" and b3: "[x'].t' = [x].t" and b4: "T=T\<^isub>1\<rightarrow>T\<^isub>2"
    by auto
  obtain c::"name" where "c\<sharp>(\<Gamma>,x,x',t,t')" by (erule exists_fresh[OF fs_name1])
  then have fs: "c\<sharp>\<Gamma>" "c\<noteq>x" "c\<noteq>x'" "c\<sharp>t" "c\<sharp>t'" by (simp_all add: fresh_atm[symmetric]) 
  then have b5: "[(x',c)]\<bullet>t'=[(x,c)]\<bullet>t" using b3 fs by (simp add: alpha')
  have "([(x,c)]\<bullet>[(x',c)]\<bullet>((x',T\<^isub>1)#\<Gamma>)) \<turnstile> ([(x,c)]\<bullet>[(x',c)]\<bullet>t') : T\<^isub>2" using b2
    by (simp only: typing_eqvt')
  then have "(x,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2" using fs b1 a2 b5 by (perm_simp add: calc_atm)
  then show ?thesis using prems b4 by simp
qed

lemma t_Case_elim[elim]: 
  assumes "\<Gamma> \<turnstile> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 : T" and "x\<^isub>1\<sharp>\<Gamma>" and "x\<^isub>2\<sharp>\<Gamma>" 
  obtains \<sigma>\<^isub>1 \<sigma>\<^isub>2 where "\<Gamma> \<turnstile> e : Data (DSum \<sigma>\<^isub>1 \<sigma>\<^isub>2)" 
                  and "(x\<^isub>1, Data \<sigma>\<^isub>1)#\<Gamma> \<turnstile> e\<^isub>1 : T" 
                  and "(x\<^isub>2, Data \<sigma>\<^isub>2)#\<Gamma> \<turnstile> e\<^isub>2 : T"
proof -
  have f:"x\<^isub>1\<sharp>\<Gamma>" "x\<^isub>2\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 : T" by fact
  then obtain \<sigma>\<^isub>1 \<sigma>\<^isub>2 x\<^isub>1' x\<^isub>2' e\<^isub>1' e\<^isub>2' where 
    h:"\<Gamma> \<turnstile> e : Data (DSum \<sigma>\<^isub>1 \<sigma>\<^isub>2)" and 
    h1:"(x\<^isub>1',Data \<sigma>\<^isub>1)#\<Gamma> \<turnstile> e\<^isub>1' : T" and 
    h2:"(x\<^isub>2',Data \<sigma>\<^isub>2)#\<Gamma> \<turnstile> e\<^isub>2' : T" and
    e1:"[x\<^isub>1].e\<^isub>1=[x\<^isub>1'].e\<^isub>1'" and e2:"[x\<^isub>2].e\<^isub>2=[x\<^isub>2'].e\<^isub>2'"
    by auto
  obtain c::name where f':"c \<sharp> (x\<^isub>1,x\<^isub>1',e\<^isub>1,e\<^isub>1',\<Gamma>)" by (erule exists_fresh[OF fs_name1])
  have e1':"[(x\<^isub>1,c)]\<bullet>e\<^isub>1 = [(x\<^isub>1',c)]\<bullet>e\<^isub>1'" using e1 f' by (auto simp add: alpha' fresh_prod fresh_atm)
  have "[(x\<^isub>1',c)]\<bullet>((x\<^isub>1',Data \<sigma>\<^isub>1)# \<Gamma>) \<turnstile> [(x\<^isub>1',c)]\<bullet>e\<^isub>1' : T" using h1 typing_eqvt' by blast
  then have x:"(c,Data \<sigma>\<^isub>1)#( [(x\<^isub>1',c)]\<bullet>\<Gamma>) \<turnstile> [(x\<^isub>1',c)]\<bullet>e\<^isub>1': T" using f' 
    by (auto simp add: fresh_atm calc_atm)
  have "x\<^isub>1' \<sharp> \<Gamma>" using h1 typing_implies_valid by auto
  then have "(c,Data \<sigma>\<^isub>1)#\<Gamma> \<turnstile> [(x\<^isub>1 ,c)]\<bullet>e\<^isub>1 : T" using f' x e1' by (auto simp add: perm_fresh_fresh)
  then have "[(x\<^isub>1,c)]\<bullet>((c,Data \<sigma>\<^isub>1)#\<Gamma>) \<turnstile> [(x\<^isub>1,c)]\<bullet>[(x\<^isub>1 ,c)]\<bullet>e\<^isub>1 : T" using typing_eqvt' by blast 
  then have "([(x\<^isub>1,c)]\<bullet>(c,Data \<sigma>\<^isub>1)) #\<Gamma> \<turnstile> [(x\<^isub>1,c)]\<bullet>[(x\<^isub>1 ,c)]\<bullet>e\<^isub>1 : T" using f f' 
    by (auto simp add: perm_fresh_fresh)
  then have "([(x\<^isub>1,c)]\<bullet>(c,Data \<sigma>\<^isub>1)) #\<Gamma> \<turnstile> e\<^isub>1 : T" by perm_simp
  then have g1:"(x\<^isub>1, Data \<sigma>\<^isub>1)#\<Gamma> \<turnstile> e\<^isub>1 : T"  using f' by (auto simp add: fresh_atm calc_atm fresh_prod)
    (* The second part of the proof is the same *)
  obtain c::name where f':"c \<sharp> (x\<^isub>2,x\<^isub>2',e\<^isub>2,e\<^isub>2',\<Gamma>)" by (erule exists_fresh[OF fs_name1])
  have e2':"[(x\<^isub>2,c)]\<bullet>e\<^isub>2 = [(x\<^isub>2',c)]\<bullet>e\<^isub>2'" using e2 f' by (auto simp add: alpha' fresh_prod fresh_atm)
  have "[(x\<^isub>2',c)]\<bullet>((x\<^isub>2',Data \<sigma>\<^isub>2)# \<Gamma>) \<turnstile> [(x\<^isub>2',c)]\<bullet>e\<^isub>2' : T" using h2 typing_eqvt' by blast
  then have x:"(c,Data \<sigma>\<^isub>2)#([(x\<^isub>2',c)]\<bullet>\<Gamma>) \<turnstile> [(x\<^isub>2',c)]\<bullet>e\<^isub>2': T" using f' 
    by (auto simp add: fresh_atm calc_atm)
  have "x\<^isub>2' \<sharp> \<Gamma>" using h2 typing_implies_valid by auto
  then have "(c,Data \<sigma>\<^isub>2)#\<Gamma> \<turnstile> [(x\<^isub>2 ,c)]\<bullet>e\<^isub>2 : T" using f' x e2' by (auto simp add: perm_fresh_fresh)
  then have "[(x\<^isub>2,c)]\<bullet>((c,Data \<sigma>\<^isub>2)#\<Gamma>) \<turnstile> [(x\<^isub>2,c)]\<bullet>[(x\<^isub>2 ,c)]\<bullet>e\<^isub>2 : T" using typing_eqvt' by blast 
  then have "([(x\<^isub>2,c)]\<bullet>(c,Data \<sigma>\<^isub>2))#\<Gamma> \<turnstile> [(x\<^isub>2,c)]\<bullet>[(x\<^isub>2 ,c)]\<bullet>e\<^isub>2 : T" using f f' 
    by (auto simp add: perm_fresh_fresh)
  then have "([(x\<^isub>2,c)]\<bullet>(c,Data \<sigma>\<^isub>2)) #\<Gamma> \<turnstile> e\<^isub>2 : T" by perm_simp
  then have g2:"(x\<^isub>2,Data \<sigma>\<^isub>2)#\<Gamma> \<turnstile> e\<^isub>2 : T"  using f' by (auto simp add: fresh_atm calc_atm fresh_prod)
  show ?thesis using g1 g2 prems by auto 
qed

lemma weakening: 
  assumes "\<Gamma>\<^isub>1 \<turnstile> e: T" and "valid \<Gamma>\<^isub>2" and "\<Gamma>\<^isub>1 \<lless> \<Gamma>\<^isub>2"
  shows "\<Gamma>\<^isub>2 \<turnstile> e: T"
  using assms
proof(nominal_induct \<Gamma>\<^isub>1 e T avoiding: \<Gamma>\<^isub>2 rule: typing.strong_induct)
  case (t_Lam x \<Gamma>\<^isub>1 T\<^isub>1 t T\<^isub>2 \<Gamma>\<^isub>2)
  have ih: "\<lbrakk>valid ((x,T\<^isub>1)#\<Gamma>\<^isub>2); (x,T\<^isub>1)#\<Gamma>\<^isub>1 \<lless> (x,T\<^isub>1)#\<Gamma>\<^isub>2\<rbrakk> \<Longrightarrow> (x,T\<^isub>1)#\<Gamma>\<^isub>2 \<turnstile> t : T\<^isub>2" by fact
  have H1: "valid \<Gamma>\<^isub>2" by fact
  have H2: "\<Gamma>\<^isub>1 \<lless> \<Gamma>\<^isub>2" by fact
  have fs: "x\<sharp>\<Gamma>\<^isub>2" by fact
  then have "valid ((x,T\<^isub>1)#\<Gamma>\<^isub>2)" using H1 by auto
  moreover have "(x,T\<^isub>1)#\<Gamma>\<^isub>1 \<lless> (x,T\<^isub>1)#\<Gamma>\<^isub>2" using H2 by auto
  ultimately have "(x,T\<^isub>1)#\<Gamma>\<^isub>2 \<turnstile> t : T\<^isub>2" using ih by simp 
  thus "\<Gamma>\<^isub>2 \<turnstile> Lam [x].t : T\<^isub>1\<rightarrow>T\<^isub>2" using fs by auto
next
  case (t_Case x\<^isub>1 \<Gamma>\<^isub>1 e e\<^isub>2 x\<^isub>2 e\<^isub>1 S\<^isub>1 S\<^isub>2 T \<Gamma>\<^isub>2)
  then have ih\<^isub>1: "valid ((x\<^isub>1,Data S\<^isub>1)#\<Gamma>\<^isub>2) \<Longrightarrow> (x\<^isub>1,Data S\<^isub>1)#\<Gamma>\<^isub>2 \<turnstile> e\<^isub>1 : T" 
       and  ih\<^isub>2: "valid ((x\<^isub>2,Data S\<^isub>2)#\<Gamma>\<^isub>2) \<Longrightarrow> (x\<^isub>2,Data S\<^isub>2)#\<Gamma>\<^isub>2 \<turnstile> e\<^isub>2 : T" 
       and  ih\<^isub>3: "\<Gamma>\<^isub>2 \<turnstile> e : Data (DSum S\<^isub>1 S\<^isub>2)" by auto 
  have fs\<^isub>1: "x\<^isub>1\<sharp>\<Gamma>\<^isub>2" "x\<^isub>1\<sharp>e" "x\<^isub>1\<sharp>e\<^isub>2" "x\<^isub>1\<sharp>x\<^isub>2" by fact
  have fs\<^isub>2: "x\<^isub>2\<sharp>\<Gamma>\<^isub>2" "x\<^isub>2\<sharp>e" "x\<^isub>2\<sharp>e\<^isub>1" "x\<^isub>2\<sharp>x\<^isub>1" by fact
  have "valid \<Gamma>\<^isub>2" by fact
  then have "valid ((x\<^isub>1,Data S\<^isub>1)#\<Gamma>\<^isub>2)" and "valid ((x\<^isub>2,Data S\<^isub>2)#\<Gamma>\<^isub>2)" using fs\<^isub>1 fs\<^isub>2 by auto
  then have "(x\<^isub>1, Data S\<^isub>1)#\<Gamma>\<^isub>2 \<turnstile> e\<^isub>1 : T" and "(x\<^isub>2, Data S\<^isub>2)#\<Gamma>\<^isub>2 \<turnstile> e\<^isub>2 : T" using ih\<^isub>1 ih\<^isub>2 by simp_all
  with ih\<^isub>3 show "\<Gamma>\<^isub>2 \<turnstile> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 : T" using fs\<^isub>1 fs\<^isub>2 by auto
qed (auto)

lemma context_exchange:
  assumes a: "(x\<^isub>1,T\<^isub>1)#(x\<^isub>2,T\<^isub>2)#\<Gamma> \<turnstile> e : T"
  shows "(x\<^isub>2,T\<^isub>2)#(x\<^isub>1,T\<^isub>1)#\<Gamma> \<turnstile> e : T"
proof -
  from  a have "valid ((x\<^isub>1,T\<^isub>1)#(x\<^isub>2,T\<^isub>2)#\<Gamma>)" by (simp add: typing_implies_valid)
  then have "x\<^isub>1\<noteq>x\<^isub>2" "x\<^isub>1\<sharp>\<Gamma>" "x\<^isub>2\<sharp>\<Gamma>" "valid \<Gamma>"
    by (auto simp: fresh_list_cons fresh_atm[symmetric])
  then have "valid ((x\<^isub>2,T\<^isub>2)#(x\<^isub>1,T\<^isub>1)#\<Gamma>)"
    by (auto simp: fresh_list_cons fresh_atm)
  moreover 
  have "(x\<^isub>1,T\<^isub>1)#(x\<^isub>2,T\<^isub>2)#\<Gamma> \<lless> (x\<^isub>2,T\<^isub>2)#(x\<^isub>1,T\<^isub>1)#\<Gamma>" by auto
  ultimately show "(x\<^isub>2,T\<^isub>2)#(x\<^isub>1,T\<^isub>1)#\<Gamma> \<turnstile> e : T" using a by (auto intro: weakening)
qed

lemma typing_var_unicity: 
  assumes "(x,t\<^isub>1)#\<Gamma> \<turnstile> Var x : t\<^isub>2"
  shows "t\<^isub>1=t\<^isub>2"
proof - 
  have "(x,t\<^isub>2) \<in> set ((x,t\<^isub>1)#\<Gamma>)" and "valid ((x,t\<^isub>1)#\<Gamma>)" using assms by auto
  thus "t\<^isub>1=t\<^isub>2" by (simp only: type_unicity_in_context)
qed

lemma typing_substitution: 
  fixes \<Gamma>::"(name \<times> ty) list"
  assumes "(x,T')#\<Gamma> \<turnstile> e : T" 
  and     "\<Gamma> \<turnstile> e': T'" 
  shows "\<Gamma> \<turnstile> e[x::=e'] : T"
  using assms
proof (nominal_induct e avoiding: \<Gamma> e' x arbitrary: T rule: trm.induct)
  case (Var y \<Gamma> e' x T)
  have h1: "(x,T')#\<Gamma> \<turnstile> Var y : T" by fact
  have h2: "\<Gamma> \<turnstile> e' : T'" by fact
  show "\<Gamma> \<turnstile> (Var y)[x::=e'] : T"
  proof (cases "x=y")
    case True
    assume as: "x=y"
    then have "T=T'" using h1 typing_var_unicity by auto
    then show "\<Gamma> \<turnstile> (Var y)[x::=e'] : T" using as h2 by simp
  next
    case False
    assume as: "x\<noteq>y" 
    have "(y,T) \<in> set ((x,T')#\<Gamma>)" using h1 by auto
    then have "(y,T) \<in> set \<Gamma>" using as by auto
    moreover 
    have "valid \<Gamma>" using h2 by (simp only: typing_implies_valid)
    ultimately show "\<Gamma> \<turnstile> (Var y)[x::=e'] : T" using as by (simp add: t_Var)
  qed
next
  case (Lam y t \<Gamma> e' x T)
  have vc: "y\<sharp>\<Gamma>" "y\<sharp>x" "y\<sharp>e'"  by fact
  have pr1: "\<Gamma> \<turnstile> e' : T'" by fact
  have pr2: "(x,T')#\<Gamma> \<turnstile> Lam [y].t : T" by fact
  then obtain T\<^isub>1 T\<^isub>2 where pr2': "(y,T\<^isub>1)#(x,T')#\<Gamma> \<turnstile> t : T\<^isub>2" and eq: "T = T\<^isub>1\<rightarrow>T\<^isub>2" 
    using vc by (auto simp add: fresh_list_cons)
  then have pr2'':"(x,T')#(y,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2" by (simp add: context_exchange)
  have ih: "\<lbrakk>(x,T')#(y,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2; (y,T\<^isub>1)#\<Gamma> \<turnstile> e' : T'\<rbrakk> \<Longrightarrow> (y,T\<^isub>1)#\<Gamma> \<turnstile> t[x::=e'] : T\<^isub>2" by fact
  have "valid \<Gamma>" using pr1 by (simp add: typing_implies_valid)
  then have "valid ((y,T\<^isub>1)#\<Gamma>)" using vc by auto
  then have "(y,T\<^isub>1)#\<Gamma> \<turnstile> e' : T'" using pr1 by (auto intro: weakening)
  then have "(y,T\<^isub>1)#\<Gamma> \<turnstile> t[x::=e'] : T\<^isub>2" using ih pr2'' by simp
  then have "\<Gamma> \<turnstile> Lam [y].(t[x::=e']) : T\<^isub>1\<rightarrow>T\<^isub>2" using vc by (auto intro: t_Lam)
  thus "\<Gamma> \<turnstile> (Lam [y].t)[x::=e'] : T" using vc eq by simp
next
  case (Case t\<^isub>1 x\<^isub>1 t\<^isub>2 x\<^isub>2 t3 \<Gamma> e' x T)
  have vc: "x\<^isub>1\<sharp>\<Gamma>" "x\<^isub>1\<sharp>e'" "x\<^isub>1\<sharp>x""x\<^isub>1\<sharp>t\<^isub>1" "x\<^isub>1\<sharp>t3" "x\<^isub>2\<sharp>\<Gamma>" 
           "x\<^isub>2\<sharp>e'" "x\<^isub>2\<sharp>x"  "x\<^isub>2\<sharp>t\<^isub>1" "x\<^isub>2\<sharp>t\<^isub>2" "x\<^isub>2\<noteq>x\<^isub>1" by fact
  have as1: "\<Gamma> \<turnstile> e' : T'" by fact
  have as2: "(x,T')#\<Gamma> \<turnstile> Case t\<^isub>1 of inl x\<^isub>1 \<rightarrow> t\<^isub>2 | inr x\<^isub>2 \<rightarrow> t3 : T" by fact
  then obtain S\<^isub>1 S\<^isub>2 where 
    h1:"(x,T')#\<Gamma> \<turnstile> t\<^isub>1 : Data (DSum S\<^isub>1 S\<^isub>2)" and
    h2:"(x\<^isub>1,Data S\<^isub>1)#(x,T')#\<Gamma> \<turnstile> t\<^isub>2 : T" and
    h3:"(x\<^isub>2,Data S\<^isub>2)#(x,T')#\<Gamma> \<turnstile> t3 : T"
    using vc by (auto simp add: fresh_list_cons)
  have ih1: "\<lbrakk>(x,T')#\<Gamma> \<turnstile> t\<^isub>1 : T; \<Gamma> \<turnstile> e' : T'\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t\<^isub>1[x::=e'] : T" 
  and  ih2: "\<lbrakk>(x,T')#(x\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> t\<^isub>2:T; (x\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> e':T'\<rbrakk> \<Longrightarrow> (x\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> t\<^isub>2[x::=e']:T" 
  and  ih3: "\<lbrakk>(x,T')#(x\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> t3:T; (x\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> e':T'\<rbrakk> \<Longrightarrow> (x\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> t3[x::=e']:T"
    by fact
  from h2 have h2': "(x,T')#(x\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> t\<^isub>2 : T" by (rule context_exchange)
  from h3 have h3': "(x,T')#(x\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> t3 : T" by (rule context_exchange)
  have "\<Gamma> \<turnstile> t\<^isub>1[x::=e'] : Data (DSum S\<^isub>1 S\<^isub>2)" using h1 ih1 as1 by simp
  moreover
  have "valid ((x\<^isub>1,Data S\<^isub>1)#\<Gamma>)" using h2' by (auto dest: typing_implies_valid)
  then have "(x\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> e' : T'" using as1 by (auto simp add: weakening)
  then have "(x\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> t\<^isub>2[x::=e'] : T" using ih2 h2' by simp
  moreover 
  have "valid ((x\<^isub>2,Data S\<^isub>2)#\<Gamma>)" using h3' by (auto dest: typing_implies_valid)
  then have "(x\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> e' : T'" using as1 by (auto simp add: weakening)
  then have "(x\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> t3[x::=e'] : T" using ih3 h3' by simp
  ultimately have "\<Gamma> \<turnstile> Case (t\<^isub>1[x::=e']) of inl x\<^isub>1 \<rightarrow> (t\<^isub>2[x::=e']) | inr x\<^isub>2 \<rightarrow> (t3[x::=e']) : T"
    using vc by (auto simp add: fresh_atm fresh_subst)
  thus "\<Gamma> \<turnstile> (Case t\<^isub>1 of inl x\<^isub>1 \<rightarrow> t\<^isub>2 | inr x\<^isub>2 \<rightarrow> t3)[x::=e'] : T" using vc by simp
qed (simp, fast)+

text {* Big-Step Evaluation *}

inductive2
  big :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<Down> _" [80,80] 80) 
where
  b_Lam[intro]:   "Lam [x].e \<Down> Lam [x].e"
| b_App[intro]:   "\<lbrakk>x\<sharp>(e\<^isub>1,e\<^isub>2,e'); e\<^isub>1\<Down>Lam [x].e; e\<^isub>2\<Down>e\<^isub>2'; e[x::=e\<^isub>2']\<Down>e'\<rbrakk> \<Longrightarrow> App e\<^isub>1 e\<^isub>2 \<Down> e'"
| b_Const[intro]: "Const n \<Down> Const n"
| b_Pr[intro]:    "\<lbrakk>e\<^isub>1\<Down>e\<^isub>1'; e\<^isub>2\<Down>e\<^isub>2'\<rbrakk> \<Longrightarrow> Pr e\<^isub>1 e\<^isub>2 \<Down> Pr e\<^isub>1' e\<^isub>2'"
| b_Fst[intro]:   "e\<Down>Pr e\<^isub>1 e\<^isub>2 \<Longrightarrow> Fst e\<Down>e\<^isub>1"
| b_Snd[intro]:   "e\<Down>Pr e\<^isub>1 e\<^isub>2 \<Longrightarrow> Snd e\<Down>e\<^isub>2"
| b_InL[intro]:   "e\<Down>e' \<Longrightarrow> InL e \<Down> InL e'"
| b_InR[intro]:   "e\<Down>e' \<Longrightarrow> InR e \<Down> InR e'"
| b_CaseL[intro]: "\<lbrakk>x\<^isub>1\<sharp>(e,e\<^isub>2,e'',x\<^isub>2); x\<^isub>2\<sharp>(e,e\<^isub>1,e'',x\<^isub>1) ; e\<Down>InL e'; e\<^isub>1[x\<^isub>1::=e']\<Down>e''\<rbrakk> 
                   \<Longrightarrow> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> e''"
| b_CaseR[intro]: "\<lbrakk>x\<^isub>1\<sharp>(e,e\<^isub>2,e'',x\<^isub>2); x\<^isub>2\<sharp>(e,e\<^isub>1,e'',x\<^isub>1) ; e\<Down>InR e'; e\<^isub>2[x\<^isub>2::=e']\<Down>e''\<rbrakk> 
                   \<Longrightarrow> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> e''"

nominal_inductive big
  by (simp_all add: abs_fresh fresh_prod fresh_atm)

lemma big_eqvt':
  fixes pi::"name prm"
  assumes a: "(pi\<bullet>t) \<Down> (pi\<bullet>t')"
  shows "t \<Down> t'"
using a
apply -
apply(drule_tac pi="rev pi" in big.eqvt)
apply(perm_simp)
done

lemma fresh_preserved:
  fixes x::name
  fixes t::trm
  fixes t'::trm
  assumes "e \<Down> e'" and "x\<sharp>e" 
  shows "x\<sharp>e'"
  using assms by (induct) (auto simp add:fresh_subst')

declare trm.inject  [simp add]
declare ty.inject  [simp add]
declare data.inject [simp add]

inductive_cases2 b_App_inv_auto[elim]: "App e\<^isub>1 e\<^isub>2 \<Down> t" 
inductive_cases2 b_Case_inv_auto[elim]: "Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> t"
inductive_cases2 b_Lam_inv_auto[elim]: "Lam[x].t \<Down> t"
inductive_cases2 b_Const_inv_auto[elim]: "Const n \<Down> t"
inductive_cases2 b_Fst_inv_auto[elim]: "Fst e \<Down> t"
inductive_cases2 b_Snd_inv_auto[elim]: "Snd e \<Down> t"
inductive_cases2 b_InL_inv_auto[elim]: "InL e \<Down> t"
inductive_cases2 b_InR_inv_auto[elim]: "InR e \<Down> t"
inductive_cases2 b_Pr_inv_auto[elim]: "Pr e\<^isub>1 e\<^isub>2 \<Down> t"

declare trm.inject  [simp del]
declare ty.inject  [simp del]
declare data.inject [simp del]

lemma b_App_elim[elim]:
  assumes "App e\<^isub>1 e\<^isub>2 \<Down> e'" and "x\<sharp>(e\<^isub>1,e\<^isub>2,e')"
  obtains f\<^isub>1 and f\<^isub>2 where "e\<^isub>1 \<Down> Lam [x]. f\<^isub>1" "e\<^isub>2 \<Down> f\<^isub>2" "f\<^isub>1[x::=f\<^isub>2] \<Down> e'"
  using assms
  apply -
  apply(erule b_App_inv_auto)
  apply(drule_tac pi="[(xa,x)]" in big.eqvt)
  apply(drule_tac pi="[(xa,x)]" in big.eqvt)
  apply(drule_tac pi="[(xa,x)]" in big.eqvt)
  apply(perm_simp add: calc_atm eqvts)
  done

lemma  b_CaseL_elim[elim]: 
  assumes "Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> e''" 
  and     "\<And> t. \<not>  e \<Down> InR t"
  and     "x\<^isub>1\<sharp>e''" "x\<^isub>1\<sharp>e" "x\<^isub>2\<sharp>e''" "x\<^isub>1\<sharp>e"
  obtains e' where "e \<Down> InL e'" and "e\<^isub>1[x\<^isub>1::=e'] \<Down> e''"
  using assms 
  apply -
  apply(rule b_Case_inv_auto)
  apply(auto)
  apply(simp add: alpha)
  apply(auto)
  apply(drule_tac x="[(x\<^isub>1,x\<^isub>1')]\<bullet>e'" in meta_spec)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>1,x\<^isub>1')]" in big_eqvt')
  apply(perm_simp add: fresh_prod)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>1,x\<^isub>1')]" in big_eqvt')
  apply(perm_simp add: eqvts calc_atm)
  apply(assumption)
  apply(drule_tac x="[(x\<^isub>1,x\<^isub>1')]\<bullet>e'" in meta_spec)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>1,x\<^isub>1')]" in big_eqvt')
  apply(perm_simp add: fresh_prod)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>1,x\<^isub>1')]" in big_eqvt')
  apply(perm_simp add: eqvts calc_atm)
  apply(assumption)
done

lemma b_CaseR_elim[elim]: 
  assumes "Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> e''" 
  and     "\<And> t. \<not> e \<Down> InL t"
  and     "x\<^isub>1\<sharp>e''" "x\<^isub>1\<sharp>e" "x\<^isub>2\<sharp>e''" "x\<^isub>2\<sharp>e"
  obtains e' where "e \<Down> InR e'" and "e\<^isub>2[x\<^isub>2::=e'] \<Down> e''"
  using assms 
  apply -
  apply(rule b_Case_inv_auto)
  apply(auto)
  apply(simp add: alpha)
  apply(auto)
  apply(drule_tac x="[(x\<^isub>2,x\<^isub>2')]\<bullet>e'" in meta_spec)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>2,x\<^isub>2')]" in big_eqvt')
  apply(perm_simp add: fresh_prod)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>2,x\<^isub>2')]" in big_eqvt')
  apply(perm_simp add: eqvts calc_atm)
  apply(assumption)
  apply(drule_tac x="[(x\<^isub>2,x\<^isub>2')]\<bullet>e'" in meta_spec)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>2,x\<^isub>2')]" in big_eqvt')
  apply(perm_simp add: fresh_prod)
  apply(drule meta_mp)
  apply(rule_tac pi="[(x\<^isub>2,x\<^isub>2')]" in big_eqvt')
  apply(perm_simp add: eqvts calc_atm)
  apply(assumption)
done

inductive2
  val :: "trm\<Rightarrow>bool" 
where
  v_Lam[intro]:   "val (Lam [x].e)"
| v_Const[intro]: "val (Const n)"
| v_Pr[intro]:    "\<lbrakk>val e\<^isub>1; val e\<^isub>2\<rbrakk> \<Longrightarrow> val (Pr e\<^isub>1 e\<^isub>2)"
| v_InL[intro]:   "val e \<Longrightarrow> val (InL e)"
| v_InR[intro]:   "val e \<Longrightarrow> val (InR e)"

declare trm.inject  [simp add]
declare ty.inject  [simp add]
declare data.inject [simp add]

inductive_cases2 v_Const_inv_auto[elim]: "val (Const n)"
inductive_cases2 v_Pr_inv_auto[elim]: "val (Pr e\<^isub>1 e\<^isub>2)"
inductive_cases2 v_InL_inv_auto[elim]: "val (InL e)"
inductive_cases2 v_InR_inv_auto[elim]: "val (InR e)"
inductive_cases2 v_Fst_inv_auto[elim]: "val (Fst e)"
inductive_cases2 v_Snd_inv_auto[elim]: "val (Snd e)"
inductive_cases2 v_Case_inv_auto[elim]: "val (Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2)"
inductive_cases2 v_Var_inv_auto[elim]: "val (Var x)"
inductive_cases2 v_Lam_inv_auto[elim]: "val (Lam [x].e)"
inductive_cases2 v_App_inv_auto[elim]: "val (App e\<^isub>1 e\<^isub>2)"

declare trm.inject  [simp del]
declare ty.inject  [simp del]
declare data.inject [simp del]

lemma subject_reduction:
  assumes a: "e \<Down> e'" 
  and     b: "\<Gamma> \<turnstile> e : T"
  shows "\<Gamma> \<turnstile> e' : T"
  using a b
proof (nominal_induct avoiding: \<Gamma> arbitrary: T rule: big.strong_induct) 
  case (b_App x e\<^isub>1 e\<^isub>2 e' e e\<^isub>2' \<Gamma> T)
  have vc: "x\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T" by fact
  then obtain T' where 
    a1: "\<Gamma> \<turnstile> e\<^isub>1 : T'\<rightarrow>T" and  
    a2: "\<Gamma> \<turnstile> e\<^isub>2 : T'" by auto
  have ih1: "\<Gamma> \<turnstile> e\<^isub>1 : T' \<rightarrow> T \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].e : T' \<rightarrow> T" by fact
  have ih2: "\<Gamma> \<turnstile> e\<^isub>2 : T' \<Longrightarrow> \<Gamma> \<turnstile> e\<^isub>2' : T'" by fact 
  have ih3: "\<Gamma> \<turnstile> e[x::=e\<^isub>2'] : T \<Longrightarrow> \<Gamma> \<turnstile> e' : T" by fact
  have "\<Gamma> \<turnstile> Lam [x].e : T'\<rightarrow>T" using ih1 a1 by simp 
  then have "((x,T')#\<Gamma>) \<turnstile> e : T" using vc by (auto simp add: ty.inject)
  moreover
  have "\<Gamma> \<turnstile> e\<^isub>2': T'" using ih2 a2 by simp
  ultimately have "\<Gamma> \<turnstile> e[x::=e\<^isub>2'] : T" by (simp add: typing_substitution)
  thus "\<Gamma> \<turnstile> e' : T" using ih3 by simp
next
  case (b_CaseL x\<^isub>1 e e\<^isub>2 e'' x\<^isub>2 e\<^isub>1 e' \<Gamma>)
  have vc: "x\<^isub>1\<sharp>\<Gamma>" "x\<^isub>2\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 : T" by fact 
  then obtain S\<^isub>1 S\<^isub>2 e\<^isub>1' e\<^isub>2' where 
    a1: "\<Gamma> \<turnstile> e : Data (DSum S\<^isub>1 S\<^isub>2)" and 
    a2: "((x\<^isub>1,Data S\<^isub>1)#\<Gamma>) \<turnstile> e\<^isub>1 : T" using vc by auto 
  have ih1:"\<Gamma> \<turnstile> e : Data (DSum S\<^isub>1 S\<^isub>2) \<Longrightarrow> \<Gamma> \<turnstile> InL e' : Data (DSum S\<^isub>1 S\<^isub>2)" by fact 
  have ih2:"\<Gamma> \<turnstile> e\<^isub>1[x\<^isub>1::=e'] : T \<Longrightarrow> \<Gamma> \<turnstile> e'' : T " by fact 
  have "\<Gamma> \<turnstile> InL e' : Data (DSum S\<^isub>1 S\<^isub>2)" using ih1 a1 by simp
  then have "\<Gamma> \<turnstile> e' : Data S\<^isub>1" by auto
  then have "\<Gamma> \<turnstile> e\<^isub>1[x\<^isub>1::=e'] : T" using a2 by (simp add: typing_substitution)
  then show "\<Gamma> \<turnstile> e'' : T" using ih2 by simp
next
 case (b_CaseR x\<^isub>1 e e\<^isub>2 e'' x\<^isub>2 e\<^isub>1 e' \<Gamma> T)
 then show "\<Gamma> \<turnstile> e'' : T" by (blast intro: typing_substitution)
qed (blast)+

lemma unicity_of_evaluation:
  assumes a: "e \<Down> e\<^isub>1" 
  and     b: "e \<Down> e\<^isub>2"
  shows "e\<^isub>1 = e\<^isub>2"
  using a b
proof (nominal_induct e e\<^isub>1 avoiding: e\<^isub>2 rule: big.strong_induct)
  case (b_Lam x e t\<^isub>2)
  have "Lam [x].e \<Down> t\<^isub>2" by fact
  thus "Lam [x].e = t\<^isub>2" by (cases, simp_all add: trm.inject)
next
  case (b_App x e\<^isub>1 e\<^isub>2 e' e\<^isub>1' e\<^isub>2' t\<^isub>2)
  have ih1: "\<And>t. e\<^isub>1 \<Down> t \<Longrightarrow> Lam [x].e\<^isub>1' = t" by fact
  have ih2:"\<And>t. e\<^isub>2 \<Down> t \<Longrightarrow> e\<^isub>2' = t" by fact
  have ih3: "\<And>t. e\<^isub>1'[x::=e\<^isub>2'] \<Down> t \<Longrightarrow> e' = t" by fact
  have app: "App e\<^isub>1 e\<^isub>2 \<Down> t\<^isub>2" by fact
  have vc: "x\<sharp>e\<^isub>1" "x\<sharp>e\<^isub>2" by fact
  then have "x \<sharp> App e\<^isub>1 e\<^isub>2" by auto
  then have vc': "x\<sharp>t\<^isub>2" using fresh_preserved app by blast
  from vc vc' obtain f\<^isub>1 f\<^isub>2 where x1: "e\<^isub>1 \<Down> Lam [x]. f\<^isub>1" and x2: "e\<^isub>2 \<Down> f\<^isub>2" and x3: "f\<^isub>1[x::=f\<^isub>2] \<Down> t\<^isub>2"
    using app by (auto simp add: fresh_prod)
  then have "Lam [x]. f\<^isub>1 = Lam [x]. e\<^isub>1'" using ih1 by simp
  then 
  have "f\<^isub>1 = e\<^isub>1'" by (auto simp add: trm.inject alpha) 
  moreover 
  have "f\<^isub>2 = e\<^isub>2'" using x2 ih2 by simp
  ultimately have "e\<^isub>1'[x::=e\<^isub>2'] \<Down> t\<^isub>2" using x3 by simp
  thus ?case using ih3 by simp
next
  case (b_CaseL  x\<^isub>1 e e\<^isub>2 e'' x\<^isub>2 e\<^isub>1 e' t\<^isub>2)
  have fs: "x\<^isub>1\<sharp>e" "x\<^isub>1\<sharp>t\<^isub>2" "x\<^isub>2\<sharp>e" "x\<^isub>2\<sharp>t\<^isub>2" by fact 
  have ih1:"\<And>t. e \<Down> t \<Longrightarrow> InL e' = t" by fact 
  have ih2:"\<And>t. e\<^isub>1[x\<^isub>1::=e'] \<Down> t \<Longrightarrow> e'' = t" by fact
  have ha: "\<not>(\<exists>t. e \<Down> InR t)" using ih1 by force
  have "Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> t\<^isub>2" by fact
  then obtain f' where "e \<Down> InL f'" and h: "e\<^isub>1[x\<^isub>1::=f']\<Down>t\<^isub>2" using ha fs by auto
  then have "InL f' = InL e'" using ih1 by simp
  then have "f' = e'" by (simp add: trm.inject)
  then have "e\<^isub>1[x\<^isub>1::=e'] \<Down> t\<^isub>2" using h by simp
  then show "e'' = t\<^isub>2" using ih2 by simp
next 
  case (b_CaseR x\<^isub>1 e e\<^isub>2 e'' x\<^isub>2 e\<^isub>1 e' t\<^isub>2 )
  have fs: "x\<^isub>1\<sharp>e" "x\<^isub>1\<sharp>t\<^isub>2" "x\<^isub>2\<sharp>e" "x\<^isub>2\<sharp>t\<^isub>2" by fact 
  have ih1: "\<And>t. e \<Down> t \<Longrightarrow> InR e' = t" by fact
  have ih2: "\<And>t. e\<^isub>2[x\<^isub>2::=e'] \<Down> t \<Longrightarrow> e'' = t" by fact
  have ha: "\<not>(\<exists>t. e \<Down> InL t)" using ih1 by force
  have "Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2 \<Down> t\<^isub>2" by fact
  then obtain f' where "e \<Down> InR f'" and h: "e\<^isub>2[x\<^isub>2::=f']\<Down>t\<^isub>2"  using ha fs by auto
  then have "InR f' = InR e'" using ih1 by simp
  then have "e\<^isub>2[x\<^isub>2::=e'] \<Down> t\<^isub>2" using h by (simp add: trm.inject)
  thus "e'' = t\<^isub>2" using ih2 by simp
next
  case b_Fst
  then show ?case by (force simp add: trm.inject)
next
  case b_Snd
  then show ?case by (force simp add: trm.inject)
qed (blast)+

lemma not_val_App[simp]:
  shows 
  "\<not> val (App e\<^isub>1 e\<^isub>2)" 
  "\<not> val (Fst e)"
  "\<not> val (Snd e)"
  "\<not> val (Var x)"
  "\<not> val (Case e of inl x\<^isub>1 \<rightarrow> e\<^isub>1 | inr x\<^isub>2 \<rightarrow> e\<^isub>2)"
by auto

lemma reduces_evaluates_to_values:
  assumes h:"t \<Down> t'"
  shows "val t'"
  using h by (induct) (auto)

lemma type_prod_evaluates_to_pairs:
  assumes a: "\<Gamma> \<turnstile> t : Data (DProd S\<^isub>1 S\<^isub>2)" 
  and     b: "t \<Down> t'"
  obtains t\<^isub>1 t\<^isub>2 where "t' = Pr t\<^isub>1 t\<^isub>2"
proof -
   have "\<Gamma> \<turnstile> t' : Data (DProd S\<^isub>1 S\<^isub>2)" using assms subject_reduction by simp
   moreover
   have "val t'" using reduces_evaluates_to_values assms by simp
   ultimately obtain t\<^isub>1 t\<^isub>2 where "t' = Pr t\<^isub>1 t\<^isub>2" by (cases, auto simp add:ty.inject data.inject)
   thus ?thesis using prems by auto
qed

lemma type_sum_evaluates_to_ins:
  assumes "\<Gamma> \<turnstile> t : Data (DSum \<sigma>\<^isub>1 \<sigma>\<^isub>2)" and "t \<Down> t'"
  shows "(\<exists>t''. t' = InL t'') \<or> (\<exists>t''. t' = InR t'')"
proof -
  have "\<Gamma> \<turnstile> t' : Data (DSum \<sigma>\<^isub>1 \<sigma>\<^isub>2)" using assms subject_reduction by simp
  moreover
  have "val t'" using reduces_evaluates_to_values assms by simp
  ultimately obtain t'' where "t' = InL t'' \<or>  t' = InR t''"
    by (cases, auto simp add:ty.inject data.inject)
  thus ?thesis by auto
qed

lemma type_arrow_evaluates_to_lams:
  assumes "\<Gamma> \<turnstile> t : \<sigma> \<rightarrow> \<tau>" and "t \<Down> t'"
  obtains  x t'' where "t' = Lam [x]. t''"
proof -
  have "\<Gamma> \<turnstile> t' : \<sigma> \<rightarrow> \<tau>" using assms subject_reduction by simp
  moreover
  have "val t'" using reduces_evaluates_to_values assms by simp
  ultimately obtain x t'' where "t' = Lam [x]. t''" by (cases, auto simp add:ty.inject data.inject)
  thus ?thesis using prems by auto
qed

lemma type_nat_evaluates_to_consts:
  assumes "\<Gamma> \<turnstile> t : Data DNat" and "t \<Down> t'"
  obtains n where "t' = Const n"
proof -
  have "\<Gamma> \<turnstile> t' : Data DNat " using assms subject_reduction by simp
  moreover have "val t'" using reduces_evaluates_to_values assms by simp
  ultimately obtain n where "t' = Const n" by (cases, auto simp add:ty.inject data.inject)
  thus ?thesis using prems by auto
qed

consts
  V' :: "data \<Rightarrow> trm set" 

nominal_primrec    
  "V' (DNat) = {Const n | n. n \<in> (UNIV::nat set)}"
  "V' (DProd S\<^isub>1 S\<^isub>2) = {Pr x y | x y. x \<in> V' S\<^isub>1 \<and> y \<in> V' S\<^isub>2}"
  "V' (DSum S\<^isub>1 S\<^isub>2) = {InL x | x. x \<in> V' S\<^isub>1} \<union> {InR y | y. y \<in> V' S\<^isub>2}"
apply(rule TrueI)+
done

lemma Vprimes_are_values :
  fixes S::"data"
  assumes h: "e \<in> V' S"
  shows "val e"
using h 
by (nominal_induct S arbitrary: e rule:data.induct)
   (auto)

lemma V'_eqvt:
  fixes pi::"name prm"
  assumes a: "v \<in> V' S"
  shows "(pi\<bullet>v) \<in> V' S"
using a
by (nominal_induct S arbitrary: v rule: data.induct)
   (auto simp add: trm.inject)

consts
  V :: "ty \<Rightarrow> trm set" 

nominal_primrec
  "V (Data S) = V' S"
  "V (T\<^isub>1 \<rightarrow> T\<^isub>2) = {Lam [x].e | x e. \<forall> v \<in> (V T\<^isub>1). \<exists> v'. e[x::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2}"
apply(rule TrueI)+ 
done

lemma V_eqvt:
  fixes pi::"name prm"
  assumes a: "x\<in>V T"
  shows "(pi\<bullet>x)\<in>V T"
using a
apply(nominal_induct T arbitrary: pi x rule: ty.induct)
apply(auto simp add: trm.inject perm_set_def)
apply(perm_simp add: V'_eqvt)
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

lemma V_arrow_elim_weak[elim] :
  assumes h:"u \<in> (V (T\<^isub>1 \<rightarrow> T\<^isub>2))"
  obtains a t where "u = Lam[a].t" and "\<forall> v \<in> (V T\<^isub>1). \<exists> v'. t[a::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2"
using h by (auto)

lemma V_arrow_elim_strong[elim]:
  fixes c::"'a::fs_name"
  assumes h: "u \<in> V (T\<^isub>1 \<rightarrow> T\<^isub>2)"
  obtains a t where "a\<sharp>c" "u = Lam[a].t" "\<forall>v \<in> (V T\<^isub>1). \<exists> v'. t[a::=v] \<Down> v' \<and> v' \<in> V T\<^isub>2"
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

lemma V_are_values :
  fixes T::"ty"
  assumes h:"e \<in> V T"
  shows "val e"
using h by (nominal_induct T arbitrary: e rule:ty.induct, auto simp add: Vprimes_are_values)

lemma values_reduce_to_themselves:
  assumes h:"val v"
  shows "v \<Down> v"
using h by (induct,auto)

lemma Vs_reduce_to_themselves[simp]:
  assumes h:"v \<in> V T"
  shows "v \<Down> v"
using h by (simp add: values_reduce_to_themselves V_are_values)

lemma V_sum:
  assumes h:"x \<in> V (Data (DSum S\<^isub>1 S\<^isub>2))"
  shows "(\<exists> y. x= InL y \<and>  y \<in> V' S\<^isub>1) \<or> (\<exists> y. x= InR y \<and> y \<in> V' S\<^isub>2)"
using h by simp

abbreviation 
 mapsto :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> bool" ("_ maps _ to _" [55,55,55] 55) 
where
 "\<theta> maps x to e\<equiv> (lookup \<theta> x) = e"

abbreviation 
  v_closes :: "(name\<times>trm) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ Vcloses _" [55,55] 55) 
where
  "\<theta> Vcloses \<Gamma> \<equiv> \<forall>x T. ((x,T) \<in> set \<Gamma> \<longrightarrow> (\<exists>v. \<theta> maps x to v \<and> v \<in> (V T)))"

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
  fixes T :: "ty"
  fixes \<Gamma> :: "(name \<times> ty) list"
  fixes \<theta> :: "(name \<times> trm) list"
  fixes e :: "trm"
  assumes h1: "\<Gamma> \<turnstile> e : T"
  and     h2: "\<theta> Vcloses \<Gamma>"
  shows "\<exists>v. \<theta><e> \<Down> v \<and> v \<in> V T" 
using h2 h1
proof(nominal_induct e avoiding: \<Gamma> \<theta> arbitrary: T rule: trm.induct)
  case (App e\<^isub>1 e\<^isub>2 \<Gamma> \<theta> T)
  have ih\<^isub>1:"\<And>\<theta> \<Gamma> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> e\<^isub>1 : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><e\<^isub>1> \<Down> v \<and> v \<in> V T" by fact
  have ih\<^isub>2:"\<And>\<theta> \<Gamma> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> e\<^isub>2 : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><e\<^isub>2> \<Down> v \<and> v \<in> V T" by fact
  have as\<^isub>1:"\<theta> Vcloses \<Gamma>" by fact 
  have as\<^isub>2: "\<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T" by fact
  from as\<^isub>2 obtain T' where "\<Gamma> \<turnstile> e\<^isub>1 : T' \<rightarrow> T" and "\<Gamma> \<turnstile> e\<^isub>2 : T'" by auto
  then obtain v\<^isub>1 v\<^isub>2 where "(i)": "\<theta><e\<^isub>1> \<Down> v\<^isub>1" "v\<^isub>1 \<in> V (T' \<rightarrow> T)"
                      and "(ii)":"\<theta><e\<^isub>2> \<Down> v\<^isub>2" "v\<^isub>2 \<in> V T'" using ih\<^isub>1 ih\<^isub>2 as\<^isub>1 by blast
  from "(i)" obtain x e' 
            where "v\<^isub>1 = Lam[x].e'" 
            and "(iii)": "(\<forall>v \<in> (V T').\<exists> v'. e'[x::=v] \<Down> v' \<and> v' \<in> V T)"
            and "(iv)":  "\<theta><e\<^isub>1> \<Down> Lam [x].e'" 
            and fr: "x\<sharp>(\<theta>,e\<^isub>1,e\<^isub>2)" by blast
  from fr have fr\<^isub>1: "x\<sharp>\<theta><e\<^isub>1>" and fr\<^isub>2: "x\<sharp>\<theta><e\<^isub>2>" by (simp_all add: fresh_psubst)
  from "(ii)" "(iii)" obtain v\<^isub>3 where "(v)": "e'[x::=v\<^isub>2] \<Down> v\<^isub>3" "v\<^isub>3 \<in> V T" by auto
  from fr\<^isub>2 "(ii)" have "x\<sharp>v\<^isub>2" by (simp add: fresh_preserved)
  then have "x\<sharp>e'[x::=v\<^isub>2]" by (simp add: fresh_subst_fresh)
  then have fr\<^isub>3: "x\<sharp>v\<^isub>3" using "(v)" by (simp add: fresh_preserved)
  from fr\<^isub>1 fr\<^isub>2 fr\<^isub>3 have "x\<sharp>(\<theta><e\<^isub>1>,\<theta><e\<^isub>2>,v\<^isub>3)" by simp
  with "(iv)" "(ii)" "(v)" have "App (\<theta><e\<^isub>1>) (\<theta><e\<^isub>2>) \<Down> v\<^isub>3" by auto
  then show "\<exists>v. \<theta><App e\<^isub>1 e\<^isub>2> \<Down> v \<and> v \<in> V T" using "(v)" by auto
next
  case (Pr t\<^isub>1 t\<^isub>2 \<Gamma> \<theta> T)
  have "\<Gamma> \<turnstile> Pr t\<^isub>1 t\<^isub>2 : T" by fact
  then obtain T\<^isub>a T\<^isub>b where ta:"\<Gamma> \<turnstile> t\<^isub>1 : Data T\<^isub>a" and "\<Gamma> \<turnstile> t\<^isub>2 : Data T\<^isub>b" 
                      and eq:"T=Data (DProd T\<^isub>a T\<^isub>b)" by auto
  have h:"\<theta> Vcloses \<Gamma>" by fact
  then obtain v\<^isub>1 v\<^isub>2 where "\<theta><t\<^isub>1> \<Down> v\<^isub>1 \<and> v\<^isub>1 \<in> V (Data T\<^isub>a)" "\<theta><t\<^isub>2> \<Down> v\<^isub>2 \<and> v\<^isub>2 \<in> V (Data T\<^isub>b)" 
    using prems by blast
  thus "\<exists>v. \<theta><Pr t\<^isub>1 t\<^isub>2> \<Down> v \<and> v \<in> V T" using eq by auto
next 
  case (Lam x e \<Gamma> \<theta> T)
  have ih:"\<And>\<theta> \<Gamma> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><e> \<Down> v \<and> v \<in> V T" by fact
  have as\<^isub>1: "\<theta> Vcloses \<Gamma>" by fact
  have as\<^isub>2: "\<Gamma> \<turnstile> Lam [x].e : T" by fact
  have fs: "x\<sharp>\<Gamma>" "x\<sharp>\<theta>" by fact
  from as\<^isub>2 fs obtain T\<^isub>1 T\<^isub>2 
    where "(i)": "(x,T\<^isub>1)#\<Gamma> \<turnstile> e:T\<^isub>2" and "(ii)": "T = T\<^isub>1 \<rightarrow> T\<^isub>2" by auto
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
  then have "\<theta><Lam [x].e> \<Down> Lam[x].\<theta><e> \<and> Lam[x].\<theta><e> \<in> V (T\<^isub>1\<rightarrow>T\<^isub>2)" using fs by auto
  thus "\<exists>v. \<theta><Lam [x].e> \<Down> v \<and> v \<in> V T" using "(ii)" by auto
next
  case (Case t' n\<^isub>1 t\<^isub>1 n\<^isub>2 t\<^isub>2 \<Gamma> \<theta> T)
  have f: "n\<^isub>1\<sharp>\<Gamma>" "n\<^isub>1\<sharp>\<theta>" "n\<^isub>2\<sharp>\<Gamma>" "n\<^isub>2\<sharp>\<theta>" "n\<^isub>2\<noteq>n\<^isub>1" "n\<^isub>1\<sharp>t'"
  "n\<^isub>1\<sharp>t\<^isub>2" "n\<^isub>2\<sharp>t'" "n\<^isub>2\<sharp>t\<^isub>1" by fact
  have h:"\<theta> Vcloses \<Gamma>" by fact
  have th:"\<Gamma> \<turnstile> Case t' of inl n\<^isub>1 \<rightarrow> t\<^isub>1 | inr n\<^isub>2 \<rightarrow> t\<^isub>2 : T" by fact
  then obtain S\<^isub>1 S\<^isub>2 where 
    hm:"\<Gamma> \<turnstile> t' : Data (DSum S\<^isub>1 S\<^isub>2)" and
    hl:"(n\<^isub>1,Data S\<^isub>1)#\<Gamma> \<turnstile> t\<^isub>1 : T" and
    hr:"(n\<^isub>2,Data S\<^isub>2)#\<Gamma> \<turnstile> t\<^isub>2 : T" using f by auto
  then obtain v\<^isub>0 where ht':"\<theta><t'> \<Down> v\<^isub>0" and hS:"v\<^isub>0 \<in> V (Data (DSum S\<^isub>1 S\<^isub>2))" using prems h by blast
  (* We distinguish between the cases InL and InR *)
  { fix v\<^isub>0'
    assume eqc:"v\<^isub>0 = InL v\<^isub>0'" and "v\<^isub>0' \<in> V' S\<^isub>1"
    then have inc: "v\<^isub>0' \<in> V (Data S\<^isub>1)" by auto
    have "valid \<Gamma>" using th typing_implies_valid by auto
    then moreover have "valid ((n\<^isub>1,Data S\<^isub>1)#\<Gamma>)" using f by auto
    then moreover have "(n\<^isub>1,v\<^isub>0')#\<theta> Vcloses (n\<^isub>1,Data S\<^isub>1)#\<Gamma>" 
      using inc h monotonicity by blast
    moreover 
    have ih:"\<And>\<Gamma> \<theta> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> t\<^isub>1 : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><t\<^isub>1> \<Down> v \<and> v \<in> V T" by fact
    ultimately obtain v\<^isub>1 where ho: "((n\<^isub>1,v\<^isub>0')#\<theta>)<t\<^isub>1> \<Down> v\<^isub>1 \<and> v\<^isub>1 \<in> V T" using hl by blast
    then have r:"\<theta><t\<^isub>1>[n\<^isub>1::=v\<^isub>0'] \<Down> v\<^isub>1 \<and> v\<^isub>1 \<in> V T" using psubst_subst_psubst f by simp
    then moreover have "n\<^isub>1\<sharp>(\<theta><t'>,\<theta><t\<^isub>2>,v\<^isub>1,n\<^isub>2)" 
      proof -
	have "n\<^isub>1\<sharp>v\<^isub>0" using ht' fresh_preserved fresh_psubst f by auto 
	then have "n\<^isub>1\<sharp>v\<^isub>0'" using eqc by auto
	then have "n\<^isub>1\<sharp>v\<^isub>1" using f r fresh_preserved fresh_subst_fresh by blast
	thus "n\<^isub>1\<sharp>(\<theta><t'>,\<theta><t\<^isub>2>,v\<^isub>1,n\<^isub>2)" using f by (simp add: fresh_atm fresh_psubst)
      qed
    moreover have "n\<^isub>2\<sharp>(\<theta><t'>,\<theta><t\<^isub>1>,v\<^isub>1,n\<^isub>1)"
      proof -
	have "n\<^isub>2\<sharp>v\<^isub>0" using ht' fresh_preserved fresh_psubst f by auto
	then have "n\<^isub>2\<sharp>v\<^isub>0'" using eqc by auto
	then have "n\<^isub>2\<sharp>((n\<^isub>1,v\<^isub>0')#\<theta>)" using f fresh_list_cons fresh_atm by force 
	then have "n\<^isub>2\<sharp>((n\<^isub>1,v\<^isub>0')#\<theta>)<t\<^isub>1>" using f fresh_psubst by auto
	moreover then have "n\<^isub>2 \<sharp> v\<^isub>1" using fresh_preserved ho by auto
	ultimately show  "n\<^isub>2\<sharp>(\<theta><t'>,\<theta><t\<^isub>1>,v\<^isub>1,n\<^isub>1)" using f by (simp add: fresh_psubst fresh_atm)
      qed
    ultimately have "Case \<theta><t'> of inl n\<^isub>1 \<rightarrow> \<theta><t\<^isub>1> | inr n\<^isub>2 \<rightarrow> \<theta><t\<^isub>2> \<Down> v\<^isub>1 \<and> v\<^isub>1 \<in> V T" using ht' eqc by auto
    moreover 
      have "Case \<theta><t'> of inl n\<^isub>1 \<rightarrow> \<theta><t\<^isub>1> | inr n\<^isub>2 \<rightarrow> \<theta><t\<^isub>2> = \<theta><Case t' of inl n\<^isub>1 \<rightarrow> t\<^isub>1 | inr n\<^isub>2 \<rightarrow> t\<^isub>2>" 
      using f by auto
    ultimately have "\<exists>v. \<theta><Case t' of inl n\<^isub>1 \<rightarrow> t\<^isub>1 | inr n\<^isub>2 \<rightarrow> t\<^isub>2> \<Down> v \<and> v \<in> V T" by auto
  }
  moreover 
  { fix v\<^isub>0'
    assume eqc:"v\<^isub>0 = InR v\<^isub>0'" and "v\<^isub>0' \<in> V' S\<^isub>2"
    then have inc:"v\<^isub>0' \<in> V (Data S\<^isub>2)" by auto
    have "valid \<Gamma>" using th typing_implies_valid by auto
    then moreover have "valid ((n\<^isub>2,Data S\<^isub>2)#\<Gamma>)" using f by auto
    then moreover have "(n\<^isub>2,v\<^isub>0')#\<theta> Vcloses (n\<^isub>2,Data S\<^isub>2)#\<Gamma>" 
      using inc h monotonicity by blast
    moreover have ih:"\<And>\<Gamma> \<theta> T. \<lbrakk>\<theta> Vcloses \<Gamma>; \<Gamma> \<turnstile> t\<^isub>2 : T\<rbrakk> \<Longrightarrow> \<exists>v. \<theta><t\<^isub>2> \<Down> v \<and> v \<in> V T" by fact
    ultimately obtain v\<^isub>2 where ho:"((n\<^isub>2,v\<^isub>0')#\<theta>)<t\<^isub>2> \<Down> v\<^isub>2 \<and> v\<^isub>2 \<in> V T" using hr by blast
    then have r:"\<theta><t\<^isub>2>[n\<^isub>2::=v\<^isub>0'] \<Down> v\<^isub>2 \<and> v\<^isub>2 \<in> V T" using psubst_subst_psubst f by simp
    moreover have "n\<^isub>1\<sharp>(\<theta><t'>,\<theta><t\<^isub>2>,v\<^isub>2,n\<^isub>2)"
    proof -
      have "n\<^isub>1\<sharp>\<theta><t'>" using fresh_psubst f by simp
      then have "n\<^isub>1\<sharp>v\<^isub>0" using ht' fresh_preserved by auto
      then have "n\<^isub>1\<sharp>v\<^isub>0'" using eqc by auto
      then have "n\<^isub>1\<sharp>((n\<^isub>2,v\<^isub>0')#\<theta>)" using f fresh_list_cons fresh_atm by force 
      then have "n\<^isub>1\<sharp>((n\<^isub>2,v\<^isub>0')#\<theta>)<t\<^isub>2>" using f fresh_psubst by auto
      moreover then have "n\<^isub>1\<sharp>v\<^isub>2" using fresh_preserved ho by auto
      ultimately show  "n\<^isub>1 \<sharp> (\<theta><t'>,\<theta><t\<^isub>2>,v\<^isub>2,n\<^isub>2)" using f by (simp add: fresh_psubst fresh_atm)
    qed
    moreover have "n\<^isub>2 \<sharp> (\<theta><t'>,\<theta><t\<^isub>1>,v\<^isub>2,n\<^isub>1)"
      proof -
	have "n\<^isub>2\<sharp>\<theta><t'>" using fresh_psubst f by simp
	then have "n\<^isub>2\<sharp>v\<^isub>0" using ht' fresh_preserved by auto
	then have "n\<^isub>2\<sharp>v\<^isub>0'" using eqc by auto
	then have "n\<^isub>2\<sharp>\<theta><t\<^isub>2>[n\<^isub>2::=v\<^isub>0']" using f fresh_subst_fresh by auto
	then have "n\<^isub>2\<sharp>v\<^isub>2" using f fresh_preserved r by blast
	then show "n\<^isub>2\<sharp>(\<theta><t'>,\<theta><t\<^isub>1>,v\<^isub>2,n\<^isub>1)" using f by (simp add: fresh_atm fresh_psubst)
      qed
    ultimately have "Case \<theta><t'> of inl n\<^isub>1 \<rightarrow> \<theta><t\<^isub>1> | inr n\<^isub>2 \<rightarrow> \<theta><t\<^isub>2> \<Down> v\<^isub>2 \<and> v\<^isub>2 \<in> V T" using ht' eqc by auto
    then have "\<exists>v. \<theta><Case t' of inl n\<^isub>1 \<rightarrow> t\<^isub>1 | inr n\<^isub>2 \<rightarrow> t\<^isub>2> \<Down> v \<and> v \<in> V T" using f by auto
  }
  ultimately show "\<exists>v. \<theta><Case t' of inl n\<^isub>1 \<rightarrow> t\<^isub>1 | inr n\<^isub>2 \<rightarrow> t\<^isub>2> \<Down> v \<and> v \<in> V T" using hS V_sum by blast
qed (force)+

theorem termination_of_evaluation:
  assumes a: "[] \<turnstile> e : T"
  shows "\<exists>v. e \<Down> v \<and> val v"
proof -
  from a have "\<exists>v. (([]::(name \<times> trm) list)<e>) \<Down> v \<and> v \<in> V T" 
    by (rule termination_aux) (auto)
  thus "\<exists>v. e \<Down> v \<and> val v" using V_are_values by auto
qed 

end
