theory CK_Machine 
  imports "HOL-Nominal.Nominal" 
begin

text \<open>
  
  This theory establishes soundness and completeness for a CK-machine
  with respect to a cbv-big-step semantics. The language includes 
  functions, recursion, booleans and numbers. In the soundness proof 
  the small-step cbv-reduction relation is used in order to get the 
  induction through. The type-preservation property is proved for the 
  machine and  also for the small- and big-step semantics. Finally, 
  the progress property is proved for the small-step semantics.

  The development is inspired by notes about context machines written
  by Roshan James (Indiana University) and also by the lecture notes 
  written by Andy Pitts for his semantics course. See
  
     \<^url>\<open>http://www.cs.indiana.edu/~rpjames/lm.pdf\<close>
     \<^url>\<open>https://www.cl.cam.ac.uk/teaching/2001/Semantics\<close>
\<close>

atom_decl name

nominal_datatype lam =
  VAR "name"
| APP "lam" "lam" 
| LAM "\<guillemotleft>name\<guillemotright>lam" (\<open>LAM [_]._\<close>)
| NUM "nat"
| DIFF "lam" "lam" (\<open>_ -- _\<close>)    (* subtraction *) 
| PLUS "lam" "lam" (\<open>_ ++ _\<close>)    (* addition *)
| TRUE
| FALSE
| IF "lam" "lam" "lam"
| FIX "\<guillemotleft>name\<guillemotright>lam" (\<open>FIX [_]._\<close>)  (* recursion *)
| ZET "lam"                      (* zero test *)
| EQI "lam" "lam"                (* equality test on numbers *)

section \<open>Capture-Avoiding Substitution\<close>

nominal_primrec
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  (\<open>_[_::=_]\<close> [100,100,100] 100)
where
  "(VAR x)[y::=s] = (if x=y then s else (VAR x))"
| "(APP t\<^sub>1 t\<^sub>2)[y::=s] = APP (t\<^sub>1[y::=s]) (t\<^sub>2[y::=s])"
| "x\<sharp>(y,s) \<Longrightarrow> (LAM [x].t)[y::=s] = LAM [x].(t[y::=s])"
| "(NUM n)[y::=s] = NUM n"
| "(t\<^sub>1 -- t\<^sub>2)[y::=s] = (t\<^sub>1[y::=s]) -- (t\<^sub>2[y::=s])"
| "(t\<^sub>1 ++ t\<^sub>2)[y::=s] = (t\<^sub>1[y::=s]) ++ (t\<^sub>2[y::=s])"
| "x\<sharp>(y,s) \<Longrightarrow> (FIX [x].t)[y::=s] = FIX [x].(t[y::=s])"
| "TRUE[y::=s] = TRUE"
| "FALSE[y::=s] = FALSE"
| "(IF t1 t2 t3)[y::=s] = IF (t1[y::=s]) (t2[y::=s]) (t3[y::=s])"
| "(ZET t)[y::=s] = ZET (t[y::=s])"
| "(EQI t1 t2)[y::=s] = EQI (t1[y::=s]) (t2[y::=s])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
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
   (auto simp add: abs_fresh fresh_prod fresh_atm fresh_nat)

lemma subst_rename: 
  assumes a: "y\<sharp>t"
  shows "t[x::=s] = ([(y,x)]\<bullet>t)[y::=s]"
using a 
by (nominal_induct t avoiding: x y s rule: lam.strong_induct)
   (auto simp add: calc_atm fresh_atm abs_fresh perm_nat_def)

section \<open>Evaluation Contexts\<close>

datatype ctx = 
    Hole (\<open>\<box>\<close>)  
  | CAPPL "ctx" "lam"
  | CAPPR "lam" "ctx"
  | CDIFFL "ctx" "lam"
  | CDIFFR "lam" "ctx"
  | CPLUSL "ctx" "lam"
  | CPLUSR "lam" "ctx"
  | CIF "ctx" "lam" "lam"
  | CZET "ctx"
  | CEQIL "ctx" "lam"
  | CEQIR "lam" "ctx"

text \<open>The operation of filling a term into a context:\<close> 

fun
  filling :: "ctx \<Rightarrow> lam \<Rightarrow> lam" (\<open>_\<lbrakk>_\<rbrakk>\<close>)
where
  "\<box>\<lbrakk>t\<rbrakk> = t"
| "(CAPPL E t')\<lbrakk>t\<rbrakk> = APP (E\<lbrakk>t\<rbrakk>) t'"
| "(CAPPR t' E)\<lbrakk>t\<rbrakk> = APP t' (E\<lbrakk>t\<rbrakk>)"
| "(CDIFFL E t')\<lbrakk>t\<rbrakk> = (E\<lbrakk>t\<rbrakk>) -- t'"
| "(CDIFFR t' E)\<lbrakk>t\<rbrakk> = t' -- (E\<lbrakk>t\<rbrakk>)"
| "(CPLUSL E t')\<lbrakk>t\<rbrakk> = (E\<lbrakk>t\<rbrakk>) ++ t'"
| "(CPLUSR t' E)\<lbrakk>t\<rbrakk> = t' ++ (E\<lbrakk>t\<rbrakk>)"
| "(CIF E t1 t2)\<lbrakk>t\<rbrakk> = IF (E\<lbrakk>t\<rbrakk>) t1 t2"
| "(CZET E)\<lbrakk>t\<rbrakk> = ZET (E\<lbrakk>t\<rbrakk>)"
| "(CEQIL E t')\<lbrakk>t\<rbrakk> = EQI (E\<lbrakk>t\<rbrakk>) t'"
| "(CEQIR t' E)\<lbrakk>t\<rbrakk> = EQI t' (E\<lbrakk>t\<rbrakk>)"

text \<open>The operation of composing two contexts:\<close>

fun 
 ctx_compose :: "ctx \<Rightarrow> ctx \<Rightarrow> ctx" (\<open>_ \<circ> _\<close>)
where
  "\<box> \<circ> E' = E'"
| "(CAPPL E t') \<circ> E' = CAPPL (E \<circ> E') t'"
| "(CAPPR t' E) \<circ> E' = CAPPR t' (E \<circ> E')"
| "(CDIFFL E t') \<circ> E' = CDIFFL (E \<circ> E') t'"
| "(CDIFFR t' E) \<circ> E' = CDIFFR t' (E \<circ> E')"
| "(CPLUSL E t') \<circ> E' = CPLUSL (E \<circ> E') t'"
| "(CPLUSR t' E) \<circ> E' = CPLUSR t' (E \<circ> E')"
| "(CIF E t1 t2) \<circ> E' = CIF (E \<circ> E') t1 t2"
| "(CZET E) \<circ> E' = CZET (E \<circ> E')"
| "(CEQIL E t') \<circ> E' = CEQIL (E \<circ> E') t'"
| "(CEQIR t' E) \<circ> E' = CEQIR t' (E \<circ> E')"

lemma ctx_compose:
  shows "(E1 \<circ> E2)\<lbrakk>t\<rbrakk> = E1\<lbrakk>E2\<lbrakk>t\<rbrakk>\<rbrakk>"
by (induct E1 rule: ctx.induct) (auto)

text \<open>Composing a list (stack) of contexts.\<close>

fun
  ctx_composes :: "ctx list \<Rightarrow> ctx" (\<open>_\<down>\<close>)
where
    "[]\<down> = \<box>"
  | "(E#Es)\<down> = (Es\<down>) \<circ> E"

section \<open>The CK-Machine\<close>

inductive
  val :: "lam\<Rightarrow>bool" 
where
  v_LAM[intro]:   "val (LAM [x].e)"
| v_NUM[intro]:   "val (NUM n)"  
| v_FALSE[intro]: "val FALSE"
| v_TRUE[intro]:  "val TRUE"

equivariance val 

inductive
  machine :: "lam\<Rightarrow>ctx list\<Rightarrow>lam\<Rightarrow>ctx list\<Rightarrow>bool" (\<open><_,_> \<leadsto> <_,_>\<close>)
where
  m1[intro]: "<APP e1 e2,Es> \<leadsto> <e1,(CAPPL \<box> e2)#Es>"
| m2[intro]: "val v \<Longrightarrow> <v,(CAPPL \<box> e2)#Es> \<leadsto> <e2,(CAPPR v \<box>)#Es>"
| m3[intro]: "val v \<Longrightarrow> <v,(CAPPR (LAM [y].e) \<box>)#Es> \<leadsto> <e[y::=v],Es>"
| m4[intro]: "<e1 -- e2, Es> \<leadsto> <e1,(CDIFFL \<box> e2)#Es>"
| m5[intro]: "<NUM n1,(CDIFFL \<box> e2)#Es> \<leadsto> <e2,(CDIFFR (NUM n1) \<box>)#Es>"
| m6[intro]: "<NUM n2,(CDIFFR (NUM n1) \<box>)#Es> \<leadsto> <NUM (n1 - n2),Es>"
| m4'[intro]:"<e1 ++ e2, Es> \<leadsto> <e1,(CPLUSL \<box> e2)#Es>"
| m5'[intro]:"<NUM n1,(CPLUSL \<box> e2)#Es> \<leadsto> <e2,(CPLUSR (NUM n1) \<box>)#Es>"
| m6'[intro]:"<NUM n2,(CPLUSR (NUM n1) \<box>)#Es> \<leadsto> <NUM (n1+n2),Es>"
| m7[intro]: "<IF e1 e2 e3,Es> \<leadsto> <e1,(CIF \<box> e2 e3)#Es>"
| m8[intro]: "<TRUE,(CIF \<box> e1 e2)#Es> \<leadsto> <e1,Es>"
| m9[intro]: "<FALSE,(CIF \<box> e1 e2)#Es> \<leadsto> <e2,Es>"
| mA[intro]: "<FIX [x].t,Es> \<leadsto> <t[x::=FIX [x].t],Es>"
| mB[intro]: "<ZET e,Es> \<leadsto> <e,(CZET \<box>)#Es>"
| mC[intro]: "<NUM 0,(CZET \<box>)#Es> \<leadsto> <TRUE,Es>"
| mD[intro]: "0 < n \<Longrightarrow> <NUM n,(CZET \<box>)#Es> \<leadsto> <FALSE,Es>"
| mE[intro]: "<EQI e1 e2,Es> \<leadsto> <e1,(CEQIL \<box> e2)#Es>"
| mF[intro]: "<NUM n1,(CEQIL \<box> e2)#Es> \<leadsto> <e2,(CEQIR (NUM n1) \<box>)#Es>"
| mG[intro]: "<NUM n,(CEQIR (NUM n) \<box>)#Es> \<leadsto> <TRUE,Es>"
| mH[intro]: "n1\<noteq>n2 \<Longrightarrow> <NUM n1,(CEQIR (NUM n2) \<box>)#Es> \<leadsto> <FALSE,Es>"

inductive 
  "machine_star" :: "lam\<Rightarrow>ctx list\<Rightarrow>lam\<Rightarrow>ctx list\<Rightarrow>bool" (\<open><_,_> \<leadsto>* <_,_>\<close>)
where
  ms1[intro]: "<e,Es> \<leadsto>* <e,Es>"
| ms2[intro]: "\<lbrakk><e1,Es1> \<leadsto> <e2,Es2>; <e2,Es2> \<leadsto>* <e3,Es3>\<rbrakk> \<Longrightarrow> <e1,Es1> \<leadsto>* <e3,Es3>"

lemma ms3[intro,trans]:
  assumes a: "<e1,Es1> \<leadsto>* <e2,Es2>" "<e2,Es2> \<leadsto>* <e3,Es3>"
  shows "<e1,Es1> \<leadsto>* <e3,Es3>"
using a by (induct) (auto) 

lemma ms4[intro]:
  assumes a: "<e1,Es1> \<leadsto> <e2,Es2>" 
  shows "<e1,Es1> \<leadsto>* <e2,Es2>"
using a by (rule ms2) (rule ms1)

section \<open>The Evaluation Relation (Big-Step Semantics)\<close>

inductive
  eval :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open>_ \<Down> _\<close>) 
where
  eval_NUM[intro]:  "NUM n \<Down> NUM n" 
| eval_DIFF[intro]: "\<lbrakk>t1 \<Down> (NUM n1); t2 \<Down> (NUM n2)\<rbrakk> \<Longrightarrow> t1 -- t2 \<Down> NUM (n1 - n2)"
| eval_PLUS[intro]: "\<lbrakk>t1 \<Down> (NUM n1); t2 \<Down> (NUM n2)\<rbrakk> \<Longrightarrow> t1 ++ t2 \<Down> NUM (n1 + n2)"
| eval_LAM[intro]:  "LAM [x].t \<Down> LAM [x].t"
| eval_APP[intro]:  "\<lbrakk>t1\<Down> LAM [x].t; t2\<Down> t2'; t[x::=t2']\<Down> t'\<rbrakk> \<Longrightarrow> APP t1 t2 \<Down> t'"
| eval_FIX[intro]:  "t[x::= FIX [x].t] \<Down> t' \<Longrightarrow> FIX [x].t \<Down> t'"
| eval_IF1[intro]:  "\<lbrakk>t1 \<Down> TRUE; t2 \<Down> t'\<rbrakk> \<Longrightarrow> IF t1 t2 t3 \<Down> t'"
| eval_IF2[intro]:  "\<lbrakk>t1 \<Down> FALSE; t3 \<Down> t'\<rbrakk> \<Longrightarrow> IF t1 t2 t3 \<Down> t'"
| eval_TRUE[intro]: "TRUE \<Down> TRUE"
| eval_FALSE[intro]:"FALSE \<Down> FALSE"
| eval_ZET1[intro]: "t \<Down> NUM 0 \<Longrightarrow> ZET t \<Down> TRUE"
| eval_ZET2[intro]: "\<lbrakk>t \<Down> NUM n; 0 < n\<rbrakk> \<Longrightarrow> ZET t \<Down> FALSE"
| eval_EQ1[intro]:  "\<lbrakk>t1 \<Down> NUM n; t2 \<Down> NUM n\<rbrakk> \<Longrightarrow> EQI t1 t2 \<Down> TRUE"
| eval_EQ2[intro]:  "\<lbrakk>t1 \<Down> NUM n1; t2 \<Down> NUM n2; n1\<noteq>n2\<rbrakk> \<Longrightarrow> EQI t1 t2 \<Down> FALSE"

declare lam.inject[simp]
inductive_cases eval_elim:
  "APP t1 t2 \<Down> t'"
  "IF t1 t2 t3 \<Down> t'"
  "ZET t \<Down> t'"
  "EQI t1 t2 \<Down> t'"
  "t1 ++ t2 \<Down> t'"
  "t1 -- t2 \<Down> t'"
  "(NUM n) \<Down> t"
  "TRUE \<Down> t"
  "FALSE \<Down> t"
declare lam.inject[simp del]

lemma eval_to:
  assumes a: "t \<Down> t'"
  shows "val t'"
using a by (induct) (auto)

lemma eval_val:
  assumes a: "val t"
  shows "t \<Down> t"
using a by (induct) (auto)

text \<open>The Completeness Property:\<close>

theorem eval_implies_machine_star_ctx:
  assumes a: "t \<Down> t'"
  shows "<t,Es> \<leadsto>* <t',Es>"
using a
by (induct arbitrary: Es)
   (metis eval_to machine.intros ms1 ms2 ms3 ms4 v_LAM)+

corollary eval_implies_machine_star:
  assumes a: "t \<Down> t'"
  shows "<t,[]> \<leadsto>* <t',[]>"
using a by (auto dest: eval_implies_machine_star_ctx)

section \<open>The CBV Reduction Relation (Small-Step Semantics)\<close>

lemma less_eqvt[eqvt]:
  fixes pi::"name prm"
  and   n1 n2::"nat"
  shows "(pi\<bullet>(n1 < n2)) = ((pi\<bullet>n1) < (pi\<bullet>n2))"
by (simp add: perm_nat_def perm_bool)

inductive
  cbv :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open>_ \<longrightarrow>cbv _\<close>) 
where
  cbv1: "\<lbrakk>val v; x\<sharp>v\<rbrakk> \<Longrightarrow> APP (LAM [x].t) v \<longrightarrow>cbv t[x::=v]"
| cbv2[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> APP t t2 \<longrightarrow>cbv APP t' t2"
| cbv3[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> APP t2 t \<longrightarrow>cbv APP t2 t'"
| cbv4[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> t -- t2 \<longrightarrow>cbv t' -- t2"
| cbv5[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> t2 -- t \<longrightarrow>cbv t2 -- t'"
| cbv6[intro]: "(NUM n1) -- (NUM n2) \<longrightarrow>cbv NUM (n1 - n2)"
| cbv4'[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> t ++ t2 \<longrightarrow>cbv t' ++ t2"
| cbv5'[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> t2 ++ t \<longrightarrow>cbv t2 ++ t'"
| cbv6'[intro]:"(NUM n1) ++ (NUM n2) \<longrightarrow>cbv NUM (n1 + n2)"
| cbv7[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> IF t t1 t2 \<longrightarrow>cbv IF t' t1 t2"
| cbv8[intro]: "IF TRUE t1 t2 \<longrightarrow>cbv t1"
| cbv9[intro]: "IF FALSE t1 t2 \<longrightarrow>cbv t2"
| cbvA[intro]: "FIX [x].t \<longrightarrow>cbv t[x::=FIX [x].t]"
| cbvB[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> ZET t \<longrightarrow>cbv ZET t'"
| cbvC[intro]: "ZET (NUM 0) \<longrightarrow>cbv TRUE"
| cbvD[intro]: "0 < n \<Longrightarrow> ZET (NUM n) \<longrightarrow>cbv FALSE"
| cbvE[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> EQI t t2 \<longrightarrow>cbv EQI t' t2"
| cbvF[intro]: "t \<longrightarrow>cbv t' \<Longrightarrow> EQI t2 t \<longrightarrow>cbv EQI t2 t'"
| cbvG[intro]: "EQI (NUM n) (NUM n) \<longrightarrow>cbv TRUE"
| cbvH[intro]: "n1\<noteq>n2 \<Longrightarrow> EQI (NUM n1) (NUM n2) \<longrightarrow>cbv FALSE"

equivariance cbv
nominal_inductive cbv
 by (simp_all add: abs_fresh fresh_fact)

lemma better_cbv1[intro]: 
  assumes a: "val v" 
  shows "APP (LAM [x].t) v \<longrightarrow>cbv t[x::=v]"
proof -
  obtain y::"name" where fs: "y\<sharp>(x,t,v)" by (rule exists_fresh, rule fin_supp, blast)
  have "APP (LAM [x].t) v = APP (LAM [y].([(y,x)]\<bullet>t)) v" using fs
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  also have "\<dots> \<longrightarrow>cbv  ([(y,x)]\<bullet>t)[y::=v]" using fs a by (auto simp add: cbv.eqvt cbv1)
  also have "\<dots> = t[x::=v]" using fs by (simp add: subst_rename[symmetric])
  finally show "APP (LAM [x].t) v \<longrightarrow>cbv t[x::=v]" by simp
qed

inductive 
  "cbv_star" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (\<open> _ \<longrightarrow>cbv* _\<close>)
where
  cbvs1[intro]: "e \<longrightarrow>cbv* e"
| cbvs2[intro]: "\<lbrakk>e1\<longrightarrow>cbv e2; e2 \<longrightarrow>cbv* e3\<rbrakk> \<Longrightarrow> e1 \<longrightarrow>cbv* e3"

lemma cbvs3[intro,trans]:
  assumes a: "e1 \<longrightarrow>cbv* e2" "e2 \<longrightarrow>cbv* e3"
  shows "e1 \<longrightarrow>cbv* e3"
using a by (induct) (auto) 

lemma cbv_in_ctx:
  assumes a: "t \<longrightarrow>cbv t'"
  shows "E\<lbrakk>t\<rbrakk> \<longrightarrow>cbv E\<lbrakk>t'\<rbrakk>"
using a by (induct E) (auto)

lemma machine_implies_cbv_star_ctx:
  assumes a: "<e,Es> \<leadsto> <e',Es'>"
  shows "(Es\<down>)\<lbrakk>e\<rbrakk> \<longrightarrow>cbv* (Es'\<down>)\<lbrakk>e'\<rbrakk>"
using a by (induct) (auto simp add: ctx_compose intro: cbv_in_ctx)

lemma machine_star_implies_cbv_star_ctx:
  assumes a: "<e,Es> \<leadsto>* <e',Es'>"
  shows "(Es\<down>)\<lbrakk>e\<rbrakk> \<longrightarrow>cbv* (Es'\<down>)\<lbrakk>e'\<rbrakk>"
using a 
by (induct) (auto dest: machine_implies_cbv_star_ctx)

lemma machine_star_implies_cbv_star:
  assumes a: "<e,[]> \<leadsto>* <e',[]>"
  shows "e \<longrightarrow>cbv* e'"
using a by (auto dest: machine_star_implies_cbv_star_ctx)

lemma cbv_eval:
  assumes a: "t1 \<longrightarrow>cbv t2" "t2 \<Down> t3"
  shows "t1 \<Down> t3"
using a
by (induct arbitrary: t3)
   (auto elim!: eval_elim intro: eval_val)

lemma cbv_star_eval:
  assumes a: "t1 \<longrightarrow>cbv* t2" "t2 \<Down> t3"
  shows "t1 \<Down> t3"
using a by (induct) (auto simp add: cbv_eval)

lemma cbv_star_implies_eval:
  assumes a: "t \<longrightarrow>cbv* v" "val v"
  shows "t \<Down> v"
using a
by (induct)
   (auto simp add: eval_val cbv_star_eval dest: cbvs2)

text \<open>The Soundness Property\<close>

theorem machine_star_implies_eval:
  assumes a: "<t1,[]> \<leadsto>* <t2,[]>" 
  and     b: "val t2" 
  shows "t1 \<Down> t2"
proof -
  from a have "t1 \<longrightarrow>cbv* t2" by (simp add: machine_star_implies_cbv_star)
  then show "t1 \<Down> t2" using b by (simp add: cbv_star_implies_eval)
qed

section \<open>Typing\<close>

text \<open>Types\<close>

nominal_datatype ty =
  tVAR "string"
| tBOOL 
| tINT
| tARR "ty" "ty" (\<open>_ \<rightarrow> _\<close>)

declare ty.inject[simp]

lemma ty_fresh:
  fixes x::"name"
  and   T::"ty"
  shows "x\<sharp>T"
by (induct T rule: ty.induct)
   (auto simp add: fresh_string)

text \<open>Typing Contexts\<close>

type_synonym tctx = "(name\<times>ty) list"

text \<open>Sub-Typing Contexts\<close>

abbreviation
  "sub_tctx" :: "tctx \<Rightarrow> tctx \<Rightarrow> bool" (\<open>_ \<subseteq> _\<close>) 
where
  "\<Gamma>\<^sub>1 \<subseteq> \<Gamma>\<^sub>2 \<equiv> \<forall>x. x \<in> set \<Gamma>\<^sub>1 \<longrightarrow> x \<in> set \<Gamma>\<^sub>2"

text \<open>Valid Typing Contexts\<close>

inductive
  valid :: "tctx \<Rightarrow> bool"
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

section \<open>The Typing Relation\<close>

inductive
  typing :: "tctx \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" (\<open>_ \<turnstile> _ : _\<close>) 
where
  t_VAR[intro]:  "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> VAR x : T"
| t_APP[intro]:  "\<lbrakk>\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1\<rightarrow>T\<^sub>2; \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> APP t\<^sub>1 t\<^sub>2 : T\<^sub>2"
| t_LAM[intro]:  "\<lbrakk>x\<sharp>\<Gamma>; (x,T\<^sub>1)#\<Gamma> \<turnstile> t : T\<^sub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> LAM [x].t : T\<^sub>1 \<rightarrow> T\<^sub>2"
| t_NUM[intro]:  "\<Gamma> \<turnstile> (NUM n) : tINT"
| t_DIFF[intro]: "\<lbrakk>\<Gamma> \<turnstile> t\<^sub>1 : tINT; \<Gamma> \<turnstile> t\<^sub>2 : tINT\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 -- t\<^sub>2 : tINT"
| t_PLUS[intro]: "\<lbrakk>\<Gamma> \<turnstile> t\<^sub>1 : tINT; \<Gamma> \<turnstile> t\<^sub>2 : tINT\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 ++ t\<^sub>2 : tINT"
| t_TRUE[intro]:  "\<Gamma> \<turnstile> TRUE : tBOOL"
| t_FALSE[intro]: "\<Gamma> \<turnstile> FALSE : tBOOL"
| t_IF[intro]:    "\<lbrakk>\<Gamma> \<turnstile> t1 : tBOOL; \<Gamma> \<turnstile> t2 : T; \<Gamma> \<turnstile> t3 : T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> IF t1 t2 t3 : T"
| t_ZET[intro]:   "\<Gamma> \<turnstile> t : tINT \<Longrightarrow> \<Gamma> \<turnstile> ZET t : tBOOL"
| t_EQI[intro]:   "\<lbrakk>\<Gamma> \<turnstile> t1 : tINT; \<Gamma> \<turnstile> t2 : tINT\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EQI t1 t2 : tBOOL"
| t_FIX[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T)#\<Gamma> \<turnstile> t : T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> FIX [x].t : T"  

declare lam.inject[simp]
inductive_cases typing_inversion[elim]:
  "\<Gamma> \<turnstile> t\<^sub>1 -- t\<^sub>2 : T"
  "\<Gamma> \<turnstile> t\<^sub>1 ++ t\<^sub>2 : T"
  "\<Gamma> \<turnstile> IF t1 t2 t3 : T"
  "\<Gamma> \<turnstile> ZET t : T"
  "\<Gamma> \<turnstile> EQI t1 t2 : T"
  "\<Gamma> \<turnstile> APP t1 t2 : T"
  "\<Gamma> \<turnstile> TRUE : T"
  "\<Gamma> \<turnstile> FALSE : T"
  "\<Gamma> \<turnstile> NUM n : T"
declare lam.inject[simp del]

equivariance typing
nominal_inductive typing
  by (simp_all add: abs_fresh ty_fresh)

lemma t_LAM_inversion[dest]:
  assumes ty: "\<Gamma> \<turnstile> LAM [x].t : T" 
  and     fc: "x\<sharp>\<Gamma>" 
  shows "\<exists>T\<^sub>1 T\<^sub>2. T = T\<^sub>1 \<rightarrow> T\<^sub>2 \<and> (x,T\<^sub>1)#\<Gamma> \<turnstile> t : T\<^sub>2"
using ty fc 
by (cases rule: typing.strong_cases) 
   (auto simp add: alpha lam.inject abs_fresh ty_fresh)

lemma t_FIX_inversion[dest]:
  assumes ty: "\<Gamma> \<turnstile> FIX [x].t : T" 
  and     fc: "x\<sharp>\<Gamma>" 
  shows "(x,T)#\<Gamma> \<turnstile> t : T"
using ty fc 
by (cases rule: typing.strong_cases) 
   (auto simp add: alpha lam.inject abs_fresh ty_fresh)

section \<open>The Type-Preservation Property for the CBV Reduction Relation\<close>

lemma weakening: 
  fixes \<Gamma>1 \<Gamma>2::"tctx"
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
proof (nominal_induct "\<Delta>@[(x,T')]@\<Gamma>" e T avoiding: x e' \<Delta> rule: typing.strong_induct)
  case (t_VAR y T x e' \<Delta>)
  then have a1: "valid (\<Delta>@[(x,T')]@\<Gamma>)" 
       and  a2: "(y,T) \<in> set (\<Delta>@[(x,T')]@\<Gamma>)" 
       and  a3: "\<Gamma> \<turnstile> e' : T'" .
  from a1 have a4: "valid (\<Delta>@\<Gamma>)" by (rule valid_insert)
  { assume eq: "x=y"
    from a1 a2 have "T=T'" using eq by (auto intro: context_unique)
    with a3 have "\<Delta>@\<Gamma> \<turnstile> VAR y[x::=e'] : T" using eq a4 by (auto intro: weakening)
  }
  moreover
  { assume ineq: "x\<noteq>y"
    from a2 have "(y,T) \<in> set (\<Delta>@\<Gamma>)" using ineq by simp
    then have "\<Delta>@\<Gamma> \<turnstile> VAR y[x::=e'] : T" using ineq a4 by auto
  }
  ultimately show "\<Delta>@\<Gamma> \<turnstile> VAR y[x::=e'] : T" by blast
qed (auto | force simp add: fresh_list_append fresh_list_cons)+

corollary type_substitution:
  assumes a: "(x,T')#\<Gamma> \<turnstile> e : T"
  and     b: "\<Gamma> \<turnstile> e' : T'"
  shows "\<Gamma> \<turnstile> e[x::=e'] : T"
using a b
by (auto intro: type_substitution_aux[where \<Delta>="[]",simplified])

theorem cbv_type_preservation:
  assumes a: "t \<longrightarrow>cbv t'"
  and     b: "\<Gamma> \<turnstile> t : T" 
  shows "\<Gamma> \<turnstile> t' : T"
using a b
apply(nominal_induct avoiding: \<Gamma> T rule: cbv.strong_induct)
apply(auto elim!: typing_inversion dest: t_LAM_inversion simp add: type_substitution)
apply(frule t_FIX_inversion)
apply(auto simp add: type_substitution)
done

corollary cbv_star_type_preservation:
  assumes a: "t \<longrightarrow>cbv* t'"
  and     b: "\<Gamma> \<turnstile> t : T" 
  shows "\<Gamma> \<turnstile> t' : T"
using a b
by (induct) (auto intro: cbv_type_preservation)

section \<open>The Type-Preservation Property for the Machine and Evaluation Relation\<close>

theorem machine_type_preservation:
  assumes a: "<t,[]> \<leadsto>* <t',[]>"
  and     b: "\<Gamma> \<turnstile> t : T" 
  shows "\<Gamma> \<turnstile> t' : T"
proof -
  from a have "t \<longrightarrow>cbv* t'" by (simp add: machine_star_implies_cbv_star)
  then show "\<Gamma> \<turnstile> t' : T" using b by (simp add: cbv_star_type_preservation)
qed

theorem eval_type_preservation:
  assumes a: "t \<Down> t'"
  and     b: "\<Gamma> \<turnstile> t : T" 
  shows "\<Gamma> \<turnstile> t' : T"
proof -
  from a have "<t,[]> \<leadsto>* <t',[]>" by (simp add: eval_implies_machine_star)
  then show "\<Gamma> \<turnstile> t' : T" using b by (simp add: machine_type_preservation)
qed

text \<open>The Progress Property\<close>

lemma canonical_tARR[dest]:
  assumes a: "[] \<turnstile> t : T1 \<rightarrow> T2"
  and     b: "val t"
  shows "\<exists>x t'. t = LAM [x].t'"
using b a by (induct) (auto) 

lemma canonical_tINT[dest]:
  assumes a: "[] \<turnstile> t : tINT"
  and     b: "val t"
  shows "\<exists>n. t = NUM n"
using b a 
by (induct) (auto simp add: fresh_list_nil)

lemma canonical_tBOOL[dest]:
  assumes a: "[] \<turnstile> t : tBOOL"
  and     b: "val t"
  shows "t = TRUE \<or> t = FALSE"
using b a 
by (induct) (auto simp add: fresh_list_nil)

theorem progress:
  assumes a: "[] \<turnstile> t : T"
  shows "(\<exists>t'. t \<longrightarrow>cbv t') \<or> (val t)"
using a
by (induct \<Gamma>\<equiv>"[]::tctx" t T)
   (auto dest!: canonical_tINT intro!: cbv.intros gr0I)

end

