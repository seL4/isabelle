(* $Id$ *)

theory Contexts
imports "../Nominal"
begin

text {* 
  
  We show here that the Plotkin-style of defining
  beta-reduction (based on congruence rules) is
  equivalent to the Felleisen-Hieb-style representation 
  (based on contexts). We also define cbv-evaluation 
  via a CK-machine described by Roshan James.
  
  The interesting point in this theory is that contexts 
  do not contain any binders. On the other hand the operation 
  of filling a term into a context produces an alpha-equivalent 
  term. 

*}

atom_decl name

text {* 
  Lambda-Terms - the Lam-term constructor binds a name
*}
nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {* 
  Contexts - the lambda case in contexts does not bind 
  a name, even if we introduce the notation [_]._ for CLam.
*}

nominal_datatype ctx = 
    Hole ("\<box>" 1000)  
  | CAppL "ctx" "lam"
  | CAppR "lam" "ctx" 
  | CLam "name" "ctx"  ("CLam [_]._" [100,100] 100) 

text {* Capture-avoiding substitution *}

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

text {*
  Filling is the operation that fills a term into a hole. 
  This operation is possibly capturing.
*}

consts 
  filling :: "ctx \<Rightarrow> lam \<Rightarrow> lam" ("_\<lbrakk>_\<rbrakk>" [100,100] 100)

nominal_primrec
  "\<box>\<lbrakk>t\<rbrakk> = t"
  "(CAppL E t')\<lbrakk>t\<rbrakk> = App (E\<lbrakk>t\<rbrakk>) t'"
  "(CAppR t' E)\<lbrakk>t\<rbrakk> = App t' (E\<lbrakk>t\<rbrakk>)"
  "(CLam [x].E)\<lbrakk>t\<rbrakk> = Lam [x].(E\<lbrakk>t\<rbrakk>)" 
by (rule TrueI)+

text {* 
  While contexts themselves are not alpha-equivalence classes, the 
  filling operation produces an alpha-equivalent lambda-term. 
*}

lemma alpha_test: 
  shows "x\<noteq>y \<Longrightarrow> (CLam [x].\<box>) \<noteq> (CLam [y].\<box>)"
  and   "(CLam [x].\<box>)\<lbrakk>Var x\<rbrakk> = (CLam [y].\<box>)\<lbrakk>Var y\<rbrakk>"
by (auto simp add: alpha ctx.inject lam.inject calc_atm fresh_atm) 

text {* The composition of two contexts. *}

consts 
 ctx_compose :: "ctx \<Rightarrow> ctx \<Rightarrow> ctx" ("_ \<circ> _" [100,100] 100)

nominal_primrec
  "\<box> \<circ> E' = E'"
  "(CAppL E t') \<circ> E' = CAppL (E \<circ> E') t'"
  "(CAppR t' E) \<circ> E' = CAppR t' (E \<circ> E')"
  "(CLam [x].E) \<circ> E' = CLam [x].(E \<circ> E')"
by (rule TrueI)+
  
lemma ctx_compose:
  shows "(E1 \<circ> E2)\<lbrakk>t\<rbrakk> = E1\<lbrakk>E2\<lbrakk>t\<rbrakk>\<rbrakk>"
by (induct E1 rule: ctx.induct) (auto)

text {* Beta-reduction via contexts in the Felleisen-Hieb style. *}

inductive
  ctx_red :: "lam\<Rightarrow>lam\<Rightarrow>bool" ("_ \<longrightarrow>x _" [80,80] 80) 
where
  xbeta[intro]: "E\<lbrakk>App (Lam [x].t) t'\<rbrakk> \<longrightarrow>x E\<lbrakk>t[x::=t']\<rbrakk>" 

text {* Beta-reduction via congruence rules in the Plotkin style. *}

inductive
  cong_red :: "lam\<Rightarrow>lam\<Rightarrow>bool" ("_ \<longrightarrow>o _" [80,80] 80) 
where
  obeta[intro]: "App (Lam [x].t) t' \<longrightarrow>o t[x::=t']"
| oapp1[intro]: "t \<longrightarrow>o t' \<Longrightarrow> App t t2 \<longrightarrow>o App t' t2"
| oapp2[intro]: "t \<longrightarrow>o t' \<Longrightarrow> App t2 t \<longrightarrow>o App t2 t'"
| olam[intro]:  "t \<longrightarrow>o t' \<Longrightarrow> Lam [x].t \<longrightarrow>o Lam [x].t'"

text {* The proof that shows both relations are equal. *}

lemma cong_red_in_ctx:
  assumes a: "t \<longrightarrow>o t'"
  shows "E\<lbrakk>t\<rbrakk> \<longrightarrow>o E\<lbrakk>t'\<rbrakk>"
using a
by (induct E rule: ctx.induct) (auto)

lemma ctx_red_in_ctx:
  assumes a: "t \<longrightarrow>x t'"
  shows "E\<lbrakk>t\<rbrakk> \<longrightarrow>x E\<lbrakk>t'\<rbrakk>"
using a
by (induct) (auto simp add: ctx_compose[symmetric])

theorem ctx_red_implies_cong_red:
  assumes a: "t \<longrightarrow>x t'"
  shows "t \<longrightarrow>o t'"
using a by (induct) (auto intro: cong_red_in_ctx)

theorem cong_red_implies_ctx_red:
  assumes a: "t \<longrightarrow>o t'"
  shows "t \<longrightarrow>x t'"
using a
proof (induct)
  case (obeta x t' t)
  have "\<box>\<lbrakk>App (Lam [x].t) t'\<rbrakk> \<longrightarrow>x \<box>\<lbrakk>t[x::=t']\<rbrakk>" by (rule xbeta) 
  then show  "App (Lam [x].t) t' \<longrightarrow>x t[x::=t']" by simp
qed (metis ctx_red_in_ctx filling.simps)+ (* found by SledgeHammer *)

lemma ctx_existence:
  assumes a: "t \<longrightarrow>o t'"
  shows "\<exists>C s s'. t = C\<lbrakk>s\<rbrakk> \<and> t' = C\<lbrakk>s'\<rbrakk> \<and> s \<longrightarrow>o s'"
using a
by (induct) (metis cong_red.intros filling.simps)+

section {* We now use context in a CBV list machine *}

text {* First, a function that composes a list of contexts. *}

primrec
  ctx_composes :: "ctx list \<Rightarrow> ctx" ("_\<down>" [80] 80)
where
    "[]\<down> = \<box>"
  | "(E#Es)\<down> = (Es\<down>) \<circ> E"    

text {* Values *}

inductive
  val :: "lam\<Rightarrow>bool" 
where
   v_Lam[intro]: "val (Lam [x].e)"
 | v_Var[intro]: "val (Var x)"

text {* CBV-reduction using contexts *}

inductive
  cbv :: "lam\<Rightarrow>lam\<Rightarrow>bool" ("_ \<longrightarrow>cbv _" [80,80] 80) 
where
  cbv_beta[intro]: "val v \<Longrightarrow> E\<lbrakk>App (Lam [x].e) v\<rbrakk> \<longrightarrow>cbv E\<lbrakk>e[x::=v]\<rbrakk>"

text {* reflexive, transitive closure of CBV reduction *}
inductive 
  "cbv_star" :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>cbv* _" [80,80] 80)
where
  cbvs1[intro]: "e \<longrightarrow>cbv* e"
| cbvs2[intro]: "e \<longrightarrow>cbv e' \<Longrightarrow> e \<longrightarrow>cbv* e'"
| cbvs3[intro,trans]: "\<lbrakk>e1\<longrightarrow>cbv* e2; e2 \<longrightarrow>cbv* e3\<rbrakk> \<Longrightarrow> e1 \<longrightarrow>cbv* e3"

text {* A little CK-machine, which builds up a list of evaluation contexts. *}

inductive
  machine :: "lam\<Rightarrow>ctx list\<Rightarrow>lam\<Rightarrow>ctx list\<Rightarrow>bool" ("<_,_> \<mapsto> <_,_>" [60,60,60,60] 60)
where
  m1[intro]: "<App e1 e2, Es> \<mapsto> <e1,(CAppL \<box> e2)#Es>"
| m2[intro]: "val v \<Longrightarrow> <v,(CAppL \<box> e2)#Es> \<mapsto> <e2,(CAppR v \<box>)#Es>"
| m3[intro]: "val v \<Longrightarrow> <v,(CAppR (Lam [x].e) \<box>)#Es> \<mapsto> <e[x::=v],Es>"

lemma machine_red_implies_cbv_reds_aux:
  assumes a: "<e,Es> \<mapsto> <e',Es'>"
  shows "(Es\<down>)\<lbrakk>e\<rbrakk> \<longrightarrow>cbv* (Es'\<down>)\<lbrakk>e'\<rbrakk>"
using a by (induct) (auto simp add: ctx_compose)

lemma machine_execution_implies_cbv_reds:
  assumes a: "<e,[]> \<mapsto> <e',[]>"
  shows "e \<longrightarrow>cbv* e'"
using a by (auto dest: machine_red_implies_cbv_reds_aux)

text {*
  One would now like to show something about the opposite
  direction, by according to Amr Sabry this amounts to
  showing a standardisation lemma, which is hard.
  *}

end
