theory Contexts
imports "../Nominal"
begin

text {* 
  
  We show here that the Plotkin-style of defining
  beta-reduction (based on congruence rules) is
  equivalent to the Felleisen-Hieb-style representation 
  (based on contexts). 
  
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

text {* Capture-Avoiding Substitution *}

nominal_primrec
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [100,100,100] 100)
where
  "(Var x)[y::=s] = (if x=y then s else (Var x))"
| "(App t\<^isub>1 t\<^isub>2)[y::=s] = App (t\<^isub>1[y::=s]) (t\<^isub>2[y::=s])"
| "x\<sharp>(y,s) \<Longrightarrow> (Lam [x].t)[y::=s] = Lam [x].(t[y::=s])"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess)+
done

text {*
  Filling is the operation that fills a term into a hole. 
  This operation is possibly capturing.
*}

nominal_primrec
  filling :: "ctx \<Rightarrow> lam \<Rightarrow> lam" ("_\<lbrakk>_\<rbrakk>" [100,100] 100)
where
  "\<box>\<lbrakk>t\<rbrakk> = t"
| "(CAppL E t')\<lbrakk>t\<rbrakk> = App (E\<lbrakk>t\<rbrakk>) t'"
| "(CAppR t' E)\<lbrakk>t\<rbrakk> = App t' (E\<lbrakk>t\<rbrakk>)"
| "(CLam [x].E)\<lbrakk>t\<rbrakk> = Lam [x].(E\<lbrakk>t\<rbrakk>)" 
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

nominal_primrec
 ctx_compose :: "ctx \<Rightarrow> ctx \<Rightarrow> ctx" ("_ \<circ> _" [100,100] 100)
where
  "\<box> \<circ> E' = E'"
| "(CAppL E t') \<circ> E' = CAppL (E \<circ> E') t'"
| "(CAppR t' E) \<circ> E' = CAppR t' (E \<circ> E')"
| "(CLam [x].E) \<circ> E' = CLam [x].(E \<circ> E')"
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

end
