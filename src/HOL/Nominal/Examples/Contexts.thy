(* $Id$ *)

theory Contexts
imports "../Nominal"
begin

text {* 
  
  We show here that the Plotkin-style of defining
  reductions relation based on congruence rules is
  equivalent to the Felleisen-Hieb-style representation 
  based on contexts. 
  
  The interesting point is that contexts do not bind 
  anything. On the other hand the operation of replacing 
  a term into a context produces an alpha-equivalent term. 

*}

atom_decl name

text {* Terms *}
nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {* Contexts - the lambda case in contexts does not bind a name *}
nominal_datatype ctx = 
    Hole
  | CAppL "ctx" "lam"
  | CAppR "lam" "ctx" 
  | CLam "name" "ctx"  ("CLam [_]._" [100,100] 100) 

text {* Capture-avoiding substitution and three lemmas *}

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

lemma  subst_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>t1[x::=t2] = (pi\<bullet>t1)[(pi\<bullet>x)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: x t2 rule: lam.induct)
   (auto simp add: perm_bij fresh_atm fresh_bij)

lemma subst_fresh:
  fixes x y::"name"
  and   t t'::"lam"
  shows "y\<sharp>([x].t,t') \<Longrightarrow> y\<sharp>t[x::=t']"
by (nominal_induct t avoiding: x y t' rule: lam.inducts)
   (auto simp add: abs_fresh fresh_prod fresh_atm)

text {* 
  Replace is the operation that fills a term into a hole. While
  contexts themselves are not alpha-equivalence classes, the 
  filling operation produces an alpha-equivalent lambda-term. 
*}

consts 
  replace :: "ctx \<Rightarrow> lam \<Rightarrow> lam" ("_<_>" [100,100] 100)

nominal_primrec
  "Hole<t> = t"
  "(CAppL E t')<t> = App (E<t>) t'"
  "(CAppR t' E)<t> = App t' (E<t>)"
  "(CLam [x].E)<t> = Lam [x].(E<t>)" 
by (rule TrueI)+


lemma alpha_test: 
  shows "(CLam [x].Hole)<Var x> = (CLam [y].Hole)<Var y>"
by (auto simp add: alpha lam.inject calc_atm fresh_atm) 


lemma replace_eqvt[eqvt]:
  fixes pi:: "name prm"
  shows "pi\<bullet>(E<e>) = (pi\<bullet>E)<(pi\<bullet>e)>"
by (nominal_induct E rule: ctx.inducts) (auto)

lemma replace_fresh:
  fixes x::"name"
  and   E::"ctx"
  and   t::"lam"
  shows "x\<sharp>(E,t) \<Longrightarrow> x\<sharp>E<t>"
by (induct E rule: ctx.weak_induct)
   (auto simp add: fresh_prod abs_fresh)


text {* Composition of two contexts *}

consts 
 ctx_replace :: "ctx \<Rightarrow> ctx \<Rightarrow> ctx" ("_ \<circ> _" [100,100] 100)

nominal_primrec
  "Hole \<circ> E' = E'"
  "(CAppL E t') \<circ> E' = CAppL (E \<circ> E') t'"
  "(CAppR t' E) \<circ> E' = CAppR t' (E \<circ> E')"
  "(CLam [x].E) \<circ> E' = CLam [x].(E \<circ> E')"
by (rule TrueI)+
  
lemma ctx_compose:
  shows "E1<E2<t>> = (E1 \<circ> E2)<t>"
by (induct E1 rule: ctx.weak_induct) (auto)

lemma ctx_compose_fresh:
  fixes x::"name"
  and   E1 E2::"ctx"
  shows "x\<sharp>(E1,E2) \<Longrightarrow> x\<sharp>(E1\<circ>E2)"
by (induct E1 rule: ctx.weak_induct)
   (auto simp add: fresh_prod)

text {* Beta-reduction via contexts *}

inductive
  ctx_red :: "lam\<Rightarrow>lam\<Rightarrow>bool" ("_ \<longrightarrow>x _" [80,80] 80) 
where
  xbeta[intro]: "x\<sharp>(E,t') \<Longrightarrow> E<App (Lam [x].t) t'> \<longrightarrow>x E<t[x::=t']>" 

equivariance ctx_red

nominal_inductive ctx_red
  by (simp_all add: replace_fresh subst_fresh abs_fresh)

text {* Beta-reduction via congruence rules *}

inductive
  cong_red :: "lam\<Rightarrow>lam\<Rightarrow>bool" ("_ \<longrightarrow>o _" [80,80] 80) 
where
  obeta[intro]: "x\<sharp>t' \<Longrightarrow> App (Lam [x].t) t' \<longrightarrow>o t[x::=t']"
| oapp1[intro]: "t \<longrightarrow>o t' \<Longrightarrow> App t t2 \<longrightarrow>o App t' t2"
| oapp2[intro]: "t \<longrightarrow>o t' \<Longrightarrow> App t2 t \<longrightarrow>o App t2 t'"
| olam[intro]:  "t \<longrightarrow>o t' \<Longrightarrow> Lam [x].t \<longrightarrow>o Lam [x].t'"

equivariance cong_red

nominal_inductive cong_red
  by (simp_all add: subst_fresh abs_fresh)

text {* The proof that shows both relations are equal *}

lemma cong_red_ctx:
  assumes a: "t \<longrightarrow>o t'"
  shows "E<t> \<longrightarrow>o E<t'>"
using a
by (induct E rule: ctx.weak_induct) (auto)

lemma ctx_red_ctx:
  assumes a: "t \<longrightarrow>x t'"
  shows "E<t> \<longrightarrow>x E<t'>"
using a 
by (nominal_induct t t' avoiding: E rule: ctx_red.strong_induct) 
   (auto simp add: ctx_compose ctx_compose_fresh)

lemma ctx_red_hole:
  assumes a: "Hole<t> \<longrightarrow>x Hole<t'>"
  shows "t \<longrightarrow>x t'"
using a by simp

theorem ctx_red_cong_red:
  assumes a: "t \<longrightarrow>x t'"
  shows "t \<longrightarrow>o t'"
using a 
by (induct) (auto intro!: cong_red_ctx)

theorem cong_red_ctx_red:
  assumes a: "t \<longrightarrow>o t'"
  shows "t \<longrightarrow>x t'"
using a 
apply(induct)
apply(rule ctx_red_hole)
apply(rule xbeta)
apply(simp)
apply(metis ctx_red_ctx replace.simps)+ (* found by SledgeHammer *)
done

end
