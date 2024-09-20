(*  Title:      HOL/Datatype_Examples/Milner_Tofte.thy
    Author:     Dmitriy Traytel, ETH Zürich
    Copyright   2015

Modernized version of an old development by Jacob Frost

Based upon the article
    Robin Milner and Mads Tofte,
    Co-induction in Relational Semantics,
    Theoretical Computer Science 87 (1991), pages 209-220.

Written up as
    Jacob Frost, A Case Study of Co_induction in Isabelle/HOL
    Report 308, Computer Lab, University of Cambridge (1993).
*)

section \<open>Milner-Tofte: Co-induction in Relational Semantics\<close>

theory Milner_Tofte
imports Main
begin

typedecl Const
typedecl ExVar
typedecl TyConst

datatype Ex =
  e_const (e_const_fst: Const)
| e_var ExVar
| e_fn ExVar Ex (\<open>fn _ => _\<close> [0,51] 1000)
| e_fix ExVar ExVar Ex (\<open>fix _ ( _ ) = _\<close> [0,51,51] 1000)
| e_app Ex Ex (\<open>_ @@ _\<close> [51,51] 1000)

datatype Ty =
  t_const TyConst
| t_fun Ty Ty (\<open>_ -> _\<close> [51,51] 1000)

datatype 'a genClos =
  clos_mk ExVar Ex "ExVar \<rightharpoonup> 'a" (\<open>\<langle>_ , _ , _\<rangle>\<close> [0,0,0] 1000)

codatatype Val =
  v_const Const
| v_clos "Val genClos"

type_synonym Clos = "Val genClos"
type_synonym ValEnv = "ExVar \<rightharpoonup> Val"
type_synonym TyEnv = "ExVar \<rightharpoonup> Ty"

axiomatization 
  c_app :: "[Const, Const] => Const" and
  isof :: "[Const, Ty] => bool" (\<open>_ isof _\<close> [36,36] 50) where
  isof_app: "\<lbrakk>c1 isof t1 -> t2; c2 isof t1\<rbrakk> \<Longrightarrow> c_app c1 c2 isof t2"

text \<open>The dynamic semantics is defined inductively by a set of inference
rules.  These inference rules allows one to draw conclusions of the form ve
|- e ---> v, read the expression e evaluates to the value v in the value
environment ve.  Therefore the relation _ |- _ ---> _ is defined in Isabelle
as the least fixpoint of the functor eval_fun below.  From this definition
introduction rules and a strong elimination (induction) rule can be derived.\<close>

inductive eval :: "[ValEnv, Ex, Val] => bool" (\<open>_ \<turnstile> _ ---> _\<close> [36,0,36] 50) where
  eval_const: "ve \<turnstile> e_const c ---> v_const c"
| eval_var2:  "ev \<in> dom ve  \<Longrightarrow> ve \<turnstile> e_var ev ---> the (ve ev)"
| eval_fn:    "ve \<turnstile> fn ev => e ---> v_clos \<langle>ev, e, ve\<rangle>"
| eval_fix:   "cl = \<langle>ev1, e, ve(ev2 \<mapsto> v_clos cl)\<rangle> \<Longrightarrow> ve \<turnstile> fix ev2(ev1) = e ---> v_clos(cl)"
| eval_app1:  "\<lbrakk>ve \<turnstile> e1 ---> v_const c1; ve \<turnstile> e2 ---> v_const c2\<rbrakk> \<Longrightarrow>
                ve \<turnstile> e1 @@ e2 ---> v_const (c_app c1 c2)"
| eval_app2:  "\<lbrakk>ve \<turnstile> e1 ---> v_clos \<langle>xm, em, vem\<rangle>; ve \<turnstile> e2 ---> v2; vem(xm \<mapsto> v2) \<turnstile> em ---> v\<rbrakk> \<Longrightarrow>
                ve \<turnstile> e1 @@ e2 ---> v"

declare eval.intros[intro]

text \<open>The static semantics is defined in the same way as the dynamic
semantics.  The relation te |- e ===> t express the expression e has the
type t in the type environment te.\<close>

inductive elab :: "[TyEnv, Ex, Ty] => bool" (\<open>_ \<turnstile> _ ===> _\<close> [36,0,36] 50) where
  elab_const: "c isof ty \<Longrightarrow> te \<turnstile> e_const c ===> ty"
| elab_var:   "x \<in> dom te \<Longrightarrow> te \<turnstile> e_var x ===> the (te x)"
| elab_fn:    "te(x \<mapsto> ty1) \<turnstile> e ===> ty2 \<Longrightarrow> te \<turnstile> fn x => e ===> ty1 -> ty2"
| elab_fix:   "te(f \<mapsto> ty1 -> ty2, x \<mapsto> ty1) \<turnstile> e ===> ty2 \<Longrightarrow> te \<turnstile> fix f x = e ===> ty1 -> ty2"
| elab_app:   "\<lbrakk>te \<turnstile> e1 ===> ty1 -> ty2; te \<turnstile> e2 ===> ty1\<rbrakk> \<Longrightarrow> te \<turnstile> e1 @@ e2 ===> ty2"

declare elab.intros[intro]
inductive_cases elabE[elim!]:
  "te \<turnstile> e_const(c) ===> ty"
  "te \<turnstile> e_var(x) ===> ty"
  "te \<turnstile> fn x => e ===> ty"
  "te \<turnstile> fix f(x) = e ===> ty"
  "te \<turnstile> e1 @@ e2 ===> ty"

(* The original correspondence relation *)

abbreviation isof_env :: "[ValEnv,TyEnv] => bool" (\<open>_ isofenv _\<close>) where
  "ve isofenv te \<equiv> (dom(ve) = dom(te) \<and>
     (\<forall>x. x \<in> dom ve \<longrightarrow> (\<exists>c. the (ve x) = v_const(c) \<and> c isof the (te x))))"

coinductive hasty :: "[Val, Ty] => bool" (\<open>_ hasty _\<close> [36,36] 50) where
  hasty_const: "c isof t \<Longrightarrow> v_const c hasty t"
| hasty_clos:  "\<lbrakk>te \<turnstile> fn ev => e ===> t; dom(ve) = dom(te) \<and>
   (\<forall>x. x \<in> dom ve --> the (ve x) hasty the (te x)); cl = \<langle>ev,e,ve\<rangle>\<rbrakk> \<Longrightarrow> v_clos cl hasty t"

declare hasty.intros[intro]
inductive_cases hastyE[elim!]:
  "v_const c hasty t"
  "v_clos \<langle>xm , em , evm\<rangle> hasty u -> t"

definition hasty_env :: "[ValEnv, TyEnv] => bool" (\<open>_ hastyenv _ \<close> [36,36] 35) where
  [simp]: "ve hastyenv te \<equiv> (dom(ve) = dom(te) \<and>
     (\<forall>x. x \<in> dom ve --> the (ve x) hasty the (te x)))"

theorem consistency: "\<lbrakk>ve \<turnstile> e ---> v; ve hastyenv te; te \<turnstile> e ===> t\<rbrakk> \<Longrightarrow> v hasty t"
proof (induct ve e v arbitrary: t te rule: eval.induct)
  case (eval_fix cl x e ve f)
  then show ?case
    by coinduction
      (auto 0 11 intro: exI[of _ "te(f \<mapsto> _)"] exI[of _ x] exI[of _ e] exI[of _ "ve(f \<mapsto> v_clos cl)"])
next
  case (eval_app2 ve e1 xm em evm e2 v2 v)
  then obtain u where "te \<turnstile> e1 ===> u -> t" "te \<turnstile> e2 ===> u" by auto
  with eval_app2(2)[of te "u -> t"] eval_app2(4)[of te u] eval_app2(1,3,5,7) show ?case
    by (auto 0 4 elim!: eval_app2(6)[rotated])
qed (auto 8 0 intro!: isof_app)

lemma basic_consistency_aux:
  "ve isofenv te \<Longrightarrow> ve hastyenv te"
  using hasty_const hasty_env_def by force

theorem basic_consistency:
  "\<lbrakk>ve isofenv te; ve \<turnstile> e ---> v_const c; te \<turnstile> e ===> t\<rbrakk> \<Longrightarrow> c isof t"
  by (auto dest: consistency intro!: basic_consistency_aux)

end
