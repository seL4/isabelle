theory Lam_Funs
  imports "HOL-Nominal.Nominal"
begin

text \<open>
  Provides useful definitions for reasoning
  with lambda-terms. 
\<close>

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text \<open>The depth of a lambda-term.\<close>

nominal_primrec
  depth :: "lam \<Rightarrow> nat"
where
  "depth (Var x) = 1"
| "depth (App t1 t2) = (max (depth t1) (depth t2)) + 1"
| "depth (Lam [a].t) = (depth t) + 1"
  by(finite_guess | simp | fresh_guess)+

text \<open>
  The free variables of a lambda-term. A complication in this
  function arises from the fact that it returns a name set, which 
  is not a finitely supported type. Therefore we have to prove 
  the invariant that frees always returns a finite set of names. 
\<close>

nominal_primrec (invariant: "\<lambda>s::name set. finite s")
  frees :: "lam \<Rightarrow> name set"
where
  "frees (Var a) = {a}"
| "frees (App t1 t2) = (frees t1) \<union> (frees t2)"
| "frees (Lam [a].t) = (frees t) - {a}"
apply(finite_guess | simp add: fresh_def | fresh_guess)+
  apply (simp add: at_fin_set_supp at_name_inst)
apply(fresh_guess)+
done

text \<open>
  We can avoid the definition of frees by
  using the build in notion of support.
\<close>

lemma frees_equals_support:
  shows "frees t = supp t"
by (nominal_induct t rule: lam.strong_induct)
   (simp_all add: lam.supp supp_atm abs_supp)

text \<open>Parallel and single capture-avoiding substitution.\<close>

fun
  lookup :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam"   
where
  "lookup [] x        = Var x"
| "lookup ((y,e)#\<theta>) x = (if x=y then e else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  and   \<theta>::"(name\<times>lam) list"
  and   X::"name"
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>) (auto simp add: eqvts)
 
nominal_primrec
  psubst :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam"  ("_<_>" [95,95] 105)
where
  "\<theta><(Var x)> = (lookup \<theta> x)"
| "\<theta><(App e\<^sub>1 e\<^sub>2)> = App (\<theta><e\<^sub>1>) (\<theta><e\<^sub>2>)"
| "x\<sharp>\<theta> \<Longrightarrow> \<theta><(Lam [x].e)> = Lam [x].(\<theta><e>)"
  by (finite_guess | simp add: abs_fresh | fresh_guess)+

lemma psubst_eqvt[eqvt]:
  fixes pi::"name prm" 
  and   t::"lam"
  shows "pi\<bullet>(\<theta><t>) = (pi\<bullet>\<theta>)<(pi\<bullet>t)>"
by (nominal_induct t avoiding: \<theta> rule: lam.strong_induct)
   (simp_all add: eqvts fresh_bij)

abbreviation 
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [100,100,100] 100)
where 
  "t[x::=t']  \<equiv> ([(x,t')])<t>" 

lemma subst[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  and   "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
by (simp_all add: fresh_list_cons fresh_list_nil)

lemma subst_supp: 
  shows "supp(t1[a::=t2]) \<subseteq> (((supp(t1)-{a})\<union>supp(t2))::name set)"
proof (nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
  case (Var name)
  then show ?case
    by (simp add: lam.supp(1) supp_atm)
next
  case (App lam1 lam2)
  then show ?case
    using lam.supp(2) by fastforce
next
  case (Lam name lam)
  then show ?case
    using frees.simps(3) frees_equals_support by auto
qed

text \<open>
  Contexts - lambda-terms with a single hole.
  Note that the lambda case in contexts does not bind a 
  name, even if we introduce the notation [_]._ for CLam.
\<close>
nominal_datatype clam = 
    Hole ("\<box>" 1000)  
  | CAppL "clam" "lam"
  | CAppR "lam" "clam" 
  | CLam "name" "clam"  ("CLam [_]._" [100,100] 100) 

text \<open>Filling a lambda-term into a context.\<close>

nominal_primrec
  filling :: "clam \<Rightarrow> lam \<Rightarrow> lam" ("_\<lbrakk>_\<rbrakk>" [100,100] 100)
where
  "\<box>\<lbrakk>t\<rbrakk> = t"
| "(CAppL E t')\<lbrakk>t\<rbrakk> = App (E\<lbrakk>t\<rbrakk>) t'"
| "(CAppR t' E)\<lbrakk>t\<rbrakk> = App t' (E\<lbrakk>t\<rbrakk>)"
| "(CLam [x].E)\<lbrakk>t\<rbrakk> = Lam [x].(E\<lbrakk>t\<rbrakk>)" 
by (rule TrueI)+

text \<open>Composition od two contexts\<close>

nominal_primrec
 clam_compose :: "clam \<Rightarrow> clam \<Rightarrow> clam" ("_ \<circ> _" [100,100] 100)
where
  "\<box> \<circ> E' = E'"
| "(CAppL E t') \<circ> E' = CAppL (E \<circ> E') t'"
| "(CAppR t' E) \<circ> E' = CAppR t' (E \<circ> E')"
| "(CLam [x].E) \<circ> E' = CLam [x].(E \<circ> E')"
by (rule TrueI)+
  
lemma clam_compose:
  shows "(E1 \<circ> E2)\<lbrakk>t\<rbrakk> = E1\<lbrakk>E2\<lbrakk>t\<rbrakk>\<rbrakk>"
by (induct E1 rule: clam.induct) (auto)

end
