theory W
imports Nominal
begin

text {* Example for strong induction rules avoiding sets of atoms. *}

atom_decl tvar var 

abbreviation
  "difference_list" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" ("_ - _" [60,60] 60) 
where
  "xs - ys \<equiv> [x \<leftarrow> xs. x\<notin>set ys]"

lemma difference_eqvt_tvar[eqvt]:
  fixes pi::"tvar prm"
  and   Xs Ys::"tvar list"
  shows "pi\<bullet>(Xs - Ys) = (pi\<bullet>Xs) - (pi\<bullet>Ys)"
by (induct Xs) (simp_all add: eqvts)

lemma difference_fresh:
  fixes X::"tvar"
  and   Xs Ys::"tvar list"
  assumes a: "X\<in>set Ys"
  shows "X\<sharp>(Xs - Ys)"
using a
by (induct Xs) (auto simp add: fresh_list_nil fresh_list_cons fresh_atm)

nominal_datatype ty = 
    TVar "tvar"
  | Fun "ty" "ty" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype tyS = 
    Ty  "ty"
  | ALL "\<guillemotleft>tvar\<guillemotright>tyS" ("\<forall>[_]._" [100,100] 100)

nominal_datatype trm = 
    Var "var"
  | App "trm" "trm" 
  | Lam "\<guillemotleft>var\<guillemotright>trm" ("Lam [_]._" [100,100] 100)
  | Let "\<guillemotleft>var\<guillemotright>trm" "trm" 

abbreviation
  LetBe :: "var \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm" ("Let _ be _ in _" [100,100,100] 100)
where
 "Let x be t1 in t2 \<equiv> trm.Let x t2 t1"

types 
  Ctxt  = "(var\<times>tyS) list" 

text {* free type variables *}

class ftv = type +
  fixes ftv :: "'a \<Rightarrow> tvar list"

instantiation * :: (ftv, ftv) ftv
begin

primrec ftv_prod
where
 "ftv (x::'a::ftv, y::'b::ftv) = (ftv x)@(ftv y)"

instance ..

end

instantiation tvar :: ftv
begin

definition
  ftv_of_tvar[simp]:  "ftv X \<equiv> [(X::tvar)]"

instance ..

end

instantiation var :: ftv
begin

definition
  ftv_of_var[simp]:   "ftv (x::var) \<equiv> []" 

instance ..

end

instantiation list :: (ftv) ftv
begin

primrec ftv_list
where
  "ftv [] = []"
| "ftv (x#xs) = (ftv x)@(ftv xs)"

instance ..

end

(* free type-variables of types *)

instantiation ty :: ftv
begin

nominal_primrec ftv_ty
where
  "ftv (TVar X) = [X]"
| "ftv (T\<^isub>1\<rightarrow>T\<^isub>2) = (ftv T\<^isub>1)@(ftv T\<^isub>2)"
by (rule TrueI)+

instance ..

end

lemma ftv_ty_eqvt[eqvt]:
  fixes pi::"tvar prm"
  and   T::"ty"
  shows "pi\<bullet>(ftv T) = ftv (pi\<bullet>T)"
by (nominal_induct T rule: ty.strong_induct)
   (perm_simp add: append_eqvt)+

instantiation tyS :: ftv
begin

nominal_primrec ftv_tyS
where
  "ftv (Ty T)    = ftv T"
| "ftv (\<forall>[X].S) = (ftv S) - [X]"
apply(finite_guess add: ftv_ty_eqvt fs_tvar1)+
apply(rule TrueI)+
apply(rule difference_fresh)
apply(simp)
apply(fresh_guess add: ftv_ty_eqvt fs_tvar1)+
done

instance ..

end

lemma ftv_tyS_eqvt[eqvt]:
  fixes pi::"tvar prm"
  and   S::"tyS"
  shows "pi\<bullet>(ftv S) = ftv (pi\<bullet>S)"
apply(nominal_induct S rule: tyS.strong_induct)
apply(simp add: eqvts)
apply(simp only: ftv_tyS.simps)
apply(simp only: eqvts)
apply(simp add: eqvts)
done 

lemma ftv_Ctxt_eqvt[eqvt]:
  fixes pi::"tvar prm"
  and   \<Gamma>::"Ctxt"
  shows "pi\<bullet>(ftv \<Gamma>) = ftv (pi\<bullet>\<Gamma>)"
by (induct \<Gamma>) (auto simp add: eqvts)

text {* Valid *}
inductive
  valid :: "Ctxt \<Rightarrow> bool"
where
  V_Nil[intro]:  "valid []"
| V_Cons[intro]: "\<lbrakk>valid \<Gamma>;x\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((x,S)#\<Gamma>)"

equivariance valid

text {* General *}
consts
  gen :: "ty \<Rightarrow> tvar list \<Rightarrow> tyS"

primrec 
  "gen T [] = Ty T"
  "gen T (X#Xs) = \<forall>[X].(gen T Xs)"

lemma gen_eqvt[eqvt]:
  fixes pi::"tvar prm"
  shows "pi\<bullet>(gen T Xs) = gen (pi\<bullet>T) (pi\<bullet>Xs)"
by (induct Xs) (simp_all add: eqvts)

abbreviation 
  close :: "Ctxt \<Rightarrow> ty \<Rightarrow> tyS"
where 
  "close \<Gamma> T \<equiv> gen T ((ftv T) - (ftv \<Gamma>))"

lemma close_eqvt[eqvt]:
  fixes pi::"tvar prm"
  shows "pi\<bullet>(close \<Gamma> T) = close (pi\<bullet>\<Gamma>) (pi\<bullet>T)"
by (simp_all only: eqvts)
  
text {* Substitution *}

types Subst = "(tvar\<times>ty) list"

class psubst =
  fixes psubst :: "Subst \<Rightarrow> 'a \<Rightarrow> 'a"       ("_<_>" [100,60] 120)

abbreviation 
  subst :: "'a::psubst \<Rightarrow> tvar \<Rightarrow> ty \<Rightarrow> 'a"  ("_[_::=_]" [100,100,100] 100)
where
  "smth[X::=T] \<equiv> ([(X,T)])<smth>" 

fun
  lookup :: "Subst \<Rightarrow> tvar \<Rightarrow> ty"   
where
  "lookup [] X        = TVar X"
| "lookup ((Y,T)#\<theta>) X = (if X=Y then T else lookup \<theta> X)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"tvar prm"
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>) (auto simp add: eqvts)

instantiation ty :: psubst
begin

nominal_primrec psubst_ty
where
  "\<theta><TVar X>   = lookup \<theta> X"
| "\<theta><T\<^isub>1 \<rightarrow> T\<^isub>2> = (\<theta><T\<^isub>1>) \<rightarrow> (\<theta><T\<^isub>2>)"
by (rule TrueI)+

instance ..

end

lemma psubst_ty_eqvt[eqvt]:
  fixes pi1::"tvar prm"
  and   \<theta>::"Subst"
  and   T::"ty"
  shows "pi1\<bullet>(\<theta><T>) = (pi1\<bullet>\<theta>)<(pi1\<bullet>T)>"
by (induct T rule: ty.induct) (simp_all add: eqvts)

text {* instance *}
inductive
  general :: "ty \<Rightarrow> tyS \<Rightarrow> bool"("_ \<prec> _" [50,51] 50)  
where
  G_Ty[intro]:  "T \<prec> (Ty T)" 
| G_All[intro]: "\<lbrakk>X\<sharp>T'; (T::ty) \<prec> S\<rbrakk> \<Longrightarrow> T[X::=T'] \<prec> \<forall>[X].S"

equivariance general[tvar] 

text{* typing judgements *}
inductive
  typing :: "Ctxt \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" (" _ \<turnstile> _ : _ " [60,60,60] 60) 
where
  T_VAR[intro]: "\<lbrakk>valid \<Gamma>; (x,S)\<in>set \<Gamma>; T \<prec> S\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| T_APP[intro]: "\<lbrakk>\<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1\<rightarrow>T\<^isub>2; \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App t\<^isub>1 t\<^isub>2 : T\<^isub>2" 
| T_LAM[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,Ty T\<^isub>1)#\<Gamma>) \<turnstile> t : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T\<^isub>1\<rightarrow>T\<^isub>2"
| T_LET[intro]: "\<lbrakk>x\<sharp>\<Gamma>; \<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1; ((x,close \<Gamma> T\<^isub>1)#\<Gamma>) \<turnstile> t\<^isub>2 : T\<^isub>2; set (ftv T\<^isub>1 - ftv \<Gamma>) \<sharp>* T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Let x be t\<^isub>1 in t\<^isub>2 : T\<^isub>2"

lemma fresh_star_tvar_eqvt[eqvt]:
  "(pi::tvar prm) \<bullet> ((Xs::tvar set) \<sharp>* (x::'a::{cp_tvar_tvar,pt_tvar})) = (pi \<bullet> Xs) \<sharp>* (pi \<bullet> x)"
  by (simp only: pt_fresh_star_bij_ineq(1) [OF pt_tvar_inst pt_tvar_inst at_tvar_inst cp_tvar_tvar_inst] perm_bool)

equivariance typing[tvar]

lemma fresh_tvar_trm: "(X::tvar) \<sharp> (t::trm)"
  by (nominal_induct t rule: trm.strong_induct) (simp_all add: fresh_atm abs_fresh)

lemma ftv_ty: "supp (T::ty) = set (ftv T)"
  by (nominal_induct T rule: ty.strong_induct) (simp_all add: ty.supp supp_atm)

lemma ftv_tyS: "supp (s::tyS) = set (ftv s)"
  by (nominal_induct s rule: tyS.strong_induct) (auto simp add: tyS.supp abs_supp ftv_ty)

lemma ftv_Ctxt: "supp (\<Gamma>::Ctxt) = set (ftv \<Gamma>)"
  apply (induct \<Gamma>)
  apply (simp_all add: supp_list_nil supp_list_cons)
  apply (case_tac a)
  apply (simp add: supp_prod supp_atm ftv_tyS)
  done

lemma ftv_tvars: "supp (Tvs::tvar list) = set Tvs"
  by (induct Tvs) (simp_all add: supp_list_nil supp_list_cons supp_atm)

lemma difference_supp: "((supp ((xs::tvar list) - ys))::tvar set) = supp xs - supp ys"
  by (induct xs) (auto simp add: supp_list_nil supp_list_cons ftv_tvars)

lemma set_supp_eq: "set (xs::tvar list) = supp xs"
  by (induct xs) (simp_all add: supp_list_nil supp_list_cons supp_atm)

nominal_inductive2 typing
  avoids T_LET: "set (ftv T\<^isub>1 - ftv \<Gamma>)"
  apply (simp add: fresh_star_def fresh_def ftv_Ctxt)
  apply (simp add: fresh_star_def fresh_tvar_trm)
  apply assumption
  apply simp
  done

lemma perm_fresh_fresh_aux:
  "\<forall>(x,y)\<in>set (pi::tvar prm). x \<sharp> z \<and> y \<sharp> z \<Longrightarrow> pi \<bullet> (z::'a::pt_tvar) = z"
  apply (induct pi rule: rev_induct)
  apply simp
  apply (simp add: split_paired_all pt_tvar2)
  apply (frule_tac x="(a, b)" in bspec)
  apply simp
  apply (simp add: perm_fresh_fresh)
  done

lemma freshs_mem: "x \<in> (S::tvar set) \<Longrightarrow> S \<sharp>* z \<Longrightarrow> x \<sharp> z"
  by (simp add: fresh_star_def)

lemma fresh_gen_set:
  fixes X::"tvar"
  and   Xs::"tvar list"
  assumes asm: "X\<in>set Xs" 
  shows "X\<sharp>gen T Xs"
using asm
apply(induct Xs)
apply(simp)
apply(case_tac "X=a")
apply(simp add: abs_fresh)
apply(simp add: abs_fresh)
done

lemma close_fresh:
  fixes \<Gamma>::"Ctxt"
  shows "\<forall>(X::tvar)\<in>set ((ftv T) - (ftv \<Gamma>)). X\<sharp>(close \<Gamma> T)"
by (simp add: fresh_gen_set)

lemma gen_supp: "(supp (gen T Xs)::tvar set) = supp T - supp Xs"
  by (induct Xs) (auto simp add: supp_list_nil supp_list_cons tyS.supp abs_supp supp_atm)

lemma minus_Int_eq: "T - (T - U) = T \<inter> U"
  by blast

lemma close_supp: "supp (close \<Gamma> T) = set (ftv T) \<inter> set (ftv \<Gamma>)"
  apply (simp add: gen_supp difference_supp ftv_ty ftv_Ctxt)
  apply (simp only: set_supp_eq minus_Int_eq)
  done

lemma better_T_LET:
  assumes x: "x\<sharp>\<Gamma>"
  and t1: "\<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1"
  and t2: "((x,close \<Gamma> T\<^isub>1)#\<Gamma>) \<turnstile> t\<^isub>2 : T\<^isub>2"
  shows "\<Gamma> \<turnstile> Let x be t\<^isub>1 in t\<^isub>2 : T\<^isub>2"
proof -
  have fin: "finite (set (ftv T\<^isub>1 - ftv \<Gamma>))" by simp
  obtain pi where pi1: "(pi \<bullet> set (ftv T\<^isub>1 - ftv \<Gamma>)) \<sharp>* (T\<^isub>2, \<Gamma>)"
    and pi2: "set pi \<subseteq> set (ftv T\<^isub>1 - ftv \<Gamma>) \<times> (pi \<bullet> set (ftv T\<^isub>1 - ftv \<Gamma>))"
    by (rule at_set_avoiding [OF at_tvar_inst fin fs_tvar1, of "(T\<^isub>2, \<Gamma>)"])
  from pi1 have pi1': "(pi \<bullet> set (ftv T\<^isub>1 - ftv \<Gamma>)) \<sharp>* \<Gamma>"
    by (simp add: fresh_star_prod)
  have Gamma_fresh: "\<forall>(x,y)\<in>set pi. x \<sharp> \<Gamma> \<and> y \<sharp> \<Gamma>"
    apply (rule ballI)
    apply (simp add: split_paired_all)
    apply (drule subsetD [OF pi2])
    apply (erule SigmaE)
    apply (drule freshs_mem [OF _ pi1'])
    apply (simp add: ftv_Ctxt [symmetric] fresh_def)
    done
  have close_fresh': "\<forall>(x, y)\<in>set pi. x \<sharp> close \<Gamma> T\<^isub>1 \<and> y \<sharp> close \<Gamma> T\<^isub>1"
    apply (rule ballI)
    apply (simp add: split_paired_all)
    apply (drule subsetD [OF pi2])
    apply (erule SigmaE)
    apply (drule bspec [OF close_fresh])
    apply (drule freshs_mem [OF _ pi1'])
    apply (simp add: fresh_def close_supp ftv_Ctxt)
    done
  note x
  moreover from Gamma_fresh perm_boolI [OF t1, of pi]
  have "\<Gamma> \<turnstile> t\<^isub>1 : pi \<bullet> T\<^isub>1"
    by (simp add: perm_fresh_fresh_aux eqvts fresh_tvar_trm)
  moreover from t2 close_fresh'
  have "(x,(pi \<bullet> close \<Gamma> T\<^isub>1))#\<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>2"
    by (simp add: perm_fresh_fresh_aux)
  with Gamma_fresh have "(x,close \<Gamma> (pi \<bullet> T\<^isub>1))#\<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>2"
    by (simp add: close_eqvt perm_fresh_fresh_aux)
  moreover from pi1 Gamma_fresh
  have "set (ftv (pi \<bullet> T\<^isub>1) - ftv \<Gamma>) \<sharp>* T\<^isub>2"
    by (simp only: eqvts fresh_star_prod perm_fresh_fresh_aux)
  ultimately show ?thesis by (rule T_LET)
qed

end
