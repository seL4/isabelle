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

lemma difference_supset:
  fixes xs::"'a list"
  and   ys::"'a list"
  and   zs::"'a list"
  assumes asm: "set xs \<subseteq> set ys"
  shows "xs - ys = []"
using asm
by (induct xs) (auto)

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

consts ftv :: "'a \<Rightarrow> tvar list"

overloading 
  ftv_prod \<equiv> "ftv :: ('a \<times> 'b) \<Rightarrow> tvar list"
  ftv_tvar \<equiv> "ftv :: tvar \<Rightarrow> tvar list"
  ftv_var  \<equiv> "ftv :: var \<Rightarrow> tvar list"
  ftv_list \<equiv> "ftv :: 'a list \<Rightarrow> tvar list"
  ftv_ty   \<equiv> "ftv :: ty \<Rightarrow> tvar list"
begin

primrec 
  ftv_prod
where
 "ftv_prod (x, y) = (ftv x) @ (ftv y)"

definition
  ftv_tvar :: "tvar \<Rightarrow> tvar list"
where
[simp]: "ftv_tvar X \<equiv> [(X::tvar)]"

definition
  ftv_var :: "var \<Rightarrow> tvar list"
where
[simp]: "ftv_var x \<equiv> []"

primrec 
  ftv_list
where
  "ftv_list [] = []"
| "ftv_list (x#xs) = (ftv x)@(ftv_list xs)"

nominal_primrec 
  ftv_ty :: "ty \<Rightarrow> tvar list"
where
  "ftv_ty (TVar X) = [X]"
| "ftv_ty (T1 \<rightarrow>T2) = (ftv_ty T1) @ (ftv_ty T2)"
by (rule TrueI)+

end

lemma ftv_ty_eqvt[eqvt]:
  fixes pi::"tvar prm"
  and   T::"ty"
  shows "pi\<bullet>(ftv T) = ftv (pi\<bullet>T)"
by (nominal_induct T rule: ty.strong_induct)
   (perm_simp add: append_eqvt)+

overloading 
  ftv_tyS  \<equiv> "ftv :: tyS \<Rightarrow> tvar list"
begin

nominal_primrec 
  ftv_tyS :: "tyS \<Rightarrow> tvar list"
where
  "ftv_tyS (Ty T)    = ((ftv (T::ty))::tvar list)"
| "ftv_tyS (\<forall>[X].S) = (ftv_tyS S) - [X]"
apply(finite_guess add: ftv_ty_eqvt fs_tvar1)+
apply(rule TrueI)+
apply(rule difference_fresh)
apply(simp)
apply(fresh_guess add: ftv_ty_eqvt fs_tvar1)+
done

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

consts
  psubst :: "Subst \<Rightarrow> 'a \<Rightarrow> 'a"       ("_<_>" [100,60] 120)

abbreviation 
  subst :: "'a \<Rightarrow> tvar \<Rightarrow> ty \<Rightarrow> 'a"  ("_[_::=_]" [100,100,100] 100)
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

lemma lookup_fresh:
  fixes X::"tvar"
  assumes a: "X\<sharp>\<theta>"
  shows "lookup \<theta> X = TVar X"
using a
by (induct \<theta>)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

overloading 
  psubst_ty \<equiv> "psubst :: Subst \<Rightarrow> ty \<Rightarrow> ty"
begin

nominal_primrec 
  psubst_ty
where
  "\<theta><TVar X>   = lookup \<theta> X"
| "\<theta><T\<^isub>1 \<rightarrow> T\<^isub>2> = (\<theta><T\<^isub>1>) \<rightarrow> (\<theta><T\<^isub>2>)"
by (rule TrueI)+

end

lemma psubst_ty_eqvt[eqvt]:
  fixes pi::"tvar prm"
  and   \<theta>::"Subst"
  and   T::"ty"
  shows "pi\<bullet>(\<theta><T>) = (pi\<bullet>\<theta>)<(pi\<bullet>T)>"
by (induct T rule: ty.induct) (simp_all add: eqvts)

overloading 
  psubst_tyS \<equiv> "psubst :: Subst \<Rightarrow> tyS \<Rightarrow> tyS"
begin

nominal_primrec 
  psubst_tyS :: "Subst \<Rightarrow> tyS \<Rightarrow> tyS"
where 
  "\<theta><(Ty T)> = Ty (\<theta><T>)"
| "X\<sharp>\<theta> \<Longrightarrow> \<theta><(\<forall>[X].S)> = \<forall>[X].(\<theta><S>)"
apply(finite_guess add: psubst_ty_eqvt fs_tvar1)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess add: psubst_ty_eqvt fs_tvar1)+
done

end

overloading 
  psubst_Ctxt \<equiv> "psubst :: Subst \<Rightarrow> Ctxt \<Rightarrow> Ctxt"
begin

fun
  psubst_Ctxt :: "Subst \<Rightarrow> Ctxt \<Rightarrow> Ctxt"
where
  "psubst_Ctxt \<theta> [] = []"
| "psubst_Ctxt \<theta> ((x,S)#\<Gamma>) = (x,\<theta><S>)#(psubst_Ctxt \<theta> \<Gamma>)"

end

lemma fresh_lookup:
  fixes X::"tvar"
  and   \<theta>::"Subst"
  and   Y::"tvar"
  assumes asms: "X\<sharp>Y" "X\<sharp>\<theta>"
  shows "X\<sharp>(lookup \<theta> Y)"
  using asms
  by (induct \<theta>)
     (auto simp add: fresh_list_cons fresh_prod fresh_atm)

lemma fresh_psubst_ty:
  fixes X::"tvar"
  and   \<theta>::"Subst"
  and   T::"ty"
  assumes asms: "X\<sharp>\<theta>" "X\<sharp>T"
  shows "X\<sharp>\<theta><T>"
  using asms
  by (nominal_induct T rule: ty.strong_induct)
     (auto simp add: fresh_list_append fresh_list_cons fresh_prod fresh_lookup)

lemma fresh_psubst_tyS:
  fixes X::"tvar"
  and   \<theta>::"Subst"
  and   S::"tyS"
  assumes asms: "X\<sharp>\<theta>" "X\<sharp>S"
  shows "X\<sharp>\<theta><S>"
  using asms
  by (nominal_induct S avoiding: \<theta>  X rule: tyS.strong_induct)
     (auto simp add: fresh_psubst_ty abs_fresh)

lemma fresh_psubst_Ctxt:
  fixes X::"tvar"
  and   \<theta>::"Subst"
  and   \<Gamma>::"Ctxt"
  assumes asms: "X\<sharp>\<theta>" "X\<sharp>\<Gamma>"
  shows "X\<sharp>\<theta><\<Gamma>>"
using asms
by (induct \<Gamma>)
   (auto simp add: fresh_psubst_tyS fresh_list_cons)

lemma subst_freshfact2_ty: 
  fixes   X::"tvar"
  and     Y::"tvar"
  and     T::"ty"
  assumes asms: "X\<sharp>S"
  shows "X\<sharp>T[X::=S]"
  using asms
by (nominal_induct T rule: ty.strong_induct)
   (auto simp add: fresh_atm)

text {* instance of a type scheme *}
inductive
  inst :: "ty \<Rightarrow> tyS \<Rightarrow> bool"("_ \<prec> _" [50,51] 50)  
where
  I_Ty[intro]:  "T \<prec> (Ty T)" 
| I_All[intro]: "\<lbrakk>X\<sharp>T'; T \<prec> S\<rbrakk> \<Longrightarrow> T[X::=T'] \<prec> \<forall>[X].S"

equivariance inst[tvar] 

nominal_inductive inst
  by (simp_all add: abs_fresh subst_freshfact2_ty)

lemma subst_forget_ty:
  fixes T::"ty"
  and   X::"tvar"
  assumes a: "X\<sharp>T"
  shows "T[X::=S] = T"
  using a
  by  (nominal_induct T rule: ty.strong_induct)
      (auto simp add: fresh_atm)

lemma psubst_ty_lemma:
  fixes \<theta>::"Subst"
  and   X::"tvar"
  and   T'::"ty"
  and   T::"ty"
  assumes a: "X\<sharp>\<theta>" 
  shows "\<theta><T[X::=T']> = (\<theta><T>)[X::=\<theta><T'>]"
using a
apply(nominal_induct T avoiding: \<theta> X T' rule: ty.strong_induct)
apply(auto simp add: ty.inject lookup_fresh)
apply(rule sym)
apply(rule subst_forget_ty)
apply(rule fresh_lookup)
apply(simp_all add: fresh_atm)
done

lemma general_preserved:
  fixes \<theta>::"Subst"
  assumes a: "T \<prec> S"
  shows "\<theta><T> \<prec> \<theta><S>"
using a
apply(nominal_induct T S avoiding: \<theta> rule: inst.strong_induct)
apply(auto)[1]
apply(simp add: psubst_ty_lemma)
apply(rule_tac I_All)
apply(simp add: fresh_psubst_ty)
apply(simp)
done


text{* typing judgements *}
inductive
  typing :: "Ctxt \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" (" _ \<turnstile> _ : _ " [60,60,60] 60) 
where
  T_VAR[intro]: "\<lbrakk>valid \<Gamma>; (x,S)\<in>set \<Gamma>; T \<prec> S\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| T_APP[intro]: "\<lbrakk>\<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1\<rightarrow>T\<^isub>2; \<Gamma> \<turnstile> t\<^isub>2 : T\<^isub>1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App t\<^isub>1 t\<^isub>2 : T\<^isub>2" 
| T_LAM[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,Ty T\<^isub>1)#\<Gamma>) \<turnstile> t : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T\<^isub>1\<rightarrow>T\<^isub>2"
| T_LET[intro]: "\<lbrakk>x\<sharp>\<Gamma>; \<Gamma> \<turnstile> t\<^isub>1 : T\<^isub>1; ((x,close \<Gamma> T\<^isub>1)#\<Gamma>) \<turnstile> t\<^isub>2 : T\<^isub>2; set (ftv T\<^isub>1 - ftv \<Gamma>) \<sharp>* T\<^isub>2\<rbrakk> 
                 \<Longrightarrow> \<Gamma> \<turnstile> Let x be t\<^isub>1 in t\<^isub>2 : T\<^isub>2"

equivariance typing[tvar]

lemma fresh_tvar_trm: 
  fixes X::"tvar"
  and   t::"trm"
  shows "X\<sharp>t"
by (nominal_induct t rule: trm.strong_induct) 
   (simp_all add: fresh_atm abs_fresh)

lemma ftv_ty: 
  fixes T::"ty"
  shows "supp T = set (ftv T)"
by (nominal_induct T rule: ty.strong_induct) 
   (simp_all add: ty.supp supp_atm)

lemma ftv_tyS: 
  fixes S::"tyS"
  shows "supp S = set (ftv S)"
by (nominal_induct S rule: tyS.strong_induct) 
   (auto simp add: tyS.supp abs_supp ftv_ty)

lemma ftv_Ctxt: 
  fixes \<Gamma>::"Ctxt"
  shows "supp \<Gamma> = set (ftv \<Gamma>)"
apply (induct \<Gamma>)
apply (simp_all add: supp_list_nil supp_list_cons)
apply (case_tac a)
apply (simp add: supp_prod supp_atm ftv_tyS)
done

lemma ftv_tvars: 
  fixes Tvs::"tvar list"
  shows "supp Tvs = set Tvs"
by (induct Tvs) 
   (simp_all add: supp_list_nil supp_list_cons supp_atm)

lemma difference_supp: 
  fixes xs ys::"tvar list"
  shows "((supp (xs - ys))::tvar set) = supp xs - supp ys"
by (induct xs) 
   (auto simp add: supp_list_nil supp_list_cons ftv_tvars)

lemma set_supp_eq: 
  fixes xs::"tvar list"
  shows "set xs = supp xs"
by (induct xs) 
   (simp_all add: supp_list_nil supp_list_cons supp_atm)

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

lemma freshs_mem:
  fixes S::"tvar set"
  assumes "x \<in> S"
  and     "S \<sharp>* z"
  shows  "x \<sharp> z"
using prems  by (simp add: fresh_star_def)

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

lemma gen_supp: 
  shows "(supp (gen T Xs)::tvar set) = supp T - supp Xs"
by (induct Xs) 
   (auto simp add: supp_list_nil supp_list_cons tyS.supp abs_supp supp_atm)

lemma minus_Int_eq: 
  shows "T - (T - U) = T \<inter> U"
  by blast

lemma close_supp: 
  shows "supp (close \<Gamma> T) = set (ftv T) \<inter> set (ftv \<Gamma>)"
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

lemma ftv_ty_subst:
  fixes T::"ty"
  and   \<theta>::"Subst"
  and   X Y ::"tvar"
  assumes a1: "X \<in> set (ftv T)"
  and     a2: "Y \<in> set (ftv (lookup \<theta> X))"
  shows "Y \<in> set (ftv (\<theta><T>))"
using a1 a2
by (nominal_induct T rule: ty.strong_induct) (auto)

lemma ftv_tyS_subst:
  fixes S::"tyS"
  and   \<theta>::"Subst"
  and   X Y::"tvar"
  assumes a1: "X \<in> set (ftv S)"
  and     a2: "Y \<in> set (ftv (lookup \<theta> X))"
  shows "Y \<in> set (ftv (\<theta><S>))"
using a1 a2
by (nominal_induct S avoiding: \<theta> Y rule: tyS.strong_induct) 
   (auto simp add: ftv_ty_subst fresh_atm)

lemma ftv_Ctxt_subst:
  fixes \<Gamma>::"Ctxt"
  and   \<theta>::"Subst"
  assumes a1: "X \<in> set (ftv \<Gamma>)"
  and     a2: "Y \<in> set (ftv (lookup \<theta> X))"
  shows "Y \<in> set (ftv (\<theta><\<Gamma>>))"
using a1 a2
by (induct \<Gamma>)
   (auto simp add: ftv_tyS_subst)

lemma gen_preserved1:
  assumes asm: "Xs \<sharp>* \<theta>"
  shows "\<theta><gen T Xs> = gen (\<theta><T>) Xs"
using asm
by (induct Xs) 
   (auto simp add: fresh_star_def)

lemma gen_preserved2:
  fixes T::"ty"
  and   \<Gamma>::"Ctxt"
  assumes asm: "((ftv T) - (ftv \<Gamma>)) \<sharp>* \<theta>"
  shows "((ftv (\<theta><T>)) - (ftv (\<theta><\<Gamma>>))) = ((ftv T) - (ftv \<Gamma>))"
using asm
apply(nominal_induct T rule: ty.strong_induct)
apply(auto simp add: fresh_star_def)
apply(simp add: lookup_fresh)
apply(simp add: ftv_Ctxt[symmetric])
apply(fold fresh_def)
apply(rule fresh_psubst_Ctxt)
apply(assumption)
apply(assumption)
apply(rule difference_supset)
apply(auto)
apply(simp add: ftv_Ctxt_subst)
done

lemma close_preserved:
  fixes \<Gamma>::"Ctxt"
  assumes asm: "((ftv T) - (ftv \<Gamma>)) \<sharp>* \<theta>"
  shows "\<theta><close \<Gamma> T> = close (\<theta><\<Gamma>>) (\<theta><T>)"
using asm
by (simp add: gen_preserved1 gen_preserved2)

lemma var_fresh_for_ty:
  fixes x::"var"
  and   T::"ty"
  shows "x\<sharp>T"
by (nominal_induct T rule: ty.strong_induct)
   (simp_all add: fresh_atm)

lemma var_fresh_for_tyS:
  fixes x::"var"
  and   S::"tyS"
  shows "x\<sharp>S"
by (nominal_induct S rule: tyS.strong_induct)
   (simp_all add: abs_fresh var_fresh_for_ty)

lemma psubst_fresh_Ctxt:
  fixes x::"var"
  and   \<Gamma>::"Ctxt"
  and   \<theta>::"Subst"
  shows "x\<sharp>\<theta><\<Gamma>> = x\<sharp>\<Gamma>"
by (induct \<Gamma>)
   (auto simp add: fresh_list_cons fresh_list_nil fresh_prod var_fresh_for_tyS)

lemma psubst_valid:
  fixes \<theta>::Subst
  and   \<Gamma>::Ctxt
  assumes a: "valid \<Gamma>"
  shows "valid (\<theta><\<Gamma>>)"
using a
by (induct) 
   (auto simp add: psubst_fresh_Ctxt)

lemma psubst_in:
  fixes \<Gamma>::"Ctxt"
  and   \<theta>::"Subst"
  and   pi::"tvar prm"
  and   S::"tyS"
  assumes a: "(x,S)\<in>set \<Gamma>"
  shows "(x,\<theta><S>)\<in>set (\<theta><\<Gamma>>)"
using a
by (induct \<Gamma>)
   (auto simp add: calc_atm)


lemma typing_preserved:
  fixes \<theta>::"Subst"
  and   pi::"tvar prm"
  assumes a: "\<Gamma> \<turnstile> t : T"
  shows "(\<theta><\<Gamma>>) \<turnstile> t : (\<theta><T>)"
using a
proof (nominal_induct \<Gamma> t T avoiding: \<theta> rule: typing.strong_induct)
  case (T_VAR \<Gamma> x S T)
  have a1: "valid \<Gamma>" by fact
  have a2: "(x, S) \<in> set \<Gamma>" by fact
  have a3: "T \<prec> S" by fact
  have  "valid (\<theta><\<Gamma>>)" using a1 by (simp add: psubst_valid)
  moreover
  have  "(x,\<theta><S>)\<in>set (\<theta><\<Gamma>>)" using a2 by (simp add: psubst_in)
  moreover
  have "\<theta><T> \<prec> \<theta><S>" using a3 by (simp add: general_preserved)
  ultimately show "(\<theta><\<Gamma>>) \<turnstile> Var x : (\<theta><T>)" by (simp add: typing.T_VAR)
next
  case (T_APP \<Gamma> t1 T1 T2 t2)
  have "\<theta><\<Gamma>> \<turnstile> t1 : \<theta><T1 \<rightarrow> T2>" by fact
  then have "\<theta><\<Gamma>> \<turnstile> t1 : (\<theta><T1>) \<rightarrow> (\<theta><T2>)" by simp
  moreover
  have "\<theta><\<Gamma>> \<turnstile> t2 : \<theta><T1>" by fact
  ultimately show "\<theta><\<Gamma>> \<turnstile> App t1 t2 : \<theta><T2>" by (simp add: typing.T_APP)
next
  case (T_LAM x \<Gamma> T1 t T2)
  fix pi::"tvar prm" and \<theta>::"Subst"
  have "x\<sharp>\<Gamma>" by fact
  then have "x\<sharp>\<theta><\<Gamma>>" by (simp add: psubst_fresh_Ctxt)
  moreover
  have "\<theta><((x, Ty T1)#\<Gamma>)> \<turnstile> t : \<theta><T2>" by fact
  then have "((x, Ty (\<theta><T1>))#(\<theta><\<Gamma>>)) \<turnstile> t : \<theta><T2>" by (simp add: calc_atm)
  ultimately show "\<theta><\<Gamma>> \<turnstile> Lam [x].t : \<theta><T1 \<rightarrow> T2>" by (simp add: typing.T_LAM)
next
  case (T_LET x \<Gamma> t1 T1 t2 T2)
  have vc: "((ftv T1) - (ftv \<Gamma>)) \<sharp>* \<theta>" by fact
  have "x\<sharp>\<Gamma>" by fact
   then have a1: "x\<sharp>\<theta><\<Gamma>>" by (simp add: calc_atm psubst_fresh_Ctxt)
  have a2: "\<theta><\<Gamma>> \<turnstile> t1 : \<theta><T1>" by fact 
  have a3: "\<theta><((x, close \<Gamma> T1)#\<Gamma>)> \<turnstile> t2 : \<theta><T2>" by fact
  from a2 a3 show "\<theta><\<Gamma>> \<turnstile> Let x be t1 in t2 : \<theta><T2>"
    apply -
    apply(rule better_T_LET)
    apply(rule a1)
    apply(rule a2)
    apply(simp add: close_preserved vc)
    done
qed



end
