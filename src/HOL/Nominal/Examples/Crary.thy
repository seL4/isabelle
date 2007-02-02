(* "$Id$" *)
(*                                                    *)
(* Formalisation of the chapter on Logical Relations  *)
(* and a Case Study in Equivalence Checking           *)
(* by Karl Crary from the book on Advanced Topics in  *)
(* Types and Programming Languages, MIT Press 2005    *)

(* The formalisation was done by Julien Narboux and   *)
(* Christian Urban                                    *)

theory Crary
  imports "Nominal"
begin

atom_decl name 

nominal_datatype ty = TBase 
                    | TUnit 
                    | Arrow "ty" "ty" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype trm = Unit
                     | Var "name"
                     | Lam "\<guillemotleft>name\<guillemotright>trm" ("Lam [_]._" [100,100] 100)
                     | App "trm" "trm"
                     | Const "nat"

(* The next 3 lemmas should be in the nominal library *)
lemma eq_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = (pi\<bullet>x=pi\<bullet>y)"
  apply(simp add: perm_bool perm_bij)
  done

lemma in_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  assumes "x\<in>X"
  shows "pi\<bullet>x \<in> pi\<bullet>X"
  using assms by (perm_simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])

lemma set_eqvt:
  fixes pi::"name prm"
  and   xs::"('a::pt_name) list"
  shows "pi\<bullet>(set xs) = set (pi\<bullet>xs)"
  by (perm_simp add: pt_list_set_pi[OF pt_name_inst])
(* end of library *)

lemma perm_ty[simp]: 
  fixes T::"ty"
  and   pi::"name prm"
  shows "pi\<bullet>T = T"
  by (induct T rule: ty.induct_weak) (simp_all)

lemma fresh_ty[simp]:
  fixes x::"name" 
  and   T::"ty"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

lemma ty_cases:
  fixes T::ty
  shows "(\<exists> T1 T2. T=T1\<rightarrow>T2) \<or> T=TUnit \<or> T=TBase"
by (induct T rule:ty.induct_weak) (auto)

text {* Size Functions *} 

instance ty :: size ..

nominal_primrec
  "size (TBase) = 1"
  "size (TUnit) = 1"
  "size (T1\<rightarrow>T2) = size T1 + size T2"
by (rule TrueI)+

instance trm :: size ..

nominal_primrec 
  "size (Unit) = 1"
  "size (Var x) = 1"
  "size (Lam [x].t) = size t + 1"
  "size (App t1 t2) = size t1 + size t2"
  "size (Const n) = 1"
apply(finite_guess add: fs_name1 perm_nat_def)+
apply(perm_full_simp add: perm_nat_def)
apply(simp add: fs_name1)
apply(rule TrueI)+
apply(simp add: fresh_nat)+
apply(fresh_guess add: fs_name1 perm_nat_def)+
done

lemma ty_size_greater_zero[simp]:
  fixes T::"ty"
  shows "size T > 0"
by (nominal_induct rule:ty.induct) (simp_all)

text {* valid contexts *}

inductive2
  valid :: "(name \<times> 'a::pt_name) list \<Rightarrow> bool"
where
    v_nil[intro]:  "valid []"
  | v_cons[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

lemma valid_eqvt[eqvt]:
  fixes   pi:: "name prm"
  assumes a: "valid \<Gamma>"
  shows "valid (pi\<bullet>\<Gamma>)"
  using a
  by (induct) (auto simp add: fresh_bij)

inductive_cases2  
  valid_cons_elim_auto[elim]:"valid ((x,T)#\<Gamma>)"

text {* typing judgements for terms *}

inductive2
  typing :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" (" _ \<turnstile> _ : _ " [60,60,60] 60) 
where
  t_Var[intro]:   "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| t_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e1 : T1\<rightarrow>T2; \<Gamma> \<turnstile> e2 : T1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T2"
| t_Lam[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T1)#\<Gamma> \<turnstile> t : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T1\<rightarrow>T2"
| t_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n : TBase"
| t_Unit[intro]:  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Unit : TUnit"

lemma typing_valid:
  assumes "\<Gamma> \<turnstile> t : T"
  shows "valid \<Gamma>"
  using assms
  by (induct) (auto)
 
lemma typing_eqvt[eqvt]:
  fixes pi::"name prm"
  assumes "\<Gamma> \<turnstile> t : T"
  shows "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>t) : (pi\<bullet>T)"
  using assms
  apply(induct)
  apply(auto simp add: fresh_bij set_eqvt valid_eqvt) 
  apply(rule t_Var)
  apply(drule valid_eqvt)
  apply(assumption)
  apply(drule in_eqvt)
  apply(simp add: set_eqvt)
  done

text {* Inversion lemmas for the typing judgment *}

declare trm.inject [simp add]
declare ty.inject  [simp add]

inductive_cases2 t_Lam_elim_auto[elim]: "\<Gamma> \<turnstile> Lam [x].t : T"
inductive_cases2 t_Var_elim_auto[elim]: "\<Gamma> \<turnstile> Var x : T"
inductive_cases2 t_App_elim_auto[elim]: "\<Gamma> \<turnstile> App x y : T"
inductive_cases2  t_Const_elim_auto[elim]: "\<Gamma> \<turnstile> Const n : T"
inductive_cases2  t_Unit_elim_auto[elim]: "\<Gamma> \<turnstile> Unit : TUnit"

declare trm.inject [simp del]
declare ty.inject [simp del]

lemma typing_induct_strong
  [consumes 1, case_names t_Var t_App t_Lam t_Const t_Unit]:
    fixes  P::"'a::fs_name \<Rightarrow> (name\<times>ty) list \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow>bool"
    and    x :: "'a::fs_name"
    assumes a: "\<Gamma> \<turnstile> e : T"
    and a1: "\<And>\<Gamma> x T c. \<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> P c \<Gamma> (Var x) T"
    and a2: "\<And>\<Gamma> e1 T1 T2 e2 c. \<lbrakk>\<And>c. P c \<Gamma> e1 (T1\<rightarrow>T2); \<And>c. P c \<Gamma> e2 T1\<rbrakk> 
             \<Longrightarrow> P c \<Gamma> (App e1 e2) T2"
    and a3: "\<And>x \<Gamma> T1 t T2 c.\<lbrakk>x\<sharp>(\<Gamma>,c); \<And>c. P c ((x,T1)#\<Gamma>) t T2\<rbrakk>
             \<Longrightarrow> P c \<Gamma> (Lam [x].t) (T1\<rightarrow>T2)"
    and a4: "\<And>\<Gamma> n c. valid \<Gamma> \<Longrightarrow> P c \<Gamma> (Const n) TBase"
    and a5: "\<And>\<Gamma> c. valid \<Gamma> \<Longrightarrow> P c \<Gamma> Unit TUnit"
    shows "P c \<Gamma> e T"
proof -
  from a have "\<And>(pi::name prm) c. P c (pi\<bullet>\<Gamma>) (pi\<bullet>e) (pi\<bullet>T)"
  proof (induct)
    case (t_Var \<Gamma> x T pi c)
    have "valid \<Gamma>" by fact
    then have "valid (pi\<bullet>\<Gamma>)" by (simp only: eqvt)
    moreover
    have "(x,T)\<in>set \<Gamma>" by fact
    then have "pi\<bullet>(x,T)\<in>pi\<bullet>(set \<Gamma>)" by (simp only: pt_set_bij[OF pt_name_inst, OF at_name_inst])  
    then have "(pi\<bullet>x,T)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: set_eqvt)
    ultimately show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>(Var x)) (pi\<bullet>T)" using a1 by simp
  next
    case (t_App \<Gamma> e1 T1 T2 e2 pi c)
    thus "P c (pi\<bullet>\<Gamma>) (pi\<bullet>(App e1 e2)) (pi\<bullet>T2)" using a2 
      by (simp only: eqvt) (blast)
  next
    case (t_Lam x \<Gamma> T1 t T2 pi c)
    obtain y::"name" where fs: "y\<sharp>(pi\<bullet>x,pi\<bullet>\<Gamma>,pi\<bullet>t,c)" by (erule exists_fresh[OF fs_name1])
    let ?sw = "[(pi\<bullet>x,y)]"
    let ?pi' = "?sw@pi"
    have f0: "x\<sharp>\<Gamma>" by fact
    have f1: "(pi\<bullet>x)\<sharp>(pi\<bullet>\<Gamma>)" using f0 by (simp add: fresh_bij)
    have f2: "y\<sharp>?pi'\<bullet>\<Gamma>" by (auto simp add: pt_name2 fresh_left calc_atm perm_pi_simp)
      have ih1: "\<And>c. P c (?pi'\<bullet>((x,T1)#\<Gamma>)) (?pi'\<bullet>t) (?pi'\<bullet>T2)" by fact
    then have "P c (?pi'\<bullet>\<Gamma>) (Lam [y].(?pi'\<bullet>t)) (T1\<rightarrow>T2)" using fs f2 a3
      by (simp add: calc_atm)
    then have "P c (?sw\<bullet>pi\<bullet>\<Gamma>) (?sw\<bullet>(Lam [(pi\<bullet>x)].(pi\<bullet>t))) (T1\<rightarrow>T2)" 
      by (simp del: append_Cons add: calc_atm pt_name2)
    moreover have "(?sw\<bullet>pi\<bullet>\<Gamma>) = (pi\<bullet>\<Gamma>)"
      by (rule perm_fresh_fresh) (simp_all add: fs f1)
    moreover have "(?sw\<bullet>(Lam [(pi\<bullet>x)].(pi\<bullet>t))) = Lam [(pi\<bullet>x)].(pi\<bullet>t)"
      by (rule perm_fresh_fresh) (simp_all add: fs f1 fresh_atm abs_fresh)
    ultimately show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>(Lam [x].t)) (pi\<bullet>T1\<rightarrow>T2)" by simp
  next
    case (t_Const \<Gamma> n pi c)
    thus "P c (pi\<bullet>\<Gamma>) (pi\<bullet>(Const n)) (pi\<bullet>TBase)" using a4 by (simp, blast intro: valid_eqvt)
  next
    case (t_Unit \<Gamma> pi c)
    thus "P c (pi\<bullet>\<Gamma>) (pi\<bullet>Unit) (pi\<bullet>TUnit)" using a5 by (simp, blast intro: valid_eqvt)
  qed 
  then have "P c (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>e) (([]::name prm)\<bullet>T)" by blast
  then show "P c \<Gamma> e T" by simp
qed

text {* capture-avoiding substitution *}

fun
  lookup :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm"   
where
  "lookup [] X        = Var X"
  "lookup ((Y,T)#\<theta>) X = (if X=Y then T else lookup \<theta> X)"

lemma lookup_eqvt:
  fixes pi::"name prm"
  and   \<theta>::"(name\<times>trm) list"
  and   X::"name"
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>)
   (auto simp add: perm_bij)

lemma lookup_fresh:
  fixes z::"name"
  assumes "z\<sharp>\<theta>" "z\<sharp>x"
  shows "z \<sharp>lookup \<theta> x"
using assms 
by (induct rule: lookup.induct) (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using assms 
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

consts
  psubst :: "(name\<times>trm) list \<Rightarrow> trm \<Rightarrow> trm"  ("_<_>" [60,100] 100)
 
nominal_primrec
  "\<theta><(Var x)> = (lookup \<theta> x)"
  "\<theta><(App t1 t2)> = App (\<theta><t1>) (\<theta><t2>)"
  "x\<sharp>\<theta> \<Longrightarrow> \<theta><(Lam [x].t)> = Lam [x].(\<theta><t>)"
  "\<theta><(Const n)> = Const n"
  "\<theta><(Unit)> = Unit"
apply(finite_guess add: fs_name1 lookup_eqvt)+
apply(perm_full_simp)
apply(simp add: fs_name1)
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess add: fs_name1 lookup_eqvt)+
done

abbreviation 
 subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)
where
  "t[x::=t']  \<equiv> ([(x,t')])<t>" 

lemma subst[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  and   "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
  and   "Const n[y::=t'] = Const n"
  and   "Unit [y::=t'] = Unit"
  by (simp_all add: fresh_list_cons fresh_list_nil)

lemma subst_eqvt[eqvt]:
  fixes pi::"name prm" 
  and   t::"trm"
  shows "pi\<bullet>(t[x::=t']) = (pi\<bullet>t)[(pi\<bullet>x)::=(pi\<bullet>t')]"
  by (nominal_induct t avoiding: x t' rule: trm.induct)
     (perm_simp add: fresh_bij)+

lemma subst_rename: 
  fixes c::"name"
  and   t1::"trm"
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
  using a
  apply(nominal_induct t1 avoiding: a c t2 rule: trm.induct)
  apply(simp add: trm.inject calc_atm fresh_atm abs_fresh perm_nat_def)+
  done

lemma fresh_psubst: 
  fixes z::"name"
  and   t::"trm"
  assumes "z\<sharp>t" "z\<sharp>\<theta>"
  shows "z\<sharp>(\<theta><t>)"
using assms
by (nominal_induct t avoiding: z \<theta> t rule: trm.induct)
   (auto simp add: abs_fresh lookup_fresh)

lemma fresh_subst'':
  fixes z::"name"
  and   t1::"trm"
  and   t2::"trm"
  assumes "z\<sharp>t2"
  shows "z\<sharp>t1[z::=t2]"
using assms 
by (nominal_induct t1 avoiding: t2 z rule: trm.induct)
   (auto simp add: abs_fresh fresh_nat fresh_atm)

lemma fresh_subst':
  fixes z::"name"
  and   t1::"trm"
  and   t2::"trm"
  assumes "z\<sharp>[y].t1" "z\<sharp>t2"
  shows "z\<sharp>t1[y::=t2]"
using assms 
by (nominal_induct t1 avoiding: y t2 z rule: trm.induct)
   (auto simp add: abs_fresh fresh_nat fresh_atm)

lemma fresh_subst:
  fixes z::"name"
  and   t1::"trm"
  and   t2::"trm"
  assumes "z\<sharp>t1" "z\<sharp>t2"
  shows "z\<sharp>t1[y::=t2]"
using assms fresh_subst'
by (auto simp add: abs_fresh) 

lemma fresh_psubst_simpl:
  assumes "x\<sharp>t"
  shows "(x,u)#\<theta><t> = \<theta><t>" 
using assms
proof (nominal_induct t avoiding: x u \<theta> rule: trm.induct)
  case (Lam y t x u)
  have fs: "y\<sharp>\<theta>" "y\<sharp>x" "y\<sharp>u" by fact
  moreover have "x\<sharp> Lam [y].t" by fact 
  ultimately have "x\<sharp>t" by (simp add: abs_fresh fresh_atm)
  moreover have ih:"\<And>n T. n\<sharp>t \<Longrightarrow> ((n,T)#\<theta>)<t> = \<theta><t>" by fact
  ultimately have "(x,u)#\<theta><t> = \<theta><t>" by auto
  moreover have "(x,u)#\<theta><Lam [y].t> = Lam [y]. ((x,u)#\<theta><t>)" using fs 
    by (simp add: fresh_list_cons fresh_prod)
  moreover have " \<theta><Lam [y].t> = Lam [y]. (\<theta><t>)" using fs by simp
  ultimately show "(x,u)#\<theta><Lam [y].t> = \<theta><Lam [y].t>" by auto
qed (auto simp add: fresh_atm abs_fresh)

text {* Equivalence (defined) *}

inductive2
  equiv_def :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ == _ : _" [60,60] 60) 
where
  Q_Refl[intro]:  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> t == t : T"
| Q_Symm[intro]:  "\<Gamma> \<turnstile> t == s : T \<Longrightarrow> \<Gamma> \<turnstile> s == t : T"
| Q_Trans[intro]: "\<lbrakk>\<Gamma> \<turnstile> s == t : T; \<Gamma> \<turnstile> t == u : T\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> s == u : T"
| Q_Abs[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T1)#\<Gamma> \<turnstile> s2 == t2 : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. s2 ==  Lam [x]. t2 : T1 \<rightarrow> T2"
| Q_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> s1 == t1 : T1 \<rightarrow> T2 ; \<Gamma> \<turnstile> s2 == t2 : T1\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> App s1 s2 == App t1 t2 : T2"
| Q_Beta[intro]:  "\<lbrakk>x\<sharp>(\<Gamma>,s2,t2); (x,T1)#\<Gamma> \<turnstile> s12 == t12 : T2 ; \<Gamma> \<turnstile> s2 == t2 : T1\<rbrakk> 
                   \<Longrightarrow>  \<Gamma> \<turnstile> App (Lam [x]. s12) s2 ==  t12[x::=t2] : T2"
| Q_Ext[intro]:   "\<lbrakk>x\<sharp>(\<Gamma>,s,t); (x,T1)#\<Gamma> \<turnstile> App s (Var x) == App t (Var x) : T2\<rbrakk> 
                   \<Longrightarrow> \<Gamma> \<turnstile> s == t : T1 \<rightarrow> T2"

lemma equiv_def_valid:
  assumes "\<Gamma> \<turnstile> t == s : T"
  shows "valid \<Gamma>"
using assms by (induct,auto elim:typing_valid)

lemma equiv_def_eqvt[eqvt]:
  fixes pi::"name prm"
  assumes a: "\<Gamma> \<turnstile> s == t : T"
  shows "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>s) == (pi\<bullet>t) : (pi\<bullet>T)"
using a
apply(induct)
apply(auto intro: typing_eqvt valid_eqvt simp add: fresh_bij subst_eqvt simp del: perm_ty)
apply(rule_tac x="pi\<bullet>x" in Q_Ext)
apply(simp add: fresh_bij)+
done

lemma equiv_def_strong_induct
  [consumes 1, case_names Q_Refl Q_Symm Q_Trans Q_Abs Q_App Q_Beta Q_Ext]:
  fixes c::"'a::fs_name"
  assumes a0: "\<Gamma> \<turnstile> s == t : T" 
  and     a1: "\<And>\<Gamma> t T c.  \<Gamma> \<turnstile> t : T  \<Longrightarrow> P c \<Gamma> t t T"
  and     a2: "\<And>\<Gamma> t s T c. \<lbrakk>\<And>d. P d \<Gamma> t s T\<rbrakk> \<Longrightarrow>  P c \<Gamma> s t T"
  and     a3: "\<And>\<Gamma> s t T u c. \<lbrakk>\<And>d. P d \<Gamma> s t T; \<And>d. P d \<Gamma> t u T\<rbrakk> 
               \<Longrightarrow> P c \<Gamma> s u T"
  and     a4: "\<And>x \<Gamma> T1 s2 t2 T2 c. \<lbrakk>x\<sharp>\<Gamma>; x\<sharp>c; \<And>d. P d ((x,T1)#\<Gamma>) s2 t2 T2\<rbrakk>
               \<Longrightarrow> P c \<Gamma> (Lam [x].s2) (Lam [x].t2) (T1\<rightarrow>T2)"
  and     a5: "\<And>\<Gamma> s1 t1 T1 T2 s2 t2 c. \<lbrakk>\<And>d. P d \<Gamma> s1 t1 (T1\<rightarrow>T2); \<And>d. P d \<Gamma> s2 t2 T1\<rbrakk> 
               \<Longrightarrow> P c \<Gamma> (App s1 s2) (App t1 t2) T2"
  and     a6: "\<And>x \<Gamma> T1 s12 t12 T2 s2 t2 c.
               \<lbrakk>x\<sharp>(\<Gamma>,s2,t2); x\<sharp>c; \<And>d. P d ((x,T1)#\<Gamma>) s12 t12 T2; \<And>d. P d \<Gamma> s2 t2 T1\<rbrakk> 
               \<Longrightarrow> P c \<Gamma> (App (Lam [x].s12) s2) (t12[x::=t2]) T2"
  and     a7: "\<And>x \<Gamma> s t T1 T2 c.
               \<lbrakk>x\<sharp>(\<Gamma>,s,t); \<And>d. P d ((x,T1)#\<Gamma>) (App s (Var x)) (App t (Var x)) T2\<rbrakk>
               \<Longrightarrow> P c \<Gamma> s t (T1\<rightarrow>T2)"
 shows "P c \<Gamma>  s t T"
proof -
  from a0 have "\<And>(pi::name prm) c. P c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) (pi\<bullet>T)" 
    proof(induct)
      case (Q_Refl \<Gamma> t T pi c)
      then show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>t) (pi\<bullet>t) (pi\<bullet>T)" using a1 by (simp only: eqvt)
    next
      case (Q_Symm \<Gamma> t s T pi c)
      then show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) (pi\<bullet>T)" using a2 by (simp only: equiv_def_eqvt)
    next
      case (Q_Trans \<Gamma> s t T u pi c)
      then show " P c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>u) (pi\<bullet>T)" using a3 by (blast intro: equiv_def_eqvt)
    next
      case (Q_App \<Gamma> s1 t1 T1 T2 s2 t2 pi c)
      then show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>App s1 s2) (pi\<bullet>App t1 t2) (pi\<bullet>T2)" using a5 
	by (simp only: eqvt) (blast)
    next
      case (Q_Ext x \<Gamma> s t T1 T2 pi c)
      then show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) (pi\<bullet>T1\<rightarrow>T2)"  
	by (auto intro!: a7 simp add: fresh_bij)
    next
      case (Q_Abs x \<Gamma> T1 s2 t2 T2 pi c)
      obtain y::"name" where fs: "y\<sharp>(pi\<bullet>x,pi\<bullet>s2,pi\<bullet>t2,pi\<bullet>\<Gamma>,c)" by (rule exists_fresh[OF fs_name1])
      let ?sw="[(pi\<bullet>x,y)]"
      let ?pi'="?sw@pi"
      have f1: "x\<sharp>\<Gamma>" by fact
      have f2: "(pi\<bullet>x)\<sharp>(pi\<bullet>\<Gamma>)" using f1 by (simp add: fresh_bij)
      have f3: "y\<sharp>?pi'\<bullet>\<Gamma>" using f1 by (auto simp add: pt_name2 fresh_left calc_atm perm_pi_simp)
      have ih1: "\<And>c. P c (?pi'\<bullet>((x,T1)#\<Gamma>)) (?pi'\<bullet>s2) (?pi'\<bullet>t2) (?pi'\<bullet>T2)" by fact
      then have "\<And>c. P c ((y,T1)#(?pi'\<bullet>\<Gamma>)) (?pi'\<bullet>s2) (?pi'\<bullet>t2) T2" by (simp add: calc_atm)
      then have "P c  (?pi'\<bullet>\<Gamma>) (?pi'\<bullet>Lam [x].s2) (?pi'\<bullet>Lam [x].t2) (T1\<rightarrow>T2)" using a4 f3 fs
	by (simp add: calc_atm)
      then have "P c (?sw\<bullet>pi\<bullet>\<Gamma>) (?sw\<bullet>Lam [(pi\<bullet>x)].(pi\<bullet>s2)) (?sw\<bullet>Lam [(pi\<bullet>x)].(pi\<bullet>t2)) (T1\<rightarrow>T2)" 
	by (simp del: append_Cons add: calc_atm pt_name2)
      moreover have "(?sw\<bullet>(pi\<bullet>\<Gamma>)) = (pi\<bullet>\<Gamma>)" 
	by (rule perm_fresh_fresh) (simp_all add: fs f2)
      moreover have "(?sw\<bullet>(Lam [(pi\<bullet>x)].(pi\<bullet>s2))) = Lam [(pi\<bullet>x)].(pi\<bullet>s2)" 
	by (rule perm_fresh_fresh) (simp_all add: fs f2 abs_fresh)
      moreover have "(?sw\<bullet>(Lam [(pi\<bullet>x)].(pi\<bullet>t2))) = Lam [(pi\<bullet>x)].(pi\<bullet>t2)" 
	by (rule perm_fresh_fresh) (simp_all add: fs f2 abs_fresh)
      ultimately have "P c (pi\<bullet>\<Gamma>) (Lam [(pi\<bullet>x)].(pi\<bullet>s2)) (Lam [(pi\<bullet>x)].(pi\<bullet>t2)) (T1\<rightarrow>T2)" by simp
      then show  "P c (pi\<bullet>\<Gamma>) (pi\<bullet>Lam [x].s2) (pi\<bullet>Lam [x].t2) (pi\<bullet>T1\<rightarrow>T2)" by simp 
    next 
      case (Q_Beta x \<Gamma> s2 t2 T1 s12 t12 T2 pi c) 
      obtain y::"name" where fs: "y\<sharp>(pi\<bullet>x,pi\<bullet>s12,pi\<bullet>t12,pi\<bullet>s2,pi\<bullet>t2,pi\<bullet>\<Gamma>,c)" 
	by (rule exists_fresh[OF fs_name1])
      let ?sw="[(pi\<bullet>x,y)]"
      let ?pi'="?sw@pi"
      have f1: "x\<sharp>(\<Gamma>,s2,t2)" by fact 
      have f2: "(pi\<bullet>x)\<sharp>(pi\<bullet>(\<Gamma>,s2,t2))" using f1 by (simp add: fresh_bij)
      have f3: "y\<sharp>(?pi'\<bullet>(\<Gamma>,s2,t2))" using f1 
	by (auto simp add: pt_name2 fresh_left calc_atm perm_pi_simp fresh_prod)
      have ih1: "\<And>c. P c (?pi'\<bullet>((x,T1)#\<Gamma>)) (?pi'\<bullet>s12) (?pi'\<bullet>t12) (?pi'\<bullet>T2)" by fact
      then have "\<And>c. P c ((y,T1)#(?pi'\<bullet>\<Gamma>)) (?pi'\<bullet>s12) (?pi'\<bullet>t12) (?pi'\<bullet>T2)" by (simp add: calc_atm)
      moreover
      have ih2: "\<And>c. P c (?pi'\<bullet>\<Gamma>) (?pi'\<bullet>s2) (?pi'\<bullet>t2) (?pi'\<bullet>T1)" by fact
      ultimately have "P c  (?pi'\<bullet>\<Gamma>) (?pi'\<bullet>(App (Lam [x].s12) s2)) (?pi'\<bullet>(t12[x::=t2])) (?pi'\<bullet>T2)" 
	using a6 f3 fs by (force simp add: subst_eqvt calc_atm del: perm_ty)
      then have "P c (?sw\<bullet>pi\<bullet>\<Gamma>) (?sw\<bullet>(App (Lam [(pi\<bullet>x)].(pi\<bullet>s12)) (pi\<bullet>s2))) 
	(?sw\<bullet>((pi\<bullet>t12)[(pi\<bullet>x)::=(pi\<bullet>t2)])) T2" 
	by (simp del: append_Cons add: calc_atm pt_name2 subst_eqvt)
      moreover have "(?sw\<bullet>(pi\<bullet>\<Gamma>)) = (pi\<bullet>\<Gamma>)" 
	by (rule perm_fresh_fresh) (simp_all add: fs[simplified] f2[simplified])
      moreover have "(?sw\<bullet>(App (Lam [(pi\<bullet>x)].(pi\<bullet>s12)) (pi\<bullet>s2))) = App (Lam [(pi\<bullet>x)].(pi\<bullet>s12)) (pi\<bullet>s2)" 
	by (rule perm_fresh_fresh) (simp_all add: fs[simplified] f2[simplified] abs_fresh)
      moreover have "(?sw\<bullet>((pi\<bullet>t12)[(pi\<bullet>x)::=(pi\<bullet>t2)])) = ((pi\<bullet>t12)[(pi\<bullet>x)::=(pi\<bullet>t2)])" 
	by (rule perm_fresh_fresh) 
	   (simp_all add: fs[simplified] f2[simplified] fresh_subst fresh_subst'')
      ultimately have "P c (pi\<bullet>\<Gamma>) (App (Lam [(pi\<bullet>x)].(pi\<bullet>s12)) (pi\<bullet>s2)) ((pi\<bullet>t12)[(pi\<bullet>x)::=(pi\<bullet>t2)]) T2"
	by simp
      then show "P c (pi\<bullet>\<Gamma>) (pi\<bullet>App (Lam [x].s12) s2) (pi\<bullet>t12[x::=t2]) (pi\<bullet>T2)" by (simp add: subst_eqvt)
    qed
  then have "P c (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>s) (([]::name prm)\<bullet>t) (([]::name prm)\<bullet>T)" by blast
  then show "P c \<Gamma> s t T" by simp
qed

text {* Weak head reduction *}

inductive2
  whr_def :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<leadsto> _" [80,80] 80) 
where
  QAR_Beta[intro]: "App (Lam [x]. t12) t2 \<leadsto> t12[x::=t2]"
| QAR_App[intro]: "t1 \<leadsto> t1' \<Longrightarrow> App t1 t2 \<leadsto> App t1' t2"

declare trm.inject  [simp add]
declare ty.inject  [simp add]

inductive_cases2 whr_Gen[elim]: "t \<leadsto> t'"
inductive_cases2 whr_Lam[elim]: "Lam [x].t \<leadsto> t'"
inductive_cases2 whr_App_Lam[elim]: "App (Lam [x].t12) t2 \<leadsto> t"
inductive_cases2 whr_Var[elim]: "Var x \<leadsto> t"
inductive_cases2 whr_Const[elim]: "Const n \<leadsto> t"
inductive_cases2 whr_App[elim]: "App p q \<leadsto> t"
inductive_cases2 whr_Const_Right[elim]: "t \<leadsto> Const n"
inductive_cases2 whr_Var_Right[elim]: "t \<leadsto> Var x"
inductive_cases2 whr_App_Right[elim]: "t \<leadsto> App p q"

declare trm.inject  [simp del]
declare ty.inject  [simp del]

text {* Weak head normalization *}

abbreviation 
 nf :: "trm \<Rightarrow> bool" ("_ \<leadsto>|" [100] 100)
where
  "t\<leadsto>|  \<equiv> \<not>(\<exists> u. t \<leadsto> u)" 

inductive2
  whn_def :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<Down> _" [80,80] 80) 
where
  QAN_Reduce[intro]: "\<lbrakk>s \<leadsto> t; t \<Down> u\<rbrakk> \<Longrightarrow> s \<Down> u"
| QAN_Normal[intro]: "t\<leadsto>|  \<Longrightarrow> t \<Down> t"

lemma whr_eqvt:
  fixes pi::"name prm"
  assumes a: "t \<leadsto> t'"
  shows "(pi\<bullet>t) \<leadsto> (pi\<bullet>t')"
using a
by (induct) (auto simp add: subst_eqvt fresh_bij)

lemma whn_eqvt[eqvt]:
  fixes pi::"name prm"
  assumes a: "t \<Down> t'"
  shows "(pi\<bullet>t) \<Down> (pi\<bullet>t')"
using a
apply(induct)
apply(rule QAN_Reduce)
apply(rule whr_eqvt)
apply(assumption)+
apply(rule QAN_Normal)
apply(auto)
apply(drule_tac pi="rev pi" in whr_eqvt)
apply(perm_simp)
done

text {* Algorithmic term equivalence and algorithmic path equivalence *}

inductive2
  alg_equiv :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ <=> _ : _" [60,60] 60) 
and
  alg_path_equiv :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ \<leftrightarrow> _ : _" [60,60] 60) 
where
  QAT_Base[intro]:  "\<lbrakk>s \<Down> p; t \<Down> q; \<Gamma> \<turnstile> p \<leftrightarrow> q : TBase \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s <=> t : TBase"
| QAT_Arrow[intro]: "\<lbrakk>x\<sharp>\<Gamma>; x\<sharp>s; x\<sharp>t; (x,T1)#\<Gamma> \<turnstile> App s (Var x) <=> App t (Var x) : T2\<rbrakk> 
                     \<Longrightarrow> \<Gamma> \<turnstile> s <=> t : T1 \<rightarrow> T2"
| QAT_One[intro]:   "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> s <=> t : TUnit"
| QAP_Var[intro]:   "\<lbrakk>valid \<Gamma>;(x,T) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x \<leftrightarrow> Var x : T"
| QAP_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> p \<leftrightarrow> q : T1 \<rightarrow> T2; \<Gamma> \<turnstile> s <=> t : T1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App p s \<leftrightarrow> App q t : T2"
| QAP_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n \<leftrightarrow> Const n : TBase"

lemma alg_equiv_alg_path_equiv_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "\<Gamma> \<turnstile> s <=> t : T \<Longrightarrow> (pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>s) <=> (pi\<bullet>t) : (pi\<bullet>T)" 
  and   "\<Gamma> \<turnstile> p \<leftrightarrow> q : T \<Longrightarrow> (pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>p) \<leftrightarrow> (pi\<bullet>q) : (pi\<bullet>T)"
apply(induct rule: alg_equiv_alg_path_equiv.inducts)
apply(auto intro: whn_eqvt simp add: fresh_bij valid_eqvt)
apply(rule_tac x="pi\<bullet>x" in  QAT_Arrow)
apply(auto simp add: fresh_bij)
apply(rule QAP_Var)
apply(simp add: valid_eqvt)
apply(simp add: pt_list_set_pi[OF pt_name_inst, symmetric])
apply(perm_simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])
done

lemma alg_equiv_alg_path_equiv_strong_induct
  [case_names QAT_Base QAT_Arrow QAT_One QAP_Var QAP_App QAP_Const]:
  fixes c::"'a::fs_name"
  assumes a1: "\<And>s p t q \<Gamma> c. \<lbrakk>s \<Down> p; t \<Down> q; \<Gamma> \<turnstile> p \<leftrightarrow> q : TBase; \<And>d. P2 d \<Gamma> p q TBase\<rbrakk> 
               \<Longrightarrow> P1 c \<Gamma> s t TBase"
  and     a2: "\<And>x \<Gamma> s t T1 T2 c.
               \<lbrakk>x\<sharp>\<Gamma>; x\<sharp>s; x\<sharp>t; x\<sharp>c; (x,T1)#\<Gamma> \<turnstile> App s (Var x) <=> App t (Var x) : T2;
               \<And>d. P1 d ((x,T1)#\<Gamma>) (App s (Var x)) (App t (Var x)) T2\<rbrakk>
               \<Longrightarrow> P1 c \<Gamma> s t (T1\<rightarrow>T2)"
  and     a3: "\<And>\<Gamma> s t c. valid \<Gamma> \<Longrightarrow> P1 c \<Gamma> s t TUnit"
  and     a4: "\<And>\<Gamma> x T c. \<lbrakk>valid \<Gamma>; (x,T) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> P2 c \<Gamma> (Var x) (Var x) T"
  and     a5: "\<And>\<Gamma> p q T1 T2 s t c.
               \<lbrakk>\<Gamma> \<turnstile> p \<leftrightarrow> q : T1\<rightarrow>T2; \<And>d. P2 d \<Gamma> p q (T1\<rightarrow>T2); \<Gamma> \<turnstile> s <=> t : T1; \<And>d. P1 d \<Gamma> s t T1\<rbrakk>
               \<Longrightarrow> P2 c \<Gamma> (App p s) (App q t) T2"
  and     a6: "\<And>\<Gamma> n c. valid \<Gamma> \<Longrightarrow> P2 c \<Gamma> (Const n) (Const n) TBase"
  shows "(\<Gamma> \<turnstile> s <=> t : T \<longrightarrow>P1 c \<Gamma> s t T) \<and> (\<Gamma>' \<turnstile> s' \<leftrightarrow> t' : T' \<longrightarrow> P2 c \<Gamma>' s' t' T')"
proof -
  have "(\<Gamma> \<turnstile> s <=> t : T \<longrightarrow> (\<forall>c (pi::name prm). P1 c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) T)) \<and> 
        (\<Gamma>' \<turnstile> s' \<leftrightarrow> t' : T' \<longrightarrow> (\<forall>c (pi::name prm). P2 c (pi\<bullet>\<Gamma>') (pi\<bullet>s') (pi\<bullet>t') T'))"
  proof(induct rule: alg_equiv_alg_path_equiv.induct)
    case (QAT_Base s q t p \<Gamma>)
    then show "\<forall>c (pi::name prm). P1 c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) TBase"
      apply(auto)
      apply(rule_tac p="pi\<bullet>q" and q="pi\<bullet>p" in  a1)
      apply(simp_all add: whn_eqvt alg_equiv_alg_path_equiv_eqvt[simplified])
      done
  next
    case (QAT_Arrow x \<Gamma> s t T1 T2)
    show ?case
    proof (rule allI, rule allI)
      fix c::"'a::fs_name" and pi::"name prm"
      obtain y::"name" where fs: "y\<sharp>(pi\<bullet>s,pi\<bullet>t,pi\<bullet>\<Gamma>,c)" by (rule exists_fresh[OF fs_name1])
      let ?sw="[(pi\<bullet>x,y)]"
      let ?pi'="?sw@pi"
      have f0: "x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" by fact
      then have f1: "x\<sharp>(\<Gamma>,s,t)" by simp
      have f2: "(pi\<bullet>x)\<sharp>(pi\<bullet>(\<Gamma>,s,t))" using f1 by (simp add: fresh_bij)
      have f3: "y\<sharp>?pi'\<bullet>(\<Gamma>,s,t)" using f1 
	by (simp only: pt_name2 fresh_left, auto simp add: perm_pi_simp calc_atm)
      then have f3': "y\<sharp>?pi'\<bullet>\<Gamma>" "y\<sharp>?pi'\<bullet>s" "y\<sharp>?pi'\<bullet>t" by (auto simp add: fresh_prod)
      have pr1: "(x,T1)#\<Gamma> \<turnstile> App s (Var x) <=> App t (Var x) : T2" by fact
      then have "(?pi'\<bullet>((x,T1)#\<Gamma>)) \<turnstile> (?pi'\<bullet>(App s (Var x))) <=> (?pi'\<bullet>(App t (Var x))) : (?pi'\<bullet>T2)" 
	by (rule alg_equiv_alg_path_equiv_eqvt)
      then have "(y,T1)#(?pi'\<bullet>\<Gamma>) \<turnstile> (App (?pi'\<bullet>s) (Var y)) <=> (App (?pi'\<bullet>t) (Var y)) : T2" 
	by (simp add: calc_atm)
      moreover    
      have ih1: "\<forall>c (pi::name prm).  P1 c (pi\<bullet>((x,T1)#\<Gamma>)) (pi\<bullet>App s (Var x)) (pi\<bullet>App t (Var x)) T2"
	by fact
      then have "\<And>c.  P1 c (?pi'\<bullet>((x,T1)#\<Gamma>)) (?pi'\<bullet>App s (Var x)) (?pi'\<bullet>App t (Var x)) T2"
	by auto
      then have "\<And>c.  P1 c ((y,T1)#(?pi'\<bullet>\<Gamma>)) (App (?pi'\<bullet>s) (Var y)) (App (?pi'\<bullet>t) (Var y)) T2"
	by (simp add: calc_atm)     
      ultimately have "P1 c (?pi'\<bullet>\<Gamma>) (?pi'\<bullet>s) (?pi'\<bullet>t) (T1\<rightarrow>T2)" using a2 f3' fs by simp
      then have "P1 c (?sw\<bullet>pi\<bullet>\<Gamma>) (?sw\<bullet>pi\<bullet>s) (?sw\<bullet>pi\<bullet>t) (T1\<rightarrow>T2)" 
	by (simp del: append_Cons add: calc_atm pt_name2)
      moreover have "(?sw\<bullet>(pi\<bullet>\<Gamma>)) = (pi\<bullet>\<Gamma>)" 
	by (rule perm_fresh_fresh) (simp_all add: fs[simplified] f2[simplified])
      moreover have "(?sw\<bullet>(pi\<bullet>s)) = (pi\<bullet>s)" 
	by (rule perm_fresh_fresh) (simp_all add: fs[simplified] f2[simplified])
      moreover have "(?sw\<bullet>(pi\<bullet>t)) = (pi\<bullet>t)" 
	by (rule perm_fresh_fresh) (simp_all add: fs[simplified] f2[simplified])
      ultimately show "P1 c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) (T1\<rightarrow>T2)" by (simp)
    qed
  next
    case (QAT_One \<Gamma> s t)
    then show "\<forall>c (pi::name prm). P1 c (pi\<bullet>\<Gamma>) (pi\<bullet>s) (pi\<bullet>t) TUnit"
      by (auto intro!: a3 simp add: valid_eqvt)
  next
    case (QAP_Var \<Gamma> x T)
    then show "\<forall>c (pi::name prm). P2 c (pi \<bullet> \<Gamma>) (pi \<bullet> Var x) (pi \<bullet> Var x) T"
      apply(auto intro!: a4 simp add: valid_eqvt)
      apply(simp add: pt_list_set_pi[OF pt_name_inst, symmetric])
      apply(perm_simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])
      done
  next
    case (QAP_App \<Gamma> p q T1 T2 s t)
    then show "\<forall>c (pi::name prm). P2 c (pi\<bullet>\<Gamma>) (pi\<bullet>App p s) (pi\<bullet>App q t) T2"
      by (auto intro!: a5 simp add: alg_equiv_alg_path_equiv_eqvt[simplified])
  next
    case (QAP_Const \<Gamma> n)
    then show "\<forall>c (pi::name prm). P2 c (pi\<bullet>\<Gamma>) (pi\<bullet>Const n) (pi\<bullet>Const n) TBase"
      by (auto intro!: a6 simp add: valid_eqvt)
  qed
  then have "(\<Gamma> \<turnstile> s <=> t : T \<longrightarrow> P1 c (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>s) (([]::name prm)\<bullet>t) T) \<and> 
             (\<Gamma>' \<turnstile> s' \<leftrightarrow> t' : T' \<longrightarrow> P2 c (([]::name prm)\<bullet>\<Gamma>') (([]::name prm)\<bullet>s') (([]::name prm)\<bullet>t') T')"
    by blast
  then show ?thesis by simp
qed

(* post-processing of the strong induction principle proved above; *) 
(* the code extracts the strong_inducts-version from strong_induct *)
setup {*
  PureThy.add_thmss
    [(("alg_equiv_alg_path_equiv_strong_inducts",
      ProjectRule.projects (ProofContext.init (the_context())) [1,2]
        (thm "alg_equiv_alg_path_equiv_strong_induct")), [])] #> snd
*}

declare trm.inject  [simp add]
declare ty.inject  [simp add]

inductive_cases2 whn_inv_auto[elim]: "t \<Down> t'"

inductive_cases2 alg_equiv_Base_inv_auto[elim]: "\<Gamma> \<turnstile> s<=>t : TBase"
inductive_cases2 alg_equiv_Arrow_inv_auto[elim]: "\<Gamma> \<turnstile> s<=>t : T1 \<rightarrow> T2"

inductive_cases2 alg_path_equiv_Base_inv_auto[elim]: "\<Gamma> \<turnstile> s\<leftrightarrow>t : TBase"
inductive_cases2 alg_path_equiv_Unit_inv_auto[elim]: "\<Gamma> \<turnstile> s\<leftrightarrow>t : TUnit"
inductive_cases2 alg_path_equiv_Arrow_inv_auto[elim]: "\<Gamma> \<turnstile> s\<leftrightarrow>t : T1 \<rightarrow> T2"

inductive_cases2 alg_path_equiv_Var_left_inv_auto[elim]: "\<Gamma> \<turnstile> Var x \<leftrightarrow> t : T"
inductive_cases2 alg_path_equiv_Var_left_inv_auto'[elim]: "\<Gamma> \<turnstile> Var x \<leftrightarrow> t : T'"
inductive_cases2 alg_path_equiv_Var_right_inv_auto[elim]: "\<Gamma> \<turnstile> s \<leftrightarrow> Var x : T"
inductive_cases2 alg_path_equiv_Var_right_inv_auto'[elim]: "\<Gamma> \<turnstile> s \<leftrightarrow> Var x : T'"
inductive_cases2 alg_path_equiv_Const_left_inv_auto[elim]: "\<Gamma> \<turnstile> Const n \<leftrightarrow> t : T"
inductive_cases2 alg_path_equiv_Const_right_inv_auto[elim]: "\<Gamma> \<turnstile> s \<leftrightarrow> Const n : T"
inductive_cases2 alg_path_equiv_App_left_inv_auto[elim]: "\<Gamma> \<turnstile> App p s \<leftrightarrow> t : T"
inductive_cases2 alg_path_equiv_App_right_inv_auto[elim]: "\<Gamma> \<turnstile> s \<leftrightarrow> App q t : T"
inductive_cases2 alg_path_equiv_Lam_left_inv_auto[elim]: "\<Gamma> \<turnstile> Lam[x].s \<leftrightarrow> t : T"
inductive_cases2 alg_path_equiv_Lam_right_inv_auto[elim]: "\<Gamma> \<turnstile> t \<leftrightarrow> Lam[x].s : T"

declare trm.inject [simp del]
declare ty.inject [simp del]

text {* Subcontext. *}

abbreviation
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [55,55] 55)
where
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> (\<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow>  (a,\<sigma>)\<in>set \<Gamma>2) \<and> valid \<Gamma>2"

lemma alg_equiv_valid:
  shows  "\<Gamma> \<turnstile> s <=> t : T \<Longrightarrow> valid \<Gamma>" and  "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> valid \<Gamma>"
by (induct rule : alg_equiv_alg_path_equiv.inducts, auto)

lemma algorithmic_monotonicity:
  fixes \<Gamma>':: "(name\<times>ty) list"
  shows "\<Gamma> \<turnstile> s <=> t : T \<Longrightarrow> \<Gamma>\<lless>\<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile> s <=> t : T"
  and "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> \<Gamma>\<lless>\<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile> s \<leftrightarrow> t : T"
proof (nominal_induct \<Gamma> s t T and \<Gamma> s t T avoiding: \<Gamma>' rule: alg_equiv_alg_path_equiv_strong_inducts)
  case (QAT_Arrow x \<Gamma> s t T1 T2 \<Gamma>')
  have fs:"x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" by fact
  have h2:"\<Gamma>\<lless>\<Gamma>'" by fact
  have ih:"\<And>\<Gamma>'. \<lbrakk>(x,T1)#\<Gamma> \<lless> \<Gamma>'\<rbrakk>  \<Longrightarrow> \<Gamma>' \<turnstile> App s (Var x) <=> App t (Var x) : T2" by fact
  have "x\<sharp>\<Gamma>'" by fact
  then have sub:"(x,T1)#\<Gamma> \<lless> (x,T1)#\<Gamma>'" using h2 by auto
  then have "(x,T1)#\<Gamma>' \<turnstile> App s (Var x) <=> App t (Var x) : T2" using ih by auto
  then show "\<Gamma>' \<turnstile> s <=> t : T1\<rightarrow>T2" using sub fs by auto
qed (auto)

text {* Logical equivalence. *}

function log_equiv :: "((name\<times>ty) list \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool)"   
                      ("_ \<turnstile> _ is _ : _" [60,60,60,60] 60) 
where    
   "\<Gamma> \<turnstile> s is t : TUnit = valid \<Gamma>"
 | "\<Gamma> \<turnstile> s is t : TBase = \<Gamma> \<turnstile> s <=> t : TBase"
 | "\<Gamma> \<turnstile> s is t : (T1 \<rightarrow> T2) =  
           (valid \<Gamma> \<and> (\<forall>\<Gamma>' s' t'. \<Gamma>\<lless>\<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> s' is t' : T1 \<longrightarrow>  (\<Gamma>' \<turnstile> (App s s') is (App t t') : T2)))"
apply (auto simp add: ty.inject)
apply (subgoal_tac "(\<exists>T1 T2. b=T1 \<rightarrow> T2) \<or> b=TUnit \<or> b=TBase" )
apply (force)
apply (rule ty_cases)
done

termination
apply(relation "measure (\<lambda>(_,_,_,T). size T)")
apply(auto)
done

lemma log_equiv_valid: 
  assumes "\<Gamma> \<turnstile> s is t : T"
  shows "valid \<Gamma>"
using assms 
by (induct rule: log_equiv.induct,auto elim: alg_equiv_valid)

lemma logical_monotonicity :
 fixes T::ty
 assumes "\<Gamma> \<turnstile> s is t : T" "\<Gamma>\<lless>\<Gamma>'" 
 shows "\<Gamma>' \<turnstile> s is t : T"
using assms
proof (induct arbitrary: \<Gamma>' rule: log_equiv.induct)
  case (2 \<Gamma> s t \<Gamma>')
  then show "\<Gamma>' \<turnstile> s is t : TBase" using algorithmic_monotonicity by auto
next
  case (3 \<Gamma> s t T1 T2 \<Gamma>')
  have h1:"\<Gamma> \<turnstile> s is t : T1\<rightarrow>T2" by fact
  have h2:"\<Gamma>\<lless>\<Gamma>'" by fact
  {
    fix \<Gamma>'' s' t'
    assume "\<Gamma>'\<lless>\<Gamma>''" "\<Gamma>'' \<turnstile> s' is t' : T1"
    then have "\<Gamma>'' \<turnstile> (App s s') is (App t t') : T2" using h1 h2 by auto
  }
  then show "\<Gamma>' \<turnstile> s is t : T1\<rightarrow>T2" using h2 by auto
qed (auto)
  
lemma forget: 
  fixes x::"name"
  and   L::"trm"
  assumes a: "x\<sharp>L" 
  shows "L[x::=P] = L"
  using a
by (nominal_induct L avoiding: x P rule: trm.induct)
   (auto simp add: fresh_atm abs_fresh)

lemma subst_fun_eq:
  fixes u::trm
  assumes h:"[x].t1 = [y].t2"
  shows "t1[x::=u] = t2[y::=u]"
proof -
  { 
    assume "x=y" and "t1=t2"
    then have ?thesis using h by simp
  }
  moreover 
  {
    assume h1:"x \<noteq> y" and h2:"t1=[(x,y)] \<bullet> t2" and h3:"x \<sharp> t2"
    then have "([(x,y)] \<bullet> t2)[x::=u] = t2[y::=u]" by (simp add: subst_rename)
    then have ?thesis using h2 by simp 
  }
  ultimately show ?thesis using alpha h by blast
qed

lemma psubst_empty[simp]:
  shows "[]<t> = t"
  by (nominal_induct t rule: trm.induct) (auto simp add: fresh_list_nil)

lemma psubst_subst_psubst:
  assumes h:"c \<sharp> \<theta>"
  shows "\<theta><t>[c::=s] = (c,s)#\<theta><t>"
  using h
by (nominal_induct t avoiding: \<theta> c s rule: trm.induct)
   (auto simp add: fresh_list_cons fresh_atm forget lookup_fresh lookup_fresh' fresh_psubst)

lemma subst_fresh_simpl:
  assumes a: "x\<sharp>\<theta>"
  shows "\<theta><Var x> = Var x"
using a
by (induct \<theta> arbitrary: x, auto simp add:fresh_list_cons fresh_prod fresh_atm)

lemma psubst_subst_propagate: 
  assumes "x\<sharp>\<theta>" 
  shows "\<theta><t[x::=u]> = \<theta><t>[x::=\<theta><u>]"
using assms
proof (nominal_induct t avoiding: x u \<theta> rule: trm.induct)
  case (Var n x u \<theta>)
  { assume "x=n"
    moreover have "x\<sharp>\<theta>" by fact 
    ultimately have "\<theta><Var n[x::=u]> = \<theta><Var n>[x::=\<theta><u>]" using subst_fresh_simpl by auto
  }
  moreover 
  { assume h:"x\<noteq>n"
    then have "x\<sharp>Var n" by (auto simp add: fresh_atm) 
    moreover have "x\<sharp>\<theta>" by fact
    ultimately have "x\<sharp>\<theta><Var n>" using fresh_psubst by blast
    then have " \<theta><Var n>[x::=\<theta><u>] =  \<theta><Var n>" using forget by auto
    then have "\<theta><Var n[x::=u]> = \<theta><Var n>[x::=\<theta><u>]" using h by auto
  }
  ultimately show ?case by auto  
next
  case (Lam n t x u \<theta>)
  have fs:"n\<sharp>x" "n\<sharp>u" "n\<sharp>\<theta>" "x\<sharp>\<theta>" by fact
  have ih:"\<And> y s \<theta>. y\<sharp>\<theta> \<Longrightarrow> ((\<theta><(t[y::=s])>) = ((\<theta><t>)[y::=(\<theta><s>)]))" by fact
  have "\<theta> <(Lam [n].t)[x::=u]> = \<theta><Lam [n]. (t [x::=u])>" using fs by auto
  then have "\<theta> <(Lam [n].t)[x::=u]> = Lam [n]. \<theta><t [x::=u]>" using fs by auto
  moreover have "\<theta><t[x::=u]> = \<theta><t>[x::=\<theta><u>]" using ih fs by blast
  ultimately have "\<theta> <(Lam [n].t)[x::=u]> = Lam [n].(\<theta><t>[x::=\<theta><u>])" by auto
  moreover have "Lam [n].(\<theta><t>[x::=\<theta><u>]) = (Lam [n].\<theta><t>)[x::=\<theta><u>]" using fs fresh_psubst by auto
  ultimately have "\<theta><(Lam [n].t)[x::=u]> = (Lam [n].\<theta><t>)[x::=\<theta><u>]" using fs by auto
  then show "\<theta><(Lam [n].t)[x::=u]> = \<theta><Lam [n].t>[x::=\<theta><u>]" using fs by auto
qed (auto)
 
lemma fresh_subst_fresh:
    assumes "a\<sharp>e"
    shows "a\<sharp>t[a::=e]"
using assms 
by (nominal_induct t avoiding: a e rule: trm.induct)
   (auto simp add: fresh_atm abs_fresh fresh_nat) 

lemma path_equiv_implies_nf:
  assumes "\<Gamma> \<turnstile> s \<leftrightarrow> t : T"
  shows "s \<leadsto>|" and "t \<leadsto>|"
using assms
by (induct rule: alg_equiv_alg_path_equiv.inducts(2)) (simp, auto)

lemma path_equiv_implies_nf:
  shows "\<Gamma> \<turnstile> s <=> t : T \<Longrightarrow> True"
    and "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> s \<leadsto>|"
        "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> t \<leadsto>|"
by (induct rule: alg_equiv_alg_path_equiv.inducts) (auto)

lemma main_lemma:
  shows "\<Gamma> \<turnstile> s is t : T \<Longrightarrow> \<Gamma> \<turnstile> s <=> t : T" and "\<Gamma> \<turnstile> p \<leftrightarrow> q : T \<Longrightarrow> \<Gamma> \<turnstile> p is q : T"
proof (nominal_induct T arbitrary: \<Gamma> s t p q rule:ty.induct)
  case (Arrow T1 T2)
  { 
    case (1 \<Gamma> s t)
    have ih1:"\<And>\<Gamma> s t. \<Gamma> \<turnstile> s is t : T2 \<Longrightarrow> \<Gamma> \<turnstile> s <=> t : T2" by fact
    have ih2:"\<And>\<Gamma> s t. \<Gamma> \<turnstile> s \<leftrightarrow> t : T1 \<Longrightarrow> \<Gamma> \<turnstile> s is t : T1" by fact
    have h:"\<Gamma> \<turnstile> s is t : T1\<rightarrow>T2" by fact
    obtain x::name where fs:"x\<sharp>(\<Gamma>,s,t)" by (erule exists_fresh[OF fs_name1])
    have "valid \<Gamma>" using h log_equiv_valid by auto
    then have v:"valid ((x,T1)#\<Gamma>)" using fs by auto
    then have "(x,T1)#\<Gamma> \<turnstile> Var x \<leftrightarrow> Var x : T1" by auto
    then have "(x,T1)#\<Gamma> \<turnstile> Var x is Var x : T1" using ih2 by auto
    then have "(x,T1)#\<Gamma> \<turnstile> App s (Var x) is App t (Var x) : T2" using h v by auto
    then have "(x,T1)#\<Gamma> \<turnstile> App s (Var x) <=> App t (Var x) : T2" using ih1 by auto
    then show "\<Gamma> \<turnstile> s <=> t : T1\<rightarrow>T2" using fs by (auto simp add: fresh_prod)
  next
    case (2 \<Gamma> p q)
    have h:"\<Gamma> \<turnstile> p \<leftrightarrow> q : T1\<rightarrow>T2" by fact
    have ih1:"\<And>\<Gamma> s t. \<Gamma> \<turnstile> s \<leftrightarrow> t : T2 \<Longrightarrow> \<Gamma> \<turnstile> s is t : T2" by fact
    have ih2:"\<And>\<Gamma> s t. \<Gamma> \<turnstile> s is t : T1 \<Longrightarrow> \<Gamma> \<turnstile> s <=> t : T1" by fact
    {
      fix \<Gamma>' s t
      assume "\<Gamma>\<lless>\<Gamma>'" and hl:"\<Gamma>' \<turnstile> s is t : T1"
      then have "\<Gamma>' \<turnstile> p \<leftrightarrow> q : T1 \<rightarrow> T2" using h algorithmic_monotonicity by auto
      moreover have "\<Gamma>' \<turnstile> s <=> t : T1" using ih2 hl by auto
      ultimately have "\<Gamma>' \<turnstile> App p s \<leftrightarrow> App q t : T2" by auto
      then have "\<Gamma>' \<turnstile> App p s is App q t : T2" using ih1 by auto
    }
    moreover have "valid \<Gamma>" using h alg_equiv_valid by auto
    ultimately show "\<Gamma> \<turnstile> p is q : T1\<rightarrow>T2"  by auto
  }
next
  case TBase
  { case 2
    have h:"\<Gamma> \<turnstile> s \<leftrightarrow> t : TBase" by fact
    then have "s \<leadsto>|" and "t \<leadsto>|" using path_equiv_implies_nf by auto
    then have "s \<Down> s" and "t \<Down> t" by auto
    then have "\<Gamma> \<turnstile> s <=> t : TBase" using h by auto
    then show "\<Gamma> \<turnstile> s is t : TBase" by auto
  }
qed (auto elim:alg_equiv_valid)

corollary corollary_main:
  assumes a: "\<Gamma> \<turnstile> s \<leftrightarrow> t : T"
  shows "\<Gamma> \<turnstile> s <=> t : T"
using a main_lemma by blast

lemma algorithmic_symmetry_aux:
  shows "\<Gamma> \<turnstile> s <=> t : T \<Longrightarrow> \<Gamma> \<turnstile> t <=> s : T" 
  and   "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<turnstile> t \<leftrightarrow> s : T"
by (induct rule: alg_equiv_alg_path_equiv.inducts) (auto)

lemma algorithmic_symmetry:
  assumes a: "\<Gamma> \<turnstile> s <=> t : T"
  shows "\<Gamma> \<turnstile> t <=> s : T"
using a by (simp add: algorithmic_symmetry_aux)

lemma algorithmic_path_symmetry:
  assumes a: "\<Gamma> \<turnstile> s \<leftrightarrow> t : T"
  shows "\<Gamma> \<turnstile> t \<leftrightarrow> s : T"
using a by (simp add: algorithmic_symmetry_aux)

lemma red_unicity : 
  assumes a: "x \<leadsto> a" 
  and     b: "x \<leadsto> b"
  shows "a=b"
  using a b
apply (induct arbitrary: b)
apply (erule whr_App_Lam)
apply (clarify)
apply (rule subst_fun_eq)
apply (simp)
apply (force)
apply (erule whr_App)
apply (blast)+
done

lemma nf_unicity :
  assumes "x \<Down> a" "x \<Down> b"
  shows "a=b"
  using assms 
proof (induct arbitrary: b)
  case (QAN_Reduce x t a b)
  have h:"x \<leadsto> t" "t \<Down> a" by fact
  have ih:"\<And>b. t \<Down> b \<Longrightarrow> a = b" by fact
  have "x \<Down> b" by fact
  then obtain t' where "x \<leadsto> t'" and hl:"t' \<Down> b" using h by auto
  then have "t=t'" using h red_unicity by auto
  then show "a=b" using ih hl by auto
qed (auto)

lemma Q_eqvt :
  fixes pi:: "name prm"
  shows "\<Gamma> \<turnstile> s <=> t : T \<Longrightarrow> (pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>s) <=> (pi\<bullet>t) : T"
  and "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> (pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>s) \<leftrightarrow> (pi\<bullet>t) : T"
using assms
proof (induct rule:alg_equiv_alg_path_equiv.inducts)
  case (QAP_Var \<Gamma> x T)
  then have "pi\<bullet>(x,T) \<in> (pi\<bullet>(set \<Gamma>))" using in_eqvt by blast
  then have "(pi\<bullet>x,T) \<in> (set (pi\<bullet>\<Gamma>))" using set_eqvt perm_ty by auto
  moreover have "valid \<Gamma>" by fact
  ultimately show ?case using valid_eqvt by auto
next
  case (QAT_Arrow x \<Gamma> s t T1 T2)
  then have h:"((pi\<bullet>x)\<sharp>(pi\<bullet>\<Gamma>))" "((pi\<bullet>x)\<sharp>(pi\<bullet>s))" "((pi\<bullet>x)\<sharp>(pi\<bullet>t))"  using fresh_bij by auto
  have "(pi\<bullet>((x,T1)#\<Gamma>)) \<turnstile> pi \<bullet> (App s (Var x)) <=> pi \<bullet> (App t (Var x)) : T2" by fact
  then have "(pi\<bullet>((x,T1)#\<Gamma>)) \<turnstile> (App (pi\<bullet>s) (Var (pi\<bullet>x))) <=> (App (pi\<bullet>t) (Var (pi\<bullet>x))) : T2" by auto
  moreover have "pi\<bullet>((x,T1)#\<Gamma>) = (pi\<bullet>x,pi\<bullet>T1)#(pi\<bullet>\<Gamma>)" by auto
  ultimately have "((pi\<bullet>x,T1)#(pi\<bullet>\<Gamma>))  \<turnstile> (App (pi\<bullet>s) (Var (pi\<bullet>x))) <=> (App (pi\<bullet>t) (Var (pi\<bullet>x))) : T2" 
    using perm_ty by auto
  then show ?case using h by auto
qed (auto elim:whn_eqvt valid_eqvt)
 
(* FIXME this lemma should not be here I am reinventing the wheel I guess *)

lemma perm_basic[simp]:
 fixes x y::"name"
shows "[(x,y)]\<bullet>y = x"
using assms using calc_atm by perm_simp

lemma Q_Arrow_strong_inversion:
  assumes fs:"x\<sharp>\<Gamma>" "x\<sharp>t" "x\<sharp>u" and h:"\<Gamma> \<turnstile> t <=> u : T1\<rightarrow>T2"
  shows "(x,T1)#\<Gamma> \<turnstile> App t (Var x) <=> App u (Var x) : T2"
proof -
  obtain y where  fs2:"y\<sharp>\<Gamma>" "y\<sharp>u" "y\<sharp>t" and "(y,T1)#\<Gamma> \<turnstile> App t (Var y) <=> App u (Var y) : T2" 
    using h by auto
  then have "([(x,y)]\<bullet>((y,T1)#\<Gamma>)) \<turnstile> [(x,y)]\<bullet> App t (Var y) <=> [(x,y)]\<bullet> App u (Var y) : T2" 
    using Q_eqvt by blast
  then show ?thesis using fs fs2 by (perm_simp)
qed

lemma fresh_context: 
  fixes  \<Gamma> :: "(name\<times>ty) list"
  and    a :: "name"
  assumes "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using assms by(induct \<Gamma>, auto simp add: fresh_prod fresh_list_cons fresh_atm)

lemma type_unicity_in_context:
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    pi:: "name prm"
  and    a :: "name"
  and    \<tau> :: "ty"
  assumes "valid \<Gamma>" and "(x,T1) \<in> set \<Gamma>" and "(x,T2) \<in> set \<Gamma>"
  shows "T1=T2"
using assms by (induct \<Gamma>, auto dest!: fresh_context)

(* 

Warning: This lemma is false.

lemma algorithmic_type_unicity:
  shows "\<lbrakk> \<Gamma> \<turnstile> s <=> t : T ; \<Gamma> \<turnstile> s <=> u : T' \<rbrakk> \<Longrightarrow> T = T'"
  and "\<lbrakk> \<Gamma> \<turnstile> s \<leftrightarrow> t : T ; \<Gamma> \<turnstile> s \<leftrightarrow> u : T' \<rbrakk> \<Longrightarrow> T = T'"

Here is the counter example : 
\<Gamma> \<turnstile> Const n <=> Const n : Tbase and \<Gamma> \<turnstile> Const n <=> Const n : TUnit

*)

lemma algorithmic_path_type_unicity:
  shows "\<lbrakk> \<Gamma> \<turnstile> s \<leftrightarrow> t : T ; \<Gamma> \<turnstile> s \<leftrightarrow> u : T' \<rbrakk> \<Longrightarrow> T = T'"
proof (induct arbitrary:  u T' 
       rule: alg_equiv_alg_path_equiv.inducts(2) [of _ _ _ _ _  "%a b c d . True"    ])
  case (QAP_Var \<Gamma> x T u T')
  have "\<Gamma> \<turnstile> Var x \<leftrightarrow> u : T'" by fact
  then have "u=Var x" and "(x,T') \<in> set \<Gamma>" by auto
  moreover have "valid \<Gamma>" "(x,T) \<in> set \<Gamma>" by fact
  ultimately show "T=T'" using type_unicity_in_context by auto
next
  case (QAP_App \<Gamma> p q T1 T2 s t u T2')
  have ih:"\<And>u T. \<Gamma> \<turnstile> p \<leftrightarrow> u : T \<Longrightarrow> T1\<rightarrow>T2 = T" by fact
  have "\<Gamma> \<turnstile> App p s \<leftrightarrow> u : T2'" by fact
  then obtain r t T1' where "u = App r t"  "\<Gamma> \<turnstile> p \<leftrightarrow> r : T1' \<rightarrow> T2'" by auto
  then have "T1\<rightarrow>T2 = T1' \<rightarrow> T2'" by auto
  then show "T2=T2'" using ty.inject by auto
qed (auto)

lemma algorithmic_transitivity:
  shows "\<lbrakk> \<Gamma> \<turnstile> s <=> t : T ; \<Gamma> \<turnstile> t <=> u : T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s <=> u : T"
  and  "\<lbrakk> \<Gamma> \<turnstile> s \<leftrightarrow> t : T ; \<Gamma> \<turnstile> t \<leftrightarrow> u : T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<leftrightarrow> u : T"
proof (nominal_induct \<Gamma> s t T and \<Gamma> s t T avoiding: u rule: alg_equiv_alg_path_equiv_strong_inducts)
  case (QAT_Base s p t q \<Gamma> u)
  have h:"s \<Down> p" "t \<Down> q" by fact
  have ih:"\<And>u. \<Gamma> \<turnstile> q \<leftrightarrow> u : TBase \<Longrightarrow> \<Gamma> \<turnstile> p \<leftrightarrow> u : TBase" by fact
  have "\<Gamma> \<turnstile> t <=> u : TBase" by fact
  then obtain r q' where hl:"t \<Down> q'" "u \<Down> r" "\<Gamma> \<turnstile> q' \<leftrightarrow> r : TBase" by auto
  moreover have eq:"q=q'" using nf_unicity hl h by auto
  ultimately have "\<Gamma> \<turnstile> p \<leftrightarrow> r : TBase" using ih by auto
  then show "\<Gamma> \<turnstile> s <=> u : TBase" using hl h by auto
next
  case (QAT_Arrow  x \<Gamma> s t T1 T2 u)
  have fs:"x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" by fact
  moreover have h:"\<Gamma> \<turnstile> t <=> u : T1\<rightarrow>T2" by fact
  moreover then obtain y where "y\<sharp>\<Gamma>" "y\<sharp>t" "y\<sharp>u" and "(y,T1)#\<Gamma> \<turnstile> App t (Var y) <=> App u (Var y) : T2" 
    by auto
  moreover have fs2:"x\<sharp>u" by fact
  ultimately have "(x,T1)#\<Gamma> \<turnstile> App t (Var x) <=> App u (Var x) : T2" using Q_Arrow_strong_inversion by blast
  moreover have ih:"\<And> v. (x,T1)#\<Gamma> \<turnstile> App t (Var x) <=> v : T2 \<Longrightarrow> (x,T1)#\<Gamma> \<turnstile> App s (Var x) <=> v : T2" 
    by fact
  ultimately have "(x,T1)#\<Gamma> \<turnstile> App s (Var x) <=> App u (Var x) : T2" by auto
  then show "\<Gamma> \<turnstile> s <=> u : T1\<rightarrow>T2" using fs fs2 by auto
next
  case (QAP_App \<Gamma> p q T1 T2 s t u)
  have h1:"\<Gamma> \<turnstile> p \<leftrightarrow> q : T1\<rightarrow>T2" by fact
  have ih1:"\<And>u. \<Gamma> \<turnstile> q \<leftrightarrow> u : T1\<rightarrow>T2 \<Longrightarrow> \<Gamma> \<turnstile> p \<leftrightarrow> u : T1\<rightarrow>T2" by fact
  have "\<Gamma> \<turnstile> s <=> t : T1" by fact
  have ih2:"\<And>u. \<Gamma> \<turnstile> t <=> u : T1 \<Longrightarrow> \<Gamma> \<turnstile> s <=> u : T1" by fact
  have "\<Gamma> \<turnstile> App q t \<leftrightarrow> u : T2" by fact
  then obtain r T1' v where ha:"\<Gamma> \<turnstile> q \<leftrightarrow> r : T1'\<rightarrow>T2" and hb:"\<Gamma> \<turnstile> t <=> v : T1'" and eq:"u = App r v" 
    by auto
  moreover have "\<Gamma> \<turnstile> q \<leftrightarrow> p : T1\<rightarrow>T2" using h1 algorithmic_path_symmetry by auto
  ultimately have "T1'\<rightarrow>T2 = T1\<rightarrow>T2" using algorithmic_path_type_unicity by auto
  then have "T1' = T1" using ty.inject by auto
  then have "\<Gamma> \<turnstile> s <=> v : T1" "\<Gamma> \<turnstile> p \<leftrightarrow> r : T1\<rightarrow>T2" using ih1 ih2 ha hb by auto
  then show "\<Gamma> \<turnstile> App p s \<leftrightarrow> u : T2" using eq by auto
qed (auto)

lemma algorithmic_weak_head_closure:
  shows "\<lbrakk>\<Gamma> \<turnstile> s <=> t : T ; s' \<leadsto> s; t' \<leadsto> t\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s' <=> t' : T"
by (nominal_induct \<Gamma> s t T avoiding: s' t'  
    rule: alg_equiv_alg_path_equiv_strong_inducts(1) [of _ _ _ _ "%a b c d e. True"])
   (auto)

lemma logical_symmetry:
  assumes a: "\<Gamma> \<turnstile> s is t : T"
  shows "\<Gamma> \<turnstile> t is s : T"
using a 
by (nominal_induct arbitrary: \<Gamma> s t rule:ty.induct) (auto simp add: algorithmic_symmetry)

lemma logical_transitivity:
  assumes "\<Gamma> \<turnstile> s is t : T" "\<Gamma> \<turnstile> t is u : T" 
  shows "\<Gamma> \<turnstile> s is u : T"
using assms
proof (nominal_induct arbitrary: \<Gamma> s t u  rule:ty.induct)
  case TBase
  then show "\<Gamma> \<turnstile> s is u : TBase" by (auto elim:  algorithmic_transitivity)
next 
  case (Arrow T1 T2 \<Gamma> s t u)
  have h1:"\<Gamma> \<turnstile> s is t : T1 \<rightarrow> T2" by fact
  have h2:"\<Gamma> \<turnstile> t is u : T1 \<rightarrow> T2" by fact
  have ih1:"\<And>\<Gamma> s t u. \<lbrakk>\<Gamma> \<turnstile> s is t : T1; \<Gamma> \<turnstile> t is u : T1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s is u : T1" by fact
  have ih2:"\<And>\<Gamma> s t u. \<lbrakk>\<Gamma> \<turnstile> s is t : T2; \<Gamma> \<turnstile> t is u : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s is u : T2" by fact
  {
    fix \<Gamma>' s' u'
    assume hsub:"\<Gamma>\<lless>\<Gamma>'" and hl:"\<Gamma>' \<turnstile> s' is u' : T1"
    then have "\<Gamma>' \<turnstile> u' is s' : T1" using logical_symmetry by blast
    then have "\<Gamma>' \<turnstile> u' is u' : T1" using ih1 hl by blast
    then have "\<Gamma>' \<turnstile> App t u' is App u u' : T2" using h2 hsub by auto
    moreover have "\<Gamma>' \<turnstile>  App s s' is App t u' : T2" using h1 hsub hl by auto
    ultimately have "\<Gamma>' \<turnstile>  App s s' is App u u' : T2" using ih2 by blast
  }
  moreover have "valid \<Gamma>" using h1 alg_equiv_valid by auto
  ultimately show "\<Gamma> \<turnstile> s is u : T1 \<rightarrow> T2" by auto
qed (auto)

lemma logical_weak_head_closure:
  assumes a: "\<Gamma> \<turnstile> s is t : T" "s' \<leadsto> s" "t' \<leadsto> t"
  shows "\<Gamma> \<turnstile> s' is t' : T"
using a
apply(nominal_induct arbitrary: \<Gamma> s t s' t' rule:ty.induct)
apply(auto simp add: algorithmic_weak_head_closure)
apply(blast)
done

lemma logical_weak_head_closure':
  assumes "\<Gamma> \<turnstile> s is t : T" "s' \<leadsto> s" 
  shows "\<Gamma> \<turnstile> s' is t : T"
using assms
proof (nominal_induct arbitrary: \<Gamma> s t s' rule: ty.induct)
  case (TBase  \<Gamma> s t s')
  then show ?case by force
next
  case (TUnit \<Gamma> s t s')
  then show ?case by auto
next
  case (Arrow T1 T2 \<Gamma> s t s')
  have h1:"s' \<leadsto> s" by fact
  have ih:"\<And>\<Gamma> s t s'. \<lbrakk>\<Gamma> \<turnstile> s is t : T2; s' \<leadsto> s\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s' is t : T2" by fact
  have h2:"\<Gamma> \<turnstile> s is t : T1\<rightarrow>T2" by fact
  then have hb:"\<forall>\<Gamma>' s' t'. \<Gamma>\<lless>\<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> s' is t' : T1 \<longrightarrow>  (\<Gamma>' \<turnstile> (App s s') is (App t t') : T2)" by auto
  {
    fix \<Gamma>' s2 t2
    assume "\<Gamma>\<lless>\<Gamma>'" and "\<Gamma>' \<turnstile> s2 is t2 : T1"
    then have "\<Gamma>' \<turnstile> (App s s2) is (App t t2) : T2" using hb by auto
    moreover have "(App s' s2)  \<leadsto> (App s s2)" using h1 by auto  
    ultimately have "\<Gamma>' \<turnstile> App s' s2 is App t t2 : T2" using ih by auto
  }
  moreover have "valid \<Gamma>" using h2 log_equiv_valid by auto
  ultimately show "\<Gamma> \<turnstile> s' is t : T1\<rightarrow>T2" by auto
qed

abbreviation 
 log_equiv_subst :: "(name\<times>ty) list \<Rightarrow> (name\<times>trm) list \<Rightarrow>  (name\<times>trm) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool"  
                     ("_ \<turnstile> _ is _ over _" [60,60] 60) 
where
  "\<Gamma>' \<turnstile> \<gamma> is \<delta> over \<Gamma> \<equiv> valid \<Gamma>' \<and> (\<forall>  x T. (x,T) \<in> set \<Gamma> \<longrightarrow> \<Gamma>' \<turnstile> \<gamma><Var x> is  \<delta><Var x> : T)"

lemma logical_pseudo_reflexivity:
  assumes "\<Gamma>' \<turnstile> t is s over \<Gamma>"
  shows "\<Gamma>' \<turnstile> s is s over \<Gamma>" 
proof -
  have "\<Gamma>' \<turnstile> t is s over \<Gamma>" by fact
  moreover then have "\<Gamma>' \<turnstile> s is t over \<Gamma>" using logical_symmetry by blast
  ultimately show "\<Gamma>' \<turnstile> s is s over \<Gamma>" using logical_transitivity by blast
qed

lemma logical_subst_monotonicity :
  fixes \<Gamma>::"(name\<times>ty) list"
  and   \<Gamma>'::"(name\<times>ty) list"
  and   \<Gamma>''::"(name\<times>ty) list"
  assumes "\<Gamma>' \<turnstile> s is t over \<Gamma>" "\<Gamma>'\<lless>\<Gamma>''"
  shows "\<Gamma>'' \<turnstile> s is t over \<Gamma>"
  using assms logical_monotonicity by blast

lemma equiv_subst_ext :
  assumes h1:"\<Gamma>' \<turnstile> \<gamma> is \<delta> over \<Gamma>" and h2:"\<Gamma>' \<turnstile> s is t : T" and fs:"x\<sharp>\<Gamma>"
  shows "\<Gamma>' \<turnstile> (x,s)#\<gamma> is (x,t)#\<delta> over (x,T)#\<Gamma>"
using assms
proof -
{
  fix y U
  assume "(y,U) \<in> set ((x,T)#\<Gamma>)"
  moreover
  { 
    assume "(y,U) \<in> set [(x,T)]"
    then have "\<Gamma>' \<turnstile> (x,s)#\<gamma><Var y> is (x,t)#\<delta><Var y> : U" by auto 
  }
  moreover
  {
    assume hl:"(y,U) \<in> set \<Gamma>"
    then have "\<not> y\<sharp>\<Gamma>" by (induct \<Gamma>) (auto simp add: fresh_list_cons fresh_atm fresh_prod)
    then have hf:"x\<sharp> Var y" using fs by (auto simp add: fresh_atm)
    then have "(x,s)#\<gamma><Var y> = \<gamma><Var y>" "(x,t)#\<delta><Var y> = \<delta><Var y>" using fresh_psubst_simpl by blast+ 
    moreover have  "\<Gamma>' \<turnstile> \<gamma><Var y> is \<delta><Var y> : U" using h1 hl by auto
    ultimately have "\<Gamma>' \<turnstile> (x,s)#\<gamma><Var y> is (x,t)#\<delta><Var y> : U" by auto
  }
  ultimately have "\<Gamma>' \<turnstile> (x,s)#\<gamma><Var y> is (x,t)#\<delta><Var y> : U" by auto
}
moreover have "valid \<Gamma>'" using h2 log_equiv_valid by blast
ultimately show "\<Gamma>' \<turnstile> (x,s)#\<gamma> is (x,t)#\<delta> over (x,T)#\<Gamma>" by auto
qed

theorem fundamental_theorem:
  assumes "\<Gamma> \<turnstile> t : T" "\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>"
  shows "\<Gamma>' \<turnstile> \<gamma><t> is \<theta><t> : T"   
using assms
proof (nominal_induct avoiding:\<Gamma>' \<gamma> \<theta>  rule: typing_induct_strong)
case (t_Lam x \<Gamma> T1 t2 T2 \<Gamma>' \<gamma> \<theta>)
have fs:"x\<sharp>\<gamma>" "x\<sharp>\<theta>" "x\<sharp>\<Gamma>" by fact
have h:"\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
have ih:"\<And> \<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over (x,T1)#\<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><t2> is \<theta><t2> : T2" by fact
{
  fix \<Gamma>'' s' t'
  assume "\<Gamma>'\<lless>\<Gamma>''" and hl:"\<Gamma>''\<turnstile> s' is t' : T1"
  then have "\<Gamma>'' \<turnstile> \<gamma> is \<theta> over \<Gamma>" using logical_subst_monotonicity h by blast
  then have "\<Gamma>'' \<turnstile> (x,s')#\<gamma> is (x,t')#\<theta> over (x,T1)#\<Gamma>" using equiv_subst_ext hl fs by blast
  then have "\<Gamma>'' \<turnstile> (x,s')#\<gamma><t2> is (x,t')#\<theta><t2> : T2" using ih by auto
  then have "\<Gamma>''\<turnstile>\<gamma><t2>[x::=s'] is \<theta><t2>[x::=t'] : T2" using psubst_subst_psubst fs by simp
  moreover have "App (Lam [x].\<gamma><t2>) s' \<leadsto> \<gamma><t2>[x::=s']" by auto
  moreover have "App (Lam [x].\<theta><t2>) t' \<leadsto> \<theta><t2>[x::=t']" by auto
  ultimately have "\<Gamma>''\<turnstile> App (Lam [x].\<gamma><t2>) s' is App (Lam [x].\<theta><t2>) t' : T2" 
    using logical_weak_head_closure by auto
}
moreover have "valid \<Gamma>'" using h by auto
ultimately show "\<Gamma>' \<turnstile> \<gamma><Lam [x].t2> is \<theta><Lam [x].t2> : T1\<rightarrow>T2" using fs by auto 
qed (auto)

theorem fundamental_theorem_2:
  assumes h1: "\<Gamma> \<turnstile> s == t : T" 
  and     h2: "\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>"
  shows "\<Gamma>' \<turnstile> \<gamma><s> is \<theta><t> : T"
using h1 h2
proof (nominal_induct \<Gamma> s t T avoiding: \<Gamma>' \<gamma> \<theta> rule: equiv_def_strong_induct)
  case (Q_Refl \<Gamma> t T \<Gamma>' \<gamma> \<theta>)
  have "\<Gamma> \<turnstile> t : T" by fact
  moreover have "\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
  ultimately show "\<Gamma>' \<turnstile> \<gamma><t> is \<theta><t> : T" using fundamental_theorem by blast
next
  case (Q_Symm \<Gamma> t s T \<Gamma>' \<gamma> \<theta>)
  have "\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
  moreover have ih:"\<And> \<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><t> is \<theta><s> : T" by fact
  ultimately show "\<Gamma>' \<turnstile> \<gamma><s> is \<theta><t> : T" using logical_symmetry by blast
next
  case (Q_Trans \<Gamma> s t T u \<Gamma>' \<gamma> \<theta>)
  have ih1:"\<And> \<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><s> is \<theta><t> : T" by fact
  have ih2:"\<And> \<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><t> is \<theta><u> : T" by fact
  have h:"\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
  then have "\<Gamma>' \<turnstile> \<theta> is \<theta> over \<Gamma>" using logical_pseudo_reflexivity by auto
  then have "\<Gamma>' \<turnstile> \<theta><t> is \<theta><u> : T" using ih2 by auto
  moreover have "\<Gamma>' \<turnstile> \<gamma><s> is \<theta><t> : T" using ih1 h by auto
  ultimately show "\<Gamma>' \<turnstile> \<gamma><s> is \<theta><u> : T" using logical_transitivity by blast
next
  case (Q_Abs x \<Gamma> T1 s2 t2 T2 \<Gamma>' \<gamma> \<theta>)
  have fs:"x\<sharp>\<Gamma>" by fact
  have fs2: "x\<sharp>\<gamma>" "x\<sharp>\<theta>" by fact 
  have h2:"\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
  have ih:"\<And>\<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over (x,T1)#\<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><s2> is \<theta><t2> : T2" by fact
  {
    fix \<Gamma>'' s' t'
    assume "\<Gamma>'\<lless>\<Gamma>''" and hl:"\<Gamma>''\<turnstile> s' is t' : T1"
    then have "\<Gamma>'' \<turnstile> \<gamma> is \<theta> over \<Gamma>" using h2 logical_subst_monotonicity by blast
    then have "\<Gamma>'' \<turnstile> (x,s')#\<gamma> is (x,t')#\<theta> over (x,T1)#\<Gamma>" using equiv_subst_ext hl fs by blast
    then have "\<Gamma>'' \<turnstile> (x,s')#\<gamma><s2> is (x,t')#\<theta><t2> : T2" using ih by blast
    then have "\<Gamma>''\<turnstile> \<gamma><s2>[x::=s'] is \<theta><t2>[x::=t'] : T2" using fs2 psubst_subst_psubst by auto
    moreover have "App (Lam [x]. \<gamma><s2>) s' \<leadsto>  \<gamma><s2>[x::=s']" 
              and "App (Lam [x].\<theta><t2>) t' \<leadsto> \<theta><t2>[x::=t']" by auto
    ultimately have "\<Gamma>'' \<turnstile> App (Lam [x]. \<gamma><s2>) s' is App (Lam [x].\<theta><t2>) t' : T2" 
      using logical_weak_head_closure by auto
  }
  moreover have "valid \<Gamma>'" using h2 by auto
  ultimately have "\<Gamma>' \<turnstile> Lam [x].\<gamma><s2> is Lam [x].\<theta><t2> : T1\<rightarrow>T2" by auto
  then show "\<Gamma>' \<turnstile> \<gamma><Lam [x].s2> is \<theta><Lam [x].t2> : T1\<rightarrow>T2" using fs2 by auto
next
  case (Q_App \<Gamma> s1 t1 T1 T2 s2 t2 \<Gamma>' \<gamma> \<theta>)
  then show "\<Gamma>' \<turnstile> \<gamma><App s1 s2> is \<theta><App t1 t2> : T2" by auto 
next
  case (Q_Beta x \<Gamma> T1 s12 t12 T2 s2 t2 \<Gamma>' \<gamma> \<theta>)
  have h:"\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
  have fs:"x\<sharp>\<Gamma>" by fact
  have fs2:"x\<sharp>\<gamma>" "x\<sharp>\<theta>" by fact 
  have ih1:"\<And>\<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><s2> is \<theta><t2> : T1" by fact
  have ih2:"\<And>\<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over (x,T1)#\<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><s12> is \<theta><t12> : T2" by fact
  have "\<Gamma>' \<turnstile> \<gamma><s2> is \<theta><t2> : T1" using ih1 h by auto
  then have "\<Gamma>' \<turnstile> (x,\<gamma><s2>)#\<gamma> is (x,\<theta><t2>)#\<theta> over (x,T1)#\<Gamma>" using equiv_subst_ext h fs by blast
  then have "\<Gamma>' \<turnstile> (x,\<gamma><s2>)#\<gamma><s12> is (x,\<theta><t2>)#\<theta><t12> : T2" using ih2 by auto
  then have "\<Gamma>' \<turnstile> \<gamma><s12>[x::=\<gamma><s2>] is \<theta><t12>[x::=\<theta><t2>] : T2" using fs2 psubst_subst_psubst by auto
  then have "\<Gamma>' \<turnstile> \<gamma><s12>[x::=\<gamma><s2>] is \<theta><t12[x::=t2]> : T2" using fs2 psubst_subst_propagate by auto
  moreover have "App (Lam [x].\<gamma><s12>) (\<gamma><s2>) \<leadsto> \<gamma><s12>[x::=\<gamma><s2>]" by auto 
  ultimately have "\<Gamma>' \<turnstile> App (Lam [x].\<gamma><s12>) (\<gamma><s2>) is \<theta><t12[x::=t2]> : T2" 
    using logical_weak_head_closure' by auto
  then show "\<Gamma>' \<turnstile> \<gamma><App (Lam [x].s12) s2> is \<theta><t12[x::=t2]> : T2" using fs2 by simp
next
  case (Q_Ext x \<Gamma> s t T1 T2 \<Gamma>' \<gamma> \<theta>)
  have h2:"\<Gamma>' \<turnstile> \<gamma> is \<theta> over \<Gamma>" by fact
  have fs:"x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" by fact
  have ih:"\<And>\<Gamma>' \<gamma> \<theta>. \<Gamma>' \<turnstile> \<gamma> is \<theta> over (x,T1)#\<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> \<gamma><App s (Var x)> is \<theta><App t (Var x)> : T2" 
    by fact
   {
    fix \<Gamma>'' s' t'
    assume hsub:"\<Gamma>'\<lless>\<Gamma>''" and hl:"\<Gamma>''\<turnstile> s' is t' : T1"
    then have "\<Gamma>'' \<turnstile> \<gamma> is \<theta> over \<Gamma>" using h2 logical_subst_monotonicity by blast
    then have "\<Gamma>'' \<turnstile> (x,s')#\<gamma> is (x,t')#\<theta> over (x,T1)#\<Gamma>" using equiv_subst_ext hl fs by blast
    then have "\<Gamma>'' \<turnstile> (x,s')#\<gamma><App s (Var x)>  is (x,t')#\<theta><App t (Var x)> : T2" using ih by blast
    then have "\<Gamma>'' \<turnstile> App (((x,s')#\<gamma>)<s>) (((x,s')#\<gamma>)<(Var x)>) is App ((x,t')#\<theta><t>) ((x,t')#\<theta><(Var x)>) : T2"
      by auto
    then have "\<Gamma>'' \<turnstile> App ((x,s')#\<gamma><s>) s'  is App ((x,t')#\<theta><t>) t' : T2" by auto
    then have "\<Gamma>'' \<turnstile> App (\<gamma><s>) s' is App (\<theta><t>) t' : T2" using fs fresh_psubst_simpl by auto
  }
  moreover have "valid \<Gamma>'" using h2 by auto
  ultimately show "\<Gamma>' \<turnstile> \<gamma><s> is \<theta><t> : T1\<rightarrow>T2" by auto
qed

theorem completeness:
  assumes "\<Gamma> \<turnstile> s == t : T"
  shows "\<Gamma> \<turnstile> s <=> t : T"
using assms
proof -
  {
    fix x T
    assume "(x,T) \<in> set \<Gamma>" "valid \<Gamma>"
    then have "\<Gamma> \<turnstile> Var x is Var x : T" using main_lemma by blast
  }
  moreover have "valid \<Gamma>" using equiv_def_valid assms by auto
  ultimately have "\<Gamma> \<turnstile> [] is [] over \<Gamma>" by auto 
  then have "\<Gamma> \<turnstile> []<s> is []<t> : T" using fundamental_theorem_2 assms by blast
  then have "\<Gamma> \<turnstile> s is t : T" by simp
  then show  "\<Gamma> \<turnstile> s <=> t : T" using main_lemma by simp
qed

(* Soundness is left as an exercise - like in the book - for the avid formalist 

theorem soundness:
  shows "\<lbrakk>\<Gamma> \<turnstile> s <=> t : T; \<Gamma> \<turnstile> t : T; \<Gamma> \<turnstile> s : T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s == t : T"
  and   "\<lbrakk>\<Gamma> \<turnstile> s \<leftrightarrow> t : T; \<Gamma> \<turnstile> t : T; \<Gamma> \<turnstile> s : T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s == t : T"

*)

end

