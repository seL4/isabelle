(* $Id: *)

(* A challenge suggested by Adam Chlipala *)

theory Compile
imports "Nominal"
begin

atom_decl name 

nominal_datatype data = DNat
                      | DProd "data" "data"
                      | DSum "data" "data"

nominal_datatype ty = Data "data"
                    | Arrow "ty" "ty" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype trm = Var "name"
                     | Lam "\<guillemotleft>name\<guillemotright>trm" ("Lam [_]._" [100,100] 100)
                     | App "trm" "trm"
                     | Const "nat"
                     | Pr "trm" "trm"
                     | Fst "trm"
                     | Snd "trm"
                     | InL "trm"
                     | InR "trm"
                     | Case "trm" "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" 
                             ("Case _ of inl _ \<rightarrow> _ | inr _ \<rightarrow> _" [100,100,100,100,100] 100)

nominal_datatype dataI = OneI | NatI

nominal_datatype tyI = DataI "dataI"
                     | ArrowI "tyI" "tyI" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype trmI = IVar "name"
                      | ILam "\<guillemotleft>name\<guillemotright>trmI" ("ILam [_]._" [100,100] 100)
                      | IApp "trmI" "trmI"
                      | IUnit
                      | INat "nat"
                      | ISucc "trmI"
                      | IAss "trmI" "trmI" ("_\<mapsto>_" [100,100] 100)
                      | IRef "trmI" 
                      | ISeq "trmI" "trmI" ("_;;_" [100,100] 100)
                      | Iif "trmI" "trmI" "trmI"

text {* valid contexts *}

consts
  ctxts :: "((name\<times>'a::pt_name) list) set" 
  valid :: "(name\<times>'a::pt_name) list \<Rightarrow> bool"
translations
  "valid \<Gamma>" \<rightleftharpoons> "\<Gamma> \<in> ctxts"  

inductive ctxts
intros
v1[intro]: "valid []"
v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

text {* typing judgements for trms *}

consts
  typing :: "(((name\<times>ty) list)\<times>trm\<times>ty) set" 
syntax
  "_typing_judge" :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" (" _ \<turnstile> _ : _ " [80,80,80] 80) 
translations
  "\<Gamma> \<turnstile> t : \<tau>" \<rightleftharpoons> "(\<Gamma>,t,\<tau>) \<in> typing"  

inductive typing
intros
t0[intro]: "\<lbrakk>valid \<Gamma>; (x,\<tau>)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
t1[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : \<tau>1\<rightarrow>\<tau>2; \<Gamma> \<turnstile> e2 : \<tau>1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"
t2[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,\<tau>1)#\<Gamma>) \<turnstile> t : \<tau>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : \<tau>1\<rightarrow>\<tau>2"
t3[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n : Data(DNat)"
t4[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : Data(\<sigma>1); \<Gamma> \<turnstile> e2 : Data(\<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Pr e1 e2 : Data (DProd \<sigma>1 \<sigma>2)"
t5[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(DProd \<sigma>1 \<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Fst e : Data(\<sigma>1)"
t6[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(DProd \<sigma>1 \<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Snd e : Data(\<sigma>2)"
t7[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(\<sigma>1)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> InL e : Data(DSum \<sigma>1 \<sigma>2)"
t8[intro]: "\<lbrakk>\<Gamma> \<turnstile> e : Data(\<sigma>2)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> InR e : Data(DSum \<sigma>1 \<sigma>2)"
t9[intro]: "\<lbrakk>x1\<sharp>\<Gamma>; x2\<sharp>\<Gamma>; \<Gamma> \<turnstile> e: Data(DSum \<sigma>1 \<sigma>2); 
             ((x1,Data(\<sigma>1))#\<Gamma>) \<turnstile> e1 : \<tau>; ((x2,Data(\<sigma>2))#\<Gamma>) \<turnstile> e2 : \<tau>\<rbrakk> 
             \<Longrightarrow> \<Gamma> \<turnstile> (Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2) : \<tau>"

text {* typing judgements for Itrms *}

consts
  Ityping :: "(((name\<times>tyI) list)\<times>trmI\<times>tyI) set" 
syntax
  "_typing_judge" :: "(name\<times>tyI) list\<Rightarrow>trmI\<Rightarrow>tyI\<Rightarrow>bool" (" _ I\<turnstile> _ : _ " [80,80,80] 80) 
translations
  "\<Gamma> I\<turnstile> t : \<tau>" \<rightleftharpoons> "(\<Gamma>,t,\<tau>) \<in> Ityping"  

inductive Ityping
intros
t0[intro]: "\<lbrakk>valid \<Gamma>; (x,\<tau>)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> I\<turnstile> IVar x : \<tau>"
t1[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e1 : \<tau>1\<rightarrow>\<tau>2; \<Gamma> I\<turnstile> e2 : \<tau>1\<rbrakk>\<Longrightarrow> \<Gamma> I\<turnstile> IApp e1 e2 : \<tau>2"
t2[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,\<tau>1)#\<Gamma>) I\<turnstile> t : \<tau>2\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> ILam [x].t : \<tau>1\<rightarrow>\<tau>2"
t3[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> I\<turnstile> IUnit : DataI(OneI)"
t4[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> I\<turnstile> INat(n) : DataI(NatI)"
t5[intro]: "\<Gamma> I\<turnstile> e : DataI(NatI) \<Longrightarrow> \<Gamma> I\<turnstile> ISucc(e) : DataI(NatI)"
t6[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e : DataI(NatI)\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> IRef e : DataI (NatI)"
t7[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e1 : DataI(NatI); \<Gamma> I\<turnstile> e2 : DataI(NatI)\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> e1\<mapsto>e2 : DataI(OneI)"
t8[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e1 : DataI(NatI); \<Gamma> I\<turnstile> e2 : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> e1;;e2 : \<tau>"
t9[intro]: "\<lbrakk>\<Gamma> I\<turnstile> e: DataI(NatI); \<Gamma> I\<turnstile> e1 : \<tau>; \<Gamma> I\<turnstile> e2 : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> I\<turnstile> Iif e e1 e2 : \<tau>"

text {* capture-avoiding substitution *}

consts
 subst :: "'a \<Rightarrow> name \<Rightarrow> 'a \<Rightarrow> 'a"  ("_[_::=_]" [100,100,100] 100)

constdefs 
  subst_Var :: "name \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm"
  "subst_Var x t' \<equiv> \<lambda>y. (if y=x then t' else (Var y))"
  
  subst_App :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_App x t' \<equiv> \<lambda>_ _ r1 r2. App r1 r2"

  subst_Lam :: "name \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_Lam x t' \<equiv> \<lambda>a _ r. Lam [a].r"

  subst_Const :: "name \<Rightarrow> trm \<Rightarrow> nat \<Rightarrow> trm"
  "subst_Const x t' \<equiv> \<lambda>n. Const n"

  subst_Pr :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_Pr x t' \<equiv> \<lambda>_ _ r1 r2. Pr r1 r2"

  subst_Fst :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_Fst x t' \<equiv> \<lambda>_ r. Fst r"

  subst_Snd :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_Snd x t' \<equiv> \<lambda>_ r. Snd r"
 
  subst_InL :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_InL x t' \<equiv> \<lambda>_ r. InL r"

  subst_InR :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_InR x t' \<equiv> \<lambda>_ r. InR r"

  subst_Case :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  "subst_Case x t' \<equiv> \<lambda>_ x _ y _ r r1 r2. Case r of inl x \<rightarrow> r1 | inr y \<rightarrow> r2"

defs(overloaded)
  subst_def: 
    "t[x::=t'] \<equiv> trm_rec (subst_Var x t') (subst_Lam x t') (subst_App x t')
                        (subst_Const x t') (subst_Pr x t') (subst_Fst x t') (subst_Snd x t')
                         (subst_InL x t') (subst_InR x t') (subst_Case x t') t"

(* FIXME: the next two lemmas need to be in Nominal.thy *)
lemma perm_if:
  fixes pi::"'a prm"
  shows "pi\<bullet>(if b then c1 else c2) = (if (pi\<bullet>b) then (pi\<bullet>c1) else (pi\<bullet>c2))"
apply(simp add: perm_fun_def)
done

lemma eq_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
  apply(simp add: perm_bool perm_bij)
  done

lemma fin_supp_subst:
  shows "finite ((supp (subst_Var x t))::name set)"
  and   "finite ((supp (subst_Lam x t))::name set)"
  and   "finite ((supp (subst_App x t))::name set)"
  and   "finite ((supp (subst_Const x t))::name set)"
  and   "finite ((supp (subst_Pr x t))::name set)"
  and   "finite ((supp (subst_Fst x t))::name set)"
  and   "finite ((supp (subst_Snd x t))::name set)"
  and   "finite ((supp (subst_InL x t))::name set)"
  and   "finite ((supp (subst_InR x t))::name set)"
  and   "finite ((supp (subst_Case x t))::name set)"
apply -
apply(finite_guess add: fs_name1 subst_Var_def perm_if eq_eqvt)
apply(finite_guess add: fs_name1 subst_Lam_def)
apply(finite_guess add: fs_name1 subst_App_def)
apply(finite_guess add: fs_name1 subst_Const_def)
apply(finite_guess add: fs_name1 subst_Pr_def)
apply(finite_guess add: fs_name1 subst_Fst_def)
apply(finite_guess add: fs_name1 subst_Snd_def)
apply(finite_guess add: fs_name1 subst_InL_def)
apply(finite_guess add: fs_name1 subst_InR_def)
apply(finite_guess only: fs_name1 subst_Case_def)
apply(perm_simp)
apply(simp)
done

lemma fcb_subst_Lam:
  shows "x\<sharp>(subst_Lam y t') x t r"
  by (simp add: subst_Lam_def abs_fresh)

lemma fcb_subst_Case:
  assumes a: "x\<sharp>r" "x\<sharp>r2" "y\<sharp>r" "y\<sharp>r1"
  shows "x\<sharp>(subst_Case z t') e x e1 y e2 r r1 r2 \<and> y\<sharp>(subst_Case z t') e x e1 y e2 r r1 r2"
  using a
  by (simp add: subst_Case_def abs_fresh)

lemma subst:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  and   "\<lbrakk>x\<sharp>y; x\<sharp>t'\<rbrakk> \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
  and   "(Const n)[y::=t'] = Const n"
  and   "(Pr e1 e2)[y::=t'] = Pr (e1[y::=t']) (e2[y::=t'])"
  and   "(Fst e)[y::=t'] = Fst (e[y::=t'])"
  and   "(Snd e)[y::=t'] = Snd (e[y::=t'])"
  and   "(InL e)[y::=t'] = InL (e[y::=t'])"
  and   "(InR e)[y::=t'] = InR (e[y::=t'])"
  and   "\<lbrakk>z\<noteq>x; x\<sharp>y; x\<sharp>e; x\<sharp>e2; z\<sharp>y; z\<sharp>e; z\<sharp>e1; x\<sharp>t'; z\<sharp>t'\<rbrakk> 
         \<Longrightarrow> (Case e of inl x \<rightarrow> e1 | inr z \<rightarrow> e2)[y::=t'] =
                                    (Case (e[y::=t']) of inl x \<rightarrow> (e1[y::=t']) | inr z \<rightarrow> (e2[y::=t']))"
apply(unfold subst_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_Var_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_App_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(fresh_guess add: fs_name1 subst_Var_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 subst_Lam_def)
apply(fresh_guess add: fs_name1 subst_App_def)
apply(fresh_guess add: fs_name1 subst_Const_def)
apply(fresh_guess add: fs_name1 subst_Pr_def)
apply(fresh_guess add: fs_name1 subst_Fst_def)
apply(fresh_guess add: fs_name1 subst_Snd_def)
apply(fresh_guess add: fs_name1 subst_InL_def)
apply(fresh_guess add: fs_name1 subst_InR_def)
apply(fresh_guess only: fs_name1 subst_Case_def)
apply(perm_simp)
apply(simp, simp)
apply(simp add: subst_Lam_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_Const_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_Pr_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_Fst_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_Snd_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_InL_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(simp add: subst_InR_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_subst)+
apply(simp add: fcb_subst_Lam)
apply(simp add: fcb_subst_Case)
apply(fresh_guess add: fs_name1 subst_Var_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 subst_Var_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 subst_Lam_def)
apply(fresh_guess add: fs_name1 subst_Lam_def)
apply(fresh_guess add: fs_name1 subst_App_def)
apply(fresh_guess add: fs_name1 subst_App_def)
apply(fresh_guess add: fs_name1 subst_Const_def)
apply(fresh_guess add: fs_name1 subst_Const_def)
apply(fresh_guess add: fs_name1 subst_Pr_def)
apply(fresh_guess add: fs_name1 subst_Pr_def)
apply(fresh_guess add: fs_name1 subst_Fst_def)
apply(fresh_guess add: fs_name1 subst_Fst_def)
apply(fresh_guess add: fs_name1 subst_Snd_def)
apply(fresh_guess add: fs_name1 subst_Snd_def)
apply(fresh_guess add: fs_name1 subst_InL_def)
apply(fresh_guess add: fs_name1 subst_InL_def)
apply(fresh_guess add: fs_name1 subst_InR_def)
apply(fresh_guess add: fs_name1 subst_InR_def)
apply(fresh_guess only: fs_name1 subst_Case_def)
apply(perm_simp)
apply(simp, simp)
apply(fresh_guess only: fs_name1 subst_Case_def)
apply(perm_simp)
apply(simp, simp)
apply(assumption)+
apply(simp add: subst_Case_def)
done

constdefs 
  subst_IVar :: "name \<Rightarrow> trmI \<Rightarrow> name \<Rightarrow> trmI"
  "subst_IVar x t' \<equiv> \<lambda>y. (if y=x then t' else (IVar y))"
  
  subst_IApp :: "name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_IApp x t' \<equiv> \<lambda>_ _ r1 r2. IApp r1 r2"

  subst_ILam :: "name \<Rightarrow> trmI \<Rightarrow> name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_ILam x t' \<equiv> \<lambda>a _ r. ILam [a].r"

  subst_IUnit :: "name \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_IUnit x t' \<equiv> IUnit"

  subst_INat :: "name \<Rightarrow> trmI \<Rightarrow> nat \<Rightarrow> trmI"
  "subst_INat x t' \<equiv> \<lambda>n. INat n"

  subst_ISucc :: "name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_ISucc x t' \<equiv> \<lambda>_ r. ISucc r"

  subst_IAss :: "name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_IAss x t' \<equiv> \<lambda>_ _ r1 r2. r1\<mapsto>r2"
 
  subst_IRef :: "name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_IRef x t' \<equiv> \<lambda>_ r. IRef r"

  subst_ISeq :: "name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_ISeq x t' \<equiv> \<lambda>_ _ r1 r2. ISeq r1 r2"

  subst_Iif :: "name \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "subst_Iif x t' \<equiv> \<lambda>_ _ _ r r1 r2. Iif r r1 r2"

defs(overloaded)
  subst_trmI_def: 
    "t[x::=t'] \<equiv> trmI_rec (subst_IVar x t') (subst_ILam x t') (subst_IApp x t')
                        (subst_IUnit x t') (subst_INat x t') (subst_ISucc x t') (subst_IAss x t')
                         (subst_IRef x t') (subst_ISeq x t') (subst_Iif x t') t"

lemma fin_supp_Isubst:
  shows "finite ((supp (subst_IVar x t))::name set)"
  and   "finite ((supp (subst_ILam x t))::name set)"
  and   "finite ((supp (subst_IApp x t))::name set)"
  and   "finite ((supp (subst_INat x t))::name set)"
  and   "finite ((supp (subst_IUnit x t))::name set)"
  and   "finite ((supp (subst_ISucc x t))::name set)"
  and   "finite ((supp (subst_IAss x t))::name set)"
  and   "finite ((supp (subst_IRef x t))::name set)"
  and   "finite ((supp (subst_ISeq x t))::name set)"
  and   "finite ((supp (subst_Iif x t))::name set)"
apply -
apply(finite_guess add: fs_name1 subst_IVar_def perm_if eq_eqvt)
apply(finite_guess add: fs_name1 subst_ILam_def)
apply(finite_guess add: fs_name1 subst_IApp_def)
apply(finite_guess add: fs_name1 subst_INat_def)
apply(finite_guess add: fs_name1 subst_IUnit_def)
apply(finite_guess add: fs_name1 subst_ISucc_def)
apply(finite_guess add: fs_name1 subst_IAss_def)
apply(finite_guess add: fs_name1 subst_IRef_def)
apply(finite_guess add: fs_name1 subst_ISeq_def)
apply(finite_guess only: fs_name1 subst_Iif_def)
apply(perm_simp)
apply(simp)
done

lemma fcb_subst_ILam:
  shows "x\<sharp>(subst_ILam y t') x t r"
  by (simp add: subst_ILam_def abs_fresh)

lemma Isubst:
  shows "(IVar x)[y::=t'] = (if x=y then t' else (IVar x))"
  and   "(IApp t1 t2)[y::=t'] = IApp (t1[y::=t']) (t2[y::=t'])"
  and   "\<lbrakk>x\<sharp>y; x\<sharp>t'\<rbrakk> \<Longrightarrow> (ILam [x].t)[y::=t'] = ILam [x].(t[y::=t'])"
  and   "(INat n)[y::=t'] = INat n"
  and   "(IUnit)[y::=t'] = IUnit"
  and   "(ISucc e)[y::=t'] = ISucc (e[y::=t'])"
  and   "(IAss e1 e2)[y::=t'] = IAss (e1[y::=t']) (e2[y::=t'])"
  and   "(IRef e)[y::=t'] = IRef (e[y::=t'])"
  and   "(ISeq e1 e2)[y::=t'] = ISeq (e1[y::=t']) (e2[y::=t'])"
  and   "(Iif e e1 e2)[y::=t'] = Iif (e[y::=t']) (e1[y::=t']) (e2[y::=t'])"
apply(unfold subst_trmI_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_IVar_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_IApp_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(fresh_guess add: fs_name1 subst_IVar_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 subst_ILam_def)
apply(fresh_guess add: fs_name1 subst_IApp_def)
apply(fresh_guess add: fs_name1 subst_IUnit_def)
apply(fresh_guess add: fs_name1 subst_INat_def)
apply(fresh_guess add: fs_name1 subst_ISucc_def)
apply(fresh_guess add: fs_name1 subst_IAss_def)
apply(fresh_guess add: fs_name1 subst_IRef_def)
apply(fresh_guess add: fs_name1 subst_ISeq_def)
apply(fresh_guess only: fs_name1 subst_Iif_def)
apply(perm_simp)
apply(simp, simp)
apply(simp add: subst_ILam_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_INat_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_IUnit_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_ISucc_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_IAss_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_IRef_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_ISeq_def)
apply(rule trans)
apply(rule trmI.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_Isubst)+
apply(simp add: fcb_subst_ILam)
apply(simp add: subst_Iif_def)
done

lemma Isubst_eqvt:
  fixes pi::"name prm"
  and   t1::"trmI"
  and   t2::"trmI"
  and   x::"name"
  shows "pi\<bullet>(t1[x::=t2]) = ((pi\<bullet>t1)[(pi\<bullet>x)::=(pi\<bullet>t2)])"
  apply(nominal_induct t1 avoiding: x t2 rule: trmI.induct)
  apply(simp_all add: Isubst perm_if eq_eqvt fresh_bij)
  done

lemma Isubst_supp:
  fixes t1::"trmI"
  and   t2::"trmI"
  and   x::"name"
  shows "((supp (t1[x::=t2]))::name set) \<subseteq> (supp t2)\<union>((supp t1)-{x})"
apply(nominal_induct t1 avoiding: x t2 rule: trmI.induct)
apply(auto simp add: Isubst trmI.supp supp_atm abs_supp supp_nat)
apply(blast)+
done

lemma Isubst_fresh:
  fixes x::"name"
  and   y::"name"
  and   t1::"trmI"
  and   t2::"trmI"
  assumes a: "x\<sharp>[y].t1" "x\<sharp>t2"
  shows "x\<sharp>(t1[y::=t2])"
using a
apply(auto simp add: fresh_def Isubst_supp)
apply(drule rev_subsetD)
apply(rule Isubst_supp)
apply(simp add: abs_supp)
done

text {* big-step evaluation for trms *}

consts
  big :: "(trm\<times>trm) set" 
syntax
  "_big_judge" :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<Down> _" [80,80] 80) 
translations
  "e1 \<Down> e2" \<rightleftharpoons> "(e1,e2) \<in> big"

inductive big
intros
b0[intro]: "Lam [x].e \<Down> Lam [x].e"
b1[intro]: "\<lbrakk>e1\<Down>Lam [x].e; e2\<Down>e2'; e[x::=e2']\<Down>e'\<rbrakk> \<Longrightarrow> App e1 e2 \<Down> e'"
b2[intro]: "Const n \<Down> Const n"
b3[intro]: "\<lbrakk>e1\<Down>e1'; e2\<Down>e2'\<rbrakk> \<Longrightarrow> Pr e1 e2 \<Down> Pr e1' e2'"
b4[intro]: "e\<Down>Pr e1 e2 \<Longrightarrow> Fst e\<Down>e1"
b5[intro]: "e\<Down>Pr e1 e2 \<Longrightarrow> Snd e\<Down>e2"
b6[intro]: "e\<Down>e' \<Longrightarrow> InL e \<Down> InL e'"
b7[intro]: "e\<Down>e' \<Longrightarrow> InR e \<Down> InR e'"
b8[intro]: "\<lbrakk>e\<Down>InL e'; e1[x::=e']\<Down>e''\<rbrakk> \<Longrightarrow> Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2 \<Down> e''"
b9[intro]: "\<lbrakk>e\<Down>InR e'; e2[x::=e']\<Down>e''\<rbrakk> \<Longrightarrow> Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2 \<Down> e''"

consts
  Ibig :: "(((nat\<Rightarrow>nat)\<times>trmI)\<times>((nat\<Rightarrow>nat)\<times>trmI)) set" 
syntax
  "_Ibig_judge" :: "((nat\<Rightarrow>nat)\<times>trmI)\<Rightarrow>((nat\<Rightarrow>nat)\<times>trmI)\<Rightarrow>bool" ("_ I\<Down> _" [80,80] 80) 
translations
  "(m,e1) I\<Down> (m',e2)" \<rightleftharpoons> "((m,e1),(m',e2)) \<in> Ibig"

inductive Ibig
intros
m0[intro]: "(m,ILam [x].e) I\<Down> (m,ILam [x].e)"
m1[intro]: "\<lbrakk>(m,e1)I\<Down>(m',ILam [x].e); (m',e2)I\<Down>(m'',e3); (m'',e[x::=e3])I\<Down>(m''',e4)\<rbrakk> 
            \<Longrightarrow> (m,IApp e1 e2) I\<Down> (m''',e4)"
m2[intro]: "(m,IUnit) I\<Down> (m,IUnit)"
m3[intro]: "(m,INat(n))I\<Down>(m,INat(n))"
m4[intro]: "(m,e)I\<Down>(m',INat(n)) \<Longrightarrow> (m,ISucc(e))I\<Down>(m',INat(n+1))"
m5[intro]: "(m,e)I\<Down>(m',INat(n)) \<Longrightarrow> (m,IRef(e))I\<Down>(m',INat(m' n))"
m6[intro]: "\<lbrakk>(m,e1)I\<Down>(m',INat(n1)); (m',e2)I\<Down>(m'',INat(n2))\<rbrakk> \<Longrightarrow> (m,e1\<mapsto>e2)I\<Down>(m''(n1:=n2),IUnit)"
m7[intro]: "\<lbrakk>(m,e1)I\<Down>(m',IUnit); (m',e2)I\<Down>(m'',e)\<rbrakk> \<Longrightarrow> (m,e1;;e2)I\<Down>(m'',e)"
m8[intro]: "\<lbrakk>(m,e)I\<Down>(m',INat(n)); n\<noteq>0; (m',e1)I\<Down>(m'',e)\<rbrakk> \<Longrightarrow> (m,Iif e e1 e2)I\<Down>(m'',e)"
m9[intro]: "\<lbrakk>(m,e)I\<Down>(m',INat(0)); (m',e2)I\<Down>(m'',e)\<rbrakk> \<Longrightarrow> (m,Iif e e1 e2)I\<Down>(m'',e)"

text {* Translation functions *}

constdefs 
  trans_data :: "data \<Rightarrow> tyI"
  "trans_data \<equiv> \<lambda>_. DataI(NatI)"
  
  trans_arrow :: "ty \<Rightarrow> ty \<Rightarrow> tyI \<Rightarrow> tyI \<Rightarrow> tyI"
  "trans_arrow \<equiv> \<lambda>_ _ r1 r2. ArrowI r1 r2"

  trans_type::"ty \<Rightarrow> tyI"  
  "trans_type \<tau> \<equiv> ty_rec (trans_data) (trans_arrow) \<tau>"

lemma trans_type:
  shows "trans_type (Data \<sigma>) = DataI(NatI)"
  and   "trans_type (\<tau>1\<rightarrow>\<tau>2) = (trans_type \<tau>1)\<rightarrow>(trans_type \<tau>2)"
apply(unfold trans_type_def)
apply(rule trans)
apply(rule ty.recs[where P="\<lambda>_. True", simplified])
apply(simp add: trans_data_def)
apply(rule trans)
apply(rule ty.recs[where P="\<lambda>_. True", simplified])
apply(simp add: trans_arrow_def)
done

constdefs 
  trans_Var :: "name \<Rightarrow> trmI"
  "trans_Var \<equiv> \<lambda>x. IVar x"
  
  trans_App :: "trm \<Rightarrow> trm \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_App \<equiv> \<lambda>_ _ r1 r2. IApp r1 r2"

  trans_Lam :: "name \<Rightarrow> trm \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_Lam \<equiv> \<lambda>a _ r. ILam [a].r"

  trans_Const :: "nat \<Rightarrow> trmI"
  "trans_Const \<equiv> \<lambda>n. INat n"

  trans_Pr :: "trm \<Rightarrow> trm \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_Pr \<equiv> \<lambda>_ _ r1 r2. 
         let limit = IRef(INat 0) in 
         let v1 = r1 in 
         let v2 = r2 in 
         (((ISucc limit)\<mapsto>v1);;(ISucc(ISucc limit)\<mapsto>v2));;(INat 0 \<mapsto> ISucc(ISucc(limit)))"

  trans_Fst :: "trm \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_Fst \<equiv> \<lambda>_ r. IRef (ISucc r)"

  trans_Snd :: "trm \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_Snd \<equiv> \<lambda>_ r. IRef (ISucc (ISucc r))"
 
  trans_InL :: "trm \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_InL \<equiv> \<lambda>_ r. 
         let limit = IRef(INat 0) in 
         let v = r in 
         (((ISucc limit)\<mapsto>INat(0));;(ISucc(ISucc limit)\<mapsto>v));;(INat 0 \<mapsto> ISucc(ISucc(limit)))"

  trans_InR :: "trm \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_InR \<equiv> \<lambda>_ r. 
         let limit = IRef(INat 0) in 
         let v = r in 
         (((ISucc limit)\<mapsto>INat(1));;(ISucc(ISucc limit)\<mapsto>v));;(INat 0 \<mapsto> ISucc(ISucc(limit)))"

  trans_Case :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI \<Rightarrow> trmI"
  "trans_Case \<equiv> \<lambda>_ x1 _ x2 _ r r1 r2. 
         let v = r in
         let v1 = r1 in
         let v2 = r2 in 
         Iif (IRef (ISucc v)) (v2[x2::=IRef (ISucc (ISucc v))]) (v1[x1::=IRef (ISucc (ISucc v))])"

  trans :: "trm \<Rightarrow> trmI" 
    "trans t \<equiv> trm_rec (trans_Var) (trans_Lam) (trans_App)
                           (trans_Const) (trans_Pr) (trans_Fst) (trans_Snd)
                           (trans_InL) (trans_InR) (trans_Case) t"

lemma fin_supp_trans:
  shows "finite ((supp (trans_Var))::name set)"
  and   "finite ((supp (trans_Lam))::name set)"
  and   "finite ((supp (trans_App))::name set)"
  and   "finite ((supp (trans_Const))::name set)"
  and   "finite ((supp (trans_Pr))::name set)"
  and   "finite ((supp (trans_Fst))::name set)"
  and   "finite ((supp (trans_Snd))::name set)"
  and   "finite ((supp (trans_InL))::name set)"
  and   "finite ((supp (trans_InR))::name set)"
  and   "finite ((supp (trans_Case))::name set)"
apply -
apply(finite_guess add: fs_name1 trans_Var_def)
apply(finite_guess add: fs_name1 trans_Lam_def)
apply(finite_guess add: fs_name1 trans_App_def)
apply(finite_guess add: fs_name1 trans_Const_def)
apply(finite_guess add: fs_name1 trans_Pr_def Let_def perm_nat_def)
apply(finite_guess add: fs_name1 trans_Fst_def)
apply(finite_guess add: fs_name1 trans_Snd_def)
apply(finite_guess add: fs_name1 trans_InL_def Let_def perm_nat_def)
apply(finite_guess add: fs_name1 trans_InR_def Let_def perm_nat_def)
apply(finite_guess add: fs_name1 trans_Case_def Let_def Isubst_eqvt)
done

lemma fcb_trans_Lam:
  shows "x\<sharp>(trans_Lam) x t r"
  by (simp add: trans_Lam_def abs_fresh)

lemma fcb_trans_Case:
  assumes a: "x\<sharp>r" "x\<sharp>r2" "y\<sharp>r" "y\<sharp>r1"
  shows "x\<sharp>(trans_Case) e x e1 y e2 r r1 r2 \<and> y\<sharp>(trans_Case) e x e1 y e2 r r1 r2"
  using a
  by (simp add: trans_Case_def abs_fresh Isubst_fresh)
  
lemma trans:
  shows "trans (Var x) = (IVar x)"
  and   "trans (App e1 e2) = IApp (trans e1) (trans e2)"
  and   "trans (Lam [x].e) = ILam [x].(trans e)"
  and   "trans (Const n) = INat n"
  and   "trans (Pr e1 e2) = 
             (let limit = IRef(INat 0) in 
              let v1 = (trans e1) in 
              let v2 = (trans e2) in 
              (((ISucc limit)\<mapsto>v1);;(ISucc(ISucc limit)\<mapsto>v2));;(INat 0 \<mapsto> ISucc(ISucc(limit))))"
  and   "trans (Fst e) = IRef (ISucc (trans e))"
  and   "trans (Snd e) = IRef (ISucc (ISucc (trans e)))"
  and   "trans (InL e) = 
              (let limit = IRef(INat 0) in 
               let v = (trans e) in 
               (((ISucc limit)\<mapsto>INat(0));;(ISucc(ISucc limit)\<mapsto>v));;(INat 0 \<mapsto> ISucc(ISucc(limit))))"
  and   "trans (InR e) = 
              (let limit = IRef(INat 0) in 
               let v = (trans e) in 
               (((ISucc limit)\<mapsto>INat(1));;(ISucc(ISucc limit)\<mapsto>v));;(INat 0 \<mapsto> ISucc(ISucc(limit))))"
  and   "\<lbrakk>x2\<noteq>x1; x1\<sharp>e; x1\<sharp>e2; x2\<sharp>e; x2\<sharp>e1\<rbrakk> \<Longrightarrow> 
         trans (Case e of inl x1 \<rightarrow> e1 | inr x2 \<rightarrow> e2) =
             (let v = (trans e) in
              let v1 = (trans e1) in
              let v2 = (trans e2) in 
              Iif (IRef (ISucc v)) (v2[x2::=IRef (ISucc (ISucc v))]) (v1[x1::=IRef (ISucc (ISucc v))]))"
apply(unfold trans_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_Var_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_App_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(fresh_guess add: fs_name1 trans_Var_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 trans_Lam_def)
apply(fresh_guess add: fs_name1 trans_App_def)
apply(fresh_guess add: fs_name1 trans_Const_def)
apply(fresh_guess add: fs_name1 trans_Pr_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_Fst_def)
apply(fresh_guess add: fs_name1 trans_Snd_def)
apply(fresh_guess add: fs_name1 trans_InL_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_InR_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_Case_def Let_def Isubst_eqvt)
apply(simp add: trans_Lam_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_Const_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_Pr_def Let_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_Fst_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_Snd_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_InL_def Let_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(simp add: trans_InR_def Let_def)
apply(rule trans)
apply(rule trm.recs[where P="\<lambda>_. True", simplified])
apply(rule fin_supp_trans)+
apply(simp add: fcb_trans_Lam)
apply(simp add: fcb_trans_Case)
apply(fresh_guess add: fs_name1 trans_Var_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 trans_Var_def perm_if eq_eqvt)
apply(fresh_guess add: fs_name1 trans_Lam_def)
apply(fresh_guess add: fs_name1 trans_Lam_def)
apply(fresh_guess add: fs_name1 trans_App_def)
apply(fresh_guess add: fs_name1 trans_App_def)
apply(fresh_guess add: fs_name1 trans_Const_def)
apply(fresh_guess add: fs_name1 trans_Const_def)
apply(fresh_guess add: fs_name1 trans_Pr_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_Pr_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_Fst_def)
apply(fresh_guess add: fs_name1 trans_Fst_def)
apply(fresh_guess add: fs_name1 trans_Snd_def)
apply(fresh_guess add: fs_name1 trans_Snd_def)
apply(fresh_guess add: fs_name1 trans_InL_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_InL_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_InR_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_InR_def Let_def perm_nat_def)
apply(fresh_guess add: fs_name1 trans_Case_def Let_def Isubst_eqvt)
apply(fresh_guess add: fs_name1 trans_Case_def Let_def Isubst_eqvt)
apply(assumption)+
apply(simp add: trans_Case_def Let_def)
done


end