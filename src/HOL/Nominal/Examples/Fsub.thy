(* $Id$ *)

theory fsub
imports "../nominal" 
begin

text {* Authors: Christian Urban,
                 Benjamin Pierce,
                 Steve Zdancewic.
                 Stephanie Weihrich and
                 Dimitrios Vytiniotis;

                 with help from Stefan Berghofer and  Markus Wenzel.
      *}


section {* Atom Types, Types and Terms *}

atom_decl tyvrs vrs

nominal_datatype ty = 
    TVar  "tyvrs"
  | Top
  | Arrow  "ty" "ty"          ("_ \<rightarrow> _" [900,900] 900)
  | TAll  "\<guillemotleft>tyvrs\<guillemotright>ty" "ty" 

nominal_datatype trm = 
    Var   "vrs"
  | Lam   "\<guillemotleft>vrs\<guillemotright>trm" "ty"
  | TAbs  "\<guillemotleft>tyvrs\<guillemotright>trm" "ty"
  | App   "trm" "trm"
  | TApp  "trm" "ty"

syntax
  TAll_syn  :: "tyvrs \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" ("\<forall> [_<:_]._" [900,900,900] 900)
  Lam_syn   :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"   ("Lam [_:_]._" [100,100,100] 100)
  TAbs_syn  :: "tyvrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("TAbs [_<:_]._" [100,100,100] 100)

translations 
  "\<forall>[a<:ty1].ty2" \<rightleftharpoons> "TAll a ty2 ty1"
  "Lam  [a:tys].t" \<rightleftharpoons> "trm.Lam a t tys"
  "TAbs [a<:tys].t" \<rightleftharpoons> "trm.TAbs a t tys"

subsection {* Typing contexts and Their Domains *}

types ty_context = "(tyvrs\<times>ty) list"

consts
  "domain" :: "ty_context \<Rightarrow> tyvrs set"
primrec
  "domain [] = {}"
  "domain (X#\<Gamma>) = {fst X}\<union>(domain \<Gamma>)" 

lemma domain_eqvt:
  fixes pi::"tyvrs prm"
  shows "pi\<bullet>(domain \<Gamma>) = domain (pi\<bullet>\<Gamma>)" 
  by (induct \<Gamma>, auto simp add: perm_set_def)

lemma finite_domain:
  fixes \<Gamma>::"ty_context"
  shows "finite (domain \<Gamma>)"
  by (induct \<Gamma>, auto)

lemma domain_inclusion:
  assumes a: "(X,T)\<in>set \<Gamma>" 
  shows "X\<in>(domain \<Gamma>)"
  using a by (induct \<Gamma>, auto)

lemma domain_existence:
  assumes a: "X\<in>(domain \<Gamma>)" 
  shows "\<exists>T.(X,T)\<in>set \<Gamma>"
  using a by (induct \<Gamma>, auto)

lemma domain_append:
  shows "domain (\<Gamma>@\<Delta>) = ((domain \<Gamma>) \<union> (domain \<Delta>))"
  by (induct \<Gamma>, auto)

section {* Size Functions and Capture Avoiding Substitutiuon for Types *}

text {* they cannot yet be defined conveniently unless we have a recursion combinator *}

consts size_ty :: "ty \<Rightarrow> nat"

lemma size_ty[simp]:
  shows "size_ty (TVar X) = 1"
  and   "size_ty (Top) = 1"
  and   "\<lbrakk>size_ty t1 = m ; size_ty t2 = n\<rbrakk> \<Longrightarrow> size_ty (t1 \<rightarrow> t2) = m + n + 1"
  and   "\<lbrakk>size_ty t1 = m ; size_ty t2 = n\<rbrakk> \<Longrightarrow> size_ty (\<forall> [a<:t1].t2) = m + n + 1"
sorry

consts subst_ty :: "ty \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> ty"

lemma subst_ty[simp]:
  shows "subst_ty (TVar X) Y T = (if X=Y then T else (TVar X))"
  and   "subst_ty Top Y T = Top"
  and   "subst_ty (T1 \<rightarrow> T2) Y T = (subst_ty T1 Y T) \<rightarrow> (subst_ty T2 Y T)"
  and   "X\<sharp>(Y,T) \<Longrightarrow> subst_ty (\<forall>[X<:T1].T2) Y T = (\<forall>[X<:(subst_ty T1 Y T)].(subst_ty T2 Y T))"
  and   "\<lbrakk>X\<sharp>Y; X\<sharp>T\<rbrakk> \<Longrightarrow> subst_ty (\<forall>[X<:T1].T2) Y T = (\<forall>[X<:(subst_ty T1 Y T)].(subst_ty T2 Y T))"
sorry


consts subst_ctxt :: "ty_context \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> ty_context"
primrec
"subst_ctxt [] Y T = []"
"subst_ctxt (XT#Xs) Y T = (fst XT, subst_ty (snd XT) Y T)#(subst_ctxt Xs Y T)"

subsection {* valid contexts *}

constdefs
  "closed_in" :: "ty \<Rightarrow> ty_context \<Rightarrow> bool" ("_ closed'_in _" [100,100] 100)
  "S closed_in \<Gamma> \<equiv> (supp S)\<subseteq>(domain \<Gamma>)"

lemma closed_in_def2:
  shows "(S closed_in \<Gamma>) = ((supp S)\<subseteq>((supp (domain \<Gamma>)):: tyvrs set))"
apply(simp add: closed_in_def)
apply(simp add: at_fin_set_supp[OF at_tyvrs_inst, OF finite_domain])
done

lemma closed_in_eqvt:
  fixes pi::"tyvrs prm"
  assumes a: "S closed_in \<Gamma>" 
  shows "(pi\<bullet>S) closed_in (pi\<bullet>\<Gamma>)"
  using a
proof (unfold "closed_in_def")
  assume "supp S \<subseteq> (domain \<Gamma>)" 
  hence "pi\<bullet>(supp S) \<subseteq> pi\<bullet>(domain \<Gamma>)"
    by (simp add: pt_subseteq_eqvt[OF pt_tyvrs_inst, OF at_tyvrs_inst])
  thus "(supp (pi\<bullet>S)) \<subseteq> (domain (pi\<bullet>\<Gamma>))"
    by (simp add: domain_eqvt pt_perm_supp[OF pt_tyvrs_inst, OF at_tyvrs_inst])
qed

consts
  valid_rel :: "ty_context set" 
  valid_sym :: "ty_context \<Rightarrow> bool" ("\<turnstile> _ ok" [100] 100)
translations
  "\<turnstile> \<Gamma> ok" \<rightleftharpoons> "\<Gamma> \<in> valid_rel"  
inductive valid_rel
intros
v1[intro]: "\<turnstile> [] ok"
v2[intro]: "\<lbrakk>\<turnstile> \<Gamma> ok; X\<sharp>\<Gamma>; T closed_in \<Gamma>\<rbrakk>  \<Longrightarrow>  \<turnstile> ((X,T)#\<Gamma>) ok"

lemma valid_eqvt:
  fixes pi::"tyvrs prm"
  assumes a: "\<turnstile> \<Gamma> ok" 
  shows "\<turnstile> (pi\<bullet>\<Gamma>) ok"
  using a
proof (induct)
  case v1
  show ?case by force
next
  case (v2 T X \<Gamma>)
  have a1: "\<turnstile> (pi \<bullet> \<Gamma>) ok" by fact
  have a2: "X\<sharp>\<Gamma>" by fact
  have a3: "T closed_in \<Gamma>" by fact
  show ?case
  proof (simp, rule valid_rel.v2)
    show "\<turnstile> (pi \<bullet> \<Gamma>) ok" using a1 by simp
  next 
    show "(pi\<bullet>X)\<sharp>(pi\<bullet>\<Gamma>)" using a2 by (simp add: fresh_eqvt)
  next
    show "(pi\<bullet>T) closed_in (pi\<bullet>\<Gamma>)" using a3 by (rule closed_in_eqvt)
  qed
qed

lemma validE:
  assumes a: "\<turnstile> ((X,T)#\<Gamma>) ok"
  shows "\<turnstile> \<Gamma> ok \<and> X\<sharp>\<Gamma> \<and> T closed_in \<Gamma>"
using a by (cases, auto)

lemma validE_append:
  assumes a: "\<turnstile> (\<Delta>@\<Gamma>) ok" 
  shows "\<turnstile> \<Gamma> ok"
  using a by (induct \<Delta>, auto dest: validE)

lemma domain_fresh:
  fixes X::"tyvrs"
  assumes a: "\<turnstile> \<Gamma> ok" 
  shows "X\<sharp>(domain \<Gamma>) = X\<sharp>\<Gamma>"
using a
apply(induct \<Gamma>)
apply(auto simp add: fresh_list_nil fresh_list_cons fresh_set_empty fresh_prod fresh_atm
  fresh_fin_insert[OF pt_tyvrs_inst, OF at_tyvrs_inst, OF fs_tyvrs_inst, OF finite_domain])
apply(force simp add: closed_in_def2 fresh_def)
done

lemma closed_in_fresh:
  fixes X::"tyvrs"
  assumes a1: "S closed_in \<Gamma>"
  and     a2: "X\<sharp>\<Gamma>" 
  and     a3: "\<turnstile> \<Gamma> ok"
  shows "X\<sharp>S"
using a1 a2 a3
apply(simp add: closed_in_def2)
apply(simp add: domain_fresh[symmetric])
apply(simp add: fresh_def)
apply(force)
done

lemma replace_type:
  assumes a: "\<turnstile> (\<Delta>@(X,T)#\<Gamma>) ok"
  and     b: "S closed_in \<Gamma>"
  shows "\<turnstile> (\<Delta>@(X,S)#\<Gamma>) ok"
using a b 
apply(induct \<Delta>)
apply(auto dest!: validE intro!: v2 simp add: fresh_list_append fresh_list_cons fresh_prod)
apply(drule validE_append)
apply(drule validE)
apply(drule_tac S="S" in closed_in_fresh)
apply(simp)
apply(force)+
apply(simp add: closed_in_def2)
apply(simp add: domain_append)
done

lemma fresh_implies_not_member:
  fixes \<Gamma>::"ty_context"
  assumes a: "X\<sharp>\<Gamma>" 
  shows "\<not>(\<exists>T.(X,T)\<in>(set \<Gamma>))"
  using a
  apply (induct \<Gamma>)
  apply (auto dest: validE simp add: fresh_list_cons fresh_prod fresh_atm)
  done
 
lemma uniqueness_of_ctxt:
  fixes \<Gamma>::"ty_context"
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "(X,T)\<in>set \<Gamma>"
  and     c: "(X,S)\<in>set \<Gamma>"
  shows "T=S"
using a b c
apply (induct \<Gamma>)
apply (auto dest!: validE fresh_implies_not_member)
done
 
section {* Subtyping *}

consts
  subtype_of_rel :: "(ty_context \<times> ty \<times> ty) set"   
  subtype_of_sym :: "ty_context \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"   ("_ \<turnstile> _ <: _" [100,100,100] 100)
translations
  "\<Gamma> \<turnstile> S <: T" \<rightleftharpoons> "(\<Gamma>,S,T) \<in> subtype_of_rel"
inductive subtype_of_rel
intros
S_Top[intro]:   "\<lbrakk>\<turnstile> \<Gamma> ok; S closed_in \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
S_Var[intro]:   "\<lbrakk>\<turnstile> \<Gamma> ok; (X,S) \<in> set \<Gamma>; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (TVar X) <: T"
S_Refl[intro]:  "\<lbrakk>\<turnstile> \<Gamma> ok; X \<in> domain \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> TVar X <: TVar X"
S_Arrow[intro]: "\<lbrakk>\<Gamma> \<turnstile> T1 <: S1; \<Gamma> \<turnstile> S2 <: T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (S1 \<rightarrow> S2) <: (T1 \<rightarrow> T2)" 
S_All[intro]:   "\<lbrakk>\<Gamma> \<turnstile> T1 <: S1; X\<sharp>\<Gamma>; ((X,T1)#\<Gamma>) \<turnstile> S2 <: T2\<rbrakk> 
                  \<Longrightarrow> \<Gamma> \<turnstile> \<forall> [X<:S1].S2 <: \<forall> [X<:T1].T2"  

lemma subtype_implies_closed:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  shows "S closed_in \<Gamma> \<and> T closed_in \<Gamma>"
using a
proof (induct)
  case (S_Top S \<Gamma>)
  have "Top closed_in \<Gamma>" by (simp add: closed_in_def ty.supp)
  moreover
  have "S closed_in \<Gamma>" by fact
  ultimately show "S closed_in \<Gamma> \<and> Top closed_in \<Gamma>" by simp
next
  case (S_Var S T X \<Gamma>)
  have "(X,S)\<in>set \<Gamma>" by fact
  hence "X \<in> domain \<Gamma>" by (rule domain_inclusion)
  hence "(TVar X) closed_in \<Gamma>" by (simp add: closed_in_def ty.supp supp_atm)
  moreover
  have "S closed_in \<Gamma> \<and> T closed_in \<Gamma>" by fact
  hence "T closed_in \<Gamma>" by force
  ultimately show "(TVar X) closed_in \<Gamma> \<and> T closed_in \<Gamma>" by simp
qed (auto simp add: closed_in_def ty.supp supp_atm abs_supp)


lemma subtype_implies_ok:
  fixes X::"tyvrs"
  assumes a1: "\<Gamma> \<turnstile> S <: T"
  shows "\<turnstile> \<Gamma> ok"  
using a1 by (induct, auto)

lemma subtype_implies_fresh:
  fixes X::"tyvrs"
  assumes a1: "\<Gamma> \<turnstile> S <: T"
  and     a2: "X\<sharp>\<Gamma>"
  shows "X\<sharp>S \<and> X\<sharp>T"  
proof -
  from a1 have "\<turnstile> \<Gamma> ok" by (rule subtype_implies_ok)
  with a2 have "X\<sharp>domain(\<Gamma>)" by (simp add: domain_fresh)
  moreover
  from a1 have "S closed_in \<Gamma> \<and> T closed_in \<Gamma>" by (rule subtype_implies_closed)
  hence "supp S \<subseteq> ((supp (domain \<Gamma>))::tyvrs set)" 
    and "supp T \<subseteq> ((supp (domain \<Gamma>))::tyvrs set)" by (simp_all add: closed_in_def2)
  ultimately show "X\<sharp>S \<and> X\<sharp>T" by (force simp add: supp_prod fresh_def)
qed

lemma silly_eqvt1:
  fixes X::"'a::pt_tyvrs"
  and   S::"'b::pt_tyvrs"
  and   pi::"tyvrs prm"
 shows "(X,S) \<in> set \<Gamma> \<Longrightarrow> (pi\<bullet>X,pi\<bullet>S) \<in> set (pi\<bullet>\<Gamma>)"
apply(drule_tac pi="pi" in pt_set_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
apply(simp add: pt_list_set_pi[OF pt_tyvrs_inst])
done

lemma silly_eqvt2:
  fixes X::"tyvrs"
  and   pi::"tyvrs prm"
 shows "X \<in> (domain \<Gamma>) \<Longrightarrow> (pi\<bullet>X) \<in> (domain (pi\<bullet>\<Gamma>))"
apply(drule_tac pi="pi" in pt_set_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
apply(simp add: domain_eqvt pt_list_set_pi[OF pt_tyvrs_inst] )
done

lemma subtype_eqvt:
  fixes pi::"tyvrs prm"
  shows "\<Gamma> \<turnstile> S <: T \<Longrightarrow> (pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>S) <: (pi\<bullet>T)"
apply(erule subtype_of_rel.induct)
apply(force intro: valid_eqvt closed_in_eqvt)
apply(force intro: closed_in_eqvt valid_eqvt silly_eqvt1)
apply(force intro: valid_eqvt silly_eqvt2)
apply(force)
apply(force intro!: S_All simp add: fresh_prod pt_fresh_bij1[OF pt_tyvrs_inst, OF at_tyvrs_inst])
done

lemma subtype_of_rel_induct[consumes 1, case_names S_Top S_Var S_Refl S_Arrow S_All]:
  fixes  P :: "'a::fs_tyvrs\<Rightarrow>ty_context \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow>bool"
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and a1:    "\<And>\<Gamma> S x. \<turnstile> \<Gamma> ok \<Longrightarrow> S closed_in \<Gamma> \<Longrightarrow> P x \<Gamma> S Top"
  and a2:    "\<And>\<Gamma> X S T x. \<turnstile> \<Gamma> ok \<Longrightarrow> (X,S)\<in>set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> (\<And>z. P z \<Gamma> S T)
              \<Longrightarrow> P x \<Gamma> (TVar X) T"
  and a3:    "\<And>\<Gamma> X x. \<turnstile> \<Gamma> ok \<Longrightarrow> X\<in>domain \<Gamma> \<Longrightarrow> P x \<Gamma> (TVar X) (TVar X)"  
  and a4:    "\<And>\<Gamma> S1 S2 T1 T2 x. \<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow> (\<And>z. P z \<Gamma> T1 S1) \<Longrightarrow> \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> 
              (\<And>z. P z \<Gamma> S2 T2) \<Longrightarrow> P x \<Gamma> (S1 \<rightarrow> S2) (T1 \<rightarrow> T2)"
  and a5:    "\<And>\<Gamma> X S1 S2 T1 T2 x. 
              X\<sharp>x \<Longrightarrow> X\<sharp>(\<Gamma>,S1,T1) \<Longrightarrow> \<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow> (\<And>z. P z \<Gamma> T1 S1) \<Longrightarrow> ((X,T1)#\<Gamma>) \<turnstile> S2 <: T2 
              \<Longrightarrow> (\<And>z. P z ((X,T1)#\<Gamma>) S2 T2) \<Longrightarrow> P x \<Gamma> (\<forall> [X<:S1].S2) (\<forall> [X<:T1].T2)"
  shows "P x \<Gamma> S T"
proof -
  from a have "\<And>(pi::tyvrs prm) (x::'a::fs_tyvrs). P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>T)"
  proof (induct)
    case (S_Top S \<Gamma>) 
    thus "P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>Top)" by (force intro: valid_eqvt closed_in_eqvt a1)
  next
    case (S_Var S T X \<Gamma>)
    have b1: "\<turnstile> \<Gamma> ok" by fact 
    have b2: "(X,S) \<in> set \<Gamma>" by fact
    have b3: "\<Gamma> \<turnstile> S <: T" by fact
    have b4: "\<And>(pi::tyvrs prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>T)" by fact
    from b1 have "\<turnstile> (pi\<bullet>\<Gamma>) ok" by (rule valid_eqvt)
    moreover
    from b2 have "pi\<bullet>(X,S)\<in>pi\<bullet>(set \<Gamma>)" by (rule pt_set_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence "(pi\<bullet>X,pi\<bullet>S)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: pt_list_set_pi[OF pt_tyvrs_inst])
    moreover 
    from b3 have "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>S) <: (pi\<bullet>T)" by (rule subtype_eqvt)
    moreover 
    from b4 have "\<And>x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>T)" by simp
    ultimately 
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(TVar X)) (pi\<bullet>T)" by (simp add: a2)
  next
    case (S_Refl X \<Gamma>)
    have b1: "\<turnstile> \<Gamma> ok" by fact
    have b2: "X \<in> domain \<Gamma>" by fact
    from b1 have "\<turnstile> (pi\<bullet>\<Gamma>) ok" by (rule valid_eqvt)
    moreover
    from b2 have "(pi\<bullet>X)\<in>pi\<bullet>domain \<Gamma>" by (rule pt_set_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence "(pi\<bullet>X)\<in>domain (pi\<bullet>\<Gamma>)" by (simp add: domain_eqvt pt_list_set_pi[OF pt_tyvrs_inst])
    ultimately show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(TVar X)) (pi\<bullet>(TVar X))" by (simp add: a3)
  next
    case S_Arrow thus ?case by (auto intro: a4 subtype_eqvt)
  next
    case (S_All S1 S2 T1 T2 X \<Gamma>)
    have b1: "\<Gamma> \<turnstile> T1 <: S1" by fact 
    have b2: "\<And>(pi::tyvrs prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>T1) (pi\<bullet>S1)" by fact
    have b4: "((X,T1)#\<Gamma>) \<turnstile> S2 <: T2" by fact
    have b5: "\<And>(pi::tyvrs prm) x. P x (pi\<bullet>((X,T1)#\<Gamma>)) (pi\<bullet>S2) (pi\<bullet>T2)" by fact
    have b3': "X\<sharp>\<Gamma>" by fact
    have b3'': "X\<sharp>T1" "X\<sharp>S1" using b1 b3' by (simp_all add: subtype_implies_fresh)
    have b3: "X\<sharp>(\<Gamma>,S1,T1)" using b3' b3'' by (simp add: fresh_prod)
    have "\<exists>C::tyvrs. C\<sharp>(pi\<bullet>X,pi\<bullet>S2,pi\<bullet>T2,pi\<bullet>S1,pi\<bullet>T1,pi\<bullet>\<Gamma>,x)"
      by (rule at_exists_fresh[OF at_tyvrs_inst], simp add: fs_tyvrs1)
    then obtain C::"tyvrs" where  f1: "C\<noteq>(pi\<bullet>X)" and f2: "C\<sharp>(pi\<bullet>S1)" and f3: "C\<sharp>(pi\<bullet>T1)"
      and f4: "C\<sharp>(pi\<bullet>S2)" and f5: "C\<sharp>(pi\<bullet>T2)" and f6: "C\<sharp>(pi\<bullet>\<Gamma>)" and f7: "C\<sharp>x"
      by (auto simp add: fresh_prod fresh_atm)
    let ?pi' = "[(C,pi\<bullet>X)]@pi"
    from b2 have c1: "\<And>x. P x (?pi'\<bullet>\<Gamma>) (?pi'\<bullet>T1) (?pi'\<bullet>S1)" by simp
    from b5 have "\<And>x. P x (?pi'\<bullet>((X,T1)#\<Gamma>)) (?pi'\<bullet>S2) (?pi'\<bullet>T2)" by simp
    hence "\<And>x. P x ((?pi'\<bullet>X,?pi'\<bullet>T1)#(?pi'\<bullet>\<Gamma>)) (?pi'\<bullet>S2) (?pi'\<bullet>T2)" by simp
    hence c2: "\<And>x. P x ((C,?pi'\<bullet>T1)#(?pi'\<bullet>\<Gamma>)) (?pi'\<bullet>S2) (?pi'\<bullet>T2)" using f1
      by (simp only: pt_tyvrs2 calc_atm, simp)
    from b3 have "(pi\<bullet>X)\<sharp>(pi\<bullet>\<Gamma>)" 
      by (simp add: fresh_prod pt_fresh_bij[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    with f6 have f6a: "?pi'\<bullet>\<Gamma>=pi\<bullet>\<Gamma>" 
      by (simp only: pt_tyvrs2 pt_fresh_fresh[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence f6': "C\<sharp>(?pi'\<bullet>\<Gamma>)" using f6 by simp
    from b3 have "(pi\<bullet>X)\<sharp>(pi\<bullet>S1)" 
      by (simp add: fresh_prod pt_fresh_bij[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    with f2 have f2a: "?pi'\<bullet>S1=pi\<bullet>S1" 
      by (simp only: pt_tyvrs2 pt_fresh_fresh[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence f2': "C\<sharp>(?pi'\<bullet>S1)" using f2 by simp
    from b3 have "(pi\<bullet>X)\<sharp>(pi\<bullet>T1)" 
      by (simp add: fresh_prod pt_fresh_bij[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    with f3 have f3a: "?pi'\<bullet>T1=pi\<bullet>T1" 
      by (simp only: pt_tyvrs2 pt_fresh_fresh[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence f3': "C\<sharp>(?pi'\<bullet>T1)" using f3 by simp
    from b1 have e1: "(?pi'\<bullet>\<Gamma>) \<turnstile> (?pi'\<bullet>T1) <: (?pi'\<bullet>S1)" by (rule subtype_eqvt)
    from b4 have "(?pi'\<bullet>((X,T1)#\<Gamma>)) \<turnstile> (?pi'\<bullet>S2) <: (?pi'\<bullet>T2)" by (rule subtype_eqvt)
    hence "((?pi'\<bullet>X,?pi'\<bullet>T1)#(?pi'\<bullet>\<Gamma>)) \<turnstile> (?pi'\<bullet>S2) <: (?pi'\<bullet>T2)" by simp
    hence e2: "((C,?pi'\<bullet>T1)#(?pi'\<bullet>\<Gamma>)) \<turnstile> (?pi'\<bullet>S2) <: (?pi'\<bullet>T2)" using f1
      by (simp only: pt_tyvrs2 calc_atm, simp)
    have fnew: "C\<sharp>(?pi'\<bullet>\<Gamma>,?pi'\<bullet>S1,?pi'\<bullet>T1)" using f6' f2' f3' by (simp add: fresh_prod)
    have main: "P x (?pi'\<bullet>\<Gamma>) (\<forall> [C<:(?pi'\<bullet>S1)].(?pi'\<bullet>S2)) (\<forall> [C<:(?pi'\<bullet>T1)].(?pi'\<bullet>T2))"
      using f7 fnew e1 c1 e2 c2 by (rule a5)
    have alpha1: "(\<forall> [C<:(?pi'\<bullet>S1)].(?pi'\<bullet>S2)) = (pi\<bullet>(\<forall> [X<:S1].S2))"
      using f1 f4 f2a[symmetric] by (simp add: ty.inject alpha pt_tyvrs2[symmetric])
    have alpha2: "(\<forall> [C<:(?pi'\<bullet>T1)].(?pi'\<bullet>T2)) = (pi\<bullet>(\<forall> [X<:T1].T2))"
      using f1 f5 f3a[symmetric] by (simp add: ty.inject alpha pt_tyvrs2[symmetric])
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(\<forall> [X<:S1].S2)) (pi\<bullet>(\<forall> [X<:T1].T2))"
      using alpha1 alpha2 f6a main by simp  
  qed
  hence "P x (([]::tyvrs prm)\<bullet>\<Gamma>) (([]::tyvrs prm)\<bullet>S) (([]::tyvrs prm)\<bullet>T)" by blast
  thus ?thesis by simp
qed

subsection {* Reflexivity of Subtyping *}

lemma subtype_reflexivity:
  assumes a: "\<turnstile> \<Gamma> ok"
  and b: "T closed_in \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
using a b
proof(nominal_induct T avoiding: \<Gamma> rule: ty.induct_unsafe)
  case (TAll X T\<^isub>1 T\<^isub>2)
  have ih_T\<^isub>1: "\<And>\<Gamma>. \<turnstile> \<Gamma> ok \<Longrightarrow> T\<^isub>1 closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> T\<^isub>1 <: T\<^isub>1" by fact 
  have ih_T\<^isub>2: "\<And>\<Gamma>. \<turnstile> \<Gamma> ok \<Longrightarrow> T\<^isub>2 closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> T\<^isub>2 <: T\<^isub>2" by fact
  have fresh_cond: "X\<sharp>\<Gamma>" by fact
  have "(\<forall>[X<:T\<^isub>2].T\<^isub>1) closed_in \<Gamma>" by fact
  hence closed\<^isub>T\<^isub>2: "T\<^isub>2 closed_in \<Gamma>" and closed\<^isub>T\<^isub>1: "T\<^isub>1 closed_in ((X,T\<^isub>2)#\<Gamma>)" 
    by (auto simp add: closed_in_def ty.supp abs_supp)
  have ok: "\<turnstile> \<Gamma> ok" by fact  
  hence ok': "\<turnstile> ((X,T\<^isub>2)#\<Gamma>) ok" using closed\<^isub>T\<^isub>2 fresh_cond by force
  have "\<Gamma> \<turnstile> T\<^isub>2 <: T\<^isub>2" using ih_T\<^isub>2 closed\<^isub>T\<^isub>2 ok by simp
  moreover
  have "((X,T\<^isub>2)#\<Gamma>) \<turnstile> T\<^isub>1 <: T\<^isub>1" using ih_T\<^isub>1 closed\<^isub>T\<^isub>1 ok' by simp
  ultimately show "\<Gamma> \<turnstile> \<forall>[X<:T\<^isub>2].T\<^isub>1 <: \<forall>[X<:T\<^isub>2].T\<^isub>1" using fresh_cond 
    by (simp add: subtype_of_rel.S_All)
qed (auto simp add: closed_in_def ty.supp supp_atm)

lemma subtype_reflexivity:
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "T closed_in \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
using a b
apply(nominal_induct T avoiding: \<Gamma> rule: ty.induct_unsafe)
apply(auto simp add: ty.supp abs_supp closed_in_def supp_atm)
--{* Too bad that this instantiation cannot be found automatically. *}
apply(drule_tac x="(tyvrs, ty2)#\<Gamma>" in meta_spec)
apply(force simp add: closed_in_def)
done

text {* Inversion lemmas *}
lemma S_TopE:
  assumes a: "\<Gamma> \<turnstile> Top <: T"
  shows "T = Top"
using a by (cases, auto) 

lemma S_ArrowE_left:
  assumes a: "\<Gamma> \<turnstile> S1 \<rightarrow> S2 <: T" 
  shows "T = Top \<or> (\<exists>T1 T2. T = T1 \<rightarrow> T2 \<and> \<Gamma> \<turnstile> T1 <: S1 \<and> \<Gamma> \<turnstile> S2 <: T2)"
using a by (cases, auto simp add: ty.inject)

lemma S_AllE_left:
  shows "\<lbrakk>\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: T; X\<sharp>\<Gamma>; X\<sharp>S1\<rbrakk>
         \<Longrightarrow> T = Top \<or> (\<exists>T1 T2. T = \<forall>[X<:T1].T2 \<and> \<Gamma> \<turnstile> T1 <: S1 \<and> ((X,T1)#\<Gamma>) \<turnstile> S2 <: T2)"
  apply(frule subtype_implies_ok)
  apply(ind_cases "\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: T")
  apply(auto simp add: ty.inject alpha)
  apply(rule_tac x="[(X,Xa)]\<bullet>T2" in exI)
  (* term *)
  apply(rule conjI)
  apply(rule sym)
  apply(rule pt_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
  apply(rule pt_tyvrs3)
  apply(simp)
  apply(rule at_ds5[OF at_tyvrs_inst])
  (* 1st conjunct *)
  apply(rule conjI)
  apply(simp add: pt_fresh_left[OF pt_tyvrs_inst, OF at_tyvrs_inst] calc_atm)
  apply(drule_tac \<Gamma>="((Xa,T1)#\<Gamma>)" in  subtype_implies_closed)+
  apply(simp add: closed_in_def)
  apply(simp add: domain_fresh[of "\<Gamma>" "X", symmetric])
  apply(simp add: fresh_def)
  apply(subgoal_tac "X \<notin> (insert Xa (domain \<Gamma>))")(*A*)
  apply(force)
  (*A*)
  apply(simp add: at_fin_set_supp[OF at_tyvrs_inst, OF finite_domain])
  (* 2nd conjunct *)
  apply(frule_tac X="X" in subtype_implies_fresh)
  apply(assumption)
  apply(drule_tac X="Xa" in subtype_implies_fresh)
  apply(assumption)
  apply(simp add: fresh_prod)
  apply(drule_tac pi="[(X,Xa)]" in subtype_eqvt)
  apply(simp add: calc_atm)
  apply(simp add: pt_fresh_fresh[OF pt_tyvrs_inst, OF at_tyvrs_inst])
  done

section {* Type Substitution *}

lemma subst_ty_fresh:
  fixes X :: "tyvrs"
  assumes a: "X\<sharp>(T,P)"
  shows "X\<sharp>(subst_ty T Y P)"
  using a
  apply (nominal_induct T avoiding : T Y P rule: ty.induct_unsafe)
  apply (auto simp add: fresh_prod abs_fresh)
  done

lemma subst_ctxt_fresh:
  fixes X::"tyvrs"
  assumes a: "X\<sharp>(\<Gamma>,P)"
  shows "X\<sharp>(subst_ctxt \<Gamma> Y P)"
  using a
  apply (induct \<Gamma>)
  apply (auto intro: subst_ty_fresh simp add: fresh_prod fresh_list_cons)
  done

(*
lemma subst_ctxt_closed:
  shows  "subst_ty b X P closed_in (subst_ctxt \<Delta> X P @ \<Gamma>)"


lemma substitution_ok:
  shows "\<turnstile> (\<Delta>@(X,Q)#\<Gamma>) ok \<longrightarrow> \<Gamma> \<turnstile> P <: Q \<longrightarrow> \<turnstile> ((subst_ctxt \<Delta> X P)@\<Gamma>)  ok"
  apply (induct \<Delta>)
  apply (auto dest: validE)
  apply (rule v2)
  apply assumption
  apply (drule validE)
  apply (auto simp add: fresh_list_append)
  apply (rule subst_ctxt_fresh)
  apply (simp add: fresh_prod)
  apply (drule_tac X = "a" in subtype_implies_fresh)
  apply (simp add: fresh_list_cons)
  apply (simp add: fresh_prod)
  apply (simp add: fresh_list_cons)
  apply (drule validE)

done
*)

(* note: What should nominal induct do if the context is compound? *)
(*
lemma type_substitution:
  assumes a0: "(\<Delta>@(X,Q)#\<Gamma>) \<turnstile> S <: T"
  shows "\<turnstile> (\<Delta>@(X,Q)#\<Gamma>) ok \<longrightarrow> \<Gamma> \<turnstile> P <: Q 
         \<longrightarrow> ((subst_ctxt \<Delta> X P)@\<Gamma>) \<turnstile> (subst_ty S X P) <: (subst_ty T X P)"
  using a0 
  thm subtype_of_rel_induct
  apply(rule subtype_of_rel_induct[of "\<Delta>@(X,Q)#\<Gamma>" "S" "T" _ "P"])
  apply(auto)
  apply(rule S_Top)
  defer
  defer
  defer
  apply(rule S_Var)
  defer
  defer
  defer
  defer
  apply(rule S_Refl)
  defer
  defer


apply (nominal_induct \<Delta> X Q \<Gamma> S T rule: subtype_of_rel_induct)
*)

section {* Weakening *}

constdefs 
  extends :: "ty_context \<Rightarrow> ty_context \<Rightarrow> bool" ("_ extends _" [100,100] 100)
  "\<Delta> extends \<Gamma> \<equiv> \<forall>X Q. (X,Q)\<in>set \<Gamma> \<longrightarrow> (X,Q)\<in>set \<Delta>"

lemma extends_domain:
  assumes a: "\<Delta> extends \<Gamma>"
  shows "domain \<Gamma> \<subseteq> domain \<Delta>"
  using a 
  apply (auto simp add: extends_def)
  apply (drule domain_existence)
  apply (force simp add: domain_inclusion)
  done

lemma extends_closed:
  assumes a1: "T closed_in \<Gamma>"
  and     a2: "\<Delta> extends \<Gamma>"
  shows "T closed_in \<Delta>"
  using a1 a2
  by (auto dest: extends_domain simp add: closed_in_def)

lemma extends_memb:
  assumes a: "\<Delta> extends \<Gamma>"
  and b: "(X,T) \<in> set \<Gamma>"
  shows "(X,T) \<in> set \<Delta>"
  using a b by (simp add: extends_def)

lemma weakening:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and b: "\<turnstile> \<Delta> ok"
  and c: "\<Delta> extends \<Gamma>"
  shows "\<Delta> \<turnstile> S <: T"
  using a b c 
proof (nominal_induct \<Gamma> S T avoiding: \<Delta> rule: subtype_of_rel_induct)
  case (S_Top \<Gamma> S) 
  have lh_drv_prem: "S closed_in \<Gamma>" by fact
  have "\<turnstile> \<Delta> ok" by fact
  moreover
  have "\<Delta> extends \<Gamma>" by fact
  hence "S closed_in \<Delta>" using lh_drv_prem by (simp only: extends_closed)
  ultimately show "\<Delta> \<turnstile> S <: Top" by force
next 
  case (S_Var \<Gamma> X S T)
  have lh_drv_prem: "(X,S) \<in> set \<Gamma>" by fact
  have ih: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> S <: T" by fact
  have ok: "\<turnstile> \<Delta> ok" by fact
  have extends: "\<Delta> extends \<Gamma>" by fact
  have "(X,S) \<in> set \<Delta>" using lh_drv_prem extends by (simp only: extends_memb)
  moreover
  have "\<Delta> \<turnstile> S <: T" using ok extends ih by simp
  ultimately show "\<Delta> \<turnstile> TVar X <: T" using ok by force
next
  case (S_Refl \<Gamma> X)
  have lh_drv_prem: "X \<in> domain \<Gamma>" by fact
  have "\<turnstile> \<Delta> ok" by fact
  moreover
  have "\<Delta> extends \<Gamma>" by fact
  hence "X \<in> domain \<Delta>" using lh_drv_prem by (force dest: extends_domain)
  ultimately show "\<Delta> \<turnstile> TVar X <: TVar X" by force
next 
  case (S_Arrow \<Gamma> S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2) thus "\<Delta> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1 \<rightarrow> T\<^isub>2" by blast
next
  case (S_All \<Gamma> X S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2)
  have fresh_cond: "X\<sharp>\<Delta>" by fact
  have ih\<^isub>1: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  have ih\<^isub>2: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends ((X,T\<^isub>1)#\<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> S\<^isub>2 <: T\<^isub>2" by fact
  have lh_drv_prem: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  hence closed\<^isub>T\<^isub>1: "T\<^isub>1 closed_in \<Gamma>" by (simp add: subtype_implies_closed) 
  have ok: "\<turnstile> \<Delta> ok" by fact
  have ext: "\<Delta> extends \<Gamma>" by fact
  have "T\<^isub>1 closed_in \<Delta>" using ext closed\<^isub>T\<^isub>1 by (simp only: extends_closed)
  hence "\<turnstile> ((X,T\<^isub>1)#\<Delta>) ok" using fresh_cond ok by force   
  moreover 
  have "((X,T\<^isub>1)#\<Delta>) extends ((X,T\<^isub>1)#\<Gamma>)" using ext by (force simp add: extends_def)
  ultimately have "((X,T\<^isub>1)#\<Delta>) \<turnstile> S\<^isub>2 <: T\<^isub>2" using ih\<^isub>2 by simp
  moreover
  have "\<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" using ok ext ih\<^isub>1 by simp 
  ultimately show "\<Delta> \<turnstile> \<forall> [X<:S\<^isub>1].S\<^isub>2 <: \<forall> [X<:T\<^isub>1].T\<^isub>2" using ok by (force intro: S_All)
qed

text {* In fact all "non-binding" cases can be solved automatically: *}

lemma weakening:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and b: "\<turnstile> \<Delta> ok"
  and c: "\<Delta> extends \<Gamma>"
  shows "\<Delta> \<turnstile> S <: T"
  using a b c 
proof (nominal_induct \<Gamma> S T avoiding: \<Delta> rule: subtype_of_rel_induct)
  case (S_All \<Gamma> X S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2)
  have fresh_cond: "X\<sharp>\<Delta>" by fact
  have ih\<^isub>1: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  have ih\<^isub>2: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends ((X,T\<^isub>1)#\<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> S\<^isub>2 <: T\<^isub>2" by fact
  have lh_drv_prem: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  hence closed\<^isub>T\<^isub>1: "T\<^isub>1 closed_in \<Gamma>" by (simp add: subtype_implies_closed) 
  have ok: "\<turnstile> \<Delta> ok" by fact
  have ext: "\<Delta> extends \<Gamma>" by fact
  have "T\<^isub>1 closed_in \<Delta>" using ext closed\<^isub>T\<^isub>1 by (simp only: extends_closed)
  hence "\<turnstile> ((X,T\<^isub>1)#\<Delta>) ok" using fresh_cond ok by force   
  moreover 
  have "((X,T\<^isub>1)#\<Delta>) extends ((X,T\<^isub>1)#\<Gamma>)" using ext by (force simp add: extends_def)
  ultimately have "((X,T\<^isub>1)#\<Delta>) \<turnstile> S\<^isub>2 <: T\<^isub>2" using ih\<^isub>2 by simp
  moreover
  have "\<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" using ok ext ih\<^isub>1 by simp 
  ultimately show "\<Delta> \<turnstile> \<forall> [X<:S\<^isub>1].S\<^isub>2 <: \<forall> [X<:T\<^isub>1].T\<^isub>2" using ok by (force intro: S_All)
qed (blast intro: extends_closed extends_memb dest: extends_domain)+

text {* our contexts grow from right to left *}

lemma transitivity_and_narrowing:
  shows "\<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  and "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow> (\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> M <: N"
proof (induct Q fixing: \<Gamma> S T and \<Delta> \<Gamma> X P M N taking: "size_ty" rule: measure_induct_rule)
  case (less Q) 
  note IH_trans = prems[THEN conjunct1, rule_format]
  note IH_narrow = prems[THEN conjunct2, THEN spec, of _ "[]", simplified, rule_format]

    --{* The inner induction for transitivity over @{term "\<Gamma> \<turnstile> S <: Q"} *}
  have transitivity: 
    "\<And>\<Gamma> S T. \<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  proof - 
    
      -- {* We first handle the case where T = Top once and for all; this saves some 
      repeated argument below (just like on paper :-).  To do so we establish a little 
      lemma that is invoked where needed in the induction for transitivity. *} 
    have top_case: 
      "\<And>\<Gamma> S T' P. \<lbrakk>\<turnstile> \<Gamma> ok; S closed_in \<Gamma>; P \<Longrightarrow> \<Gamma> \<turnstile> S <: T'; T'=Top \<or> P\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T'"
    proof - 
      fix \<Gamma> S T' P
      assume S_Top_prm1: "S closed_in \<Gamma>"
	and  S_Top_prm2: "\<turnstile> \<Gamma> ok"
	and  alternative: "P \<Longrightarrow> \<Gamma> \<turnstile> S <: T'" 
	and  "T'=Top \<or> P" 
      moreover
      { assume "T'=Top"
	hence "\<Gamma> \<turnstile> S <: T'" using S_Top_prm1 S_Top_prm2 by (simp add: S_Top)
      } 
      moreover 
      { assume P 
	with alternative have "\<Gamma> \<turnstile> S <: T'" by simp 
      }
      ultimately show "\<Gamma> \<turnstile> S <: T'" by blast
    qed

	--{* Now proceed by the inner induction on the left-hand derivation *}
    fix \<Gamma>' S' T
    assume a: "\<Gamma>' \<turnstile> S' <: Q" --{* lh derivation *}
    assume b: "\<Gamma>' \<turnstile> Q <: T" --{* rh derivation *}
    from a b show "\<Gamma>' \<turnstile> S' <: T"
    proof(nominal_induct \<Gamma>' S' Q\<equiv>Q avoiding: \<Gamma>' S' T rule: subtype_of_rel_induct)
      case (S_Top \<Gamma> S) 
	--{* in this case lh drv is @{term "\<Gamma> \<turnstile> S <: Top"} *}
      hence rh_drv: "\<Gamma> \<turnstile> Top <: T" by simp
      hence T_inst: "T = Top" by (simp add: S_TopE)
      have lh_drv_prm1: "\<turnstile> \<Gamma> ok" by fact
      have lh_drv_prm2: "S closed_in \<Gamma>" by fact
      from lh_drv_prm1 lh_drv_prm2 have "\<Gamma> \<turnstile> S <: Top" by (simp add: subtype_of_rel.S_Top)
      thus "\<Gamma> \<turnstile> S <: T" using T_inst by simp
    next
      case (S_Var \<Gamma> Y U Q) 
	--{* in this case lh drv is @{term "\<Gamma> \<turnstile> TVar(Y) <: Q"} *}
      hence IH_inner: "\<Gamma> \<turnstile> U <: T" by simp
      have lh_drv_prm1: "\<turnstile> \<Gamma> ok" by fact
      have lh_drv_prm2: "(Y,U)\<in>set \<Gamma>" by fact
      from IH_inner show "\<Gamma> \<turnstile> TVar Y <: T" using lh_drv_prm1 lh_drv_prm2 
	by (simp add: subtype_of_rel.S_Var)
    next
      case (S_Refl \<Gamma> X) 
	--{* in this case lh drv is @{term "\<Gamma> \<turnstile> TVar X <: TVar X"} *}
      thus "\<Gamma> \<turnstile> TVar X <: T" by simp
    next
      case (S_Arrow \<Gamma> S1 S2 Q1 Q2) 
	--{* in this case lh drv is @{term "\<Gamma> \<turnstile> S1 \<rightarrow> S2 <: Q1 \<rightarrow> Q2"} *}
      hence rh_drv: "\<Gamma> \<turnstile> Q1 \<rightarrow> Q2 <: T" by simp
      have Q_inst: "Q1 \<rightarrow> Q2 = Q" by fact
      hence Q1_less: "size_ty Q1 < size_ty Q" 
	and Q2_less: "size_ty Q2 < size_ty Q" by auto
      have lh_drv_prm1: "\<Gamma> \<turnstile> Q1 <: S1" by fact
      have lh_drv_prm2: "\<Gamma> \<turnstile> S2 <: Q2" by fact      
      have "S1 closed_in \<Gamma>" and "S2 closed_in \<Gamma>" 
	using lh_drv_prm1 lh_drv_prm2 by (simp_all add: subtype_implies_closed)
      hence "(S1 \<rightarrow> S2) closed_in \<Gamma>" by (simp add: closed_in_def ty.supp)
      moreover
      have "\<turnstile> \<Gamma> ok" using rh_drv by (rule subtype_implies_ok)
      moreover
      from rh_drv have "T = Top \<or> (\<exists>T1 T2.  T = T1 \<rightarrow> T2 \<and> \<Gamma> \<turnstile> T1 <: Q1 \<and> \<Gamma> \<turnstile> Q2 <: T2)" 
	by (simp add: S_ArrowE_left)  
      moreover
      { assume "\<exists>T1 T2. T = T1 \<rightarrow> T2 \<and> \<Gamma> \<turnstile> T1 <: Q1 \<and> \<Gamma> \<turnstile> Q2 <: T2"
	then obtain T1 T2 
	  where T_inst: "T = T1 \<rightarrow> T2" 
	  and   rh_drv_prm1: "\<Gamma> \<turnstile> T1 <: Q1"
	  and   rh_drv_prm2: "\<Gamma> \<turnstile> Q2 <: T2" by force
        from IH_trans[of "Q1"] have "\<Gamma> \<turnstile> T1 <: S1" using Q1_less rh_drv_prm1 lh_drv_prm1 by simp 
	moreover
	from IH_trans[of "Q2"] have "\<Gamma> \<turnstile> S2 <: T2" using Q2_less rh_drv_prm2 lh_drv_prm2 by simp
	ultimately have "\<Gamma> \<turnstile> S1 \<rightarrow> S2 <: T1 \<rightarrow> T2" by (simp add: subtype_of_rel.S_Arrow)
	hence "\<Gamma> \<turnstile> S1 \<rightarrow> S2 <: T" using T_inst by simp
      }
      ultimately show "\<Gamma> \<turnstile> S1 \<rightarrow> S2 <: T" using top_case by blast
    next
      case (S_All \<Gamma> X S1 S2 Q1 Q2) 
	--{* in this case lh drv is @{term "\<Gamma>\<turnstile>\<forall>[X<:S1].S2 <: \<forall>[X<:Q1].Q2"} *}
      hence rh_drv: "\<Gamma> \<turnstile> \<forall>[X<:Q1].Q2 <: T" by simp
      have lh_drv_prm1: "\<Gamma> \<turnstile> Q1 <: S1" by fact
      have lh_drv_prm2: "((X,Q1)#\<Gamma>) \<turnstile> S2 <: Q2" by fact
      have fresh_cond: "X\<sharp>\<Gamma>" "X\<sharp>Q1" by fact
      have Q_inst: "\<forall>[X<:Q1].Q2 = Q" by fact
      hence Q1_less: "size_ty Q1 < size_ty Q" 
	and Q2_less: "size_ty Q2 < size_ty Q " by auto
      have "S1 closed_in \<Gamma>" and "S2 closed_in ((X,Q1)#\<Gamma>)" 
	using lh_drv_prm1 lh_drv_prm2 by (simp_all add: subtype_implies_closed)
      hence "(\<forall>[X<:S1].S2) closed_in \<Gamma>" by (force simp add: closed_in_def ty.supp abs_supp)
      moreover
      have "\<turnstile> \<Gamma> ok" using rh_drv by (rule subtype_implies_ok)
      moreover
      from rh_drv have "T = Top \<or> (\<exists>T1 T2. T = \<forall>[X<:T1].T2 \<and> \<Gamma> \<turnstile> T1 <: Q1 \<and> ((X,T1)#\<Gamma>) \<turnstile> Q2 <: T2)" 
	using fresh_cond by (simp add: S_AllE_left)
      moreover
      { assume "\<exists>T1 T2. T = \<forall>[X<:T1].T2 \<and> \<Gamma> \<turnstile> T1 <: Q1 \<and> ((X,T1)#\<Gamma>) \<turnstile> Q2 <: T2"
	then obtain T1 T2 
	  where T_inst: "T = \<forall>[X<:T1].T2" 
	  and   rh_drv_prm1: "\<Gamma> \<turnstile> T1 <: Q1" 
	  and   rh_drv_prm2:"((X,T1)#\<Gamma>) \<turnstile> Q2 <: T2" by force
        from IH_trans[of "Q1"] have "\<Gamma> \<turnstile> T1 <: S1" 
	  using lh_drv_prm1 rh_drv_prm1 Q1_less by blast
        moreover
	from IH_narrow[of "Q1"] have "((X,T1)#\<Gamma>) \<turnstile> S2 <: Q2" 
	  using Q1_less lh_drv_prm2 rh_drv_prm1 by blast
	with IH_trans[of "Q2"] have "((X,T1)#\<Gamma>) \<turnstile> S2 <: T2" 
	  using Q2_less rh_drv_prm2 by blast
        moreover
	ultimately have "\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: \<forall>[X<:T1].T2"
	  using fresh_cond by (simp add: subtype_of_rel.S_All)
	hence "\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: T" using T_inst by simp
      }
      ultimately show "\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: T" using top_case by blast
    qed
  qed

  --{* The inner induction for narrowing over @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> M <: N"} *}
  have narrowing:
    "\<And>\<Delta> \<Gamma> X M N P. (\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P<:Q \<Longrightarrow> (\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> M <: N"
  proof -
    fix \<Delta>' \<Gamma>' X M N P
    assume a: "(\<Delta>'@[(X,Q)]@\<Gamma>') \<turnstile> M <: N"
    assume b: "\<Gamma>' \<turnstile> P<:Q"
    from a b show "(\<Delta>'@[(X,P)]@\<Gamma>') \<turnstile> M <: N" 
    proof (nominal_induct \<Gamma>\<equiv>"\<Delta>'@[(X,Q)]@\<Gamma>'" M N avoiding: \<Delta>' \<Gamma>' X rule: subtype_of_rel_induct) 
      case (S_Top _ S \<Delta> \<Gamma> X)
	--{* in this case lh drv is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> S <: Top"} *}
      hence lh_drv_prm1: "\<turnstile> (\<Delta>@[(X,Q)]@\<Gamma>) ok" 
        and lh_drv_prm2: "S closed_in (\<Delta>@[(X,Q)]@\<Gamma>)" by simp_all
      have rh_drv: "\<Gamma> \<turnstile> P <: Q" by fact
      hence "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      with lh_drv_prm1 have "\<turnstile> (\<Delta>@[(X,P)]@\<Gamma>) ok" by (simp add: replace_type)
      moreover
      from lh_drv_prm2 have "S closed_in (\<Delta>@[(X,P)]@\<Gamma>)" by (simp add: closed_in_def domain_append)
      ultimately show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S <: Top" by (simp add: subtype_of_rel.S_Top)
    next
      case (S_Var _ Y S N \<Delta> \<Gamma> X) 
	--{* in this case lh drv is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> TVar Y <: N"} *}
      hence IH_inner: "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S <: N" 
	and lh_drv_prm1: "\<turnstile> (\<Delta>@[(X,Q)]@\<Gamma>) ok" 
        and lh_drv_prm2: "(Y,S)\<in>set (\<Delta>@[(X,Q)]@\<Gamma>)" by simp_all
      have rh_drv: "\<Gamma> \<turnstile> P <: Q" by fact
      hence "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      hence cntxt_ok: "\<turnstile> (\<Delta>@[(X,P)]@\<Gamma>) ok" using lh_drv_prm1 by (simp add: replace_type)
	-- {* we distinguishing the cases @{term "X\<noteq>Y"} and @{term "X=Y"} (the latter 
	being the interesting one) *}
      { assume "X\<noteq>Y"
	hence "(Y,S)\<in>set (\<Delta>@[(X,P)]@\<Gamma>)" using lh_drv_prm2 by simp
	with IH_inner have "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> TVar Y <: N" 
	  using cntxt_ok by (simp add: subtype_of_rel.S_Var)
      }
      moreover
      { have memb_XQ: "(X,Q)\<in>set (\<Delta>@[(X,Q)]@\<Gamma>)" by simp
	have memb_XP: "(X,P)\<in>set (\<Delta>@[(X,P)]@\<Gamma>)" by simp
	assume "X=Y" 
	hence "S=Q" using lh_drv_prm1 lh_drv_prm2 memb_XQ by (simp only: uniqueness_of_ctxt)
	hence "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Q <: N" using IH_inner by simp
	moreover
	have "(\<Delta>@[(X,P)]@\<Gamma>) extends \<Gamma>" by (simp add: extends_def)
	hence "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> P <: Q" using rh_drv cntxt_ok by (simp only: weakening)
	ultimately have "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> P <: N" using transitivity by simp
	hence "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> TVar X <: N" using memb_XP cntxt_ok 
	  by (simp only: subtype_of_rel.S_Var)
      }
      ultimately show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> TVar Y <: N" by blast
    next
      case (S_Refl _ Y \<Delta> \<Gamma> X)
	--{* in this case lh drv is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> TVar Y <: TVar Y"} *}
      hence lh_drv_prm1: "\<turnstile> (\<Delta>@[(X,Q)]@\<Gamma>) ok" 
	and lh_drv_prm2: "Y \<in> domain (\<Delta>@[(X,Q)]@\<Gamma>)" by simp_all
      have "\<Gamma> \<turnstile> P <: Q" by fact
      hence "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      with lh_drv_prm1 have "\<turnstile> (\<Delta>@[(X,P)]@\<Gamma>) ok" by (simp add: replace_type)
      moreover
      from lh_drv_prm2 have "Y \<in> domain (\<Delta>@[(X,P)]@\<Gamma>)" by (simp add: domain_append)
      ultimately show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> TVar Y <: TVar Y" by (simp add: subtype_of_rel.S_Refl)
    next
      case (S_Arrow _ Q1 Q2 S1 S2 \<Delta> \<Gamma> X) 
	--{* in this case lh drv is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> Q1 \<rightarrow> Q2 <: S1 \<rightarrow> S2"} *}
      thus "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Q1 \<rightarrow> Q2 <: S1 \<rightarrow> S2" by blast 
    next
      case (S_All _ Y S1 S2 T1 T2 \<Delta> \<Gamma> X)
	--{* in this case lh drv is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> \<forall>[Y<:S1].S2 <: \<forall>[Y<:T1].T2"} *}
      hence IH_inner1: "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> T1 <: S1" 
	and IH_inner2: "((Y,T1)#\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S2 <: T2" 
	and lh_drv_prm2: "Y\<sharp>(\<Delta>@[(X,Q)]@\<Gamma>)" by force+
      have rh_drv: "\<Gamma> \<turnstile> P <: Q" by fact
      hence "Y\<sharp>P" using lh_drv_prm2 by (simp only: fresh_list_append subtype_implies_fresh)
      hence "Y\<sharp>(\<Delta>@[(X,P)]@\<Gamma>)" using lh_drv_prm2 
	by (simp add: fresh_list_append fresh_list_cons fresh_prod)
      with IH_inner1 IH_inner2 
      show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> \<forall>[Y<:S1].S2 <: \<forall>[Y<:T1].T2" by (simp add: subtype_of_rel.S_All)
    qed
  qed
  from transitivity narrowing show ?case by blast 
qed




end