(* $Id$ *)

(*<*)
theory fsub
imports "../nominal" 
begin
(*>*)

text{* Authors: Christian Urban,
                Benjamin Pierce,
                Steve Zdancewic,
                Stephanie Weihrich and
                Dimitrios Vytiniotis,

       with great help from Stefan Berghofer and  Markus Wenzel. *}

section {* Types for Names, Nominal Datatype Declaration for Types and Terms *}

text {* The main point of this solution is to use names everywhere (be they bound, 
  binding or free). In System \FSUB{} there are two kinds of names corresponding to 
  type-variables and to term-variables. These two kinds of names are represented in 
  the nominal datatype package as atom-types @{text "tyvrs"} and @{text "vrs"}: *}

atom_decl tyvrs vrs

text{* There are numerous facts that come with this declaration: for example that 
  there are infinitely many elements in @{text "tyvrs"} and @{text "vrs"}. *}

text{* The constructors for types and terms in System \FSUB{} contain abstractions 
  over type-variables and term-variables. The nominal datatype-package uses 
  @{text "\<guillemotleft>\<dots>\<guillemotright>\<dots>"} to indicate where abstractions occur. *}

nominal_datatype ty = 
    Tvar   "tyvrs"
  | Top
  | Arrow  "ty" "ty"          ("_ \<rightarrow> _" [100,100] 100)
  | Forall "\<guillemotleft>tyvrs\<guillemotright>ty" "ty" 

nominal_datatype trm = 
    Var   "vrs"
  | Lam   "\<guillemotleft>vrs\<guillemotright>trm" "ty" 
  | Tabs  "\<guillemotleft>tyvrs\<guillemotright>trm" "ty"
  | App   "trm" "trm"
  | Tapp  "trm" "ty"

text {* To be polite to the eye, some more familiar notation is introduced. 
  Because of the change in the order of arguments, one needs to use 
  translation rules, instead of syntax annotations at the term-constructors
  as given for @{term "Arrow"}. *}

syntax
  Forall_syn :: "tyvrs \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" ("\<forall>[_<:_]._" [100,100,100] 100)
  Lam_syn    :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"   ("Lam [_:_]._" [100,100,100] 100)
  Tabs_syn   :: "tyvrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("Tabs [_<:_]._" [100,100,100] 100)

translations 
  "\<forall>[X<:T\<^isub>1].T\<^isub>2" \<rightleftharpoons> "ty.Forall X T\<^isub>2 T\<^isub>1"
  "Lam [x:T].t" \<rightleftharpoons> "trm.Lam x t T"
  "Tabs [X<:T].t" \<rightleftharpoons> "trm.Tabs X t T"

text {* Again there are numerous facts that are proved automatically for @{typ "ty"} 
  and @{typ "trm"}: for example that the set of free variables, i.e.~@{text "support"}, 
  is only finite. However note that nominal-datatype declarations do \emph{not} define 
  "classical" constructor-based datatypes, but rather define $\alpha$-equivalence 
  classes---we can for example show that $\alpha$-equivalent @{typ "ty"}s 
  and @{typ "trm"}s are equal: *}

lemma alpha_illustration:
  shows "\<forall>[X<:T].(Tvar X) = \<forall>[Y<:T].(Tvar Y)" 
  and "Lam [x:T].(Var x) = Lam [y:T].(Var y)"
  by (simp_all add: ty.inject trm.inject alpha calc_atm fresh_atm)

section {* SubTyping Contexts *}

types ty_context = "(tyvrs\<times>ty) list"

text {* Typing contexts are represented as lists "growing" on the left; we
  thereby deviating from the convention in the POPLmark-paper. The lists contain
  pairs of type-variables and types. *}

text {* In order to state valitity-conditions for typing-contexts, the notion of
  a @{text "domain"} of a typing-context is handy. *}

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
  shows "finite (domain \<Gamma>)"
  by (induct \<Gamma>, auto)

lemma domain_supp:
  shows "(supp (domain \<Gamma>)) = (domain \<Gamma>)"
  by (simp only: at_fin_set_supp at_tyvrs_inst finite_domain)

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

lemma fresh_domain_cons:
  fixes X::"tyvrs"
  shows "X\<sharp>(domain (Y#\<Gamma>)) = (X\<sharp>(fst Y) \<and> X\<sharp>(domain \<Gamma>))"
  by (simp add: fresh_fin_insert pt_tyvrs_inst at_tyvrs_inst fs_tyvrs_inst finite_domain)

lemma fresh_domain:
  fixes X::"tyvrs"
  assumes a: "X\<sharp>\<Gamma>" 
  shows "X\<sharp>(domain \<Gamma>)"
using a
apply(induct \<Gamma>)
apply(simp add: fresh_set_empty) 
apply(simp only: fresh_domain_cons)
apply(auto simp add: fresh_prod fresh_list_cons) 
done

text {* Not all lists of type @{typ "ty_context"} are well-formed. One condition
  requires that in @{term "(X,S)#\<Gamma>"} all free variables of @{term "S"} must be 
  in the @{term "domain"} of @{term "\<Gamma>"}, that is @{term "S"} must be @{text "closed"} 
  in @{term "\<Gamma>"}. The set of free variables of @{term "S"} is defined as the 
  @{text "support"} of @{term "S"}. *}

constdefs
  "closed_in" :: "ty \<Rightarrow> ty_context \<Rightarrow> bool" ("_ closed'_in _" [100,100] 100)
  "S closed_in \<Gamma> \<equiv> (supp S)\<subseteq>(domain \<Gamma>)"

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

text {* Now validity of a context is a straightforward inductive definition. *}
  
consts
  valid_rel :: "ty_context set" 
  valid_sym :: "ty_context \<Rightarrow> bool" ("\<turnstile> _ ok" [100] 100)
translations
  "\<turnstile> \<Gamma> ok" \<rightleftharpoons> "\<Gamma> \<in> valid_rel"  
inductive valid_rel
intros
valid_nil[simp]:  "\<turnstile> [] ok"
valid_cons[simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; X\<sharp>(domain \<Gamma>); T closed_in \<Gamma>\<rbrakk>  \<Longrightarrow>  \<turnstile> ((X,T)#\<Gamma>) ok"

lemma valid_eqvt:
  fixes pi::"tyvrs prm"
  assumes a: "\<turnstile> \<Gamma> ok" 
  shows "\<turnstile> (pi\<bullet>\<Gamma>) ok"
  using a
proof (induct)
  case valid_nil
  show "\<turnstile> (pi\<bullet>[]) ok" by simp
next
  case (valid_cons T X \<Gamma>)
  have "\<turnstile> (pi\<bullet>\<Gamma>) ok" by fact
  moreover
  have "X\<sharp>(domain \<Gamma>)" by fact
  hence "(pi\<bullet>X)\<sharp>(domain (pi\<bullet>\<Gamma>))" by (simp add: fresh_eqvt domain_eqvt[symmetric])
  moreover
  have "T closed_in \<Gamma>" by fact
  hence "(pi\<bullet>T) closed_in (pi\<bullet>\<Gamma>)" by (simp add: closed_in_eqvt)
  ultimately show "\<turnstile> (pi\<bullet>((X,T)#\<Gamma>)) ok" by simp
qed

lemma validE:
  assumes a: "\<turnstile> ((X,T)#\<Gamma>) ok"
  shows "\<turnstile> \<Gamma> ok \<and> X\<sharp>(domain \<Gamma>) \<and> T closed_in \<Gamma>"
using a by (cases, auto)

lemma validE_append:
  assumes a: "\<turnstile> (\<Delta>@\<Gamma>) ok" 
  shows "\<turnstile> \<Gamma> ok"
  using a by (induct \<Delta>, auto dest: validE)

lemma closed_in_fresh:
  fixes X::"tyvrs"
  assumes a: "S closed_in \<Gamma>"
  and     b: "X\<sharp>(domain \<Gamma>)" 
  and     c: "\<turnstile> \<Gamma> ok"
  shows "X\<sharp>S"
using a b c by (force simp add: fresh_def domain_supp closed_in_def)

lemma replace_type:
  assumes a: "\<turnstile> (\<Delta>@(X,T)#\<Gamma>) ok"
  and     b: "S closed_in \<Gamma>"
  shows "\<turnstile> (\<Delta>@(X,S)#\<Gamma>) ok"
using a b
apply(induct \<Delta>)
apply(auto dest!: validE intro!: valid_cons simp add: domain_append closed_in_def)
done

lemma uniqueness_of_ctxt:
  fixes \<Gamma>::"ty_context"
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "(X,T)\<in>set \<Gamma>"
  and     c: "(X,S)\<in>set \<Gamma>"
  shows "T=S"
using a b c
proof (induct)
  case valid_nil thus "T=S" by simp
next
  case (valid_cons U Y \<Gamma>)
  moreover
  { fix \<Gamma>::"ty_context"
    assume a: "X\<sharp>(domain \<Gamma>)" 
    have "\<not>(\<exists>T.(X,T)\<in>(set \<Gamma>))" using a 
    proof (induct \<Gamma>)
      case (Cons Y \<Gamma>)
      thus "\<not> (\<exists>T.(X,T)\<in>set(Y#\<Gamma>))" 
	by (simp only: fresh_domain_cons, auto simp add: fresh_atm)
    qed (simp)
  }
  ultimately show "T=S" by auto
qed 

section {* Size and Capture-Avoiding Substitutiuon for Types *}

text {* In the current version of the nominal datatype-package even simple 
  functions (such as size of types and capture-avoiding substitution) can 
  only be defined manually via some labourious proof constructions. Therefore 
  we sill just assume them here. *}

consts size_ty :: "ty \<Rightarrow> nat"

lemma size_ty[simp]:
  shows "size_ty (Tvar X) = 1"
  and   "size_ty (Top) = 1"
  and   "\<lbrakk>size_ty T\<^isub>1 = m; size_ty T\<^isub>2 = n\<rbrakk> \<Longrightarrow> size_ty (T\<^isub>1 \<rightarrow> T\<^isub>2) = m + n + 1"
  and   "\<lbrakk>size_ty T\<^isub>1 = m; size_ty T\<^isub>2 = n\<rbrakk> \<Longrightarrow> size_ty (\<forall>[X<:T\<^isub>1].T\<^isub>2) = m + n + 1"
sorry

consts subst_ty :: "ty \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> ty" ("_[_:=_]\<^isub>t\<^isub>y" [100,100,100] 100)

lemma subst_ty[simp]:
  shows "(Tvar X)[Y:=T]\<^isub>t\<^isub>y = (if X=Y then T else (Tvar X))"
  and   "(Top)[Y:=T]\<^isub>t\<^isub>y = Top"
  and   "(T\<^isub>1 \<rightarrow> T\<^isub>2)[Y:=T]\<^isub>t\<^isub>y = (T\<^isub>1[Y:=T]\<^isub>t\<^isub>y) \<rightarrow> (T\<^isub>2[Y:=T]\<^isub>t\<^isub>y)"
  and   "X\<sharp>(Y,T) \<Longrightarrow> (\<forall>[X<:T\<^isub>1].T\<^isub>2)[Y:=T]\<^isub>t\<^isub>y = (\<forall>[X<:(T\<^isub>1[Y:=T]\<^isub>t\<^isub>y)].(T\<^isub>2[Y:=T]\<^isub>t\<^isub>y))"
  and   "\<lbrakk>X\<sharp>Y; X\<sharp>T\<rbrakk> \<Longrightarrow> (\<forall>[X<:T\<^isub>1].T\<^isub>2)[Y:=T]\<^isub>t\<^isub>y = (\<forall>[X<:(T\<^isub>1[Y:=T]\<^isub>t\<^isub>y)].(T\<^isub>2[Y:=T]\<^isub>t\<^isub>y))"
sorry

consts subst_tyc :: "ty_context \<Rightarrow> tyvrs \<Rightarrow> ty \<Rightarrow> ty_context" ("_[_:=_]\<^isub>t\<^isub>y\<^isub>c" [100,100,100] 100)
primrec
"([])[Y:=T]\<^isub>t\<^isub>y\<^isub>c= []"
"(XT#\<Gamma>)[Y:=T]\<^isub>t\<^isub>y\<^isub>c = (fst XT,(snd XT)[Y:=T]\<^isub>t\<^isub>y)#(\<Gamma>[Y:=T]\<^isub>t\<^isub>y\<^isub>c)"
 
section {* Subtyping-Relation *}

consts
  subtype_of :: "(ty_context \<times> ty \<times> ty) set"   
syntax 
  subtype_of_syn :: "ty_context \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"   ("_\<turnstile>_<:_" [100,100,100] 100)

translations
  "\<Gamma> \<turnstile> S <: T" \<rightleftharpoons> "(\<Gamma>,S,T) \<in> subtype_of"
inductive subtype_of
intros
S_Top[intro]:    "\<lbrakk>\<turnstile> \<Gamma> ok; S closed_in \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
S_Var[intro]:    "\<lbrakk>(X,S) \<in> set \<Gamma>; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Tvar X) <: T"
S_Refl[intro]:   "\<lbrakk>\<turnstile> \<Gamma> ok; X \<in> domain \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Tvar X <: Tvar X"
S_Arrow[intro]:  "\<lbrakk>\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1; \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (S\<^isub>1 \<rightarrow> S\<^isub>2) <: (T\<^isub>1 \<rightarrow> T\<^isub>2)" 
S_Forall[intro]: "\<lbrakk>\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1; X\<sharp>\<Gamma>; ((X,T\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: T\<^isub>2\<rbrakk> 
                 \<Longrightarrow> \<Gamma> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: \<forall>[X<:T\<^isub>1].T\<^isub>2"  

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
  hence "(Tvar X) closed_in \<Gamma>" by (simp add: closed_in_def ty.supp supp_atm)
  moreover
  have "S closed_in \<Gamma> \<and> T closed_in \<Gamma>" by fact
  hence "T closed_in \<Gamma>" by force
  ultimately show "(Tvar X) closed_in \<Gamma> \<and> T closed_in \<Gamma>" by simp
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
  with a2 have "X\<sharp>domain(\<Gamma>)" by (simp add: fresh_domain)
  moreover
  from a1 have "S closed_in \<Gamma> \<and> T closed_in \<Gamma>" by (rule subtype_implies_closed)
  hence "supp S \<subseteq> ((supp (domain \<Gamma>))::tyvrs set)" 
    and "supp T \<subseteq> ((supp (domain \<Gamma>))::tyvrs set)" by (simp_all add: domain_supp closed_in_def)
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
apply(erule subtype_of.induct)
apply(force intro: valid_eqvt closed_in_eqvt)
apply(force intro: closed_in_eqvt valid_eqvt silly_eqvt1)
apply(force intro: valid_eqvt silly_eqvt2)
apply(force)
apply(force intro!: S_Forall simp add: fresh_prod fresh_eqvt)
done

lemma subtype_of_induct[consumes 1, case_names S_Top S_Var S_Refl S_Arrow S_Forall]:
  fixes  P :: "'a::fs_tyvrs\<Rightarrow>ty_context \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow>bool"
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and a1: "\<And>\<Gamma> S x. \<lbrakk>\<turnstile> \<Gamma> ok; S closed_in \<Gamma>\<rbrakk> \<Longrightarrow> P x \<Gamma> S Top"
  and a2: "\<And>\<Gamma> X S T x. \<lbrakk>(X,S)\<in>set \<Gamma>; \<Gamma> \<turnstile> S <: T; \<And>z. P z \<Gamma> S T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Tvar X) T"
  and a3: "\<And>\<Gamma> X x. \<lbrakk>\<turnstile> \<Gamma> ok; X\<in>domain \<Gamma>\<rbrakk> \<Longrightarrow> P x \<Gamma> (Tvar X) (Tvar X)"  
  and a4: "\<And>\<Gamma> S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2 x. \<lbrakk>\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1; \<And>z. P z \<Gamma> T\<^isub>1 S\<^isub>1; \<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2; \<And>z. P z \<Gamma> S\<^isub>2 T\<^isub>2\<rbrakk> 
  \<Longrightarrow> P x \<Gamma> (S\<^isub>1 \<rightarrow> S\<^isub>2) (T\<^isub>1 \<rightarrow> T\<^isub>2)"
  and a5: "\<And>\<Gamma> X S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2 x. 
  \<lbrakk>X\<sharp>x; X\<sharp>(\<Gamma>,S\<^isub>1,T\<^isub>1); \<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1; \<And>z. P z \<Gamma> T\<^isub>1 S\<^isub>1; ((X,T\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: T\<^isub>2; \<And>z. P z ((X,T\<^isub>1)#\<Gamma>) S\<^isub>2 T\<^isub>2\<rbrakk>
  \<Longrightarrow> P x \<Gamma> (\<forall>[X<:S\<^isub>1].S\<^isub>2) (\<forall>[X<:T\<^isub>1].T\<^isub>2)"
  shows "P x \<Gamma> S T"
proof -
  from a have "\<And>(pi::tyvrs prm) (x::'a::fs_tyvrs). P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>T)"
  proof (induct)
    case (S_Top S \<Gamma>) 
    thus "P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>Top)" by (force intro: valid_eqvt closed_in_eqvt a1)
  next
    case (S_Var S T X \<Gamma>)
    have "(X,S) \<in> set \<Gamma>" by fact
    hence "pi\<bullet>(X,S)\<in>pi\<bullet>(set \<Gamma>)" by (rule pt_set_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence "(pi\<bullet>X,pi\<bullet>S)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: pt_list_set_pi[OF pt_tyvrs_inst])
    moreover
    have "\<Gamma> \<turnstile> S <: T" by fact
    hence "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>S) <: (pi\<bullet>T)" by (rule subtype_eqvt)
    moreover
    have  "\<And>(pi::tyvrs prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>T)" by fact
    hence "\<And>x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>S) (pi\<bullet>T)" by simp
    ultimately 
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Tvar X)) (pi\<bullet>T)" by (simp add: a2)
  next
    case (S_Refl X \<Gamma>)
    have "\<turnstile> \<Gamma> ok" by fact
    hence "\<turnstile> (pi\<bullet>\<Gamma>) ok" by (rule valid_eqvt)
    moreover
    have "X \<in> domain \<Gamma>" by fact
    hence "(pi\<bullet>X)\<in>pi\<bullet>domain \<Gamma>" by (rule pt_set_bij2[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence "(pi\<bullet>X)\<in>domain (pi\<bullet>\<Gamma>)" by (simp add: domain_eqvt pt_list_set_pi[OF pt_tyvrs_inst])
    ultimately show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Tvar X)) (pi\<bullet>(Tvar X))" by (simp add: a3)
  next
    case S_Arrow thus ?case by (auto intro: a4 subtype_eqvt)
  next
    case (S_Forall S1 S2 T1 T2 X \<Gamma>)
    have b1: "\<Gamma> \<turnstile> T1 <: S1" by fact 
    have b2: "\<And>(pi::tyvrs prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>T1) (pi\<bullet>S1)" by fact
    have b4: "((X,T1)#\<Gamma>) \<turnstile> S2 <: T2" by fact
    have b5: "\<And>(pi::tyvrs prm) x. P x (pi\<bullet>((X,T1)#\<Gamma>)) (pi\<bullet>S2) (pi\<bullet>T2)" by fact
    have b3: "X\<sharp>\<Gamma>" by fact
    have b3': "X\<sharp>T1" "X\<sharp>S1" using b1 b3 by (simp_all add: subtype_implies_fresh)
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
    from b3' have "(pi\<bullet>X)\<sharp>(pi\<bullet>S1)" 
      by (simp add: fresh_prod pt_fresh_bij[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    with f2 have f2a: "?pi'\<bullet>S1=pi\<bullet>S1" 
      by (simp only: pt_tyvrs2 pt_fresh_fresh[OF pt_tyvrs_inst, OF at_tyvrs_inst])
    hence f2': "C\<sharp>(?pi'\<bullet>S1)" using f2 by simp
    from b3' have "(pi\<bullet>X)\<sharp>(pi\<bullet>T1)" 
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
    have main: "P x (?pi'\<bullet>\<Gamma>) (\<forall>[C<:(?pi'\<bullet>S1)].(?pi'\<bullet>S2)) (\<forall>[C<:(?pi'\<bullet>T1)].(?pi'\<bullet>T2))"
      using f7 fnew e1 c1 e2 c2 by (rule a5)
    have alpha1: "(\<forall>[C<:(?pi'\<bullet>S1)].(?pi'\<bullet>S2)) = (pi\<bullet>(\<forall>[X<:S1].S2))"
      using f1 f4 f2a[symmetric] by (simp add: ty.inject alpha pt_tyvrs2[symmetric])
    have alpha2: "(\<forall>[C<:(?pi'\<bullet>T1)].(?pi'\<bullet>T2)) = (pi\<bullet>(\<forall>[X<:T1].T2))"
      using f1 f5 f3a[symmetric] by (simp add: ty.inject alpha pt_tyvrs2[symmetric])
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(\<forall>[X<:S1].S2)) (pi\<bullet>(\<forall>[X<:T1].T2))"
      using alpha1 alpha2 f6a main by simp  
  qed
  hence "P x (([]::tyvrs prm)\<bullet>\<Gamma>) (([]::tyvrs prm)\<bullet>S) (([]::tyvrs prm)\<bullet>T)" by blast
  thus ?thesis by simp
qed

section {* Reflexivity of Subtyping *}

lemma subtype_reflexivity:
  assumes a: "\<turnstile> \<Gamma> ok"
  and b: "T closed_in \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
using a b
proof(nominal_induct T avoiding: \<Gamma> rule: ty.induct_unsafe)
  case (Forall X T\<^isub>1 T\<^isub>2)
  have ih_T\<^isub>1: "\<And>\<Gamma>. \<turnstile> \<Gamma> ok \<Longrightarrow> T\<^isub>1 closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> T\<^isub>1 <: T\<^isub>1" by fact 
  have ih_T\<^isub>2: "\<And>\<Gamma>. \<turnstile> \<Gamma> ok \<Longrightarrow> T\<^isub>2 closed_in \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> T\<^isub>2 <: T\<^isub>2" by fact
  have fresh_cond: "X\<sharp>\<Gamma>" by fact
  hence fresh_domain: "X\<sharp>(domain \<Gamma>)" by (simp add: fresh_domain)
  have "(\<forall>[X<:T\<^isub>2].T\<^isub>1) closed_in \<Gamma>" by fact
  hence closed\<^isub>T\<^isub>2: "T\<^isub>2 closed_in \<Gamma>" and closed\<^isub>T\<^isub>1: "T\<^isub>1 closed_in ((X,T\<^isub>2)#\<Gamma>)" 
    by (auto simp add: closed_in_def ty.supp abs_supp)
  have ok: "\<turnstile> \<Gamma> ok" by fact  
  hence ok': "\<turnstile> ((X,T\<^isub>2)#\<Gamma>) ok" using closed\<^isub>T\<^isub>2 fresh_domain by simp
  have "\<Gamma> \<turnstile> T\<^isub>2 <: T\<^isub>2" using ih_T\<^isub>2 closed\<^isub>T\<^isub>2 ok by simp
  moreover
  have "((X,T\<^isub>2)#\<Gamma>) \<turnstile> T\<^isub>1 <: T\<^isub>1" using ih_T\<^isub>1 closed\<^isub>T\<^isub>1 ok' by simp
  ultimately show "\<Gamma> \<turnstile> \<forall>[X<:T\<^isub>2].T\<^isub>1 <: \<forall>[X<:T\<^isub>2].T\<^isub>1" using fresh_cond 
    by (simp add: subtype_of.S_Forall)
qed (auto simp add: closed_in_def ty.supp supp_atm)

lemma subtype_reflexivity_semiautomated:
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "T closed_in \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
using a b
apply(nominal_induct T avoiding: \<Gamma> rule: ty.induct_unsafe)
apply(auto simp add: ty.supp abs_supp closed_in_def supp_atm)
  --{* Too bad that this instantiation cannot be found automatically by
  \isakeyword{auto}; \isakeyword{blast} would find it if we had not used 
  the definition @{text "closed_in_def"}. *}
apply(drule_tac x="(tyvrs, ty2)#\<Gamma>" in meta_spec)
apply(force simp add: closed_in_def fresh_domain)
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

lemma S_ForallE_left:
  shows "\<lbrakk>\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: T; X\<sharp>\<Gamma>; X\<sharp>S1\<rbrakk>
         \<Longrightarrow> T = Top \<or> (\<exists>T1 T2. T = \<forall>[X<:T1].T2 \<and> \<Gamma> \<turnstile> T1 <: S1 \<and> ((X,T1)#\<Gamma>) \<turnstile> S2 <: T2)"
  apply(frule subtype_implies_ok)
  apply(ind_cases "\<Gamma> \<turnstile> \<forall>[X<:S1].S2 <: T")
  apply(auto simp add: ty.inject alpha)
  apply(rule_tac x="[(X,Xa)]\<bullet>T\<^isub>2" in exI)
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
  apply(drule_tac \<Gamma>="((Xa,T\<^isub>1)#\<Gamma>)" in  subtype_implies_closed)+
  apply(simp add: closed_in_def)
  apply(drule fresh_domain)+
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
  shows "X\<sharp>T[Y:=P]\<^isub>t\<^isub>y"
  using a
  apply (nominal_induct T avoiding : T Y P rule: ty.induct_unsafe)
  apply (auto simp add: fresh_prod abs_fresh)
  done

lemma subst_ctxt_fresh:
  fixes X::"tyvrs"
  assumes a: "X\<sharp>(\<Gamma>,P)"
  shows "X\<sharp>\<Gamma>[Y:=P]\<^isub>t\<^isub>y\<^isub>c"
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
  thm subtype_of_induct
  apply(rule subtype_of_induct[of "\<Delta>@(X,Q)#\<Gamma>" "S" "T" _ "P"])
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


apply (nominal_induct \<Delta> X Q \<Gamma> S T rule: subtype_of_induct)
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
proof (nominal_induct \<Gamma> S T avoiding: \<Delta> rule: subtype_of_induct)
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
  ultimately show "\<Delta> \<turnstile> Tvar X <: T" using ok by force
next
  case (S_Refl \<Gamma> X)
  have lh_drv_prem: "X \<in> domain \<Gamma>" by fact
  have "\<turnstile> \<Delta> ok" by fact
  moreover
  have "\<Delta> extends \<Gamma>" by fact
  hence "X \<in> domain \<Delta>" using lh_drv_prem by (force dest: extends_domain)
  ultimately show "\<Delta> \<turnstile> Tvar X <: Tvar X" by force
next 
  case (S_Arrow \<Gamma> S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2) thus "\<Delta> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1 \<rightarrow> T\<^isub>2" by blast
next
  case (S_Forall \<Gamma> X S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2)
  have fresh_cond: "X\<sharp>\<Delta>" by fact
  hence fresh_domain: "X\<sharp>(domain \<Delta>)" by (simp add: fresh_domain)
  have ih\<^isub>1: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  have ih\<^isub>2: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends ((X,T\<^isub>1)#\<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> S\<^isub>2 <: T\<^isub>2" by fact
  have lh_drv_prem: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  hence closed\<^isub>T\<^isub>1: "T\<^isub>1 closed_in \<Gamma>" by (simp add: subtype_implies_closed) 
  have ok: "\<turnstile> \<Delta> ok" by fact
  have ext: "\<Delta> extends \<Gamma>" by fact
  have "T\<^isub>1 closed_in \<Delta>" using ext closed\<^isub>T\<^isub>1 by (simp only: extends_closed)
  hence "\<turnstile> ((X,T\<^isub>1)#\<Delta>) ok" using fresh_domain ok by force   
  moreover 
  have "((X,T\<^isub>1)#\<Delta>) extends ((X,T\<^isub>1)#\<Gamma>)" using ext by (force simp add: extends_def)
  ultimately have "((X,T\<^isub>1)#\<Delta>) \<turnstile> S\<^isub>2 <: T\<^isub>2" using ih\<^isub>2 by simp
  moreover
  have "\<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" using ok ext ih\<^isub>1 by simp 
  ultimately show "\<Delta> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: \<forall>[X<:T\<^isub>1].T\<^isub>2" using ok by (force intro: S_Forall)
qed

text {* In fact all "non-binding" cases can be solved automatically: *}

lemma weakening_semiautomated:
  assumes a: "\<Gamma> \<turnstile> S <: T"
  and b: "\<turnstile> \<Delta> ok"
  and c: "\<Delta> extends \<Gamma>"
  shows "\<Delta> \<turnstile> S <: T"
  using a b c 
proof (nominal_induct \<Gamma> S T avoiding: \<Delta> rule: subtype_of_induct)
  case (S_Forall \<Gamma> X S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2)
  have fresh_cond: "X\<sharp>\<Delta>" by fact
  hence fresh_domain: "X\<sharp>(domain \<Delta>)" by (simp add: fresh_domain)
  have ih\<^isub>1: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  have ih\<^isub>2: "\<And>\<Delta>. \<turnstile> \<Delta> ok \<Longrightarrow> \<Delta> extends ((X,T\<^isub>1)#\<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> S\<^isub>2 <: T\<^isub>2" by fact
  have lh_drv_prem: "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1" by fact
  hence closed\<^isub>T\<^isub>1: "T\<^isub>1 closed_in \<Gamma>" by (simp add: subtype_implies_closed) 
  have ok: "\<turnstile> \<Delta> ok" by fact
  have ext: "\<Delta> extends \<Gamma>" by fact
  have "T\<^isub>1 closed_in \<Delta>" using ext closed\<^isub>T\<^isub>1 by (simp only: extends_closed)
  hence "\<turnstile> ((X,T\<^isub>1)#\<Delta>) ok" using fresh_domain ok by force   
  moreover 
  have "((X,T\<^isub>1)#\<Delta>) extends ((X,T\<^isub>1)#\<Gamma>)" using ext by (force simp add: extends_def)
  ultimately have "((X,T\<^isub>1)#\<Delta>) \<turnstile> S\<^isub>2 <: T\<^isub>2" using ih\<^isub>2 by simp
  moreover
  have "\<Delta> \<turnstile> T\<^isub>1 <: S\<^isub>1" using ok ext ih\<^isub>1 by simp 
  ultimately show "\<Delta> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: \<forall>[X<:T\<^isub>1].T\<^isub>2" using ok by (force intro: S_Forall)
qed (blast intro: extends_closed extends_memb dest: extends_domain)+

text {* Next we prove the transitivity and narrowing for the subtyping relation. 
The POPLmark-paper says the following:

\begin{lemma}[Transitivity and Narrowing] \
\begin{enumerate}
\item If @{term "\<Gamma> \<turnstile> S<:Q"} and @{term "\<Gamma> \<turnstile> Q<:T"}, then @{term "\<Gamma> \<turnstile> S<:T"}.
\item If @{text "\<Gamma>,X<:Q,\<Delta> \<turnstile> M<:N"} and @{term "\<Gamma> \<turnstile> P<:Q"} then @{text "\<Gamma>,X<:P,\<Delta> \<turnstile> M<:N"}.
\end{enumerate}
\end{lemma}

The two parts are proved simultaneously, by induction on the size
of @{term "Q"}.  The argument for part (2) assumes that part (1) has 
been established already for the @{term "Q"} in question; part (1) uses 
part (2) only for strictly smaller @{term "Q"}.

For the induction on the size of @{term "Q"}, we use the induction-rule 
@{text "measure_induct_rule"}:

\begin{center}
@{thm measure_induct_rule[of "size_ty",no_vars]}
\end{center}

It says in English: in order to show a property @{term "P a"} for all @{term "a"}, 
it requires to prove that for all @{term x} @{term "P x"} holds using the 
assumption that for all @{term y} whose size is strictly smaller than 
that of @{term x} the property @{term "P y"} holds. *}

lemma 
  shows trans: "\<Gamma>\<turnstile>S<:Q \<Longrightarrow> \<Gamma>\<turnstile>Q<:T \<Longrightarrow> \<Gamma>\<turnstile>S<:T" 
  and narrow: "(\<Delta>@[(X,Q)]@\<Gamma>)\<turnstile>M<:N \<Longrightarrow> \<Gamma>\<turnstile>P<:Q \<Longrightarrow> (\<Delta>@[(X,P)]@\<Gamma>)\<turnstile>M<:N"
proof (induct Q fixing: \<Gamma> S T \<Delta> X P M N taking: "size_ty" rule: measure_induct_rule)
  case (less Q)
    --{* \begin{minipage}[t]{0.9\textwidth}
    First we mention the induction hypotheses of the outer induction for later
    reference:\end{minipage}*}
  have IH_trans:  
    "\<And>Q' \<Gamma> S T. \<lbrakk>size_ty Q' < size_ty Q; \<Gamma>\<turnstile>S<:Q'; \<Gamma>\<turnstile>Q'<:T\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>S<:T" by fact
  have IH_narrow:
    "\<And>Q' \<Delta> \<Gamma> X M N P. \<lbrakk>size_ty Q' < size_ty Q; (\<Delta>@[(X,Q')]@\<Gamma>)\<turnstile>M<:N; \<Gamma>\<turnstile>P<:Q'\<rbrakk> 
    \<Longrightarrow> (\<Delta>@[(X,P)]@\<Gamma>)\<turnstile>M<:N" by fact
    --{* \begin{minipage}[t]{0.9\textwidth}
    We proceed with the transitivity proof as an auxiliary lemma, because it needs 
    to be referenced in the narrowing proof.\end{minipage}*}
  have transitivity_aux:
    "\<And>\<Gamma> S T. \<lbrakk>\<Gamma> \<turnstile> S <: Q; \<Gamma> \<turnstile> Q <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  proof - 
    fix \<Gamma>' S' T
    assume "\<Gamma>' \<turnstile> S' <: Q" --{* left-hand derivation *}
      and  "\<Gamma>' \<turnstile> Q <: T"  --{* right-hand derivation *}
    thus "\<Gamma>' \<turnstile> S' <: T"
    proof (nominal_induct \<Gamma>' S' Q\<equiv>Q avoiding: \<Gamma>' S' rule: subtype_of_induct) 
      case (S_Top \<Gamma> S) 
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "\<Gamma> \<turnstile> S <: Top"}, giving
	us @{term "\<turnstile> \<Gamma> ok"} and @{term "S closed_in \<Gamma>"}. This case is straightforward, 
	because the right-hand derivation must be of the form @{term "\<Gamma> \<turnstile> Top <: Top"} 
	giving us the equation @{term "T = Top"}.\end{minipage}*}
      hence rh_drv: "\<Gamma> \<turnstile> Top <: T" by simp
      hence T_inst: "T = Top" by (simp add: S_TopE)
      have "\<turnstile> \<Gamma> ok" 
	and "S closed_in \<Gamma>" by fact
      hence "\<Gamma> \<turnstile> S <: Top" by (simp add: subtype_of.S_Top)
      thus "\<Gamma> \<turnstile> S <: T" using T_inst by simp
    next
      case (S_Var \<Gamma> Y U) 
	-- {* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "\<Gamma> \<turnstile> Tvar Y <: Q"} 
	with @{term "S = Tvar Y"}. We have therefore @{term "(Y,U)"} 
	is in @{term "\<Gamma>"} and by inner induction hypothesis @{term "\<Gamma> \<turnstile> U <: T"}. 
	By @{text "S_Var"} follows @{term "\<Gamma> \<turnstile> Tvar Y <: T"}.\end{minipage}*}
      hence IH_inner: "\<Gamma> \<turnstile> U <: T" by simp
      have "(Y,U) \<in> set \<Gamma>" by fact
      with IH_inner show "\<Gamma> \<turnstile> Tvar Y <: T" by (simp add: subtype_of.S_Var)
    next
      case (S_Refl \<Gamma> X) 
	--{* \begin{minipage}[t]{0.9\textwidth}
        In this case the left-hand derivation is @{term "\<Gamma>\<turnstile>(Tvar X) <: (Tvar X)"} with
        @{term "Q=Tvar X"}. The goal then follows immediately from the right-hand 
	derivation.\end{minipage}*}
      thus "\<Gamma> \<turnstile> Tvar X <: T" by simp
    next
      case (S_Arrow \<Gamma> S\<^isub>1 S\<^isub>2 Q\<^isub>1 Q\<^isub>2) 
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: Q\<^isub>1 \<rightarrow> Q\<^isub>2"} with
        @{term "S\<^isub>1\<rightarrow>S\<^isub>2=S"} and @{term "Q\<^isub>1\<rightarrow>Q\<^isub>2=Q"}. We know that the @{text "size_ty"} of 
	@{term Q\<^isub>1} and @{term Q\<^isub>2} is smaller than that of @{term Q};
	so we can apply the outer induction hypotheses for @{term Q\<^isub>1} and @{term Q\<^isub>2}. 
	We also have the sub-derivations  @{term "\<Gamma>\<turnstile>Q\<^isub>1<:S\<^isub>1"} and @{term "\<Gamma>\<turnstile>S\<^isub>2<:Q\<^isub>2"}.
	The right-hand derivation is @{term "\<Gamma> \<turnstile> Q\<^isub>1 \<rightarrow> Q\<^isub>2 <: T"}. There exists types 
	@{text "T\<^isub>1,T\<^isub>2"} such that @{term "T=Top \<or> T=T\<^isub>1\<rightarrow>T\<^isub>2"}. The @{term "Top"}-case is 
	straightforward once we know @{term "(S\<^isub>1 \<rightarrow> S\<^isub>2) closed_in \<Gamma>"} and @{term "\<turnstile> \<Gamma> ok"}. 
	In the other case we have the sub-derivations @{term "\<Gamma>\<turnstile>T\<^isub>1<:Q\<^isub>1"} and @{term "\<Gamma>\<turnstile>Q\<^isub>2<:T\<^isub>2"}. 
	Using the outer induction hypothesis for transitivity we can derive @{term "\<Gamma>\<turnstile>T\<^isub>1<:S\<^isub>1"} 
	and @{term "\<Gamma>\<turnstile>S\<^isub>2<:T\<^isub>2"}. By rule @{text "S_Arrow"} follows @{term "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1 \<rightarrow> T\<^isub>2"},
	which is @{term "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>"}.\end{minipage}*}
      hence rh_drv: "\<Gamma> \<turnstile> Q\<^isub>1 \<rightarrow> Q\<^isub>2 <: T" by simp
      from `Q\<^isub>1 \<rightarrow> Q\<^isub>2 = Q` 
      have Q\<^isub>1\<^isub>2_less: "size_ty Q\<^isub>1 < size_ty Q" "size_ty Q\<^isub>2 < size_ty Q" by auto
      have lh_drv_prm\<^isub>1: "\<Gamma> \<turnstile> Q\<^isub>1 <: S\<^isub>1" by fact
      have lh_drv_prm\<^isub>2: "\<Gamma> \<turnstile> S\<^isub>2 <: Q\<^isub>2" by fact      
      from rh_drv have "T=Top \<or> (\<exists>T\<^isub>1 T\<^isub>2. T=T\<^isub>1\<rightarrow>T\<^isub>2 \<and> \<Gamma>\<turnstile>T\<^isub>1<:Q\<^isub>1 \<and> \<Gamma>\<turnstile>Q\<^isub>2<:T\<^isub>2)" 
	by (simp add: S_ArrowE_left)  
      moreover
      have "S\<^isub>1 closed_in \<Gamma>" and "S\<^isub>2 closed_in \<Gamma>" 
	using lh_drv_prm\<^isub>1 lh_drv_prm\<^isub>2 by (simp_all add: subtype_implies_closed)
      hence "(S\<^isub>1 \<rightarrow> S\<^isub>2) closed_in \<Gamma>" by (simp add: closed_in_def ty.supp)
      moreover
      have "\<turnstile> \<Gamma> ok" using rh_drv by (rule subtype_implies_ok)
      moreover
      { assume "\<exists>T\<^isub>1 T\<^isub>2. T=T\<^isub>1\<rightarrow>T\<^isub>2 \<and> \<Gamma>\<turnstile>T\<^isub>1<:Q\<^isub>1 \<and> \<Gamma>\<turnstile>Q\<^isub>2<:T\<^isub>2"
	then obtain T\<^isub>1 T\<^isub>2 
	  where T_inst: "T = T\<^isub>1 \<rightarrow> T\<^isub>2" 
	  and   rh_drv_prm\<^isub>1: "\<Gamma> \<turnstile> T\<^isub>1 <: Q\<^isub>1"
	  and   rh_drv_prm\<^isub>2: "\<Gamma> \<turnstile> Q\<^isub>2 <: T\<^isub>2" by force
	from IH_trans[of "Q\<^isub>1"] 
	have "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1" using Q\<^isub>1\<^isub>2_less rh_drv_prm\<^isub>1 lh_drv_prm\<^isub>1 by simp 
	moreover
	from IH_trans[of "Q\<^isub>2"] 
	have "\<Gamma> \<turnstile> S\<^isub>2 <: T\<^isub>2" using Q\<^isub>1\<^isub>2_less rh_drv_prm\<^isub>2 lh_drv_prm\<^isub>2 by simp
	ultimately have "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T\<^isub>1 \<rightarrow> T\<^isub>2" by (simp add: subtype_of.S_Arrow)
	hence "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T" using T_inst by simp
      }
      ultimately show "\<Gamma> \<turnstile> S\<^isub>1 \<rightarrow> S\<^isub>2 <: T" by blast
    next
      case (S_Forall \<Gamma> X S\<^isub>1 S\<^isub>2 Q\<^isub>1 Q\<^isub>2) 
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{text "\<Gamma>\<turnstile>\<forall>[X<:S\<^isub>1].S\<^isub>2 <: \<forall>[X<:Q\<^isub>1].Q\<^isub>2"} with 
	@{text "\<forall>[X<:S\<^isub>1].S\<^isub>2=S"} and @{text "\<forall>[X<:Q\<^isub>1].Q\<^isub>2=Q"}. We therefore have the sub-derivations  
	@{term "\<Gamma>\<turnstile>Q\<^isub>1<:S\<^isub>1"} and @{term "((X,Q\<^isub>1)#\<Gamma>)\<turnstile>S\<^isub>2<:Q\<^isub>2"}. Since @{term "X"} is a binder, we
	assume that it is sufficiently fresh; in particular we have the freshness conditions
	@{term "X\<sharp>\<Gamma>"} and @{term "X\<sharp>Q\<^isub>1"} (these assumptions are provided by the strong induction
	rule @{text "subtype_of_induct"}). We know that the @{text "size_ty"} of 
	@{term Q\<^isub>1} and @{term Q\<^isub>2} is smaller than that of @{term Q};
	so we can apply the outer induction hypotheses for @{term Q\<^isub>1} and @{term Q\<^isub>2}. 
	The right-hand derivation is @{text "\<Gamma> \<turnstile> \<forall>[X<:Q\<^isub>1].Q\<^isub>2 <: T"}. Since @{term "X\<sharp>\<Gamma>"} 
	and @{term "X\<sharp>Q\<^isub>1"} there exists types @{text "T\<^isub>1,T\<^isub>2"} such that 
	@{text "T=Top \<or> T=\<forall>[X<:T\<^isub>1].T\<^isub>2"}. The @{term "Top"}-case is straightforward once we know 
	@{text "(\<forall>[X<:S\<^isub>1].S\<^isub>2) closed_in \<Gamma>"} and @{term "\<turnstile> \<Gamma> ok"}. In the other case we have 
	the sub-derivations @{term "\<Gamma>\<turnstile>T\<^isub>1<:Q\<^isub>1"}. @{term "((X,T\<^isub>1)#\<Gamma>)\<turnstile>Q\<^isub>2<:T\<^isub>2"}. Using the outer 
	induction hypothesis for transitivity we can derive @{term "\<Gamma>\<turnstile>T\<^isub>1<:S\<^isub>1"}. From the outer 
	induction for narrowing we get @{term "((X,T\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: Q\<^isub>2"} and then using induction 
	again @{term "((X,T\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: T\<^isub>2"}. By rule @{text "S_Forall"} and the freshness 
	condition @{term "X\<sharp>\<Gamma>"} follows @{text "\<Gamma> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: \<forall>[X<:T\<^isub>1].T\<^isub>2"}.which is 
	@{text "\<Gamma> \<turnstile>  \<forall>[X<:S\<^isub>1].S\<^isub>2 <: T\<^isub>"}.\end{minipage}*}
      hence rh_drv: "\<Gamma> \<turnstile> \<forall>[X<:Q\<^isub>1].Q\<^isub>2 <: T" by simp
      have lh_drv_prm\<^isub>1: "\<Gamma> \<turnstile> Q\<^isub>1 <: S\<^isub>1" by fact
      have lh_drv_prm\<^isub>2: "((X,Q\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: Q\<^isub>2" by fact
      have fresh_cond: "X\<sharp>\<Gamma>" "X\<sharp>Q\<^isub>1" by fact
      from `\<forall>[X<:Q\<^isub>1].Q\<^isub>2 = Q` 
      have Q\<^isub>1\<^isub>2_less: "size_ty Q\<^isub>1 < size_ty Q" "size_ty Q\<^isub>2 < size_ty Q " by auto
      from rh_drv 
      have "T=Top \<or> (\<exists>T\<^isub>1 T\<^isub>2. T=\<forall>[X<:T\<^isub>1].T\<^isub>2 \<and> \<Gamma>\<turnstile>T\<^isub>1<:Q\<^isub>1 \<and> ((X,T\<^isub>1)#\<Gamma>)\<turnstile>Q\<^isub>2<:T\<^isub>2)" 
	using fresh_cond by (simp add: S_ForallE_left)
      moreover
      have "S\<^isub>1 closed_in \<Gamma>" and "S\<^isub>2 closed_in ((X,Q\<^isub>1)#\<Gamma>)" 
	using lh_drv_prm\<^isub>1 lh_drv_prm\<^isub>2 by (simp_all add: subtype_implies_closed)
      hence "(\<forall>[X<:S\<^isub>1].S\<^isub>2) closed_in \<Gamma>" by (force simp add: closed_in_def ty.supp abs_supp)
      moreover
      have "\<turnstile> \<Gamma> ok" using rh_drv by (rule subtype_implies_ok)
      moreover
      { assume "\<exists>T\<^isub>1 T\<^isub>2. T=\<forall>[X<:T\<^isub>1].T\<^isub>2 \<and> \<Gamma>\<turnstile>T\<^isub>1<:Q\<^isub>1 \<and> ((X,T\<^isub>1)#\<Gamma>)\<turnstile>Q\<^isub>2<:T\<^isub>2"
	then obtain T\<^isub>1 T\<^isub>2 
	  where T_inst: "T = \<forall>[X<:T\<^isub>1].T\<^isub>2" 
	  and   rh_drv_prm\<^isub>1: "\<Gamma> \<turnstile> T\<^isub>1 <: Q\<^isub>1" 
	  and   rh_drv_prm\<^isub>2:"((X,T\<^isub>1)#\<Gamma>) \<turnstile> Q\<^isub>2 <: T\<^isub>2" by force
	from IH_trans[of "Q\<^isub>1"] 
	have "\<Gamma> \<turnstile> T\<^isub>1 <: S\<^isub>1" using lh_drv_prm\<^isub>1 rh_drv_prm\<^isub>1 Q\<^isub>1\<^isub>2_less by blast
	moreover
	from IH_narrow[of "Q\<^isub>1" "[]"] 
	have "((X,T\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: Q\<^isub>2" using Q\<^isub>1\<^isub>2_less lh_drv_prm\<^isub>2 rh_drv_prm\<^isub>1 by simp
	with IH_trans[of "Q\<^isub>2"] 
	have "((X,T\<^isub>1)#\<Gamma>) \<turnstile> S\<^isub>2 <: T\<^isub>2" using Q\<^isub>1\<^isub>2_less rh_drv_prm\<^isub>2 by simp
	ultimately have "\<Gamma> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: \<forall>[X<:T\<^isub>1].T\<^isub>2"
	  using fresh_cond by (simp add: subtype_of.S_Forall)
	hence "\<Gamma> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: T" using T_inst by simp
      }
      ultimately show "\<Gamma> \<turnstile> \<forall>[X<:S\<^isub>1].S\<^isub>2 <: T" by blast
    qed
  qed

  { --{* The transitivity proof is now by the auxiliary lemma. *}
    case 1 
    have  "\<Gamma> \<turnstile> S <: Q" 
      and "\<Gamma> \<turnstile> Q <: T" by fact
    thus "\<Gamma> \<turnstile> S <: T" by (rule transitivity_aux) 
  next 
    --{* The narrowing proof proceeds by an induction over @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> M <: N"}. *}
    case 2
    have  "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> M <: N" --{* left-hand derivation *}
      and "\<Gamma> \<turnstile> P<:Q" by fact --{* right-hand derivation *}
    thus "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> M <: N" 
    proof (nominal_induct \<Gamma>\<equiv>"\<Delta>@[(X,Q)]@\<Gamma>" M N avoiding: \<Delta> \<Gamma> X rule: subtype_of_induct) 
      case (S_Top _ S \<Delta> \<Gamma> X)
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> S <: Top"}. We show
	that the context @{term "\<Delta>@[(X,P)]@\<Gamma>"} is ok and that @{term S} is closed in 
	@{term "\<Delta>@[(X,P)]@\<Gamma>"}. Then we can apply the @{text "S_Top"}-rule.\end{minipage}*}
      hence lh_drv_prm\<^isub>1: "\<turnstile> (\<Delta>@[(X,Q)]@\<Gamma>) ok" 
	and lh_drv_prm\<^isub>2: "S closed_in (\<Delta>@[(X,Q)]@\<Gamma>)" by simp_all
      have rh_drv: "\<Gamma> \<turnstile> P <: Q" by fact
      hence "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      with lh_drv_prm\<^isub>1 have "\<turnstile> (\<Delta>@[(X,P)]@\<Gamma>) ok" by (simp add: replace_type)
      moreover
      from lh_drv_prm\<^isub>2 have "S closed_in (\<Delta>@[(X,P)]@\<Gamma>)" 
	by (simp add: closed_in_def domain_append)
      ultimately show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S <: Top" by (simp add: subtype_of.S_Top)
    next
      case (S_Var _ Y S N \<Delta> \<Gamma> X) 
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> Tvar Y <: N"}. We therefore 
	know that the contexts @{term "\<Delta>@[(X,Q)]@\<Gamma>"} and @{term "\<Delta>@[(X,P)]@\<Gamma>"} are ok, and that 
	@{term "(Y,S)"} is in @{term "\<Delta>@[(X,Q)]@\<Gamma>"}. By inner induction hypothesis we have 
	@{term "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S <: N"}. We need to show that @{term "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Tvar Y <: N"} 
	holds. In case @{term "X\<noteq>Y"} we know that @{term "(Y,S)"} is in @{term "\<Delta>@[(X,P)]@\<Gamma>"} and 
	can use the inner induction hypothesis and rule @{text "S_Var"} to conclude. In case 
	@{term "X=Y"} we can infer that @{term "S=Q"}; moreover we have that 
	@{term "(\<Delta>@[(X,P)]@\<Gamma>) extends \<Gamma>"} and therefore by @{text "weakening"} that 
	@{term "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> P <: Q"} holds. By transitivity we obtain then 
	@{term "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> P <: N"} and can conclude by applying rule @{text "S_Var"}.
	\end{minipage}*}
      hence IH_inner: "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S <: N"
	and lh_drv_prm: "(Y,S) \<in> set (\<Delta>@[(X,Q)]@\<Gamma>)"
	and rh_drv: "\<Gamma> \<turnstile> P<:Q"
	and ok\<^isub>Q: "\<turnstile> (\<Delta>@[(X,Q)]@\<Gamma>) ok" by (simp_all add: subtype_implies_ok)
      hence ok\<^isub>P: "\<turnstile> (\<Delta>@[(X,P)]@\<Gamma>) ok" by (simp add: subtype_implies_ok) 
      show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Tvar Y <: N"
      proof (cases "X=Y")
	case False
	have "X\<noteq>Y" by fact
	hence "(Y,S)\<in>set (\<Delta>@[(X,P)]@\<Gamma>)" using lh_drv_prm by simp
	with IH_inner show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Tvar Y <: N" by (simp add: subtype_of.S_Var)
      next
	case True
	have memb\<^isub>X\<^isub>Q: "(X,Q)\<in>set (\<Delta>@[(X,Q)]@\<Gamma>)" by simp
	have memb\<^isub>X\<^isub>P: "(X,P)\<in>set (\<Delta>@[(X,P)]@\<Gamma>)" by simp
	have eq: "X=Y" by fact 
	hence "S=Q" using ok\<^isub>Q lh_drv_prm memb\<^isub>X\<^isub>Q by (simp only: uniqueness_of_ctxt)
	hence "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Q <: N" using IH_inner by simp
	moreover
	have "(\<Delta>@[(X,P)]@\<Gamma>) extends \<Gamma>" by (simp add: extends_def)
	hence "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> P <: Q" using rh_drv ok\<^isub>P by (simp only: weakening)
	ultimately have "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> P <: N" by (simp add: transitivity_aux) 
	thus "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Tvar Y <: N" using memb\<^isub>X\<^isub>P eq by (simp only: subtype_of.S_Var)
      qed
    next
      case (S_Refl _ Y \<Delta> \<Gamma> X)
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> Tvar Y <: Tvar Y"} and we
	therefore know that @{term "\<Delta>@[(X,Q)]@\<Gamma>"} is ok and thad @{term "Y"} is in 
	the domain of @{term "\<Delta>@[(X,Q)]@\<Gamma>"}. We therefore know that @{term "\<Delta>@[(X,P)]@\<Gamma>"} is ok
	and that @{term Y} is in the domain of @{term "\<Delta>@[(X,P)]@\<Gamma>"}. We can conclude by applying 
	rule @{text "S_Refl"}.\end{minipage}*}
      hence lh_drv_prm\<^isub>1: "\<turnstile> (\<Delta>@[(X,Q)]@\<Gamma>) ok" 
	and lh_drv_prm\<^isub>2: "Y \<in> domain (\<Delta>@[(X,Q)]@\<Gamma>)" by simp_all
      have "\<Gamma> \<turnstile> P <: Q" by fact
      hence "P closed_in \<Gamma>" by (simp add: subtype_implies_closed)
      with lh_drv_prm\<^isub>1 have "\<turnstile> (\<Delta>@[(X,P)]@\<Gamma>) ok" by (simp add: replace_type)
      moreover
      from lh_drv_prm\<^isub>2 have "Y \<in> domain (\<Delta>@[(X,P)]@\<Gamma>)" by (simp add: domain_append)
      ultimately show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Tvar Y <: Tvar Y" by (simp add: subtype_of.S_Refl)
    next
      case (S_Arrow _ Q\<^isub>1 Q\<^isub>2 S\<^isub>1 S\<^isub>2 \<Delta> \<Gamma> X) 
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case the left-hand derivation is @{term "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> Q\<^isub>1 \<rightarrow> Q\<^isub>2 <: S\<^isub>1 \<rightarrow> S\<^isub>2"} 
	and the proof is trivial.\end{minipage}*}
      thus "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> Q\<^isub>1 \<rightarrow> Q\<^isub>2 <: S\<^isub>1 \<rightarrow> S\<^isub>2" by blast 
    next
      case (S_Forall _ Y S\<^isub>1 S\<^isub>2 T\<^isub>1 T\<^isub>2 \<Delta> \<Gamma> X)
	--{* \begin{minipage}[t]{0.9\textwidth}
	In this case teh left-hand derivation is @{text "(\<Delta>@[(X,Q)]@\<Gamma>) \<turnstile> \<forall>[Y<:S\<^isub>1].S\<^isub>2 <: \<forall>[Y<:T\<^isub>1].T\<^isub>2"}
	and therfore we know that the binder @{term Y} is fresh for @{term "\<Delta>@[(X,Q)]@\<Gamma>"}. By
	the inner induction hypothesis we have that @{term "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> T\<^isub>1 <: S\<^isub>1"} and 
	@{term "((Y,T\<^isub>1)#\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S\<^isub>2 <: T\<^isub>2"}. Since @{term P} is a subtype of @{term Q}
	we can infer that @{term Y} is fresh for @{term P} and thus also fresh for 
	@{term "\<Delta>@[(X,P)]@\<Gamma>"}. We can then conclude by applying rule @{text "S_Forall"}.
	\end{minipage}*}
      hence IH_inner\<^isub>1: "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> T\<^isub>1 <: S\<^isub>1" 
	and IH_inner\<^isub>2: "((Y,T\<^isub>1)#\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> S\<^isub>2 <: T\<^isub>2" 
	and lh_drv_prm: "Y\<sharp>(\<Delta>@[(X,Q)]@\<Gamma>)" by force+
      have rh_drv: "\<Gamma> \<turnstile> P <: Q" by fact
      hence "Y\<sharp>P" using lh_drv_prm by (simp only: fresh_list_append subtype_implies_fresh)
      hence "Y\<sharp>(\<Delta>@[(X,P)]@\<Gamma>)" using lh_drv_prm 
	by (simp add: fresh_list_append fresh_list_cons fresh_prod)
      with IH_inner\<^isub>1 IH_inner\<^isub>2 
      show "(\<Delta>@[(X,P)]@\<Gamma>) \<turnstile> \<forall>[Y<:S\<^isub>1].S\<^isub>2 <: \<forall>[Y<:T\<^isub>1].T\<^isub>2" by (simp add: subtype_of.S_Forall)
    qed
  } 
qed


end