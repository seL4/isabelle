theory SN
  imports Lam_Funs
begin

text {* Strong Normalisation proof from the Proofs and Types book *}

section {* Beta Reduction *}

lemma subst_rename: 
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
using a
by (nominal_induct t1 avoiding: a c t2 rule: lam.strong_induct)
   (auto simp add: calc_atm fresh_atm abs_fresh)

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
by (nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1" "a\<sharp>t2"
  shows "a\<sharp>t1[b::=t2]"
using a
by (nominal_induct t1 avoiding: a b t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact': 
  fixes a::"name"
  assumes a: "a\<sharp>t2"
  shows "a\<sharp>t1[a::=t2]"
using a 
by (nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma subst_lemma:  
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
by (nominal_induct M avoiding: x y N L rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

lemma id_subs: 
  shows "t[x::=Var x] = t"
  by (nominal_induct t avoiding: x rule: lam.strong_induct)
     (simp_all add: fresh_atm)

lemma lookup_fresh:
  fixes z::"name"
  assumes "z\<sharp>\<theta>" "z\<sharp>x"
  shows "z\<sharp> lookup \<theta> x"
using assms 
by (induct rule: lookup.induct) (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using assms 
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

lemma psubst_subst:
  assumes h:"c\<sharp>\<theta>"
  shows "(\<theta><t>)[c::=s] = ((c,s)#\<theta>)<t>"
  using h
by (nominal_induct t avoiding: \<theta> c s rule: lam.strong_induct)
   (auto simp add: fresh_list_cons fresh_atm forget lookup_fresh lookup_fresh')
 
inductive 
  Beta :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
where
  b1[intro!]: "s1 \<longrightarrow>\<^isub>\<beta> s2 \<Longrightarrow> App s1 t \<longrightarrow>\<^isub>\<beta> App s2 t"
| b2[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> App t s1 \<longrightarrow>\<^isub>\<beta> App t s2"
| b3[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> Lam [a].s1 \<longrightarrow>\<^isub>\<beta> Lam [a].s2"
| b4[intro!]: "a\<sharp>s2 \<Longrightarrow> App (Lam [a].s1) s2\<longrightarrow>\<^isub>\<beta> (s1[a::=s2])"

equivariance Beta

nominal_inductive Beta
  by (simp_all add: abs_fresh fresh_fact')

lemma beta_preserves_fresh: 
  fixes a::"name"
  assumes a: "t\<longrightarrow>\<^isub>\<beta> s"
  shows "a\<sharp>t \<Longrightarrow> a\<sharp>s"
using a
apply(nominal_induct t s avoiding: a rule: Beta.strong_induct)
apply(auto simp add: abs_fresh fresh_fact fresh_atm)
done

lemma beta_abs: 
  assumes a: "Lam [a].t\<longrightarrow>\<^isub>\<beta> t'" 
  shows "\<exists>t''. t'=Lam [a].t'' \<and> t\<longrightarrow>\<^isub>\<beta> t''"
proof -
  have "a\<sharp>Lam [a].t" by (simp add: abs_fresh)
  with a have "a\<sharp>t'" by (simp add: beta_preserves_fresh)
  with a show ?thesis
    by (cases rule: Beta.strong_cases[where a="a" and aa="a"])
       (auto simp add: lam.inject abs_fresh alpha)
qed

lemma beta_subst: 
  assumes a: "M \<longrightarrow>\<^isub>\<beta> M'"
  shows "M[x::=N]\<longrightarrow>\<^isub>\<beta> M'[x::=N]" 
using a
by (nominal_induct M M' avoiding: x N rule: Beta.strong_induct)
   (auto simp add: fresh_atm subst_lemma fresh_fact)

section {* types *}

nominal_datatype ty =
    TVar "nat"
  | TArr "ty" "ty" (infix "\<rightarrow>" 200)

lemma fresh_ty:
  fixes a ::"name"
  and   \<tau>  ::"ty"
  shows "a\<sharp>\<tau>"
by (nominal_induct \<tau> rule: ty.strong_induct)
   (auto simp add: fresh_nat)

(* valid contexts *)

inductive 
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
  v1[intro]: "valid []"
| v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

equivariance valid 

(* typing judgements *)

lemma fresh_context: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    a :: "name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using a
by (induct \<Gamma>)
   (auto simp add: fresh_prod fresh_list_cons fresh_atm)

inductive 
  typing :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60)
where
  t1[intro]: "\<lbrakk>valid \<Gamma>; (a,\<tau>)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var a : \<tau>"
| t2[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>; \<Gamma> \<turnstile> t2 : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : \<sigma>"
| t3[intro]: "\<lbrakk>a\<sharp>\<Gamma>;((a,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [a].t : \<tau>\<rightarrow>\<sigma>"

equivariance typing

nominal_inductive typing
  by (simp_all add: abs_fresh fresh_ty)

subsection {* a fact about beta *}

constdefs
  "NORMAL" :: "lam \<Rightarrow> bool"
  "NORMAL t \<equiv> \<not>(\<exists>t'. t\<longrightarrow>\<^isub>\<beta> t')"

lemma NORMAL_Var:
  shows "NORMAL (Var a)"
proof -
  { assume "\<exists>t'. (Var a) \<longrightarrow>\<^isub>\<beta> t'"
    then obtain t' where "(Var a) \<longrightarrow>\<^isub>\<beta> t'" by blast
    hence False by (cases) (auto) 
  }
  thus "NORMAL (Var a)" by (auto simp add: NORMAL_def)
qed

text {* Inductive version of Strong Normalisation *}
inductive 
  SN :: "lam \<Rightarrow> bool"
where
  SN_intro: "(\<And>t'. t \<longrightarrow>\<^isub>\<beta> t' \<Longrightarrow> SN t') \<Longrightarrow> SN t"

lemma SN_preserved: 
  assumes a: "SN t1" "t1\<longrightarrow>\<^isub>\<beta> t2"
  shows "SN t2"
using a 
by (cases) (auto)

lemma double_SN_aux:
  assumes a: "SN a"
  and b: "SN b"
  and hyp: "\<And>x z.
    \<lbrakk>\<And>y. x \<longrightarrow>\<^isub>\<beta> y \<Longrightarrow> SN y; \<And>y. x \<longrightarrow>\<^isub>\<beta> y \<Longrightarrow> P y z;
     \<And>u. z \<longrightarrow>\<^isub>\<beta> u \<Longrightarrow> SN u; \<And>u. z \<longrightarrow>\<^isub>\<beta> u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a
  have r: "\<And>b. SN b \<Longrightarrow> P a b"
  proof (induct a rule: SN.SN.induct)
    case (SN_intro x)
    note SNI' = SN_intro
    have "SN b" by fact
    thus ?case
    proof (induct b rule: SN.SN.induct)
      case (SN_intro y)
      show ?case
        apply (rule hyp)
        apply (erule SNI')
        apply (erule SNI')
        apply (rule SN.SN_intro)
        apply (erule SN_intro)+
        done
    qed
  qed
  from b show ?thesis by (rule r)
qed

lemma double_SN[consumes 2]:
  assumes a: "SN a"
  and     b: "SN b" 
  and     c: "\<And>x z. \<lbrakk>\<And>y. x \<longrightarrow>\<^isub>\<beta> y \<Longrightarrow> P y z; \<And>u. z \<longrightarrow>\<^isub>\<beta> u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
using a b c
apply(rule_tac double_SN_aux)
apply(assumption)+
apply(blast)
done

section {* Candidates *}

nominal_primrec
  RED :: "ty \<Rightarrow> lam set"
where
  "RED (TVar X) = {t. SN(t)}"
| "RED (\<tau>\<rightarrow>\<sigma>) =   {t. \<forall>u. (u\<in>RED \<tau> \<longrightarrow> (App t u)\<in>RED \<sigma>)}"
by (rule TrueI)+

text {* neutral terms *}
constdefs
  NEUT :: "lam \<Rightarrow> bool"
  "NEUT t \<equiv> (\<exists>a. t = Var a) \<or> (\<exists>t1 t2. t = App t1 t2)" 

(* a slight hack to get the first element of applications *)
(* this is needed to get (SN t) from SN (App t s)         *) 
inductive 
  FST :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<guillemotright> _" [80,80] 80)
where
  fst[intro!]:  "(App t s) \<guillemotright> t"

nominal_primrec
  fst_app_aux::"lam\<Rightarrow>lam option"
where
  "fst_app_aux (Var a)     = None"
| "fst_app_aux (App t1 t2) = Some t1"
| "fst_app_aux (Lam [x].t) = None"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: fresh_none)
apply(fresh_guess)+
done

definition
  fst_app_def[simp]: "fst_app t = the (fst_app_aux t)"

lemma SN_of_FST_of_App: 
  assumes a: "SN (App t s)"
  shows "SN (fst_app (App t s))"
using a
proof - 
  from a have "\<forall>z. (App t s \<guillemotright> z) \<longrightarrow> SN z"
    by (induct rule: SN.SN.induct)
       (blast elim: FST.cases intro: SN_intro)
  then have "SN t" by blast
  then show "SN (fst_app (App t s))" by simp
qed

section {* Candidates *}

constdefs
  "CR1" :: "ty \<Rightarrow> bool"
  "CR1 \<tau> \<equiv> \<forall>t. (t\<in>RED \<tau> \<longrightarrow> SN t)"

  "CR2" :: "ty \<Rightarrow> bool"
  "CR2 \<tau> \<equiv> \<forall>t t'. (t\<in>RED \<tau> \<and> t \<longrightarrow>\<^isub>\<beta> t') \<longrightarrow> t'\<in>RED \<tau>"

  "CR3_RED" :: "lam \<Rightarrow> ty \<Rightarrow> bool"
  "CR3_RED t \<tau> \<equiv> \<forall>t'. t\<longrightarrow>\<^isub>\<beta> t' \<longrightarrow>  t'\<in>RED \<tau>" 

  "CR3" :: "ty \<Rightarrow> bool"
  "CR3 \<tau> \<equiv> \<forall>t. (NEUT t \<and> CR3_RED t \<tau>) \<longrightarrow> t\<in>RED \<tau>"
   
  "CR4" :: "ty \<Rightarrow> bool"
  "CR4 \<tau> \<equiv> \<forall>t. (NEUT t \<and> NORMAL t) \<longrightarrow>t\<in>RED \<tau>"

lemma CR3_implies_CR4: 
  assumes a: "CR3 \<tau>" 
  shows "CR4 \<tau>"
using a by (auto simp add: CR3_def CR3_RED_def CR4_def NORMAL_def)

(* sub_induction in the arrow-type case for the next proof *) 
lemma sub_induction: 
  assumes a: "SN(u)"
  and     b: "u\<in>RED \<tau>"
  and     c1: "NEUT t"
  and     c2: "CR2 \<tau>"
  and     c3: "CR3 \<sigma>"
  and     c4: "CR3_RED t (\<tau>\<rightarrow>\<sigma>)"
  shows "(App t u)\<in>RED \<sigma>"
using a b
proof (induct)
  fix u
  assume as: "u\<in>RED \<tau>"
  assume ih: " \<And>u'. \<lbrakk>u \<longrightarrow>\<^isub>\<beta> u'; u' \<in> RED \<tau>\<rbrakk> \<Longrightarrow> App t u' \<in> RED \<sigma>"
  have "NEUT (App t u)" using c1 by (auto simp add: NEUT_def)
  moreover
  have "CR3_RED (App t u) \<sigma>" unfolding CR3_RED_def
  proof (intro strip)
    fix r
    assume red: "App t u \<longrightarrow>\<^isub>\<beta> r"
    moreover
    { assume "\<exists>t'. t \<longrightarrow>\<^isub>\<beta> t' \<and> r = App t' u"
      then obtain t' where a1: "t \<longrightarrow>\<^isub>\<beta> t'" and a2: "r = App t' u" by blast
      have "t'\<in>RED (\<tau>\<rightarrow>\<sigma>)" using c4 a1 by (simp add: CR3_RED_def)
      then have "App t' u\<in>RED \<sigma>" using as by simp
      then have "r\<in>RED \<sigma>" using a2 by simp
    }
    moreover
    { assume "\<exists>u'. u \<longrightarrow>\<^isub>\<beta> u' \<and> r = App t u'"
      then obtain u' where b1: "u \<longrightarrow>\<^isub>\<beta> u'" and b2: "r = App t u'" by blast
      have "u'\<in>RED \<tau>" using as b1 c2 by (auto simp add: CR2_def)
      with ih have "App t u' \<in> RED \<sigma>" using b1 by simp
      then have "r\<in>RED \<sigma>" using b2 by simp
    }
    moreover
    { assume "\<exists>x t'. t = Lam [x].t'"
      then obtain x t' where "t = Lam [x].t'" by blast
      then have "NEUT (Lam [x].t')" using c1 by simp
      then have "False" by (simp add: NEUT_def)
      then have "r\<in>RED \<sigma>" by simp
    }
    ultimately show "r \<in> RED \<sigma>" by (cases) (auto simp add: lam.inject)
  qed
  ultimately show "App t u \<in> RED \<sigma>" using c3 by (simp add: CR3_def)
qed 

text {* properties of the candiadates *}
lemma RED_props: 
  shows "CR1 \<tau>" and "CR2 \<tau>" and "CR3 \<tau>"
proof (nominal_induct \<tau> rule: ty.strong_induct)
  case (TVar a)
  { case 1 show "CR1 (TVar a)" by (simp add: CR1_def)
  next
    case 2 show "CR2 (TVar a)" by (auto intro: SN_preserved simp add: CR2_def)
  next
    case 3 show "CR3 (TVar a)" by (auto intro: SN_intro simp add: CR3_def CR3_RED_def)
  }
next
  case (TArr \<tau>1 \<tau>2)
  { case 1
    have ih_CR3_\<tau>1: "CR3 \<tau>1" by fact
    have ih_CR1_\<tau>2: "CR1 \<tau>2" by fact
    have "\<And>t. t \<in> RED (\<tau>1 \<rightarrow> \<tau>2) \<Longrightarrow> SN t" 
    proof - 
      fix t
      assume "t \<in> RED (\<tau>1 \<rightarrow> \<tau>2)"
      then have a: "\<forall>u. u \<in> RED \<tau>1 \<longrightarrow> App t u \<in> RED \<tau>2" by simp
      from ih_CR3_\<tau>1 have "CR4 \<tau>1" by (simp add: CR3_implies_CR4) 
      moreover
      fix a have "NEUT (Var a)" by (force simp add: NEUT_def)
      moreover
      have "NORMAL (Var a)" by (rule NORMAL_Var)
      ultimately have "(Var a)\<in> RED \<tau>1" by (simp add: CR4_def)
      with a have "App t (Var a) \<in> RED \<tau>2" by simp
      hence "SN (App t (Var a))" using ih_CR1_\<tau>2 by (simp add: CR1_def)
      thus "SN t" by (auto dest: SN_of_FST_of_App)
    qed
    then show "CR1 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR1_def by simp
  next
    case 2
    have ih_CR2_\<tau>2: "CR2 \<tau>2" by fact
    then show "CR2 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR2_def by auto 
  next
    case 3
    have ih_CR1_\<tau>1: "CR1 \<tau>1" by fact
    have ih_CR2_\<tau>1: "CR2 \<tau>1" by fact
    have ih_CR3_\<tau>2: "CR3 \<tau>2" by fact
    show "CR3 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR3_def
    proof (simp, intro strip)
      fix t u
      assume a1: "u \<in> RED \<tau>1"
      assume a2: "NEUT t \<and> CR3_RED t (\<tau>1 \<rightarrow> \<tau>2)"
      have "SN(u)" using a1 ih_CR1_\<tau>1 by (simp add: CR1_def)
      then show "(App t u)\<in>RED \<tau>2" using ih_CR2_\<tau>1 ih_CR3_\<tau>2 a1 a2 by (blast intro: sub_induction)
    qed
  }
qed
   
text {* 
  the next lemma not as simple as on paper, probably because of 
  the stronger double_SN induction 
*} 
lemma abs_RED: 
  assumes asm: "\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>"
  shows "Lam [x].t\<in>RED (\<tau>\<rightarrow>\<sigma>)"
proof -
  have b1: "SN t" 
  proof -
    have "Var x\<in>RED \<tau>"
    proof -
      have "CR4 \<tau>" by (simp add: RED_props CR3_implies_CR4)
      moreover
      have "NEUT (Var x)" by (auto simp add: NEUT_def)
      moreover
      have "NORMAL (Var x)" by (auto elim: Beta.cases simp add: NORMAL_def)
      ultimately show "Var x\<in>RED \<tau>" by (simp add: CR4_def)
    qed
    then have "t[x::=Var x]\<in>RED \<sigma>" using asm by simp
    then have "t\<in>RED \<sigma>" by (simp add: id_subs)
    moreover 
    have "CR1 \<sigma>" by (simp add: RED_props)
    ultimately show "SN t" by (simp add: CR1_def)
  qed
  show "Lam [x].t\<in>RED (\<tau>\<rightarrow>\<sigma>)"
  proof (simp, intro strip)
    fix u
    assume b2: "u\<in>RED \<tau>"
    then have b3: "SN u" using RED_props by (auto simp add: CR1_def)
    show "App (Lam [x].t) u \<in> RED \<sigma>" using b1 b3 b2 asm
    proof(induct t u rule: double_SN)
      fix t u
      assume ih1: "\<And>t'.  \<lbrakk>t \<longrightarrow>\<^isub>\<beta> t'; u\<in>RED \<tau>; \<forall>s\<in>RED \<tau>. t'[x::=s]\<in>RED \<sigma>\<rbrakk> \<Longrightarrow> App (Lam [x].t') u \<in> RED \<sigma>" 
      assume ih2: "\<And>u'.  \<lbrakk>u \<longrightarrow>\<^isub>\<beta> u'; u'\<in>RED \<tau>; \<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>\<rbrakk> \<Longrightarrow> App (Lam [x].t) u' \<in> RED \<sigma>"
      assume as1: "u \<in> RED \<tau>"
      assume as2: "\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>"
      have "CR3_RED (App (Lam [x].t) u) \<sigma>" unfolding CR3_RED_def
      proof(intro strip)
        fix r
        assume red: "App (Lam [x].t) u \<longrightarrow>\<^isub>\<beta> r"
        moreover
        { assume "\<exists>t'. t \<longrightarrow>\<^isub>\<beta> t' \<and> r = App (Lam [x].t') u"
          then obtain t' where a1: "t \<longrightarrow>\<^isub>\<beta> t'" and a2: "r = App (Lam [x].t') u" by blast
          have "App (Lam [x].t') u\<in>RED \<sigma>" using ih1 a1 as1 as2
            apply(auto)
            apply(drule_tac x="t'" in meta_spec)
            apply(simp)
            apply(drule meta_mp)
            prefer 2
            apply(auto)[1]
            apply(rule ballI)
            apply(drule_tac x="s" in bspec)
            apply(simp)
            apply(subgoal_tac "CR2 \<sigma>")(*A*)
            apply(unfold CR2_def)[1]
            apply(drule_tac x="t[x::=s]" in spec)
            apply(drule_tac x="t'[x::=s]" in spec)
            apply(simp add: beta_subst)
            (*A*)
            apply(simp add: RED_props)
            done
          then have "r\<in>RED \<sigma>" using a2 by simp
        }
        moreover
        { assume "\<exists>u'. u \<longrightarrow>\<^isub>\<beta> u' \<and> r = App (Lam [x].t) u'"
          then obtain u' where b1: "u \<longrightarrow>\<^isub>\<beta> u'" and b2: "r = App (Lam [x].t) u'" by blast
          have "App (Lam [x].t) u'\<in>RED \<sigma>" using ih2 b1 as1 as2
            apply(auto)
            apply(drule_tac x="u'" in meta_spec)
            apply(simp)
            apply(drule meta_mp)
            apply(subgoal_tac "CR2 \<tau>")
            apply(unfold CR2_def)[1]
            apply(drule_tac x="u" in spec)
            apply(drule_tac x="u'" in spec)
            apply(simp)
            apply(simp add: RED_props)
            apply(simp)
            done
          then have "r\<in>RED \<sigma>" using b2 by simp
        }
        moreover
        { assume "r = t[x::=u]"
          then have "r\<in>RED \<sigma>" using as1 as2 by auto
        }
        ultimately show "r \<in> RED \<sigma>" 
          (* one wants to use the strong elimination principle; for this one 
             has to know that x\<sharp>u *)
        apply(cases) 
        apply(auto simp add: lam.inject)
        apply(drule beta_abs)
        apply(auto)[1]
        apply(auto simp add: alpha subst_rename)
        done
    qed
    moreover 
    have "NEUT (App (Lam [x].t) u)" unfolding NEUT_def by (auto)
    ultimately show "App (Lam [x].t) u \<in> RED \<sigma>"  using RED_props by (simp add: CR3_def)
  qed
qed
qed

abbreviation 
 mapsto :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> bool" ("_ maps _ to _" [55,55,55] 55) 
where
 "\<theta> maps x to e \<equiv> (lookup \<theta> x) = e"

abbreviation 
  closes :: "(name\<times>lam) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ closes _" [55,55] 55) 
where
  "\<theta> closes \<Gamma> \<equiv> \<forall>x T. ((x,T) \<in> set \<Gamma> \<longrightarrow> (\<exists>t. \<theta> maps x to t \<and> t \<in> RED T))"

lemma all_RED: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  and     b: "\<theta> closes \<Gamma>"
  shows "\<theta><t> \<in> RED \<tau>"
using a b
proof(nominal_induct  avoiding: \<theta> rule: typing.strong_induct)
  case (t3 a \<Gamma> \<sigma> t \<tau> \<theta>) --"lambda case"
  have ih: "\<And>\<theta>. \<theta> closes ((a,\<sigma>)#\<Gamma>) \<Longrightarrow> \<theta><t> \<in> RED \<tau>" by fact
  have \<theta>_cond: "\<theta> closes \<Gamma>" by fact
  have fresh: "a\<sharp>\<Gamma>" "a\<sharp>\<theta>" by fact+
  from ih have "\<forall>s\<in>RED \<sigma>. ((a,s)#\<theta>)<t> \<in> RED \<tau>" using fresh \<theta>_cond fresh_context by simp
  then have "\<forall>s\<in>RED \<sigma>. \<theta><t>[a::=s] \<in> RED \<tau>" using fresh by (simp add: psubst_subst)
  then have "Lam [a].(\<theta><t>) \<in> RED (\<sigma> \<rightarrow> \<tau>)" by (simp only: abs_RED)
  then show "\<theta><(Lam [a].t)> \<in> RED (\<sigma> \<rightarrow> \<tau>)" using fresh by simp
qed auto

section {* identity substitution generated from a context \<Gamma> *}
fun
  "id" :: "(name\<times>ty) list \<Rightarrow> (name\<times>lam) list"
where
  "id []    = []"
| "id ((x,\<tau>)#\<Gamma>) = (x,Var x)#(id \<Gamma>)"

lemma id_maps:
  shows "(id \<Gamma>) maps a to (Var a)"
by (induct \<Gamma>) (auto)

lemma id_fresh:
  fixes a::"name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "a\<sharp>(id \<Gamma>)"
using a
by (induct \<Gamma>)
   (auto simp add: fresh_list_nil fresh_list_cons)

lemma id_apply:  
  shows "(id \<Gamma>)<t> = t"
by (nominal_induct t avoiding: \<Gamma> rule: lam.strong_induct)
   (auto simp add: id_maps id_fresh)

lemma id_closes:
  shows "(id \<Gamma>) closes \<Gamma>"
apply(auto)
apply(simp add: id_maps)
apply(subgoal_tac "CR3 T") --"A"
apply(drule CR3_implies_CR4)
apply(simp add: CR4_def)
apply(drule_tac x="Var x" in spec)
apply(force simp add: NEUT_def NORMAL_Var)
--"A"
apply(rule RED_props)
done

lemma typing_implies_RED:  
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "t \<in> RED \<tau>"
proof -
  have "(id \<Gamma>)<t>\<in>RED \<tau>" 
  proof -
    have "(id \<Gamma>) closes \<Gamma>" by (rule id_closes)
    with a show ?thesis by (rule all_RED)
  qed
  thus"t \<in> RED \<tau>" by (simp add: id_apply)
qed

lemma typing_implies_SN: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "SN(t)"
proof -
  from a have "t \<in> RED \<tau>" by (rule typing_implies_RED)
  moreover
  have "CR1 \<tau>" by (rule RED_props)
  ultimately show "SN(t)" by (simp add: CR1_def)
qed

end