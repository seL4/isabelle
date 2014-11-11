(*  Title:      CCL/Fix.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

section {* Tentative attempt at including fixed point induction; justified by Smith *}

theory Fix
imports Type
begin

definition idgen :: "i \<Rightarrow> i"
  where "idgen(f) == lam t. case(t,true,false, \<lambda>x y.<f`x, f`y>, \<lambda>u. lam x. f ` u(x))"

axiomatization INCL :: "[i\<Rightarrow>o]\<Rightarrow>o" where
  INCL_def: "INCL(\<lambda>x. P(x)) == (ALL f.(ALL n:Nat. P(f^n`bot)) \<longrightarrow> P(fix(f)))" and
  po_INCL: "INCL(\<lambda>x. a(x) [= b(x))" and
  INCL_subst: "INCL(P) \<Longrightarrow> INCL(\<lambda>x. P((g::i\<Rightarrow>i)(x)))"


subsection {* Fixed Point Induction *}

lemma fix_ind:
  assumes base: "P(bot)"
    and step: "\<And>x. P(x) \<Longrightarrow> P(f(x))"
    and incl: "INCL(P)"
  shows "P(fix(f))"
  apply (rule incl [unfolded INCL_def, rule_format])
  apply (rule Nat_ind [THEN ballI], assumption)
   apply simp_all
   apply (rule base)
  apply (erule step)
  done


subsection {* Inclusive Predicates *}

lemma inclXH: "INCL(P) \<longleftrightarrow> (ALL f. (ALL n:Nat. P(f ^ n ` bot)) \<longrightarrow> P(fix(f)))"
  by (simp add: INCL_def)

lemma inclI: "\<lbrakk>\<And>f. ALL n:Nat. P(f^n`bot) \<Longrightarrow> P(fix(f))\<rbrakk> \<Longrightarrow> INCL(\<lambda>x. P(x))"
  unfolding inclXH by blast

lemma inclD: "\<lbrakk>INCL(P); \<And>n. n:Nat \<Longrightarrow> P(f^n`bot)\<rbrakk> \<Longrightarrow> P(fix(f))"
  unfolding inclXH by blast

lemma inclE: "\<lbrakk>INCL(P); (ALL n:Nat. P(f^n`bot)) \<longrightarrow> P(fix(f)) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (blast dest: inclD)


subsection {* Lemmas for Inclusive Predicates *}

lemma npo_INCL: "INCL(\<lambda>x. \<not> a(x) [= t)"
  apply (rule inclI)
  apply (drule bspec)
   apply (rule zeroT)
  apply (erule contrapos)
  apply (rule po_trans)
   prefer 2
   apply assumption
  apply (subst napplyBzero)
  apply (rule po_cong, rule po_bot)
  done

lemma conj_INCL: "\<lbrakk>INCL(P); INCL(Q)\<rbrakk> \<Longrightarrow> INCL(\<lambda>x. P(x) \<and> Q(x))"
  by (blast intro!: inclI dest!: inclD)

lemma all_INCL: "(\<And>a. INCL(P(a))) \<Longrightarrow> INCL(\<lambda>x. ALL a. P(a,x))"
  by (blast intro!: inclI dest!: inclD)

lemma ball_INCL: "(\<And>a. a:A \<Longrightarrow> INCL(P(a))) \<Longrightarrow> INCL(\<lambda>x. ALL a:A. P(a,x))"
  by (blast intro!: inclI dest!: inclD)

lemma eq_INCL: "INCL(\<lambda>x. a(x) = (b(x)::'a::prog))"
  apply (simp add: eq_iff)
  apply (rule conj_INCL po_INCL)+
  done


subsection {* Derivation of Reachability Condition *}

(* Fixed points of idgen *)

lemma fix_idgenfp: "idgen(fix(idgen)) = fix(idgen)"
  apply (rule fixB [symmetric])
  done

lemma id_idgenfp: "idgen(lam x. x) = lam x. x"
  apply (simp add: idgen_def)
  apply (rule term_case [THEN allI])
      apply simp_all
  done

(* All fixed points are lam-expressions *)

schematic_lemma idgenfp_lam: "idgen(d) = d \<Longrightarrow> d = lam x. ?f(x)"
  apply (unfold idgen_def)
  apply (erule ssubst)
  apply (rule refl)
  done

(* Lemmas for rewriting fixed points of idgen *)

lemma l_lemma: "\<lbrakk>a = b; a ` t = u\<rbrakk> \<Longrightarrow> b ` t = u"
  by (simp add: idgen_def)

lemma idgen_lemmas:
  "idgen(d) = d \<Longrightarrow> d ` bot = bot"
  "idgen(d) = d \<Longrightarrow> d ` true = true"
  "idgen(d) = d \<Longrightarrow> d ` false = false"
  "idgen(d) = d \<Longrightarrow> d ` <a,b> = <d ` a,d ` b>"
  "idgen(d) = d \<Longrightarrow> d ` (lam x. f(x)) = lam x. d ` f(x)"
  by (erule l_lemma, simp add: idgen_def)+


(* Proof of Reachability law - show that fix and lam x.x both give LEAST fixed points
  of idgen and hence are they same *)

lemma po_eta:
  "\<lbrakk>ALL x. t ` x [= u ` x; EX f. t=lam x. f(x); EX f. u=lam x. f(x)\<rbrakk> \<Longrightarrow> t [= u"
  apply (drule cond_eta)+
  apply (erule ssubst)
  apply (erule ssubst)
  apply (rule po_lam [THEN iffD2])
  apply simp
  done

schematic_lemma po_eta_lemma: "idgen(d) = d \<Longrightarrow> d = lam x. ?f(x)"
  apply (unfold idgen_def)
  apply (erule sym)
  done

lemma lemma1:
  "idgen(d) = d \<Longrightarrow>
    {p. EX a b. p=<a,b> \<and> (EX t. a=fix(idgen) ` t \<and> b = d ` t)} <=
      POgen({p. EX a b. p=<a,b> \<and> (EX t. a=fix(idgen) ` t  \<and> b = d ` t)})"
  apply clarify
  apply (rule_tac t = t in term_case)
      apply (simp_all add: POgenXH idgen_lemmas idgen_lemmas [OF fix_idgenfp])
   apply blast
  apply fast
  done

lemma fix_least_idgen: "idgen(d) = d \<Longrightarrow> fix(idgen) [= d"
  apply (rule allI [THEN po_eta])
    apply (rule lemma1 [THEN [2] po_coinduct])
     apply (blast intro: po_eta_lemma fix_idgenfp)+
  done

lemma lemma2:
  "idgen(d) = d \<Longrightarrow>
    {p. EX a b. p=<a,b> \<and> b = d ` a} <= POgen({p. EX a b. p=<a,b> \<and> b = d ` a})"
  apply clarify
  apply (rule_tac t = a in term_case)
      apply (simp_all add: POgenXH idgen_lemmas)
  apply fast
  done

lemma id_least_idgen: "idgen(d) = d \<Longrightarrow> lam x. x [= d"
  apply (rule allI [THEN po_eta])
    apply (rule lemma2 [THEN [2] po_coinduct])
     apply simp
    apply (fast intro: po_eta_lemma fix_idgenfp)+
  done

lemma reachability: "fix(idgen) = lam x. x"
  apply (fast intro: eq_iff [THEN iffD2]
    id_idgenfp [THEN fix_least_idgen] fix_idgenfp [THEN id_least_idgen])
  done

(********)

lemma id_apply: "f = lam x. x \<Longrightarrow> f`t = t"
  apply (erule ssubst)
  apply (rule applyB)
  done

lemma term_ind:
  assumes 1: "P(bot)" and 2: "P(true)" and 3: "P(false)"
    and 4: "\<And>x y. \<lbrakk>P(x); P(y)\<rbrakk> \<Longrightarrow> P(<x,y>)"
    and 5: "\<And>u.(\<And>x. P(u(x))) \<Longrightarrow> P(lam x. u(x))"
    and 6: "INCL(P)"
  shows "P(t)"
  apply (rule reachability [THEN id_apply, THEN subst])
  apply (rule_tac x = t in spec)
  apply (rule fix_ind)
    apply (unfold idgen_def)
    apply (rule allI)
    apply (subst applyBbot)
    apply (rule 1)
   apply (rule allI)
   apply (rule applyB [THEN ssubst])
    apply (rule_tac t = "xa" in term_case)
       apply simp_all
       apply (fast intro: assms INCL_subst all_INCL)+
  done

end
