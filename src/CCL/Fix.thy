(*  Title:      CCL/Fix.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

header {* Tentative attempt at including fixed point induction; justified by Smith *}

theory Fix
imports Type
begin

consts
  idgen      ::       "[i]=>i"
  INCL      :: "[i=>o]=>o"

defs
  idgen_def:
  "idgen(f) == lam t. case(t,true,false,%x y.<f`x, f`y>,%u. lam x. f ` u(x))"

axioms
  INCL_def:   "INCL(%x. P(x)) == (ALL f.(ALL n:Nat. P(f^n`bot)) --> P(fix(f)))"
  po_INCL:    "INCL(%x. a(x) [= b(x))"
  INCL_subst: "INCL(P) ==> INCL(%x. P((g::i=>i)(x)))"


subsection {* Fixed Point Induction *}

lemma fix_ind:
  assumes base: "P(bot)"
    and step: "!!x. P(x) ==> P(f(x))"
    and incl: "INCL(P)"
  shows "P(fix(f))"
  apply (rule incl [unfolded INCL_def, rule_format])
  apply (rule Nat_ind [THEN ballI], assumption)
   apply simp_all
   apply (rule base)
  apply (erule step)
  done


subsection {* Inclusive Predicates *}

lemma inclXH: "INCL(P) <-> (ALL f. (ALL n:Nat. P(f ^ n ` bot)) --> P(fix(f)))"
  by (simp add: INCL_def)

lemma inclI: "[| !!f. ALL n:Nat. P(f^n`bot) ==> P(fix(f)) |] ==> INCL(%x. P(x))"
  unfolding inclXH by blast

lemma inclD: "[| INCL(P);  !!n. n:Nat ==> P(f^n`bot) |] ==> P(fix(f))"
  unfolding inclXH by blast

lemma inclE: "[| INCL(P);  (ALL n:Nat. P(f^n`bot))-->P(fix(f)) ==> R |] ==> R"
  by (blast dest: inclD)


subsection {* Lemmas for Inclusive Predicates *}

lemma npo_INCL: "INCL(%x.~ a(x) [= t)"
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

lemma conj_INCL: "[| INCL(P);  INCL(Q) |] ==> INCL(%x. P(x) & Q(x))"
  by (blast intro!: inclI dest!: inclD)

lemma all_INCL: "[| !!a. INCL(P(a)) |] ==> INCL(%x. ALL a. P(a,x))"
  by (blast intro!: inclI dest!: inclD)

lemma ball_INCL: "[| !!a. a:A ==> INCL(P(a)) |] ==> INCL(%x. ALL a:A. P(a,x))"
  by (blast intro!: inclI dest!: inclD)

lemma eq_INCL: "INCL(%x. a(x) = (b(x)::'a::prog))"
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

lemma idgenfp_lam: "idgen(d) = d ==> d = lam x. ?f(x)"
  apply (unfold idgen_def)
  apply (erule ssubst)
  apply (rule refl)
  done

(* Lemmas for rewriting fixed points of idgen *)

lemma l_lemma: "[| a = b;  a ` t = u |] ==> b ` t = u"
  by (simp add: idgen_def)

lemma idgen_lemmas:
  "idgen(d) = d ==> d ` bot = bot"
  "idgen(d) = d ==> d ` true = true"
  "idgen(d) = d ==> d ` false = false"
  "idgen(d) = d ==> d ` <a,b> = <d ` a,d ` b>"
  "idgen(d) = d ==> d ` (lam x. f(x)) = lam x. d ` f(x)"
  by (erule l_lemma, simp add: idgen_def)+


(* Proof of Reachability law - show that fix and lam x.x both give LEAST fixed points
  of idgen and hence are they same *)

lemma po_eta:
  "[| ALL x. t ` x [= u ` x;  EX f. t=lam x. f(x);  EX f. u=lam x. f(x) |] ==> t [= u"
  apply (drule cond_eta)+
  apply (erule ssubst)
  apply (erule ssubst)
  apply (rule po_lam [THEN iffD2])
  apply simp
  done

lemma po_eta_lemma: "idgen(d) = d ==> d = lam x. ?f(x)"
  apply (unfold idgen_def)
  apply (erule sym)
  done

lemma lemma1:
  "idgen(d) = d ==>
    {p. EX a b. p=<a,b> & (EX t. a=fix(idgen) ` t & b = d ` t)} <=
      POgen({p. EX a b. p=<a,b> & (EX t. a=fix(idgen) ` t  & b = d ` t)})"
  apply clarify
  apply (rule_tac t = t in term_case)
      apply (simp_all add: POgenXH idgen_lemmas idgen_lemmas [OF fix_idgenfp])
   apply blast
  apply fast
  done

lemma fix_least_idgen: "idgen(d) = d ==> fix(idgen) [= d"
  apply (rule allI [THEN po_eta])
    apply (rule lemma1 [THEN [2] po_coinduct])
     apply (blast intro: po_eta_lemma fix_idgenfp)+
  done

lemma lemma2:
  "idgen(d) = d ==>
    {p. EX a b. p=<a,b> & b = d ` a} <= POgen({p. EX a b. p=<a,b> & b = d ` a})"
  apply clarify
  apply (rule_tac t = a in term_case)
      apply (simp_all add: POgenXH idgen_lemmas)
  apply fast
  done

lemma id_least_idgen: "idgen(d) = d ==> lam x. x [= d"
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

lemma id_apply: "f = lam x. x ==> f`t = t"
  apply (erule ssubst)
  apply (rule applyB)
  done

lemma term_ind:
  assumes 1: "P(bot)" and 2: "P(true)" and 3: "P(false)"
    and 4: "!!x y.[| P(x);  P(y) |] ==> P(<x,y>)"
    and 5: "!!u.(!!x. P(u(x))) ==> P(lam x. u(x))"
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
