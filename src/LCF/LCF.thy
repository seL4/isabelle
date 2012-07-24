(*  Title:      LCF/LCF.thy
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge
*)

header {* LCF on top of First-Order Logic *}

theory LCF
imports "~~/src/FOL/FOL"
begin

text {* This theory is based on Lawrence Paulson's book Logic and Computation. *}

subsection {* Natural Deduction Rules for LCF *}

classes cpo < "term"
default_sort cpo

typedecl tr
typedecl void
typedecl ('a,'b) prod  (infixl "*" 6)
typedecl ('a,'b) sum  (infixl "+" 5)

arities
  "fun" :: (cpo, cpo) cpo
  prod :: (cpo, cpo) cpo
  sum :: (cpo, cpo) cpo
  tr :: cpo
  void :: cpo

consts
 UU     :: "'a"
 TT     :: "tr"
 FF     :: "tr"
 FIX    :: "('a => 'a) => 'a"
 FST    :: "'a*'b => 'a"
 SND    :: "'a*'b => 'b"
 INL    :: "'a => 'a+'b"
 INR    :: "'b => 'a+'b"
 WHEN   :: "['a=>'c, 'b=>'c, 'a+'b] => 'c"
 adm    :: "('a => o) => o"
 VOID   :: "void"               ("'(')")
 PAIR   :: "['a,'b] => 'a*'b"   ("(1<_,/_>)" [0,0] 100)
 COND   :: "[tr,'a,'a] => 'a"   ("(_ =>/ (_ |/ _))" [60,60,60] 60)
 less   :: "['a,'a] => o"       (infixl "<<" 50)

axiomatization where
  (** DOMAIN THEORY **)

  eq_def:        "x=y == x << y & y << x" and

  less_trans:    "[| x << y; y << z |] ==> x << z" and

  less_ext:      "(ALL x. f(x) << g(x)) ==> f << g" and

  mono:          "[| f << g; x << y |] ==> f(x) << g(y)" and

  minimal:       "UU << x" and

  FIX_eq:        "\<And>f. f(FIX(f)) = FIX(f)"

axiomatization where
  (** TR **)

  tr_cases:      "p=UU | p=TT | p=FF" and

  not_TT_less_FF: "~ TT << FF" and
  not_FF_less_TT: "~ FF << TT" and
  not_TT_less_UU: "~ TT << UU" and
  not_FF_less_UU: "~ FF << UU" and

  COND_UU:       "UU => x | y  =  UU" and
  COND_TT:       "TT => x | y  =  x" and
  COND_FF:       "FF => x | y  =  y"

axiomatization where
  (** PAIRS **)

  surj_pairing:  "<FST(z),SND(z)> = z" and

  FST:   "FST(<x,y>) = x" and
  SND:   "SND(<x,y>) = y"

axiomatization where
  (*** STRICT SUM ***)

  INL_DEF: "~x=UU ==> ~INL(x)=UU" and
  INR_DEF: "~x=UU ==> ~INR(x)=UU" and

  INL_STRICT: "INL(UU) = UU" and
  INR_STRICT: "INR(UU) = UU" and

  WHEN_UU:  "WHEN(f,g,UU) = UU" and
  WHEN_INL: "~x=UU ==> WHEN(f,g,INL(x)) = f(x)" and
  WHEN_INR: "~x=UU ==> WHEN(f,g,INR(x)) = g(x)" and

  SUM_EXHAUSTION:
    "z = UU | (EX x. ~x=UU & z = INL(x)) | (EX y. ~y=UU & z = INR(y))"

axiomatization where
  (** VOID **)

  void_cases:    "(x::void) = UU"

  (** INDUCTION **)

axiomatization where
  induct:        "[| adm(P); P(UU); ALL x. P(x) --> P(f(x)) |] ==> P(FIX(f))"

axiomatization where
  (** Admissibility / Chain Completeness **)
  (* All rules can be found on pages 199--200 of Larry's LCF book.
     Note that "easiness" of types is not taken into account
     because it cannot be expressed schematically; flatness could be. *)

  adm_less:      "\<And>t u. adm(%x. t(x) << u(x))" and
  adm_not_less:  "\<And>t u. adm(%x.~ t(x) << u)" and
  adm_not_free:  "\<And>A. adm(%x. A)" and
  adm_subst:     "\<And>P t. adm(P) ==> adm(%x. P(t(x)))" and
  adm_conj:      "\<And>P Q. [| adm(P); adm(Q) |] ==> adm(%x. P(x)&Q(x))" and
  adm_disj:      "\<And>P Q. [| adm(P); adm(Q) |] ==> adm(%x. P(x)|Q(x))" and
  adm_imp:       "\<And>P Q. [| adm(%x.~P(x)); adm(Q) |] ==> adm(%x. P(x)-->Q(x))" and
  adm_all:       "\<And>P. (!!y. adm(P(y))) ==> adm(%x. ALL y. P(y,x))"


lemma eq_imp_less1: "x = y ==> x << y"
  by (simp add: eq_def)

lemma eq_imp_less2: "x = y ==> y << x"
  by (simp add: eq_def)

lemma less_refl [simp]: "x << x"
  apply (rule eq_imp_less1)
  apply (rule refl)
  done

lemma less_anti_sym: "[| x << y; y << x |] ==> x=y"
  by (simp add: eq_def)

lemma ext: "(!!x::'a::cpo. f(x)=(g(x)::'b::cpo)) ==> (%x. f(x))=(%x. g(x))"
  apply (rule less_anti_sym)
  apply (rule less_ext)
  apply simp
  apply simp
  done

lemma cong: "[| f=g; x=y |] ==> f(x)=g(y)"
  by simp

lemma less_ap_term: "x << y ==> f(x) << f(y)"
  by (rule less_refl [THEN mono])

lemma less_ap_thm: "f << g ==> f(x) << g(x)"
  by (rule less_refl [THEN [2] mono])

lemma ap_term: "(x::'a::cpo) = y ==> (f(x)::'b::cpo) = f(y)"
  apply (rule cong [OF refl])
  apply simp
  done

lemma ap_thm: "f = g ==> f(x) = g(x)"
  apply (erule cong)
  apply (rule refl)
  done


lemma UU_abs: "(%x::'a::cpo. UU) = UU"
  apply (rule less_anti_sym)
  prefer 2
  apply (rule minimal)
  apply (rule less_ext)
  apply (rule allI)
  apply (rule minimal)
  done

lemma UU_app: "UU(x) = UU"
  by (rule UU_abs [symmetric, THEN ap_thm])

lemma less_UU: "x << UU ==> x=UU"
  apply (rule less_anti_sym)
  apply assumption
  apply (rule minimal)
  done

lemma tr_induct: "[| P(UU); P(TT); P(FF) |] ==> ALL b. P(b)"
  apply (rule allI)
  apply (rule mp)
  apply (rule_tac [2] p = b in tr_cases)
  apply blast
  done

lemma Contrapos: "~ B ==> (A ==> B) ==> ~A"
  by blast

lemma not_less_imp_not_eq1: "~ x << y \<Longrightarrow> x \<noteq> y"
  apply (erule Contrapos)
  apply simp
  done

lemma not_less_imp_not_eq2: "~ y << x \<Longrightarrow> x \<noteq> y"
  apply (erule Contrapos)
  apply simp
  done

lemma not_UU_eq_TT: "UU \<noteq> TT"
  by (rule not_less_imp_not_eq2) (rule not_TT_less_UU)
lemma not_UU_eq_FF: "UU \<noteq> FF"
  by (rule not_less_imp_not_eq2) (rule not_FF_less_UU)
lemma not_TT_eq_UU: "TT \<noteq> UU"
  by (rule not_less_imp_not_eq1) (rule not_TT_less_UU)
lemma not_TT_eq_FF: "TT \<noteq> FF"
  by (rule not_less_imp_not_eq1) (rule not_TT_less_FF)
lemma not_FF_eq_UU: "FF \<noteq> UU"
  by (rule not_less_imp_not_eq1) (rule not_FF_less_UU)
lemma not_FF_eq_TT: "FF \<noteq> TT"
  by (rule not_less_imp_not_eq1) (rule not_FF_less_TT)


lemma COND_cases_iff [rule_format]:
    "ALL b. P(b=>x|y) <-> (b=UU-->P(UU)) & (b=TT-->P(x)) & (b=FF-->P(y))"
  apply (insert not_UU_eq_TT not_UU_eq_FF not_TT_eq_UU
    not_TT_eq_FF not_FF_eq_UU not_FF_eq_TT)
  apply (rule tr_induct)
  apply (simplesubst COND_UU)
  apply blast
  apply (simplesubst COND_TT)
  apply blast
  apply (simplesubst COND_FF)
  apply blast
  done

lemma COND_cases: 
  "[| x = UU --> P(UU); x = TT --> P(xa); x = FF --> P(y) |] ==> P(x => xa | y)"
  apply (rule COND_cases_iff [THEN iffD2])
  apply blast
  done

lemmas [simp] =
  minimal
  UU_app
  UU_app [THEN ap_thm]
  UU_app [THEN ap_thm, THEN ap_thm]
  not_TT_less_FF not_FF_less_TT not_TT_less_UU not_FF_less_UU not_UU_eq_TT
  not_UU_eq_FF not_TT_eq_UU not_TT_eq_FF not_FF_eq_UU not_FF_eq_TT
  COND_UU COND_TT COND_FF
  surj_pairing FST SND


subsection {* Ordered pairs and products *}

lemma expand_all_PROD: "(ALL p. P(p)) <-> (ALL x y. P(<x,y>))"
  apply (rule iffI)
  apply blast
  apply (rule allI)
  apply (rule surj_pairing [THEN subst])
  apply blast
  done

lemma PROD_less: "(p::'a*'b) << q <-> FST(p) << FST(q) & SND(p) << SND(q)"
  apply (rule iffI)
  apply (rule conjI)
  apply (erule less_ap_term)
  apply (erule less_ap_term)
  apply (erule conjE)
  apply (rule surj_pairing [of p, THEN subst])
  apply (rule surj_pairing [of q, THEN subst])
  apply (rule mono, erule less_ap_term, assumption)
  done

lemma PROD_eq: "p=q <-> FST(p)=FST(q) & SND(p)=SND(q)"
  apply (rule iffI)
  apply simp
  apply (unfold eq_def)
  apply (simp add: PROD_less)
  done

lemma PAIR_less [simp]: "<a,b> << <c,d> <-> a<<c & b<<d"
  by (simp add: PROD_less)

lemma PAIR_eq [simp]: "<a,b> = <c,d> <-> a=c & b=d"
  by (simp add: PROD_eq)

lemma UU_is_UU_UU [simp]: "<UU,UU> = UU"
  by (rule less_UU) (simp add: PROD_less)

lemma FST_STRICT [simp]: "FST(UU) = UU"
  apply (rule subst [OF UU_is_UU_UU])
  apply (simp del: UU_is_UU_UU)
  done

lemma SND_STRICT [simp]: "SND(UU) = UU"
  apply (rule subst [OF UU_is_UU_UU])
  apply (simp del: UU_is_UU_UU)
  done


subsection {* Fixedpoint theory *}

lemma adm_eq: "adm(%x. t(x)=(u(x)::'a::cpo))"
  apply (unfold eq_def)
  apply (rule adm_conj adm_less)+
  done

lemma adm_not_not: "adm(P) ==> adm(%x.~~P(x))"
  by simp

lemma not_eq_TT: "ALL p. ~p=TT <-> (p=FF | p=UU)"
  and not_eq_FF: "ALL p. ~p=FF <-> (p=TT | p=UU)"
  and not_eq_UU: "ALL p. ~p=UU <-> (p=TT | p=FF)"
  by (rule tr_induct, simp_all)+

lemma adm_not_eq_tr: "ALL p::tr. adm(%x. ~t(x)=p)"
  apply (rule tr_induct)
  apply (simp_all add: not_eq_TT not_eq_FF not_eq_UU)
  apply (rule adm_disj adm_eq)+
  done

lemmas adm_lemmas =
  adm_not_free adm_eq adm_less adm_not_less
  adm_not_eq_tr adm_conj adm_disj adm_imp adm_all


ML {*
  fun induct_tac ctxt v i =
    res_inst_tac ctxt [(("f", 0), v)] @{thm induct} i THEN
    REPEAT (resolve_tac @{thms adm_lemmas} i)
*}

lemma least_FIX: "f(p) = p ==> FIX(f) << p"
  apply (tactic {* induct_tac @{context} "f" 1 *})
  apply (rule minimal)
  apply (intro strip)
  apply (erule subst)
  apply (erule less_ap_term)
  done

lemma lfp_is_FIX:
  assumes 1: "f(p) = p"
    and 2: "ALL q. f(q)=q --> p << q"
  shows "p = FIX(f)"
  apply (rule less_anti_sym)
  apply (rule 2 [THEN spec, THEN mp])
  apply (rule FIX_eq)
  apply (rule least_FIX)
  apply (rule 1)
  done


lemma FIX_pair: "<FIX(f),FIX(g)> = FIX(%p.<f(FST(p)),g(SND(p))>)"
  apply (rule lfp_is_FIX)
  apply (simp add: FIX_eq [of f] FIX_eq [of g])
  apply (intro strip)
  apply (simp add: PROD_less)
  apply (rule conjI)
  apply (rule least_FIX)
  apply (erule subst, rule FST [symmetric])
  apply (rule least_FIX)
  apply (erule subst, rule SND [symmetric])
  done

lemma FIX1: "FIX(f) = FST(FIX(%p. <f(FST(p)),g(SND(p))>))"
  by (rule FIX_pair [unfolded PROD_eq FST SND, THEN conjunct1])

lemma FIX2: "FIX(g) = SND(FIX(%p. <f(FST(p)),g(SND(p))>))"
  by (rule FIX_pair [unfolded PROD_eq FST SND, THEN conjunct2])

lemma induct2:
  assumes 1: "adm(%p. P(FST(p),SND(p)))"
    and 2: "P(UU::'a,UU::'b)"
    and 3: "ALL x y. P(x,y) --> P(f(x),g(y))"
  shows "P(FIX(f),FIX(g))"
  apply (rule FIX1 [THEN ssubst, of _ f g])
  apply (rule FIX2 [THEN ssubst, of _ f g])
  apply (rule induct [where ?f = "%x. <f(FST(x)),g(SND(x))>"])
  apply (rule 1)
  apply simp
  apply (rule 2)
  apply (simp add: expand_all_PROD)
  apply (rule 3)
  done

ML {*
fun induct2_tac ctxt (f, g) i =
  res_inst_tac ctxt [(("f", 0), f), (("g", 0), g)] @{thm induct2} i THEN
  REPEAT(resolve_tac @{thms adm_lemmas} i)
*}

end
