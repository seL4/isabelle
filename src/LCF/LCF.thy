(*  Title:      LCF/LCF.thy
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge
*)

section \<open>LCF on top of First-Order Logic\<close>

theory LCF
imports FOL
begin

text \<open>This theory is based on Lawrence Paulson's book Logic and Computation.\<close>

subsection \<open>Natural Deduction Rules for LCF\<close>

class cpo = "term"
default_sort cpo

typedecl tr
typedecl void
typedecl ('a,'b) prod  (infixl \<open>*\<close> 6)
typedecl ('a,'b) sum  (infixl \<open>+\<close> 5)

instance "fun" :: (cpo, cpo) cpo ..
instance prod :: (cpo, cpo) cpo ..
instance sum :: (cpo, cpo) cpo ..
instance tr :: cpo ..
instance void :: cpo ..

consts
 UU     :: "'a"
 TT     :: "tr"
 FF     :: "tr"
 FIX    :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
 FST    :: "'a*'b \<Rightarrow> 'a"
 SND    :: "'a*'b \<Rightarrow> 'b"
 INL    :: "'a \<Rightarrow> 'a+'b"
 INR    :: "'b \<Rightarrow> 'a+'b"
 WHEN   :: "['a\<Rightarrow>'c, 'b\<Rightarrow>'c, 'a+'b] \<Rightarrow> 'c"
 adm    :: "('a \<Rightarrow> o) \<Rightarrow> o"
 VOID   :: "void"               (\<open>'(')\<close>)
 PAIR   :: "['a,'b] \<Rightarrow> 'a*'b"   (\<open>(\<open>indent=1 notation=\<open>mixfix PAIR\<close>\<close><_,/_>)\<close> [0,0] 100)
 COND   :: "[tr,'a,'a] \<Rightarrow> 'a"   (\<open>(\<open>notation=\<open>mixfix COND\<close>\<close>_ \<Rightarrow>/ (_ |/ _))\<close> [60,60,60] 60)
 less   :: "['a,'a] \<Rightarrow> o"       (infixl \<open><<\<close> 50)

axiomatization where
  (** DOMAIN THEORY **)

  eq_def:        "x=y == x << y \<and> y << x" and

  less_trans:    "\<lbrakk>x << y; y << z\<rbrakk> \<Longrightarrow> x << z" and

  less_ext:      "(\<forall>x. f(x) << g(x)) \<Longrightarrow> f << g" and

  mono:          "\<lbrakk>f << g; x << y\<rbrakk> \<Longrightarrow> f(x) << g(y)" and

  minimal:       "UU << x" and

  FIX_eq:        "\<And>f. f(FIX(f)) = FIX(f)"

axiomatization where
  (** TR **)

  tr_cases:      "p=UU \<or> p=TT \<or> p=FF" and

  not_TT_less_FF: "\<not> TT << FF" and
  not_FF_less_TT: "\<not> FF << TT" and
  not_TT_less_UU: "\<not> TT << UU" and
  not_FF_less_UU: "\<not> FF << UU" and

  COND_UU:       "UU \<Rightarrow> x | y  =  UU" and
  COND_TT:       "TT \<Rightarrow> x | y  =  x" and
  COND_FF:       "FF \<Rightarrow> x | y  =  y"

axiomatization where
  (** PAIRS **)

  surj_pairing:  "<FST(z),SND(z)> = z" and

  FST:   "FST(<x,y>) = x" and
  SND:   "SND(<x,y>) = y"

axiomatization where
  (*** STRICT SUM ***)

  INL_DEF: "\<not>x=UU \<Longrightarrow> \<not>INL(x)=UU" and
  INR_DEF: "\<not>x=UU \<Longrightarrow> \<not>INR(x)=UU" and

  INL_STRICT: "INL(UU) = UU" and
  INR_STRICT: "INR(UU) = UU" and

  WHEN_UU:  "WHEN(f,g,UU) = UU" and
  WHEN_INL: "\<not>x=UU \<Longrightarrow> WHEN(f,g,INL(x)) = f(x)" and
  WHEN_INR: "\<not>x=UU \<Longrightarrow> WHEN(f,g,INR(x)) = g(x)" and

  SUM_EXHAUSTION:
    "z = UU \<or> (\<exists>x. \<not>x=UU \<and> z = INL(x)) \<or> (\<exists>y. \<not>y=UU \<and> z = INR(y))"

axiomatization where
  (** VOID **)

  void_cases:    "(x::void) = UU"

  (** INDUCTION **)

axiomatization where
  induct: "\<lbrakk>adm(P); P(UU); \<forall>x. P(x) \<longrightarrow> P(f(x))\<rbrakk> \<Longrightarrow> P(FIX(f))"

axiomatization where
  (** Admissibility / Chain Completeness **)
  (* All rules can be found on pages 199--200 of Larry's LCF book.
     Note that "easiness" of types is not taken into account
     because it cannot be expressed schematically; flatness could be. *)

  adm_less:      "\<And>t u. adm(\<lambda>x. t(x) << u(x))" and
  adm_not_less:  "\<And>t u. adm(\<lambda>x.\<not> t(x) << u)" and
  adm_not_free:  "\<And>A. adm(\<lambda>x. A)" and
  adm_subst:     "\<And>P t. adm(P) \<Longrightarrow> adm(\<lambda>x. P(t(x)))" and
  adm_conj:      "\<And>P Q. \<lbrakk>adm(P); adm(Q)\<rbrakk> \<Longrightarrow> adm(\<lambda>x. P(x)\<and>Q(x))" and
  adm_disj:      "\<And>P Q. \<lbrakk>adm(P); adm(Q)\<rbrakk> \<Longrightarrow> adm(\<lambda>x. P(x)\<or>Q(x))" and
  adm_imp:       "\<And>P Q. \<lbrakk>adm(\<lambda>x.\<not>P(x)); adm(Q)\<rbrakk> \<Longrightarrow> adm(\<lambda>x. P(x)\<longrightarrow>Q(x))" and
  adm_all:       "\<And>P. (\<And>y. adm(P(y))) \<Longrightarrow> adm(\<lambda>x. \<forall>y. P(y,x))"


lemma eq_imp_less1: "x = y \<Longrightarrow> x << y"
  by (simp add: eq_def)

lemma eq_imp_less2: "x = y \<Longrightarrow> y << x"
  by (simp add: eq_def)

lemma less_refl [simp]: "x << x"
  apply (rule eq_imp_less1)
  apply (rule refl)
  done

lemma less_anti_sym: "\<lbrakk>x << y; y << x\<rbrakk> \<Longrightarrow> x=y"
  by (simp add: eq_def)

lemma ext: "(\<And>x::'a::cpo. f(x)=(g(x)::'b::cpo)) \<Longrightarrow> (\<lambda>x. f(x))=(\<lambda>x. g(x))"
  apply (rule less_anti_sym)
  apply (rule less_ext)
  apply simp
  apply simp
  done

lemma cong: "\<lbrakk>f = g; x = y\<rbrakk> \<Longrightarrow> f(x)=g(y)"
  by simp

lemma less_ap_term: "x << y \<Longrightarrow> f(x) << f(y)"
  by (rule less_refl [THEN mono])

lemma less_ap_thm: "f << g \<Longrightarrow> f(x) << g(x)"
  by (rule less_refl [THEN [2] mono])

lemma ap_term: "(x::'a::cpo) = y \<Longrightarrow> (f(x)::'b::cpo) = f(y)"
  apply (rule cong [OF refl])
  apply simp
  done

lemma ap_thm: "f = g \<Longrightarrow> f(x) = g(x)"
  apply (erule cong)
  apply (rule refl)
  done


lemma UU_abs: "(\<lambda>x::'a::cpo. UU) = UU"
  apply (rule less_anti_sym)
  prefer 2
  apply (rule minimal)
  apply (rule less_ext)
  apply (rule allI)
  apply (rule minimal)
  done

lemma UU_app: "UU(x) = UU"
  by (rule UU_abs [symmetric, THEN ap_thm])

lemma less_UU: "x << UU \<Longrightarrow> x=UU"
  apply (rule less_anti_sym)
  apply assumption
  apply (rule minimal)
  done

lemma tr_induct: "\<lbrakk>P(UU); P(TT); P(FF)\<rbrakk> \<Longrightarrow> \<forall>b. P(b)"
  apply (rule allI)
  apply (rule mp)
  apply (rule_tac [2] p = b in tr_cases)
  apply blast
  done

lemma Contrapos: "\<not> B \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> \<not>A"
  by blast

lemma not_less_imp_not_eq1: "\<not> x << y \<Longrightarrow> x \<noteq> y"
  apply (erule Contrapos)
  apply simp
  done

lemma not_less_imp_not_eq2: "\<not> y << x \<Longrightarrow> x \<noteq> y"
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
    "\<forall>b. P(b\<Rightarrow>x|y) \<longleftrightarrow> (b=UU\<longrightarrow>P(UU)) \<and> (b=TT\<longrightarrow>P(x)) \<and> (b=FF\<longrightarrow>P(y))"
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
  "\<lbrakk>x = UU \<longrightarrow> P(UU); x = TT \<longrightarrow> P(xa); x = FF \<longrightarrow> P(y)\<rbrakk> \<Longrightarrow> P(x \<Rightarrow> xa | y)"
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


subsection \<open>Ordered pairs and products\<close>

lemma expand_all_PROD: "(\<forall>p. P(p)) \<longleftrightarrow> (\<forall>x y. P(<x,y>))"
  apply (rule iffI)
  apply blast
  apply (rule allI)
  apply (rule surj_pairing [THEN subst])
  apply blast
  done

lemma PROD_less: "(p::'a*'b) << q \<longleftrightarrow> FST(p) << FST(q) \<and> SND(p) << SND(q)"
  apply (rule iffI)
  apply (rule conjI)
  apply (erule less_ap_term)
  apply (erule less_ap_term)
  apply (erule conjE)
  apply (rule surj_pairing [of p, THEN subst])
  apply (rule surj_pairing [of q, THEN subst])
  apply (rule mono, erule less_ap_term, assumption)
  done

lemma PROD_eq: "p=q \<longleftrightarrow> FST(p)=FST(q) \<and> SND(p)=SND(q)"
  apply (rule iffI)
  apply simp
  apply (unfold eq_def)
  apply (simp add: PROD_less)
  done

lemma PAIR_less [simp]: "<a,b> << <c,d> \<longleftrightarrow> a<<c \<and> b<<d"
  by (simp add: PROD_less)

lemma PAIR_eq [simp]: "<a,b> = <c,d> \<longleftrightarrow> a=c \<and> b=d"
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


subsection \<open>Fixedpoint theory\<close>

lemma adm_eq: "adm(\<lambda>x. t(x)=(u(x)::'a::cpo))"
  apply (unfold eq_def)
  apply (rule adm_conj adm_less)+
  done

lemma adm_not_not: "adm(P) \<Longrightarrow> adm(\<lambda>x. \<not> \<not> P(x))"
  by simp

lemma not_eq_TT: "\<forall>p. \<not>p=TT \<longleftrightarrow> (p=FF \<or> p=UU)"
  and not_eq_FF: "\<forall>p. \<not>p=FF \<longleftrightarrow> (p=TT \<or> p=UU)"
  and not_eq_UU: "\<forall>p. \<not>p=UU \<longleftrightarrow> (p=TT \<or> p=FF)"
  by (rule tr_induct, simp_all)+

lemma adm_not_eq_tr: "\<forall>p::tr. adm(\<lambda>x. \<not>t(x)=p)"
  apply (rule tr_induct)
  apply (simp_all add: not_eq_TT not_eq_FF not_eq_UU)
  apply (rule adm_disj adm_eq)+
  done

lemmas adm_lemmas =
  adm_not_free adm_eq adm_less adm_not_less
  adm_not_eq_tr adm_conj adm_disj adm_imp adm_all

method_setup induct = \<open>
  Scan.lift Parse.embedded_inner_syntax >> (fn v => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      Rule_Insts.res_inst_tac ctxt [((("f", 0), Position.none), v)] [] @{thm induct} i THEN
      REPEAT (resolve_tac ctxt @{thms adm_lemmas} i)))
\<close>

lemma least_FIX: "f(p) = p \<Longrightarrow> FIX(f) << p"
  apply (induct f)
  apply (rule minimal)
  apply (intro strip)
  apply (erule subst)
  apply (erule less_ap_term)
  done

lemma lfp_is_FIX:
  assumes 1: "f(p) = p"
    and 2: "\<forall>q. f(q)=q \<longrightarrow> p << q"
  shows "p = FIX(f)"
  apply (rule less_anti_sym)
  apply (rule 2 [THEN spec, THEN mp])
  apply (rule FIX_eq)
  apply (rule least_FIX)
  apply (rule 1)
  done


lemma FIX_pair: "<FIX(f),FIX(g)> = FIX(\<lambda>p.<f(FST(p)),g(SND(p))>)"
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

lemma FIX1: "FIX(f) = FST(FIX(\<lambda>p. <f(FST(p)),g(SND(p))>))"
  by (rule FIX_pair [unfolded PROD_eq FST SND, THEN conjunct1])

lemma FIX2: "FIX(g) = SND(FIX(\<lambda>p. <f(FST(p)),g(SND(p))>))"
  by (rule FIX_pair [unfolded PROD_eq FST SND, THEN conjunct2])

lemma induct2:
  assumes 1: "adm(\<lambda>p. P(FST(p),SND(p)))"
    and 2: "P(UU::'a,UU::'b)"
    and 3: "\<forall>x y. P(x,y) \<longrightarrow> P(f(x),g(y))"
  shows "P(FIX(f),FIX(g))"
  apply (rule FIX1 [THEN ssubst, of _ f g])
  apply (rule FIX2 [THEN ssubst, of _ f g])
  apply (rule induct [where ?f = "\<lambda>x. <f(FST(x)),g(SND(x))>"])
  apply (rule 1)
  apply simp
  apply (rule 2)
  apply (simp add: expand_all_PROD)
  apply (rule 3)
  done

ML \<open>
fun induct2_tac ctxt (f, g) i =
  Rule_Insts.res_inst_tac ctxt
    [((("f", 0), Position.none), f), ((("g", 0), Position.none), g)] [] @{thm induct2} i THEN
  REPEAT(resolve_tac ctxt @{thms adm_lemmas} i)
\<close>

end
