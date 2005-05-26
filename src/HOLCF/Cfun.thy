(*  Title:      HOLCF/Cfun.thy
    ID:         $Id$
    Author:     Franz Regensburger

Definition of the type ->  of continuous functions.
*)

header {* The type of continuous functions *}

theory Cfun
imports TypedefPcpo
begin

defaultsort cpo

subsection {* Definition of continuous function type *}

typedef (CFun)  ('a, 'b) "->" (infixr 0) = "{f::'a => 'b. cont f}"
by (rule exI, rule CfunI)

syntax
	Rep_CFun  :: "('a -> 'b) => ('a => 'b)" ("_$_" [999,1000] 999)
                                                (* application      *)
        Abs_CFun  :: "('a => 'b) => ('a -> 'b)" (binder "LAM " 10)
                                                (* abstraction      *)
        less_cfun :: "[('a -> 'b),('a -> 'b)]=>bool"

syntax (xsymbols)
  "->"		:: "[type, type] => type"      ("(_ \<rightarrow>/ _)" [1,0]0)
  "LAM "	:: "[idts, 'a => 'b] => ('a -> 'b)"
					("(3\<Lambda>_./ _)" [0, 10] 10)
  Rep_CFun      :: "('a -> 'b) => ('a => 'b)"  ("(_\<cdot>_)" [999,1000] 999)

syntax (HTML output)
  Rep_CFun      :: "('a -> 'b) => ('a => 'b)"  ("(_\<cdot>_)" [999,1000] 999)

text {*
  Derive old type definition rules for @{term Abs_CFun} \& @{term Rep_CFun}.
  @{term Rep_CFun} and @{term Abs_CFun} should be replaced by
  @{term Rep_Cfun} and @{term Abs_Cfun} in future.
*}

lemma Rep_Cfun: "Rep_CFun fo : CFun"
by (rule Rep_CFun)

lemma Rep_Cfun_inverse: "Abs_CFun (Rep_CFun fo) = fo"
by (rule Rep_CFun_inverse)

lemma Abs_Cfun_inverse: "f:CFun==>Rep_CFun(Abs_CFun f)=f"
by (erule Abs_CFun_inverse)

text {* Additional lemma about the isomorphism between
        @{typ "'a -> 'b"} and @{term Cfun} *}

lemma Abs_Cfun_inverse2: "cont f ==> Rep_CFun (Abs_CFun f) = f"
apply (rule Abs_Cfun_inverse)
apply (unfold CFun_def)
apply (erule mem_Collect_eq [THEN ssubst])
done

text {* Simplification of application *}

lemma Cfunapp2: "cont f ==> (Abs_CFun f)$x = f x"
by (erule Abs_Cfun_inverse2 [THEN fun_cong])

text {* Beta - equality for continuous functions *}

lemma beta_cfun: "cont(c1) ==> (LAM x .c1 x)$u = c1 u"
by (rule Cfunapp2)

text {* Eta - equality for continuous functions *}

lemma eta_cfun: "(LAM x. f$x) = f"
by (rule Rep_CFun_inverse)

subsection {* Class instances *}

instance "->"  :: (cpo, cpo) sq_ord ..

defs (overloaded)
  less_cfun_def: "(op <<) == (% fo1 fo2. Rep_CFun fo1 << Rep_CFun fo2 )"

lemma adm_CFun: "adm (\<lambda>f. f \<in> CFun)"
by (simp add: CFun_def, rule admI, rule cont_lub_fun)

lemma UU_CFun: "\<bottom> \<in> CFun"
by (simp add: CFun_def inst_fun_pcpo cont_const)

instance "->" :: (cpo, cpo) po
by (rule typedef_po [OF type_definition_CFun less_cfun_def])

instance "->" :: (cpo, cpo) cpo
by (rule typedef_cpo [OF type_definition_CFun less_cfun_def adm_CFun])

instance "->" :: (cpo, pcpo) pcpo
by (rule typedef_pcpo_UU [OF type_definition_CFun less_cfun_def UU_CFun])

lemmas cont_Rep_CFun =
  typedef_cont_Rep [OF type_definition_CFun less_cfun_def adm_CFun]

lemmas cont_Abs_CFun = 
  typedef_cont_Abs [OF type_definition_CFun less_cfun_def adm_CFun]

lemmas strict_Rep_CFun =
  typedef_strict_Rep [OF type_definition_CFun less_cfun_def UU_CFun]

lemmas strict_Abs_CFun =
  typedef_strict_Abs [OF type_definition_CFun less_cfun_def UU_CFun]

text {* for compatibility with old HOLCF-Version *}
lemma inst_cfun_po: "(op <<)=(%f1 f2. Rep_CFun f1 << Rep_CFun f2)"
apply (fold less_cfun_def)
apply (rule refl)
done

text {* lemmas about application of continuous functions *}

lemma cfun_cong: "[| f=g; x=y |] ==> f$x = g$y"
by simp

lemma cfun_fun_cong: "f=g ==> f$x = g$x"
by simp

lemma cfun_arg_cong: "x=y ==> f$x = f$y"
by simp

text {* access to @{term less_cfun} in class po *}

lemma less_cfun: "( f1 << f2 ) = (Rep_CFun(f1) << Rep_CFun(f2))"
by (simp add: inst_cfun_po)

subsection {* Type @{typ "'a -> 'b"} is pointed *}

lemma minimal_cfun: "Abs_CFun(% x. UU) << f"
apply (subst less_cfun)
apply (subst Abs_Cfun_inverse2)
apply (rule cont_const)
apply (rule minimal_fun)
done

lemmas UU_cfun_def = minimal_cfun [THEN minimal2UU, symmetric, standard]

lemma least_cfun: "? x::'a->'b::pcpo.!y. x<<y"
apply (rule_tac x = "Abs_CFun (% x. UU) " in exI)
apply (rule minimal_cfun [THEN allI])
done

subsection {* Monotonicity of application *}

text {*
  @{term Rep_CFun} yields continuous functions in @{typ "'a => 'b"}.
  This is continuity of @{term Rep_CFun} in its 'second' argument:
  @{prop "cont_Rep_CFun2 ==> monofun_Rep_CFun2 & contlub_Rep_CFun2"}
*}

lemma cont_Rep_CFun2: "cont (Rep_CFun fo)"
apply (rule_tac P = "cont" in CollectD)
apply (fold CFun_def)
apply (rule Rep_Cfun)
done

lemmas monofun_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2mono, standard]
 -- {* @{thm monofun_Rep_CFun2} *} (* monofun(Rep_CFun(?fo)) *)

lemmas contlub_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2contlub, standard]
 -- {* @{thm contlub_Rep_CFun2} *} (* contlub(Rep_CFun(?fo)) *)

text {* expanded thms @{thm [source] cont_Rep_CFun2}, @{thm [source] contlub_Rep_CFun2} look nice with mixfix syntax *}

lemmas cont_cfun_arg = cont_Rep_CFun2 [THEN contE, THEN spec, THEN mp]
  -- {* @{thm cont_cfun_arg} *} (* chain(x1) ==> range (%i. fo3$(x1 i)) <<| fo3$(lub (range ?x1))    *)
 
lemmas contlub_cfun_arg = contlub_Rep_CFun2 [THEN contlubE, THEN spec, THEN mp]
 -- {* @{thm contlub_cfun_arg} *} (* chain(?x1) ==> ?fo4$(lub (range ?x1)) = lub (range (%i. ?fo4$(?x1 i))) *)

text {* @{term Rep_CFun} is monotone in its 'first' argument *}

lemma monofun_Rep_CFun1: "monofun(Rep_CFun)"
by (rule cont_Rep_CFun [THEN cont2mono])

text {* monotonicity of application @{term Rep_CFun} in mixfix syntax @{text "[_]_"} *}

lemma monofun_cfun_fun: "f1 << f2 ==> f1$x << f2$x"
apply (rule_tac x = "x" in spec)
apply (rule less_fun [THEN subst])
apply (erule monofun_Rep_CFun1 [THEN monofunE [rule_format]])
done

lemmas monofun_cfun_arg = monofun_Rep_CFun2 [THEN monofunE [rule_format], standard]
 -- {* @{thm monofun_cfun_arg} *} (* ?x2 << ?x1 ==> ?fo5$?x2 << ?fo5$?x1 *)

lemma chain_monofun: "chain Y ==> chain (%i. f\<cdot>(Y i))"
apply (rule chainI)
apply (rule monofun_cfun_arg)
apply (erule chainE)
done

text {* monotonicity of @{term Rep_CFun} in both arguments in mixfix syntax @{text "[_]_"} *}

lemma monofun_cfun: "[|f1<<f2;x1<<x2|] ==> f1$x1 << f2$x2"
apply (rule trans_less)
apply (erule monofun_cfun_arg)
apply (erule monofun_cfun_fun)
done

lemma strictI: "f$x = UU ==> f$UU = UU"
apply (rule eq_UU_iff [THEN iffD2])
apply (erule subst)
apply (rule minimal [THEN monofun_cfun_arg])
done

subsection {* Type @{typ "'a -> 'b"} is a cpo *}

text {* ch2ch - rules for the type @{typ "'a -> 'b"} use MF2 lemmas from Cont.thy *}

lemma ch2ch_Rep_CFunR: "chain(Y) ==> chain(%i. f$(Y i))"
by (erule monofun_Rep_CFun2 [THEN ch2ch_MF2R])

lemmas ch2ch_Rep_CFunL = monofun_Rep_CFun1 [THEN ch2ch_MF2L, standard]
 -- {* @{thm ch2ch_Rep_CFunL} *} (* chain(?F) ==> chain (%i. ?F i$?x) *)

text {* the lub of a chain of continous functions is monotone: uses MF2 lemmas from Cont.thy *}

lemma lub_cfun_mono: "chain(F) ==> monofun(% x. lub(range(% j.(F j)$x)))"
apply (rule lub_MF2_mono)
apply (rule monofun_Rep_CFun1)
apply (rule monofun_Rep_CFun2 [THEN allI])
apply assumption
done

text {* a lemma about the exchange of lubs for type @{typ "'a -> 'b"}: uses MF2 lemmas from Cont.thy *}

lemma ex_lubcfun: "[| chain(F); chain(Y) |] ==> 
                lub(range(%j. lub(range(%i. F(j)$(Y i))))) = 
                lub(range(%i. lub(range(%j. F(j)$(Y i)))))"
apply (rule ex_lubMF2)
apply (rule monofun_Rep_CFun1)
apply (rule monofun_Rep_CFun2 [THEN allI])
apply assumption
apply assumption
done

text {* the lub of a chain of cont. functions is continuous *}

lemma cont_lubcfun: "chain(F) ==> cont(% x. lub(range(% j. F(j)$x)))"
apply (rule monocontlub2cont)
apply (erule lub_cfun_mono)
apply (rule contlubI [rule_format])
apply (subst contlub_cfun_arg [THEN ext])
apply assumption
apply (erule ex_lubcfun)
apply assumption
done

text {* type @{typ "'a -> 'b"} is chain complete *}

lemma lub_cfun: "chain(CCF) ==> range(CCF) <<| (LAM x. lub(range(% i. CCF(i)$x)))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst less_cfun)
apply (subst Abs_Cfun_inverse2)
apply (erule cont_lubcfun)
apply (rule lub_fun [THEN is_lubD1, THEN ub_rangeD])
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (subst less_cfun)
apply (subst Abs_Cfun_inverse2)
apply (erule cont_lubcfun)
apply (rule lub_fun [THEN is_lub_lub])
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (erule monofun_Rep_CFun1 [THEN ub2ub_monofun])
done

lemmas thelub_cfun = lub_cfun [THEN thelubI, standard]
 -- {* @{thm thelub_cfun} *} (* 
chain(?CCF1) ==>  lub (range ?CCF1) = (LAM x. lub (range (%i. ?CCF1 i$x)))
*)

subsection {* Miscellaneous *}

text {* Extensionality in @{typ "'a -> 'b"} *}

lemma ext_cfun: "(!!x. f$x = g$x) ==> f = g"
apply (rule Rep_CFun_inject [THEN iffD1])
apply (rule ext)
apply simp
done

text {* Monotonicity of @{term Abs_CFun} *}

lemma semi_monofun_Abs_CFun: "[| cont(f); cont(g); f<<g|] ==> Abs_CFun(f)<<Abs_CFun(g)"
by (simp add: less_cfun Abs_Cfun_inverse2)

text {* Extensionality wrt. @{term "op <<"} in @{typ "'a -> 'b"} *}

lemma less_cfun2: "(!!x. f$x << g$x) ==> f << g"
apply (rule_tac t = "f" in Rep_Cfun_inverse [THEN subst])
apply (rule_tac t = "g" in Rep_Cfun_inverse [THEN subst])
apply (rule semi_monofun_Abs_CFun)
apply (rule cont_Rep_CFun2)
apply (rule cont_Rep_CFun2)
apply (rule less_fun [THEN iffD2])
apply simp
done

text {* for compatibility with old HOLCF-Version *}
lemma inst_cfun_pcpo: "UU = Abs_CFun(%x. UU)"
apply (simp add: UU_def UU_cfun_def)
done

subsection {* Continuity of application *}

text {* the contlub property for @{term Rep_CFun} its 'first' argument *}

lemma contlub_Rep_CFun1: "contlub(Rep_CFun)"
by (rule cont_Rep_CFun [THEN cont2contlub])

text {* the cont property for @{term Rep_CFun} in its first argument *}

lemma cont_Rep_CFun1: "cont(Rep_CFun)"
by (rule cont_Rep_CFun)

text {* contlub, cont properties of @{term Rep_CFun} in its first argument in mixfix @{text "_[_]"} *}

lemma contlub_cfun_fun: 
"chain(FY) ==> 
  lub(range FY)$x = lub(range (%i. FY(i)$x))"
apply (rule trans)
apply (erule contlub_Rep_CFun1 [THEN contlubE, THEN spec, THEN mp, THEN fun_cong])
apply (subst thelub_fun)
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (rule refl)
done

lemma cont_cfun_fun: 
"chain(FY) ==> 
  range(%i. FY(i)$x) <<| lub(range FY)$x"
apply (rule thelubE)
apply (erule ch2ch_Rep_CFunL)
apply (erule contlub_cfun_fun [symmetric])
done

text {* contlub, cont  properties of @{term Rep_CFun} in both argument in mixfix @{text "_[_]"} *}

lemma contlub_cfun: 
"[|chain(FY);chain(TY)|] ==> 
  (lub(range FY))$(lub(range TY)) = lub(range(%i. FY(i)$(TY i)))"
apply (rule contlub_CF2)
apply (rule cont_Rep_CFun1)
apply (rule allI)
apply (rule cont_Rep_CFun2)
apply assumption
apply assumption
done

lemma cont_cfun: 
"[|chain(FY);chain(TY)|] ==> 
  range(%i.(FY i)$(TY i)) <<| (lub (range FY))$(lub(range TY))"
apply (rule thelubE)
apply (rule monofun_Rep_CFun1 [THEN ch2ch_MF2LR])
apply (rule allI)
apply (rule monofun_Rep_CFun2)
apply assumption
apply assumption
apply (erule contlub_cfun [symmetric])
apply assumption
done

text {* cont2cont lemma for @{term Rep_CFun} *}

lemma cont2cont_Rep_CFun: "[|cont(%x. ft x);cont(%x. tt x)|] ==> cont(%x. (ft x)$(tt x))"
apply (best intro: cont2cont_app2 cont_const cont_Rep_CFun1 cont_Rep_CFun2)
done

text {* cont2mono Lemma for @{term "%x. LAM y. c1(x)(y)"} *}

lemma cont2mono_LAM:
assumes p1: "!!x. cont(c1 x)"
assumes p2: "!!y. monofun(%x. c1 x y)"
shows "monofun(%x. LAM y. c1 x y)"
apply (rule monofunI [rule_format])
apply (rule less_cfun2)
apply (simp add: beta_cfun p1)
apply (erule p2 [THEN monofunE [rule_format]])
done

text {* cont2cont Lemma for @{term "%x. LAM y. c1 x y"} *}

lemma cont2cont_LAM:
assumes p1: "!!x. cont(c1 x)"
assumes p2: "!!y. cont(%x. c1 x y)"
shows "cont(%x. LAM y. c1 x y)"
apply (rule cont_Abs_CFun)
apply (simp add: p1 CFun_def)
apply (simp add: p2 cont2cont_CF1L_rev)
done

text {* cont2cont Lemma for @{term "%x. LAM y. c1 x$y"} *}

lemma cont2cont_eta: "cont c1 ==> cont (%x. LAM y. c1 x$y)"
by (simp only: eta_cfun)

text {* cont2cont tactic *}

lemmas cont_lemmas1 =
  cont_const cont_id cont_Rep_CFun2 cont2cont_Rep_CFun cont2cont_LAM

text {*
  Continuity simproc by Brian Huffman.
  Given the term @{term "cont f"}, the procedure tries to
  construct the theorem @{prop "cont f == True"}. If this
  theorem cannot be completely solved by the introduction
  rules, then the procedure returns a conditional rewrite
  rule with the unsolved subgoals as premises.
*}

ML_setup {*
local
  val rules = thms "cont_lemmas1";
  fun solve_cont sg _ t =
    let val tr = instantiate' [] [SOME (cterm_of sg t)] Eq_TrueI;
        val tac = REPEAT_ALL_NEW (resolve_tac rules) 1;
    in Option.map fst (Seq.pull (tac tr)) end;
in
  val cont_proc = Simplifier.simproc (Theory.sign_of (the_context ()))
        "continuity" ["cont f"] solve_cont;
end;
Addsimprocs [cont_proc];
*}

text {* HINT: @{text cont_tac} is now installed in simplifier in Lift.ML ! *}

(*val cont_tac = (fn i => (resolve_tac cont_lemmas i));*)
(*val cont_tacR = (fn i => (REPEAT (cont_tac i)));*)

text {* function application @{text "_[_]"} is strict in its first arguments *}

lemma strict_Rep_CFun1 [simp]: "\<bottom>\<cdot>x = \<bottom>"
by (simp add: inst_cfun_pcpo beta_cfun)

text {* Instantiate the simplifier *}

declare beta_cfun [simp]

text {* some lemmata for functions with flat/chfin domain/range types *}

lemma chfin_Rep_CFunR: "chain (Y::nat => 'a::cpo->'b::chfin)  
      ==> !s. ? n. lub(range(Y))$s = Y n$s"
apply (rule allI)
apply (subst contlub_cfun_fun)
apply assumption
apply (fast intro!: thelubI chfin lub_finch2 chfin2finch ch2ch_Rep_CFunL)
done

subsection {* Continuous injection-retraction pairs *}

text {* Continuous retractions are strict. *}

lemma retraction_strict:
  "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> f\<cdot>\<bottom> = \<bottom>"
apply (rule UU_I)
apply (drule_tac x="\<bottom>" in spec)
apply (erule subst)
apply (rule monofun_cfun_arg)
apply (rule minimal)
done

lemma injection_eq:
  "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> (g\<cdot>x = g\<cdot>y) = (x = y)"
apply (rule iffI)
apply (drule_tac f=f in cfun_arg_cong)
apply simp
apply simp
done

lemma injection_defined_rev:
  "\<lbrakk>\<forall>x. f\<cdot>(g\<cdot>x) = x; g\<cdot>z = \<bottom>\<rbrakk> \<Longrightarrow> z = \<bottom>"
apply (drule_tac f=f in cfun_arg_cong)
apply (simp add: retraction_strict)
done

lemma injection_defined:
  "\<lbrakk>\<forall>x. f\<cdot>(g\<cdot>x) = x; z \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> g\<cdot>z \<noteq> \<bottom>"
by (erule contrapos_nn, rule injection_defined_rev)

text {* propagation of flatness and chain-finiteness by retractions *}

lemma chfin2chfin:
  "\<forall>y. (f::'a::chfin \<rightarrow> 'b)\<cdot>(g\<cdot>y) = y
    \<Longrightarrow> \<forall>Y::nat \<Rightarrow> 'b. chain Y \<longrightarrow> (\<exists>n. max_in_chain n Y)"
apply clarify
apply (drule_tac f=g in chain_monofun)
apply (drule chfin [rule_format])
apply (unfold max_in_chain_def)
apply (simp add: injection_eq)
done

lemma flat2flat:
  "\<forall>y. (f::'a::flat \<rightarrow> 'b::pcpo)\<cdot>(g\<cdot>y) = y
    \<Longrightarrow> \<forall>x y::'b. x \<sqsubseteq> y \<longrightarrow> x = \<bottom> \<or> x = y"
apply clarify
apply (drule_tac fo=g in monofun_cfun_arg)
apply (drule ax_flat [rule_format])
apply (erule disjE)
apply (simp add: injection_defined_rev)
apply (simp add: injection_eq)
done

text {* a result about functions with flat codomain *}

lemma flat_eqI: "\<lbrakk>(x::'a::flat) \<sqsubseteq> y; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> x = y"
by (drule ax_flat [rule_format], simp)

lemma flat_codom:
  "f\<cdot>x = (c::'b::flat) \<Longrightarrow> f\<cdot>\<bottom> = \<bottom> \<or> (\<forall>z. f\<cdot>z = c)"
apply (case_tac "f\<cdot>x = \<bottom>")
apply (rule disjI1)
apply (rule UU_I)
apply (erule_tac t="\<bottom>" in subst)
apply (rule minimal [THEN monofun_cfun_arg])
apply clarify
apply (rule_tac a = "f\<cdot>\<bottom>" in refl [THEN box_equals])
apply (erule minimal [THEN monofun_cfun_arg, THEN flat_eqI])
apply (erule minimal [THEN monofun_cfun_arg, THEN flat_eqI])
done


subsection {* Identity and composition *}

consts
  ID      :: "'a \<rightarrow> 'a"
  cfcomp  :: "('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'c"

syntax  "@oo" :: "['b \<rightarrow> 'c, 'a \<rightarrow> 'b] \<Rightarrow> 'a \<rightarrow> 'c" (infixr "oo" 100)
     
translations  "f1 oo f2" == "cfcomp$f1$f2"

defs
  ID_def: "ID \<equiv> (\<Lambda> x. x)"
  oo_def: "cfcomp \<equiv> (\<Lambda> f g x. f\<cdot>(g\<cdot>x))" 

lemma ID1 [simp]: "ID\<cdot>x = x"
by (simp add: ID_def)

lemma cfcomp1: "(f oo g) = (\<Lambda> x. f\<cdot>(g\<cdot>x))"
by (simp add: oo_def)

lemma cfcomp2 [simp]: "(f oo g)\<cdot>x = f\<cdot>(g\<cdot>x)"
by (simp add: cfcomp1)

text {*
  Show that interpretation of (pcpo,@{text "_->_"}) is a category.
  The class of objects is interpretation of syntactical class pcpo.
  The class of arrows  between objects @{typ 'a} and @{typ 'b} is interpret. of @{typ "'a -> 'b"}.
  The identity arrow is interpretation of @{term ID}.
  The composition of f and g is interpretation of @{text "oo"}.
*}

lemma ID2 [simp]: "f oo ID = f"
by (rule ext_cfun, simp)

lemma ID3 [simp]: "ID oo f = f"
by (rule ext_cfun, simp)

lemma assoc_oo: "f oo (g oo h) = (f oo g) oo h"
by (rule ext_cfun, simp)


subsection {* Strictified functions *}

defaultsort pcpo

consts  
  Istrictify :: "('a \<rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  strictify  :: "('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'b"

defs
  Istrictify_def: "Istrictify f x \<equiv> if x = \<bottom> then \<bottom> else f\<cdot>x"    
  strictify_def:  "strictify \<equiv> (\<Lambda> f x. Istrictify f x)"

text {* results about strictify *}

lemma Istrictify1: "Istrictify f \<bottom> = \<bottom>"
by (simp add: Istrictify_def)

lemma Istrictify2: "x \<noteq> \<bottom> \<Longrightarrow> Istrictify f x = f\<cdot>x"
by (simp add: Istrictify_def)

lemma monofun_Istrictify1: "monofun (\<lambda>f. Istrictify f x)"
apply (rule monofunI [rule_format])
apply (simp add: Istrictify_def monofun_cfun_fun)
done

lemma monofun_Istrictify2: "monofun (\<lambda>x. Istrictify f x)"
apply (rule monofunI [rule_format])
apply (simp add: Istrictify_def monofun_cfun_arg)
apply clarify
apply (simp add: eq_UU_iff)
done

lemma contlub_Istrictify1: "contlub (\<lambda>f. Istrictify f x)"
apply (rule contlubI [rule_format])
apply (case_tac "x = \<bottom>")
apply (simp add: Istrictify1)
apply (simp add: thelub_const)
apply (simp add: Istrictify2)
apply (erule contlub_cfun_fun)
done

lemma contlub_Istrictify2: "contlub (\<lambda>x. Istrictify f x)"
apply (rule contlubI [rule_format])
apply (case_tac "lub (range Y) = \<bottom>")
apply (simp add: Istrictify1 chain_UU_I)
apply (simp add: thelub_const)
apply (simp add: Istrictify2)
apply (simp add: contlub_cfun_arg)
apply (rule lub_equal2)
apply (rule chain_mono2 [THEN exE])
apply (erule chain_UU_I_inverse2)
apply (assumption)
apply (blast intro: Istrictify2 [symmetric])
apply (erule chain_monofun)
apply (erule monofun_Istrictify2 [THEN ch2ch_monofun])
done

lemmas cont_Istrictify1 =
  monocontlub2cont [OF monofun_Istrictify1 contlub_Istrictify1, standard]

lemmas cont_Istrictify2 =
  monocontlub2cont [OF monofun_Istrictify2 contlub_Istrictify2, standard]

lemma strictify1 [simp]: "strictify\<cdot>f\<cdot>\<bottom> = \<bottom>"
apply (unfold strictify_def)
apply (simp add: cont_Istrictify1 cont_Istrictify2)
apply (rule Istrictify1)
done

lemma strictify2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> strictify\<cdot>f\<cdot>x = f\<cdot>x"
apply (unfold strictify_def)
apply (simp add: cont_Istrictify1 cont_Istrictify2)
apply (erule Istrictify2)
done

lemma strictify_conv_if: "strictify\<cdot>f\<cdot>x = (if x = \<bottom> then \<bottom> else f\<cdot>x)"
by simp

end
