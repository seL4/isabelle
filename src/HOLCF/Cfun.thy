(*  Title:      HOLCF/Cfun.thy
    ID:         $Id$
    Author:     Franz Regensburger

Definition of the type ->  of continuous functions.
*)

header {* The type of continuous functions *}

theory Cfun
imports TypedefPcpo
uses ("cont_proc.ML")
begin

defaultsort cpo

subsection {* Definition of continuous function type *}

typedef (CFun)  ('a, 'b) "->" (infixr 0) = "{f::'a => 'b. cont f}"
by (rule exI, fast intro: cont_const)

syntax
  Rep_CFun :: "('a -> 'b) => ('a => 'b)" ("_$_" [999,1000] 999)
                                                (* application *)
  Abs_CFun :: "('a => 'b) => ('a -> 'b)" (binder "LAM " 10)
                                                (* abstraction *)

syntax (xsymbols)
  "->"     :: "[type, type] => type"      ("(_ \<rightarrow>/ _)" [1,0]0)
  "LAM "   :: "[idts, 'a => 'b] => ('a -> 'b)"
					("(3\<Lambda>_./ _)" [0, 10] 10)
  Rep_CFun :: "('a -> 'b) => ('a => 'b)" ("(_\<cdot>_)" [999,1000] 999)

syntax (HTML output)
  Rep_CFun :: "('a -> 'b) => ('a => 'b)" ("(_\<cdot>_)" [999,1000] 999)

subsection {* Class instances *}

instance "->"  :: (cpo, cpo) sq_ord ..

defs (overloaded)
  less_cfun_def: "(op \<sqsubseteq>) \<equiv> (\<lambda>f g. Rep_CFun f \<sqsubseteq> Rep_CFun g)"

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

lemmas Rep_CFun_strict =
  typedef_Rep_strict [OF type_definition_CFun less_cfun_def UU_CFun]

lemmas Abs_CFun_strict =
  typedef_Abs_strict [OF type_definition_CFun less_cfun_def UU_CFun]

text {* Additional lemma about the isomorphism between
        @{typ "'a -> 'b"} and @{term CFun} *}

lemma Abs_CFun_inverse2: "cont f \<Longrightarrow> Rep_CFun (Abs_CFun f) = f"
by (simp add: Abs_CFun_inverse CFun_def)

text {* Beta-equality for continuous functions *}

lemma beta_cfun [simp]: "cont f \<Longrightarrow> (\<Lambda> x. f x)\<cdot>u = f u"
by (simp add: Abs_CFun_inverse2)

text {* Eta-equality for continuous functions *}

lemma eta_cfun: "(\<Lambda> x. f\<cdot>x) = f"
by (rule Rep_CFun_inverse)

text {* Extensionality for continuous functions *}

lemma ext_cfun: "(\<And>x. f\<cdot>x = g\<cdot>x) \<Longrightarrow> f = g"
by (simp add: Rep_CFun_inject [symmetric] ext)

text {* lemmas about application of continuous functions *}

lemma cfun_cong: "\<lbrakk>f = g; x = y\<rbrakk> \<Longrightarrow> f\<cdot>x = g\<cdot>y"
by simp

lemma cfun_fun_cong: "f = g \<Longrightarrow> f\<cdot>x = g\<cdot>x"
by simp

lemma cfun_arg_cong: "x = y \<Longrightarrow> f\<cdot>x = f\<cdot>y"
by simp

subsection {* Continuity of application *}

lemma cont_Rep_CFun1: "cont (\<lambda>f. f\<cdot>x)"
by (rule cont_Rep_CFun [THEN cont2cont_CF1L])

lemma cont_Rep_CFun2: "cont (\<lambda>x. f\<cdot>x)"
apply (rule_tac P = "cont" in CollectD)
apply (fold CFun_def)
apply (rule Rep_CFun)
done

lemmas monofun_Rep_CFun = cont_Rep_CFun [THEN cont2mono]
lemmas contlub_Rep_CFun = cont_Rep_CFun [THEN cont2contlub]

lemmas monofun_Rep_CFun1 = cont_Rep_CFun1 [THEN cont2mono, standard]
lemmas contlub_Rep_CFun1 = cont_Rep_CFun1 [THEN cont2contlub, standard]
lemmas monofun_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2mono, standard]
lemmas contlub_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2contlub, standard]

text {* contlub, cont properties of @{term Rep_CFun} in each argument *}

lemma contlub_cfun_arg: "chain Y \<Longrightarrow> f\<cdot>(lub (range Y)) = (\<Squnion>i. f\<cdot>(Y i))"
by (rule contlub_Rep_CFun2 [THEN contlubE])

lemma cont_cfun_arg: "chain Y \<Longrightarrow> range (\<lambda>i. f\<cdot>(Y i)) <<| f\<cdot>(lub (range Y))"
by (rule cont_Rep_CFun2 [THEN contE])

lemma contlub_cfun_fun: "chain F \<Longrightarrow> lub (range F)\<cdot>x = (\<Squnion>i. F i\<cdot>x)"
by (rule contlub_Rep_CFun1 [THEN contlubE])

lemma cont_cfun_fun: "chain F \<Longrightarrow> range (\<lambda>i. F i\<cdot>x) <<| lub (range F)\<cdot>x"
by (rule cont_Rep_CFun1 [THEN contE])

text {* Extensionality wrt. @{term "op <<"} in @{typ "'a -> 'b"} *}

lemma less_cfun_ext: "(\<And>x. f\<cdot>x \<sqsubseteq> g\<cdot>x) \<Longrightarrow> f \<sqsubseteq> g"
by (simp add: less_cfun_def less_fun_def)

text {* monotonicity of application *}

lemma monofun_cfun_fun: "f \<sqsubseteq> g \<Longrightarrow> f\<cdot>x \<sqsubseteq> g\<cdot>x"
by (simp add: less_cfun_def less_fun_def)

lemma monofun_cfun_arg: "x \<sqsubseteq> y \<Longrightarrow> f\<cdot>x \<sqsubseteq> f\<cdot>y"
by (rule monofun_Rep_CFun2 [THEN monofunE])

lemma monofun_cfun: "\<lbrakk>f \<sqsubseteq> g; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f\<cdot>x \<sqsubseteq> g\<cdot>y"
by (rule trans_less [OF monofun_cfun_fun monofun_cfun_arg])

text {* ch2ch - rules for the type @{typ "'a -> 'b"} *}

lemma chain_monofun: "chain Y \<Longrightarrow> chain (\<lambda>i. f\<cdot>(Y i))"
by (erule monofun_Rep_CFun2 [THEN ch2ch_monofun])

lemma ch2ch_Rep_CFunR: "chain Y \<Longrightarrow> chain (\<lambda>i. f\<cdot>(Y i))"
by (rule monofun_Rep_CFun2 [THEN ch2ch_monofun])

lemma ch2ch_Rep_CFunL: "chain F \<Longrightarrow> chain (\<lambda>i. (F i)\<cdot>x)"
by (rule monofun_Rep_CFun1 [THEN ch2ch_monofun])

lemma ch2ch_Rep_CFun: "\<lbrakk>chain F; chain Y\<rbrakk> \<Longrightarrow> chain (\<lambda>i. (F i)\<cdot>(Y i))"
apply (rule chainI)
apply (rule monofun_cfun)
apply (erule chainE)
apply (erule chainE)
done

text {* contlub, cont properties of @{term Rep_CFun} in both arguments *}

lemma contlub_cfun: 
  "\<lbrakk>chain F; chain Y\<rbrakk> \<Longrightarrow> (\<Squnion>i. F i)\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. F i\<cdot>(Y i))"
apply (simp only: contlub_cfun_fun)
apply (simp only: contlub_cfun_arg)
apply (rule diag_lub)
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (erule monofun_Rep_CFun2 [THEN ch2ch_monofun])
done

lemma cont_cfun: 
  "\<lbrakk>chain F; chain Y\<rbrakk> \<Longrightarrow> range (\<lambda>i. F i\<cdot>(Y i)) <<| (\<Squnion>i. F i)\<cdot>(\<Squnion>i. Y i)"
apply (rule thelubE)
apply (simp only: ch2ch_Rep_CFun)
apply (simp only: contlub_cfun)
done

text {* strictness *}

lemma strictI: "f\<cdot>x = \<bottom> \<Longrightarrow> f\<cdot>\<bottom> = \<bottom>"
apply (rule UU_I)
apply (erule subst)
apply (rule minimal [THEN monofun_cfun_arg])
done

text {* the lub of a chain of continous functions is monotone *}

lemma lub_cfun_mono: "chain F \<Longrightarrow> monofun (\<lambda>x. \<Squnion>i. F i\<cdot>x)"
apply (drule ch2ch_monofun [OF monofun_Rep_CFun])
apply (simp add: thelub_fun [symmetric])
apply (erule monofun_lub_fun)
apply (simp add: monofun_Rep_CFun2)
done

text {* a lemma about the exchange of lubs for type @{typ "'a -> 'b"} *}

lemma ex_lub_cfun: "[| chain(F); chain(Y) |] ==> 
                lub(range(%j. lub(range(%i. F(j)$(Y i))))) = 
                lub(range(%i. lub(range(%j. F(j)$(Y i)))))"
by (simp add: diag_lub ch2ch_Rep_CFunL ch2ch_Rep_CFunR)

text {* the lub of a chain of cont. functions is continuous *}

lemma cont_lub_cfun: "chain F \<Longrightarrow> cont (\<lambda>x. \<Squnion>i. F i\<cdot>x)"
apply (rule cont2cont_lub)
apply (erule monofun_Rep_CFun [THEN ch2ch_monofun])
apply (rule cont_Rep_CFun2)
done

text {* type @{typ "'a -> 'b"} is chain complete *}

lemma lub_cfun: "chain F \<Longrightarrow> range F <<| (LAM x. LUB i. F i$x)"
apply (subst thelub_fun [symmetric])
apply (erule monofun_Rep_CFun [THEN ch2ch_monofun])
apply (erule typedef_is_lub [OF type_definition_CFun less_cfun_def adm_CFun])
done

lemmas thelub_cfun = lub_cfun [THEN thelubI, standard]
 -- {* @{thm thelub_cfun} *} (* chain F \<Longrightarrow> lub (range F) = (\<Lambda>x. \<Squnion>i. F i\<cdot>x) *)

subsection {* Miscellaneous *}

text {* Monotonicity of @{term Abs_CFun} *}

lemma semi_monofun_Abs_CFun: "[| cont(f); cont(g); f<<g|] ==> Abs_CFun(f)<<Abs_CFun(g)"
by (simp add: less_cfun_def Abs_CFun_inverse2)

text {* for compatibility with old HOLCF-Version *}
lemma inst_cfun_pcpo: "\<bottom> = (\<Lambda> x. \<bottom>)"
by (simp add: inst_fun_pcpo [symmetric] Abs_CFun_strict)

subsection {* Continuity of application *}

text {* cont2cont lemma for @{term Rep_CFun} *}

lemma cont2cont_Rep_CFun:
  "\<lbrakk>cont f; cont t\<rbrakk> \<Longrightarrow> cont (\<lambda>x. (f x)\<cdot>(t x))"
by (best intro: cont2cont_app2 cont_const cont_Rep_CFun cont_Rep_CFun2)

text {* cont2mono Lemma for @{term "%x. LAM y. c1(x)(y)"} *}

lemma cont2mono_LAM:
assumes p1: "!!x. cont(c1 x)"
assumes p2: "!!y. monofun(%x. c1 x y)"
shows "monofun(%x. LAM y. c1 x y)"
apply (rule monofunI)
apply (rule less_cfun_ext)
apply (simp add: p1)
apply (erule p2 [THEN monofunE])
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

text {* continuity simplification procedure *}

lemmas cont_lemmas1 =
  cont_const cont_id cont_Rep_CFun2 cont2cont_Rep_CFun cont2cont_LAM

use "cont_proc.ML";
setup ContProc.setup;

(*val cont_tac = (fn i => (resolve_tac cont_lemmas i));*)
(*val cont_tacR = (fn i => (REPEAT (cont_tac i)));*)

text {* function application is strict in its first argument *}

lemma Rep_CFun_strict1 [simp]: "\<bottom>\<cdot>x = \<bottom>"
by (simp add: Rep_CFun_strict)

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

lemma injection_less:
  "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> (g\<cdot>x \<sqsubseteq> g\<cdot>y) = (x \<sqsubseteq> y)"
apply (rule iffI)
apply (drule_tac f=f in monofun_cfun_arg)
apply simp
apply (erule monofun_cfun_arg)
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
apply (drule_tac f=g in monofun_cfun_arg)
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

lemma cont_Istrictify1: "cont (\<lambda>f. Istrictify f x)"
apply (case_tac "x = \<bottom>")
apply (simp add: Istrictify1)
apply (simp add: Istrictify2)
done

lemma monofun_Istrictify2: "monofun (\<lambda>x. Istrictify f x)"
apply (rule monofunI)
apply (simp add: Istrictify_def monofun_cfun_arg)
apply clarify
apply (simp add: eq_UU_iff)
done

lemma contlub_Istrictify2: "contlub (\<lambda>x. Istrictify f x)"
apply (rule contlubI)
apply (case_tac "lub (range Y) = \<bottom>")
apply (simp add: Istrictify1 chain_UU_I thelub_const)
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
