(*  Title:      HOLCF/Cfun.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

header {* The type of continuous functions *}

theory Cfun
imports Pcpodef Fun_Cpo Product_Cpo
begin

default_sort cpo

subsection {* Definition of continuous function type *}

lemma Ex_cont: "\<exists>f. cont f"
by (rule exI, rule cont_const)

lemma adm_cont: "adm cont"
by (rule admI, rule cont_lub_fun)

cpodef (CFun)  ('a, 'b) cfun (infixr "->" 0) = "{f::'a => 'b. cont f}"
by (simp_all add: Ex_cont adm_cont)

type_notation (xsymbols)
  cfun  ("(_ \<rightarrow>/ _)" [1, 0] 0)

notation
  Rep_CFun  ("(_$/_)" [999,1000] 999)

notation (xsymbols)
  Rep_CFun  ("(_\<cdot>/_)" [999,1000] 999)

notation (HTML output)
  Rep_CFun  ("(_\<cdot>/_)" [999,1000] 999)

subsection {* Syntax for continuous lambda abstraction *}

syntax "_cabs" :: "'a"

parse_translation {*
(* rewrite (_cabs x t) => (Abs_CFun (%x. t)) *)
  [mk_binder_tr (@{syntax_const "_cabs"}, @{const_syntax Abs_CFun})];
*}

text {* To avoid eta-contraction of body: *}
typed_print_translation {*
  let
    fun cabs_tr' _ _ [Abs abs] = let
          val (x,t) = atomic_abs_tr' abs
        in Syntax.const @{syntax_const "_cabs"} $ x $ t end

      | cabs_tr' _ T [t] = let
          val xT = domain_type (domain_type T);
          val abs' = ("x",xT,(incr_boundvars 1 t)$Bound 0);
          val (x,t') = atomic_abs_tr' abs';
        in Syntax.const @{syntax_const "_cabs"} $ x $ t' end;

  in [(@{const_syntax Abs_CFun}, cabs_tr')] end;
*}

text {* Syntax for nested abstractions *}

syntax
  "_Lambda" :: "[cargs, 'a] \<Rightarrow> logic"  ("(3LAM _./ _)" [1000, 10] 10)

syntax (xsymbols)
  "_Lambda" :: "[cargs, 'a] \<Rightarrow> logic" ("(3\<Lambda> _./ _)" [1000, 10] 10)

parse_ast_translation {*
(* rewrite (LAM x y z. t) => (_cabs x (_cabs y (_cabs z t))) *)
(* cf. Syntax.lambda_ast_tr from src/Pure/Syntax/syn_trans.ML *)
  let
    fun Lambda_ast_tr [pats, body] =
          Syntax.fold_ast_p @{syntax_const "_cabs"}
            (Syntax.unfold_ast @{syntax_const "_cargs"} pats, body)
      | Lambda_ast_tr asts = raise Syntax.AST ("Lambda_ast_tr", asts);
  in [(@{syntax_const "_Lambda"}, Lambda_ast_tr)] end;
*}

print_ast_translation {*
(* rewrite (_cabs x (_cabs y (_cabs z t))) => (LAM x y z. t) *)
(* cf. Syntax.abs_ast_tr' from src/Pure/Syntax/syn_trans.ML *)
  let
    fun cabs_ast_tr' asts =
      (case Syntax.unfold_ast_p @{syntax_const "_cabs"}
          (Syntax.Appl (Syntax.Constant @{syntax_const "_cabs"} :: asts)) of
        ([], _) => raise Syntax.AST ("cabs_ast_tr'", asts)
      | (xs, body) => Syntax.Appl
          [Syntax.Constant @{syntax_const "_Lambda"},
           Syntax.fold_ast @{syntax_const "_cargs"} xs, body]);
  in [(@{syntax_const "_cabs"}, cabs_ast_tr')] end
*}

text {* Dummy patterns for continuous abstraction *}
translations
  "\<Lambda> _. t" => "CONST Abs_CFun (\<lambda> _. t)"

subsection {* Continuous function space is pointed *}

lemma UU_CFun: "\<bottom> \<in> CFun"
by (simp add: CFun_def inst_fun_pcpo)

instance cfun :: (finite_po, finite_po) finite_po
by (rule typedef_finite_po [OF type_definition_CFun])

instance cfun :: (finite_po, chfin) chfin
by (rule typedef_chfin [OF type_definition_CFun below_CFun_def])

instance cfun :: (cpo, discrete_cpo) discrete_cpo
by intro_classes (simp add: below_CFun_def Rep_CFun_inject)

instance cfun :: (cpo, pcpo) pcpo
by (rule typedef_pcpo [OF type_definition_CFun below_CFun_def UU_CFun])

lemmas Rep_CFun_strict =
  typedef_Rep_strict [OF type_definition_CFun below_CFun_def UU_CFun]

lemmas Abs_CFun_strict =
  typedef_Abs_strict [OF type_definition_CFun below_CFun_def UU_CFun]

text {* function application is strict in its first argument *}

lemma Rep_CFun_strict1 [simp]: "\<bottom>\<cdot>x = \<bottom>"
by (simp add: Rep_CFun_strict)

lemma LAM_strict [simp]: "(\<Lambda> x. \<bottom>) = \<bottom>"
by (simp add: inst_fun_pcpo [symmetric] Abs_CFun_strict)

text {* for compatibility with old HOLCF-Version *}
lemma inst_cfun_pcpo: "\<bottom> = (\<Lambda> x. \<bottom>)"
by simp

subsection {* Basic properties of continuous functions *}

text {* Beta-equality for continuous functions *}

lemma Abs_CFun_inverse2: "cont f \<Longrightarrow> Rep_CFun (Abs_CFun f) = f"
by (simp add: Abs_CFun_inverse CFun_def)

lemma beta_cfun: "cont f \<Longrightarrow> (\<Lambda> x. f x)\<cdot>u = f u"
by (simp add: Abs_CFun_inverse2)

text {* Beta-reduction simproc *}

text {*
  Given the term @{term "(\<Lambda> x. f x)\<cdot>y"}, the procedure tries to
  construct the theorem @{term "(\<Lambda> x. f x)\<cdot>y == f y"}.  If this
  theorem cannot be completely solved by the cont2cont rules, then
  the procedure returns the ordinary conditional @{text beta_cfun}
  rule.

  The simproc does not solve any more goals that would be solved by
  using @{text beta_cfun} as a simp rule.  The advantage of the
  simproc is that it can avoid deeply-nested calls to the simplifier
  that would otherwise be caused by large continuity side conditions.
*}

simproc_setup beta_cfun_proc ("Abs_CFun f\<cdot>x") = {*
  fn phi => fn ss => fn ct =>
    let
      val dest = Thm.dest_comb;
      val (f, x) = (apfst (snd o dest o snd o dest) o dest) ct;
      val [T, U] = Thm.dest_ctyp (ctyp_of_term f);
      val tr = instantiate' [SOME T, SOME U] [SOME f, SOME x]
          (mk_meta_eq @{thm beta_cfun});
      val rules = Cont2ContData.get (Simplifier.the_context ss);
      val tac = SOLVED' (REPEAT_ALL_NEW (match_tac rules));
    in SOME (perhaps (SINGLE (tac 1)) tr) end
*}

text {* Eta-equality for continuous functions *}

lemma eta_cfun: "(\<Lambda> x. f\<cdot>x) = f"
by (rule Rep_CFun_inverse)

text {* Extensionality for continuous functions *}

lemma cfun_eq_iff: "f = g \<longleftrightarrow> (\<forall>x. f\<cdot>x = g\<cdot>x)"
by (simp add: Rep_CFun_inject [symmetric] fun_eq_iff)

lemma cfun_eqI: "(\<And>x. f\<cdot>x = g\<cdot>x) \<Longrightarrow> f = g"
by (simp add: cfun_eq_iff)

text {* Extensionality wrt. ordering for continuous functions *}

lemma cfun_below_iff: "f \<sqsubseteq> g \<longleftrightarrow> (\<forall>x. f\<cdot>x \<sqsubseteq> g\<cdot>x)" 
by (simp add: below_CFun_def fun_below_iff)

lemma cfun_belowI: "(\<And>x. f\<cdot>x \<sqsubseteq> g\<cdot>x) \<Longrightarrow> f \<sqsubseteq> g"
by (simp add: cfun_below_iff)

text {* Congruence for continuous function application *}

lemma cfun_cong: "\<lbrakk>f = g; x = y\<rbrakk> \<Longrightarrow> f\<cdot>x = g\<cdot>y"
by simp

lemma cfun_fun_cong: "f = g \<Longrightarrow> f\<cdot>x = g\<cdot>x"
by simp

lemma cfun_arg_cong: "x = y \<Longrightarrow> f\<cdot>x = f\<cdot>y"
by simp

subsection {* Continuity of application *}

lemma cont_Rep_CFun1: "cont (\<lambda>f. f\<cdot>x)"
by (rule cont_Rep_CFun [THEN cont2cont_fun])

lemma cont_Rep_CFun2: "cont (\<lambda>x. f\<cdot>x)"
apply (cut_tac x=f in Rep_CFun)
apply (simp add: CFun_def)
done

lemmas monofun_Rep_CFun = cont_Rep_CFun [THEN cont2mono]

lemmas monofun_Rep_CFun1 = cont_Rep_CFun1 [THEN cont2mono, standard]
lemmas monofun_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2mono, standard]

text {* contlub, cont properties of @{term Rep_CFun} in each argument *}

lemma contlub_cfun_arg: "chain Y \<Longrightarrow> f\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. f\<cdot>(Y i))"
by (rule cont_Rep_CFun2 [THEN cont2contlubE])

lemma cont_cfun_arg: "chain Y \<Longrightarrow> range (\<lambda>i. f\<cdot>(Y i)) <<| f\<cdot>(\<Squnion>i. Y i)"
by (rule cont_Rep_CFun2 [THEN contE])

lemma contlub_cfun_fun: "chain F \<Longrightarrow> (\<Squnion>i. F i)\<cdot>x = (\<Squnion>i. F i\<cdot>x)"
by (rule cont_Rep_CFun1 [THEN cont2contlubE])

lemma cont_cfun_fun: "chain F \<Longrightarrow> range (\<lambda>i. F i\<cdot>x) <<| (\<Squnion>i. F i)\<cdot>x"
by (rule cont_Rep_CFun1 [THEN contE])

text {* monotonicity of application *}

lemma monofun_cfun_fun: "f \<sqsubseteq> g \<Longrightarrow> f\<cdot>x \<sqsubseteq> g\<cdot>x"
by (simp add: cfun_below_iff)

lemma monofun_cfun_arg: "x \<sqsubseteq> y \<Longrightarrow> f\<cdot>x \<sqsubseteq> f\<cdot>y"
by (rule monofun_Rep_CFun2 [THEN monofunE])

lemma monofun_cfun: "\<lbrakk>f \<sqsubseteq> g; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> f\<cdot>x \<sqsubseteq> g\<cdot>y"
by (rule below_trans [OF monofun_cfun_fun monofun_cfun_arg])

text {* ch2ch - rules for the type @{typ "'a -> 'b"} *}

lemma chain_monofun: "chain Y \<Longrightarrow> chain (\<lambda>i. f\<cdot>(Y i))"
by (erule monofun_Rep_CFun2 [THEN ch2ch_monofun])

lemma ch2ch_Rep_CFunR: "chain Y \<Longrightarrow> chain (\<lambda>i. f\<cdot>(Y i))"
by (rule monofun_Rep_CFun2 [THEN ch2ch_monofun])

lemma ch2ch_Rep_CFunL: "chain F \<Longrightarrow> chain (\<lambda>i. (F i)\<cdot>x)"
by (rule monofun_Rep_CFun1 [THEN ch2ch_monofun])

lemma ch2ch_Rep_CFun [simp]:
  "\<lbrakk>chain F; chain Y\<rbrakk> \<Longrightarrow> chain (\<lambda>i. (F i)\<cdot>(Y i))"
by (simp add: chain_def monofun_cfun)

lemma ch2ch_LAM [simp]:
  "\<lbrakk>\<And>x. chain (\<lambda>i. S i x); \<And>i. cont (\<lambda>x. S i x)\<rbrakk> \<Longrightarrow> chain (\<lambda>i. \<Lambda> x. S i x)"
by (simp add: chain_def cfun_below_iff)

text {* contlub, cont properties of @{term Rep_CFun} in both arguments *}

lemma contlub_cfun: 
  "\<lbrakk>chain F; chain Y\<rbrakk> \<Longrightarrow> (\<Squnion>i. F i)\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. F i\<cdot>(Y i))"
by (simp add: contlub_cfun_fun contlub_cfun_arg diag_lub)

lemma cont_cfun: 
  "\<lbrakk>chain F; chain Y\<rbrakk> \<Longrightarrow> range (\<lambda>i. F i\<cdot>(Y i)) <<| (\<Squnion>i. F i)\<cdot>(\<Squnion>i. Y i)"
apply (rule thelubE)
apply (simp only: ch2ch_Rep_CFun)
apply (simp only: contlub_cfun)
done

lemma contlub_LAM:
  "\<lbrakk>\<And>x. chain (\<lambda>i. F i x); \<And>i. cont (\<lambda>x. F i x)\<rbrakk>
    \<Longrightarrow> (\<Lambda> x. \<Squnion>i. F i x) = (\<Squnion>i. \<Lambda> x. F i x)"
apply (simp add: thelub_CFun)
apply (simp add: Abs_CFun_inverse2)
apply (simp add: thelub_fun ch2ch_lambda)
done

lemmas lub_distribs = 
  contlub_cfun [symmetric]
  contlub_LAM [symmetric]

text {* strictness *}

lemma strictI: "f\<cdot>x = \<bottom> \<Longrightarrow> f\<cdot>\<bottom> = \<bottom>"
apply (rule UU_I)
apply (erule subst)
apply (rule minimal [THEN monofun_cfun_arg])
done

text {* type @{typ "'a -> 'b"} is chain complete *}

lemma lub_cfun: "chain F \<Longrightarrow> range F <<| (\<Lambda> x. \<Squnion>i. F i\<cdot>x)"
by (simp only: contlub_cfun_fun [symmetric] eta_cfun thelubE)

lemma thelub_cfun: "chain F \<Longrightarrow> (\<Squnion>i. F i) = (\<Lambda> x. \<Squnion>i. F i\<cdot>x)"
by (rule lub_cfun [THEN thelubI])

subsection {* Continuity simplification procedure *}

text {* cont2cont lemma for @{term Rep_CFun} *}

lemma cont2cont_Rep_CFun [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes t: "cont (\<lambda>x. t x)"
  shows "cont (\<lambda>x. (f x)\<cdot>(t x))"
proof -
  have 1: "\<And>y. cont (\<lambda>x. (f x)\<cdot>y)"
    using cont_Rep_CFun1 f by (rule cont_compose)
  show "cont (\<lambda>x. (f x)\<cdot>(t x))"
    using t cont_Rep_CFun2 1 by (rule cont_apply)
qed

text {* cont2mono Lemma for @{term "%x. LAM y. c1(x)(y)"} *}

lemma cont2mono_LAM:
  "\<lbrakk>\<And>x. cont (\<lambda>y. f x y); \<And>y. monofun (\<lambda>x. f x y)\<rbrakk>
    \<Longrightarrow> monofun (\<lambda>x. \<Lambda> y. f x y)"
  unfolding monofun_def cfun_below_iff by simp

text {* cont2cont Lemma for @{term "%x. LAM y. f x y"} *}

text {*
  Not suitable as a cont2cont rule, because on nested lambdas
  it causes exponential blow-up in the number of subgoals.
*}

lemma cont2cont_LAM:
  assumes f1: "\<And>x. cont (\<lambda>y. f x y)"
  assumes f2: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. \<Lambda> y. f x y)"
proof (rule cont_Abs_CFun)
  fix x
  from f1 show "f x \<in> CFun" by (simp add: CFun_def)
  from f2 show "cont f" by (rule cont2cont_lambda)
qed

text {*
  This version does work as a cont2cont rule, since it
  has only a single subgoal.
*}

lemma cont2cont_LAM' [simp, cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'c::cpo"
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. \<Lambda> y. f x y)"
using assms by (simp add: cont2cont_LAM prod_cont_iff)

lemma cont2cont_LAM_discrete [simp, cont2cont]:
  "(\<And>y::'a::discrete_cpo. cont (\<lambda>x. f x y)) \<Longrightarrow> cont (\<lambda>x. \<Lambda> y. f x y)"
by (simp add: cont2cont_LAM)

lemmas cont_lemmas1 =
  cont_const cont_id cont_Rep_CFun2 cont2cont_Rep_CFun cont2cont_LAM

subsection {* Miscellaneous *}

text {* Monotonicity of @{term Abs_CFun} *}

lemma semi_monofun_Abs_CFun:
  "\<lbrakk>cont f; cont g; f \<sqsubseteq> g\<rbrakk> \<Longrightarrow> Abs_CFun f \<sqsubseteq> Abs_CFun g"
by (simp add: below_CFun_def Abs_CFun_inverse2)

text {* some lemmata for functions with flat/chfin domain/range types *}

lemma chfin_Rep_CFunR: "chain (Y::nat => 'a::cpo->'b::chfin)  
      ==> !s. ? n. (LUB i. Y i)$s = Y n$s"
apply (rule allI)
apply (subst contlub_cfun_fun)
apply assumption
apply (fast intro!: thelubI chfin lub_finch2 chfin2finch ch2ch_Rep_CFunL)
done

lemma adm_chfindom: "adm (\<lambda>(u::'a::cpo \<rightarrow> 'b::chfin). P(u\<cdot>s))"
by (rule adm_subst, simp, rule adm_chfin)

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

lemma injection_below:
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
apply (drule chfin)
apply (unfold max_in_chain_def)
apply (simp add: injection_eq)
done

lemma flat2flat:
  "\<forall>y. (f::'a::flat \<rightarrow> 'b::pcpo)\<cdot>(g\<cdot>y) = y
    \<Longrightarrow> \<forall>x y::'b. x \<sqsubseteq> y \<longrightarrow> x = \<bottom> \<or> x = y"
apply clarify
apply (drule_tac f=g in monofun_cfun_arg)
apply (drule ax_flat)
apply (erule disjE)
apply (simp add: injection_defined_rev)
apply (simp add: injection_eq)
done

text {* a result about functions with flat codomain *}

lemma flat_eqI: "\<lbrakk>(x::'a::flat) \<sqsubseteq> y; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> x = y"
by (drule ax_flat, simp)

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

definition
  ID :: "'a \<rightarrow> 'a" where
  "ID = (\<Lambda> x. x)"

definition
  cfcomp  :: "('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'c" where
  oo_def: "cfcomp = (\<Lambda> f g x. f\<cdot>(g\<cdot>x))"

abbreviation
  cfcomp_syn :: "['b \<rightarrow> 'c, 'a \<rightarrow> 'b] \<Rightarrow> 'a \<rightarrow> 'c"  (infixr "oo" 100)  where
  "f oo g == cfcomp\<cdot>f\<cdot>g"

lemma ID1 [simp]: "ID\<cdot>x = x"
by (simp add: ID_def)

lemma cfcomp1: "(f oo g) = (\<Lambda> x. f\<cdot>(g\<cdot>x))"
by (simp add: oo_def)

lemma cfcomp2 [simp]: "(f oo g)\<cdot>x = f\<cdot>(g\<cdot>x)"
by (simp add: cfcomp1)

lemma cfcomp_LAM: "cont g \<Longrightarrow> f oo (\<Lambda> x. g x) = (\<Lambda> x. f\<cdot>(g x))"
by (simp add: cfcomp1)

lemma cfcomp_strict [simp]: "\<bottom> oo f = \<bottom>"
by (simp add: cfun_eq_iff)

text {*
  Show that interpretation of (pcpo,@{text "_->_"}) is a category.
  The class of objects is interpretation of syntactical class pcpo.
  The class of arrows  between objects @{typ 'a} and @{typ 'b} is interpret. of @{typ "'a -> 'b"}.
  The identity arrow is interpretation of @{term ID}.
  The composition of f and g is interpretation of @{text "oo"}.
*}

lemma ID2 [simp]: "f oo ID = f"
by (rule cfun_eqI, simp)

lemma ID3 [simp]: "ID oo f = f"
by (rule cfun_eqI, simp)

lemma assoc_oo: "f oo (g oo h) = (f oo g) oo h"
by (rule cfun_eqI, simp)

subsection {* Map operator for continuous function space *}

definition
  cfun_map :: "('b \<rightarrow> 'a) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'd)"
where
  "cfun_map = (\<Lambda> a b f x. b\<cdot>(f\<cdot>(a\<cdot>x)))"

lemma cfun_map_beta [simp]: "cfun_map\<cdot>a\<cdot>b\<cdot>f\<cdot>x = b\<cdot>(f\<cdot>(a\<cdot>x))"
unfolding cfun_map_def by simp

lemma cfun_map_ID: "cfun_map\<cdot>ID\<cdot>ID = ID"
unfolding cfun_eq_iff by simp

lemma cfun_map_map:
  "cfun_map\<cdot>f1\<cdot>g1\<cdot>(cfun_map\<cdot>f2\<cdot>g2\<cdot>p) =
    cfun_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
by (rule cfun_eqI) simp

subsection {* Strictified functions *}

default_sort pcpo

definition
  strictify  :: "('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'b" where
  "strictify = (\<Lambda> f x. if x = \<bottom> then \<bottom> else f\<cdot>x)"

text {* results about strictify *}

lemma cont_strictify1: "cont (\<lambda>f. if x = \<bottom> then \<bottom> else f\<cdot>x)"
by simp

lemma monofun_strictify2: "monofun (\<lambda>x. if x = \<bottom> then \<bottom> else f\<cdot>x)"
apply (rule monofunI)
apply (auto simp add: monofun_cfun_arg)
done

lemma cont_strictify2: "cont (\<lambda>x. if x = \<bottom> then \<bottom> else f\<cdot>x)"
apply (rule contI2)
apply (rule monofun_strictify2)
apply (case_tac "(\<Squnion>i. Y i) = \<bottom>", simp)
apply (simp add: contlub_cfun_arg del: if_image_distrib)
apply (drule chain_UU_I_inverse2, clarify, rename_tac j)
apply (rule lub_mono2, rule_tac x=j in exI, simp_all)
apply (auto dest!: chain_mono_less)
done

lemma strictify_conv_if: "strictify\<cdot>f\<cdot>x = (if x = \<bottom> then \<bottom> else f\<cdot>x)"
  unfolding strictify_def
  by (simp add: cont_strictify1 cont_strictify2 cont2cont_LAM)

lemma strictify1 [simp]: "strictify\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (simp add: strictify_conv_if)

lemma strictify2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> strictify\<cdot>f\<cdot>x = f\<cdot>x"
by (simp add: strictify_conv_if)

subsection {* Continuity of let-bindings *}

lemma cont2cont_Let:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g1: "\<And>y. cont (\<lambda>x. g x y)"
  assumes g2: "\<And>x. cont (\<lambda>y. g x y)"
  shows "cont (\<lambda>x. let y = f x in g x y)"
unfolding Let_def using f g2 g1 by (rule cont_apply)

lemma cont2cont_Let' [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>p. g (fst p) (snd p))"
  shows "cont (\<lambda>x. let y = f x in g x y)"
using f
proof (rule cont2cont_Let)
  fix x show "cont (\<lambda>y. g x y)"
    using g by (simp add: prod_cont_iff)
next
  fix y show "cont (\<lambda>x. g x y)"
    using g by (simp add: prod_cont_iff)
qed

text {* The simple version (suggested by Joachim Breitner) is needed if
  the type of the defined term is not a cpo. *}

lemma cont2cont_Let_simple [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. g x y)"
  shows "cont (\<lambda>x. let y = t in g x y)"
unfolding Let_def using assms .

end
