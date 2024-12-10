(*  Title:      HOL/HOLCF/Cfun.thy
    Author:     Franz Regensburger
    Author:     Brian Huffman
*)

section \<open>The type of continuous functions\<close>

theory Cfun
  imports Cpodef
begin

default_sort cpo


subsection \<open>Definition of continuous function type\<close>

definition "cfun = {f::'a \<Rightarrow> 'b. cont f}"

cpodef ('a, 'b) cfun (\<open>(\<open>notation=\<open>infix \<rightarrow>\<close>\<close>_ \<rightarrow>/ _)\<close> [1, 0] 0) = "cfun :: ('a \<Rightarrow> 'b) set"
  by (auto simp: cfun_def intro: cont_const adm_cont)

type_notation (ASCII)
  cfun  (infixr \<open>->\<close> 0)

notation (ASCII)
  Rep_cfun  (\<open>(\<open>notation=\<open>infix $\<close>\<close>_$/_)\<close> [999,1000] 999)

notation
  Rep_cfun  (\<open>(\<open>notation=\<open>infix \<cdot>\<close>\<close>_\<cdot>/_)\<close> [999,1000] 999)


subsection \<open>Syntax for continuous lambda abstraction\<close>

syntax "_cabs" :: "[logic, logic] \<Rightarrow> logic"

parse_translation \<open>
(* rewrite (_cabs x t) => (Abs_cfun (%x. t)) *)
  [Syntax_Trans.mk_binder_tr (\<^syntax_const>\<open>_cabs\<close>, \<^const_syntax>\<open>Abs_cfun\<close>)]
\<close>

print_translation \<open>
  [(\<^const_syntax>\<open>Abs_cfun\<close>, fn ctxt => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' ctxt abs
      in Syntax.const \<^syntax_const>\<open>_cabs\<close> $ x $ t end)]
\<close>  \<comment> \<open>To avoid eta-contraction of body\<close>

text \<open>Syntax for nested abstractions\<close>

syntax (ASCII)
  "_Lambda" :: "[cargs, logic] \<Rightarrow> logic"  (\<open>(\<open>indent=3 notation=\<open>binder LAM\<close>\<close>LAM _./ _)\<close> [1000, 10] 10)

syntax
  "_Lambda" :: "[cargs, logic] \<Rightarrow> logic" (\<open>(\<open>indent=3 notation=\<open>binder \<Lambda>\<close>\<close>\<Lambda> _./ _)\<close> [1000, 10] 10)

syntax_consts
  "_Lambda" \<rightleftharpoons> Abs_cfun

parse_ast_translation \<open>
(* rewrite (LAM x y z. t) => (_cabs x (_cabs y (_cabs z t))) *)
(* cf. Syntax.lambda_ast_tr from src/Pure/Syntax/syn_trans.ML *)
  let
    fun Lambda_ast_tr [pats, body] =
          Ast.fold_ast_p \<^syntax_const>\<open>_cabs\<close>
            (Ast.unfold_ast \<^syntax_const>\<open>_cargs\<close> (Ast.strip_positions pats), body)
      | Lambda_ast_tr asts = raise Ast.AST ("Lambda_ast_tr", asts);
  in [(\<^syntax_const>\<open>_Lambda\<close>, K Lambda_ast_tr)] end
\<close>

print_ast_translation \<open>
(* rewrite (_cabs x (_cabs y (_cabs z t))) => (LAM x y z. t) *)
(* cf. Syntax.abs_ast_tr' from src/Pure/Syntax/syn_trans.ML *)
  let
    fun cabs_ast_tr' asts =
      (case Ast.unfold_ast_p \<^syntax_const>\<open>_cabs\<close>
          (Ast.Appl (Ast.Constant \<^syntax_const>\<open>_cabs\<close> :: asts)) of
        ([], _) => raise Ast.AST ("cabs_ast_tr'", asts)
      | (xs, body) => Ast.Appl
          [Ast.Constant \<^syntax_const>\<open>_Lambda\<close>,
           Ast.fold_ast \<^syntax_const>\<open>_cargs\<close> xs, body]);
  in [(\<^syntax_const>\<open>_cabs\<close>, K cabs_ast_tr')] end
\<close>

text \<open>Dummy patterns for continuous abstraction\<close>
translations
  "\<Lambda> _. t" \<rightharpoonup> "CONST Abs_cfun (\<lambda>_. t)"


subsection \<open>Continuous function space is pointed\<close>

lemma bottom_cfun: "\<bottom> \<in> cfun"
  by (simp add: cfun_def inst_fun_pcpo)

instance cfun :: (cpo, discrete_cpo) discrete_cpo
  by intro_classes (simp add: below_cfun_def Rep_cfun_inject)

instance cfun :: (cpo, pcpo) pcpo
  by (rule typedef_pcpo [OF type_definition_cfun below_cfun_def bottom_cfun])

lemmas Rep_cfun_strict =
  typedef_Rep_strict [OF type_definition_cfun below_cfun_def bottom_cfun]

lemmas Abs_cfun_strict =
  typedef_Abs_strict [OF type_definition_cfun below_cfun_def bottom_cfun]

text \<open>function application is strict in its first argument\<close>

lemma Rep_cfun_strict1 [simp]: "\<bottom>\<cdot>x = \<bottom>"
  by (simp add: Rep_cfun_strict)

lemma LAM_strict [simp]: "(\<Lambda> x. \<bottom>) = \<bottom>"
  by (simp add: inst_fun_pcpo [symmetric] Abs_cfun_strict)

text \<open>for compatibility with old HOLCF-Version\<close>
lemma inst_cfun_pcpo: "\<bottom> = (\<Lambda> x. \<bottom>)"
  by simp


subsection \<open>Basic properties of continuous functions\<close>

text \<open>Beta-equality for continuous functions\<close>

lemma Abs_cfun_inverse2: "cont f \<Longrightarrow> Rep_cfun (Abs_cfun f) = f"
  by (simp add: Abs_cfun_inverse cfun_def)

lemma beta_cfun: "cont f \<Longrightarrow> (\<Lambda> x. f x)\<cdot>u = f u"
  by (simp add: Abs_cfun_inverse2)


subsubsection \<open>Beta-reduction simproc\<close>

text \<open>
  Given the term \<^term>\<open>(\<Lambda> x. f x)\<cdot>y\<close>, the procedure tries to
  construct the theorem \<^term>\<open>(\<Lambda> x. f x)\<cdot>y \<equiv> f y\<close>.  If this
  theorem cannot be completely solved by the cont2cont rules, then
  the procedure returns the ordinary conditional \<open>beta_cfun\<close>
  rule.

  The simproc does not solve any more goals that would be solved by
  using \<open>beta_cfun\<close> as a simp rule.  The advantage of the
  simproc is that it can avoid deeply-nested calls to the simplifier
  that would otherwise be caused by large continuity side conditions.

  Update: The simproc now uses rule \<open>Abs_cfun_inverse2\<close> instead
  of \<open>beta_cfun\<close>, to avoid problems with eta-contraction.
\<close>

simproc_setup beta_cfun_proc ("Rep_cfun (Abs_cfun f)") = \<open>
  K (fn ctxt => fn ct =>
    let
      val f = #2 (Thm.dest_comb (#2 (Thm.dest_comb ct)));
      val [T, U] = Thm.dest_ctyp (Thm.ctyp_of_cterm f);
      val tr = Thm.instantiate' [SOME T, SOME U] [SOME f] (mk_meta_eq @{thm Abs_cfun_inverse2});
      val rules = Named_Theorems.get ctxt \<^named_theorems>\<open>cont2cont\<close>;
      val tac = SOLVED' (REPEAT_ALL_NEW (match_tac ctxt (rev rules)));
    in SOME (perhaps (SINGLE (tac 1)) tr) end)
\<close>

text \<open>Eta-equality for continuous functions\<close>

lemma eta_cfun: "(\<Lambda> x. f\<cdot>x) = f"
  by (rule Rep_cfun_inverse)

text \<open>Extensionality for continuous functions\<close>

lemma cfun_eq_iff: "f = g \<longleftrightarrow> (\<forall>x. f\<cdot>x = g\<cdot>x)"
  by (simp add: Rep_cfun_inject [symmetric] fun_eq_iff)

lemma cfun_eqI: "(\<And>x. f\<cdot>x = g\<cdot>x) \<Longrightarrow> f = g"
  by (simp add: cfun_eq_iff)

text \<open>Extensionality wrt. ordering for continuous functions\<close>

lemma cfun_below_iff: "f \<sqsubseteq> g \<longleftrightarrow> (\<forall>x. f\<cdot>x \<sqsubseteq> g\<cdot>x)"
  by (simp add: below_cfun_def fun_below_iff)

lemma cfun_belowI: "(\<And>x. f\<cdot>x \<sqsubseteq> g\<cdot>x) \<Longrightarrow> f \<sqsubseteq> g"
  by (simp add: cfun_below_iff)

text \<open>Congruence for continuous function application\<close>

lemma cfun_cong: "f = g \<Longrightarrow> x = y \<Longrightarrow> f\<cdot>x = g\<cdot>y"
  by simp

lemma cfun_fun_cong: "f = g \<Longrightarrow> f\<cdot>x = g\<cdot>x"
  by simp

lemma cfun_arg_cong: "x = y \<Longrightarrow> f\<cdot>x = f\<cdot>y"
  by simp


subsection \<open>Continuity of application\<close>

lemma cont_Rep_cfun1: "cont (\<lambda>f. f\<cdot>x)"
  by (rule cont_Rep_cfun [OF cont_id, THEN cont2cont_fun])

lemma cont_Rep_cfun2: "cont (\<lambda>x. f\<cdot>x)"
  using Rep_cfun [where x = f] by (simp add: cfun_def)

lemmas monofun_Rep_cfun = cont_Rep_cfun [THEN cont2mono]

lemmas monofun_Rep_cfun1 = cont_Rep_cfun1 [THEN cont2mono]
lemmas monofun_Rep_cfun2 = cont_Rep_cfun2 [THEN cont2mono]

text \<open>contlub, cont properties of \<^term>\<open>Rep_cfun\<close> in each argument\<close>

lemma contlub_cfun_arg: "chain Y \<Longrightarrow> f\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. f\<cdot>(Y i))"
  by (rule cont_Rep_cfun2 [THEN cont2contlubE])

lemma contlub_cfun_fun: "chain F \<Longrightarrow> (\<Squnion>i. F i)\<cdot>x = (\<Squnion>i. F i\<cdot>x)"
  by (rule cont_Rep_cfun1 [THEN cont2contlubE])

text \<open>monotonicity of application\<close>

lemma monofun_cfun_fun: "f \<sqsubseteq> g \<Longrightarrow> f\<cdot>x \<sqsubseteq> g\<cdot>x"
  by (simp add: cfun_below_iff)

lemma monofun_cfun_arg: "x \<sqsubseteq> y \<Longrightarrow> f\<cdot>x \<sqsubseteq> f\<cdot>y"
  by (rule monofun_Rep_cfun2 [THEN monofunE])

lemma monofun_cfun: "f \<sqsubseteq> g \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f\<cdot>x \<sqsubseteq> g\<cdot>y"
  by (rule below_trans [OF monofun_cfun_fun monofun_cfun_arg])

text \<open>ch2ch - rules for the type \<^typ>\<open>'a \<rightarrow> 'b\<close>\<close>

lemma chain_monofun: "chain Y \<Longrightarrow> chain (\<lambda>i. f\<cdot>(Y i))"
  by (erule monofun_Rep_cfun2 [THEN ch2ch_monofun])

lemma ch2ch_Rep_cfunR: "chain Y \<Longrightarrow> chain (\<lambda>i. f\<cdot>(Y i))"
  by (rule monofun_Rep_cfun2 [THEN ch2ch_monofun])

lemma ch2ch_Rep_cfunL: "chain F \<Longrightarrow> chain (\<lambda>i. (F i)\<cdot>x)"
  by (rule monofun_Rep_cfun1 [THEN ch2ch_monofun])

lemma ch2ch_Rep_cfun [simp]: "chain F \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. (F i)\<cdot>(Y i))"
  by (simp add: chain_def monofun_cfun)

lemma ch2ch_LAM [simp]:
  "(\<And>x. chain (\<lambda>i. S i x)) \<Longrightarrow> (\<And>i. cont (\<lambda>x. S i x)) \<Longrightarrow> chain (\<lambda>i. \<Lambda> x. S i x)"
  by (simp add: chain_def cfun_below_iff)

text \<open>contlub, cont properties of \<^term>\<open>Rep_cfun\<close> in both arguments\<close>

lemma lub_APP: "chain F \<Longrightarrow> chain Y \<Longrightarrow> (\<Squnion>i. F i\<cdot>(Y i)) = (\<Squnion>i. F i)\<cdot>(\<Squnion>i. Y i)"
  by (simp add: contlub_cfun_fun contlub_cfun_arg diag_lub)

lemma lub_LAM:
  assumes "\<And>x. chain (\<lambda>i. F i x)"
    and "\<And>i. cont (\<lambda>x. F i x)"
  shows "(\<Squnion>i. \<Lambda> x. F i x) = (\<Lambda> x. \<Squnion>i. F i x)"
  using assms by (simp add: lub_cfun lub_fun ch2ch_lambda)

lemmas lub_distribs = lub_APP lub_LAM

text \<open>strictness\<close>

lemma strictI: "f\<cdot>x = \<bottom> \<Longrightarrow> f\<cdot>\<bottom> = \<bottom>"
  apply (rule bottomI)
  apply (erule subst)
  apply (rule minimal [THEN monofun_cfun_arg])
  done

text \<open>type \<^typ>\<open>'a \<rightarrow> 'b\<close> is chain complete\<close>

lemma lub_cfun: "chain F \<Longrightarrow> (\<Squnion>i. F i) = (\<Lambda> x. \<Squnion>i. F i\<cdot>x)"
  by (simp add: lub_cfun lub_fun ch2ch_lambda)


subsection \<open>Continuity simplification procedure\<close>

text \<open>cont2cont lemma for \<^term>\<open>Rep_cfun\<close>\<close>

lemma cont2cont_APP [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes t: "cont (\<lambda>x. t x)"
  shows "cont (\<lambda>x. (f x)\<cdot>(t x))"
proof -
  from cont_Rep_cfun1 f have "cont (\<lambda>x. (f x)\<cdot>y)" for y
    by (rule cont_compose)
  with t cont_Rep_cfun2 show "cont (\<lambda>x. (f x)\<cdot>(t x))"
    by (rule cont_apply)
qed

text \<open>
  Two specific lemmas for the combination of LCF and HOL terms.
  These lemmas are needed in theories that use types like \<^typ>\<open>'a \<rightarrow> 'b \<Rightarrow> 'c\<close>.
\<close>

lemma cont_APP_app [simp]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. ((f x)\<cdot>(g x)) s)"
  by (rule cont2cont_APP [THEN cont2cont_fun])

lemma cont_APP_app_app [simp]: "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. ((f x)\<cdot>(g x)) s t)"
  by (rule cont_APP_app [THEN cont2cont_fun])


text \<open>cont2mono Lemma for \<^term>\<open>\<lambda>x. LAM y. c1(x)(y)\<close>\<close>

lemma cont2mono_LAM:
  "\<lbrakk>\<And>x. cont (\<lambda>y. f x y); \<And>y. monofun (\<lambda>x. f x y)\<rbrakk>
    \<Longrightarrow> monofun (\<lambda>x. \<Lambda> y. f x y)"
  by (simp add: monofun_def cfun_below_iff)

text \<open>cont2cont Lemma for \<^term>\<open>\<lambda>x. LAM y. f x y\<close>\<close>

text \<open>
  Not suitable as a cont2cont rule, because on nested lambdas
  it causes exponential blow-up in the number of subgoals.
\<close>

lemma cont2cont_LAM:
  assumes f1: "\<And>x. cont (\<lambda>y. f x y)"
  assumes f2: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. \<Lambda> y. f x y)"
proof (rule cont_Abs_cfun)
  from f1 show "f x \<in> cfun" for x
    by (simp add: cfun_def)
  from f2 show "cont f"
    by (rule cont2cont_lambda)
qed

text \<open>
  This version does work as a cont2cont rule, since it
  has only a single subgoal.
\<close>

lemma cont2cont_LAM' [simp, cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'c::cpo"
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  shows "cont (\<lambda>x. \<Lambda> y. f x y)"
  using assms by (simp add: cont2cont_LAM prod_cont_iff)

lemma cont2cont_LAM_discrete [simp, cont2cont]:
  "(\<And>y::'a::discrete_cpo. cont (\<lambda>x. f x y)) \<Longrightarrow> cont (\<lambda>x. \<Lambda> y. f x y)"
  by (simp add: cont2cont_LAM)


subsection \<open>Miscellaneous\<close>

text \<open>Monotonicity of \<^term>\<open>Abs_cfun\<close>\<close>

lemma monofun_LAM: "cont f \<Longrightarrow> cont g \<Longrightarrow> (\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> (\<Lambda> x. f x) \<sqsubseteq> (\<Lambda> x. g x)"
  by (simp add: cfun_below_iff)

text \<open>some lemmata for functions with flat/chfin domain/range types\<close>

lemma chfin_Rep_cfunR: "chain Y \<Longrightarrow> \<forall>s. \<exists>n. (LUB i. Y i)\<cdot>s = Y n\<cdot>s"
  for Y :: "nat \<Rightarrow> 'a::cpo \<rightarrow> 'b::chfin"
  apply (rule allI)
  apply (subst contlub_cfun_fun)
   apply assumption
  apply (fast intro!: lub_eqI chfin lub_finch2 chfin2finch ch2ch_Rep_cfunL)
  done

lemma adm_chfindom: "adm (\<lambda>(u::'a::cpo \<rightarrow> 'b::chfin). P(u\<cdot>s))"
  by (rule adm_subst, simp, rule adm_chfin)


subsection \<open>Continuous injection-retraction pairs\<close>

text \<open>Continuous retractions are strict.\<close>

lemma retraction_strict: "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> f\<cdot>\<bottom> = \<bottom>"
  apply (rule bottomI)
  apply (drule_tac x="\<bottom>" in spec)
  apply (erule subst)
  apply (rule monofun_cfun_arg)
  apply (rule minimal)
  done

lemma injection_eq: "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> (g\<cdot>x = g\<cdot>y) = (x = y)"
  apply (rule iffI)
   apply (drule_tac f=f in cfun_arg_cong)
   apply simp
  apply simp
  done

lemma injection_below: "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> (g\<cdot>x \<sqsubseteq> g\<cdot>y) = (x \<sqsubseteq> y)"
  apply (rule iffI)
   apply (drule_tac f=f in monofun_cfun_arg)
   apply simp
  apply (erule monofun_cfun_arg)
  done

lemma injection_defined_rev: "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> g\<cdot>z = \<bottom> \<Longrightarrow> z = \<bottom>"
  apply (drule_tac f=f in cfun_arg_cong)
  apply (simp add: retraction_strict)
  done

lemma injection_defined: "\<forall>x. f\<cdot>(g\<cdot>x) = x \<Longrightarrow> z \<noteq> \<bottom> \<Longrightarrow> g\<cdot>z \<noteq> \<bottom>"
  by (erule contrapos_nn, rule injection_defined_rev)


text \<open>a result about functions with flat codomain\<close>

lemma flat_eqI: "x \<sqsubseteq> y \<Longrightarrow> x \<noteq> \<bottom> \<Longrightarrow> x = y"
  for x y :: "'a::flat"
  by (drule ax_flat) simp

lemma flat_codom: "f\<cdot>x = c \<Longrightarrow> f\<cdot>\<bottom> = \<bottom> \<or> (\<forall>z. f\<cdot>z = c)"
  for c :: "'b::flat"
  apply (cases "f\<cdot>x = \<bottom>")
   apply (rule disjI1)
   apply (rule bottomI)
   apply (erule_tac t="\<bottom>" in subst)
   apply (rule minimal [THEN monofun_cfun_arg])
  apply clarify
  apply (rule_tac a = "f\<cdot>\<bottom>" in refl [THEN box_equals])
   apply (erule minimal [THEN monofun_cfun_arg, THEN flat_eqI])
  apply (erule minimal [THEN monofun_cfun_arg, THEN flat_eqI])
  done


subsection \<open>Identity and composition\<close>

definition ID :: "'a \<rightarrow> 'a"
  where "ID = (\<Lambda> x. x)"

definition cfcomp  :: "('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'c"
  where oo_def: "cfcomp = (\<Lambda> f g x. f\<cdot>(g\<cdot>x))"

abbreviation cfcomp_syn :: "['b \<rightarrow> 'c, 'a \<rightarrow> 'b] \<Rightarrow> 'a \<rightarrow> 'c"  (infixr \<open>oo\<close> 100)
  where "f oo g == cfcomp\<cdot>f\<cdot>g"

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

text \<open>
  Show that interpretation of (pcpo, \<open>_\<rightarrow>_\<close>) is a category.
  \<^item> The class of objects is interpretation of syntactical class pcpo.
  \<^item> The class of arrows  between objects \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close> is interpret. of \<^typ>\<open>'a \<rightarrow> 'b\<close>.
  \<^item> The identity arrow is interpretation of \<^term>\<open>ID\<close>.
  \<^item> The composition of f and g is interpretation of \<open>oo\<close>.
\<close>

lemma ID2 [simp]: "f oo ID = f"
  by (rule cfun_eqI, simp)

lemma ID3 [simp]: "ID oo f = f"
  by (rule cfun_eqI) simp

lemma assoc_oo: "f oo (g oo h) = (f oo g) oo h"
  by (rule cfun_eqI) simp


subsection \<open>Strictified functions\<close>

default_sort pcpo

definition seq :: "'a \<rightarrow> 'b \<rightarrow> 'b"
  where "seq = (\<Lambda> x. if x = \<bottom> then \<bottom> else ID)"

lemma cont2cont_if_bottom [cont2cont, simp]:
  assumes f: "cont (\<lambda>x. f x)"
    and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. if f x = \<bottom> then \<bottom> else g x)"
proof (rule cont_apply [OF f])
  show "cont (\<lambda>y. if y = \<bottom> then \<bottom> else g x)" for x
    unfolding cont_def is_lub_def is_ub_def ball_simps
    by (simp add: lub_eq_bottom_iff)
  show "cont (\<lambda>x. if y = \<bottom> then \<bottom> else g x)" for y
    by (simp add: g)
qed

lemma seq_conv_if: "seq\<cdot>x = (if x = \<bottom> then \<bottom> else ID)"
  by (simp add: seq_def)

lemma seq_simps [simp]:
  "seq\<cdot>\<bottom> = \<bottom>"
  "seq\<cdot>x\<cdot>\<bottom> = \<bottom>"
  "x \<noteq> \<bottom> \<Longrightarrow> seq\<cdot>x = ID"
  by (simp_all add: seq_conv_if)

definition strictify  :: "('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'b"
  where "strictify = (\<Lambda> f x. seq\<cdot>x\<cdot>(f\<cdot>x))"

lemma strictify_conv_if: "strictify\<cdot>f\<cdot>x = (if x = \<bottom> then \<bottom> else f\<cdot>x)"
  by (simp add: strictify_def)

lemma strictify1 [simp]: "strictify\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by (simp add: strictify_conv_if)

lemma strictify2 [simp]: "x \<noteq> \<bottom> \<Longrightarrow> strictify\<cdot>f\<cdot>x = f\<cdot>x"
  by (simp add: strictify_conv_if)


subsection \<open>Continuity of let-bindings\<close>

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
  from g show "cont (\<lambda>y. g x y)" for x
    by (simp add: prod_cont_iff)
  from g show "cont (\<lambda>x. g x y)" for y
    by (simp add: prod_cont_iff)
qed

text \<open>The simple version (suggested by Joachim Breitner) is needed if
  the type of the defined term is not a cpo.\<close>

lemma cont2cont_Let_simple [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. g x y)"
  shows "cont (\<lambda>x. let y = t in g x y)"
  unfolding Let_def using assms .

end
