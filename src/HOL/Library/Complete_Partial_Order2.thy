(*  Title:      HOL/Library/Complete_Partial_Order2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

section \<open>Formalisation of chain-complete partial orders, continuity and admissibility\<close>

theory Complete_Partial_Order2 imports 
  Main Lattice_Syntax
begin

lemma chain_transfer [transfer_rule]:
  includes lifting_syntax
  shows "((A ===> A ===> (=)) ===> rel_set A ===> (=)) Complete_Partial_Order.chain Complete_Partial_Order.chain"
unfolding chain_def[abs_def] by transfer_prover
                             
lemma linorder_chain [simp, intro!]:
  fixes Y :: "_ :: linorder set"
  shows "Complete_Partial_Order.chain (\<le>) Y"
by(auto intro: chainI)

lemma fun_lub_apply: "\<And>Sup. fun_lub Sup Y x = Sup ((\<lambda>f. f x) ` Y)"
by(simp add: fun_lub_def image_def)

lemma fun_lub_empty [simp]: "fun_lub lub {} = (\<lambda>_. lub {})"
by(rule ext)(simp add: fun_lub_apply)

lemma chain_fun_ordD: 
  assumes "Complete_Partial_Order.chain (fun_ord le) Y"
  shows "Complete_Partial_Order.chain le ((\<lambda>f. f x) ` Y)"
by(rule chainI)(auto dest: chainD[OF assms] simp add: fun_ord_def)

lemma chain_Diff:
  "Complete_Partial_Order.chain ord A
  \<Longrightarrow> Complete_Partial_Order.chain ord (A - B)"
by(erule chain_subset) blast

lemma chain_rel_prodD1:
  "Complete_Partial_Order.chain (rel_prod orda ordb) Y
  \<Longrightarrow> Complete_Partial_Order.chain orda (fst ` Y)"
by(auto 4 3 simp add: chain_def)

lemma chain_rel_prodD2:
  "Complete_Partial_Order.chain (rel_prod orda ordb) Y
  \<Longrightarrow> Complete_Partial_Order.chain ordb (snd ` Y)"
by(auto 4 3 simp add: chain_def)


context ccpo begin

lemma ccpo_fun: "class.ccpo (fun_lub Sup) (fun_ord (\<le>)) (mk_less (fun_ord (\<le>)))"
  by standard (auto 4 3 simp add: mk_less_def fun_ord_def fun_lub_apply
    intro: order.trans order.antisym chain_imageI ccpo_Sup_upper ccpo_Sup_least)

lemma ccpo_Sup_below_iff: "Complete_Partial_Order.chain (\<le>) Y \<Longrightarrow> Sup Y \<le> x \<longleftrightarrow> (\<forall>y\<in>Y. y \<le> x)"
by(fast intro: order_trans[OF ccpo_Sup_upper] ccpo_Sup_least)

lemma Sup_minus_bot: 
  assumes chain: "Complete_Partial_Order.chain (\<le>) A"
  shows "\<Squnion>(A - {\<Squnion>{}}) = \<Squnion>A"
    (is "?lhs = ?rhs")
proof (rule order.antisym)
  show "?lhs \<le> ?rhs"
    by (blast intro: ccpo_Sup_least chain_Diff[OF chain] ccpo_Sup_upper[OF chain])
  show "?rhs \<le> ?lhs"
  proof (rule ccpo_Sup_least [OF chain])
    show "x \<in> A \<Longrightarrow> x \<le> ?lhs" for x
      by (cases "x = \<Squnion>{}")
        (blast intro: ccpo_Sup_least chain_empty ccpo_Sup_upper[OF chain_Diff[OF chain]])+
  qed
qed

lemma mono_lub:
  fixes le_b (infix "\<sqsubseteq>" 60)
  assumes chain: "Complete_Partial_Order.chain (fun_ord (\<le>)) Y"
  and mono: "\<And>f. f \<in> Y \<Longrightarrow> monotone le_b (\<le>) f"
  shows "monotone (\<sqsubseteq>) (\<le>) (fun_lub Sup Y)"
proof(rule monotoneI)
  fix x y
  assume "x \<sqsubseteq> y"

  have chain'': "\<And>x. Complete_Partial_Order.chain (\<le>) ((\<lambda>f. f x) ` Y)"
    using chain by(rule chain_imageI)(simp add: fun_ord_def)
  then show "fun_lub Sup Y x \<le> fun_lub Sup Y y" unfolding fun_lub_apply
  proof(rule ccpo_Sup_least)
    fix x'
    assume "x' \<in> (\<lambda>f. f x) ` Y"
    then obtain f where "f \<in> Y" "x' = f x" by blast
    note \<open>x' = f x\<close> also
    from \<open>f \<in> Y\<close> \<open>x \<sqsubseteq> y\<close> have "f x \<le> f y" by(blast dest: mono monotoneD)
    also have "\<dots> \<le> \<Squnion>((\<lambda>f. f y) ` Y)" using chain''
      by(rule ccpo_Sup_upper)(simp add: \<open>f \<in> Y\<close>)
    finally show "x' \<le> \<Squnion>((\<lambda>f. f y) ` Y)" .
  qed
qed

context
  fixes le_b (infix "\<sqsubseteq>" 60) and Y f
  assumes chain: "Complete_Partial_Order.chain le_b Y" 
  and mono1: "\<And>y. y \<in> Y \<Longrightarrow> monotone le_b (\<le>) (\<lambda>x. f x y)"
  and mono2: "\<And>x a b. \<lbrakk> x \<in> Y; a \<sqsubseteq> b; a \<in> Y; b \<in> Y \<rbrakk> \<Longrightarrow> f x a \<le> f x b"
begin

lemma Sup_mono: 
  assumes le: "x \<sqsubseteq> y" and x: "x \<in> Y" and y: "y \<in> Y"
  shows "\<Squnion>(f x ` Y) \<le> \<Squnion>(f y ` Y)" (is "_ \<le> ?rhs")
proof(rule ccpo_Sup_least)
  from chain show chain': "Complete_Partial_Order.chain (\<le>) (f x ` Y)" when "x \<in> Y" for x
    by(rule chain_imageI) (insert that, auto dest: mono2)

  fix x'
  assume "x' \<in> f x ` Y"
  then obtain y' where "y' \<in> Y" "x' = f x y'" by blast note this(2)
  also from mono1[OF \<open>y' \<in> Y\<close>] le have "\<dots> \<le> f y y'" by(rule monotoneD)
  also have "\<dots> \<le> ?rhs" using chain'[OF y]
    by (auto intro!: ccpo_Sup_upper simp add: \<open>y' \<in> Y\<close>)
  finally show "x' \<le> ?rhs" .
qed(rule x)

lemma diag_Sup: "\<Squnion>((\<lambda>x. \<Squnion>(f x ` Y)) ` Y) = \<Squnion>((\<lambda>x. f x x) ` Y)" (is "?lhs = ?rhs")
proof(rule order.antisym)
  have chain1: "Complete_Partial_Order.chain (\<le>) ((\<lambda>x. \<Squnion>(f x ` Y)) ` Y)"
    using chain by(rule chain_imageI)(rule Sup_mono)
  have chain2: "\<And>y'. y' \<in> Y \<Longrightarrow> Complete_Partial_Order.chain (\<le>) (f y' ` Y)" using chain
    by(rule chain_imageI)(auto dest: mono2)
  have chain3: "Complete_Partial_Order.chain (\<le>) ((\<lambda>x. f x x) ` Y)"
    using chain by(rule chain_imageI)(auto intro: monotoneD[OF mono1] mono2 order.trans)

  show "?lhs \<le> ?rhs" using chain1
  proof(rule ccpo_Sup_least)
    fix x'
    assume "x' \<in> (\<lambda>x. \<Squnion>(f x ` Y)) ` Y"
    then obtain y' where "y' \<in> Y" "x' = \<Squnion>(f y' ` Y)" by blast note this(2)
    also have "\<dots> \<le> ?rhs" using chain2[OF \<open>y' \<in> Y\<close>]
    proof(rule ccpo_Sup_least)
      fix x
      assume "x \<in> f y' ` Y"
      then obtain y where "y \<in> Y" and x: "x = f y' y" by blast
      define y'' where "y'' = (if y \<sqsubseteq> y' then y' else y)"
      from chain \<open>y \<in> Y\<close> \<open>y' \<in> Y\<close> have "y \<sqsubseteq> y' \<or> y' \<sqsubseteq> y" by(rule chainD)
      hence "f y' y \<le> f y'' y''" using \<open>y \<in> Y\<close> \<open>y' \<in> Y\<close>
        by(auto simp add: y''_def intro: mono2 monotoneD[OF mono1])
      also from \<open>y \<in> Y\<close> \<open>y' \<in> Y\<close> have "y'' \<in> Y" by(simp add: y''_def)
      from chain3 have "f y'' y'' \<le> ?rhs" by(rule ccpo_Sup_upper)(simp add: \<open>y'' \<in> Y\<close>)
      finally show "x \<le> ?rhs" by(simp add: x)
    qed
    finally show "x' \<le> ?rhs" .
  qed

  show "?rhs \<le> ?lhs" using chain3
  proof(rule ccpo_Sup_least)
    fix y
    assume "y \<in> (\<lambda>x. f x x) ` Y"
    then obtain x where "x \<in> Y" and "y = f x x" by blast note this(2)
    also from chain2[OF \<open>x \<in> Y\<close>] have "\<dots> \<le> \<Squnion>(f x ` Y)"
      by(rule ccpo_Sup_upper)(simp add: \<open>x \<in> Y\<close>)
    also have "\<dots> \<le> ?lhs" by(rule ccpo_Sup_upper[OF chain1])(simp add: \<open>x \<in> Y\<close>)
    finally show "y \<le> ?lhs" .
  qed
qed

end

lemma Sup_image_mono_le:
  fixes le_b (infix "\<sqsubseteq>" 60) and Sup_b ("\<Or>")
  assumes ccpo: "class.ccpo Sup_b (\<sqsubseteq>) lt_b"
  assumes chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
  and mono: "\<And>x y. \<lbrakk> x \<sqsubseteq> y; x \<in> Y \<rbrakk> \<Longrightarrow> f x \<le> f y"
  shows "Sup (f ` Y) \<le> f (\<Or>Y)"
proof(rule ccpo_Sup_least)
  show "Complete_Partial_Order.chain (\<le>) (f ` Y)"
    using chain by(rule chain_imageI)(rule mono)

  fix x
  assume "x \<in> f ` Y"
  then obtain y where "y \<in> Y" and "x = f y" by blast note this(2)
  also have "y \<sqsubseteq> \<Or>Y" using ccpo chain \<open>y \<in> Y\<close> by(rule ccpo.ccpo_Sup_upper)
  hence "f y \<le> f (\<Or>Y)" using \<open>y \<in> Y\<close> by(rule mono)
  finally show "x \<le> \<dots>" .
qed

lemma swap_Sup:
  fixes le_b (infix "\<sqsubseteq>" 60)
  assumes Y: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
  and Z: "Complete_Partial_Order.chain (fun_ord (\<le>)) Z"
  and mono: "\<And>f. f \<in> Z \<Longrightarrow> monotone (\<sqsubseteq>) (\<le>) f"
  shows "\<Squnion>((\<lambda>x. \<Squnion>(x ` Y)) ` Z) = \<Squnion>((\<lambda>x. \<Squnion>((\<lambda>f. f x) ` Z)) ` Y)"
  (is "?lhs = ?rhs")
proof(cases "Y = {}")
  case True
  then show ?thesis
    by (simp add: image_constant_conv cong del: SUP_cong_simp)
next
  case False
  have chain1: "\<And>f. f \<in> Z \<Longrightarrow> Complete_Partial_Order.chain (\<le>) (f ` Y)"
    by(rule chain_imageI[OF Y])(rule monotoneD[OF mono])
  have chain2: "Complete_Partial_Order.chain (\<le>) ((\<lambda>x. \<Squnion>(x ` Y)) ` Z)" using Z
  proof(rule chain_imageI)
    fix f g
    assume "f \<in> Z" "g \<in> Z"
      and "fun_ord (\<le>) f g"
    from chain1[OF \<open>f \<in> Z\<close>] show "\<Squnion>(f ` Y) \<le> \<Squnion>(g ` Y)"
    proof(rule ccpo_Sup_least)
      fix x
      assume "x \<in> f ` Y"
      then obtain y where "y \<in> Y" "x = f y" by blast note this(2)
      also have "\<dots> \<le> g y" using \<open>fun_ord (\<le>) f g\<close> by(simp add: fun_ord_def)
      also have "\<dots> \<le> \<Squnion>(g ` Y)" using chain1[OF \<open>g \<in> Z\<close>]
        by(rule ccpo_Sup_upper)(simp add: \<open>y \<in> Y\<close>)
      finally show "x \<le> \<Squnion>(g ` Y)" .
    qed
  qed
  have chain3: "\<And>x. Complete_Partial_Order.chain (\<le>) ((\<lambda>f. f x) ` Z)"
    using Z by(rule chain_imageI)(simp add: fun_ord_def)
  have chain4: "Complete_Partial_Order.chain (\<le>) ((\<lambda>x. \<Squnion>((\<lambda>f. f x) ` Z)) ` Y)"
    using Y
  proof(rule chain_imageI)
    fix f x y
    assume "x \<sqsubseteq> y"
    show "\<Squnion>((\<lambda>f. f x) ` Z) \<le> \<Squnion>((\<lambda>f. f y) ` Z)" (is "_ \<le> ?rhs") using chain3
    proof(rule ccpo_Sup_least)
      fix x'
      assume "x' \<in> (\<lambda>f. f x) ` Z"
      then obtain f where "f \<in> Z" "x' = f x" by blast note this(2)
      also have "f x \<le> f y" using \<open>f \<in> Z\<close> \<open>x \<sqsubseteq> y\<close> by(rule monotoneD[OF mono])
      also have "f y \<le> ?rhs" using chain3
        by(rule ccpo_Sup_upper)(simp add: \<open>f \<in> Z\<close>)
      finally show "x' \<le> ?rhs" .
    qed
  qed

  from chain2 have "?lhs \<le> ?rhs"
  proof(rule ccpo_Sup_least)
    fix x
    assume "x \<in> (\<lambda>x. \<Squnion>(x ` Y)) ` Z"
    then obtain f where "f \<in> Z" "x = \<Squnion>(f ` Y)" by blast note this(2)
    also have "\<dots> \<le> ?rhs" using chain1[OF \<open>f \<in> Z\<close>]
    proof(rule ccpo_Sup_least)
      fix x'
      assume "x' \<in> f ` Y"
      then obtain y where "y \<in> Y" "x' = f y" by blast note this(2)
      also have "f y \<le> \<Squnion>((\<lambda>f. f y) ` Z)" using chain3
        by(rule ccpo_Sup_upper)(simp add: \<open>f \<in> Z\<close>)
      also have "\<dots> \<le> ?rhs" using chain4 by(rule ccpo_Sup_upper)(simp add: \<open>y \<in> Y\<close>)
      finally show "x' \<le> ?rhs" .
    qed
    finally show "x \<le> ?rhs" .
  qed
  moreover
  have "?rhs \<le> ?lhs" using chain4
  proof(rule ccpo_Sup_least)
    fix x
    assume "x \<in> (\<lambda>x. \<Squnion>((\<lambda>f. f x) ` Z)) ` Y"
    then obtain y where "y \<in> Y" "x = \<Squnion>((\<lambda>f. f y) ` Z)" by blast note this(2)
    also have "\<dots> \<le> ?lhs" using chain3
    proof(rule ccpo_Sup_least)
      fix x'
      assume "x' \<in> (\<lambda>f. f y) ` Z"
      then obtain f where "f \<in> Z" "x' = f y" by blast note this(2)
      also have "f y \<le> \<Squnion>(f ` Y)" using chain1[OF \<open>f \<in> Z\<close>]
        by(rule ccpo_Sup_upper)(simp add: \<open>y \<in> Y\<close>)
      also have "\<dots> \<le> ?lhs" using chain2
        by(rule ccpo_Sup_upper)(simp add: \<open>f \<in> Z\<close>)
      finally show "x' \<le> ?lhs" .
    qed
    finally show "x \<le> ?lhs" .
  qed
  ultimately show "?lhs = ?rhs"
    by (rule order.antisym)
qed

lemma fixp_mono:
  assumes fg: "fun_ord (\<le>) f g"
  and f: "monotone (\<le>) (\<le>) f"
  and g: "monotone (\<le>) (\<le>) g"
  shows "ccpo_class.fixp f \<le> ccpo_class.fixp g"
unfolding fixp_def
proof(rule ccpo_Sup_least)
  fix x
  assume "x \<in> ccpo_class.iterates f"
  thus "x \<le> \<Squnion>ccpo_class.iterates g"
  proof induction
    case (step x)
    from f step.IH have "f x \<le> f (\<Squnion>ccpo_class.iterates g)" by(rule monotoneD)
    also have "\<dots> \<le> g (\<Squnion>ccpo_class.iterates g)" using fg by(simp add: fun_ord_def)
    also have "\<dots> = \<Squnion>ccpo_class.iterates g" by(fold fixp_def fixp_unfold[OF g]) simp
    finally show ?case .
  qed(blast intro: ccpo_Sup_least)
qed(rule chain_iterates[OF f])

context fixes ordb :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) begin

lemma iterates_mono:
  assumes f: "f \<in> ccpo.iterates (fun_lub Sup) (fun_ord (\<le>)) F"
  and mono: "\<And>f. monotone (\<sqsubseteq>) (\<le>) f \<Longrightarrow> monotone (\<sqsubseteq>) (\<le>) (F f)"
  shows "monotone (\<sqsubseteq>) (\<le>) f"
using f
by(induction rule: ccpo.iterates.induct[OF ccpo_fun, consumes 1, case_names step Sup])(blast intro: mono mono_lub)+

lemma fixp_preserves_mono:
  assumes mono: "\<And>x. monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. F f x)"
  and mono2: "\<And>f. monotone (\<sqsubseteq>) (\<le>) f \<Longrightarrow> monotone (\<sqsubseteq>) (\<le>) (F f)"
  shows "monotone (\<sqsubseteq>) (\<le>) (ccpo.fixp (fun_lub Sup) (fun_ord (\<le>)) F)"
  (is "monotone _ _ ?fixp")
proof(rule monotoneI)
  have mono: "monotone (fun_ord (\<le>)) (fun_ord (\<le>)) F"
    by(rule monotoneI)(auto simp add: fun_ord_def intro: monotoneD[OF mono])
  let ?iter = "ccpo.iterates (fun_lub Sup) (fun_ord (\<le>)) F"
  have chain: "\<And>x. Complete_Partial_Order.chain (\<le>) ((\<lambda>f. f x) ` ?iter)"
    by(rule chain_imageI[OF ccpo.chain_iterates[OF ccpo_fun mono]])(simp add: fun_ord_def)

  fix x y
  assume "x \<sqsubseteq> y"
  show "?fixp x \<le> ?fixp y"
    apply (simp only: ccpo.fixp_def[OF ccpo_fun] fun_lub_apply)
    using chain
  proof(rule ccpo_Sup_least)
    fix x'
    assume "x' \<in> (\<lambda>f. f x) ` ?iter"
    then obtain f where "f \<in> ?iter" "x' = f x" by blast note this(2)
    also have "f x \<le> f y"
      by(rule monotoneD[OF iterates_mono[OF \<open>f \<in> ?iter\<close> mono2]])(blast intro: \<open>x \<sqsubseteq> y\<close>)+
    also have "f y \<le> \<Squnion>((\<lambda>f. f y) ` ?iter)" using chain
      by(rule ccpo_Sup_upper)(simp add: \<open>f \<in> ?iter\<close>)
    finally show "x' \<le> \<dots>" .
  qed
qed

end

end

lemma monotone2monotone:
  assumes 2: "\<And>x. monotone ordb ordc (\<lambda>y. f x y)"
  and t: "monotone orda ordb (\<lambda>x. t x)"
  and 1: "\<And>y. monotone orda ordc (\<lambda>x. f x y)"
  and trans: "transp ordc"
  shows "monotone orda ordc (\<lambda>x. f x (t x))"
by(blast intro: monotoneI transpD[OF trans] monotoneD[OF t] monotoneD[OF 2] monotoneD[OF 1])

subsection \<open>Continuity\<close>

definition cont :: "('a set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b set \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "cont luba orda lubb ordb f \<longleftrightarrow> 
  (\<forall>Y. Complete_Partial_Order.chain orda Y \<longrightarrow> Y \<noteq> {} \<longrightarrow> f (luba Y) = lubb (f ` Y))"

definition mcont :: "('a set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b set \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "mcont luba orda lubb ordb f \<longleftrightarrow>
   monotone orda ordb f \<and> cont luba orda lubb ordb f"

subsubsection \<open>Theorem collection \<open>cont_intro\<close>\<close>

named_theorems cont_intro "continuity and admissibility intro rules"
ML \<open>
(* apply cont_intro rules as intro and try to solve 
   the remaining of the emerging subgoals with simp *)
fun cont_intro_tac ctxt =
  REPEAT_ALL_NEW (resolve_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>cont_intro\<close>)))
  THEN_ALL_NEW (SOLVED' (simp_tac ctxt))

fun cont_intro_simproc ctxt ct =
  let
    fun mk_stmt t = t
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of ctxt
      |> Goal.init
    fun mk_thm t =
      case SINGLE (cont_intro_tac ctxt 1) (mk_stmt t) of
        SOME thm => SOME (Goal.finish ctxt thm RS @{thm Eq_TrueI})
      | NONE => NONE
  in
    case Thm.term_of ct of
      t as Const (\<^const_name>\<open>ccpo.admissible\<close>, _) $ _ $ _ $ _ => mk_thm t
    | t as Const (\<^const_name>\<open>mcont\<close>, _) $ _ $ _ $ _ $ _ $ _ => mk_thm t
    | t as Const (\<^const_name>\<open>monotone\<close>, _) $ _ $ _ $ _ => mk_thm t
    | _ => NONE
  end
  handle THM _ => NONE 
  | TYPE _ => NONE
\<close>

simproc_setup "cont_intro"
  ( "ccpo.admissible lub ord P"
  | "mcont lub ord lub' ord' f"
  | "monotone ord ord' f"
  ) = \<open>K cont_intro_simproc\<close>

lemmas [cont_intro] =
  call_mono
  let_mono
  if_mono
  option.const_mono
  tailrec.const_mono
  bind_mono

declare if_mono[simp]

lemma monotone_id' [cont_intro]: "monotone ord ord (\<lambda>x. x)"
by(simp add: monotone_def)

lemma monotone_applyI:
  "monotone orda ordb F \<Longrightarrow> monotone (fun_ord orda) ordb (\<lambda>f. F (f x))"
by(rule monotoneI)(auto simp add: fun_ord_def dest: monotoneD)

lemma monotone_if_fun [partial_function_mono]:
  "\<lbrakk> monotone (fun_ord orda) (fun_ord ordb) F; monotone (fun_ord orda) (fun_ord ordb) G \<rbrakk>
  \<Longrightarrow> monotone (fun_ord orda) (fun_ord ordb) (\<lambda>f n. if c n then F f n else G f n)"
by(simp add: monotone_def fun_ord_def)

lemma monotone_fun_apply_fun [partial_function_mono]: 
  "monotone (fun_ord (fun_ord ord)) (fun_ord ord) (\<lambda>f n. f t (g n))"
by(rule monotoneI)(simp add: fun_ord_def)

lemma monotone_fun_ord_apply: 
  "monotone orda (fun_ord ordb) f \<longleftrightarrow> (\<forall>x. monotone orda ordb (\<lambda>y. f y x))"
by(auto simp add: monotone_def fun_ord_def)

context preorder begin

declare transp_le[cont_intro]

lemma monotone_const [simp, cont_intro]: "monotone ord (\<le>) (\<lambda>_. c)"
by(rule monotoneI) simp

end

lemma transp_le [cont_intro, simp]:
  "class.preorder ord (mk_less ord) \<Longrightarrow> transp ord"
by(rule preorder.transp_le)

context partial_function_definitions begin

declare const_mono [cont_intro, simp]

lemma transp_le [cont_intro, simp]: "transp leq"
by(rule transpI)(rule leq_trans)

lemma preorder [cont_intro, simp]: "class.preorder leq (mk_less leq)"
by(unfold_locales)(auto simp add: mk_less_def intro: leq_refl leq_trans)

declare ccpo[cont_intro, simp]

end

lemma contI [intro?]:
  "(\<And>Y. \<lbrakk> Complete_Partial_Order.chain orda Y; Y \<noteq> {} \<rbrakk> \<Longrightarrow> f (luba Y) = lubb (f ` Y)) 
  \<Longrightarrow> cont luba orda lubb ordb f"
unfolding cont_def by blast

lemma contD:
  "\<lbrakk> cont luba orda lubb ordb f; Complete_Partial_Order.chain orda Y; Y \<noteq> {} \<rbrakk> 
  \<Longrightarrow> f (luba Y) = lubb (f ` Y)"
unfolding cont_def by blast

lemma cont_id [simp, cont_intro]: "\<And>Sup. cont Sup ord Sup ord id"
by(rule contI) simp

lemma cont_id' [simp, cont_intro]: "\<And>Sup. cont Sup ord Sup ord (\<lambda>x. x)"
using cont_id[unfolded id_def] .

lemma cont_applyI [cont_intro]:
  assumes cont: "cont luba orda lubb ordb g"
  shows "cont (fun_lub luba) (fun_ord orda) lubb ordb (\<lambda>f. g (f x))"
by(rule contI)(drule chain_fun_ordD[where x=x], simp add: fun_lub_apply image_image contD[OF cont])

lemma call_cont: "cont (fun_lub lub) (fun_ord ord) lub ord (\<lambda>f. f t)"
by(simp add: cont_def fun_lub_apply)

lemma cont_if [cont_intro]:
  "\<lbrakk> cont luba orda lubb ordb f; cont luba orda lubb ordb g \<rbrakk>
  \<Longrightarrow> cont luba orda lubb ordb (\<lambda>x. if c then f x else g x)"
by(cases c) simp_all

lemma mcontI [intro?]:
   "\<lbrakk> monotone orda ordb f; cont luba orda lubb ordb f \<rbrakk> \<Longrightarrow> mcont luba orda lubb ordb f"
by(simp add: mcont_def)

lemma mcont_mono: "mcont luba orda lubb ordb f \<Longrightarrow> monotone orda ordb f"
by(simp add: mcont_def)

lemma mcont_cont [simp]: "mcont luba orda lubb ordb f \<Longrightarrow> cont luba orda lubb ordb f"
by(simp add: mcont_def)

lemma mcont_monoD:
  "\<lbrakk> mcont luba orda lubb ordb f; orda x y \<rbrakk> \<Longrightarrow> ordb (f x) (f y)"
by(auto simp add: mcont_def dest: monotoneD)

lemma mcont_contD:
  "\<lbrakk> mcont luba orda lubb ordb f; Complete_Partial_Order.chain orda Y; Y \<noteq> {} \<rbrakk>
  \<Longrightarrow> f (luba Y) = lubb (f ` Y)"
by(auto simp add: mcont_def dest: contD)

lemma mcont_call [cont_intro, simp]:
  "mcont (fun_lub lub) (fun_ord ord) lub ord (\<lambda>f. f t)"
by(simp add: mcont_def call_mono call_cont)

lemma mcont_id' [cont_intro, simp]: "mcont lub ord lub ord (\<lambda>x. x)"
by(simp add: mcont_def monotone_id')

lemma mcont_applyI:
  "mcont luba orda lubb ordb (\<lambda>x. F x) \<Longrightarrow> mcont (fun_lub luba) (fun_ord orda) lubb ordb (\<lambda>f. F (f x))"
by(simp add: mcont_def monotone_applyI cont_applyI)

lemma mcont_if [cont_intro, simp]:
  "\<lbrakk> mcont luba orda lubb ordb (\<lambda>x. f x); mcont luba orda lubb ordb (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> mcont luba orda lubb ordb (\<lambda>x. if c then f x else g x)"
by(simp add: mcont_def cont_if)

lemma cont_fun_lub_apply: 
  "cont luba orda (fun_lub lubb) (fun_ord ordb) f \<longleftrightarrow> (\<forall>x. cont luba orda lubb ordb (\<lambda>y. f y x))"
by(simp add: cont_def fun_lub_def fun_eq_iff)(auto simp add: image_def)

lemma mcont_fun_lub_apply: 
  "mcont luba orda (fun_lub lubb) (fun_ord ordb) f \<longleftrightarrow> (\<forall>x. mcont luba orda lubb ordb (\<lambda>y. f y x))"
by(auto simp add: monotone_fun_ord_apply cont_fun_lub_apply mcont_def)

context ccpo begin

lemma cont_const [simp, cont_intro]: "cont luba orda Sup (\<le>) (\<lambda>x. c)"
by (rule contI) (simp add: image_constant_conv cong del: SUP_cong_simp)

lemma mcont_const [cont_intro, simp]:
  "mcont luba orda Sup (\<le>) (\<lambda>x. c)"
by(simp add: mcont_def)

lemma cont_apply:
  assumes 2: "\<And>x. cont lubb ordb Sup (\<le>) (\<lambda>y. f x y)"
  and t: "cont luba orda lubb ordb (\<lambda>x. t x)"
  and 1: "\<And>y. cont luba orda Sup (\<le>) (\<lambda>x. f x y)"
  and mono: "monotone orda ordb (\<lambda>x. t x)"
  and mono2: "\<And>x. monotone ordb (\<le>) (\<lambda>y. f x y)"
  and mono1: "\<And>y. monotone orda (\<le>) (\<lambda>x. f x y)"
  shows "cont luba orda Sup (\<le>) (\<lambda>x. f x (t x))"
proof
  fix Y
  assume chain: "Complete_Partial_Order.chain orda Y" and "Y \<noteq> {}"
  moreover from chain have chain': "Complete_Partial_Order.chain ordb (t ` Y)"
    by(rule chain_imageI)(rule monotoneD[OF mono])
  ultimately show "f (luba Y) (t (luba Y)) = \<Squnion>((\<lambda>x. f x (t x)) ` Y)"
    by(simp add: contD[OF 1] contD[OF t] contD[OF 2] image_image)
      (rule diag_Sup[OF chain], auto intro: monotone2monotone[OF mono2 mono monotone_const transpI] monotoneD[OF mono1])
qed

lemma mcont2mcont':
  "\<lbrakk> \<And>x. mcont lub' ord' Sup (\<le>) (\<lambda>y. f x y);
     \<And>y. mcont lub ord Sup (\<le>) (\<lambda>x. f x y);
     mcont lub ord lub' ord' (\<lambda>y. t y) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. f x (t x))"
unfolding mcont_def by(blast intro: transp_le monotone2monotone cont_apply)

lemma mcont2mcont:
  "\<lbrakk>mcont lub' ord' Sup (\<le>) (\<lambda>x. f x); mcont lub ord lub' ord' (\<lambda>x. t x)\<rbrakk> 
  \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. f (t x))"
by(rule mcont2mcont'[OF _ mcont_const]) 

context
  fixes ord :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>" 60) 
  and lub :: "'b set \<Rightarrow> 'b" ("\<Or>")
begin

lemma cont_fun_lub_Sup:
  assumes chainM: "Complete_Partial_Order.chain (fun_ord (\<le>)) M"
  and mcont [rule_format]: "\<forall>f\<in>M. mcont lub (\<sqsubseteq>) Sup (\<le>) f"
  shows "cont lub (\<sqsubseteq>) Sup (\<le>) (fun_lub Sup M)"
proof(rule contI)
  fix Y
  assume chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
    and Y: "Y \<noteq> {}"
  from swap_Sup[OF chain chainM mcont[THEN mcont_mono]]
  show "fun_lub Sup M (\<Or>Y) = \<Squnion>(fun_lub Sup M ` Y)"
    by(simp add: mcont_contD[OF mcont chain Y] fun_lub_apply cong: image_cong)
qed

lemma mcont_fun_lub_Sup:
  "\<lbrakk> Complete_Partial_Order.chain (fun_ord (\<le>)) M;
    \<forall>f\<in>M. mcont lub ord Sup (\<le>) f \<rbrakk>
  \<Longrightarrow> mcont lub (\<sqsubseteq>) Sup (\<le>) (fun_lub Sup M)"
by(simp add: mcont_def cont_fun_lub_Sup mono_lub)

lemma iterates_mcont:
  assumes f: "f \<in> ccpo.iterates (fun_lub Sup) (fun_ord (\<le>)) F"
  and mono: "\<And>f. mcont lub (\<sqsubseteq>) Sup (\<le>) f \<Longrightarrow> mcont lub (\<sqsubseteq>) Sup (\<le>) (F f)"
  shows "mcont lub (\<sqsubseteq>) Sup (\<le>) f"
using f
by(induction rule: ccpo.iterates.induct[OF ccpo_fun, consumes 1, case_names step Sup])(blast intro: mono mcont_fun_lub_Sup)+

lemma fixp_preserves_mcont:
  assumes mono: "\<And>x. monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. F f x)"
  and mcont: "\<And>f. mcont lub (\<sqsubseteq>) Sup (\<le>) f \<Longrightarrow> mcont lub (\<sqsubseteq>) Sup (\<le>) (F f)"
  shows "mcont lub (\<sqsubseteq>) Sup (\<le>) (ccpo.fixp (fun_lub Sup) (fun_ord (\<le>)) F)"
  (is "mcont _ _ _ _ ?fixp")
unfolding mcont_def
proof(intro conjI monotoneI contI)
  have mono: "monotone (fun_ord (\<le>)) (fun_ord (\<le>)) F"
    by(rule monotoneI)(auto simp add: fun_ord_def intro: monotoneD[OF mono])
  let ?iter = "ccpo.iterates (fun_lub Sup) (fun_ord (\<le>)) F"
  have chain: "\<And>x. Complete_Partial_Order.chain (\<le>) ((\<lambda>f. f x) ` ?iter)"
    by(rule chain_imageI[OF ccpo.chain_iterates[OF ccpo_fun mono]])(simp add: fun_ord_def)

  {
    fix x y
    assume "x \<sqsubseteq> y"
    show "?fixp x \<le> ?fixp y"
      apply (simp only: ccpo.fixp_def[OF ccpo_fun] fun_lub_apply)
      using chain
    proof(rule ccpo_Sup_least)
      fix x'
      assume "x' \<in> (\<lambda>f. f x) ` ?iter"
      then obtain f where "f \<in> ?iter" "x' = f x" by blast note this(2)
      also from _ \<open>x \<sqsubseteq> y\<close> have "f x \<le> f y"
        by(rule mcont_monoD[OF iterates_mcont[OF \<open>f \<in> ?iter\<close> mcont]])
      also have "f y \<le> \<Squnion>((\<lambda>f. f y) ` ?iter)" using chain
        by(rule ccpo_Sup_upper)(simp add: \<open>f \<in> ?iter\<close>)
      finally show "x' \<le> \<dots>" .
    qed
  next
    fix Y
    assume chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
      and Y: "Y \<noteq> {}"
    { fix f
      assume "f \<in> ?iter"
      hence "f (\<Or>Y) = \<Squnion>(f ` Y)"
        using mcont chain Y by(rule mcont_contD[OF iterates_mcont]) }
    moreover have "\<Squnion>((\<lambda>f. \<Squnion>(f ` Y)) ` ?iter) = \<Squnion>((\<lambda>x. \<Squnion>((\<lambda>f. f x) ` ?iter)) ` Y)"
      using chain ccpo.chain_iterates[OF ccpo_fun mono]
      by(rule swap_Sup)(rule mcont_mono[OF iterates_mcont[OF _ mcont]])
    ultimately show "?fixp (\<Or>Y) = \<Squnion>(?fixp ` Y)" unfolding ccpo.fixp_def[OF ccpo_fun]
      by(simp add: fun_lub_apply cong: image_cong)
  }
qed

end

context
  fixes F :: "'c \<Rightarrow> 'c" and U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a" and C :: "('b \<Rightarrow> 'a) \<Rightarrow> 'c" and f
  assumes mono: "\<And>x. monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. U (F (C f)) x)"
  and eq: "f \<equiv> C (ccpo.fixp (fun_lub Sup) (fun_ord (\<le>)) (\<lambda>f. U (F (C f))))"
  and inverse: "\<And>f. U (C f) = f"
begin

lemma fixp_preserves_mono_uc:
  assumes mono2: "\<And>f. monotone ord (\<le>) (U f) \<Longrightarrow> monotone ord (\<le>) (U (F f))"
  shows "monotone ord (\<le>) (U f)"
using fixp_preserves_mono[OF mono mono2] by(subst eq)(simp add: inverse)

lemma fixp_preserves_mcont_uc:
  assumes mcont: "\<And>f. mcont lubb ordb Sup (\<le>) (U f) \<Longrightarrow> mcont lubb ordb Sup (\<le>) (U (F f))"
  shows "mcont lubb ordb Sup (\<le>) (U f)"
using fixp_preserves_mcont[OF mono mcont] by(subst eq)(simp add: inverse)

end

lemmas fixp_preserves_mono1 = fixp_preserves_mono_uc[of "\<lambda>x. x" _ "\<lambda>x. x", OF _ _ refl]
lemmas fixp_preserves_mono2 =
  fixp_preserves_mono_uc[of "case_prod" _ "curry", unfolded case_prod_curry curry_case_prod, OF _ _ refl]
lemmas fixp_preserves_mono3 =
  fixp_preserves_mono_uc[of "\<lambda>f. case_prod (case_prod f)" _ "\<lambda>f. curry (curry f)", unfolded case_prod_curry curry_case_prod, OF _ _ refl]
lemmas fixp_preserves_mono4 =
  fixp_preserves_mono_uc[of "\<lambda>f. case_prod (case_prod (case_prod f))" _ "\<lambda>f. curry (curry (curry f))", unfolded case_prod_curry curry_case_prod, OF _ _ refl]

lemmas fixp_preserves_mcont1 = fixp_preserves_mcont_uc[of "\<lambda>x. x" _ "\<lambda>x. x", OF _ _ refl]
lemmas fixp_preserves_mcont2 =
  fixp_preserves_mcont_uc[of "case_prod" _ "curry", unfolded case_prod_curry curry_case_prod, OF _ _ refl]
lemmas fixp_preserves_mcont3 =
  fixp_preserves_mcont_uc[of "\<lambda>f. case_prod (case_prod f)" _ "\<lambda>f. curry (curry f)", unfolded case_prod_curry curry_case_prod, OF _ _ refl]
lemmas fixp_preserves_mcont4 =
  fixp_preserves_mcont_uc[of "\<lambda>f. case_prod (case_prod (case_prod f))" _ "\<lambda>f. curry (curry (curry f))", unfolded case_prod_curry curry_case_prod, OF _ _ refl]

end

lemma (in preorder) monotone_if_bot:
  fixes bot
  assumes mono: "\<And>x y. \<lbrakk> x \<le> y; \<not> (x \<le> bound) \<rbrakk> \<Longrightarrow> ord (f x) (f y)"
  and bot: "\<And>x. \<not> x \<le> bound \<Longrightarrow> ord bot (f x)" "ord bot bot"
  shows "monotone (\<le>) ord (\<lambda>x. if x \<le> bound then bot else f x)"
by(rule monotoneI)(auto intro: bot intro: mono order_trans)

lemma (in ccpo) mcont_if_bot:
  fixes bot and lub ("\<Or>") and ord (infix "\<sqsubseteq>" 60)
  assumes ccpo: "class.ccpo lub (\<sqsubseteq>) lt"
  and mono: "\<And>x y. \<lbrakk> x \<le> y; \<not> x \<le> bound \<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y"
  and cont: "\<And>Y. \<lbrakk> Complete_Partial_Order.chain (\<le>) Y; Y \<noteq> {}; \<And>x. x \<in> Y \<Longrightarrow> \<not> x \<le> bound \<rbrakk> \<Longrightarrow> f (\<Squnion>Y) = \<Or>(f ` Y)"
  and bot: "\<And>x. \<not> x \<le> bound \<Longrightarrow> bot \<sqsubseteq> f x"
  shows "mcont Sup (\<le>) lub (\<sqsubseteq>) (\<lambda>x. if x \<le> bound then bot else f x)" (is "mcont _ _ _ _ ?g")
proof(intro mcontI contI)
  interpret c: ccpo lub "(\<sqsubseteq>)" lt by(fact ccpo)
  show "monotone (\<le>) (\<sqsubseteq>) ?g" by(rule monotone_if_bot)(simp_all add: mono bot)

  fix Y
  assume chain: "Complete_Partial_Order.chain (\<le>) Y" and Y: "Y \<noteq> {}"
  show "?g (\<Squnion>Y) = \<Or>(?g ` Y)"
  proof(cases "Y \<subseteq> {x. x \<le> bound}")
    case True
    hence "\<Squnion>Y \<le> bound" using chain by(auto intro: ccpo_Sup_least)
    moreover have "Y \<inter> {x. \<not> x \<le> bound} = {}" using True by auto
    ultimately show ?thesis using True Y
      by (auto simp add: image_constant_conv cong del: c.SUP_cong_simp)
  next
    case False
    let ?Y = "Y \<inter> {x. \<not> x \<le> bound}"
    have chain': "Complete_Partial_Order.chain (\<le>) ?Y"
      using chain by(rule chain_subset) simp

    from False obtain y where ybound: "\<not> y \<le> bound" and y: "y \<in> Y" by blast
    hence "\<not> \<Squnion>Y \<le> bound" by (metis ccpo_Sup_upper chain order.trans)
    hence "?g (\<Squnion>Y) = f (\<Squnion>Y)" by simp
    also have "\<Squnion>Y \<le> \<Squnion>?Y" using chain
    proof(rule ccpo_Sup_least)
      fix x
      assume x: "x \<in> Y"
      show "x \<le> \<Squnion>?Y"
      proof(cases "x \<le> bound")
        case True
        with chainD[OF chain x y] have "x \<le> y" using ybound by(auto intro: order_trans)
        thus ?thesis by(rule order_trans)(auto intro: ccpo_Sup_upper[OF chain'] simp add: y ybound)
      qed(auto intro: ccpo_Sup_upper[OF chain'] simp add: x)
    qed
    hence "\<Squnion>Y = \<Squnion>?Y" by(rule order.antisym)(blast intro: ccpo_Sup_least[OF chain'] ccpo_Sup_upper[OF chain])
    hence "f (\<Squnion>Y) = f (\<Squnion>?Y)" by simp
    also have "f (\<Squnion>?Y) = \<Or>(f ` ?Y)" using chain' by(rule cont)(insert y ybound, auto)
    also have "\<Or>(f ` ?Y) = \<Or>(?g ` Y)"
    proof(cases "Y \<inter> {x. x \<le> bound} = {}")
      case True
      hence "f ` ?Y = ?g ` Y" by auto
      thus ?thesis by(rule arg_cong)
    next
      case False
      have chain'': "Complete_Partial_Order.chain (\<sqsubseteq>) (insert bot (f ` ?Y))"
        using chain by(auto intro!: chainI bot dest: chainD intro: mono)
      hence chain''': "Complete_Partial_Order.chain (\<sqsubseteq>) (f ` ?Y)" by(rule chain_subset) blast
      have "bot \<sqsubseteq> \<Or>(f ` ?Y)" using y ybound by(blast intro: c.order_trans[OF bot] c.ccpo_Sup_upper[OF chain'''])
      hence "\<Or>(insert bot (f ` ?Y)) \<sqsubseteq> \<Or>(f ` ?Y)" using chain''
        by(auto intro: c.ccpo_Sup_least c.ccpo_Sup_upper[OF chain''']) 
      with _ have "\<dots> = \<Or>(insert bot (f ` ?Y))"
        by(rule c.order.antisym)(blast intro: c.ccpo_Sup_least[OF chain'''] c.ccpo_Sup_upper[OF chain''])
      also have "insert bot (f ` ?Y) = ?g ` Y" using False by auto
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
qed

context partial_function_definitions begin

lemma mcont_const [cont_intro, simp]:
  "mcont luba orda lub leq (\<lambda>x. c)"
by(rule ccpo.mcont_const)(rule Partial_Function.ccpo[OF partial_function_definitions_axioms])

lemmas [cont_intro, simp] =
  ccpo.cont_const[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]

lemma mono2mono:
  assumes "monotone ordb leq (\<lambda>y. f y)" "monotone orda ordb (\<lambda>x. t x)"
  shows "monotone orda leq (\<lambda>x. f (t x))"
using assms by(rule monotone2monotone) simp_all

lemmas mcont2mcont' = ccpo.mcont2mcont'[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas mcont2mcont = ccpo.mcont2mcont[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]

lemmas fixp_preserves_mono1 = ccpo.fixp_preserves_mono1[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mono2 = ccpo.fixp_preserves_mono2[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mono3 = ccpo.fixp_preserves_mono3[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mono4 = ccpo.fixp_preserves_mono4[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mcont1 = ccpo.fixp_preserves_mcont1[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mcont2 = ccpo.fixp_preserves_mcont2[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mcont3 = ccpo.fixp_preserves_mcont3[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
lemmas fixp_preserves_mcont4 = ccpo.fixp_preserves_mcont4[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]

lemma monotone_if_bot:
  fixes bot
  assumes g: "\<And>x. g x = (if leq x bound then bot else f x)"
  and mono: "\<And>x y. \<lbrakk> leq x y; \<not> leq x bound \<rbrakk> \<Longrightarrow> ord (f x) (f y)"
  and bot: "\<And>x. \<not> leq x bound \<Longrightarrow> ord bot (f x)" "ord bot bot"
  shows "monotone leq ord g"
unfolding g[abs_def] using preorder mono bot by(rule preorder.monotone_if_bot)

lemma mcont_if_bot:
  fixes bot
  assumes ccpo: "class.ccpo lub' ord (mk_less ord)"
  and bot: "\<And>x. \<not> leq x bound \<Longrightarrow> ord bot (f x)"
  and g: "\<And>x. g x = (if leq x bound then bot else f x)"
  and mono: "\<And>x y. \<lbrakk> leq x y; \<not> leq x bound \<rbrakk> \<Longrightarrow> ord (f x) (f y)"
  and cont: "\<And>Y. \<lbrakk> Complete_Partial_Order.chain leq Y; Y \<noteq> {}; \<And>x. x \<in> Y \<Longrightarrow> \<not> leq x bound \<rbrakk> \<Longrightarrow> f (lub Y) = lub' (f ` Y)"
  shows "mcont lub leq lub' ord g"
unfolding g[abs_def] using ccpo mono cont bot by(rule ccpo.mcont_if_bot[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]])

end

subsection \<open>Admissibility\<close>

lemma admissible_subst:
  assumes adm: "ccpo.admissible luba orda (\<lambda>x. P x)"
  and mcont: "mcont lubb ordb luba orda f"
  shows "ccpo.admissible lubb ordb (\<lambda>x. P (f x))"
apply(rule ccpo.admissibleI)
apply(frule (1) mcont_contD[OF mcont])
apply(auto intro: ccpo.admissibleD[OF adm] chain_imageI dest: mcont_monoD[OF mcont])
done

lemmas [simp, cont_intro] = 
  admissible_all
  admissible_ball
  admissible_const
  admissible_conj

lemma admissible_disj' [simp, cont_intro]:
  "\<lbrakk> class.ccpo lub ord (mk_less ord); ccpo.admissible lub ord P; ccpo.admissible lub ord Q \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. P x \<or> Q x)"
by(rule ccpo.admissible_disj)

lemma admissible_imp' [cont_intro]:
  "\<lbrakk> class.ccpo lub ord (mk_less ord);
     ccpo.admissible lub ord (\<lambda>x. \<not> P x);
     ccpo.admissible lub ord (\<lambda>x. Q x) \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. P x \<longrightarrow> Q x)"
unfolding imp_conv_disj by(rule ccpo.admissible_disj)

lemma admissible_imp [cont_intro]:
  "(Q \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. P x))
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. Q \<longrightarrow> P x)"
by(rule ccpo.admissibleI)(auto dest: ccpo.admissibleD)

lemma admissible_not_mem' [THEN admissible_subst, cont_intro, simp]:
  shows admissible_not_mem: "ccpo.admissible Union (\<subseteq>) (\<lambda>A. x \<notin> A)"
by(rule ccpo.admissibleI) auto

lemma admissible_eqI:
  assumes f: "cont luba orda lub ord (\<lambda>x. f x)"
  and g: "cont luba orda lub ord (\<lambda>x. g x)"
  shows "ccpo.admissible luba orda (\<lambda>x. f x = g x)"
apply(rule ccpo.admissibleI)
apply(simp_all add: contD[OF f] contD[OF g] cong: image_cong)
done

corollary admissible_eq_mcontI [cont_intro]:
  "\<lbrakk> mcont luba orda lub ord (\<lambda>x. f x); 
    mcont luba orda lub ord (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> ccpo.admissible luba orda (\<lambda>x. f x = g x)"
by(rule admissible_eqI)(auto simp add: mcont_def)

lemma admissible_iff [cont_intro, simp]:
  "\<lbrakk> ccpo.admissible lub ord (\<lambda>x. P x \<longrightarrow> Q x); ccpo.admissible lub ord (\<lambda>x. Q x \<longrightarrow> P x) \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. P x \<longleftrightarrow> Q x)"
by(subst iff_conv_conj_imp)(rule admissible_conj)

context ccpo begin

lemma admissible_leI:
  assumes f: "mcont luba orda Sup (\<le>) (\<lambda>x. f x)"
  and g: "mcont luba orda Sup (\<le>) (\<lambda>x. g x)"
  shows "ccpo.admissible luba orda (\<lambda>x. f x \<le> g x)"
proof(rule ccpo.admissibleI)
  fix A
  assume chain: "Complete_Partial_Order.chain orda A"
    and le: "\<forall>x\<in>A. f x \<le> g x"
    and False: "A \<noteq> {}"
  have "f (luba A) = \<Squnion>(f ` A)" by(simp add: mcont_contD[OF f] chain False)
  also have "\<dots> \<le> \<Squnion>(g ` A)"
  proof(rule ccpo_Sup_least)
    from chain show "Complete_Partial_Order.chain (\<le>) (f ` A)"
      by(rule chain_imageI)(rule mcont_monoD[OF f])
    
    fix x
    assume "x \<in> f ` A"
    then obtain y where "y \<in> A" "x = f y" by blast note this(2)
    also have "f y \<le> g y" using le \<open>y \<in> A\<close> by simp
    also have "Complete_Partial_Order.chain (\<le>) (g ` A)"
      using chain by(rule chain_imageI)(rule mcont_monoD[OF g])
    hence "g y \<le> \<Squnion>(g ` A)" by(rule ccpo_Sup_upper)(simp add: \<open>y \<in> A\<close>)
    finally show "x \<le> \<dots>" .
  qed
  also have "\<dots> = g (luba A)" by(simp add: mcont_contD[OF g] chain False)
  finally show "f (luba A) \<le> g (luba A)" .
qed

end

lemma admissible_leI:
  fixes ord (infix "\<sqsubseteq>" 60) and lub ("\<Or>")
  assumes "class.ccpo lub (\<sqsubseteq>) (mk_less (\<sqsubseteq>))"
  and "mcont luba orda lub (\<sqsubseteq>) (\<lambda>x. f x)"
  and "mcont luba orda lub (\<sqsubseteq>) (\<lambda>x. g x)"
  shows "ccpo.admissible luba orda (\<lambda>x. f x \<sqsubseteq> g x)"
using assms by(rule ccpo.admissible_leI)

declare ccpo_class.admissible_leI[cont_intro]

context ccpo begin

lemma admissible_not_below: "ccpo.admissible Sup (\<le>) (\<lambda>x. \<not> (\<le>) x y)"
by(rule ccpo.admissibleI)(simp add: ccpo_Sup_below_iff)

end

lemma (in preorder) preorder [cont_intro, simp]: "class.preorder (\<le>) (mk_less (\<le>))"
by(unfold_locales)(auto simp add: mk_less_def intro: order_trans)

context partial_function_definitions begin

lemmas [cont_intro, simp] =
  admissible_leI[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]
  ccpo.admissible_not_below[THEN admissible_subst, OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]

end

setup \<open>Sign.map_naming (Name_Space.mandatory_path "ccpo")\<close>

inductive compact :: "('a set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for lub ord x 
where compact:
  "\<lbrakk> ccpo.admissible lub ord (\<lambda>y. \<not> ord x y);
     ccpo.admissible lub ord (\<lambda>y. x \<noteq> y) \<rbrakk>
  \<Longrightarrow> compact lub ord x"

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

context ccpo begin

lemma compactI:
  assumes "ccpo.admissible Sup (\<le>) (\<lambda>y. \<not> x \<le> y)"
  shows "ccpo.compact Sup (\<le>) x"
using assms
proof(rule ccpo.compact.intros)
  have neq: "(\<lambda>y. x \<noteq> y) = (\<lambda>y. \<not> x \<le> y \<or> \<not> y \<le> x)" by(auto)
  show "ccpo.admissible Sup (\<le>) (\<lambda>y. x \<noteq> y)"
    by(subst neq)(rule admissible_disj admissible_not_below assms)+
qed

lemma compact_bot:
  assumes "x = Sup {}"
  shows "ccpo.compact Sup (\<le>) x"
proof(rule compactI)
  show "ccpo.admissible Sup (\<le>) (\<lambda>y. \<not> x \<le> y)" using assms
    by(auto intro!: ccpo.admissibleI intro: ccpo_Sup_least chain_empty)
qed

end

lemma admissible_compact_neq' [THEN admissible_subst, cont_intro, simp]:
  shows admissible_compact_neq: "ccpo.compact lub ord k \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. k \<noteq> x)"
by(simp add: ccpo.compact.simps)

lemma admissible_neq_compact' [THEN admissible_subst, cont_intro, simp]:
  shows admissible_neq_compact: "ccpo.compact lub ord k \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. x \<noteq> k)"
by(subst eq_commute)(rule admissible_compact_neq)

context partial_function_definitions begin

lemmas [cont_intro, simp] = ccpo.compact_bot[OF Partial_Function.ccpo[OF partial_function_definitions_axioms]]

end

context ccpo begin

lemma fixp_strong_induct:
  assumes [cont_intro]: "ccpo.admissible Sup (\<le>) P"
  and mono: "monotone (\<le>) (\<le>) f"
  and bot: "P (\<Squnion>{})"
  and step: "\<And>x. \<lbrakk> x \<le> ccpo_class.fixp f; P x \<rbrakk> \<Longrightarrow> P (f x)"
  shows "P (ccpo_class.fixp f)"
proof(rule fixp_induct[where P="\<lambda>x. x \<le> ccpo_class.fixp f \<and> P x", THEN conjunct2])
  note [cont_intro] = admissible_leI
  show "ccpo.admissible Sup (\<le>) (\<lambda>x. x \<le> ccpo_class.fixp f \<and> P x)" by simp
next
  show "\<Squnion>{} \<le> ccpo_class.fixp f \<and> P (\<Squnion>{})"
    by(auto simp add: bot intro: ccpo_Sup_least chain_empty)
next
  fix x
  assume "x \<le> ccpo_class.fixp f \<and> P x"
  thus "f x \<le> ccpo_class.fixp f \<and> P (f x)"
    by(subst fixp_unfold[OF mono])(auto dest: monotoneD[OF mono] intro: step)
qed(rule mono)

end

context partial_function_definitions begin

lemma fixp_strong_induct_uc:
  fixes F :: "'c \<Rightarrow> 'c"
    and U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a"
    and C :: "('b \<Rightarrow> 'a) \<Rightarrow> 'c"
    and P :: "('b \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_body (\<lambda>f. U (F (C f)) x)"
    and eq: "f \<equiv> C (fixp_fun (\<lambda>f. U (F (C f))))"
    and inverse: "\<And>f. U (C f) = f"
    and adm: "ccpo.admissible lub_fun le_fun P"
    and bot: "P (\<lambda>_. lub {})"
    and step: "\<And>f'. \<lbrakk> P (U f'); le_fun (U f') (U f) \<rbrakk> \<Longrightarrow> P (U (F f'))"
  shows "P (U f)"
unfolding eq inverse
apply (rule ccpo.fixp_strong_induct[OF ccpo adm])
apply (insert mono, auto simp: monotone_def fun_ord_def bot fun_lub_def)[2]
apply (rule_tac f'5="C x" in step)
apply (simp_all add: inverse eq)
done

end

subsection \<open>\<^term>\<open>(=)\<close> as order\<close>

definition lub_singleton :: "('a set \<Rightarrow> 'a) \<Rightarrow> bool"
where "lub_singleton lub \<longleftrightarrow> (\<forall>a. lub {a} = a)"

definition the_Sup :: "'a set \<Rightarrow> 'a"
where "the_Sup A = (THE a. a \<in> A)"

lemma lub_singleton_the_Sup [cont_intro, simp]: "lub_singleton the_Sup"
by(simp add: lub_singleton_def the_Sup_def)

lemma (in ccpo) lub_singleton: "lub_singleton Sup"
by(simp add: lub_singleton_def)

lemma (in partial_function_definitions) lub_singleton [cont_intro, simp]: "lub_singleton lub"
by(rule ccpo.lub_singleton)(rule Partial_Function.ccpo[OF partial_function_definitions_axioms])

lemma preorder_eq [cont_intro, simp]:
  "class.preorder (=) (mk_less (=))"
by(unfold_locales)(simp_all add: mk_less_def)

lemma monotone_eqI [cont_intro]:
  assumes "class.preorder ord (mk_less ord)"
  shows "monotone (=) ord f"
proof -
  interpret preorder ord "mk_less ord" by fact
  show ?thesis by(simp add: monotone_def)
qed

lemma cont_eqI [cont_intro]: 
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "lub_singleton lub"
  shows "cont the_Sup (=) lub ord f"
proof(rule contI)
  fix Y :: "'a set"
  assume "Complete_Partial_Order.chain (=) Y" "Y \<noteq> {}"
  then obtain a where "Y = {a}" by(auto simp add: chain_def)
  thus "f (the_Sup Y) = lub (f ` Y)" using assms
    by(simp add: the_Sup_def lub_singleton_def)
qed

lemma mcont_eqI [cont_intro, simp]:
  "\<lbrakk> class.preorder ord (mk_less ord); lub_singleton lub \<rbrakk>
  \<Longrightarrow> mcont the_Sup (=) lub ord f"
by(simp add: mcont_def cont_eqI monotone_eqI)

subsection \<open>ccpo for products\<close>

definition prod_lub :: "('a set \<Rightarrow> 'a) \<Rightarrow> ('b set \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b"
where "prod_lub Sup_a Sup_b Y = (Sup_a (fst ` Y), Sup_b (snd ` Y))"

lemma lub_singleton_prod_lub [cont_intro, simp]:
  "\<lbrakk> lub_singleton luba; lub_singleton lubb \<rbrakk> \<Longrightarrow> lub_singleton (prod_lub luba lubb)"
by(simp add: lub_singleton_def prod_lub_def)

lemma prod_lub_empty [simp]: "prod_lub luba lubb {} = (luba {}, lubb {})"
by(simp add: prod_lub_def)

lemma preorder_rel_prodI [cont_intro, simp]:
  assumes "class.preorder orda (mk_less orda)"
  and "class.preorder ordb (mk_less ordb)"
  shows "class.preorder (rel_prod orda ordb) (mk_less (rel_prod orda ordb))"
proof -
  interpret a: preorder orda "mk_less orda" by fact
  interpret b: preorder ordb "mk_less ordb" by fact
  show ?thesis by(unfold_locales)(auto simp add: mk_less_def intro: a.order_trans b.order_trans)
qed

lemma order_rel_prodI:
  assumes a: "class.order orda (mk_less orda)"
  and b: "class.order ordb (mk_less ordb)"
  shows "class.order (rel_prod orda ordb) (mk_less (rel_prod orda ordb))"
  (is "class.order ?ord ?ord'")
proof(intro class.order.intro class.order_axioms.intro)
  interpret a: order orda "mk_less orda" by(fact a)
  interpret b: order ordb "mk_less ordb" by(fact b)
  show "class.preorder ?ord ?ord'" by(rule preorder_rel_prodI) unfold_locales

  fix x y
  assume "?ord x y" "?ord y x"
  thus "x = y" by(cases x y rule: prod.exhaust[case_product prod.exhaust]) auto
qed

lemma monotone_rel_prodI:
  assumes mono2: "\<And>a. monotone ordb ordc (\<lambda>b. f (a, b))"
  and mono1: "\<And>b. monotone orda ordc (\<lambda>a. f (a, b))"
  and a: "class.preorder orda (mk_less orda)"
  and b: "class.preorder ordb (mk_less ordb)"
  and c: "class.preorder ordc (mk_less ordc)"
  shows "monotone (rel_prod orda ordb) ordc f"
proof -
  interpret a: preorder orda "mk_less orda" by(rule a)
  interpret b: preorder ordb "mk_less ordb" by(rule b)
  interpret c: preorder ordc "mk_less ordc" by(rule c)
  show ?thesis using mono2 mono1
    by(auto 7 2 simp add: monotone_def intro: c.order_trans)
qed

lemma monotone_rel_prodD1:
  assumes mono: "monotone (rel_prod orda ordb) ordc f"
  and preorder: "class.preorder ordb (mk_less ordb)"
  shows "monotone orda ordc (\<lambda>a. f (a, b))"
proof -
  interpret preorder ordb "mk_less ordb" by(rule preorder)
  show ?thesis using mono by(simp add: monotone_def)
qed

lemma monotone_rel_prodD2:
  assumes mono: "monotone (rel_prod orda ordb) ordc f"
  and preorder: "class.preorder orda (mk_less orda)"
  shows "monotone ordb ordc (\<lambda>b. f (a, b))"
proof -
  interpret preorder orda "mk_less orda" by(rule preorder)
  show ?thesis using mono by(simp add: monotone_def)
qed

lemma monotone_case_prodI:
  "\<lbrakk> \<And>a. monotone ordb ordc (f a); \<And>b. monotone orda ordc (\<lambda>a. f a b);
    class.preorder orda (mk_less orda); class.preorder ordb (mk_less ordb);
    class.preorder ordc (mk_less ordc) \<rbrakk>
  \<Longrightarrow> monotone (rel_prod orda ordb) ordc (case_prod f)"
by(rule monotone_rel_prodI) simp_all

lemma monotone_case_prodD1:
  assumes mono: "monotone (rel_prod orda ordb) ordc (case_prod f)"
  and preorder: "class.preorder ordb (mk_less ordb)"
  shows "monotone orda ordc (\<lambda>a. f a b)"
using monotone_rel_prodD1[OF assms] by simp

lemma monotone_case_prodD2:
  assumes mono: "monotone (rel_prod orda ordb) ordc (case_prod f)"
  and preorder: "class.preorder orda (mk_less orda)"
  shows "monotone ordb ordc (f a)"
using monotone_rel_prodD2[OF assms] by simp

context 
  fixes orda ordb ordc
  assumes a: "class.preorder orda (mk_less orda)"
  and b: "class.preorder ordb (mk_less ordb)"
  and c: "class.preorder ordc (mk_less ordc)"
begin

lemma monotone_rel_prod_iff:
  "monotone (rel_prod orda ordb) ordc f \<longleftrightarrow>
   (\<forall>a. monotone ordb ordc (\<lambda>b. f (a, b))) \<and> 
   (\<forall>b. monotone orda ordc (\<lambda>a. f (a, b)))"
using a b c by(blast intro: monotone_rel_prodI dest: monotone_rel_prodD1 monotone_rel_prodD2)

lemma monotone_case_prod_iff [simp]:
  "monotone (rel_prod orda ordb) ordc (case_prod f) \<longleftrightarrow>
   (\<forall>a. monotone ordb ordc (f a)) \<and> (\<forall>b. monotone orda ordc (\<lambda>a. f a b))"
by(simp add: monotone_rel_prod_iff)

end

lemma monotone_case_prod_apply_iff:
  "monotone orda ordb (\<lambda>x. (case_prod f x) y) \<longleftrightarrow> monotone orda ordb (case_prod (\<lambda>a b. f a b y))"
by(simp add: monotone_def)

lemma monotone_case_prod_applyD:
  "monotone orda ordb (\<lambda>x. (case_prod f x) y)
  \<Longrightarrow> monotone orda ordb (case_prod (\<lambda>a b. f a b y))"
by(simp add: monotone_case_prod_apply_iff)

lemma monotone_case_prod_applyI:
  "monotone orda ordb (case_prod (\<lambda>a b. f a b y))
  \<Longrightarrow> monotone orda ordb (\<lambda>x. (case_prod f x) y)"
by(simp add: monotone_case_prod_apply_iff)


lemma cont_case_prod_apply_iff:
  "cont luba orda lubb ordb (\<lambda>x. (case_prod f x) y) \<longleftrightarrow> cont luba orda lubb ordb (case_prod (\<lambda>a b. f a b y))"
by(simp add: cont_def split_def)

lemma cont_case_prod_applyI:
  "cont luba orda lubb ordb (case_prod (\<lambda>a b. f a b y))
  \<Longrightarrow> cont luba orda lubb ordb (\<lambda>x. (case_prod f x) y)"
by(simp add: cont_case_prod_apply_iff)

lemma cont_case_prod_applyD:
  "cont luba orda lubb ordb (\<lambda>x. (case_prod f x) y)
  \<Longrightarrow> cont luba orda lubb ordb (case_prod (\<lambda>a b. f a b y))"
by(simp add: cont_case_prod_apply_iff)

lemma mcont_case_prod_apply_iff [simp]:
  "mcont luba orda lubb ordb (\<lambda>x. (case_prod f x) y) \<longleftrightarrow> 
   mcont luba orda lubb ordb (case_prod (\<lambda>a b. f a b y))"
by(simp add: mcont_def monotone_case_prod_apply_iff cont_case_prod_apply_iff)

lemma cont_prodD1: 
  assumes cont: "cont (prod_lub luba lubb) (rel_prod orda ordb) lubc ordc f"
  and "class.preorder orda (mk_less orda)"
  and luba: "lub_singleton luba"
  shows "cont lubb ordb lubc ordc (\<lambda>y. f (x, y))"
proof(rule contI)
  interpret preorder orda "mk_less orda" by fact

  fix Y :: "'b set"
  let ?Y = "{x} \<times> Y"
  assume "Complete_Partial_Order.chain ordb Y" "Y \<noteq> {}"
  hence "Complete_Partial_Order.chain (rel_prod orda ordb) ?Y" "?Y \<noteq> {}" 
    by(simp_all add: chain_def)
  with cont have "f (prod_lub luba lubb ?Y) = lubc (f ` ?Y)" by(rule contD)
  moreover have "f ` ?Y = (\<lambda>y. f (x, y)) ` Y" by auto
  ultimately show "f (x, lubb Y) = lubc ((\<lambda>y. f (x, y)) ` Y)" using luba
    by(simp add: prod_lub_def \<open>Y \<noteq> {}\<close> lub_singleton_def)
qed

lemma cont_prodD2: 
  assumes cont: "cont (prod_lub luba lubb) (rel_prod orda ordb) lubc ordc f"
  and "class.preorder ordb (mk_less ordb)"
  and lubb: "lub_singleton lubb"
  shows "cont luba orda lubc ordc (\<lambda>x. f (x, y))"
proof(rule contI)
  interpret preorder ordb "mk_less ordb" by fact

  fix Y
  assume Y: "Complete_Partial_Order.chain orda Y" "Y \<noteq> {}"
  let ?Y = "Y \<times> {y}"
  have "f (luba Y, y) = f (prod_lub luba lubb ?Y)"
    using lubb by(simp add: prod_lub_def Y lub_singleton_def)
  also from Y have "Complete_Partial_Order.chain (rel_prod orda ordb) ?Y" "?Y \<noteq> {}"
    by(simp_all add: chain_def)
  with cont have "f (prod_lub luba lubb ?Y) = lubc (f ` ?Y)" by(rule contD)
  also have "f ` ?Y = (\<lambda>x. f (x, y)) ` Y" by auto
  finally show "f (luba Y, y) = lubc \<dots>" .
qed

lemma cont_case_prodD1:
  assumes "cont (prod_lub luba lubb) (rel_prod orda ordb) lubc ordc (case_prod f)"
  and "class.preorder orda (mk_less orda)"
  and "lub_singleton luba"
  shows "cont lubb ordb lubc ordc (f x)"
using cont_prodD1[OF assms] by simp

lemma cont_case_prodD2:
  assumes "cont (prod_lub luba lubb) (rel_prod orda ordb) lubc ordc (case_prod f)"
  and "class.preorder ordb (mk_less ordb)"
  and "lub_singleton lubb"
  shows "cont luba orda lubc ordc (\<lambda>x. f x y)"
using cont_prodD2[OF assms] by simp

context ccpo begin

lemma cont_prodI: 
  assumes mono: "monotone (rel_prod orda ordb) (\<le>) f"
  and cont1: "\<And>x. cont lubb ordb Sup (\<le>) (\<lambda>y. f (x, y))"
  and cont2: "\<And>y. cont luba orda Sup (\<le>) (\<lambda>x. f (x, y))"
  and "class.preorder orda (mk_less orda)"
  and "class.preorder ordb (mk_less ordb)"
  shows "cont (prod_lub luba lubb) (rel_prod orda ordb) Sup (\<le>) f"
proof(rule contI)
  interpret a: preorder orda "mk_less orda" by fact 
  interpret b: preorder ordb "mk_less ordb" by fact
  
  fix Y
  assume chain: "Complete_Partial_Order.chain (rel_prod orda ordb) Y"
    and "Y \<noteq> {}"
  have "f (prod_lub luba lubb Y) = f (luba (fst ` Y), lubb (snd ` Y))"
    by(simp add: prod_lub_def)
  also from cont2 have "f (luba (fst ` Y), lubb (snd ` Y)) = \<Squnion>((\<lambda>x. f (x, lubb (snd ` Y))) ` fst ` Y)"
    by(rule contD)(simp_all add: chain_rel_prodD1[OF chain] \<open>Y \<noteq> {}\<close>)
  also from cont1 have "\<And>x. f (x, lubb (snd ` Y)) = \<Squnion>((\<lambda>y. f (x, y)) ` snd ` Y)"
    by(rule contD)(simp_all add: chain_rel_prodD2[OF chain] \<open>Y \<noteq> {}\<close>)
  hence "\<Squnion>((\<lambda>x. f (x, lubb (snd ` Y))) ` fst ` Y) = \<Squnion>((\<lambda>x. \<dots> x) ` fst ` Y)" by simp
  also have "\<dots> = \<Squnion>((\<lambda>x. f (fst x, snd x)) ` Y)"
    unfolding image_image split_def using chain
    apply(rule diag_Sup)
    using monotoneD[OF mono]
    by(auto intro: monotoneI)
  finally show "f (prod_lub luba lubb Y) = \<Squnion>(f ` Y)" by simp
qed

lemma cont_case_prodI:
  assumes "monotone (rel_prod orda ordb) (\<le>) (case_prod f)"
  and "\<And>x. cont lubb ordb Sup (\<le>) (\<lambda>y. f x y)"
  and "\<And>y. cont luba orda Sup (\<le>) (\<lambda>x. f x y)"
  and "class.preorder orda (mk_less orda)"
  and "class.preorder ordb (mk_less ordb)"
  shows "cont (prod_lub luba lubb) (rel_prod orda ordb) Sup (\<le>) (case_prod f)"
by(rule cont_prodI)(simp_all add: assms)

lemma cont_case_prod_iff:
  "\<lbrakk> monotone (rel_prod orda ordb) (\<le>) (case_prod f);
     class.preorder orda (mk_less orda); lub_singleton luba;
     class.preorder ordb (mk_less ordb); lub_singleton lubb \<rbrakk>
  \<Longrightarrow> cont (prod_lub luba lubb) (rel_prod orda ordb) Sup (\<le>) (case_prod f) \<longleftrightarrow>
   (\<forall>x. cont lubb ordb Sup (\<le>) (\<lambda>y. f x y)) \<and> (\<forall>y. cont luba orda Sup (\<le>) (\<lambda>x. f x y))"
by(blast dest: cont_case_prodD1 cont_case_prodD2 intro: cont_case_prodI)

end

context partial_function_definitions begin

lemma mono2mono2:
  assumes f: "monotone (rel_prod ordb ordc) leq (\<lambda>(x, y). f x y)"
  and t: "monotone orda ordb (\<lambda>x. t x)"
  and t': "monotone orda ordc (\<lambda>x. t' x)"
  shows "monotone orda leq (\<lambda>x. f (t x) (t' x))"
proof(rule monotoneI)
  fix x y
  assume "orda x y"
  hence "rel_prod ordb ordc (t x, t' x) (t y, t' y)"
    using t t' by(auto dest: monotoneD)
  from monotoneD[OF f this] show "leq (f (t x) (t' x)) (f (t y) (t' y))" by simp
qed

lemma cont_case_prodI [cont_intro]:
  "\<lbrakk> monotone (rel_prod orda ordb) leq (case_prod f);
    \<And>x. cont lubb ordb lub leq (\<lambda>y. f x y);
    \<And>y. cont luba orda lub leq (\<lambda>x. f x y);
    class.preorder orda (mk_less orda);
    class.preorder ordb (mk_less ordb) \<rbrakk>
  \<Longrightarrow> cont (prod_lub luba lubb) (rel_prod orda ordb) lub leq (case_prod f)"
by(rule ccpo.cont_case_prodI)(rule Partial_Function.ccpo[OF partial_function_definitions_axioms])

lemma cont_case_prod_iff:
  "\<lbrakk> monotone (rel_prod orda ordb) leq (case_prod f);
     class.preorder orda (mk_less orda); lub_singleton luba;
     class.preorder ordb (mk_less ordb); lub_singleton lubb \<rbrakk>
  \<Longrightarrow> cont (prod_lub luba lubb) (rel_prod orda ordb) lub leq (case_prod f) \<longleftrightarrow>
   (\<forall>x. cont lubb ordb lub leq (\<lambda>y. f x y)) \<and> (\<forall>y. cont luba orda lub leq (\<lambda>x. f x y))"
by(blast dest: cont_case_prodD1 cont_case_prodD2 intro: cont_case_prodI)

lemma mcont_case_prod_iff [simp]:
  "\<lbrakk> class.preorder orda (mk_less orda); lub_singleton luba;
     class.preorder ordb (mk_less ordb); lub_singleton lubb \<rbrakk>
  \<Longrightarrow> mcont (prod_lub luba lubb) (rel_prod orda ordb) lub leq (case_prod f) \<longleftrightarrow>
   (\<forall>x. mcont lubb ordb lub leq (\<lambda>y. f x y)) \<and> (\<forall>y. mcont luba orda lub leq (\<lambda>x. f x y))"
unfolding mcont_def by(auto simp add: cont_case_prod_iff)

end

lemma mono2mono_case_prod [cont_intro]:
  assumes "\<And>x y. monotone orda ordb (\<lambda>f. pair f x y)"
  shows "monotone orda ordb (\<lambda>f. case_prod (pair f) x)"
by(rule monotoneI)(auto split: prod.split dest: monotoneD[OF assms])

subsection \<open>Complete lattices as ccpo\<close>

context complete_lattice begin

lemma complete_lattice_ccpo: "class.ccpo Sup (\<le>) (<)"
by(unfold_locales)(fast intro: Sup_upper Sup_least)+

lemma complete_lattice_ccpo': "class.ccpo Sup (\<le>) (mk_less (\<le>))"
by(unfold_locales)(auto simp add: mk_less_def intro: Sup_upper Sup_least)

lemma complete_lattice_partial_function_definitions: 
  "partial_function_definitions (\<le>) Sup"
by(unfold_locales)(auto intro: Sup_least Sup_upper)

lemma complete_lattice_partial_function_definitions_dual:
  "partial_function_definitions (\<ge>) Inf"
by(unfold_locales)(auto intro: Inf_lower Inf_greatest)

lemmas [cont_intro, simp] =
  Partial_Function.ccpo[OF complete_lattice_partial_function_definitions]
  Partial_Function.ccpo[OF complete_lattice_partial_function_definitions_dual]

lemma mono2mono_inf:
  assumes f: "monotone ord (\<le>) (\<lambda>x. f x)" 
  and g: "monotone ord (\<le>) (\<lambda>x. g x)"
  shows "monotone ord (\<le>) (\<lambda>x. f x \<sqinter> g x)"
by(auto 4 3 dest: monotoneD[OF f] monotoneD[OF g] intro: le_infI1 le_infI2 intro!: monotoneI)

lemma mcont_const [simp]: "mcont lub ord Sup (\<le>) (\<lambda>_. c)"
by(rule ccpo.mcont_const[OF complete_lattice_ccpo])

lemma mono2mono_sup:
  assumes f: "monotone ord (\<le>) (\<lambda>x. f x)"
  and g: "monotone ord (\<le>) (\<lambda>x. g x)"
  shows "monotone ord (\<le>) (\<lambda>x. f x \<squnion> g x)"
by(auto 4 3 intro!: monotoneI intro: sup.coboundedI1 sup.coboundedI2 dest: monotoneD[OF f] monotoneD[OF g])

lemma Sup_image_sup: 
  assumes "Y \<noteq> {}"
  shows "\<Squnion>((\<squnion>) x ` Y) = x \<squnion> \<Squnion>Y"
proof(rule Sup_eqI)
  fix y
  assume "y \<in> (\<squnion>) x ` Y"
  then obtain z where "y = x \<squnion> z" and "z \<in> Y" by blast
  from \<open>z \<in> Y\<close> have "z \<le> \<Squnion>Y" by(rule Sup_upper)
  with _ show "y \<le> x \<squnion> \<Squnion>Y" unfolding \<open>y = x \<squnion> z\<close> by(rule sup_mono) simp
next
  fix y
  assume upper: "\<And>z. z \<in> (\<squnion>) x ` Y \<Longrightarrow> z \<le> y"
  show "x \<squnion> \<Squnion>Y \<le> y" unfolding Sup_insert[symmetric]
  proof(rule Sup_least)
    fix z
    assume "z \<in> insert x Y"
    from assms obtain z' where "z' \<in> Y" by blast
    let ?z = "if z \<in> Y then x \<squnion> z else x \<squnion> z'"
    have "z \<le> x \<squnion> ?z" using \<open>z' \<in> Y\<close> \<open>z \<in> insert x Y\<close> by auto
    also have "\<dots> \<le> y" by(rule upper)(auto split: if_split_asm intro: \<open>z' \<in> Y\<close>)
    finally show "z \<le> y" .
  qed
qed

lemma mcont_sup1: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. x \<squnion> y)"
by(auto 4 3 simp add: mcont_def sup.coboundedI1 sup.coboundedI2 intro!: monotoneI contI intro: Sup_image_sup[symmetric])

lemma mcont_sup2: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>x. x \<squnion> y)"
by(subst sup_commute)(rule mcont_sup1)

lemma mcont2mcont_sup [cont_intro, simp]:
  "\<lbrakk> mcont lub ord Sup (\<le>) (\<lambda>x. f x);
     mcont lub ord Sup (\<le>) (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. f x \<squnion> g x)"
by(best intro: ccpo.mcont2mcont'[OF complete_lattice_ccpo] mcont_sup1 mcont_sup2 ccpo.mcont_const[OF complete_lattice_ccpo])

end

lemmas [cont_intro] = admissible_leI[OF complete_lattice_ccpo']

context complete_distrib_lattice begin

lemma mcont_inf1: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. x \<sqinter> y)"
by(auto intro: monotoneI contI simp add: le_infI2 inf_Sup mcont_def)

lemma mcont_inf2: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>x. x \<sqinter> y)"
by(auto intro: monotoneI contI simp add: le_infI1 Sup_inf mcont_def)

lemma mcont2mcont_inf [cont_intro, simp]:
  "\<lbrakk> mcont lub ord Sup (\<le>) (\<lambda>x. f x);
    mcont lub ord Sup (\<le>) (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. f x \<sqinter> g x)"
by(best intro: ccpo.mcont2mcont'[OF complete_lattice_ccpo] mcont_inf1 mcont_inf2 ccpo.mcont_const[OF complete_lattice_ccpo])

end

interpretation lfp: partial_function_definitions "(\<le>) :: _ :: complete_lattice \<Rightarrow> _" Sup
by(rule complete_lattice_partial_function_definitions)

declaration \<open>Partial_Function.init "lfp" \<^term>\<open>lfp.fixp_fun\<close> \<^term>\<open>lfp.mono_body\<close>
  @{thm lfp.fixp_rule_uc} @{thm lfp.fixp_induct_uc} NONE\<close>

interpretation gfp: partial_function_definitions "(\<ge>) :: _ :: complete_lattice \<Rightarrow> _" Inf
by(rule complete_lattice_partial_function_definitions_dual)

declaration \<open>Partial_Function.init "gfp" \<^term>\<open>gfp.fixp_fun\<close> \<^term>\<open>gfp.mono_body\<close>
  @{thm gfp.fixp_rule_uc} @{thm gfp.fixp_induct_uc} NONE\<close>

lemma insert_mono [partial_function_mono]:
   "monotone (fun_ord (\<subseteq>)) (\<subseteq>) A \<Longrightarrow> monotone (fun_ord (\<subseteq>)) (\<subseteq>) (\<lambda>y. insert x (A y))"
by(rule monotoneI)(auto simp add: fun_ord_def dest: monotoneD)

lemma mono2mono_insert [THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_insert: "monotone (\<subseteq>) (\<subseteq>) (insert x)"
by(rule monotoneI) blast

lemma mcont2mcont_insert[THEN lfp.mcont2mcont, cont_intro, simp]:
  shows mcont_insert: "mcont Union (\<subseteq>) Union (\<subseteq>) (insert x)"
by(blast intro: mcontI contI monotone_insert)

lemma mono2mono_image [THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_image: "monotone (\<subseteq>) (\<subseteq>) ((`) f)"
by(rule monotoneI) blast

lemma cont_image: "cont Union (\<subseteq>) Union (\<subseteq>) ((`) f)"
by(rule contI)(auto)

lemma mcont2mcont_image [THEN lfp.mcont2mcont, cont_intro, simp]:
  shows mcont_image: "mcont Union (\<subseteq>) Union (\<subseteq>) ((`) f)"
by(blast intro: mcontI monotone_image cont_image)

context complete_lattice begin

lemma monotone_Sup [cont_intro, simp]:
  "monotone ord (\<subseteq>) f \<Longrightarrow> monotone ord (\<le>) (\<lambda>x. \<Squnion>f x)"
by(blast intro: monotoneI Sup_least Sup_upper dest: monotoneD)

lemma cont_Sup:
  assumes "cont lub ord Union (\<subseteq>) f"
  shows "cont lub ord Sup (\<le>) (\<lambda>x. \<Squnion>f x)"
apply(rule contI)
apply(simp add: contD[OF assms])
apply(blast intro: Sup_least Sup_upper order_trans order.antisym)
done

lemma mcont_Sup: "mcont lub ord Union (\<subseteq>) f \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. \<Squnion>f x)"
unfolding mcont_def by(blast intro: monotone_Sup cont_Sup)

lemma monotone_SUP:
  "\<lbrakk> monotone ord (\<subseteq>) f; \<And>y. monotone ord (\<le>) (\<lambda>x. g x y) \<rbrakk> \<Longrightarrow> monotone ord (\<le>) (\<lambda>x. \<Squnion>y\<in>f x. g x y)"
by(rule monotoneI)(blast dest: monotoneD intro: Sup_upper order_trans intro!: Sup_least)

lemma monotone_SUP2:
  "(\<And>y. y \<in> A \<Longrightarrow> monotone ord (\<le>) (\<lambda>x. g x y)) \<Longrightarrow> monotone ord (\<le>) (\<lambda>x. \<Squnion>y\<in>A. g x y)"
by(rule monotoneI)(blast intro: Sup_upper order_trans dest: monotoneD intro!: Sup_least)

lemma cont_SUP:
  assumes f: "mcont lub ord Union (\<subseteq>) f"
  and g: "\<And>y. mcont lub ord Sup (\<le>) (\<lambda>x. g x y)"
  shows "cont lub ord Sup (\<le>) (\<lambda>x. \<Squnion>y\<in>f x. g x y)"
proof(rule contI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ord Y"
    and Y: "Y \<noteq> {}"
  show "\<Squnion>(g (lub Y) ` f (lub Y)) = \<Squnion>((\<lambda>x. \<Squnion>(g x ` f x)) ` Y)" (is "?lhs = ?rhs")
  proof(rule order.antisym)
    show "?lhs \<le> ?rhs"
    proof(rule Sup_least)
      fix x
      assume "x \<in> g (lub Y) ` f (lub Y)"
      with mcont_contD[OF f chain Y] mcont_contD[OF g chain Y]
      obtain y z where "y \<in> Y" "z \<in> f y"
        and x: "x = \<Squnion>((\<lambda>x. g x z) ` Y)" by auto
      show "x \<le> ?rhs" unfolding x
      proof(rule Sup_least)
        fix u
        assume "u \<in> (\<lambda>x. g x z) ` Y"
        then obtain y' where "u = g y' z" "y' \<in> Y" by auto
        from chain \<open>y \<in> Y\<close> \<open>y' \<in> Y\<close> have "ord y y' \<or> ord y' y" by(rule chainD)
        thus "u \<le> ?rhs"
        proof
          note \<open>u = g y' z\<close> also
          assume "ord y y'"
          with f have "f y \<subseteq> f y'" by(rule mcont_monoD)
          with \<open>z \<in> f y\<close>
          have "g y' z \<le> \<Squnion>(g y' ` f y')" by(auto intro: Sup_upper)
          also have "\<dots> \<le> ?rhs" using \<open>y' \<in> Y\<close> by(auto intro: Sup_upper)
          finally show ?thesis .
        next
          note \<open>u = g y' z\<close> also
          assume "ord y' y"
          with g have "g y' z \<le> g y z" by(rule mcont_monoD)
          also have "\<dots> \<le> \<Squnion>(g y ` f y)" using \<open>z \<in> f y\<close>
            by(auto intro: Sup_upper)
          also have "\<dots> \<le> ?rhs" using \<open>y \<in> Y\<close> by(auto intro: Sup_upper)
          finally show ?thesis .
        qed
      qed
    qed
  next
    show "?rhs \<le> ?lhs"
    proof(rule Sup_least)
      fix x
      assume "x \<in> (\<lambda>x. \<Squnion>(g x ` f x)) ` Y"
      then obtain y where x: "x = \<Squnion>(g y ` f y)" and "y \<in> Y" by auto
      show "x \<le> ?lhs" unfolding x
      proof(rule Sup_least)
        fix u
        assume "u \<in> g y ` f y"
        then obtain z where "u = g y z" "z \<in> f y" by auto
        note \<open>u = g y z\<close>
        also have "g y z \<le> \<Squnion>((\<lambda>x. g x z) ` Y)"
          using \<open>y \<in> Y\<close> by(auto intro: Sup_upper)
        also have "\<dots> = g (lub Y) z" by(simp add: mcont_contD[OF g chain Y])
        also have "\<dots> \<le> ?lhs" using \<open>z \<in> f y\<close> \<open>y \<in> Y\<close>
          by(auto intro: Sup_upper simp add: mcont_contD[OF f chain Y])
        finally show "u \<le> ?lhs" .
      qed
    qed
  qed
qed

lemma mcont_SUP [cont_intro, simp]:
  "\<lbrakk> mcont lub ord Union (\<subseteq>) f; \<And>y. mcont lub ord Sup (\<le>) (\<lambda>x. g x y) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. \<Squnion>y\<in>f x. g x y)"
by(blast intro: mcontI cont_SUP monotone_SUP mcont_mono)

end

lemma admissible_Ball [cont_intro, simp]:
  "\<lbrakk> \<And>x. ccpo.admissible lub ord (\<lambda>A. P A x);
     mcont lub ord Union (\<subseteq>) f;
     class.ccpo lub ord (mk_less ord) \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>A. \<forall>x\<in>f A. P A x)"
unfolding Ball_def by simp

lemma admissible_Bex'[THEN admissible_subst, cont_intro, simp]:
  shows admissible_Bex: "ccpo.admissible Union (\<subseteq>) (\<lambda>A. \<exists>x\<in>A. P x)"
by(rule ccpo.admissibleI)(auto)

subsection \<open>Parallel fixpoint induction\<close>

context
  fixes luba :: "'a set \<Rightarrow> 'a"
  and orda :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and lubb :: "'b set \<Rightarrow> 'b"
  and ordb :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes a: "class.ccpo luba orda (mk_less orda)"
  and b: "class.ccpo lubb ordb (mk_less ordb)"
begin

interpretation a: ccpo luba orda "mk_less orda" by(rule a)
interpretation b: ccpo lubb ordb "mk_less ordb" by(rule b)

lemma ccpo_rel_prodI:
  "class.ccpo (prod_lub luba lubb) (rel_prod orda ordb) (mk_less (rel_prod orda ordb))"
  (is "class.ccpo ?lub ?ord ?ord'")
proof(intro class.ccpo.intro class.ccpo_axioms.intro)
  show "class.order ?ord ?ord'" by(rule order_rel_prodI) intro_locales
qed(auto 4 4 simp add: prod_lub_def intro: a.ccpo_Sup_upper b.ccpo_Sup_upper a.ccpo_Sup_least b.ccpo_Sup_least rev_image_eqI dest: chain_rel_prodD1 chain_rel_prodD2)

interpretation ab: ccpo "prod_lub luba lubb" "rel_prod orda ordb" "mk_less (rel_prod orda ordb)"
by(rule ccpo_rel_prodI)

lemma monotone_map_prod [simp]:
  "monotone (rel_prod orda ordb) (rel_prod ordc ordd) (map_prod f g) \<longleftrightarrow>
   monotone orda ordc f \<and> monotone ordb ordd g"
by(auto simp add: monotone_def)

lemma parallel_fixp_induct:
  assumes adm: "ccpo.admissible (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>x. P (fst x) (snd x))"
  and f: "monotone orda orda f"
  and g: "monotone ordb ordb g"
  and bot: "P (luba {}) (lubb {})"
  and step: "\<And>x y. P x y \<Longrightarrow> P (f x) (g y)"
  shows "P (ccpo.fixp luba orda f) (ccpo.fixp lubb ordb g)"
proof -
  let ?lub = "prod_lub luba lubb"
    and ?ord = "rel_prod orda ordb"
    and ?P = "\<lambda>(x, y). P x y"
  from adm have adm': "ccpo.admissible ?lub ?ord ?P" by(simp add: split_def)
  hence "?P (ccpo.fixp (prod_lub luba lubb) (rel_prod orda ordb) (map_prod f g))"
    by(rule ab.fixp_induct)(auto simp add: f g step bot)
  also have "ccpo.fixp (prod_lub luba lubb) (rel_prod orda ordb) (map_prod f g) = 
            (ccpo.fixp luba orda f, ccpo.fixp lubb ordb g)" (is "?lhs = (?rhs1, ?rhs2)")
  proof(rule ab.order.antisym)
    have "ccpo.admissible ?lub ?ord (\<lambda>xy. ?ord xy (?rhs1, ?rhs2))"
      by(rule admissible_leI[OF ccpo_rel_prodI])(auto simp add: prod_lub_def chain_empty intro: a.ccpo_Sup_least b.ccpo_Sup_least)
    thus "?ord ?lhs (?rhs1, ?rhs2)"
      by(rule ab.fixp_induct)(auto 4 3 dest: monotoneD[OF f] monotoneD[OF g] simp add: b.fixp_unfold[OF g, symmetric] a.fixp_unfold[OF f, symmetric] f g intro: a.ccpo_Sup_least b.ccpo_Sup_least chain_empty)
  next
    have "ccpo.admissible luba orda (\<lambda>x. orda x (fst ?lhs))"
      by(rule admissible_leI[OF a])(auto intro: a.ccpo_Sup_least simp add: chain_empty)
    hence "orda ?rhs1 (fst ?lhs)" using f
    proof(rule a.fixp_induct)
      fix x
      assume "orda x (fst ?lhs)"
      thus "orda (f x) (fst ?lhs)"
        by(subst ab.fixp_unfold)(auto simp add: f g dest: monotoneD[OF f])
    qed(auto intro: a.ccpo_Sup_least chain_empty)
    moreover
    have "ccpo.admissible lubb ordb (\<lambda>y. ordb y (snd ?lhs))"
      by(rule admissible_leI[OF b])(auto intro: b.ccpo_Sup_least simp add: chain_empty)
    hence "ordb ?rhs2 (snd ?lhs)" using g
    proof(rule b.fixp_induct)
      fix y
      assume "ordb y (snd ?lhs)"
      thus "ordb (g y) (snd ?lhs)"
        by(subst ab.fixp_unfold)(auto simp add: f g dest: monotoneD[OF g])
    qed(auto intro: b.ccpo_Sup_least chain_empty)
    ultimately show "?ord (?rhs1, ?rhs2) ?lhs"
      by(simp add: rel_prod_conv split_beta)
  qed
  finally show ?thesis by simp
qed

end

lemma parallel_fixp_induct_uc:
  assumes a: "partial_function_definitions orda luba"
  and b: "partial_function_definitions ordb lubb"
  and F: "\<And>x. monotone (fun_ord orda) orda (\<lambda>f. U1 (F (C1 f)) x)"
  and G: "\<And>y. monotone (fun_ord ordb) ordb (\<lambda>g. U2 (G (C2 g)) y)"
  and eq1: "f \<equiv> C1 (ccpo.fixp (fun_lub luba) (fun_ord orda) (\<lambda>f. U1 (F (C1 f))))"
  and eq2: "g \<equiv> C2 (ccpo.fixp (fun_lub lubb) (fun_ord ordb) (\<lambda>g. U2 (G (C2 g))))"
  and inverse: "\<And>f. U1 (C1 f) = f"
  and inverse2: "\<And>g. U2 (C2 g) = g"
  and adm: "ccpo.admissible (prod_lub (fun_lub luba) (fun_lub lubb)) (rel_prod (fun_ord orda) (fun_ord ordb)) (\<lambda>x. P (fst x) (snd x))"
  and bot: "P (\<lambda>_. luba {}) (\<lambda>_. lubb {})"
  and step: "\<And>f g. P (U1 f) (U2 g) \<Longrightarrow> P (U1 (F f)) (U2 (G g))"
  shows "P (U1 f) (U2 g)"
apply(unfold eq1 eq2 inverse inverse2)
apply(rule parallel_fixp_induct[OF partial_function_definitions.ccpo[OF a] partial_function_definitions.ccpo[OF b] adm])
using F apply(simp add: monotone_def fun_ord_def)
using G apply(simp add: monotone_def fun_ord_def)
apply(simp add: fun_lub_def bot)
apply(rule step, simp add: inverse inverse2)
done

lemmas parallel_fixp_induct_1_1 = parallel_fixp_induct_uc[
  of _ _ _ _ "\<lambda>x. x" _ "\<lambda>x. x" "\<lambda>x. x" _ "\<lambda>x. x",
  OF _ _ _ _ _ _ refl refl]

lemmas parallel_fixp_induct_2_2 = parallel_fixp_induct_uc[
  of _ _ _ _ "case_prod" _ "curry" "case_prod" _ "curry",
  where P="\<lambda>f g. P (curry f) (curry g)",
  unfolded case_prod_curry curry_case_prod curry_K,
  OF _ _ _ _ _ _ refl refl]
  for P

lemma monotone_fst: "monotone (rel_prod orda ordb) orda fst"
by(auto intro: monotoneI)

lemma mcont_fst: "mcont (prod_lub luba lubb) (rel_prod orda ordb) luba orda fst"
by(auto intro!: mcontI monotoneI contI simp add: prod_lub_def)

lemma mcont2mcont_fst [cont_intro, simp]:
  "mcont lub ord (prod_lub luba lubb) (rel_prod orda ordb) t
  \<Longrightarrow> mcont lub ord luba orda (\<lambda>x. fst (t x))"
by(auto intro!: mcontI monotoneI contI dest: mcont_monoD mcont_contD simp add: rel_prod_sel split_beta prod_lub_def image_image)

lemma monotone_snd: "monotone (rel_prod orda ordb) ordb snd"
by(auto intro: monotoneI)

lemma mcont_snd: "mcont (prod_lub luba lubb) (rel_prod orda ordb) lubb ordb snd"
by(auto intro!: mcontI monotoneI contI simp add: prod_lub_def)

lemma mcont2mcont_snd [cont_intro, simp]:
  "mcont lub ord (prod_lub luba lubb) (rel_prod orda ordb) t
  \<Longrightarrow> mcont lub ord lubb ordb (\<lambda>x. snd (t x))"
by(auto intro!: mcontI monotoneI contI dest: mcont_monoD mcont_contD simp add: rel_prod_sel split_beta prod_lub_def image_image)

lemma monotone_Pair:
  "\<lbrakk> monotone ord orda f; monotone ord ordb g \<rbrakk>
  \<Longrightarrow> monotone ord (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
by(simp add: monotone_def)

lemma cont_Pair:
  "\<lbrakk> cont lub ord luba orda f; cont lub ord lubb ordb g \<rbrakk>
  \<Longrightarrow> cont lub ord (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
by(rule contI)(auto simp add: prod_lub_def image_image dest!: contD)

lemma mcont_Pair:
  "\<lbrakk> mcont lub ord luba orda f; mcont lub ord lubb ordb g \<rbrakk>
  \<Longrightarrow> mcont lub ord (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
by(rule mcontI)(simp_all add: monotone_Pair mcont_mono cont_Pair)

context partial_function_definitions begin
text \<open>Specialised versions of @{thm [source] mcont_call} for admissibility proofs for parallel fixpoint inductions\<close>
lemmas mcont_call_fst [cont_intro] = mcont_call[THEN mcont2mcont, OF mcont_fst]
lemmas mcont_call_snd [cont_intro] = mcont_call[THEN mcont2mcont, OF mcont_snd]
end

lemma map_option_mono [partial_function_mono]:
  "mono_option B \<Longrightarrow> mono_option (\<lambda>f. map_option g (B f))"
unfolding map_conv_bind_option by(rule bind_mono) simp_all

lemma compact_flat_lub [cont_intro]: "ccpo.compact (flat_lub x) (flat_ord x) y"
using flat_interpretation[THEN ccpo]
proof(rule ccpo.compactI[OF _ ccpo.admissibleI])
  fix A
  assume chain: "Complete_Partial_Order.chain (flat_ord x) A"
    and A: "A \<noteq> {}"
    and *: "\<forall>z\<in>A. \<not> flat_ord x y z"
  from A obtain z where "z \<in> A" by blast
  with * have z: "\<not> flat_ord x y z" ..
  hence y: "x \<noteq> y" "y \<noteq> z" by(auto simp add: flat_ord_def)
  { assume "\<not> A \<subseteq> {x}"
    then obtain z' where "z' \<in> A" "z' \<noteq> x" by auto
    then have "(THE z. z \<in> A - {x}) = z'"
      by(intro the_equality)(auto dest: chainD[OF chain] simp add: flat_ord_def)
    moreover have "z' \<noteq> y" using \<open>z' \<in> A\<close> * by(auto simp add: flat_ord_def)
    ultimately have "y \<noteq> (THE z. z \<in> A - {x})" by simp }
  with z show "\<not> flat_ord x y (flat_lub x A)" by(simp add: flat_ord_def flat_lub_def)
qed

end
