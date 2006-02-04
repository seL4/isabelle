(*  Title:      HOLCF/Pcpo.thy
    ID:         $Id$
    Author:     Franz Regensburger
*)

header {* Classes cpo and pcpo *}

theory Pcpo
imports Porder
begin

subsection {* Complete partial orders *}

text {* The class cpo of chain complete partial orders *}

axclass cpo < po
        -- {* class axiom: *}
  cpo:   "chain S \<Longrightarrow> \<exists>x. range S <<| x" 

text {* in cpo's everthing equal to THE lub has lub properties for every chain *}

lemma thelubE: "\<lbrakk>chain S; (\<Squnion>i. S i) = (l::'a::cpo)\<rbrakk> \<Longrightarrow> range S <<| l"
by (blast dest: cpo intro: lubI)

text {* Properties of the lub *}

lemma is_ub_thelub: "chain (S::nat \<Rightarrow> 'a::cpo) \<Longrightarrow> S x \<sqsubseteq> (\<Squnion>i. S i)"
by (blast dest: cpo intro: lubI [THEN is_ub_lub])

lemma is_lub_thelub:
  "\<lbrakk>chain (S::nat \<Rightarrow> 'a::cpo); range S <| x\<rbrakk> \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x"
by (blast dest: cpo intro: lubI [THEN is_lub_lub])

lemma lub_range_mono:
  "\<lbrakk>range X \<subseteq> range Y; chain Y; chain (X::nat \<Rightarrow> 'a::cpo)\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (subgoal_tac "\<exists>j. X i = Y j")
apply  clarsimp
apply  (erule is_ub_thelub)
apply auto
done

lemma lub_range_shift:
  "chain (Y::nat \<Rightarrow> 'a::cpo) \<Longrightarrow> (\<Squnion>i. Y (i + j)) = (\<Squnion>i. Y i)"
apply (rule antisym_less)
apply (rule lub_range_mono)
apply    fast
apply   assumption
apply (erule chain_shift)
apply (rule is_lub_thelub)
apply assumption
apply (rule ub_rangeI)
apply (rule_tac y="Y (i + j)" in trans_less)
apply (erule chain_mono3)
apply (rule le_add1)
apply (rule is_ub_thelub)
apply (erule chain_shift)
done

lemma maxinch_is_thelub:
  "chain Y \<Longrightarrow> max_in_chain i Y = ((\<Squnion>i. Y i) = ((Y i)::'a::cpo))"
apply (rule iffI)
apply (fast intro!: thelubI lub_finch1)
apply (unfold max_in_chain_def)
apply (safe intro!: antisym_less)
apply (fast elim!: chain_mono3)
apply (drule sym)
apply (force elim!: is_ub_thelub)
done

text {* the @{text "\<sqsubseteq>"} relation between two chains is preserved by their lubs *}

lemma lub_mono:
  "\<lbrakk>chain (X::nat \<Rightarrow> 'a::cpo); chain Y; \<forall>k. X k \<sqsubseteq> Y k\<rbrakk> 
    \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (rule trans_less)
apply (erule spec)
apply (erule is_ub_thelub)
done

text {* the = relation between two chains is preserved by their lubs *}

lemma lub_equal:
  "\<lbrakk>chain (X::nat \<Rightarrow> 'a::cpo); chain Y; \<forall>k. X k = Y k\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
by (simp only: expand_fun_eq [symmetric])

text {* more results about mono and = of lubs of chains *}

lemma lub_mono2:
  "\<lbrakk>\<exists>j. \<forall>i>j. X i = Y i; chain (X::nat \<Rightarrow> 'a::cpo); chain Y\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
apply (erule exE)
apply (subgoal_tac "(\<Squnion>i. X (i + Suc j)) \<sqsubseteq> (\<Squnion>i. Y (i + Suc j))")
apply (thin_tac "\<forall>i>j. X i = Y i")
apply (simp only: lub_range_shift)
apply simp
done

lemma lub_equal2:
  "\<lbrakk>\<exists>j. \<forall>i>j. X i = Y i; chain (X::nat \<Rightarrow> 'a::cpo); chain Y\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
by (blast intro: antisym_less lub_mono2 sym)

lemma lub_mono3:
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); chain X; \<forall>i. \<exists>j. Y i \<sqsubseteq> X j\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. X i)"
apply (erule is_lub_thelub)
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (erule trans_less)
apply (erule is_ub_thelub)
done

lemma ch2ch_lub:
  fixes Y :: "nat \<Rightarrow> nat \<Rightarrow> 'a::cpo"
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "chain (\<lambda>i. \<Squnion>j. Y i j)"
apply (rule chainI)
apply (rule lub_mono [rule_format, OF 2 2])
apply (rule chainE [OF 1])
done

lemma diag_lub:
  fixes Y :: "nat \<Rightarrow> nat \<Rightarrow> 'a::cpo"
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>i. Y i i)"
proof (rule antisym_less)
  have 3: "chain (\<lambda>i. Y i i)"
    apply (rule chainI)
    apply (rule trans_less)
    apply (rule chainE [OF 1])
    apply (rule chainE [OF 2])
    done
  have 4: "chain (\<lambda>i. \<Squnion>j. Y i j)"
    by (rule ch2ch_lub [OF 1 2])
  show "(\<Squnion>i. \<Squnion>j. Y i j) \<sqsubseteq> (\<Squnion>i. Y i i)"
    apply (rule is_lub_thelub [OF 4])
    apply (rule ub_rangeI)
    apply (rule lub_mono3 [rule_format, OF 2 3])
    apply (rule exI)
    apply (rule trans_less)
    apply (rule chain_mono3 [OF 1 le_maxI1])
    apply (rule chain_mono3 [OF 2 le_maxI2])
    done
  show "(\<Squnion>i. Y i i) \<sqsubseteq> (\<Squnion>i. \<Squnion>j. Y i j)"
    apply (rule lub_mono [rule_format, OF 3 4])
    apply (rule is_ub_thelub [OF 2])
    done
qed

lemma ex_lub:
  fixes Y :: "nat \<Rightarrow> nat \<Rightarrow> 'a::cpo"
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>j. \<Squnion>i. Y i j)"
by (simp add: diag_lub 1 2)


subsection {* Pointed cpos *}

text {* The class pcpo of pointed cpos *}

axclass pcpo < cpo
  least: "\<exists>x. \<forall>y. x \<sqsubseteq> y"

constdefs
  UU :: "'a::pcpo"
  "UU \<equiv> THE x. \<forall>y. x \<sqsubseteq> y"

syntax (xsymbols)
  UU :: "'a::pcpo" ("\<bottom>")

text {* derive the old rule minimal *}
 
lemma UU_least: "\<forall>z. \<bottom> \<sqsubseteq> z"
apply (unfold UU_def)
apply (rule theI')
apply (rule ex_ex1I)
apply (rule least)
apply (blast intro: antisym_less)
done

lemma minimal [iff]: "\<bottom> \<sqsubseteq> x"
by (rule UU_least [THEN spec])

lemma UU_reorient: "(\<bottom> = x) = (x = \<bottom>)"
by auto

ML_setup {*
local
  val meta_UU_reorient = thm "UU_reorient" RS eq_reflection;
  fun reorient_proc sg _ (_ $ t $ u) =
    case u of
        Const("Pcpo.UU",_) => NONE
      | Const("0", _) => NONE
      | Const("1", _) => NONE
      | Const("Numeral.number_of", _) $ _ => NONE
      | _ => SOME meta_UU_reorient;
in
  val UU_reorient_simproc = 
    Simplifier.simproc (the_context ())
      "UU_reorient_simproc" ["UU=x"] reorient_proc
end;

Addsimprocs [UU_reorient_simproc];
*}

text {* useful lemmas about @{term \<bottom>} *}

lemma eq_UU_iff: "(x = \<bottom>) = (x \<sqsubseteq> \<bottom>)"
by (simp add: po_eq_conv)

lemma UU_I: "x \<sqsubseteq> \<bottom> \<Longrightarrow> x = \<bottom>"
by (subst eq_UU_iff)

lemma not_less2not_eq: "\<not> (x::'a::po) \<sqsubseteq> y \<Longrightarrow> x \<noteq> y"
by auto

lemma chain_UU_I: "\<lbrakk>chain Y; (\<Squnion>i. Y i) = \<bottom>\<rbrakk> \<Longrightarrow> \<forall>i. Y i = \<bottom>"
apply (rule allI)
apply (rule UU_I)
apply (erule subst)
apply (erule is_ub_thelub)
done

lemma chain_UU_I_inverse: "\<forall>i::nat. Y i = \<bottom> \<Longrightarrow> (\<Squnion>i. Y i) = \<bottom>"
apply (rule lub_chain_maxelem)
apply (erule spec)
apply simp
done

lemma chain_UU_I_inverse2: "(\<Squnion>i. Y i) \<noteq> \<bottom> \<Longrightarrow> \<exists>i::nat. Y i \<noteq> \<bottom>"
by (blast intro: chain_UU_I_inverse)

lemma notUU_I: "\<lbrakk>x \<sqsubseteq> y; x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> y \<noteq> \<bottom>"
by (blast intro: UU_I)

lemma chain_mono2: "\<lbrakk>\<exists>j. Y j \<noteq> \<bottom>; chain Y\<rbrakk> \<Longrightarrow> \<exists>j. \<forall>i>j. Y i \<noteq> \<bottom>"
by (blast dest: notUU_I chain_mono)

subsection {* Chain-finite and flat cpos *}

text {* further useful classes for HOLCF domains *}

axclass chfin < po
  chfin: "\<forall>Y. chain Y \<longrightarrow> (\<exists>n. max_in_chain n Y)"

axclass flat < pcpo
  ax_flat: "\<forall>x y. x \<sqsubseteq> y \<longrightarrow> (x = \<bottom>) \<or> (x = y)"

text {* some properties for chfin and flat *}

text {* chfin types are cpo *}

lemma chfin_imp_cpo:
  "chain (S::nat \<Rightarrow> 'a::chfin) \<Longrightarrow> \<exists>x. range S <<| x"
apply (frule chfin [rule_format])
apply (blast intro: lub_finch1)
done

instance chfin < cpo
by intro_classes (rule chfin_imp_cpo)

text {* flat types are chfin *}

lemma flat_imp_chfin: 
     "\<forall>Y::nat \<Rightarrow> 'a::flat. chain Y \<longrightarrow> (\<exists>n. max_in_chain n Y)"
apply (unfold max_in_chain_def)
apply clarify
apply (case_tac "\<forall>i. Y i = \<bottom>")
apply simp
apply simp
apply (erule exE)
apply (rule_tac x="i" in exI)
apply clarify
apply (blast dest: chain_mono3 ax_flat [rule_format])
done

instance flat < chfin
by intro_classes (rule flat_imp_chfin)

text {* flat subclass of chfin; @{text adm_flat} not needed *}

lemma flat_eq: "(a::'a::flat) \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b = (a = b)"
by (safe dest!: ax_flat [rule_format])

lemma chfin2finch: "chain (Y::nat \<Rightarrow> 'a::chfin) \<Longrightarrow> finite_chain Y"
by (simp add: chfin finite_chain_def)

text {* lemmata for improved admissibility introdution rule *}

lemma infinite_chain_adm_lemma:
  "\<lbrakk>chain Y; \<forall>i. P (Y i);  
    \<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i); \<not> finite_chain Y\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)\<rbrakk>
      \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (case_tac "finite_chain Y")
prefer 2 apply fast
apply (unfold finite_chain_def)
apply safe
apply (erule lub_finch1 [THEN thelubI, THEN ssubst])
apply assumption
apply (erule spec)
done

lemma increasing_chain_adm_lemma:
  "\<lbrakk>chain Y;  \<forall>i. P (Y i); \<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i);
    \<forall>i. \<exists>j>i. Y i \<noteq> Y j \<and> Y i \<sqsubseteq> Y j\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)\<rbrakk>
      \<Longrightarrow> P (\<Squnion>i. Y i)"
apply (erule infinite_chain_adm_lemma)
apply assumption
apply (erule thin_rl)
apply (unfold finite_chain_def)
apply (unfold max_in_chain_def)
apply (fast dest: le_imp_less_or_eq elim: chain_mono)
done

end
