(*  Title:      HOL/HOLCF/Pcpo.thy
    Author:     Franz Regensburger
*)

section \<open>Classes cpo and pcpo\<close>

theory Pcpo
  imports Porder
begin

subsection \<open>Complete partial orders\<close>

text \<open>The class cpo of chain complete partial orders\<close>

class cpo = po +
  assumes cpo: "chain S \<Longrightarrow> \<exists>x. range S <<| x"
begin

text \<open>in cpo's everthing equal to THE lub has lub properties for every chain\<close>

lemma cpo_lubI: "chain S \<Longrightarrow> range S <<| (\<Squnion>i. S i)"
  by (fast dest: cpo elim: is_lub_lub)

lemma thelubE: "\<lbrakk>chain S; (\<Squnion>i. S i) = l\<rbrakk> \<Longrightarrow> range S <<| l"
  by (blast dest: cpo intro: is_lub_lub)

text \<open>Properties of the lub\<close>

lemma is_ub_thelub: "chain S \<Longrightarrow> S x \<sqsubseteq> (\<Squnion>i. S i)"
  by (blast dest: cpo intro: is_lub_lub [THEN is_lub_rangeD1])

lemma is_lub_thelub: "\<lbrakk>chain S; range S <| x\<rbrakk> \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x"
  by (blast dest: cpo intro: is_lub_lub [THEN is_lubD2])

lemma lub_below_iff: "chain S \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x \<longleftrightarrow> (\<forall>i. S i \<sqsubseteq> x)"
  by (simp add: is_lub_below_iff [OF cpo_lubI] is_ub_def)

lemma lub_below: "\<lbrakk>chain S; \<And>i. S i \<sqsubseteq> x\<rbrakk> \<Longrightarrow> (\<Squnion>i. S i) \<sqsubseteq> x"
  by (simp add: lub_below_iff)

lemma below_lub: "\<lbrakk>chain S; x \<sqsubseteq> S i\<rbrakk> \<Longrightarrow> x \<sqsubseteq> (\<Squnion>i. S i)"
  by (erule below_trans, erule is_ub_thelub)

lemma lub_range_mono: "\<lbrakk>range X \<subseteq> range Y; chain Y; chain X\<rbrakk> \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
  apply (erule lub_below)
  apply (subgoal_tac "\<exists>j. X i = Y j")
   apply clarsimp
   apply (erule is_ub_thelub)
  apply auto
  done

lemma lub_range_shift: "chain Y \<Longrightarrow> (\<Squnion>i. Y (i + j)) = (\<Squnion>i. Y i)"
  apply (rule below_antisym)
   apply (rule lub_range_mono)
     apply fast
    apply assumption
   apply (erule chain_shift)
  apply (rule lub_below)
   apply assumption
  apply (rule_tac i="i" in below_lub)
   apply (erule chain_shift)
  apply (erule chain_mono)
  apply (rule le_add1)
  done

lemma maxinch_is_thelub: "chain Y \<Longrightarrow> max_in_chain i Y = ((\<Squnion>i. Y i) = Y i)"
  apply (rule iffI)
   apply (fast intro!: lub_eqI lub_finch1)
  apply (unfold max_in_chain_def)
  apply (safe intro!: below_antisym)
   apply (fast elim!: chain_mono)
  apply (drule sym)
  apply (force elim!: is_ub_thelub)
  done

text \<open>the \<open>\<sqsubseteq>\<close> relation between two chains is preserved by their lubs\<close>

lemma lub_mono: "\<lbrakk>chain X; chain Y; \<And>i. X i \<sqsubseteq> Y i\<rbrakk> \<Longrightarrow> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Y i)"
  by (fast elim: lub_below below_lub)

text \<open>the = relation between two chains is preserved by their lubs\<close>

lemma lub_eq: "(\<And>i. X i = Y i) \<Longrightarrow> (\<Squnion>i. X i) = (\<Squnion>i. Y i)"
  by simp

lemma ch2ch_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "chain (\<lambda>i. \<Squnion>j. Y i j)"
  apply (rule chainI)
  apply (rule lub_mono [OF 2 2])
  apply (rule chainE [OF 1])
  done

lemma diag_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>i. Y i i)"
proof (rule below_antisym)
  have 3: "chain (\<lambda>i. Y i i)"
    apply (rule chainI)
    apply (rule below_trans)
     apply (rule chainE [OF 1])
    apply (rule chainE [OF 2])
    done
  have 4: "chain (\<lambda>i. \<Squnion>j. Y i j)"
    by (rule ch2ch_lub [OF 1 2])
  show "(\<Squnion>i. \<Squnion>j. Y i j) \<sqsubseteq> (\<Squnion>i. Y i i)"
    apply (rule lub_below [OF 4])
    apply (rule lub_below [OF 2])
    apply (rule below_lub [OF 3])
    apply (rule below_trans)
     apply (rule chain_mono [OF 1 max.cobounded1])
    apply (rule chain_mono [OF 2 max.cobounded2])
    done
  show "(\<Squnion>i. Y i i) \<sqsubseteq> (\<Squnion>i. \<Squnion>j. Y i j)"
    apply (rule lub_mono [OF 3 4])
    apply (rule is_ub_thelub [OF 2])
    done
qed

lemma ex_lub:
  assumes 1: "\<And>j. chain (\<lambda>i. Y i j)"
  assumes 2: "\<And>i. chain (\<lambda>j. Y i j)"
  shows "(\<Squnion>i. \<Squnion>j. Y i j) = (\<Squnion>j. \<Squnion>i. Y i j)"
  by (simp add: diag_lub 1 2)

end


subsection \<open>Pointed cpos\<close>

text \<open>The class pcpo of pointed cpos\<close>

class pcpo = cpo +
  assumes least: "\<exists>x. \<forall>y. x \<sqsubseteq> y"
begin

definition bottom :: "'a"  ("\<bottom>")
  where "bottom = (THE x. \<forall>y. x \<sqsubseteq> y)"

lemma minimal [iff]: "\<bottom> \<sqsubseteq> x"
  unfolding bottom_def
  apply (rule the1I2)
   apply (rule ex_ex1I)
    apply (rule least)
   apply (blast intro: below_antisym)
  apply simp
  done

end

text \<open>Old "UU" syntax:\<close>

syntax UU :: logic
translations "UU" \<rightharpoonup> "CONST bottom"

text \<open>Simproc to rewrite \<^term>\<open>\<bottom> = x\<close> to \<^term>\<open>x = \<bottom>\<close>.\<close>
setup \<open>Reorient_Proc.add (fn \<^Const_>\<open>bottom _\<close> => true | _ => false)\<close>
simproc_setup reorient_bottom ("\<bottom> = x") = Reorient_Proc.proc

text \<open>useful lemmas about \<^term>\<open>\<bottom>\<close>\<close>

lemma below_bottom_iff [simp]: "x \<sqsubseteq> \<bottom> \<longleftrightarrow> x = \<bottom>"
  by (simp add: po_eq_conv)

lemma eq_bottom_iff: "x = \<bottom> \<longleftrightarrow> x \<sqsubseteq> \<bottom>"
  by simp

lemma bottomI: "x \<sqsubseteq> \<bottom> \<Longrightarrow> x = \<bottom>"
  by (subst eq_bottom_iff)

lemma lub_eq_bottom_iff: "chain Y \<Longrightarrow> (\<Squnion>i. Y i) = \<bottom> \<longleftrightarrow> (\<forall>i. Y i = \<bottom>)"
  by (simp only: eq_bottom_iff lub_below_iff)


subsection \<open>Chain-finite and flat cpos\<close>

text \<open>further useful classes for HOLCF domains\<close>

class chfin = po +
  assumes chfin: "chain Y \<Longrightarrow> \<exists>n. max_in_chain n Y"
begin

subclass cpo
  apply standard
  apply (frule chfin)
  apply (blast intro: lub_finch1)
  done

lemma chfin2finch: "chain Y \<Longrightarrow> finite_chain Y"
  by (simp add: chfin finite_chain_def)

end

class flat = pcpo +
  assumes ax_flat: "x \<sqsubseteq> y \<Longrightarrow> x = \<bottom> \<or> x = y"
begin

subclass chfin
proof
  fix Y
  assume *: "chain Y"
  show "\<exists>n. max_in_chain n Y"
    apply (unfold max_in_chain_def)
    apply (cases "\<forall>i. Y i = \<bottom>")
     apply simp
    apply simp
    apply (erule exE)
    apply (rule_tac x="i" in exI)
    apply clarify
    using * apply (blast dest: chain_mono ax_flat)
    done
qed

lemma flat_below_iff: "x \<sqsubseteq> y \<longleftrightarrow> x = \<bottom> \<or> x = y"
  by (safe dest!: ax_flat)

lemma flat_eq: "a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b = (a = b)"
  by (safe dest!: ax_flat)

end

subsection \<open>Discrete cpos\<close>

class discrete_cpo = below +
  assumes discrete_cpo [simp]: "x \<sqsubseteq> y \<longleftrightarrow> x = y"
begin

subclass po
  by standard simp_all

text \<open>In a discrete cpo, every chain is constant\<close>

lemma discrete_chain_const:
  assumes S: "chain S"
  shows "\<exists>x. S = (\<lambda>i. x)"
proof (intro exI ext)
  fix i :: nat
  from S le0 have "S 0 \<sqsubseteq> S i" by (rule chain_mono)
  then have "S 0 = S i" by simp
  then show "S i = S 0" by (rule sym)
qed

subclass chfin
proof
  fix S :: "nat \<Rightarrow> 'a"
  assume S: "chain S"
  then have "\<exists>x. S = (\<lambda>i. x)"
    by (rule discrete_chain_const)
  then have "max_in_chain 0 S"
    by (auto simp: max_in_chain_def)
  then show "\<exists>i. max_in_chain i S" ..
qed

end

end
