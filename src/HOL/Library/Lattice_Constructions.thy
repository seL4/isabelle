(*  Title:      HOL/Library/Lattice_Constructions.thy
    Author:     Lukas Bulwahn
    Copyright   2010 TU Muenchen
*)

section \<open>Values extended by a bottom element\<close>

theory Lattice_Constructions
imports Main
begin

datatype 'a bot = Value 'a | Bot

instantiation bot :: (preorder) preorder
begin

definition less_eq_bot where
  "x \<le> y \<longleftrightarrow> (case x of Bot \<Rightarrow> True | Value x \<Rightarrow> (case y of Bot \<Rightarrow> False | Value y \<Rightarrow> x \<le> y))"

definition less_bot where
  "x < y \<longleftrightarrow> (case y of Bot \<Rightarrow> False | Value y \<Rightarrow> (case x of Bot \<Rightarrow> True | Value x \<Rightarrow> x < y))"

lemma less_eq_bot_Bot [simp]: "Bot \<le> x"
  by (simp add: less_eq_bot_def)

lemma less_eq_bot_Bot_code [code]: "Bot \<le> x \<longleftrightarrow> True"
  by simp

lemma less_eq_bot_Bot_is_Bot: "x \<le> Bot \<Longrightarrow> x = Bot"
  by (cases x) (simp_all add: less_eq_bot_def)

lemma less_eq_bot_Value_Bot [simp, code]: "Value x \<le> Bot \<longleftrightarrow> False"
  by (simp add: less_eq_bot_def)

lemma less_eq_bot_Value [simp, code]: "Value x \<le> Value y \<longleftrightarrow> x \<le> y"
  by (simp add: less_eq_bot_def)

lemma less_bot_Bot [simp, code]: "x < Bot \<longleftrightarrow> False"
  by (simp add: less_bot_def)

lemma less_bot_Bot_is_Value: "Bot < x \<Longrightarrow> \<exists>z. x = Value z"
  by (cases x) (simp_all add: less_bot_def)

lemma less_bot_Bot_Value [simp]: "Bot < Value x"
  by (simp add: less_bot_def)

lemma less_bot_Bot_Value_code [code]: "Bot < Value x \<longleftrightarrow> True"
  by simp

lemma less_bot_Value [simp, code]: "Value x < Value y \<longleftrightarrow> x < y"
  by (simp add: less_bot_def)

instance
  by standard
    (auto simp add: less_eq_bot_def less_bot_def less_le_not_le elim: order_trans split: bot.splits)

end

instance bot :: (order) order
  by standard (auto simp add: less_eq_bot_def less_bot_def split: bot.splits)

instance bot :: (linorder) linorder
  by standard (auto simp add: less_eq_bot_def less_bot_def split: bot.splits)

instantiation bot :: (order) bot
begin
  definition "bot = Bot"
  instance ..
end

instantiation bot :: (top) top
begin
  definition "top = Value top"
  instance ..
end

instantiation bot :: (semilattice_inf) semilattice_inf
begin

definition inf_bot
where
  "inf x y =
    (case x of
      Bot \<Rightarrow> Bot
    | Value v \<Rightarrow>
        (case y of
          Bot \<Rightarrow> Bot
        | Value v' \<Rightarrow> Value (inf v v')))"

instance
  by standard (auto simp add: inf_bot_def less_eq_bot_def split: bot.splits)

end

instantiation bot :: (semilattice_sup) semilattice_sup
begin

definition sup_bot
where
  "sup x y =
    (case x of
      Bot \<Rightarrow> y
    | Value v \<Rightarrow>
        (case y of
          Bot \<Rightarrow> x
        | Value v' \<Rightarrow> Value (sup v v')))"

instance
  by standard (auto simp add: sup_bot_def less_eq_bot_def split: bot.splits)

end

instance bot :: (lattice) bounded_lattice_bot
  by intro_classes (simp add: bot_bot_def)


subsection \<open>Values extended by a top element\<close>

datatype 'a top = Value 'a | Top

instantiation top :: (preorder) preorder
begin

definition less_eq_top where
  "x \<le> y \<longleftrightarrow> (case y of Top \<Rightarrow> True | Value y \<Rightarrow> (case x of Top \<Rightarrow> False | Value x \<Rightarrow> x \<le> y))"

definition less_top where
  "x < y \<longleftrightarrow> (case x of Top \<Rightarrow> False | Value x \<Rightarrow> (case y of Top \<Rightarrow> True | Value y \<Rightarrow> x < y))"

lemma less_eq_top_Top [simp]: "x \<le> Top"
  by (simp add: less_eq_top_def)

lemma less_eq_top_Top_code [code]: "x \<le> Top \<longleftrightarrow> True"
  by simp

lemma less_eq_top_is_Top: "Top \<le> x \<Longrightarrow> x = Top"
  by (cases x) (simp_all add: less_eq_top_def)

lemma less_eq_top_Top_Value [simp, code]: "Top \<le> Value x \<longleftrightarrow> False"
  by (simp add: less_eq_top_def)

lemma less_eq_top_Value_Value [simp, code]: "Value x \<le> Value y \<longleftrightarrow> x \<le> y"
  by (simp add: less_eq_top_def)

lemma less_top_Top [simp, code]: "Top < x \<longleftrightarrow> False"
  by (simp add: less_top_def)

lemma less_top_Top_is_Value: "x < Top \<Longrightarrow> \<exists>z. x = Value z"
  by (cases x) (simp_all add: less_top_def)

lemma less_top_Value_Top [simp]: "Value x < Top"
  by (simp add: less_top_def)

lemma less_top_Value_Top_code [code]: "Value x < Top \<longleftrightarrow> True"
  by simp

lemma less_top_Value [simp, code]: "Value x < Value y \<longleftrightarrow> x < y"
  by (simp add: less_top_def)

instance
  by standard
    (auto simp add: less_eq_top_def less_top_def less_le_not_le elim: order_trans split: top.splits)

end

instance top :: (order) order
  by standard (auto simp add: less_eq_top_def less_top_def split: top.splits)

instance top :: (linorder) linorder
  by standard (auto simp add: less_eq_top_def less_top_def split: top.splits)

instantiation top :: (order) top
begin
  definition "top = Top"
  instance ..
end

instantiation top :: (bot) bot
begin
  definition "bot = Value bot"
  instance ..
end

instantiation top :: (semilattice_inf) semilattice_inf
begin

definition inf_top
where
  "inf x y =
    (case x of
      Top \<Rightarrow> y
    | Value v \<Rightarrow>
        (case y of
          Top \<Rightarrow> x
        | Value v' \<Rightarrow> Value (inf v v')))"

instance
  by standard (auto simp add: inf_top_def less_eq_top_def split: top.splits)

end

instantiation top :: (semilattice_sup) semilattice_sup
begin

definition sup_top
where
  "sup x y =
    (case x of
      Top \<Rightarrow> Top
    | Value v \<Rightarrow>
        (case y of
          Top \<Rightarrow> Top
        | Value v' \<Rightarrow> Value (sup v v')))"

instance
  by standard (auto simp add: sup_top_def less_eq_top_def split: top.splits)

end

instance top :: (lattice) bounded_lattice_top
  by standard (simp add: top_top_def)


subsection \<open>Values extended by a top and a bottom element\<close>

datatype 'a flat_complete_lattice = Value 'a | Bot | Top

instantiation flat_complete_lattice :: (type) order
begin

definition less_eq_flat_complete_lattice
where
  "x \<le> y \<equiv>
    (case x of
      Bot \<Rightarrow> True
    | Value v1 \<Rightarrow>
        (case y of
          Bot \<Rightarrow> False
        | Value v2 \<Rightarrow> v1 = v2
        | Top \<Rightarrow> True)
    | Top \<Rightarrow> y = Top)"

definition less_flat_complete_lattice
where
  "x < y =
    (case x of
      Bot \<Rightarrow> y \<noteq> Bot
    | Value v1 \<Rightarrow> y = Top
    | Top \<Rightarrow> False)"

lemma [simp]: "Bot \<le> y"
  unfolding less_eq_flat_complete_lattice_def by auto

lemma [simp]: "y \<le> Top"
  unfolding less_eq_flat_complete_lattice_def by (auto split: flat_complete_lattice.splits)

lemma greater_than_two_values:
  assumes "a \<noteq> b" "Value a \<le> z" "Value b \<le> z"
  shows "z = Top"
  using assms
  by (cases z) (auto simp add: less_eq_flat_complete_lattice_def)

lemma lesser_than_two_values:
  assumes "a \<noteq> b" "z \<le> Value a" "z \<le> Value b"
  shows "z = Bot"
  using assms
  by (cases z) (auto simp add: less_eq_flat_complete_lattice_def)

instance
  by standard
    (auto simp add: less_eq_flat_complete_lattice_def less_flat_complete_lattice_def
      split: flat_complete_lattice.splits)

end

instantiation flat_complete_lattice :: (type) bot
begin
  definition "bot = Bot"
  instance ..
end

instantiation flat_complete_lattice :: (type) top
begin
  definition "top = Top"
  instance ..
end

instantiation flat_complete_lattice :: (type) lattice
begin

definition inf_flat_complete_lattice
where
  "inf x y =
    (case x of
      Bot \<Rightarrow> Bot
    | Value v1 \<Rightarrow>
        (case y of
          Bot \<Rightarrow> Bot
        | Value v2 \<Rightarrow> if v1 = v2 then x else Bot
        | Top \<Rightarrow> x)
    | Top \<Rightarrow> y)"

definition sup_flat_complete_lattice
where
  "sup x y =
    (case x of
      Bot \<Rightarrow> y
    | Value v1 \<Rightarrow>
        (case y of
          Bot \<Rightarrow> x
        | Value v2 \<Rightarrow> if v1 = v2 then x else Top
        | Top \<Rightarrow> Top)
    | Top \<Rightarrow> Top)"

instance
  by standard
    (auto simp add: inf_flat_complete_lattice_def sup_flat_complete_lattice_def
      less_eq_flat_complete_lattice_def split: flat_complete_lattice.splits)

end

instantiation flat_complete_lattice :: (type) complete_lattice
begin

definition Sup_flat_complete_lattice
where
  "Sup A =
    (if A = {} \<or> A = {Bot} then Bot
     else if \<exists>v. A - {Bot} = {Value v} then Value (THE v. A - {Bot} = {Value v})
     else Top)"

definition Inf_flat_complete_lattice
where
  "Inf A =
    (if A = {} \<or> A = {Top} then Top
     else if \<exists>v. A - {Top} = {Value v} then Value (THE v. A - {Top} = {Value v})
     else Bot)"

instance
proof
  fix x :: "'a flat_complete_lattice"
  fix A
  assume "x \<in> A"
  {
    fix v
    assume "A - {Top} = {Value v}"
    then have "(THE v. A - {Top} = {Value v}) = v"
      by (auto intro!: the1_equality)
    moreover
    from \<open>x \<in> A\<close> \<open>A - {Top} = {Value v}\<close> have "x = Top \<or> x = Value v"
      by auto
    ultimately have "Value (THE v. A - {Top} = {Value v}) \<le> x"
      by auto
  }
  with \<open>x \<in> A\<close> show "Inf A \<le> x"
    unfolding Inf_flat_complete_lattice_def
    by fastforce
next
  fix z :: "'a flat_complete_lattice"
  fix A
  show "z \<le> Inf A" if z: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  proof -
    consider "A = {} \<or> A = {Top}"
      | "A \<noteq> {}" "A \<noteq> {Top}" "\<exists>v. A - {Top} = {Value v}"
      | "A \<noteq> {}" "A \<noteq> {Top}" "\<not> (\<exists>v. A - {Top} = {Value v})"
      by blast
    then show ?thesis
    proof cases
      case 1
      then have "Inf A = Top"
        unfolding Inf_flat_complete_lattice_def by auto
      then show ?thesis by simp
    next
      case 2
      then obtain v where v1: "A - {Top} = {Value v}"
        by auto
      then have v2: "(THE v. A - {Top} = {Value v}) = v"
        by (auto intro!: the1_equality)
      from 2 v2 have Inf: "Inf A = Value v"
        unfolding Inf_flat_complete_lattice_def by simp
      from v1 have "Value v \<in> A" by blast
      then have "z \<le> Value v" by (rule z)
      with Inf show ?thesis by simp
    next
      case 3
      then have Inf: "Inf A = Bot"
        unfolding Inf_flat_complete_lattice_def by auto
      have "z \<le> Bot"
      proof (cases "A - {Top} = {Bot}")
        case True
        then have "Bot \<in> A" by blast
        then show ?thesis by (rule z)
      next
        case False
        from 3 obtain a1 where a1: "a1 \<in> A - {Top}"
          by auto
        from 3 False a1 obtain a2 where "a2 \<in> A - {Top} \<and> a1 \<noteq> a2"
          by (cases a1) auto
        with a1 z[of "a1"] z[of "a2"] show ?thesis
          apply (cases a1)
          apply auto
          apply (cases a2)
          apply auto
          apply (auto dest!: lesser_than_two_values)
          done
      qed
      with Inf show ?thesis by simp
    qed
  qed
next
  fix x :: "'a flat_complete_lattice"
  fix A
  assume "x \<in> A"
  {
    fix v
    assume "A - {Bot} = {Value v}"
    then have "(THE v. A - {Bot} = {Value v}) = v"
      by (auto intro!: the1_equality)
    moreover
    from \<open>x \<in> A\<close> \<open>A - {Bot} = {Value v}\<close> have "x = Bot \<or> x = Value v"
      by auto
    ultimately have "x \<le> Value (THE v. A - {Bot} = {Value v})"
      by auto
  }
  with \<open>x \<in> A\<close> show "x \<le> Sup A"
    unfolding Sup_flat_complete_lattice_def
    by fastforce
next
  fix z :: "'a flat_complete_lattice"
  fix A
  show "Sup A \<le> z" if z: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  proof -
    consider "A = {} \<or> A = {Bot}"
      | "A \<noteq> {}" "A \<noteq> {Bot}" "\<exists>v. A - {Bot} = {Value v}"
      | "A \<noteq> {}" "A \<noteq> {Bot}" "\<not> (\<exists>v. A - {Bot} = {Value v})"
      by blast
    then show ?thesis
    proof cases
      case 1
      then have "Sup A = Bot"
        unfolding Sup_flat_complete_lattice_def by auto
      then show ?thesis by simp
    next
      case 2
      then obtain v where v1: "A - {Bot} = {Value v}"
        by auto
      then have v2: "(THE v. A - {Bot} = {Value v}) = v"
        by (auto intro!: the1_equality)
      from 2 v2 have Sup: "Sup A = Value v"
        unfolding Sup_flat_complete_lattice_def by simp
      from v1 have "Value v \<in> A" by blast
      then have "Value v \<le> z" by (rule z)
      with Sup show ?thesis by simp
    next
      case 3
      then have Sup: "Sup A = Top"
        unfolding Sup_flat_complete_lattice_def by auto
      have "Top \<le> z"
      proof (cases "A - {Bot} = {Top}")
        case True
        then have "Top \<in> A" by blast
        then show ?thesis by (rule z)
      next
        case False
        from 3 obtain a1 where a1: "a1 \<in> A - {Bot}"
          by auto
        from 3 False a1 obtain a2 where "a2 \<in> A - {Bot} \<and> a1 \<noteq> a2"
          by (cases a1) auto
        with a1 z[of "a1"] z[of "a2"] show ?thesis
          apply (cases a1)
          apply auto
          apply (cases a2)
          apply (auto dest!: greater_than_two_values)
          done
      qed
      with Sup show ?thesis by simp
    qed
  qed
next
  show "Inf {} = (top :: 'a flat_complete_lattice)"
    by (simp add: Inf_flat_complete_lattice_def top_flat_complete_lattice_def)
  show "Sup {} = (bot :: 'a flat_complete_lattice)"
    by (simp add: Sup_flat_complete_lattice_def bot_flat_complete_lattice_def)
qed

end

end
