(*  Title:      HOL/Library/Quickcheck_Types.thy
    Author:     Lukas Bulwahn
    Copyright   2010 TU Muenchen
*)

theory Quickcheck_Types
imports Main
begin

text {*
This theory provides some default types for the quickcheck execution.
In most cases, the default type @{typ "int"} meets the sort constraints
of the proposition.
But for the type classes bot and top, the type @{typ "int"} is insufficient.
Hence, we provide other types than @{typ "int"} as further default types.  
*}

subsection {* Values extended by a bottom element *}

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

instance proof
qed (auto simp add: less_eq_bot_def less_bot_def less_le_not_le elim: order_trans split: bot.splits)

end 

instance bot :: (order) order proof
qed (auto simp add: less_eq_bot_def less_bot_def split: bot.splits)

instance bot :: (linorder) linorder proof
qed (auto simp add: less_eq_bot_def less_bot_def split: bot.splits)

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
  "inf x y = (case x of Bot => Bot | Value v => (case y of Bot => Bot | Value v' => Value (inf v v')))"

instance proof
qed (auto simp add: inf_bot_def less_eq_bot_def split: bot.splits)

end

instantiation bot :: (semilattice_sup) semilattice_sup
begin

definition sup_bot
where
  "sup x y = (case x of Bot => y | Value v => (case y of Bot => x | Value v' => Value (sup v v')))"

instance proof
qed (auto simp add: sup_bot_def less_eq_bot_def split: bot.splits)

end

instance bot :: (lattice) bounded_lattice_bot
by(intro_classes)(simp add: bot_bot_def)

section {* Values extended by a top element *}

datatype 'a top = Value 'a | Top

instantiation top :: (preorder) preorder
begin

definition less_eq_top where
  "x \<le> y \<longleftrightarrow> (case y of Top \<Rightarrow> True | Value y \<Rightarrow> (case x of Top \<Rightarrow> False | Value x \<Rightarrow> x \<le> y))"

definition less_top where
  "x < y \<longleftrightarrow> (case x of Top \<Rightarrow> False | Value x \<Rightarrow> (case y of Top \<Rightarrow> True | Value y \<Rightarrow> x < y))"

lemma less_eq_top_Top [simp]: "x <= Top"
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

instance proof
qed (auto simp add: less_eq_top_def less_top_def less_le_not_le elim: order_trans split: top.splits)

end 

instance top :: (order) order proof
qed (auto simp add: less_eq_top_def less_top_def split: top.splits)

instance top :: (linorder) linorder proof
qed (auto simp add: less_eq_top_def less_top_def split: top.splits)

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
  "inf x y = (case x of Top => y | Value v => (case y of Top => x | Value v' => Value (inf v v')))"

instance proof
qed (auto simp add: inf_top_def less_eq_top_def split: top.splits)

end

instantiation top :: (semilattice_sup) semilattice_sup
begin

definition sup_top
where
  "sup x y = (case x of Top => Top | Value v => (case y of Top => Top | Value v' => Value (sup v v')))"

instance proof
qed (auto simp add: sup_top_def less_eq_top_def split: top.splits)

end

instance top :: (lattice) bounded_lattice_top
by(intro_classes)(simp add: top_top_def)


datatype 'a flat_complete_lattice = Value 'a | Bot | Top

instantiation flat_complete_lattice :: (type) order
begin

definition less_eq_flat_complete_lattice where
  "x \<le> y == (case x of Bot => True | Value v1 => (case y of Bot => False | Value v2 => (v1 = v2) | Top => True) | Top => (y = Top))"

definition less_flat_complete_lattice where
  "x < y = (case x of Bot => \<not> (y = Bot) | Value v1 => (y = Top) | Top => False)"

lemma [simp]: "Bot <= y"
unfolding less_eq_flat_complete_lattice_def by auto

lemma [simp]: "y <= Top"
unfolding less_eq_flat_complete_lattice_def by (auto split: flat_complete_lattice.splits)

lemma greater_than_two_values:
  assumes "a ~= aa" "Value a <= z" "Value aa <= z"
  shows "z = Top"
using assms
by (cases z) (auto simp add: less_eq_flat_complete_lattice_def)

lemma lesser_than_two_values:
  assumes "a ~= aa" "z <= Value a" "z <= Value aa"
  shows "z = Bot"
using assms
by (cases z) (auto simp add: less_eq_flat_complete_lattice_def)

instance proof
qed (auto simp add: less_eq_flat_complete_lattice_def less_flat_complete_lattice_def split: flat_complete_lattice.splits)

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
  "inf x y = (case x of Bot => Bot | Value v1 => (case y of Bot => Bot | Value v2 => if (v1 = v2) then x else Bot | Top => x) | Top => y)"

definition sup_flat_complete_lattice
where
  "sup x y = (case x of Bot => y | Value v1 => (case y of Bot => x | Value v2 => if v1 = v2 then x else Top | Top => Top) | Top => Top)"

instance proof
qed (auto simp add: inf_flat_complete_lattice_def sup_flat_complete_lattice_def less_eq_flat_complete_lattice_def split: flat_complete_lattice.splits)

end

instantiation flat_complete_lattice :: (type) complete_lattice
begin

definition Sup_flat_complete_lattice
where
  "Sup A = (if (A = {} \<or> A = {Bot}) then Bot else (if (\<exists> v. A - {Bot} = {Value v}) then Value (THE v. A - {Bot} = {Value v}) else Top))"

definition Inf_flat_complete_lattice
where
  "Inf A = (if (A = {} \<or> A = {Top}) then Top else (if (\<exists> v. A - {Top} = {Value v}) then Value (THE v. A - {Top} = {Value v}) else Bot))"
 
instance
proof
  fix x A
  assume "(x :: 'a flat_complete_lattice) : A"
  {
    fix v
    assume "A - {Top} = {Value v}"
    from this have "(THE v. A - {Top} = {Value v}) = v"
      by (auto intro!: the1_equality)
    moreover
    from `x : A` `A - {Top} = {Value v}` have "x = Top \<or> x = Value v"
      by auto
    ultimately have "Value (THE v. A - {Top} = {Value v}) <= x"
      by auto
  }
  from `x : A` this show "Inf A <= x"
    unfolding Inf_flat_complete_lattice_def
    by fastforce
next
  fix z A
  assume z: "\<And>x. x : A ==> z <= (x :: 'a flat_complete_lattice)"
  {
    fix v
    assume "A - {Top} = {Value v}"
    moreover
    from this have "(THE v. A - {Top} = {Value v}) = v"
      by (auto intro!: the1_equality)
    moreover
    note z
    moreover
    ultimately have "z <= Value (THE v::'a. A - {Top} = {Value v})"
      by auto
  } moreover
  {
    assume not_one_value: "A ~= {}" "A ~= {Top}" "~ (EX v::'a. A - {Top} = {Value v})"
    have "z <= Bot"
    proof (cases "A - {Top} = {Bot}")
      case True
      from this z show ?thesis
        by auto
    next
      case False
      from not_one_value
      obtain a1 where a1: "a1 : A - {Top}" by auto
      from not_one_value False a1
      obtain a2 where "a2 : A - {Top} \<and> a1 \<noteq> a2"
        by (cases a1) auto
      from this a1 z[of "a1"] z[of "a2"] show ?thesis
        apply (cases a1)
        apply auto
        apply (cases a2)
        apply auto
        apply (auto dest!: lesser_than_two_values)
        done
    qed
  } moreover
  note z moreover
  ultimately show "z <= Inf A"
    unfolding Inf_flat_complete_lattice_def
    by auto
next
  fix x A
  assume "(x :: 'a flat_complete_lattice) : A"
  {
    fix v
    assume "A - {Bot} = {Value v}"
    from this have "(THE v. A - {Bot} = {Value v}) = v"
      by (auto intro!: the1_equality)
    moreover
    from `x : A` `A - {Bot} = {Value v}` have "x = Bot \<or> x = Value v"
      by auto
    ultimately have "x <= Value (THE v. A - {Bot} = {Value v})"
      by auto
  }
  from `x : A` this show "x <= Sup A"
    unfolding Sup_flat_complete_lattice_def
    by fastforce
next
  fix z A
  assume z: "\<And>x. x : A ==> x <= (z :: 'a flat_complete_lattice)"
  {
    fix v
    assume "A - {Bot} = {Value v}"
    moreover
    from this have "(THE v. A - {Bot} = {Value v}) = v"
      by (auto intro!: the1_equality)
    moreover
    note z
    moreover
    ultimately have "Value (THE v::'a. A - {Bot} = {Value v}) <= z"
      by auto
  } moreover
  {
    assume not_one_value: "A ~= {}" "A ~= {Bot}" "~ (EX v::'a. A - {Bot} = {Value v})"
    have "Top <= z"
    proof (cases "A - {Bot} = {Top}")
      case True
      from this z show ?thesis
        by auto
    next
      case False
      from not_one_value
      obtain a1 where a1: "a1 : A - {Bot}" by auto
      from not_one_value False a1
      obtain a2 where "a2 : A - {Bot} \<and> a1 \<noteq> a2"
        by (cases a1) auto
      from this a1 z[of "a1"] z[of "a2"] show ?thesis
        apply (cases a1)
        apply auto
        apply (cases a2)
        apply (auto dest!: greater_than_two_values)
        done
    qed
  } moreover
  note z moreover
  ultimately show "Sup A <= z"
    unfolding Sup_flat_complete_lattice_def
    by auto
next
  show "Inf {} = (top :: 'a flat_complete_lattice)"
    by(simp add: Inf_flat_complete_lattice_def top_flat_complete_lattice_def)
next
  show "Sup {} = (bot :: 'a flat_complete_lattice)"
    by(simp add: Sup_flat_complete_lattice_def bot_flat_complete_lattice_def)
qed

end

section {* Quickcheck configuration *}

quickcheck_params[finite_types = false, default_type = ["int", "int bot", "int top", "Enum.finite_4 flat_complete_lattice"]]

hide_type flat_complete_lattice bot top

end