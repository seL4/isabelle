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

subsection {* A non-distributive lattice *}

datatype non_distrib_lattice = Zero | A | B | C | One

instantiation non_distrib_lattice :: order
begin

definition less_eq_non_distrib_lattice
where
  "a <= b = (case a of Zero => True | A => (b = A) \<or> (b = One) | B => (b = B) \<or> (b = One) | C => (b = C) \<or> (b = One) | One => (b = One))"

definition less_non_distrib_lattice
where
  "a < b = (case a of Zero => (b \<noteq> Zero) | A => (b = One) | B => (b = One) | C => (b = One) | One => False)"

instance proof
qed (auto simp add: less_eq_non_distrib_lattice_def less_non_distrib_lattice_def split: non_distrib_lattice.split non_distrib_lattice.split_asm)

end

instantiation non_distrib_lattice :: lattice
begin


definition sup_non_distrib_lattice
where
  "sup a b = (if a = b then a else (if a = Zero then b else (if b = Zero then a else One)))"

definition inf_non_distrib_lattice
where
  "inf a b = (if a = b then a else (if a = One then b else (if b = One then a else Zero)))"

instance proof
qed (auto simp add: inf_non_distrib_lattice_def sup_non_distrib_lattice_def less_eq_non_distrib_lattice_def split: split_if non_distrib_lattice.split non_distrib_lattice.split_asm)

end

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

instantiation bot :: (preorder) bot
begin

definition "bot = Bot"

instance proof
qed (simp add: bot_bot_def)

end

instantiation bot :: (top) top
begin

definition "top = Value top"

instance proof
qed (simp add: top_bot_def less_eq_bot_def split: bot.split)

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

instance bot :: (lattice) bounded_lattice_bot ..

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

instantiation top :: (preorder) top
begin

definition "top = Top"

instance proof
qed (simp add: top_top_def)

end

instantiation top :: (bot) bot
begin

definition "bot = Value bot"

instance proof
qed (simp add: bot_top_def less_eq_top_def split: top.split)

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

instance top :: (lattice) bounded_lattice_top ..

section {* Quickcheck configuration *}

quickcheck_params[default_type = ["int", "non_distrib_lattice", "int bot", "int top"]]

hide_type non_distrib_lattice bot top

end