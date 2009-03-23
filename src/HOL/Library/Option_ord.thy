(*  Title:      HOL/Library/Option_ord.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Canonical order on option type *}

theory Option_ord
imports Option Main
begin

instantiation option :: (preorder) preorder
begin

definition less_eq_option where
  [code del]: "x \<le> y \<longleftrightarrow> (case x of None \<Rightarrow> True | Some x \<Rightarrow> (case y of None \<Rightarrow> False | Some y \<Rightarrow> x \<le> y))"

definition less_option where
  [code del]: "x < y \<longleftrightarrow> (case y of None \<Rightarrow> False | Some y \<Rightarrow> (case x of None \<Rightarrow> True | Some x \<Rightarrow> x < y))"

lemma less_eq_option_None [simp]: "None \<le> x"
  by (simp add: less_eq_option_def)

lemma less_eq_option_None_code [code]: "None \<le> x \<longleftrightarrow> True"
  by simp

lemma less_eq_option_None_is_None: "x \<le> None \<Longrightarrow> x = None"
  by (cases x) (simp_all add: less_eq_option_def)

lemma less_eq_option_Some_None [simp, code]: "Some x \<le> None \<longleftrightarrow> False"
  by (simp add: less_eq_option_def)

lemma less_eq_option_Some [simp, code]: "Some x \<le> Some y \<longleftrightarrow> x \<le> y"
  by (simp add: less_eq_option_def)

lemma less_option_None [simp, code]: "x < None \<longleftrightarrow> False"
  by (simp add: less_option_def)

lemma less_option_None_is_Some: "None < x \<Longrightarrow> \<exists>z. x = Some z"
  by (cases x) (simp_all add: less_option_def)

lemma less_option_None_Some [simp]: "None < Some x"
  by (simp add: less_option_def)

lemma less_option_None_Some_code [code]: "None < Some x \<longleftrightarrow> True"
  by simp

lemma less_option_Some [simp, code]: "Some x < Some y \<longleftrightarrow> x < y"
  by (simp add: less_option_def)

instance proof
qed (auto simp add: less_eq_option_def less_option_def less_le_not_le elim: order_trans split: option.splits)

end 

instance option :: (order) order proof
qed (auto simp add: less_eq_option_def less_option_def split: option.splits)

instance option :: (linorder) linorder proof
qed (auto simp add: less_eq_option_def less_option_def split: option.splits)

instantiation option :: (preorder) bot
begin

definition "bot = None"

instance proof
qed (simp add: bot_option_def)

end

instantiation option :: (top) top
begin

definition "top = Some top"

instance proof
qed (simp add: top_option_def less_eq_option_def split: option.split)

end

instance option :: (wellorder) wellorder proof
  fix P :: "'a option \<Rightarrow> bool" and z :: "'a option"
  assume H: "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  have "P None" by (rule H) simp
  then have P_Some [case_names Some]:
    "\<And>z. (\<And>x. z = Some x \<Longrightarrow> (P o Some) x) \<Longrightarrow> P z"
  proof -
    fix z
    assume "\<And>x. z = Some x \<Longrightarrow> (P o Some) x"
    with `P None` show "P z" by (cases z) simp_all
  qed
  show "P z" proof (cases z rule: P_Some)
    case (Some w)
    show "(P o Some) w" proof (induct rule: less_induct)
      case (less x)
      have "P (Some x)" proof (rule H)
        fix y :: "'a option"
        assume "y < Some x"
        show "P y" proof (cases y rule: P_Some)
          case (Some v) with `y < Some x` have "v < x" by simp
          with less show "(P o Some) v" .
        qed
      qed
      then show ?case by simp
    qed
  qed
qed

end
