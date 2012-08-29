(*  Title:      HOL/Library/Sublist_Order.thy
    Authors:    Peter Lammich, Uni Muenster <peter.lammich@uni-muenster.de>
                Florian Haftmann, Tobias Nipkow, TU Muenchen
*)

header {* Sublist Ordering *}

theory Sublist_Order
imports Main Sublist
begin

text {*
  This theory defines sublist ordering on lists.
  A list @{text ys} is a sublist of a list @{text xs},
  iff one obtains @{text ys} by erasing some elements from @{text xs}.
*}

subsection {* Definitions and basic lemmas *}

instantiation list :: (type) ord
begin

definition
  "(xs :: 'a list) \<le> ys \<longleftrightarrow> emb (op =) xs ys"

definition
  "(xs :: 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"

instance proof qed

end

lemma empty [simp, intro!]: "[] \<le> xs" by (auto simp: less_eq_list_def)

lemma drop: "xs \<le> ys \<Longrightarrow> xs \<le> (y # ys)"
  by (unfold less_eq_list_def) blast

lemma take: "xs \<le> ys \<Longrightarrow> (x#xs) \<le> (x#ys)"
  by (unfold less_eq_list_def) blast

lemmas le_list_induct [consumes 1, case_names empty drop take] =
  emb.induct [of "op =", folded less_eq_list_def]

lemmas le_list_cases [consumes 1, case_names empty drop take] =
  emb.cases [of "op =", folded less_eq_list_def]

lemma le_list_length: "xs \<le> ys \<Longrightarrow> length xs \<le> length ys"
  by (induct rule: le_list_induct) auto

lemma le_list_same_length: "xs \<le> ys \<Longrightarrow> length xs = length ys \<Longrightarrow> xs = ys"
  by (induct rule: le_list_induct) (auto dest: le_list_length)

lemma not_le_list_length[simp]: "length ys < length xs \<Longrightarrow> ~ xs <= ys"
by (metis le_list_length linorder_not_less)

lemma le_list_below_empty [simp]: "xs \<le> [] \<longleftrightarrow> xs = []"
by (auto dest: le_list_length)

lemma le_list_drop_many: "xs \<le> ys \<Longrightarrow> xs \<le> zs @ ys"
by (induct zs) (auto simp: less_eq_list_def)

lemma [code]: "[] <= xs \<longleftrightarrow> True"
by (simp add: less_eq_list_def)

lemma [code]: "(x#xs) <= [] \<longleftrightarrow> False"
by simp

lemma le_list_drop_Cons: assumes "x#xs <= ys" shows "xs <= ys"
proof-
  { fix xs' ys'
    assume "xs' <= ys"
    hence "ALL x xs. xs' = x#xs \<longrightarrow> xs <= ys"
    proof (induct rule: le_list_induct)
      case empty thus ?case by simp
    next
      note drop' = drop
      case drop thus ?case by (metis drop')
    next
      note t = take
      case take thus ?case by (simp add: drop)
    qed }
  from this[OF assms] show ?thesis by simp
qed

lemma le_list_drop_Cons2:
assumes "x#xs <= x#ys" shows "xs <= ys"
using assms
proof (cases rule: le_list_cases)
  case drop thus ?thesis by (metis le_list_drop_Cons list.inject)
qed simp_all

lemma le_list_drop_Cons_neq: assumes "x # xs <= y # ys"
shows "x ~= y \<Longrightarrow> x # xs <= ys"
using assms by (cases rule: le_list_cases) auto

lemma le_list_Cons2_iff[simp,code]: "(x#xs) <= (y#ys) \<longleftrightarrow>
  (if x=y then xs <= ys else (x#xs) <= ys)"
by (metis drop take le_list_drop_Cons2 le_list_drop_Cons_neq)

lemma le_list_take_many_iff: "zs @ xs \<le> zs @ ys \<longleftrightarrow> xs \<le> ys"
by (induct zs) (auto intro: take)

lemma le_list_Cons_EX:
  assumes "x # ys <= zs" shows "EX us vs. zs = us @ x # vs & ys <= vs"
proof-
  { fix xys zs :: "'a list" assume "xys <= zs"
    hence "ALL x ys. xys = x#ys \<longrightarrow> (EX us vs. zs = us @ x # vs & ys <= vs)"
    proof (induct rule: le_list_induct)
      case empty show ?case by simp
    next
      case take thus ?case by (metis list.inject self_append_conv2)
    next
      case drop thus ?case by (metis append_eq_Cons_conv)
    qed
  } with assms show ?thesis by blast
qed

instantiation list :: (type) order
begin

instance proof
  fix xs ys :: "'a list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" unfolding less_list_def .. 
next
  fix xs :: "'a list"
  show "xs \<le> xs" by (induct xs) (auto intro!: drop)
next
  fix xs ys :: "'a list"
  assume "xs <= ys"
  hence "ys <= xs \<longrightarrow> xs = ys"
  proof (induct rule: le_list_induct)
    case empty show ?case by simp
  next
    case take thus ?case by simp
  next
    case drop thus ?case
      by(metis le_list_drop_Cons le_list_length Suc_length_conv Suc_n_not_le_n)
  qed
  moreover assume "ys <= xs"
  ultimately show "xs = ys" by blast
next
  fix xs ys zs :: "'a list"
  assume "xs <= ys"
  hence "ys <= zs \<longrightarrow> xs <= zs"
  proof (induct arbitrary:zs rule: le_list_induct)
    case empty show ?case by simp
  next
    note take' = take
    case (take x y xs ys) show ?case
    proof
      assume "y # ys <= zs"
      with take show "x # xs <= zs"
        by(metis le_list_Cons_EX le_list_drop_many take')
    qed
  next
    case drop thus ?case by (metis le_list_drop_Cons)
  qed
  moreover assume "ys <= zs"
  ultimately show "xs <= zs" by blast
qed

end

lemma le_list_append_le_same_iff: "xs @ ys <= ys \<longleftrightarrow> xs=[]"
by (auto dest: le_list_length)

lemma le_list_append_mono: "\<lbrakk> xs <= xs'; ys <= ys' \<rbrakk> \<Longrightarrow> xs@ys <= xs'@ys'"
apply (induct rule: le_list_induct)
  apply (metis eq_Nil_appendI le_list_drop_many)
 apply (metis Cons_eq_append_conv le_list_drop_Cons order_eq_refl order_trans)
apply simp
done

lemma less_list_length: "xs < ys \<Longrightarrow> length xs < length ys"
by (metis le_list_length le_list_same_length le_neq_implies_less less_list_def)

lemma less_list_empty [simp]: "[] < xs \<longleftrightarrow> xs \<noteq> []"
by (metis empty order_less_le)

lemma less_list_below_empty[simp]: "xs < [] \<longleftrightarrow> False"
by (metis empty less_list_def)

lemma less_list_drop: "xs < ys \<Longrightarrow> xs < x # ys"
by (unfold less_le) (auto intro: drop)

lemma less_list_take_iff: "x # xs < x # ys \<longleftrightarrow> xs < ys"
by (metis le_list_Cons2_iff less_list_def)

lemma less_list_drop_many: "xs < ys \<Longrightarrow> xs < zs @ ys"
by(metis le_list_append_le_same_iff le_list_drop_many order_less_le self_append_conv2)

lemma less_list_take_many_iff: "zs @ xs < zs @ ys \<longleftrightarrow> xs < ys"
by (metis le_list_take_many_iff less_list_def)


subsection {* Appending elements *}

lemma le_list_rev_take_iff[simp]: "xs @ zs \<le> ys @ zs \<longleftrightarrow> xs \<le> ys" (is "?L = ?R")
proof
  { fix xs' ys' xs ys zs :: "'a list" assume "xs' <= ys'"
    hence "xs' = xs @ zs & ys' = ys @ zs \<longrightarrow> xs <= ys"
    proof (induct arbitrary: xs ys zs rule: le_list_induct)
      case empty show ?case by simp
    next
      note drop' = drop
      case (drop xs' ys' x)
      { assume "ys=[]" hence ?case using drop(1) by auto }
      moreover
      { fix us assume "ys = x#us"
        hence ?case using drop(2) by(simp add: drop') }
      ultimately show ?case by (auto simp:Cons_eq_append_conv)
    next
      case (take x y xs' ys')
      { assume "xs=[]" hence ?case using take(1) by auto }
      moreover
      { fix us vs assume "xs=x#us" "ys=x#vs" hence ?case using take by auto}
      moreover
      { fix us assume "xs=x#us" "ys=[]" hence ?case using take(2) by bestsimp }
      ultimately show ?case using `x = y` by (auto simp:Cons_eq_append_conv)
    qed }
  moreover assume ?L
  ultimately show ?R by blast
next
  assume ?R thus ?L by(metis le_list_append_mono order_refl)
qed

lemma less_list_rev_take: "xs @ zs < ys @ zs \<longleftrightarrow> xs < ys"
by (unfold less_le) auto

lemma le_list_rev_drop_many: "xs \<le> ys \<Longrightarrow> xs \<le> ys @ zs"
by (metis append_Nil2 empty le_list_append_mono)


subsection {* Relation to standard list operations *}

lemma le_list_map: "xs \<le> ys \<Longrightarrow> map f xs \<le> map f ys"
by (induct rule: le_list_induct) (auto intro: drop)

lemma le_list_filter_left[simp]: "filter f xs \<le> xs"
by (induct xs) (auto intro: drop)

lemma le_list_filter: "xs \<le> ys \<Longrightarrow> filter f xs \<le> filter f ys"
by (induct rule: le_list_induct) (auto intro: drop)

lemma "xs \<le> ys \<longleftrightarrow> (EX N. xs = sublist ys N)" (is "?L = ?R")
proof
  assume ?L
  thus ?R
  proof (induct rule: le_list_induct)
    case empty show ?case by (metis sublist_empty)
  next
    case (drop xs ys x)
    then obtain N where "xs = sublist ys N" by blast
    hence "xs = sublist (x#ys) (Suc ` N)"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    thus ?case by blast
  next
    case (take x y xs ys)
    then obtain N where "xs = sublist ys N" by blast
    hence "x#xs = sublist (x#ys) (insert 0 (Suc ` N))"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    thus ?case unfolding `x = y` by blast
  qed
next
  assume ?R
  then obtain N where "xs = sublist ys N" ..
  moreover have "sublist ys N <= ys"
  proof (induct ys arbitrary:N)
    case Nil show ?case by simp
  next
    case Cons thus ?case by (auto simp add:sublist_Cons drop)
  qed
  ultimately show ?L by simp
qed

end
