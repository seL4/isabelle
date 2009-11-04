(*  Title:      HOL/Library/Sublist_Order.thy
    Authors:    Peter Lammich, Uni Muenster <peter.lammich@uni-muenster.de>
                Florian Haftmann, Tobias Nipkow, TU Muenchen
*)

header {* Sublist Ordering *}

theory Sublist_Order
imports Main
begin

text {*
  This theory defines sublist ordering on lists.
  A list @{text ys} is a sublist of a list @{text xs},
  iff one obtains @{text ys} by erasing some elements from @{text xs}.
*}

subsection {* Definitions and basic lemmas *}

instantiation list :: (type) ord
begin

inductive less_eq_list where
  empty [simp, intro!]: "[] \<le> xs"
  | drop: "ys \<le> xs \<Longrightarrow> ys \<le> x # xs"
  | take: "ys \<le> xs \<Longrightarrow> x # ys \<le> x # xs"

definition
  [code del]: "(xs \<Colon> 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"

instance proof qed

end

lemma le_list_length: "xs \<le> ys \<Longrightarrow> length xs \<le> length ys"
by (induct rule: less_eq_list.induct) auto

lemma le_list_same_length: "xs \<le> ys \<Longrightarrow> length xs = length ys \<Longrightarrow> xs = ys"
by (induct rule: less_eq_list.induct) (auto dest: le_list_length)

lemma not_le_list_length[simp]: "length ys < length xs \<Longrightarrow> ~ xs <= ys"
by (metis le_list_length linorder_not_less)

lemma le_list_below_empty [simp]: "xs \<le> [] \<longleftrightarrow> xs = []"
by (auto dest: le_list_length)

lemma le_list_drop_many: "xs \<le> ys \<Longrightarrow> xs \<le> zs @ ys"
by (induct zs) (auto intro: drop)

lemma [code]: "[] <= xs \<longleftrightarrow> True"
by(metis less_eq_list.empty)

lemma [code]: "(x#xs) <= [] \<longleftrightarrow> False"
by simp

lemma le_list_drop_Cons: assumes "x#xs <= ys" shows "xs <= ys"
proof-
  { fix xs' ys'
    assume "xs' <= ys"
    hence "ALL x xs. xs' = x#xs \<longrightarrow> xs <= ys"
    proof induct
      case empty thus ?case by simp
    next
      case drop thus ?case by (metis less_eq_list.drop)
    next
      case take thus ?case by (simp add: drop)
    qed }
  from this[OF assms] show ?thesis by simp
qed

lemma le_list_drop_Cons2:
assumes "x#xs <= x#ys" shows "xs <= ys"
using assms
proof cases
  case drop thus ?thesis by (metis le_list_drop_Cons list.inject)
qed simp_all

lemma le_list_drop_Cons_neq: assumes "x # xs <= y # ys"
shows "x ~= y \<Longrightarrow> x # xs <= ys"
using assms proof cases qed auto

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
    proof induct
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
  show "xs \<le> xs" by (induct xs) (auto intro!: less_eq_list.drop)
next
  fix xs ys :: "'a list"
  assume "xs <= ys"
  hence "ys <= xs \<longrightarrow> xs = ys"
  proof induct
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
  proof (induct arbitrary:zs)
    case empty show ?case by simp
  next
    case (take xs ys x) show ?case
    proof
      assume "x # ys <= zs"
      with take show "x # xs <= zs"
        by(metis le_list_Cons_EX le_list_drop_many less_eq_list.take local.take(2))
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
apply (induct rule:less_eq_list.induct)
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
by (unfold less_le) (auto intro: less_eq_list.drop)

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
    proof (induct arbitrary: xs ys zs)
      case empty show ?case by simp
    next
      case (drop xs' ys' x)
      { assume "ys=[]" hence ?case using drop(1) by auto }
      moreover
      { fix us assume "ys = x#us"
        hence ?case using drop(2) by(simp add: less_eq_list.drop) }
      ultimately show ?case by (auto simp:Cons_eq_append_conv)
    next
      case (take xs' ys' x)
      { assume "xs=[]" hence ?case using take(1) by auto }
      moreover
      { fix us vs assume "xs=x#us" "ys=x#vs" hence ?case using take(2) by auto}
      moreover
      { fix us assume "xs=x#us" "ys=[]" hence ?case using take(2) by bestsimp }
      ultimately show ?case by (auto simp:Cons_eq_append_conv)
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
by (induct rule: less_eq_list.induct) (auto intro: less_eq_list.drop)

lemma le_list_filter_left[simp]: "filter f xs \<le> xs"
by (induct xs) (auto intro: less_eq_list.drop)

lemma le_list_filter: "xs \<le> ys \<Longrightarrow> filter f xs \<le> filter f ys"
by (induct rule: less_eq_list.induct) (auto intro: less_eq_list.drop)


lemma "xs <= ys \<longleftrightarrow> (EX N. xs = sublist ys N)" (is "?L = ?R")
proof
  assume ?L
  thus ?R
  proof induct
    case empty show ?case by (metis sublist_empty)
  next
    case (drop xs ys x)
    then obtain N where "xs = sublist ys N" by blast
    hence "xs = sublist (x#ys) (Suc ` N)"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    thus ?case by blast
  next
    case (take xs ys x)
    then obtain N where "xs = sublist ys N" by blast
    hence "x#xs = sublist (x#ys) (insert 0 (Suc ` N))"
      by (clarsimp simp add:sublist_Cons inj_image_mem_iff)
    thus ?case by blast
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
