(*  Title:      HOL/Library/Sublist_Order.thy
    Authors:    Peter Lammich, Uni Muenster <peter.lammich@uni-muenster.de>
                Florian Haftmann, TU Muenchen
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

instantiation list :: (type) order
begin

inductive less_eq_list where
  empty [simp, intro!]: "[] \<le> xs"
  | drop: "ys \<le> xs \<Longrightarrow> ys \<le> x # xs"
  | take: "ys \<le> xs \<Longrightarrow> x # ys \<le> x # xs"

lemmas ileq_empty = empty
lemmas ileq_drop = drop
lemmas ileq_take = take

lemma ileq_cases [cases set, case_names empty drop take]:
  assumes "xs \<le> ys"
    and "xs = [] \<Longrightarrow> P"
    and "\<And>z zs. ys = z # zs \<Longrightarrow> xs \<le> zs \<Longrightarrow> P"
    and "\<And>x zs ws. xs = x # zs \<Longrightarrow> ys = x # ws \<Longrightarrow> zs \<le> ws \<Longrightarrow> P"
  shows P
  using assms by (blast elim: less_eq_list.cases)

lemma ileq_induct [induct set, case_names empty drop take]:
  assumes "xs \<le> ys"
    and "\<And>zs. P [] zs"
    and "\<And>z zs ws. ws \<le> zs \<Longrightarrow>  P ws zs \<Longrightarrow> P ws (z # zs)"
    and "\<And>z zs ws. ws \<le> zs \<Longrightarrow> P ws zs \<Longrightarrow> P (z # ws) (z # zs)"
  shows "P xs ys" 
  using assms by (induct rule: less_eq_list.induct) blast+

definition
  [code del]: "(xs \<Colon> 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"

lemma ileq_length: "xs \<le> ys \<Longrightarrow> length xs \<le> length ys"
  by (induct rule: ileq_induct) auto
lemma ileq_below_empty [simp]: "xs \<le> [] \<longleftrightarrow> xs = []"
  by (auto dest: ileq_length)

instance proof
  fix xs ys :: "'a list"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs" unfolding less_list_def .. 
next
  fix xs :: "'a list"
  show "xs \<le> xs" by (induct xs) (auto intro!: ileq_empty ileq_drop ileq_take)
next
  fix xs ys :: "'a list"
  (* TODO: Is there a simpler proof ? *)
  { fix n
    have "!!l l'. \<lbrakk>l\<le>l'; l'\<le>l; n=length l + length l'\<rbrakk> \<Longrightarrow> l=l'"
    proof (induct n rule: nat_less_induct)
      case (1 n l l') from "1.prems"(1) show ?case proof (cases rule: ileq_cases)
        case empty with "1.prems"(2) show ?thesis by auto 
      next
        case (drop a l2') with "1.prems"(2) have "length l'\<le>length l" "length l \<le> length l2'" "1+length l2' = length l'" by (auto dest: ileq_length)
        hence False by simp thus ?thesis ..
      next
        case (take a l1' l2') hence LEN': "length l1' + length l2' < length l + length l'" by simp
        from "1.prems" have LEN: "length l' = length l" by (auto dest!: ileq_length)
        from "1.prems"(2) show ?thesis proof (cases rule: ileq_cases[case_names empty' drop' take'])
          case empty' with take LEN show ?thesis by simp 
        next
          case (drop' ah l2h) with take LEN have "length l1' \<le> length l2h" "1+length l2h = length l2'" "length l2' = length l1'" by (auto dest: ileq_length)
          hence False by simp thus ?thesis ..
        next
          case (take' ah l1h l2h)
          with take have 2: "ah=a" "l1h=l2'" "l2h=l1'" "l1' \<le> l2'" "l2' \<le> l1'" by auto
          with LEN' "1.hyps" "1.prems"(3) have "l1'=l2'" by blast
          with take 2 show ?thesis by simp
        qed
      qed
    qed
  }
  moreover assume "xs \<le> ys" "ys \<le> xs"
  ultimately show "xs = ys" by blast
next
  fix xs ys zs :: "'a list"
  {
    fix n
    have "!!x y z. \<lbrakk>x \<le> y; y \<le> z; n=length x + length y + length z\<rbrakk> \<Longrightarrow> x \<le> z" 
    proof (induct rule: nat_less_induct[case_names I])
      case (I n x y z)
      from I.prems(2) show ?case proof (cases rule: ileq_cases)
        case empty with I.prems(1) show ?thesis by auto
      next
        case (drop a z') hence "length x + length y + length z' < length x + length y + length z" by simp
        with I.hyps I.prems(3,1) drop(2) have "x\<le>z'" by blast
        with drop(1) show ?thesis by (auto intro: ileq_drop)
      next
        case (take a y' z') from I.prems(1) show ?thesis proof (cases rule: ileq_cases[case_names empty' drop' take'])
          case empty' thus ?thesis by auto
        next
          case (drop' ah y'h) with take have "x\<le>y'" "y'\<le>z'" "length x + length y' + length z' < length x + length y + length z" by auto
          with I.hyps I.prems(3) have "x\<le>z'" by (blast)
          with take(2) show ?thesis  by (auto intro: ileq_drop)
        next
          case (take' ah x' y'h) with take have 2: "x=a#x'" "x'\<le>y'" "y'\<le>z'" "length x' + length y' + length z' < length x + length y + length z" by auto
          with I.hyps I.prems(3) have "x'\<le>z'" by blast
          with 2 take(2) show ?thesis by (auto intro: ileq_take)
        qed
      qed
    qed
  }
  moreover assume "xs \<le> ys" "ys \<le> zs"
  ultimately show "xs \<le> zs" by blast
qed

end

lemmas ileq_intros = ileq_empty ileq_drop ileq_take

lemma ileq_drop_many: "xs \<le> ys \<Longrightarrow> xs \<le> zs @ ys"
  by (induct zs) (auto intro: ileq_drop)
lemma ileq_take_many: "xs \<le> ys \<Longrightarrow> zs @ xs \<le> zs @ ys"
  by (induct zs) (auto intro: ileq_take)

lemma ileq_same_length: "xs \<le> ys \<Longrightarrow> length xs = length ys \<Longrightarrow> xs = ys"
  by (induct rule: ileq_induct) (auto dest: ileq_length)
lemma ileq_same_append [simp]: "x # xs \<le> xs \<longleftrightarrow> False"
  by (auto dest: ileq_length)

lemma ilt_length [intro]:
  assumes "xs < ys"
  shows "length xs < length ys"
proof -
  from assms have "xs \<le> ys" and "xs \<noteq> ys" by (simp_all add: less_le)
  moreover with ileq_length have "length xs \<le> length ys" by auto
  ultimately show ?thesis by (auto intro: ileq_same_length)
qed

lemma ilt_empty [simp]: "[] < xs \<longleftrightarrow> xs \<noteq> []"
  by (unfold less_list_def, auto)
lemma ilt_emptyI: "xs \<noteq> [] \<Longrightarrow> [] < xs"
  by (unfold less_list_def, auto)
lemma ilt_emptyD: "[] < xs \<Longrightarrow> xs \<noteq> []"
  by (unfold less_list_def, auto)
lemma ilt_below_empty[simp]: "xs < [] \<Longrightarrow> False"
  by (auto dest: ilt_length)
lemma ilt_drop: "xs < ys \<Longrightarrow> xs < x # ys"
  by (unfold less_le) (auto intro: ileq_intros)
lemma ilt_take: "xs < ys \<Longrightarrow> x # xs < x # ys"
  by (unfold less_le) (auto intro: ileq_intros)
lemma ilt_drop_many: "xs < ys \<Longrightarrow> xs < zs @ ys"
  by (induct zs) (auto intro: ilt_drop)
lemma ilt_take_many: "xs < ys \<Longrightarrow> zs @ xs < zs @ ys"
  by (induct zs) (auto intro: ilt_take)


subsection {* Appending elements *}

lemma ileq_rev_take: "xs \<le> ys \<Longrightarrow> xs @ [x] \<le> ys @ [x]"
  by (induct rule: ileq_induct) (auto intro: ileq_intros ileq_drop_many)
lemma ilt_rev_take: "xs < ys \<Longrightarrow> xs @ [x] < ys @ [x]"
  by (unfold less_le) (auto dest: ileq_rev_take)
lemma ileq_rev_drop: "xs \<le> ys \<Longrightarrow> xs \<le> ys @ [x]"
  by (induct rule: ileq_induct) (auto intro: ileq_intros)
lemma ileq_rev_drop_many: "xs \<le> ys \<Longrightarrow> xs \<le> ys @ zs"
  by (induct zs rule: rev_induct) (auto dest: ileq_rev_drop)


subsection {* Relation to standard list operations *}

lemma ileq_map: "xs \<le> ys \<Longrightarrow> map f xs \<le> map f ys"
  by (induct rule: ileq_induct) (auto intro: ileq_intros)
lemma ileq_filter_left[simp]: "filter f xs \<le> xs"
  by (induct xs) (auto intro: ileq_intros)
lemma ileq_filter: "xs \<le> ys \<Longrightarrow> filter f xs \<le> filter f ys"
  by (induct rule: ileq_induct) (auto intro: ileq_intros) 

end
