(*  Title:      HOL/Library/Multiset_Order.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
*)

section \<open>More Theorems about the Multiset Order\<close>

theory Multiset_Order
imports Multiset
begin

subsection \<open>Alternative Characterizations\<close>

context preorder
begin

lemma order_mult: "class.order
  (\<lambda>M N. (M, N) \<in> mult {(x, y). x < y} \<or> M = N)
  (\<lambda>M N. (M, N) \<in> mult {(x, y). x < y})"
  (is "class.order ?le ?less")
proof -
  have irrefl: "\<And>M :: 'a multiset. \<not> ?less M M"
  proof
    fix M :: "'a multiset"
    have "trans {(x'::'a, x). x' < x}"
      by (rule transI) (blast intro: less_trans)
    moreover
    assume "(M, M) \<in> mult {(x, y). x < y}"
    ultimately have "\<exists>I J K. M = I + J \<and> M = I + K
      \<and> J \<noteq> {#} \<and> (\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset J. (k, j) \<in> {(x, y). x < y})"
      by (rule mult_implies_one_step)
    then obtain I J K where "M = I + J" and "M = I + K"
      and "J \<noteq> {#}" and "(\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset J. (k, j) \<in> {(x, y). x < y})" by blast
    then have aux1: "K \<noteq> {#}" and aux2: "\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset K. k < j" by auto
    have "finite (set_mset K)" by simp
    moreover note aux2
    ultimately have "set_mset K = {}"
      by (induct rule: finite_induct)
       (simp, metis (mono_tags) insert_absorb insert_iff insert_not_empty less_irrefl less_trans)
    with aux1 show False by simp
  qed
  have trans: "\<And>K M N :: 'a multiset. ?less K M \<Longrightarrow> ?less M N \<Longrightarrow> ?less K N"
    unfolding mult_def by (blast intro: trancl_trans)
  show "class.order ?le ?less"
    by standard (auto simp add: less_eq_multiset_def irrefl dest: trans)
qed

text \<open>The Dershowitz--Manna ordering:\<close>

definition less_multiset\<^sub>D\<^sub>M where
  "less_multiset\<^sub>D\<^sub>M M N \<longleftrightarrow>
   (\<exists>X Y. X \<noteq> {#} \<and> X \<subseteq># N \<and> M = (N - X) + Y \<and> (\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> k < a)))"


text \<open>The Huet--Oppen ordering:\<close>

definition less_multiset\<^sub>H\<^sub>O where
  "less_multiset\<^sub>H\<^sub>O M N \<longleftrightarrow> M \<noteq> N \<and> (\<forall>y. count N y < count M y \<longrightarrow> (\<exists>x. y < x \<and> count M x < count N x))"

lemma mult_imp_less_multiset\<^sub>H\<^sub>O:
  "(M, N) \<in> mult {(x, y). x < y} \<Longrightarrow> less_multiset\<^sub>H\<^sub>O M N"
proof (unfold mult_def, induct rule: trancl_induct)
  case (base P)
  then show ?case
    by (auto elim!: mult1_lessE simp add: count_eq_zero_iff less_multiset\<^sub>H\<^sub>O_def split: if_splits dest!: Suc_lessD)
next
  case (step N P)
  from step(3) have "M \<noteq> N" and
    **: "\<And>y. count N y < count M y \<Longrightarrow> (\<exists>x>y. count M x < count N x)"
    by (simp_all add: less_multiset\<^sub>H\<^sub>O_def)
  from step(2) obtain M0 a K where
    *: "P = add_mset a M0" "N = M0 + K" "a \<notin># K" "\<And>b. b \<in># K \<Longrightarrow> b < a"
    by (blast elim: mult1_lessE)
  from \<open>M \<noteq> N\<close> ** *(1,2,3) have "M \<noteq> P" by (force dest: *(4) elim!: less_asym split: if_splits )
  moreover
  { assume "count P a \<le> count M a"
    with \<open>a \<notin># K\<close> have "count N a < count M a" unfolding *(1,2)
      by (auto simp add: not_in_iff)
      with ** obtain z where z: "z > a" "count M z < count N z"
        by blast
      with * have "count N z \<le> count P z" 
        by (auto elim: less_asym intro: count_inI)
      with z have "\<exists>z > a. count M z < count P z" by auto
  } note count_a = this
  { fix y
    assume count_y: "count P y < count M y"
    have "\<exists>x>y. count M x < count P x"
    proof (cases "y = a")
      case True
      with count_y count_a show ?thesis by auto
    next
      case False
      show ?thesis
      proof (cases "y \<in># K")
        case True
        with *(4) have "y < a" by simp
        then show ?thesis by (cases "count P a \<le> count M a") (auto dest: count_a intro: less_trans)
      next
        case False
        with \<open>y \<noteq> a\<close> have "count P y = count N y" unfolding *(1,2)
          by (simp add: not_in_iff)
        with count_y ** obtain z where z: "z > y" "count M z < count N z" by auto
        show ?thesis
        proof (cases "z \<in># K")
          case True
          with *(4) have "z < a" by simp
          with z(1) show ?thesis
            by (cases "count P a \<le> count M a") (auto dest!: count_a intro: less_trans)
        next
          case False
          with \<open>a \<notin># K\<close> have "count N z \<le> count P z" unfolding *
            by (auto simp add: not_in_iff)
          with z show ?thesis by auto
        qed
      qed
    qed
  }
  ultimately show ?case unfolding less_multiset\<^sub>H\<^sub>O_def by blast
qed

lemma less_multiset\<^sub>D\<^sub>M_imp_mult:
  "less_multiset\<^sub>D\<^sub>M M N \<Longrightarrow> (M, N) \<in> mult {(x, y). x < y}"
proof -
  assume "less_multiset\<^sub>D\<^sub>M M N"
  then obtain X Y where
    "X \<noteq> {#}" and "X \<subseteq># N" and "M = N - X + Y" and "\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> k < a)"
    unfolding less_multiset\<^sub>D\<^sub>M_def by blast
  then have "(N - X + Y, N - X + X) \<in> mult {(x, y). x < y}"
    by (intro one_step_implies_mult) (auto simp: Bex_def trans_def)
  with \<open>M = N - X + Y\<close> \<open>X \<subseteq># N\<close> show "(M, N) \<in> mult {(x, y). x < y}"
    by (metis subset_mset.diff_add)
qed

lemma less_multiset\<^sub>H\<^sub>O_imp_less_multiset\<^sub>D\<^sub>M: "less_multiset\<^sub>H\<^sub>O M N \<Longrightarrow> less_multiset\<^sub>D\<^sub>M M N"
unfolding less_multiset\<^sub>D\<^sub>M_def
proof (intro iffI exI conjI)
  assume "less_multiset\<^sub>H\<^sub>O M N"
  then obtain z where z: "count M z < count N z"
    unfolding less_multiset\<^sub>H\<^sub>O_def by (auto simp: multiset_eq_iff nat_neq_iff)
  define X where "X = N - M"
  define Y where "Y = M - N"
  from z show "X \<noteq> {#}" unfolding X_def by (auto simp: multiset_eq_iff not_less_eq_eq Suc_le_eq)
  from z show "X \<subseteq># N" unfolding X_def by auto
  show "M = (N - X) + Y" unfolding X_def Y_def multiset_eq_iff count_union count_diff by force
  show "\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> k < a)"
  proof (intro allI impI)
    fix k
    assume "k \<in># Y"
    then have "count N k < count M k" unfolding Y_def
      by (auto simp add: in_diff_count)
    with \<open>less_multiset\<^sub>H\<^sub>O M N\<close> obtain a where "k < a" and "count M a < count N a"
      unfolding less_multiset\<^sub>H\<^sub>O_def by blast
    then show "\<exists>a. a \<in># X \<and> k < a" unfolding X_def
      by (auto simp add: in_diff_count)
  qed
qed

lemma mult_less_multiset\<^sub>D\<^sub>M: "(M, N) \<in> mult {(x, y). x < y} \<longleftrightarrow> less_multiset\<^sub>D\<^sub>M M N"
  by (metis less_multiset\<^sub>D\<^sub>M_imp_mult less_multiset\<^sub>H\<^sub>O_imp_less_multiset\<^sub>D\<^sub>M mult_imp_less_multiset\<^sub>H\<^sub>O)

lemma mult_less_multiset\<^sub>H\<^sub>O: "(M, N) \<in> mult {(x, y). x < y} \<longleftrightarrow> less_multiset\<^sub>H\<^sub>O M N"
  by (metis less_multiset\<^sub>D\<^sub>M_imp_mult less_multiset\<^sub>H\<^sub>O_imp_less_multiset\<^sub>D\<^sub>M mult_imp_less_multiset\<^sub>H\<^sub>O)

lemmas mult\<^sub>D\<^sub>M = mult_less_multiset\<^sub>D\<^sub>M[unfolded less_multiset\<^sub>D\<^sub>M_def]
lemmas mult\<^sub>H\<^sub>O = mult_less_multiset\<^sub>H\<^sub>O[unfolded less_multiset\<^sub>H\<^sub>O_def]

end

lemma less_multiset_less_multiset\<^sub>H\<^sub>O: "M < N \<longleftrightarrow> less_multiset\<^sub>H\<^sub>O M N"
  unfolding less_multiset_def mult\<^sub>H\<^sub>O less_multiset\<^sub>H\<^sub>O_def ..

lemmas less_multiset\<^sub>D\<^sub>M = mult\<^sub>D\<^sub>M[folded less_multiset_def]
lemmas less_multiset\<^sub>H\<^sub>O = mult\<^sub>H\<^sub>O[folded less_multiset_def]

lemma subset_eq_imp_le_multiset:
  shows "M \<subseteq># N \<Longrightarrow> M \<le> N"
  unfolding less_eq_multiset_def less_multiset\<^sub>H\<^sub>O
  by (simp add: less_le_not_le subseteq_mset_def)

(* FIXME: "le" should be "less" in this and other names *)
lemma le_multiset_right_total: "M < add_mset x M"
  unfolding less_eq_multiset_def less_multiset\<^sub>H\<^sub>O by simp

lemma less_eq_multiset_empty_left[simp]:
  shows "{#} \<le> M"
  by (simp add: subset_eq_imp_le_multiset)

lemma ex_gt_imp_less_multiset: "(\<exists>y. y \<in># N \<and> (\<forall>x. x \<in># M \<longrightarrow> x < y)) \<Longrightarrow> M < N"
  unfolding less_multiset\<^sub>H\<^sub>O
  by (metis count_eq_zero_iff count_greater_zero_iff less_le_not_le)

lemma less_eq_multiset_empty_right[simp]: "M \<noteq> {#} \<Longrightarrow> \<not> M \<le> {#}"
  by (metis less_eq_multiset_empty_left antisym)

(* FIXME: "le" should be "less" in this and other names *)
lemma le_multiset_empty_left[simp]: "M \<noteq> {#} \<Longrightarrow> {#} < M"
  by (simp add: less_multiset\<^sub>H\<^sub>O)

(* FIXME: "le" should be "less" in this and other names *)
lemma le_multiset_empty_right[simp]: "\<not> M < {#}"
  using subset_mset.le_zero_eq less_multiset\<^sub>D\<^sub>M by blast

(* FIXME: "le" should be "less" in this and other names *)
lemma union_le_diff_plus: "P \<subseteq># M \<Longrightarrow> N < P \<Longrightarrow> M - P + N < M"
  by (drule subset_mset.diff_add[symmetric]) (metis union_le_mono2)

instantiation multiset :: (preorder) ordered_ab_semigroup_monoid_add_imp_le
begin

lemma less_eq_multiset\<^sub>H\<^sub>O:
  "M \<le> N \<longleftrightarrow> (\<forall>y. count N y < count M y \<longrightarrow> (\<exists>x. y < x \<and> count M x < count N x))"
  by (auto simp: less_eq_multiset_def less_multiset\<^sub>H\<^sub>O)

instance by standard (auto simp: less_eq_multiset\<^sub>H\<^sub>O)

lemma
  fixes M N :: "'a multiset"
  shows
    less_eq_multiset_plus_left: "N \<le> (M + N)" and
    less_eq_multiset_plus_right: "M \<le> (M + N)"
  by simp_all

lemma
  fixes M N :: "'a multiset"
  shows
    le_multiset_plus_left_nonempty: "M \<noteq> {#} \<Longrightarrow> N < M + N" and
    le_multiset_plus_right_nonempty: "N \<noteq> {#} \<Longrightarrow> M < M + N"
    by simp_all

end

lemma all_lt_Max_imp_lt_mset: "N \<noteq> {#} \<Longrightarrow> (\<forall>a \<in># M. a < Max (set_mset N)) \<Longrightarrow> M < N"
  by (meson Max_in[OF finite_set_mset] ex_gt_imp_less_multiset set_mset_eq_empty_iff)

lemma lt_imp_ex_count_lt: "M < N \<Longrightarrow> \<exists>y. count M y < count N y"
  by (meson less_eq_multiset\<^sub>H\<^sub>O less_le_not_le)

lemma subset_imp_less_mset: "A \<subset># B \<Longrightarrow> A < B"
  by (simp add: order.not_eq_order_implies_strict subset_eq_imp_le_multiset)

lemma image_mset_strict_mono:
  assumes
    mono_f: "\<forall>x \<in> set_mset M. \<forall>y \<in> set_mset N. x < y \<longrightarrow> f x < f y" and
    less: "M < N"
  shows "image_mset f M < image_mset f N"
proof -
  obtain Y X where
    y_nemp: "Y \<noteq> {#}" and y_sub_N: "Y \<subseteq># N" and M_eq: "M = N - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> x < y)"
    using less[unfolded less_multiset\<^sub>D\<^sub>M] by blast

  have x_sub_M: "X \<subseteq># M"
    using M_eq by simp

  let ?fY = "image_mset f Y"
  let ?fX = "image_mset f X"

  show ?thesis
    unfolding less_multiset\<^sub>D\<^sub>M
  proof (intro exI conjI)
    show "image_mset f M = image_mset f N - ?fY + ?fX"
      using M_eq[THEN arg_cong, of "image_mset f"] y_sub_N
      by (metis image_mset_Diff image_mset_union)
  next
    obtain y where y: "\<forall>x. x \<in># X \<longrightarrow> y x \<in># Y \<and> x < y x"
      using ex_y by moura

    show "\<forall>fx. fx \<in># ?fX \<longrightarrow> (\<exists>fy. fy \<in># ?fY \<and> fx < fy)"
    proof (intro allI impI)
      fix fx
      assume "fx \<in># ?fX"
      then obtain x where fx: "fx = f x" and x_in: "x \<in># X"
        by auto
      hence y_in: "y x \<in># Y" and y_gt: "x < y x"
        using y[rule_format, OF x_in] by blast+
      hence "f (y x) \<in># ?fY \<and> f x < f (y x)"
        using mono_f y_sub_N x_sub_M x_in
        by (metis image_eqI in_image_mset mset_subset_eqD)
      thus "\<exists>fy. fy \<in># ?fY \<and> fx < fy"
        unfolding fx by auto
    qed
  qed (auto simp: y_nemp y_sub_N image_mset_subseteq_mono)
qed

lemma image_mset_mono:
  assumes
    mono_f: "\<forall>x \<in> set_mset M. \<forall>y \<in> set_mset N. x < y \<longrightarrow> f x < f y" and
    less: "M \<le> N"
  shows "image_mset f M \<le> image_mset f N"
  by (metis eq_iff image_mset_strict_mono less less_imp_le mono_f order.not_eq_order_implies_strict)

lemma mset_lt_single_right_iff[simp]: "M < {#y#} \<longleftrightarrow> (\<forall>x \<in># M. x < y)" for y :: "'a::linorder"
proof (rule iffI)
  assume M_lt_y: "M < {#y#}"
  show "\<forall>x \<in># M. x < y"
  proof
    fix x
    assume x_in: "x \<in># M"
    hence M: "M - {#x#} + {#x#} = M"
      by (meson insert_DiffM2)
    hence "\<not> {#x#} < {#y#} \<Longrightarrow> x < y"
      using x_in M_lt_y
      by (metis diff_single_eq_union le_multiset_empty_left less_add_same_cancel2 mset_le_trans)
    also have "\<not> {#y#} < M"
      using M_lt_y mset_le_not_sym by blast
    ultimately show "x < y"
      by (metis (no_types) Max_ge all_lt_Max_imp_lt_mset empty_iff finite_set_mset insertE
        less_le_trans linorder_less_linear mset_le_not_sym set_mset_add_mset_insert
        set_mset_eq_empty_iff x_in)
  qed
next
  assume y_max: "\<forall>x \<in># M. x < y"
  show "M < {#y#}"
    by (rule all_lt_Max_imp_lt_mset) (auto intro!: y_max)
qed

lemma mset_le_single_right_iff[simp]:
  "M \<le> {#y#} \<longleftrightarrow> M = {#y#} \<or> (\<forall>x \<in># M. x < y)" for y :: "'a::linorder"
  by (meson less_eq_multiset_def mset_lt_single_right_iff)


subsection \<open>Simprocs\<close>

lemma mset_le_add_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (repeat_mset i u + m \<le> repeat_mset j u + n) = (repeat_mset (i-j) u + m \<le> n)"
proof -
  assume "j \<le> i"
  then have "j + (i - j) = i"
    using le_add_diff_inverse by blast
  then show ?thesis
    by (metis (no_types) add_le_cancel_left left_add_mult_distrib_mset)
qed

lemma mset_le_add_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (repeat_mset i u + m \<le> repeat_mset j u + n) = (m \<le> repeat_mset (j-i) u + n)"
proof -
  assume "i \<le> j"
  then have "i + (j - i) = j"
    using le_add_diff_inverse by blast
  then show ?thesis
    by (metis (no_types) add_le_cancel_left left_add_mult_distrib_mset)
qed

simproc_setup msetless_cancel
  ("(l::'a::preorder multiset) + m < n" | "(l::'a multiset) < m + n" |
   "add_mset a m < n" | "m < add_mset a n" |
   "replicate_mset p a < n" | "m < replicate_mset p a" |
   "repeat_mset p m < n" | "m < repeat_mset p n") =
  \<open>fn phi => Cancel_Simprocs.less_cancel\<close>

simproc_setup msetle_cancel
  ("(l::'a::preorder multiset) + m \<le> n" | "(l::'a multiset) \<le> m + n" |
   "add_mset a m \<le> n" | "m \<le> add_mset a n" |
   "replicate_mset p a \<le> n" | "m \<le> replicate_mset p a" |
   "repeat_mset p m \<le> n" | "m \<le> repeat_mset p n") =
  \<open>fn phi => Cancel_Simprocs.less_eq_cancel\<close>


subsection \<open>Additional facts and instantiations\<close>

lemma ex_gt_count_imp_le_multiset:
  "(\<forall>y :: 'a :: order. y \<in># M + N \<longrightarrow> y \<le> x) \<Longrightarrow> count M x < count N x \<Longrightarrow> M < N"
  unfolding less_multiset\<^sub>H\<^sub>O
  by (metis count_greater_zero_iff le_imp_less_or_eq less_imp_not_less not_gr_zero union_iff)

lemma mset_lt_single_iff[iff]: "{#x#} < {#y#} \<longleftrightarrow> x < y"
  unfolding less_multiset\<^sub>H\<^sub>O by simp

lemma mset_le_single_iff[iff]: "{#x#} \<le> {#y#} \<longleftrightarrow> x \<le> y" for x y :: "'a::order"
  unfolding less_eq_multiset\<^sub>H\<^sub>O by force

instance multiset :: (linorder) linordered_cancel_ab_semigroup_add
  by standard (metis less_eq_multiset\<^sub>H\<^sub>O not_less_iff_gr_or_eq)

lemma less_eq_multiset_total:
  fixes M N :: "'a :: linorder multiset"
  shows "\<not> M \<le> N \<Longrightarrow> N \<le> M"
  by simp

instantiation multiset :: (wellorder) wellorder
begin

lemma wf_less_multiset: "wf {(M :: 'a multiset, N). M < N}"
  unfolding less_multiset_def by (auto intro: wf_mult wf)

instance by standard (metis less_multiset_def wf wf_def wf_mult)

end

instantiation multiset :: (preorder) order_bot
begin

definition bot_multiset :: "'a multiset" where "bot_multiset = {#}"

instance by standard (simp add: bot_multiset_def)

end

instance multiset :: (preorder) no_top
proof standard
  fix x :: "'a multiset"
  obtain a :: 'a where True by simp
  have "x < x + (x + {#a#})"
    by simp
  then show "\<exists>y. x < y"
    by blast
qed

instance multiset :: (preorder) ordered_cancel_comm_monoid_add
  by standard

instantiation multiset :: (linorder) distrib_lattice
begin

definition inf_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "inf_multiset A B = (if A < B then A else B)"

definition sup_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "sup_multiset A B = (if B > A then B else A)"

instance
  by intro_classes (auto simp: inf_multiset_def sup_multiset_def)

end

end
