(*  Title:      HOL/Set_Interval.thy
    Author:     Tobias Nipkow, Clemens Ballarin, Jeremy Avigad

lessThan, greaterThan, atLeast, atMost and two-sided intervals

Modern convention: Ixy stands for an interval where x and y
describe the lower and upper bound and x,y : {c,o,i}
where c = closed, o = open, i = infinite.
Examples: Ico = {_ ..< _} and Ici = {_ ..}
*)

section \<open>Set intervals\<close>

theory Set_Interval
imports Divides
begin

(* Belongs in Finite_Set but 2 is not available there *)
lemma card_2_iff: "card S = 2 \<longleftrightarrow> (\<exists>x y. S = {x,y} \<and> x \<noteq> y)"
  by (auto simp: card_Suc_eq numeral_eq_Suc)

lemma card_2_iff': "card S = 2 \<longleftrightarrow> (\<exists>x\<in>S. \<exists>y\<in>S. x \<noteq> y \<and> (\<forall>z\<in>S. z = x \<or> z = y))"
  by (auto simp: card_Suc_eq numeral_eq_Suc)

context ord
begin

definition
  lessThan    :: "'a => 'a set" ("(1{..<_})") where
  "{..<u} == {x. x < u}"

definition
  atMost      :: "'a => 'a set" ("(1{.._})") where
  "{..u} == {x. x \<le> u}"

definition
  greaterThan :: "'a => 'a set" ("(1{_<..})") where
  "{l<..} == {x. l<x}"

definition
  atLeast     :: "'a => 'a set" ("(1{_..})") where
  "{l..} == {x. l\<le>x}"

definition
  greaterThanLessThan :: "'a => 'a => 'a set"  ("(1{_<..<_})") where
  "{l<..<u} == {l<..} Int {..<u}"

definition
  atLeastLessThan :: "'a => 'a => 'a set"      ("(1{_..<_})") where
  "{l..<u} == {l..} Int {..<u}"

definition
  greaterThanAtMost :: "'a => 'a => 'a set"    ("(1{_<.._})") where
  "{l<..u} == {l<..} Int {..u}"

definition
  atLeastAtMost :: "'a => 'a => 'a set"        ("(1{_.._})") where
  "{l..u} == {l..} Int {..u}"

end


text\<open>A note of warning when using \<^term>\<open>{..<n}\<close> on type \<^typ>\<open>nat\<close>: it is equivalent to \<^term>\<open>{0::nat..<n}\<close> but some lemmas involving
\<^term>\<open>{m..<n}\<close> may not exist in \<^term>\<open>{..<n}\<close>-form as well.\<close>

syntax (ASCII)
  "_UNION_le"   :: "'a => 'a => 'b set => 'b set"       ("(3UN _<=_./ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3UN _<_./ _)" [0, 0, 10] 10)
  "_INTER_le"   :: "'a => 'a => 'b set => 'b set"       ("(3INT _<=_./ _)" [0, 0, 10] 10)
  "_INTER_less" :: "'a => 'a => 'b set => 'b set"       ("(3INT _<_./ _)" [0, 0, 10] 10)

syntax (latex output)
  "_UNION_le"   :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Union>(\<open>unbreakable\<close>_ \<le> _)/ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Union>(\<open>unbreakable\<close>_ < _)/ _)" [0, 0, 10] 10)
  "_INTER_le"   :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Inter>(\<open>unbreakable\<close>_ \<le> _)/ _)" [0, 0, 10] 10)
  "_INTER_less" :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Inter>(\<open>unbreakable\<close>_ < _)/ _)" [0, 0, 10] 10)

syntax
  "_UNION_le"   :: "'a => 'a => 'b set => 'b set"       ("(3\<Union>_\<le>_./ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Union>_<_./ _)" [0, 0, 10] 10)
  "_INTER_le"   :: "'a => 'a => 'b set => 'b set"       ("(3\<Inter>_\<le>_./ _)" [0, 0, 10] 10)
  "_INTER_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Inter>_<_./ _)" [0, 0, 10] 10)

translations
  "\<Union>i\<le>n. A" \<rightleftharpoons> "\<Union>i\<in>{..n}. A"
  "\<Union>i<n. A" \<rightleftharpoons> "\<Union>i\<in>{..<n}. A"
  "\<Inter>i\<le>n. A" \<rightleftharpoons> "\<Inter>i\<in>{..n}. A"
  "\<Inter>i<n. A" \<rightleftharpoons> "\<Inter>i\<in>{..<n}. A"


subsection \<open>Various equivalences\<close>

lemma (in ord) lessThan_iff [iff]: "(i \<in> lessThan k) = (i<k)"
by (simp add: lessThan_def)

lemma Compl_lessThan [simp]:
    "!!k:: 'a::linorder. -lessThan k = atLeast k"
  by (auto simp add: lessThan_def atLeast_def)

lemma single_Diff_lessThan [simp]: "!!k:: 'a::preorder. {k} - lessThan k = {k}"
  by auto

lemma (in ord) greaterThan_iff [iff]: "(i \<in> greaterThan k) = (k<i)"
  by (simp add: greaterThan_def)

lemma Compl_greaterThan [simp]:
    "!!k:: 'a::linorder. -greaterThan k = atMost k"
  by (auto simp add: greaterThan_def atMost_def)

lemma Compl_atMost [simp]: "!!k:: 'a::linorder. -atMost k = greaterThan k"
  apply (subst Compl_greaterThan [symmetric])
  apply (rule double_complement)
  done

lemma (in ord) atLeast_iff [iff]: "(i \<in> atLeast k) = (k<=i)"
by (simp add: atLeast_def)

lemma Compl_atLeast [simp]: "!!k:: 'a::linorder. -atLeast k = lessThan k"
  by (auto simp add: lessThan_def atLeast_def)

lemma (in ord) atMost_iff [iff]: "(i \<in> atMost k) = (i<=k)"
by (simp add: atMost_def)

lemma atMost_Int_atLeast: "!!n:: 'a::order. atMost n Int atLeast n = {n}"
by (blast intro: order_antisym)

lemma (in linorder) lessThan_Int_lessThan: "{ a <..} \<inter> { b <..} = { max a b <..}"
  by auto

lemma (in linorder) greaterThan_Int_greaterThan: "{..< a} \<inter> {..< b} = {..< min a b}"
  by auto

subsection \<open>Logical Equivalences for Set Inclusion and Equality\<close>

lemma atLeast_empty_triv [simp]: "{{}..} = UNIV"
  by auto

lemma atMost_UNIV_triv [simp]: "{..UNIV} = UNIV"
  by auto

lemma atLeast_subset_iff [iff]:
     "(atLeast x \<subseteq> atLeast y) = (y \<le> (x::'a::preorder))"
by (blast intro: order_trans)

lemma atLeast_eq_iff [iff]:
     "(atLeast x = atLeast y) = (x = (y::'a::order))"
by (blast intro: order_antisym order_trans)

lemma greaterThan_subset_iff [iff]:
     "(greaterThan x \<subseteq> greaterThan y) = (y \<le> (x::'a::linorder))"
  unfolding greaterThan_def by (auto simp: linorder_not_less [symmetric])

lemma greaterThan_eq_iff [iff]:
     "(greaterThan x = greaterThan y) = (x = (y::'a::linorder))"
  by (auto simp: elim!: equalityE)

lemma atMost_subset_iff [iff]: "(atMost x \<subseteq> atMost y) = (x \<le> (y::'a::preorder))"
  by (blast intro: order_trans)

lemma atMost_eq_iff [iff]: "(atMost x = atMost y) = (x = (y::'a::order))"
  by (blast intro: order_antisym order_trans)

lemma lessThan_subset_iff [iff]:
     "(lessThan x \<subseteq> lessThan y) = (x \<le> (y::'a::linorder))"
  unfolding lessThan_def by (auto simp: linorder_not_less [symmetric])

lemma lessThan_eq_iff [iff]:
     "(lessThan x = lessThan y) = (x = (y::'a::linorder))"
  by (auto simp: elim!: equalityE)

lemma lessThan_strict_subset_iff:
  fixes m n :: "'a::linorder"
  shows "{..<m} < {..<n} \<longleftrightarrow> m < n"
  by (metis leD lessThan_subset_iff linorder_linear not_less_iff_gr_or_eq psubset_eq)

lemma (in linorder) Ici_subset_Ioi_iff: "{a ..} \<subseteq> {b <..} \<longleftrightarrow> b < a"
  by auto

lemma (in linorder) Iic_subset_Iio_iff: "{.. a} \<subseteq> {..< b} \<longleftrightarrow> a < b"
  by auto

lemma (in preorder) Ioi_le_Ico: "{a <..} \<subseteq> {a ..}"
  by (auto intro: less_imp_le)

subsection \<open>Two-sided intervals\<close>

context ord
begin

lemma greaterThanLessThan_iff [simp]: "(i \<in> {l<..<u}) = (l < i \<and> i < u)"
  by (simp add: greaterThanLessThan_def)

lemma atLeastLessThan_iff [simp]: "(i \<in> {l..<u}) = (l \<le> i \<and> i < u)"
  by (simp add: atLeastLessThan_def)

lemma greaterThanAtMost_iff [simp]: "(i \<in> {l<..u}) = (l < i \<and> i \<le> u)"
  by (simp add: greaterThanAtMost_def)

lemma atLeastAtMost_iff [simp]: "(i \<in> {l..u}) = (l \<le> i \<and> i \<le> u)"
  by (simp add: atLeastAtMost_def)

text \<open>The above four lemmas could be declared as iffs. Unfortunately this
breaks many proofs. Since it only helps blast, it is better to leave them
alone.\<close>

lemma greaterThanLessThan_eq: "{ a <..< b} = { a <..} \<inter> {..< b }"
  by auto

lemma (in order) atLeastLessThan_eq_atLeastAtMost_diff:
  "{a..<b} = {a..b} - {b}"
  by (auto simp add: atLeastLessThan_def atLeastAtMost_def)

lemma (in order) greaterThanAtMost_eq_atLeastAtMost_diff:
  "{a<..b} = {a..b} - {a}"
  by (auto simp add: greaterThanAtMost_def atLeastAtMost_def)

end

subsubsection\<open>Emptyness, singletons, subset\<close>

context preorder
begin

lemma atLeastatMost_empty_iff[simp]:
  "{a..b} = {} \<longleftrightarrow> (\<not> a \<le> b)"
  by auto (blast intro: order_trans)

lemma atLeastatMost_empty_iff2[simp]:
  "{} = {a..b} \<longleftrightarrow> (\<not> a \<le> b)"
  by auto (blast intro: order_trans)

lemma atLeastLessThan_empty_iff[simp]:
  "{a..<b} = {} \<longleftrightarrow> (\<not> a < b)"
  by auto (blast intro: le_less_trans)

lemma atLeastLessThan_empty_iff2[simp]:
  "{} = {a..<b} \<longleftrightarrow> (\<not> a < b)"
  by auto (blast intro: le_less_trans)

lemma greaterThanAtMost_empty_iff[simp]: "{k<..l} = {} \<longleftrightarrow> \<not> k < l"
  by auto (blast intro: less_le_trans)

lemma greaterThanAtMost_empty_iff2[simp]: "{} = {k<..l} \<longleftrightarrow> \<not> k < l"
  by auto (blast intro: less_le_trans)

lemma atLeastatMost_subset_iff[simp]:
  "{a..b} \<le> {c..d} \<longleftrightarrow> (\<not> a \<le> b) \<or> c \<le> a \<and> b \<le> d"
  unfolding atLeastAtMost_def atLeast_def atMost_def
  by (blast intro: order_trans)

lemma atLeastatMost_psubset_iff:
  "{a..b} < {c..d} \<longleftrightarrow>
   ((\<not> a \<le> b) \<or> c \<le> a \<and> b \<le> d \<and> (c < a \<or> b < d)) \<and> c \<le> d"
  by(simp add: psubset_eq set_eq_iff less_le_not_le)(blast intro: order_trans)

lemma atLeastAtMost_subseteq_atLeastLessThan_iff:
  "{a..b} \<subseteq> {c ..< d} \<longleftrightarrow> (a \<le> b \<longrightarrow> c \<le> a \<and> b < d)" 
  by auto (blast intro: local.order_trans local.le_less_trans elim: )+

lemma Icc_subset_Ici_iff[simp]:
  "{l..h} \<subseteq> {l'..} = (\<not> l\<le>h \<or> l\<ge>l')"
  by(auto simp: subset_eq intro: order_trans)

lemma Icc_subset_Iic_iff[simp]:
  "{l..h} \<subseteq> {..h'} = (\<not> l\<le>h \<or> h\<le>h')"
  by(auto simp: subset_eq intro: order_trans)

lemma not_Ici_eq_empty[simp]: "{l..} \<noteq> {}"
  by(auto simp: set_eq_iff)

lemma not_Iic_eq_empty[simp]: "{..h} \<noteq> {}"
  by(auto simp: set_eq_iff)

lemmas not_empty_eq_Ici_eq_empty[simp] = not_Ici_eq_empty[symmetric]
lemmas not_empty_eq_Iic_eq_empty[simp] = not_Iic_eq_empty[symmetric]

end

context order
begin

lemma atLeastatMost_empty[simp]:
  "b < a \<Longrightarrow> {a..b} = {}"
  by(auto simp: atLeastAtMost_def atLeast_def atMost_def)

lemma atLeastLessThan_empty[simp]:
  "b \<le> a \<Longrightarrow> {a..<b} = {}"
  by(auto simp: atLeastLessThan_def)

lemma greaterThanAtMost_empty[simp]: "l \<le> k ==> {k<..l} = {}"
  by(auto simp:greaterThanAtMost_def greaterThan_def atMost_def)

lemma greaterThanLessThan_empty[simp]:"l \<le> k ==> {k<..<l} = {}"
  by(auto simp:greaterThanLessThan_def greaterThan_def lessThan_def)

lemma atLeastAtMost_singleton [simp]: "{a..a} = {a}"
  by (auto simp add: atLeastAtMost_def atMost_def atLeast_def)

lemma atLeastAtMost_singleton': "a = b \<Longrightarrow> {a .. b} = {a}" by simp

lemma Icc_eq_Icc[simp]:
  "{l..h} = {l'..h'} = (l=l' \<and> h=h' \<or> \<not> l\<le>h \<and> \<not> l'\<le>h')"
  by (simp add: order_class.order.eq_iff) (auto intro: order_trans)

lemma atLeastAtMost_singleton_iff[simp]:
  "{a .. b} = {c} \<longleftrightarrow> a = b \<and> b = c"
proof
  assume "{a..b} = {c}"
  hence *: "\<not> (\<not> a \<le> b)" unfolding atLeastatMost_empty_iff[symmetric] by simp
  with \<open>{a..b} = {c}\<close> have "c \<le> a \<and> b \<le> c" by auto
  with * show "a = b \<and> b = c" by auto
qed simp

end

context no_top
begin

(* also holds for no_bot but no_top should suffice *)
lemma not_UNIV_le_Icc[simp]: "\<not> UNIV \<subseteq> {l..h}"
using gt_ex[of h] by(auto simp: subset_eq less_le_not_le)

lemma not_UNIV_le_Iic[simp]: "\<not> UNIV \<subseteq> {..h}"
using gt_ex[of h] by(auto simp: subset_eq less_le_not_le)

lemma not_Ici_le_Icc[simp]: "\<not> {l..} \<subseteq> {l'..h'}"
using gt_ex[of h']
by(auto simp: subset_eq less_le)(blast dest:antisym_conv intro: order_trans)

lemma not_Ici_le_Iic[simp]: "\<not> {l..} \<subseteq> {..h'}"
using gt_ex[of h']
by(auto simp: subset_eq less_le)(blast dest:antisym_conv intro: order_trans)

end

context no_bot
begin

lemma not_UNIV_le_Ici[simp]: "\<not> UNIV \<subseteq> {l..}"
using lt_ex[of l] by(auto simp: subset_eq less_le_not_le)

lemma not_Iic_le_Icc[simp]: "\<not> {..h} \<subseteq> {l'..h'}"
using lt_ex[of l']
by(auto simp: subset_eq less_le)(blast dest:antisym_conv intro: order_trans)

lemma not_Iic_le_Ici[simp]: "\<not> {..h} \<subseteq> {l'..}"
using lt_ex[of l']
by(auto simp: subset_eq less_le)(blast dest:antisym_conv intro: order_trans)

end


context no_top
begin

(* also holds for no_bot but no_top should suffice *)
lemma not_UNIV_eq_Icc[simp]: "\<not> UNIV = {l'..h'}"
using gt_ex[of h'] by(auto simp: set_eq_iff  less_le_not_le)

lemmas not_Icc_eq_UNIV[simp] = not_UNIV_eq_Icc[symmetric]

lemma not_UNIV_eq_Iic[simp]: "\<not> UNIV = {..h'}"
using gt_ex[of h'] by(auto simp: set_eq_iff  less_le_not_le)

lemmas not_Iic_eq_UNIV[simp] = not_UNIV_eq_Iic[symmetric]

lemma not_Icc_eq_Ici[simp]: "\<not> {l..h} = {l'..}"
unfolding atLeastAtMost_def using not_Ici_le_Iic[of l'] by blast

lemmas not_Ici_eq_Icc[simp] = not_Icc_eq_Ici[symmetric]

(* also holds for no_bot but no_top should suffice *)
lemma not_Iic_eq_Ici[simp]: "\<not> {..h} = {l'..}"
using not_Ici_le_Iic[of l' h] by blast

lemmas not_Ici_eq_Iic[simp] = not_Iic_eq_Ici[symmetric]

end

context no_bot
begin

lemma not_UNIV_eq_Ici[simp]: "\<not> UNIV = {l'..}"
using lt_ex[of l'] by(auto simp: set_eq_iff  less_le_not_le)

lemmas not_Ici_eq_UNIV[simp] = not_UNIV_eq_Ici[symmetric]

lemma not_Icc_eq_Iic[simp]: "\<not> {l..h} = {..h'}"
unfolding atLeastAtMost_def using not_Iic_le_Ici[of h'] by blast

lemmas not_Iic_eq_Icc[simp] = not_Icc_eq_Iic[symmetric]

end


context dense_linorder
begin

lemma greaterThanLessThan_empty_iff[simp]:
  "{ a <..< b } = {} \<longleftrightarrow> b \<le> a"
  using dense[of a b] by (cases "a < b") auto

lemma greaterThanLessThan_empty_iff2[simp]:
  "{} = { a <..< b } \<longleftrightarrow> b \<le> a"
  using dense[of a b] by (cases "a < b") auto

lemma atLeastLessThan_subseteq_atLeastAtMost_iff:
  "{a ..< b} \<subseteq> { c .. d } \<longleftrightarrow> (a < b \<longrightarrow> c \<le> a \<and> b \<le> d)"
  using dense[of "max a d" "b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

lemma greaterThanAtMost_subseteq_atLeastAtMost_iff:
  "{a <.. b} \<subseteq> { c .. d } \<longleftrightarrow> (a < b \<longrightarrow> c \<le> a \<and> b \<le> d)"
  using dense[of "a" "min c b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

lemma greaterThanLessThan_subseteq_atLeastAtMost_iff:
  "{a <..< b} \<subseteq> { c .. d } \<longleftrightarrow> (a < b \<longrightarrow> c \<le> a \<and> b \<le> d)"
  using dense[of "a" "min c b"] dense[of "max a d" "b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

lemma greaterThanLessThan_subseteq_greaterThanLessThan:
  "{a <..< b} \<subseteq> {c <..< d} \<longleftrightarrow> (a < b \<longrightarrow> a \<ge> c \<and> b \<le> d)"
  using dense[of "a" "min c b"] dense[of "max a d" "b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

lemma greaterThanAtMost_subseteq_atLeastLessThan_iff:
  "{a <.. b} \<subseteq> { c ..< d } \<longleftrightarrow> (a < b \<longrightarrow> c \<le> a \<and> b < d)"
  using dense[of "a" "min c b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

lemma greaterThanLessThan_subseteq_atLeastLessThan_iff:
  "{a <..< b} \<subseteq> { c ..< d } \<longleftrightarrow> (a < b \<longrightarrow> c \<le> a \<and> b \<le> d)"
  using dense[of "a" "min c b"] dense[of "max a d" "b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

lemma greaterThanLessThan_subseteq_greaterThanAtMost_iff:
  "{a <..< b} \<subseteq> { c <.. d } \<longleftrightarrow> (a < b \<longrightarrow> c \<le> a \<and> b \<le> d)"
  using dense[of "a" "min c b"] dense[of "max a d" "b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])

end

context no_top
begin

lemma greaterThan_non_empty[simp]: "{x <..} \<noteq> {}"
  using gt_ex[of x] by auto

end

context no_bot
begin

lemma lessThan_non_empty[simp]: "{..< x} \<noteq> {}"
  using lt_ex[of x] by auto

end

lemma (in linorder) atLeastLessThan_subset_iff:
  "{a..<b} \<subseteq> {c..<d} \<Longrightarrow> b \<le> a \<or> c\<le>a \<and> b\<le>d"
  apply (auto simp:subset_eq Ball_def not_le)
  apply(frule_tac x=a in spec)
  apply(erule_tac x=d in allE)
  apply (auto simp: )
  done

lemma atLeastLessThan_inj:
  fixes a b c d :: "'a::linorder"
  assumes eq: "{a ..< b} = {c ..< d}" and "a < b" "c < d"
  shows "a = c" "b = d"
using assms by (metis atLeastLessThan_subset_iff eq less_le_not_le antisym_conv2 subset_refl)+

lemma atLeastLessThan_eq_iff:
  fixes a b c d :: "'a::linorder"
  assumes "a < b" "c < d"
  shows "{a ..< b} = {c ..< d} \<longleftrightarrow> a = c \<and> b = d"
  using atLeastLessThan_inj assms by auto

lemma (in linorder) Ioc_inj: 
  \<open>{a <.. b} = {c <.. d} \<longleftrightarrow> (b \<le> a \<and> d \<le> c) \<or> a = c \<and> b = d\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?Q
  then show ?P
    by auto
next
  assume ?P
  then have \<open>a < x \<and> x \<le> b \<longleftrightarrow> c < x \<and> x \<le> d\<close> for x
    by (simp add: set_eq_iff)
  from this [of a] this [of b] this [of c] this [of d] show ?Q
    by auto
qed

lemma (in order) Iio_Int_singleton: "{..<k} \<inter> {x} = (if x < k then {x} else {})"
  by auto

lemma (in linorder) Ioc_subset_iff: "{a<..b} \<subseteq> {c<..d} \<longleftrightarrow> (b \<le> a \<or> c \<le> a \<and> b \<le> d)"
  by (auto simp: subset_eq Ball_def) (metis less_le not_less)

lemma (in order_bot) atLeast_eq_UNIV_iff: "{x..} = UNIV \<longleftrightarrow> x = bot"
by (auto simp: set_eq_iff intro: le_bot)

lemma (in order_top) atMost_eq_UNIV_iff: "{..x} = UNIV \<longleftrightarrow> x = top"
by (auto simp: set_eq_iff intro: top_le)

lemma (in bounded_lattice) atLeastAtMost_eq_UNIV_iff:
  "{x..y} = UNIV \<longleftrightarrow> (x = bot \<and> y = top)"
by (auto simp: set_eq_iff intro: top_le le_bot)

lemma Iio_eq_empty_iff: "{..< n::'a::{linorder, order_bot}} = {} \<longleftrightarrow> n = bot"
  by (auto simp: set_eq_iff not_less le_bot)

lemma lessThan_empty_iff: "{..< n::nat} = {} \<longleftrightarrow> n = 0"
  by (simp add: Iio_eq_empty_iff bot_nat_def)

lemma mono_image_least:
  assumes f_mono: "mono f" and f_img: "f ` {m ..< n} = {m' ..< n'}" "m < n"
  shows "f m = m'"
proof -
  from f_img have "{m' ..< n'} \<noteq> {}"
    by (metis atLeastLessThan_empty_iff image_is_empty)
  with f_img have "m' \<in> f ` {m ..< n}" by auto
  then obtain k where "f k = m'" "m \<le> k" by auto
  moreover have "m' \<le> f m" using f_img by auto
  ultimately show "f m = m'"
    using f_mono by (auto elim: monoE[where x=m and y=k])
qed


subsection \<open>Infinite intervals\<close>

context dense_linorder
begin

lemma infinite_Ioo:
  assumes "a < b"
  shows "\<not> finite {a<..<b}"
proof
  assume fin: "finite {a<..<b}"
  moreover have ne: "{a<..<b} \<noteq> {}"
    using \<open>a < b\<close> by auto
  ultimately have "a < Max {a <..< b}" "Max {a <..< b} < b"
    using Max_in[of "{a <..< b}"] by auto
  then obtain x where "Max {a <..< b} < x" "x < b"
    using dense[of "Max {a<..<b}" b] by auto
  then have "x \<in> {a <..< b}"
    using \<open>a < Max {a <..< b}\<close> by auto
  then have "x \<le> Max {a <..< b}"
    using fin by auto
  with \<open>Max {a <..< b} < x\<close> show False by auto
qed

lemma infinite_Icc: "a < b \<Longrightarrow> \<not> finite {a .. b}"
  using greaterThanLessThan_subseteq_atLeastAtMost_iff[of a b a b] infinite_Ioo[of a b]
  by (auto dest: finite_subset)

lemma infinite_Ico: "a < b \<Longrightarrow> \<not> finite {a ..< b}"
  using greaterThanLessThan_subseteq_atLeastLessThan_iff[of a b a b] infinite_Ioo[of a b]
  by (auto dest: finite_subset)

lemma infinite_Ioc: "a < b \<Longrightarrow> \<not> finite {a <.. b}"
  using greaterThanLessThan_subseteq_greaterThanAtMost_iff[of a b a b] infinite_Ioo[of a b]
  by (auto dest: finite_subset)

lemma infinite_Ioo_iff [simp]: "infinite {a<..<b} \<longleftrightarrow> a < b"
  using not_less_iff_gr_or_eq by (fastforce simp: infinite_Ioo)

lemma infinite_Icc_iff [simp]: "infinite {a .. b} \<longleftrightarrow> a < b"
  using not_less_iff_gr_or_eq by (fastforce simp: infinite_Icc)

lemma infinite_Ico_iff [simp]: "infinite {a..<b} \<longleftrightarrow> a < b"
  using not_less_iff_gr_or_eq by (fastforce simp: infinite_Ico)

lemma infinite_Ioc_iff [simp]: "infinite {a<..b} \<longleftrightarrow> a < b"
  using not_less_iff_gr_or_eq by (fastforce simp: infinite_Ioc)

end

lemma infinite_Iio: "\<not> finite {..< a :: 'a :: {no_bot, linorder}}"
proof
  assume "finite {..< a}"
  then have *: "\<And>x. x < a \<Longrightarrow> Min {..< a} \<le> x"
    by auto
  obtain x where "x < a"
    using lt_ex by auto

  obtain y where "y < Min {..< a}"
    using lt_ex by auto
  also have "Min {..< a} \<le> x"
    using \<open>x < a\<close> by fact
  also note \<open>x < a\<close>
  finally have "Min {..< a} \<le> y"
    by fact
  with \<open>y < Min {..< a}\<close> show False by auto
qed

lemma infinite_Iic: "\<not> finite {.. a :: 'a :: {no_bot, linorder}}"
  using infinite_Iio[of a] finite_subset[of "{..< a}" "{.. a}"]
  by (auto simp: subset_eq less_imp_le)

lemma infinite_Ioi: "\<not> finite {a :: 'a :: {no_top, linorder} <..}"
proof
  assume "finite {a <..}"
  then have *: "\<And>x. a < x \<Longrightarrow> x \<le> Max {a <..}"
    by auto

  obtain y where "Max {a <..} < y"
    using gt_ex by auto

  obtain x where x: "a < x"
    using gt_ex by auto
  also from x have "x \<le> Max {a <..}"
    by fact
  also note \<open>Max {a <..} < y\<close>
  finally have "y \<le> Max { a <..}"
    by fact
  with \<open>Max {a <..} < y\<close> show False by auto
qed

lemma infinite_Ici: "\<not> finite {a :: 'a :: {no_top, linorder} ..}"
  using infinite_Ioi[of a] finite_subset[of "{a <..}" "{a ..}"]
  by (auto simp: subset_eq less_imp_le)

subsubsection \<open>Intersection\<close>

context linorder
begin

lemma Int_atLeastAtMost[simp]: "{a..b} Int {c..d} = {max a c .. min b d}"
by auto

lemma Int_atLeastAtMostR1[simp]: "{..b} Int {c..d} = {c .. min b d}"
by auto

lemma Int_atLeastAtMostR2[simp]: "{a..} Int {c..d} = {max a c .. d}"
by auto

lemma Int_atLeastAtMostL1[simp]: "{a..b} Int {..d} = {a .. min b d}"
by auto

lemma Int_atLeastAtMostL2[simp]: "{a..b} Int {c..} = {max a c .. b}"
by auto

lemma Int_atLeastLessThan[simp]: "{a..<b} Int {c..<d} = {max a c ..< min b d}"
by auto

lemma Int_greaterThanAtMost[simp]: "{a<..b} Int {c<..d} = {max a c <.. min b d}"
by auto

lemma Int_greaterThanLessThan[simp]: "{a<..<b} Int {c<..<d} = {max a c <..< min b d}"
by auto

lemma Int_atMost[simp]: "{..a} \<inter> {..b} = {.. min a b}"
  by (auto simp: min_def)

lemma Ioc_disjoint: "{a<..b} \<inter> {c<..d} = {} \<longleftrightarrow> b \<le> a \<or> d \<le> c \<or> b \<le> c \<or> d \<le> a"
  by auto

end

context complete_lattice
begin

lemma
  shows Sup_atLeast[simp]: "Sup {x ..} = top"
    and Sup_greaterThanAtLeast[simp]: "x < top \<Longrightarrow> Sup {x <..} = top"
    and Sup_atMost[simp]: "Sup {.. y} = y"
    and Sup_atLeastAtMost[simp]: "x \<le> y \<Longrightarrow> Sup { x .. y} = y"
    and Sup_greaterThanAtMost[simp]: "x < y \<Longrightarrow> Sup { x <.. y} = y"
  by (auto intro!: Sup_eqI)

lemma
  shows Inf_atMost[simp]: "Inf {.. x} = bot"
    and Inf_atMostLessThan[simp]: "top < x \<Longrightarrow> Inf {..< x} = bot"
    and Inf_atLeast[simp]: "Inf {x ..} = x"
    and Inf_atLeastAtMost[simp]: "x \<le> y \<Longrightarrow> Inf { x .. y} = x"
    and Inf_atLeastLessThan[simp]: "x < y \<Longrightarrow> Inf { x ..< y} = x"
  by (auto intro!: Inf_eqI)

end

lemma
  fixes x y :: "'a :: {complete_lattice, dense_linorder}"
  shows Sup_lessThan[simp]: "Sup {..< y} = y"
    and Sup_atLeastLessThan[simp]: "x < y \<Longrightarrow> Sup { x ..< y} = y"
    and Sup_greaterThanLessThan[simp]: "x < y \<Longrightarrow> Sup { x <..< y} = y"
    and Inf_greaterThan[simp]: "Inf {x <..} = x"
    and Inf_greaterThanAtMost[simp]: "x < y \<Longrightarrow> Inf { x <.. y} = x"
    and Inf_greaterThanLessThan[simp]: "x < y \<Longrightarrow> Inf { x <..< y} = x"
  by (auto intro!: Inf_eqI Sup_eqI intro: dense_le dense_le_bounded dense_ge dense_ge_bounded)

subsection \<open>Intervals of natural numbers\<close>

subsubsection \<open>The Constant \<^term>\<open>lessThan\<close>\<close>

lemma lessThan_0 [simp]: "lessThan (0::nat) = {}"
by (simp add: lessThan_def)

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
by (simp add: lessThan_def less_Suc_eq, blast)

text \<open>The following proof is convenient in induction proofs where
new elements get indices at the beginning. So it is used to transform
\<^term>\<open>{..<Suc n}\<close> to \<^term>\<open>0::nat\<close> and \<^term>\<open>{..< n}\<close>.\<close>

lemma zero_notin_Suc_image [simp]: "0 \<notin> Suc ` A"
  by auto

lemma lessThan_Suc_eq_insert_0: "{..<Suc n} = insert 0 (Suc ` {..<n})"
  by (auto simp: image_iff less_Suc_eq_0_disj)

lemma lessThan_Suc_atMost: "lessThan (Suc k) = atMost k"
by (simp add: lessThan_def atMost_def less_Suc_eq_le)

lemma atMost_Suc_eq_insert_0: "{.. Suc n} = insert 0 (Suc ` {.. n})"
  unfolding lessThan_Suc_atMost[symmetric] lessThan_Suc_eq_insert_0[of "Suc n"] ..

lemma UN_lessThan_UNIV: "(\<Union>m::nat. lessThan m) = UNIV"
by blast

subsubsection \<open>The Constant \<^term>\<open>greaterThan\<close>\<close>

lemma greaterThan_0: "greaterThan 0 = range Suc"
  unfolding greaterThan_def
  by (blast dest: gr0_conv_Suc [THEN iffD1])

lemma greaterThan_Suc: "greaterThan (Suc k) = greaterThan k - {Suc k}"
  unfolding greaterThan_def
  by (auto elim: linorder_neqE)

lemma INT_greaterThan_UNIV: "(\<Inter>m::nat. greaterThan m) = {}"
  by blast

subsubsection \<open>The Constant \<^term>\<open>atLeast\<close>\<close>

lemma atLeast_0 [simp]: "atLeast (0::nat) = UNIV"
by (unfold atLeast_def UNIV_def, simp)

lemma atLeast_Suc: "atLeast (Suc k) = atLeast k - {k}"
  unfolding atLeast_def by (auto simp: order_le_less Suc_le_eq)

lemma atLeast_Suc_greaterThan: "atLeast (Suc k) = greaterThan k"
  by (auto simp add: greaterThan_def atLeast_def less_Suc_eq_le)

lemma UN_atLeast_UNIV: "(\<Union>m::nat. atLeast m) = UNIV"
  by blast

subsubsection \<open>The Constant \<^term>\<open>atMost\<close>\<close>

lemma atMost_0 [simp]: "atMost (0::nat) = {0}"
  by (simp add: atMost_def)

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
  unfolding atMost_def by (auto simp add: less_Suc_eq order_le_less)

lemma UN_atMost_UNIV: "(\<Union>m::nat. atMost m) = UNIV"
  by blast

subsubsection \<open>The Constant \<^term>\<open>atLeastLessThan\<close>\<close>

text\<open>The orientation of the following 2 rules is tricky. The lhs is
defined in terms of the rhs.  Hence the chosen orientation makes sense
in this theory --- the reverse orientation complicates proofs (eg
nontermination). But outside, when the definition of the lhs is rarely
used, the opposite orientation seems preferable because it reduces a
specific concept to a more general one.\<close>

lemma atLeast0LessThan [code_abbrev]: "{0::nat..<n} = {..<n}"
  by(simp add:lessThan_def atLeastLessThan_def)

lemma atLeast0AtMost [code_abbrev]: "{0..n::nat} = {..n}"
  by(simp add:atMost_def atLeastAtMost_def)

lemma lessThan_atLeast0: "{..<n} = {0::nat..<n}"
  by (simp add: atLeast0LessThan)

lemma atMost_atLeast0: "{..n} = {0::nat..n}"
  by (simp add: atLeast0AtMost)

lemma atLeastLessThan0: "{m..<0::nat} = {}"
  by (simp add: atLeastLessThan_def)

lemma atLeast0_lessThan_Suc: "{0..<Suc n} = insert n {0..<n}"
  by (simp add: atLeast0LessThan lessThan_Suc)

lemma atLeast0_lessThan_Suc_eq_insert_0: "{0..<Suc n} = insert 0 (Suc ` {0..<n})"
  by (simp add: atLeast0LessThan lessThan_Suc_eq_insert_0)


subsubsection \<open>The Constant \<^term>\<open>atLeastAtMost\<close>\<close>

lemma Icc_eq_insert_lb_nat: "m \<le> n \<Longrightarrow> {m..n} = insert m {Suc m..n}"
by auto

lemma atLeast0_atMost_Suc:
  "{0..Suc n} = insert (Suc n) {0..n}"
  by (simp add: atLeast0AtMost atMost_Suc)

lemma atLeast0_atMost_Suc_eq_insert_0:
  "{0..Suc n} = insert 0 (Suc ` {0..n})"
  by (simp add: atLeast0AtMost atMost_Suc_eq_insert_0)


subsubsection \<open>Intervals of nats with \<^term>\<open>Suc\<close>\<close>

text\<open>Not a simprule because the RHS is too messy.\<close>
lemma atLeastLessThanSuc:
    "{m..<Suc n} = (if m \<le> n then insert n {m..<n} else {})"
by (auto simp add: atLeastLessThan_def)

lemma atLeastLessThan_singleton [simp]: "{m..<Suc m} = {m}"
by (auto simp add: atLeastLessThan_def)

lemma atLeastLessThanSuc_atLeastAtMost: "{l..<Suc u} = {l..u}"
  by (simp add: lessThan_Suc_atMost atLeastAtMost_def atLeastLessThan_def)

lemma atLeastSucAtMost_greaterThanAtMost: "{Suc l..u} = {l<..u}"
  by (simp add: atLeast_Suc_greaterThan atLeastAtMost_def
      greaterThanAtMost_def)

lemma atLeastSucLessThan_greaterThanLessThan: "{Suc l..<u} = {l<..<u}"
  by (simp add: atLeast_Suc_greaterThan atLeastLessThan_def
    greaterThanLessThan_def)

lemma atLeastAtMostSuc_conv: "m \<le> Suc n \<Longrightarrow> {m..Suc n} = insert (Suc n) {m..n}"
  by auto

lemma atLeastAtMost_insertL: "m \<le> n \<Longrightarrow> insert m {Suc m..n} = {m ..n}"
  by auto

text \<open>The analogous result is useful on \<^typ>\<open>int\<close>:\<close>
(* here, because we don't have an own int section *)
lemma atLeastAtMostPlus1_int_conv:
  "m \<le> 1+n \<Longrightarrow> {m..1+n} = insert (1+n) {m..n::int}"
  by (auto intro: set_eqI)

lemma atLeastLessThan_add_Un: "i \<le> j \<Longrightarrow> {i..<j+k} = {i..<j} \<union> {j..<j+k::nat}"
  by (induct k) (simp_all add: atLeastLessThanSuc)


subsubsection \<open>Intervals and numerals\<close>

lemma lessThan_nat_numeral:  \<comment> \<open>Evaluation for specific numerals\<close>
  "lessThan (numeral k :: nat) = insert (pred_numeral k) (lessThan (pred_numeral k))"
  by (simp add: numeral_eq_Suc lessThan_Suc)

lemma atMost_nat_numeral:  \<comment> \<open>Evaluation for specific numerals\<close>
  "atMost (numeral k :: nat) = insert (numeral k) (atMost (pred_numeral k))"
  by (simp add: numeral_eq_Suc atMost_Suc)

lemma atLeastLessThan_nat_numeral:  \<comment> \<open>Evaluation for specific numerals\<close>
  "atLeastLessThan m (numeral k :: nat) =
     (if m \<le> (pred_numeral k) then insert (pred_numeral k) (atLeastLessThan m (pred_numeral k))
                 else {})"
  by (simp add: numeral_eq_Suc atLeastLessThanSuc)


subsubsection \<open>Image\<close>

context linordered_semidom
begin

lemma image_add_atLeast[simp]: "plus k ` {i..} = {k + i..}"
proof -
  have "n = k + (n - k)" if "i + k \<le> n" for n
  proof -
    have "n = (n - (k + i)) + (k + i)" using that
      by (metis add_commute le_add_diff_inverse)
    then show "n = k + (n - k)"
      by (metis local.add_diff_cancel_left' add_assoc add_commute)
  qed
  then show ?thesis
    by (fastforce simp: add_le_imp_le_diff add.commute)
qed

lemma image_add_atLeastAtMost [simp]:
  "plus k ` {i..j} = {i + k..j + k}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    by (auto simp add: ac_simps)
next
  show "?B \<subseteq> ?A"
  proof
    fix n
    assume "n \<in> ?B"
    then have "i \<le> n - k"
      by (simp add: add_le_imp_le_diff)
    have "n = n - k + k"
    proof -
      from \<open>n \<in> ?B\<close> have "n = n - (i + k) + (i + k)"
        by simp
      also have "\<dots> = n - k - i + i + k"
        by (simp add: algebra_simps)
      also have "\<dots> = n - k + k"
        using \<open>i \<le> n - k\<close> by simp
      finally show ?thesis .
    qed
    moreover have "n - k \<in> {i..j}"
      using \<open>n \<in> ?B\<close>
      by (auto simp: add_le_imp_le_diff add_le_add_imp_diff_le)
    ultimately show "n \<in> ?A"
      by (simp add: ac_simps) 
  qed
qed

lemma image_add_atLeastAtMost' [simp]:
  "(\<lambda>n. n + k) ` {i..j} = {i + k..j + k}"
  by (simp add: add.commute [of _ k])

lemma image_add_atLeastLessThan [simp]:
  "plus k ` {i..<j} = {i + k..<j + k}"
  by (simp add: image_set_diff atLeastLessThan_eq_atLeastAtMost_diff ac_simps)

lemma image_add_atLeastLessThan' [simp]:
  "(\<lambda>n. n + k) ` {i..<j} = {i + k..<j + k}"
  by (simp add: add.commute [of _ k])

lemma image_add_greaterThanAtMost[simp]: "(+) c ` {a<..b} = {c + a<..c + b}"
  by (simp add: image_set_diff greaterThanAtMost_eq_atLeastAtMost_diff ac_simps)

end

context ordered_ab_group_add
begin

lemma
  fixes x :: 'a
  shows image_uminus_greaterThan[simp]: "uminus ` {x<..} = {..<-x}"
  and image_uminus_atLeast[simp]: "uminus ` {x..} = {..-x}"
proof safe
  fix y assume "y < -x"
  hence *:  "x < -y" using neg_less_iff_less[of "-y" x] by simp
  have "- (-y) \<in> uminus ` {x<..}"
    by (rule imageI) (simp add: *)
  thus "y \<in> uminus ` {x<..}" by simp
next
  fix y assume "y \<le> -x"
  have "- (-y) \<in> uminus ` {x..}"
    by (rule imageI) (insert \<open>y \<le> -x\<close>[THEN le_imp_neg_le], simp)
  thus "y \<in> uminus ` {x..}" by simp
qed simp_all

lemma
  fixes x :: 'a
  shows image_uminus_lessThan[simp]: "uminus ` {..<x} = {-x<..}"
  and image_uminus_atMost[simp]: "uminus ` {..x} = {-x..}"
proof -
  have "uminus ` {..<x} = uminus ` uminus ` {-x<..}"
    and "uminus ` {..x} = uminus ` uminus ` {-x..}" by simp_all
  thus "uminus ` {..<x} = {-x<..}" and "uminus ` {..x} = {-x..}"
    by (simp_all add: image_image
        del: image_uminus_greaterThan image_uminus_atLeast)
qed

lemma
  fixes x :: 'a
  shows image_uminus_atLeastAtMost[simp]: "uminus ` {x..y} = {-y..-x}"
  and image_uminus_greaterThanAtMost[simp]: "uminus ` {x<..y} = {-y..<-x}"
  and image_uminus_atLeastLessThan[simp]: "uminus ` {x..<y} = {-y<..-x}"
  and image_uminus_greaterThanLessThan[simp]: "uminus ` {x<..<y} = {-y<..<-x}"
  by (simp_all add: atLeastAtMost_def greaterThanAtMost_def atLeastLessThan_def
      greaterThanLessThan_def image_Int[OF inj_uminus] Int_commute)

lemma image_add_atMost[simp]: "(+) c ` {..a} = {..c + a}"
  by (auto intro!: image_eqI[where x="x - c" for x] simp: algebra_simps)

end

lemma image_Suc_atLeastAtMost [simp]:
  "Suc ` {i..j} = {Suc i..Suc j}"
  using image_add_atLeastAtMost [of 1 i j]
    by (simp only: plus_1_eq_Suc) simp

lemma image_Suc_atLeastLessThan [simp]:
  "Suc ` {i..<j} = {Suc i..<Suc j}"
  using image_add_atLeastLessThan [of 1 i j]
    by (simp only: plus_1_eq_Suc) simp

corollary image_Suc_atMost:
  "Suc ` {..n} = {1..Suc n}"
  by (simp add: atMost_atLeast0 atLeastLessThanSuc_atLeastAtMost)

corollary image_Suc_lessThan:
  "Suc ` {..<n} = {1..n}"
  by (simp add: lessThan_atLeast0 atLeastLessThanSuc_atLeastAtMost)

lemma image_diff_atLeastAtMost [simp]:
  fixes d::"'a::linordered_idom" shows "((-) d ` {a..b}) = {d-b..d-a}"
  apply auto
  apply (rule_tac x="d-x" in rev_image_eqI, auto)
  done

lemma image_diff_atLeastLessThan [simp]:
  fixes a b c::"'a::linordered_idom"
  shows "(-) c ` {a..<b} = {c - b<..c - a}"
proof -
  have "(-) c ` {a..<b} = (+) c ` uminus ` {a ..<b}"
    unfolding image_image by simp
  also have "\<dots> = {c - b<..c - a}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_greaterThanAtMost[simp]:
  fixes a b c::"'a::linordered_idom"
  shows "(-) c ` {a<..b} = {c - b..<c - a}"
proof -
  have "(-) c ` {a<..b} = (+) c ` uminus ` {a<..b}"
    unfolding image_image by simp
  also have "\<dots> = {c - b..<c - a}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_atLeast[simp]:
  fixes a c::"'a::linordered_idom"
  shows "(-) c ` {a..} = {..c - a}"
proof -
  have "(-) c ` {a..} = (+) c ` uminus ` {a ..}"
    unfolding image_image by simp
  also have "\<dots> = {..c - a}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_AtMost[simp]:
  fixes b c::"'a::linordered_idom"
  shows "(-) c ` {..b} = {c - b..}"
proof -
  have "(-) c ` {..b} = (+) c ` uminus ` {..b}"
    unfolding image_image by simp
  also have "\<dots> = {c - b..}" by simp
  finally show ?thesis by simp
qed

lemma image_minus_const_atLeastAtMost' [simp]:
  "(\<lambda>t. t-d)`{a..b} = {a-d..b-d}" for d::"'a::linordered_idom"
  by (metis (no_types, lifting) diff_conv_add_uminus image_add_atLeastAtMost' image_cong)

context linordered_field
begin

lemma image_mult_atLeastAtMost [simp]:
  "((*) d ` {a..b}) = {d*a..d*b}" if "d>0"
  using that
  by (auto simp: field_simps mult_le_cancel_right intro: rev_image_eqI [where x="x/d" for x])

lemma image_divide_atLeastAtMost [simp]:
  "((\<lambda>c. c / d) ` {a..b}) = {a/d..b/d}" if "d>0"
proof -
  from that have "inverse d > 0"
    by simp
  with image_mult_atLeastAtMost [of "inverse d" a b]
  have "(*) (inverse d) ` {a..b} = {inverse d * a..inverse d * b}"
    by blast
  moreover have "(*) (inverse d) = (\<lambda>c. c / d)"
    by (simp add: fun_eq_iff field_simps)
  ultimately show ?thesis
    by simp
qed

lemma image_mult_atLeastAtMost_if:
  "(*) c ` {x .. y} =
    (if c > 0 then {c * x .. c * y} else if x \<le> y then {c * y .. c * x} else {})"
proof (cases "c = 0 \<or> x > y")
  case True
  then show ?thesis
    by auto
next
  case False
  then have "x \<le> y"
    by auto
  from False consider "c < 0"| "c > 0"
    by (auto simp add: neq_iff)
  then show ?thesis
  proof cases
    case 1
    have "(*) c ` {x..y} = {c * y..c * x}"
    proof (rule set_eqI)
      fix d
      from 1 have "inj (\<lambda>z. z / c)"
        by (auto intro: injI)
      then have "d \<in> (*) c ` {x..y} \<longleftrightarrow> d / c \<in> (\<lambda>z. z div c) ` (*) c ` {x..y}"
        by (subst inj_image_mem_iff) simp_all
      also have "\<dots> \<longleftrightarrow> d / c \<in> {x..y}"
        using 1 by (simp add: image_image)
      also have "\<dots> \<longleftrightarrow> d \<in> {c * y..c * x}"
        by (auto simp add: field_simps 1)
      finally show "d \<in> (*) c ` {x..y} \<longleftrightarrow> d \<in> {c * y..c * x}" .
    qed
    with \<open>x \<le> y\<close> show ?thesis
      by auto
  qed (simp add: mult_left_mono_neg)
qed

lemma image_mult_atLeastAtMost_if':
  "(\<lambda>x. x * c) ` {x..y} =
    (if x \<le> y then if c > 0 then {x * c .. y * c} else {y * c .. x * c} else {})"
  using image_mult_atLeastAtMost_if [of c x y] by (auto simp add: ac_simps)

lemma image_affinity_atLeastAtMost:
  "((\<lambda>x. m * x + c) ` {a..b}) = (if {a..b} = {} then {}
            else if 0 \<le> m then {m * a + c .. m * b + c}
            else {m * b + c .. m * a + c})"
proof -
  have *: "(\<lambda>x. m * x + c) = ((\<lambda>x. x + c) \<circ> (*) m)"
    by (simp add: fun_eq_iff)
  show ?thesis by (simp only: * image_comp [symmetric] image_mult_atLeastAtMost_if)
    (auto simp add: mult_le_cancel_left)
qed

lemma image_affinity_atLeastAtMost_diff:
  "((\<lambda>x. m*x - c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 \<le> m then {m*a - c .. m*b - c}
            else {m*b - c .. m*a - c})"
  using image_affinity_atLeastAtMost [of m "-c" a b]
  by simp

lemma image_affinity_atLeastAtMost_div:
  "((\<lambda>x. x/m + c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 \<le> m then {a/m + c .. b/m + c}
            else {b/m + c .. a/m + c})"
  using image_affinity_atLeastAtMost [of "inverse m" c a b]
  by (simp add: field_class.field_divide_inverse algebra_simps inverse_eq_divide)

lemma image_affinity_atLeastAtMost_div_diff:
  "((\<lambda>x. x/m - c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 \<le> m then {a/m - c .. b/m - c}
            else {b/m - c .. a/m - c})"
  using image_affinity_atLeastAtMost_diff [of "inverse m" c a b]
  by (simp add: field_class.field_divide_inverse algebra_simps inverse_eq_divide)

end

lemma atLeast1_lessThan_eq_remove0:
  "{Suc 0..<n} = {..<n} - {0}"
  by auto

lemma atLeast1_atMost_eq_remove0:
  "{Suc 0..n} = {..n} - {0}"
  by auto

lemma image_add_int_atLeastLessThan:
    "(\<lambda>x. x + (l::int)) ` {0..<u-l} = {l..<u}"
  apply (auto simp add: image_def)
  apply (rule_tac x = "x - l" in bexI)
  apply auto
  done

lemma image_minus_const_atLeastLessThan_nat:
  fixes c :: nat
  shows "(\<lambda>i. i - c) ` {x ..< y} =
      (if c < y then {x - c ..< y - c} else if x < y then {0} else {})"
    (is "_ = ?right")
proof safe
  fix a assume a: "a \<in> ?right"
  show "a \<in> (\<lambda>i. i - c) ` {x ..< y}"
  proof cases
    assume "c < y" with a show ?thesis
      by (auto intro!: image_eqI[of _ _ "a + c"])
  next
    assume "\<not> c < y" with a show ?thesis
      by (auto intro!: image_eqI[of _ _ x] split: if_split_asm)
  qed
qed auto

lemma image_int_atLeastLessThan:
  "int ` {a..<b} = {int a..<int b}"
  by (auto intro!: image_eqI [where x = "nat x" for x])

lemma image_int_atLeastAtMost:
  "int ` {a..b} = {int a..int b}"
  by (auto intro!: image_eqI [where x = "nat x" for x])


subsubsection \<open>Finiteness\<close>

lemma finite_lessThan [iff]: fixes k :: nat shows "finite {..<k}"
  by (induct k) (simp_all add: lessThan_Suc)

lemma finite_atMost [iff]: fixes k :: nat shows "finite {..k}"
  by (induct k) (simp_all add: atMost_Suc)

lemma finite_greaterThanLessThan [iff]:
  fixes l :: nat shows "finite {l<..<u}"
  by (simp add: greaterThanLessThan_def)

lemma finite_atLeastLessThan [iff]:
  fixes l :: nat shows "finite {l..<u}"
  by (simp add: atLeastLessThan_def)

lemma finite_greaterThanAtMost [iff]:
  fixes l :: nat shows "finite {l<..u}"
  by (simp add: greaterThanAtMost_def)

lemma finite_atLeastAtMost [iff]:
  fixes l :: nat shows "finite {l..u}"
  by (simp add: atLeastAtMost_def)

text \<open>A bounded set of natural numbers is finite.\<close>
lemma bounded_nat_set_is_finite: "(\<forall>i\<in>N. i < (n::nat)) \<Longrightarrow> finite N"
  by (rule finite_subset [OF _ finite_lessThan]) auto

text \<open>A set of natural numbers is finite iff it is bounded.\<close>
lemma finite_nat_set_iff_bounded:
  "finite(N::nat set) = (\<exists>m. \<forall>n\<in>N. n<m)" (is "?F = ?B")
proof
  assume f:?F  show ?B
    using Max_ge[OF \<open>?F\<close>, simplified less_Suc_eq_le[symmetric]] by blast
next
  assume ?B show ?F using \<open>?B\<close> by(blast intro:bounded_nat_set_is_finite)
qed

lemma finite_nat_set_iff_bounded_le: "finite(N::nat set) = (\<exists>m. \<forall>n\<in>N. n\<le>m)"
  unfolding finite_nat_set_iff_bounded
  by (blast dest:less_imp_le_nat le_imp_less_Suc)

lemma finite_less_ub:
     "!!f::nat=>nat. (!!n. n \<le> f n) ==> finite {n. f n \<le> u}"
by (rule_tac B="{..u}" in finite_subset, auto intro: order_trans)

lemma bounded_Max_nat:
  fixes P :: "nat \<Rightarrow> bool"
  assumes x: "P x" and M: "\<And>x. P x \<Longrightarrow> x \<le> M"
  obtains m where "P m" "\<And>x. P x \<Longrightarrow> x \<le> m"
proof -
  have "finite {x. P x}"
    using M finite_nat_set_iff_bounded_le by auto
  then have "Max {x. P x} \<in> {x. P x}"
    using Max_in x by auto
  then show ?thesis
    by (simp add: \<open>finite {x. P x}\<close> that)
qed


text\<open>Any subset of an interval of natural numbers the size of the
subset is exactly that interval.\<close>

lemma subset_card_intvl_is_intvl:
  assumes "A \<subseteq> {k..<k + card A}"
  shows "A = {k..<k + card A}"
proof (cases "finite A")
  case True
  from this and assms show ?thesis
  proof (induct A rule: finite_linorder_max_induct)
    case empty thus ?case by auto
  next
    case (insert b A)
    hence *: "b \<notin> A" by auto
    with insert have "A \<le> {k..<k + card A}" and "b = k + card A"
      by fastforce+
    with insert * show ?case by auto
  qed
next
  case False
  with assms show ?thesis by simp
qed


subsubsection \<open>Proving Inclusions and Equalities between Unions\<close>

lemma UN_le_eq_Un0:
  "(\<Union>i\<le>n::nat. M i) = (\<Union>i\<in>{1..n}. M i) \<union> M 0" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain i where i: "i\<le>n" "x \<in> M i" by auto
    show "x \<in> ?B"
    proof(cases i)
      case 0 with i show ?thesis by simp
    next
      case (Suc j) with i show ?thesis by auto
    qed
  qed
next
  show "?B \<subseteq> ?A" by fastforce
qed

lemma UN_le_add_shift:
  "(\<Union>i\<le>n::nat. M(i+k)) = (\<Union>i\<in>{k..n+k}. M i)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" by fastforce
next
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then obtain i where i: "i \<in> {k..n+k}" "x \<in> M(i)" by auto
    hence "i-k\<le>n \<and> x \<in> M((i-k)+k)" by auto
    thus "x \<in> ?A" by blast
  qed
qed

lemma UN_le_add_shift_strict:
  "(\<Union>i<n::nat. M(i+k)) = (\<Union>i\<in>{k..<n+k}. M i)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then obtain i where i: "i \<in> {k..<n+k}" "x \<in> M(i)" by auto
    then have "i - k < n \<and> x \<in> M((i-k) + k)" by auto
    then show "x \<in> ?A" using UN_le_add_shift by blast
  qed
qed (fastforce)

lemma UN_UN_finite_eq: "(\<Union>n::nat. \<Union>i\<in>{0..<n}. A i) = (\<Union>n. A n)"
  by (auto simp add: atLeast0LessThan)

lemma UN_finite_subset:
  "(\<And>n::nat. (\<Union>i\<in>{0..<n}. A i) \<subseteq> C) \<Longrightarrow> (\<Union>n. A n) \<subseteq> C"
  by (subst UN_UN_finite_eq [symmetric]) blast

lemma UN_finite2_subset:
  assumes "\<And>n::nat. (\<Union>i\<in>{0..<n}. A i) \<subseteq> (\<Union>i\<in>{0..<n + k}. B i)"
  shows "(\<Union>n. A n) \<subseteq> (\<Union>n. B n)"
proof (rule UN_finite_subset, rule)
  fix n and a
  from assms have "(\<Union>i\<in>{0..<n}. A i) \<subseteq> (\<Union>i\<in>{0..<n + k}. B i)" .
  moreover assume "a \<in> (\<Union>i\<in>{0..<n}. A i)"
  ultimately have "a \<in> (\<Union>i\<in>{0..<n + k}. B i)" by blast
  then show "a \<in> (\<Union>i. B i)" by (auto simp add: UN_UN_finite_eq)
qed

lemma UN_finite2_eq:
  "(\<And>n::nat. (\<Union>i\<in>{0..<n}. A i) = (\<Union>i\<in>{0..<n + k}. B i)) \<Longrightarrow>
    (\<Union>n. A n) = (\<Union>n. B n)"
  apply (rule subset_antisym [OF UN_finite_subset UN_finite2_subset])
   apply auto
  apply (force simp add: atLeastLessThan_add_Un [of 0])+
  done


subsubsection \<open>Cardinality\<close>

lemma card_lessThan [simp]: "card {..<u} = u"
  by (induct u, simp_all add: lessThan_Suc)

lemma card_atMost [simp]: "card {..u} = Suc u"
  by (simp add: lessThan_Suc_atMost [THEN sym])

lemma card_atLeastLessThan [simp]: "card {l..<u} = u - l"
proof -
  have "{l..<u} = (\<lambda>x. x + l) ` {..<u-l}"
    apply (auto simp add: image_def atLeastLessThan_def lessThan_def)
    apply (rule_tac x = "x - l" in exI)
    apply arith
    done
  then have "card {l..<u} = card {..<u-l}"
    by (simp add: card_image inj_on_def)
  then show ?thesis
    by simp
qed

lemma card_atLeastAtMost [simp]: "card {l..u} = Suc u - l"
  by (subst atLeastLessThanSuc_atLeastAtMost [THEN sym], simp)

lemma card_greaterThanAtMost [simp]: "card {l<..u} = u - l"
  by (subst atLeastSucAtMost_greaterThanAtMost [THEN sym], simp)

lemma card_greaterThanLessThan [simp]: "card {l<..<u} = u - Suc l"
  by (subst atLeastSucLessThan_greaterThanLessThan [THEN sym], simp)

lemma subset_eq_atLeast0_lessThan_finite:
  fixes n :: nat
  assumes "N \<subseteq> {0..<n}"
  shows "finite N"
  using assms finite_atLeastLessThan by (rule finite_subset)

lemma subset_eq_atLeast0_atMost_finite:
  fixes n :: nat
  assumes "N \<subseteq> {0..n}"
  shows "finite N"
  using assms finite_atLeastAtMost by (rule finite_subset)

lemma ex_bij_betw_nat_finite:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h {0..<card M} M"
  apply(drule finite_imp_nat_seg_image_inj_on)
  apply(auto simp:atLeast0LessThan[symmetric] lessThan_def[symmetric] card_image bij_betw_def)
  done

lemma ex_bij_betw_finite_nat:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h M {0..<card M}"
  by (blast dest: ex_bij_betw_nat_finite bij_betw_inv)

lemma finite_same_card_bij:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> card A = card B \<Longrightarrow> \<exists>h. bij_betw h A B"
  apply(drule ex_bij_betw_finite_nat)
  apply(drule ex_bij_betw_nat_finite)
  apply(auto intro!:bij_betw_trans)
  done

lemma ex_bij_betw_nat_finite_1:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h {1 .. card M} M"
  by (rule finite_same_card_bij) auto

lemma bij_betw_iff_card:
  assumes "finite A" "finite B"
  shows "(\<exists>f. bij_betw f A B) \<longleftrightarrow> (card A = card B)"
proof
  assume "card A = card B"
  moreover obtain f where "bij_betw f A {0 ..< card A}"
    using assms ex_bij_betw_finite_nat by blast
  moreover obtain g where "bij_betw g {0 ..< card B} B"
    using assms ex_bij_betw_nat_finite by blast
  ultimately have "bij_betw (g \<circ> f) A B"
    by (auto simp: bij_betw_trans)
  thus "(\<exists>f. bij_betw f A B)" by blast
qed (auto simp: bij_betw_same_card)

lemma subset_eq_atLeast0_lessThan_card:
  fixes n :: nat
  assumes "N \<subseteq> {0..<n}"
  shows "card N \<le> n"
proof -
  from assms finite_lessThan have "card N \<le> card {0..<n}"
    using card_mono by blast
  then show ?thesis by simp
qed

text \<open>Relational version of @{thm [source] card_inj_on_le}:\<close>
lemma card_le_if_inj_on_rel:
assumes "finite B"
  "\<And>a. a \<in> A \<Longrightarrow> \<exists>b. b\<in>B \<and> r a b"
  "\<And>a1 a2 b. \<lbrakk> a1 \<in> A;  a2 \<in> A;  b \<in> B;  r a1 b;  r a2 b \<rbrakk> \<Longrightarrow> a1 = a2"
shows "card A \<le> card B"
proof -
  let ?P = "\<lambda>a b. b \<in> B \<and> r a b"
  let ?f = "\<lambda>a. SOME b. ?P a b"
  have 1: "?f ` A \<subseteq> B"  by (auto intro: someI2_ex[OF assms(2)])
  have "inj_on ?f A"
  proof (auto simp: inj_on_def)
    fix a1 a2 assume asms: "a1 \<in> A" "a2 \<in> A" "?f a1 = ?f a2"
    have 0: "?f a1 \<in> B" using "1" \<open>a1 \<in> A\<close> by blast
    have 1: "r a1 (?f a1)" using someI_ex[OF assms(2)[OF \<open>a1 \<in> A\<close>]] by blast
    have 2: "r a2 (?f a1)" using someI_ex[OF assms(2)[OF \<open>a2 \<in> A\<close>]] asms(3) by auto
    show "a1 = a2" using assms(3)[OF asms(1,2) 0 1 2] .
  qed
  with 1 show ?thesis using card_inj_on_le[of ?f A B] assms(1) by simp
qed

lemma inj_on_funpow_least: \<^marker>\<open>contributor \<open>Lars Noschinski\<close>\<close>
  \<open>inj_on (\<lambda>k. (f ^^ k) s) {0..<n}\<close>
  if \<open>(f ^^ n) s = s\<close> \<open>\<And>m. 0 < m \<Longrightarrow> m < n \<Longrightarrow> (f ^^ m) s \<noteq> s\<close>
proof -
  { fix k l assume A: "k < n" "l < n" "k \<noteq> l" "(f ^^ k) s = (f ^^ l) s"
    define k' l' where "k' = min k l" and "l' = max k l"
    with A have A': "k' < l'" "(f ^^ k') s = (f ^^ l') s" "l' < n"
      by (auto simp: min_def max_def)

    have "s = (f ^^ ((n - l') + l')) s" using that \<open>l' < n\<close> by simp
    also have "\<dots> = (f ^^ (n - l')) ((f ^^ l') s)" by (simp add: funpow_add)
    also have "(f ^^ l') s = (f ^^ k') s" by (simp add: A')
    also have "(f ^^ (n - l')) \<dots> = (f ^^ (n - l' + k')) s" by (simp add: funpow_add)
    finally have "(f ^^ (n - l' + k')) s = s" by simp
    moreover have "n - l' + k' < n" "0 < n - l' + k'"using A' by linarith+
    ultimately have False using that(2) by auto
  }
  then show ?thesis by (intro inj_onI) auto
qed


subsection \<open>Intervals of integers\<close>

lemma atLeastLessThanPlusOne_atLeastAtMost_int: "{l..<u+1} = {l..(u::int)}"
  by (auto simp add: atLeastAtMost_def atLeastLessThan_def)

lemma atLeastPlusOneAtMost_greaterThanAtMost_int: "{l+1..u} = {l<..(u::int)}"
  by (auto simp add: atLeastAtMost_def greaterThanAtMost_def)

lemma atLeastPlusOneLessThan_greaterThanLessThan_int:
    "{l+1..<u} = {l<..<u::int}"
  by (auto simp add: atLeastLessThan_def greaterThanLessThan_def)

subsubsection \<open>Finiteness\<close>

lemma image_atLeastZeroLessThan_int: "0 \<le> u ==>
    {(0::int)..<u} = int ` {..<nat u}"
  unfolding image_def lessThan_def
  apply auto
  apply (rule_tac x = "nat x" in exI)
  apply (auto simp add: zless_nat_eq_int_zless [THEN sym])
  done

lemma finite_atLeastZeroLessThan_int: "finite {(0::int)..<u}"
proof (cases "0 \<le> u")
  case True
  then show ?thesis
    by (auto simp: image_atLeastZeroLessThan_int)
qed auto

lemma finite_atLeastLessThan_int [iff]: "finite {l..<u::int}"
  by (simp only: image_add_int_atLeastLessThan [symmetric, of l] finite_imageI finite_atLeastZeroLessThan_int)

lemma finite_atLeastAtMost_int [iff]: "finite {l..(u::int)}"
  by (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym], simp)

lemma finite_greaterThanAtMost_int [iff]: "finite {l<..(u::int)}"
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma finite_greaterThanLessThan_int [iff]: "finite {l<..<u::int}"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)


subsubsection \<open>Cardinality\<close>

lemma card_atLeastZeroLessThan_int: "card {(0::int)..<u} = nat u"
proof (cases "0 \<le> u")
  case True
  then show ?thesis
    by (auto simp: image_atLeastZeroLessThan_int card_image inj_on_def)    
qed auto

lemma card_atLeastLessThan_int [simp]: "card {l..<u} = nat (u - l)"
proof -
  have "card {l..<u} = card {0..<u-l}"
    apply (subst image_add_int_atLeastLessThan [symmetric])
    apply (rule card_image)
    apply (simp add: inj_on_def)
    done
  then show ?thesis
    by (simp add: card_atLeastZeroLessThan_int)
qed

lemma card_atLeastAtMost_int [simp]: "card {l..u} = nat (u - l + 1)"
  apply (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym])
  apply (auto simp add: algebra_simps)
  done

lemma card_greaterThanAtMost_int [simp]: "card {l<..u} = nat (u - l)"
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma card_greaterThanLessThan_int [simp]: "card {l<..<u} = nat (u - (l + 1))"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)

lemma finite_M_bounded_by_nat: "finite {k. P k \<and> k < (i::nat)}"
proof -
  have "{k. P k \<and> k < i} \<subseteq> {..<i}" by auto
  with finite_lessThan[of "i"] show ?thesis by (simp add: finite_subset)
qed

lemma card_less:
  assumes zero_in_M: "0 \<in> M"
  shows "card {k \<in> M. k < Suc i} \<noteq> 0"
proof -
  from zero_in_M have "{k \<in> M. k < Suc i} \<noteq> {}" by auto
  with finite_M_bounded_by_nat show ?thesis by (auto simp add: card_eq_0_iff)
qed

lemma card_less_Suc2: 
  assumes "0 \<notin> M" shows "card {k. Suc k \<in> M \<and> k < i} = card {k \<in> M. k < Suc i}"
proof -
  have *: "\<lbrakk>j \<in> M; j < Suc i\<rbrakk> \<Longrightarrow> j - Suc 0 < i \<and> Suc (j - Suc 0) \<in> M \<and> Suc 0 \<le> j" for j
    by (cases j) (use assms in auto)
  show ?thesis
  proof (rule card_bij_eq)
    show "inj_on Suc {k. Suc k \<in> M \<and> k < i}"
      by force
    show "inj_on (\<lambda>x. x - Suc 0) {k \<in> M. k < Suc i}"
      by (rule inj_on_diff_nat) (use * in blast)
  qed (use * in auto)
qed

lemma card_less_Suc:
  assumes "0 \<in> M"
    shows "Suc (card {k. Suc k \<in> M \<and> k < i}) = card {k \<in> M. k < Suc i}"
proof -
  have "Suc (card {k. Suc k \<in> M \<and> k < i}) = Suc (card {k. Suc k \<in> M - {0} \<and> k < i})"
    by simp
  also have "\<dots> = Suc (card {k \<in> M - {0}. k < Suc i})"
    apply (subst card_less_Suc2)
    using assms by auto
  also have "\<dots> = Suc (card ({k \<in> M. k < Suc i} - {0}))"
    by (force intro: arg_cong [where f=card])
  also have "\<dots> = card (insert 0 ({k \<in> M. k < Suc i} - {0}))"
    by (simp add: card.insert_remove)
  also have "... = card {k \<in> M. k < Suc i}"
    using assms
    by (force simp add: intro: arg_cong [where f=card])
  finally show ?thesis.
qed

lemma card_le_Suc_Max: "finite S \<Longrightarrow> card S \<le> Suc (Max S)"
proof (rule classical)
  assume "finite S" and "\<not> Suc (Max S) \<ge> card S"
  then have "Suc (Max S) < card S"
    by simp
  with `finite S` have "S \<subseteq> {0..Max S}"
    by auto
  hence "card S \<le> card {0..Max S}"
    by (intro card_mono; auto)
  thus "card S \<le> Suc (Max S)"
    by simp
qed

subsection \<open>Lemmas useful with the summation operator sum\<close>

text \<open>For examples, see Algebra/poly/UnivPoly2.thy\<close>

subsubsection \<open>Disjoint Unions\<close>

text \<open>Singletons and open intervals\<close>

lemma ivl_disj_un_singleton:
  "{l::'a::linorder} Un {l<..} = {l..}"
  "{..<u} Un {u::'a::linorder} = {..u}"
  "(l::'a::linorder) < u ==> {l} Un {l<..<u} = {l..<u}"
  "(l::'a::linorder) < u ==> {l<..<u} Un {u} = {l<..u}"
  "(l::'a::linorder) \<le> u ==> {l} Un {l<..u} = {l..u}"
  "(l::'a::linorder) \<le> u ==> {l..<u} Un {u} = {l..u}"
by auto

text \<open>One- and two-sided intervals\<close>

lemma ivl_disj_un_one:
  "(l::'a::linorder) < u ==> {..l} Un {l<..<u} = {..<u}"
  "(l::'a::linorder) \<le> u ==> {..<l} Un {l..<u} = {..<u}"
  "(l::'a::linorder) \<le> u ==> {..l} Un {l<..u} = {..u}"
  "(l::'a::linorder) \<le> u ==> {..<l} Un {l..u} = {..u}"
  "(l::'a::linorder) \<le> u ==> {l<..u} Un {u<..} = {l<..}"
  "(l::'a::linorder) < u ==> {l<..<u} Un {u..} = {l<..}"
  "(l::'a::linorder) \<le> u ==> {l..u} Un {u<..} = {l..}"
  "(l::'a::linorder) \<le> u ==> {l..<u} Un {u..} = {l..}"
by auto

text \<open>Two- and two-sided intervals\<close>

lemma ivl_disj_un_two:
  "[| (l::'a::linorder) < m; m \<le> u |] ==> {l<..<m} Un {m..<u} = {l<..<u}"
  "[| (l::'a::linorder) \<le> m; m < u |] ==> {l<..m} Un {m<..<u} = {l<..<u}"
  "[| (l::'a::linorder) \<le> m; m \<le> u |] ==> {l..<m} Un {m..<u} = {l..<u}"
  "[| (l::'a::linorder) \<le> m; m < u |] ==> {l..m} Un {m<..<u} = {l..<u}"
  "[| (l::'a::linorder) < m; m \<le> u |] ==> {l<..<m} Un {m..u} = {l<..u}"
  "[| (l::'a::linorder) \<le> m; m \<le> u |] ==> {l<..m} Un {m<..u} = {l<..u}"
  "[| (l::'a::linorder) \<le> m; m \<le> u |] ==> {l..<m} Un {m..u} = {l..u}"
  "[| (l::'a::linorder) \<le> m; m \<le> u |] ==> {l..m} Un {m<..u} = {l..u}"
by auto

lemma ivl_disj_un_two_touch:
  "[| (l::'a::linorder) < m; m < u |] ==> {l<..m} Un {m..<u} = {l<..<u}"
  "[| (l::'a::linorder) \<le> m; m < u |] ==> {l..m} Un {m..<u} = {l..<u}"
  "[| (l::'a::linorder) < m; m \<le> u |] ==> {l<..m} Un {m..u} = {l<..u}"
  "[| (l::'a::linorder) \<le> m; m \<le> u |] ==> {l..m} Un {m..u} = {l..u}"
by auto

lemmas ivl_disj_un = ivl_disj_un_singleton ivl_disj_un_one ivl_disj_un_two ivl_disj_un_two_touch

subsubsection \<open>Disjoint Intersections\<close>

text \<open>One- and two-sided intervals\<close>

lemma ivl_disj_int_one:
  "{..l::'a::order} Int {l<..<u} = {}"
  "{..<l} Int {l..<u} = {}"
  "{..l} Int {l<..u} = {}"
  "{..<l} Int {l..u} = {}"
  "{l<..u} Int {u<..} = {}"
  "{l<..<u} Int {u..} = {}"
  "{l..u} Int {u<..} = {}"
  "{l..<u} Int {u..} = {}"
  by auto

text \<open>Two- and two-sided intervals\<close>

lemma ivl_disj_int_two:
  "{l::'a::order<..<m} Int {m..<u} = {}"
  "{l<..m} Int {m<..<u} = {}"
  "{l..<m} Int {m..<u} = {}"
  "{l..m} Int {m<..<u} = {}"
  "{l<..<m} Int {m..u} = {}"
  "{l<..m} Int {m<..u} = {}"
  "{l..<m} Int {m..u} = {}"
  "{l..m} Int {m<..u} = {}"
  by auto

lemmas ivl_disj_int = ivl_disj_int_one ivl_disj_int_two

subsubsection \<open>Some Differences\<close>

lemma ivl_diff[simp]:
 "i \<le> n \<Longrightarrow> {i..<m} - {i..<n} = {n..<(m::'a::linorder)}"
by(auto)

lemma (in linorder) lessThan_minus_lessThan [simp]:
  "{..< n} - {..< m} = {m ..< n}"
  by auto

lemma (in linorder) atLeastAtMost_diff_ends:
  "{a..b} - {a, b} = {a<..<b}"
  by auto


subsubsection \<open>Some Subset Conditions\<close>

lemma ivl_subset [simp]: "({i..<j} \<subseteq> {m..<n}) = (j \<le> i \<or> m \<le> i \<and> j \<le> (n::'a::linorder))"
  using linorder_class.le_less_linear[of i n]
  apply (auto simp: linorder_not_le)
   apply (force intro: leI)+
  done

lemma obtain_subset_with_card_n:
  assumes "n \<le> card S"
  obtains T where "T \<subseteq> S" "card T = n" "finite T"
proof -
  obtain n' where "card S = n + n'" 
    by (metis assms le_add_diff_inverse)
  with that show thesis
  proof (induct n' arbitrary: S)
    case 0 
    then show ?case
      by (cases "finite S") auto
  next
    case Suc 
    then show ?case 
      by (simp add: card_Suc_eq) (metis subset_insertI2)
  qed
qed

subsection \<open>Generic big monoid operation over intervals\<close>

context semiring_char_0
begin

lemma inj_on_of_nat [simp]:
  "inj_on of_nat N"
  by rule simp

lemma bij_betw_of_nat [simp]:
  "bij_betw of_nat N A \<longleftrightarrow> of_nat ` N = A"
  by (simp add: bij_betw_def)

end

context comm_monoid_set
begin

lemma atLeastLessThan_reindex:
  "F g {h m..<h n} = F (g \<circ> h) {m..<n}"
  if "bij_betw h {m..<n} {h m..<h n}" for m n ::nat
proof -
  from that have "inj_on h {m..<n}" and "h ` {m..<n} = {h m..<h n}"
    by (simp_all add: bij_betw_def)
  then show ?thesis
    using reindex [of h "{m..<n}" g] by simp
qed

lemma atLeastAtMost_reindex:
  "F g {h m..h n} = F (g \<circ> h) {m..n}"
  if "bij_betw h {m..n} {h m..h n}" for m n ::nat
proof -
  from that have "inj_on h {m..n}" and "h ` {m..n} = {h m..h n}"
    by (simp_all add: bij_betw_def)
  then show ?thesis
    using reindex [of h "{m..n}" g] by simp
qed

lemma atLeastLessThan_shift_bounds:
  "F g {m + k..<n + k} = F (g \<circ> plus k) {m..<n}"
  for m n k :: nat
  using atLeastLessThan_reindex [of "plus k" m n g]
  by (simp add: ac_simps)

lemma atLeastAtMost_shift_bounds:
  "F g {m + k..n + k} = F (g \<circ> plus k) {m..n}"
  for m n k :: nat
  using atLeastAtMost_reindex [of "plus k" m n g]
  by (simp add: ac_simps)

lemma atLeast_Suc_lessThan_Suc_shift:
  "F g {Suc m..<Suc n} = F (g \<circ> Suc) {m..<n}"
  using atLeastLessThan_shift_bounds [of _ _ 1]
  by (simp add: plus_1_eq_Suc)

lemma atLeast_Suc_atMost_Suc_shift:
  "F g {Suc m..Suc n} = F (g \<circ> Suc) {m..n}"
  using atLeastAtMost_shift_bounds [of _ _ 1]
  by (simp add: plus_1_eq_Suc)

lemma atLeast_int_lessThan_int_shift:
  "F g {int m..<int n} = F (g \<circ> int) {m..<n}"
  by (rule atLeastLessThan_reindex)
    (simp add: image_int_atLeastLessThan)

lemma atLeast_int_atMost_int_shift:
  "F g {int m..int n} = F (g \<circ> int) {m..n}"
  by (rule atLeastAtMost_reindex)
    (simp add: image_int_atLeastAtMost)

lemma atLeast0_lessThan_Suc:
  "F g {0..<Suc n} = F g {0..<n} \<^bold>* g n"
  by (simp add: atLeast0_lessThan_Suc ac_simps)

lemma atLeast0_atMost_Suc:
  "F g {0..Suc n} = F g {0..n} \<^bold>* g (Suc n)"
  by (simp add: atLeast0_atMost_Suc ac_simps)

lemma atLeast0_lessThan_Suc_shift:
  "F g {0..<Suc n} = g 0 \<^bold>* F (g \<circ> Suc) {0..<n}"
  by (simp add: atLeast0_lessThan_Suc_eq_insert_0 atLeast_Suc_lessThan_Suc_shift)

lemma atLeast0_atMost_Suc_shift:
  "F g {0..Suc n} = g 0 \<^bold>* F (g \<circ> Suc) {0..n}"
  by (simp add: atLeast0_atMost_Suc_eq_insert_0 atLeast_Suc_atMost_Suc_shift)

lemma atLeast_Suc_lessThan:
  "F g {m..<n} = g m \<^bold>* F g {Suc m..<n}" if "m < n"
proof -
  from that have "{m..<n} = insert m {Suc m..<n}"
    by auto
  then show ?thesis by simp
qed

lemma atLeast_Suc_atMost:
  "F g {m..n} = g m \<^bold>* F g {Suc m..n}" if "m \<le> n"
proof -
  from that have "{m..n} = insert m {Suc m..n}"
    by auto
  then show ?thesis by simp
qed

lemma ivl_cong:
  "a = c \<Longrightarrow> b = d \<Longrightarrow> (\<And>x. c \<le> x \<Longrightarrow> x < d \<Longrightarrow> g x = h x)
    \<Longrightarrow> F g {a..<b} = F h {c..<d}"
  by (rule cong) simp_all

lemma atLeastLessThan_shift_0:
  fixes m n p :: nat
  shows "F g {m..<n} = F (g \<circ> plus m) {0..<n - m}"
  using atLeastLessThan_shift_bounds [of g 0 m "n - m"]
  by (cases "m \<le> n") simp_all

lemma atLeastAtMost_shift_0:
  fixes m n p :: nat
  assumes "m \<le> n"
  shows "F g {m..n} = F (g \<circ> plus m) {0..n - m}"
  using assms atLeastAtMost_shift_bounds [of g 0 m "n - m"] by simp

lemma atLeastLessThan_concat:
  fixes m n p :: nat
  shows "m \<le> n \<Longrightarrow> n \<le> p \<Longrightarrow> F g {m..<n} \<^bold>* F g {n..<p} = F g {m..<p}"
  by (simp add: union_disjoint [symmetric] ivl_disj_un)

lemma atLeastLessThan_rev:
  "F g {n..<m} = F (\<lambda>i. g (m + n - Suc i)) {n..<m}"
  by (rule reindex_bij_witness [where i="\<lambda>i. m + n - Suc i" and j="\<lambda>i. m + n - Suc i"], auto)

lemma atLeastAtMost_rev:
  fixes n m :: nat
  shows "F g {n..m} = F (\<lambda>i. g (m + n - i)) {n..m}"
  by (rule reindex_bij_witness [where i="\<lambda>i. m + n - i" and j="\<lambda>i. m + n - i"]) auto

lemma atLeastLessThan_rev_at_least_Suc_atMost:
  "F g {n..<m} = F (\<lambda>i. g (m + n - i)) {Suc n..m}"
  unfolding atLeastLessThan_rev [of g n m]
  by (cases m) (simp_all add: atLeast_Suc_atMost_Suc_shift atLeastLessThanSuc_atLeastAtMost)

end


subsection \<open>Summation indexed over intervals\<close>

syntax (ASCII)
  "_from_to_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(SUM _ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(SUM _ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(SUM _<_./ _)" [0,0,10] 10)
  "_upto_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(SUM _<=_./ _)" [0,0,10] 10)

syntax (latex_sum output)
  "_from_to_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\sum_{\<close>_ = _\<^latex>\<open>}^{\<close>_\<^latex>\<open>}$\<close> _)" [0,0,0,10] 10)
  "_from_upto_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\sum_{\<close>_ = _\<^latex>\<open>}^{<\<close>_\<^latex>\<open>}$\<close> _)" [0,0,0,10] 10)
  "_upt_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\sum_{\<close>_ < _\<^latex>\<open>}$\<close> _)" [0,0,10] 10)
  "_upto_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\sum_{\<close>_ \<le> _\<^latex>\<open>}$\<close> _)" [0,0,10] 10)

syntax
  "_from_to_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sum>_<_./ _)" [0,0,10] 10)
  "_upto_sum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sum>_\<le>_./ _)" [0,0,10] 10)

translations
  "\<Sum>x=a..b. t" == "CONST sum (\<lambda>x. t) {a..b}"
  "\<Sum>x=a..<b. t" == "CONST sum (\<lambda>x. t) {a..<b}"
  "\<Sum>i\<le>n. t" == "CONST sum (\<lambda>i. t) {..n}"
  "\<Sum>i<n. t" == "CONST sum (\<lambda>i. t) {..<n}"

text\<open>The above introduces some pretty alternative syntaxes for
summation over intervals:
\begin{center}
\begin{tabular}{lll}
Old & New & \LaTeX\\
@{term[source]"\<Sum>x\<in>{a..b}. e"} & \<^term>\<open>\<Sum>x=a..b. e\<close> & @{term[mode=latex_sum]"\<Sum>x=a..b. e"}\\
@{term[source]"\<Sum>x\<in>{a..<b}. e"} & \<^term>\<open>\<Sum>x=a..<b. e\<close> & @{term[mode=latex_sum]"\<Sum>x=a..<b. e"}\\
@{term[source]"\<Sum>x\<in>{..b}. e"} & \<^term>\<open>\<Sum>x\<le>b. e\<close> & @{term[mode=latex_sum]"\<Sum>x\<le>b. e"}\\
@{term[source]"\<Sum>x\<in>{..<b}. e"} & \<^term>\<open>\<Sum>x<b. e\<close> & @{term[mode=latex_sum]"\<Sum>x<b. e"}
\end{tabular}
\end{center}
The left column shows the term before introduction of the new syntax,
the middle column shows the new (default) syntax, and the right column
shows a special syntax. The latter is only meaningful for latex output
and has to be activated explicitly by setting the print mode to
\<open>latex_sum\<close> (e.g.\ via \<open>mode = latex_sum\<close> in
antiquotations). It is not the default \LaTeX\ output because it only
works well with italic-style formulae, not tt-style.

Note that for uniformity on \<^typ>\<open>nat\<close> it is better to use
\<^term>\<open>\<Sum>x::nat=0..<n. e\<close> rather than \<open>\<Sum>x<n. e\<close>: \<open>sum\<close> may
not provide all lemmas available for \<^term>\<open>{m..<n}\<close> also in the
special form for \<^term>\<open>{..<n}\<close>.\<close>

text\<open>This congruence rule should be used for sums over intervals as
the standard theorem @{text[source]sum.cong} does not work well
with the simplifier who adds the unsimplified premise \<^term>\<open>x\<in>B\<close> to
the context.\<close>

context comm_monoid_set
begin

lemma zero_middle:
  assumes "1 \<le> p" "k \<le> p"
  shows "F (\<lambda>j. if j < k then g j else if j = k then \<^bold>1 else h (j - Suc 0)) {..p}
       = F (\<lambda>j. if j < k then g j else h j) {..p - Suc 0}"  (is "?lhs = ?rhs")
proof -
  have [simp]: "{..p - Suc 0} \<inter> {j. j < k} = {..<k}" "{..p - Suc 0} \<inter> - {j. j < k} = {k..p - Suc 0}"
    using assms by auto
  have "?lhs = F g {..<k} \<^bold>* F (\<lambda>j. if j = k then \<^bold>1 else h (j - Suc 0)) {k..p}"
    using union_disjoint [of "{..<k}" "{k..p}"] assms
    by (simp add: ivl_disj_int_one ivl_disj_un_one)
  also have "\<dots> = F g {..<k} \<^bold>* F (\<lambda>j.  h (j - Suc 0)) {Suc k..p}"
    by (simp add: atLeast_Suc_atMost [of k p] assms)
  also have "\<dots> = F g {..<k} \<^bold>* F h {k .. p - Suc 0}"
    using reindex [of Suc "{k..p - Suc 0}"] assms by simp
  also have "\<dots> = ?rhs"
    by (simp add: If_cases)
  finally show ?thesis .
qed

lemma atMost_Suc [simp]:
  "F g {..Suc n} = F g {..n} \<^bold>* g (Suc n)"
  by (simp add: atMost_Suc ac_simps)

lemma lessThan_Suc [simp]:
  "F g {..<Suc n} = F g {..<n} \<^bold>* g n"
  by (simp add: lessThan_Suc ac_simps)

lemma cl_ivl_Suc [simp]:
  "F g {m..Suc n} = (if Suc n < m then \<^bold>1 else F g {m..n} \<^bold>* g(Suc n))"
  by (auto simp: ac_simps atLeastAtMostSuc_conv)

lemma op_ivl_Suc [simp]:
  "F g {m..<Suc n} = (if n < m then \<^bold>1 else F g {m..<n} \<^bold>* g(n))"
  by (auto simp: ac_simps atLeastLessThanSuc)

lemma head:
  fixes n :: nat
  assumes mn: "m \<le> n"
  shows "F g {m..n} = g m \<^bold>* F g {m<..n}" (is "?lhs = ?rhs")
proof -
  from mn
  have "{m..n} = {m} \<union> {m<..n}"
    by (auto intro: ivl_disj_un_singleton)
  hence "?lhs = F g ({m} \<union> {m<..n})"
    by (simp add: atLeast0LessThan)
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed

lemma last_plus: 
  fixes n::nat  shows "m \<le> n \<Longrightarrow> F g {m..n} = g n \<^bold>* F g {m..<n}"
  by (cases n) (auto simp: atLeastLessThanSuc_atLeastAtMost commute)

lemma head_if:
  fixes n :: nat
  shows "F g {m..n} = (if n < m then \<^bold>1 else  F g {m..<n} \<^bold>* g(n))"
  by (simp add: commute last_plus)

lemma ub_add_nat: 
  assumes "(m::nat) \<le> n + 1"
  shows "F g {m..n + p} = F g {m..n} \<^bold>* F g {n + 1..n + p}"
proof-
  have "{m .. n+p} = {m..n} \<union> {n+1..n+p}" using \<open>m \<le> n+1\<close> by auto
  thus ?thesis by (auto simp: ivl_disj_int union_disjoint atLeastSucAtMost_greaterThanAtMost)
qed

lemma nat_group: 
  fixes k::nat shows "F (\<lambda>m. F g {m * k ..< m*k + k}) {..<n} = F g {..< n * k}"
proof (cases k)
  case (Suc l)
  then have "k > 0"
    by auto
  then show ?thesis
    by (induct n) (simp_all add: atLeastLessThan_concat add.commute atLeast0LessThan[symmetric])
qed auto   

lemma triangle_reindex:
  fixes n :: nat
  shows "F (\<lambda>(i,j). g i j) {(i,j). i+j < n} = F (\<lambda>k. F (\<lambda>i. g i (k - i)) {..k}) {..<n}"
  apply (simp add: Sigma)
  apply (rule reindex_bij_witness[where j="\<lambda>(i, j). (i+j, i)" and i="\<lambda>(k, i). (i, k - i)"])
  apply auto
  done

lemma triangle_reindex_eq:
  fixes n :: nat
  shows "F (\<lambda>(i,j). g i j) {(i,j). i+j \<le> n} = F (\<lambda>k. F (\<lambda>i. g i (k - i)) {..k}) {..n}"
using triangle_reindex [of g "Suc n"]
by (simp only: Nat.less_Suc_eq_le lessThan_Suc_atMost)

lemma nat_diff_reindex: "F (\<lambda>i. g (n - Suc i)) {..<n} = F g {..<n}"
  by (rule reindex_bij_witness[where i="\<lambda>i. n - Suc i" and j="\<lambda>i. n - Suc i"]) auto

lemma shift_bounds_nat_ivl:
  "F g {m+k..<n+k} = F (\<lambda>i. g(i + k)){m..<n::nat}"
by (induct "n", auto simp: atLeastLessThanSuc)

lemma shift_bounds_cl_nat_ivl:
  "F g {m+k..n+k} = F (\<lambda>i. g(i + k)){m..n::nat}"
  by (rule reindex_bij_witness[where i="\<lambda>i. i + k" and j="\<lambda>i. i - k"]) auto

corollary shift_bounds_cl_Suc_ivl:
  "F g {Suc m..Suc n} = F (\<lambda>i. g(Suc i)){m..n}"
by (simp add: shift_bounds_cl_nat_ivl[where k="Suc 0", simplified])

corollary Suc_reindex_ivl: "m \<le> n \<Longrightarrow> F g {m..n} \<^bold>* g (Suc n) = g m \<^bold>* F (\<lambda>i. g (Suc i)) {m..n}"
  by (simp add: assoc atLeast_Suc_atMost flip: shift_bounds_cl_Suc_ivl)

corollary shift_bounds_Suc_ivl:
  "F g {Suc m..<Suc n} = F (\<lambda>i. g(Suc i)){m..<n}"
by (simp add: shift_bounds_nat_ivl[where k="Suc 0", simplified])

lemma atMost_Suc_shift:
  shows "F g {..Suc n} = g 0 \<^bold>* F (\<lambda>i. g (Suc i)) {..n}"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) note IH = this
  have "F g {..Suc (Suc n)} = F g {..Suc n} \<^bold>* g (Suc (Suc n))"
    by (rule atMost_Suc)
  also have "F g {..Suc n}  = g 0 \<^bold>* F (\<lambda>i. g (Suc i)) {..n}"
    by (rule IH)
  also have "g 0 \<^bold>* F (\<lambda>i. g (Suc i)) {..n} \<^bold>* g (Suc (Suc n)) =
             g 0 \<^bold>* (F (\<lambda>i. g (Suc i)) {..n} \<^bold>* g (Suc (Suc n)))"
    by (rule assoc)
  also have "F (\<lambda>i. g (Suc i)) {..n} \<^bold>* g (Suc (Suc n)) = F (\<lambda>i. g (Suc i)) {..Suc n}"
    by (rule atMost_Suc [symmetric])
  finally show ?case .
qed

lemma lessThan_Suc_shift:
  "F g {..<Suc n} = g 0 \<^bold>* F (\<lambda>i. g (Suc i)) {..<n}"
  by (induction n) (simp_all add: ac_simps)

lemma atMost_shift:
  "F g {..n} = g 0 \<^bold>* F (\<lambda>i. g (Suc i)) {..<n}"
  by (metis atLeast0AtMost atLeast0LessThan atLeastLessThanSuc_atLeastAtMost 
       atLeastSucAtMost_greaterThanAtMost le0 head shift_bounds_Suc_ivl)

lemma nested_swap:
     "F (\<lambda>i. F (\<lambda>j. a i j) {0..<i}) {0..n} = F (\<lambda>j. F (\<lambda>i. a i j) {Suc j..n}) {0..<n}"
  by (induction n) (auto simp: distrib)

lemma nested_swap':
     "F (\<lambda>i. F (\<lambda>j. a i j) {..<i}) {..n} = F (\<lambda>j. F (\<lambda>i. a i j) {Suc j..n}) {..<n}"
  by (induction n) (auto simp: distrib)

lemma atLeast1_atMost_eq:
  "F g {Suc 0..n} = F (\<lambda>k. g (Suc k)) {..<n}"
proof -
  have "F g {Suc 0..n} = F g (Suc ` {..<n})"
    by (simp add: image_Suc_lessThan)
  also have "\<dots> = F (\<lambda>k. g (Suc k)) {..<n}"
    by (simp add: reindex)
  finally show ?thesis .
qed

lemma atLeastLessThan_Suc: "a \<le> b \<Longrightarrow> F g {a..<Suc b} = F g {a..<b} \<^bold>* g b"
  by (simp add: atLeastLessThanSuc commute)

lemma nat_ivl_Suc':
  assumes "m \<le> Suc n"
  shows   "F g {m..Suc n} = g (Suc n) \<^bold>* F g {m..n}"
proof -
  from assms have "{m..Suc n} = insert (Suc n) {m..n}" by auto
  also have "F g \<dots> = g (Suc n) \<^bold>* F g {m..n}" by simp
  finally show ?thesis .
qed

lemma in_pairs: "F g {2*m..Suc(2*n)} = F (\<lambda>i. g(2*i) \<^bold>* g(Suc(2*i))) {m..n}"
proof (induction n)
  case 0
  show ?case
    by (cases "m=0") auto
next
  case (Suc n)
  then show ?case
    by (auto simp: assoc split: if_split_asm)
qed

lemma in_pairs_0: "F g {..Suc(2*n)} = F (\<lambda>i. g(2*i) \<^bold>* g(Suc(2*i))) {..n}"
  using in_pairs [of _ 0 n] by (simp add: atLeast0AtMost)

end

lemma card_sum_le_nat_sum: "\<Sum> {0..<card S} \<le> \<Sum> S"
proof (cases "finite S")
  case True
  then show ?thesis
  proof (induction "card S" arbitrary: S)
    case (Suc x)
    then have "Max S \<ge> x" using card_le_Suc_Max by fastforce
    let ?S' = "S - {Max S}"
    from Suc have "Max S \<in> S" by (auto intro: Max_in)
    hence cards: "card S = Suc (card ?S')"
      using `finite S` by (intro card.remove; auto)
    hence "\<Sum> {0..<card ?S'} \<le> \<Sum> ?S'"
      using Suc by (intro Suc; auto)

    hence "\<Sum> {0..<card ?S'} + x \<le> \<Sum> ?S' + Max S"
      using `Max S \<ge> x` by simp
    also have "... = \<Sum> S"
      using sum.remove[OF `finite S` `Max S \<in> S`, where g="\<lambda>x. x"]
      by simp
    finally show ?case
      using cards Suc by auto
  qed simp
qed simp

lemma sum_natinterval_diff:
  fixes f:: "nat \<Rightarrow> ('a::ab_group_add)"
  shows  "sum (\<lambda>k. f k - f(k + 1)) {(m::nat) .. n} =
          (if m \<le> n then f m - f(n + 1) else 0)"
by (induct n, auto simp add: algebra_simps not_le le_Suc_eq)

lemma sum_diff_nat_ivl:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  shows "\<lbrakk> m \<le> n; n \<le> p \<rbrakk> \<Longrightarrow> sum f {m..<p} - sum f {m..<n} = sum f {n..<p}"
  using sum.atLeastLessThan_concat [of m n p f,symmetric]
  by (simp add: ac_simps)

lemma sum_diff_distrib: "\<forall>x. Q x \<le> P x  \<Longrightarrow> (\<Sum>x<n. P x) - (\<Sum>x<n. Q x) = (\<Sum>x<n. P x - Q x :: nat)"
  by (subst sum_subtractf_nat) auto


context unique_euclidean_semiring_with_bit_shifts
begin

lemma take_bit_sum:
  "take_bit n a = (\<Sum>k = 0..<n. push_bit k (of_bool (bit a k)))"
  for n :: nat
proof (induction n arbitrary: a)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "(\<Sum>k = 0..<Suc n. push_bit k (of_bool (bit a k))) = 
    of_bool (odd a) + (\<Sum>k = Suc 0..<Suc n. push_bit k (of_bool (bit a k)))"
    by (simp add: sum.atLeast_Suc_lessThan ac_simps)
  also have "(\<Sum>k = Suc 0..<Suc n. push_bit k (of_bool (bit a k)))
    = (\<Sum>k = 0..<n. push_bit k (of_bool (bit (a div 2) k))) * 2"
    by (simp only: sum.atLeast_Suc_lessThan_Suc_shift) (simp add: sum_distrib_right push_bit_double drop_bit_Suc bit_Suc)
  finally show ?case
    using Suc [of "a div 2"] by (simp add: ac_simps take_bit_Suc mod_2_eq_odd)
qed

end


subsubsection \<open>Shifting bounds\<close>

context comm_monoid_add
begin

context
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "f 0 = 0"
begin

lemma sum_shift_lb_Suc0_0_upt:
  "sum f {Suc 0..<k} = sum f {0..<k}"
proof (cases k)
  case 0
  then show ?thesis
    by simp
next
  case (Suc k)
  moreover have "{0..<Suc k} = insert 0 {Suc 0..<Suc k}"
    by auto
  ultimately show ?thesis
    using \<open>f 0 = 0\<close> by simp
qed

lemma sum_shift_lb_Suc0_0: "sum f {Suc 0..k} = sum f {0..k}"
proof (cases k)
  case 0
  with \<open>f 0 = 0\<close> show ?thesis
    by simp
next
  case (Suc k)
  moreover have "{0..Suc k} = insert 0 {Suc 0..Suc k}"
    by auto
  ultimately show ?thesis
    using \<open>f 0 = 0\<close> by simp
qed

end

end

lemma sum_Suc_diff:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  assumes "m \<le> Suc n"
  shows "(\<Sum>i = m..n. f(Suc i) - f i) = f (Suc n) - f m"
using assms by (induct n) (auto simp: le_Suc_eq)

lemma sum_Suc_diff':
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  assumes "m \<le> n"
  shows "(\<Sum>i = m..<n. f (Suc i) - f i) = f n - f m"
using assms by (induct n) (auto simp: le_Suc_eq)


subsubsection \<open>Telescoping\<close>

lemma sum_telescope:
  fixes f::"nat \<Rightarrow> 'a::ab_group_add"
  shows "sum (\<lambda>i. f i - f (Suc i)) {.. i} = f 0 - f (Suc i)"
  by (induct i) simp_all

lemma sum_telescope'':
  assumes "m \<le> n"
  shows   "(\<Sum>k\<in>{Suc m..n}. f k - f (k - 1)) = f n - (f m :: 'a :: ab_group_add)"
  by (rule dec_induct[OF assms]) (simp_all add: algebra_simps)

lemma sum_lessThan_telescope:
  "(\<Sum>n<m. f (Suc n) - f n :: 'a :: ab_group_add) = f m - f 0"
  by (induction m) (simp_all add: algebra_simps)

lemma sum_lessThan_telescope':
  "(\<Sum>n<m. f n - f (Suc n) :: 'a :: ab_group_add) = f 0 - f m"
  by (induction m) (simp_all add: algebra_simps)


subsubsection \<open>The formula for geometric sums\<close>

lemma sum_power2: "(\<Sum>i=0..<k. (2::nat)^i) = 2^k-1"
  by (induction k) (auto simp: mult_2)

lemma geometric_sum:
  assumes "x \<noteq> 1"
  shows "(\<Sum>i<n. x ^ i) = (x ^ n - 1) / (x - 1::'a::field)"
proof -
  from assms obtain y where "y = x - 1" and "y \<noteq> 0" by simp_all
  moreover have "(\<Sum>i<n. (y + 1) ^ i) = ((y + 1) ^ n - 1) / y"
    by (induct n) (simp_all add: field_simps \<open>y \<noteq> 0\<close>)
  ultimately show ?thesis by simp
qed

lemma diff_power_eq_sum:
  fixes y :: "'a::{comm_ring,monoid_mult}"
  shows
    "x ^ (Suc n) - y ^ (Suc n) =
      (x - y) * (\<Sum>p<Suc n. (x ^ p) * y ^ (n - p))"
proof (induct n)
  case (Suc n)
  have "x ^ Suc (Suc n) - y ^ Suc (Suc n) = x * (x * x^n) - y * (y * y ^ n)"
    by simp
  also have "... = y * (x ^ (Suc n) - y ^ (Suc n)) + (x - y) * (x * x^n)"
    by (simp add: algebra_simps)
  also have "... = y * ((x - y) * (\<Sum>p<Suc n. (x ^ p) * y ^ (n - p))) + (x - y) * (x * x^n)"
    by (simp only: Suc)
  also have "... = (x - y) * (y * (\<Sum>p<Suc n. (x ^ p) * y ^ (n - p))) + (x - y) * (x * x^n)"
    by (simp only: mult.left_commute)
  also have "... = (x - y) * (\<Sum>p<Suc (Suc n). x ^ p * y ^ (Suc n - p))"
    by (simp add: field_simps Suc_diff_le sum_distrib_right sum_distrib_left)
  finally show ?case .
qed simp

corollary power_diff_sumr2: \<comment> \<open>\<open>COMPLEX_POLYFUN\<close> in HOL Light\<close>
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "x^n - y^n = (x - y) * (\<Sum>i<n. y^(n - Suc i) * x^i)"
using diff_power_eq_sum[of x "n - 1" y]
by (cases "n = 0") (simp_all add: field_simps)

lemma power_diff_1_eq:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "x^n - 1 = (x - 1) * (\<Sum>i<n. (x^i))"
using diff_power_eq_sum [of x _ 1]
  by (cases n) auto

lemma one_diff_power_eq':
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "1 - x^n = (1 - x) * (\<Sum>i<n. x^(n - Suc i))"
using diff_power_eq_sum [of 1 _ x]
  by (cases n) auto

lemma one_diff_power_eq:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "1 - x^n = (1 - x) * (\<Sum>i<n. x^i)"
by (metis one_diff_power_eq' sum.nat_diff_reindex)

lemma sum_gp_basic:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "(1 - x) * (\<Sum>i\<le>n. x^i) = 1 - x^Suc n"
  by (simp only: one_diff_power_eq lessThan_Suc_atMost)

lemma sum_power_shift:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  assumes "m \<le> n"
  shows "(\<Sum>i=m..n. x^i) = x^m * (\<Sum>i\<le>n-m. x^i)"
proof -
  have "(\<Sum>i=m..n. x^i) = x^m * (\<Sum>i=m..n. x^(i-m))"
    by (simp add: sum_distrib_left power_add [symmetric])
  also have "(\<Sum>i=m..n. x^(i-m)) = (\<Sum>i\<le>n-m. x^i)"
    using \<open>m \<le> n\<close> by (intro sum.reindex_bij_witness[where j="\<lambda>i. i - m" and i="\<lambda>i. i + m"]) auto
  finally show ?thesis .
qed

lemma sum_gp_multiplied:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  assumes "m \<le> n"
  shows "(1 - x) * (\<Sum>i=m..n. x^i) = x^m - x^Suc n"
proof -
  have  "(1 - x) * (\<Sum>i=m..n. x^i) = x^m * (1 - x) * (\<Sum>i\<le>n-m. x^i)"
    by (metis mult.assoc mult.commute assms sum_power_shift)
  also have "... =x^m * (1 - x^Suc(n-m))"
    by (metis mult.assoc sum_gp_basic)
  also have "... = x^m - x^Suc n"
    using assms
    by (simp add: algebra_simps) (metis le_add_diff_inverse power_add)
  finally show ?thesis .
qed

lemma sum_gp:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows   "(\<Sum>i=m..n. x^i) =
               (if n < m then 0
                else if x = 1 then of_nat((n + 1) - m)
                else (x^m - x^Suc n) / (1 - x))"
using sum_gp_multiplied [of m n x] apply auto
by (metis eq_iff_diff_eq_0 mult.commute nonzero_divide_eq_eq)


subsubsection\<open>Geometric progressions\<close>

lemma sum_gp0:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows "(\<Sum>i\<le>n. x^i) = (if x = 1 then of_nat(n + 1) else (1 - x^Suc n) / (1 - x))"
  using sum_gp_basic[of x n]
  by (simp add: mult.commute field_split_simps)

lemma sum_power_add:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "(\<Sum>i\<in>I. x^(m+i)) = x^m * (\<Sum>i\<in>I. x^i)"
  by (simp add: sum_distrib_left power_add)

lemma sum_gp_offset:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows   "(\<Sum>i=m..m+n. x^i) =
       (if x = 1 then of_nat n + 1 else x^m * (1 - x^Suc n) / (1 - x))"
  using sum_gp [of x m "m+n"]
  by (auto simp: power_add algebra_simps)

lemma sum_gp_strict:
  fixes x :: "'a::{comm_ring,division_ring}"
  shows "(\<Sum>i<n. x^i) = (if x = 1 then of_nat n else (1 - x^n) / (1 - x))"
  by (induct n) (auto simp: algebra_simps field_split_simps)


subsubsection \<open>The formulae for arithmetic sums\<close>

context comm_semiring_1
begin

lemma double_gauss_sum:
  "2 * (\<Sum>i = 0..n. of_nat i) = of_nat n * (of_nat n + 1)"
  by (induct n) (simp_all add: sum.atLeast0_atMost_Suc algebra_simps left_add_twice)

lemma double_gauss_sum_from_Suc_0:
  "2 * (\<Sum>i = Suc 0..n. of_nat i) = of_nat n * (of_nat n + 1)"
proof -
  have "sum of_nat {Suc 0..n} = sum of_nat (insert 0 {Suc 0..n})"
    by simp
  also have "\<dots> = sum of_nat {0..n}"
    by (cases n) (simp_all add: atLeast0_atMost_Suc_eq_insert_0)
  finally show ?thesis
    by (simp add: double_gauss_sum)
qed

lemma double_arith_series:
  "2 * (\<Sum>i = 0..n. a + of_nat i * d) = (of_nat n + 1) * (2 * a + of_nat n * d)"
proof -
  have "(\<Sum>i = 0..n. a + of_nat i * d) = ((\<Sum>i = 0..n. a) + (\<Sum>i = 0..n. of_nat i * d))"
    by (rule sum.distrib)
  also have "\<dots> = (of_nat (Suc n) * a + d * (\<Sum>i = 0..n. of_nat i))"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis
    by (simp add: algebra_simps double_gauss_sum left_add_twice)
qed

end

context unique_euclidean_semiring_with_nat
begin

lemma gauss_sum:
  "(\<Sum>i = 0..n. of_nat i) = of_nat n * (of_nat n + 1) div 2"
  using double_gauss_sum [of n, symmetric] by simp

lemma gauss_sum_from_Suc_0:
  "(\<Sum>i = Suc 0..n. of_nat i) = of_nat n * (of_nat n + 1) div 2"
  using double_gauss_sum_from_Suc_0 [of n, symmetric] by simp

lemma arith_series:
  "(\<Sum>i = 0..n. a + of_nat i * d) = (of_nat n + 1) * (2 * a + of_nat n * d) div 2"
  using double_arith_series [of a d n, symmetric] by simp

end

lemma gauss_sum_nat:
  "\<Sum>{0..n} = (n * Suc n) div 2"
  using gauss_sum [of n, where ?'a = nat] by simp

lemma arith_series_nat:
  "(\<Sum>i = 0..n. a + i * d) = Suc n * (2 * a + n * d) div 2"
  using arith_series [of a d n] by simp

lemma Sum_Icc_int:
  "\<Sum>{m..n} = (n * (n + 1) - m * (m - 1)) div 2"
  if "m \<le> n" for m n :: int
using that proof (induct i \<equiv> "nat (n - m)" arbitrary: m n)
  case 0
  then have "m = n"
    by arith
  then show ?case
    by (simp add: algebra_simps mult_2 [symmetric])
next
  case (Suc i)
  have 0: "i = nat((n-1) - m)" "m \<le> n-1" using Suc(2,3) by arith+
  have "\<Sum> {m..n} = \<Sum> {m..1+(n-1)}" by simp
  also have "\<dots> = \<Sum> {m..n-1} + n" using \<open>m \<le> n\<close>
    by(subst atLeastAtMostPlus1_int_conv) simp_all
  also have "\<dots> = ((n-1)*(n-1+1) - m*(m-1)) div 2 + n"
    by(simp add: Suc(1)[OF 0])
  also have "\<dots> = ((n-1)*(n-1+1) - m*(m-1) + 2*n) div 2" by simp
  also have "\<dots> = (n*(n+1) - m*(m-1)) div 2"
    by (simp add: algebra_simps mult_2_right)
  finally show ?case .
qed

lemma Sum_Icc_nat:
  "\<Sum>{m..n} = (n * (n + 1) - m * (m - 1)) div 2" for m n :: nat
proof (cases "m \<le> n")
  case True
  then have *: "m * (m - 1) \<le> n * (n + 1)"
    by (meson diff_le_self order_trans le_add1 mult_le_mono)
  have "int (\<Sum>{m..n}) = (\<Sum>{int m..int n})"
    by (simp add: sum.atLeast_int_atMost_int_shift)
  also have "\<dots> = (int n * (int n + 1) - int m * (int m - 1)) div 2"
    using \<open>m \<le> n\<close> by (simp add: Sum_Icc_int)
  also have "\<dots> = int ((n * (n + 1) - m * (m - 1)) div 2)"
    using le_square * by (simp add: algebra_simps of_nat_div of_nat_diff)
  finally show ?thesis
    by (simp only: of_nat_eq_iff)
next
  case False
  then show ?thesis
    by (auto dest: less_imp_Suc_add simp add: not_le algebra_simps)
qed

lemma Sum_Ico_nat: 
  "\<Sum>{m..<n} = (n * (n - 1) - m * (m - 1)) div 2" for m n :: nat
  by (cases n) (simp_all add: atLeastLessThanSuc_atLeastAtMost Sum_Icc_nat)


subsubsection \<open>Division remainder\<close>

lemma range_mod:
  fixes n :: nat
  assumes "n > 0"
  shows "range (\<lambda>m. m mod n) = {0..<n}" (is "?A = ?B")
proof (rule set_eqI)
  fix m
  show "m \<in> ?A \<longleftrightarrow> m \<in> ?B"
  proof
    assume "m \<in> ?A"
    with assms show "m \<in> ?B"
      by auto
  next
    assume "m \<in> ?B"
    moreover have "m mod n \<in> ?A"
      by (rule rangeI)
    ultimately show "m \<in> ?A"
      by simp
  qed
qed


subsection \<open>Products indexed over intervals\<close>

syntax (ASCII)
  "_from_to_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(PROD _ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(PROD _ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(PROD _<_./ _)" [0,0,10] 10)
  "_upto_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(PROD _<=_./ _)" [0,0,10] 10)

syntax (latex_prod output)
  "_from_to_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\prod_{\<close>_ = _\<^latex>\<open>}^{\<close>_\<^latex>\<open>}$\<close> _)" [0,0,0,10] 10)
  "_from_upto_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\prod_{\<close>_ = _\<^latex>\<open>}^{<\<close>_\<^latex>\<open>}$\<close> _)" [0,0,0,10] 10)
  "_upt_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\prod_{\<close>_ < _\<^latex>\<open>}$\<close> _)" [0,0,10] 10)
  "_upto_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^latex>\<open>$\\prod_{\<close>_ \<le> _\<^latex>\<open>}$\<close> _)" [0,0,10] 10)

syntax
  "_from_to_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Prod>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Prod>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Prod>_<_./ _)" [0,0,10] 10)
  "_upto_prod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Prod>_\<le>_./ _)" [0,0,10] 10)

translations
  "\<Prod>x=a..b. t" \<rightleftharpoons> "CONST prod (\<lambda>x. t) {a..b}"
  "\<Prod>x=a..<b. t" \<rightleftharpoons> "CONST prod (\<lambda>x. t) {a..<b}"
  "\<Prod>i\<le>n. t" \<rightleftharpoons> "CONST prod (\<lambda>i. t) {..n}"
  "\<Prod>i<n. t" \<rightleftharpoons> "CONST prod (\<lambda>i. t) {..<n}"

lemma prod_int_plus_eq: "prod int {i..i+j} =  \<Prod>{int i..int (i+j)}"
  by (induct j) (auto simp add: atLeastAtMostSuc_conv atLeastAtMostPlus1_int_conv)

lemma prod_int_eq: "prod int {i..j} =  \<Prod>{int i..int j}"
proof (cases "i \<le> j")
  case True
  then show ?thesis
    by (metis le_iff_add prod_int_plus_eq)
next
  case False
  then show ?thesis
    by auto
qed

subsection \<open>Efficient folding over intervals\<close>

function fold_atLeastAtMost_nat where
  [simp del]: "fold_atLeastAtMost_nat f a (b::nat) acc =
                 (if a > b then acc else fold_atLeastAtMost_nat f (a+1) b (f a acc))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(_,a,b,_). Suc b - a)") auto

lemma fold_atLeastAtMost_nat:
  assumes "comp_fun_commute f"
  shows   "fold_atLeastAtMost_nat f a b acc = Finite_Set.fold f acc {a..b}"
using assms
proof (induction f a b acc rule: fold_atLeastAtMost_nat.induct, goal_cases)
  case (1 f a b acc)
  interpret comp_fun_commute f by fact
  show ?case
  proof (cases "a > b")
    case True
    thus ?thesis by (subst fold_atLeastAtMost_nat.simps) auto
  next
    case False
    with 1 show ?thesis
      by (subst fold_atLeastAtMost_nat.simps)
         (auto simp: atLeastAtMost_insertL[symmetric] fold_fun_left_comm)
  qed
qed

lemma sum_atLeastAtMost_code:
  "sum f {a..b} = fold_atLeastAtMost_nat (\<lambda>a acc. f a + acc) a b 0"
proof -
  have "comp_fun_commute (\<lambda>a. (+) (f a))"
    by unfold_locales (auto simp: o_def add_ac)
  thus ?thesis
    by (simp add: sum.eq_fold fold_atLeastAtMost_nat o_def)
qed

lemma prod_atLeastAtMost_code:
  "prod f {a..b} = fold_atLeastAtMost_nat (\<lambda>a acc. f a * acc) a b 1"
proof -
  have "comp_fun_commute (\<lambda>a. (*) (f a))"
    by unfold_locales (auto simp: o_def mult_ac)
  thus ?thesis
    by (simp add: prod.eq_fold fold_atLeastAtMost_nat o_def)
qed

(* TODO: Add support for folding over more kinds of intervals here *)

end
