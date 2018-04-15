(*  Title:      HOL/Set_Interval.thy
    Author:     Tobias Nipkow
    Author:     Clemens Ballarin
    Author:     Jeremy Avigad

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


text\<open>A note of warning when using @{term"{..<n}"} on type @{typ
nat}: it is equivalent to @{term"{0::nat..<n}"} but some lemmas involving
@{term"{m..<n}"} may not exist in @{term"{..<n}"}-form as well.\<close>

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
apply (auto simp add: lessThan_def atLeast_def)
done

lemma single_Diff_lessThan [simp]: "!!k:: 'a::order. {k} - lessThan k = {k}"
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

lemma Compl_atLeast [simp]:
    "!!k:: 'a::linorder. -atLeast k = lessThan k"
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
     "(atLeast x \<subseteq> atLeast y) = (y \<le> (x::'a::order))"
by (blast intro: order_trans)

lemma atLeast_eq_iff [iff]:
     "(atLeast x = atLeast y) = (x = (y::'a::linorder))"
by (blast intro: order_antisym order_trans)

lemma greaterThan_subset_iff [iff]:
     "(greaterThan x \<subseteq> greaterThan y) = (y \<le> (x::'a::linorder))"
apply (auto simp add: greaterThan_def)
 apply (subst linorder_not_less [symmetric], blast)
done

lemma greaterThan_eq_iff [iff]:
     "(greaterThan x = greaterThan y) = (x = (y::'a::linorder))"
apply (rule iffI)
 apply (erule equalityE)
 apply simp_all
done

lemma atMost_subset_iff [iff]: "(atMost x \<subseteq> atMost y) = (x \<le> (y::'a::order))"
by (blast intro: order_trans)

lemma atMost_eq_iff [iff]: "(atMost x = atMost y) = (x = (y::'a::linorder))"
by (blast intro: order_antisym order_trans)

lemma lessThan_subset_iff [iff]:
     "(lessThan x \<subseteq> lessThan y) = (x \<le> (y::'a::linorder))"
apply (auto simp add: lessThan_def)
 apply (subst linorder_not_less [symmetric], blast)
done

lemma lessThan_eq_iff [iff]:
     "(lessThan x = lessThan y) = (x = (y::'a::linorder))"
apply (rule iffI)
 apply (erule equalityE)
 apply simp_all
done

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

lemma greaterThanLessThan_iff [simp]:
  "(i \<in> {l<..<u}) = (l < i \<and> i < u)"
by (simp add: greaterThanLessThan_def)

lemma atLeastLessThan_iff [simp]:
  "(i \<in> {l..<u}) = (l \<le> i \<and> i < u)"
by (simp add: atLeastLessThan_def)

lemma greaterThanAtMost_iff [simp]:
  "(i \<in> {l<..u}) = (l < i \<and> i \<le> u)"
by (simp add: greaterThanAtMost_def)

lemma atLeastAtMost_iff [simp]:
  "(i \<in> {l..u}) = (l \<le> i \<and> i \<le> u)"
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

context order
begin

lemma atLeastatMost_empty[simp]:
  "b < a \<Longrightarrow> {a..b} = {}"
by(auto simp: atLeastAtMost_def atLeast_def atMost_def)

lemma atLeastatMost_empty_iff[simp]:
  "{a..b} = {} \<longleftrightarrow> (\<not> a \<le> b)"
by auto (blast intro: order_trans)

lemma atLeastatMost_empty_iff2[simp]:
  "{} = {a..b} \<longleftrightarrow> (\<not> a \<le> b)"
by auto (blast intro: order_trans)

lemma atLeastLessThan_empty[simp]:
  "b <= a \<Longrightarrow> {a..<b} = {}"
by(auto simp: atLeastLessThan_def)

lemma atLeastLessThan_empty_iff[simp]:
  "{a..<b} = {} \<longleftrightarrow> (\<not> a < b)"
by auto (blast intro: le_less_trans)

lemma atLeastLessThan_empty_iff2[simp]:
  "{} = {a..<b} \<longleftrightarrow> (\<not> a < b)"
by auto (blast intro: le_less_trans)

lemma greaterThanAtMost_empty[simp]: "l \<le> k ==> {k<..l} = {}"
by(auto simp:greaterThanAtMost_def greaterThan_def atMost_def)

lemma greaterThanAtMost_empty_iff[simp]: "{k<..l} = {} \<longleftrightarrow> \<not> k < l"
by auto (blast intro: less_le_trans)

lemma greaterThanAtMost_empty_iff2[simp]: "{} = {k<..l} \<longleftrightarrow> \<not> k < l"
by auto (blast intro: less_le_trans)

lemma greaterThanLessThan_empty[simp]:"l \<le> k ==> {k<..<l} = {}"
by(auto simp:greaterThanLessThan_def greaterThan_def lessThan_def)

lemma atLeastAtMost_singleton [simp]: "{a..a} = {a}"
by (auto simp add: atLeastAtMost_def atMost_def atLeast_def)

lemma atLeastAtMost_singleton': "a = b \<Longrightarrow> {a .. b} = {a}" by simp

lemma atLeastatMost_subset_iff[simp]:
  "{a..b} \<le> {c..d} \<longleftrightarrow> (\<not> a \<le> b) \<or> c \<le> a \<and> b \<le> d"
unfolding atLeastAtMost_def atLeast_def atMost_def
by (blast intro: order_trans)

lemma atLeastatMost_psubset_iff:
  "{a..b} < {c..d} \<longleftrightarrow>
   ((\<not> a \<le> b) \<or> c \<le> a \<and> b \<le> d \<and> (c < a \<or> b < d)) \<and> c \<le> d"
by(simp add: psubset_eq set_eq_iff less_le_not_le)(blast intro: order_trans)

lemma Icc_eq_Icc[simp]:
  "{l..h} = {l'..h'} = (l=l' \<and> h=h' \<or> \<not> l\<le>h \<and> \<not> l'\<le>h')"
by(simp add: order_class.eq_iff)(auto intro: order_trans)

lemma atLeastAtMost_singleton_iff[simp]:
  "{a .. b} = {c} \<longleftrightarrow> a = b \<and> b = c"
proof
  assume "{a..b} = {c}"
  hence *: "\<not> (\<not> a \<le> b)" unfolding atLeastatMost_empty_iff[symmetric] by simp
  with \<open>{a..b} = {c}\<close> have "c \<le> a \<and> b \<le> c" by auto
  with * show "a = b \<and> b = c" by auto
qed simp

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

lemma atLeastAtMost_subseteq_atLeastLessThan_iff:
  "{a .. b} \<subseteq> { c ..< d } \<longleftrightarrow> (a \<le> b \<longrightarrow> c \<le> a \<and> b < d)"
  using dense[of "max a d" "b"]
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
apply (auto simp:subset_eq Ball_def)
apply(frule_tac x=a in spec)
apply(erule_tac x=d in allE)
apply (simp add: less_imp_le)
done

lemma atLeastLessThan_inj:
  fixes a b c d :: "'a::linorder"
  assumes eq: "{a ..< b} = {c ..< d}" and "a < b" "c < d"
  shows "a = c" "b = d"
using assms by (metis atLeastLessThan_subset_iff eq less_le_not_le linorder_antisym_conv2 subset_refl)+

lemma atLeastLessThan_eq_iff:
  fixes a b c d :: "'a::linorder"
  assumes "a < b" "c < d"
  shows "{a ..< b} = {c ..< d} \<longleftrightarrow> a = c \<and> b = d"
  using atLeastLessThan_inj assms by auto

lemma (in linorder) Ioc_inj: "{a <.. b} = {c <.. d} \<longleftrightarrow> (b \<le> a \<and> d \<le> c) \<or> a = c \<and> b = d"
  by (metis eq_iff greaterThanAtMost_empty_iff2 greaterThanAtMost_iff le_cases not_le)

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

lemma Iio_eq_empty_iff_nat: "{..< n::nat} = {} \<longleftrightarrow> n = 0"
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

subsubsection \<open>The Constant @{term lessThan}\<close>

lemma lessThan_0 [simp]: "lessThan (0::nat) = {}"
by (simp add: lessThan_def)

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
by (simp add: lessThan_def less_Suc_eq, blast)

text \<open>The following proof is convenient in induction proofs where
new elements get indices at the beginning. So it is used to transform
@{term "{..<Suc n}"} to @{term "0::nat"} and @{term "{..< n}"}.\<close>

lemma zero_notin_Suc_image: "0 \<notin> Suc ` A"
  by auto

lemma lessThan_Suc_eq_insert_0: "{..<Suc n} = insert 0 (Suc ` {..<n})"
  by (auto simp: image_iff less_Suc_eq_0_disj)

lemma lessThan_Suc_atMost: "lessThan (Suc k) = atMost k"
by (simp add: lessThan_def atMost_def less_Suc_eq_le)

lemma Iic_Suc_eq_insert_0: "{.. Suc n} = insert 0 (Suc ` {.. n})"
  unfolding lessThan_Suc_atMost[symmetric] lessThan_Suc_eq_insert_0[of "Suc n"] ..

lemma UN_lessThan_UNIV: "(UN m::nat. lessThan m) = UNIV"
by blast

subsubsection \<open>The Constant @{term greaterThan}\<close>

lemma greaterThan_0: "greaterThan 0 = range Suc"
apply (simp add: greaterThan_def)
apply (blast dest: gr0_conv_Suc [THEN iffD1])
done

lemma greaterThan_Suc: "greaterThan (Suc k) = greaterThan k - {Suc k}"
apply (simp add: greaterThan_def)
apply (auto elim: linorder_neqE)
done

lemma INT_greaterThan_UNIV: "(INT m::nat. greaterThan m) = {}"
by blast

subsubsection \<open>The Constant @{term atLeast}\<close>

lemma atLeast_0 [simp]: "atLeast (0::nat) = UNIV"
by (unfold atLeast_def UNIV_def, simp)

lemma atLeast_Suc: "atLeast (Suc k) = atLeast k - {k}"
apply (simp add: atLeast_def)
apply (simp add: Suc_le_eq)
apply (simp add: order_le_less, blast)
done

lemma atLeast_Suc_greaterThan: "atLeast (Suc k) = greaterThan k"
  by (auto simp add: greaterThan_def atLeast_def less_Suc_eq_le)

lemma UN_atLeast_UNIV: "(UN m::nat. atLeast m) = UNIV"
by blast

subsubsection \<open>The Constant @{term atMost}\<close>

lemma atMost_0 [simp]: "atMost (0::nat) = {0}"
by (simp add: atMost_def)

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
apply (simp add: atMost_def)
apply (simp add: less_Suc_eq order_le_less, blast)
done

lemma UN_atMost_UNIV: "(UN m::nat. atMost m) = UNIV"
by blast

subsubsection \<open>The Constant @{term atLeastLessThan}\<close>

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

lemma lessThan_atLeast0:
  "{..<n} = {0::nat..<n}"
  by (simp add: atLeast0LessThan)

lemma atMost_atLeast0:
  "{..n} = {0::nat..n}"
  by (simp add: atLeast0AtMost)

lemma atLeastLessThan0: "{m..<0::nat} = {}"
by (simp add: atLeastLessThan_def)

lemma atLeast0_lessThan_Suc:
  "{0..<Suc n} = insert n {0..<n}"
  by (simp add: atLeast0LessThan lessThan_Suc)

lemma atLeast0_lessThan_Suc_eq_insert_0:
  "{0..<Suc n} = insert 0 (Suc ` {0..<n})"
  by (simp add: atLeast0LessThan lessThan_Suc_eq_insert_0)


subsubsection \<open>The Constant @{term atLeastAtMost}\<close>

lemma atLeast0_atMost_Suc:
  "{0..Suc n} = insert (Suc n) {0..n}"
  by (simp add: atLeast0AtMost atMost_Suc)

lemma atLeast0_atMost_Suc_eq_insert_0:
  "{0..Suc n} = insert 0 (Suc ` {0..n})"
  by (simp add: atLeast0AtMost Iic_Suc_eq_insert_0)


subsubsection \<open>Intervals of nats with @{term Suc}\<close>

text\<open>Not a simprule because the RHS is too messy.\<close>
lemma atLeastLessThanSuc:
    "{m..<Suc n} = (if m \<le> n then insert n {m..<n} else {})"
by (auto simp add: atLeastLessThan_def)

lemma atLeastLessThan_singleton [simp]: "{m..<Suc m} = {m}"
by (auto simp add: atLeastLessThan_def)
(*
lemma atLeast_sum_LessThan [simp]: "{m + k..<k::nat} = {}"
by (induct k, simp_all add: atLeastLessThanSuc)

lemma atLeastSucLessThan [simp]: "{Suc n..<n} = {}"
by (auto simp add: atLeastLessThan_def)
*)
lemma atLeastLessThanSuc_atLeastAtMost: "{l..<Suc u} = {l..u}"
  by (simp add: lessThan_Suc_atMost atLeastAtMost_def atLeastLessThan_def)

lemma atLeastSucAtMost_greaterThanAtMost: "{Suc l..u} = {l<..u}"
  by (simp add: atLeast_Suc_greaterThan atLeastAtMost_def
    greaterThanAtMost_def)

lemma atLeastSucLessThan_greaterThanLessThan: "{Suc l..<u} = {l<..<u}"
  by (simp add: atLeast_Suc_greaterThan atLeastLessThan_def
    greaterThanLessThan_def)

lemma atLeastAtMostSuc_conv: "m \<le> Suc n \<Longrightarrow> {m..Suc n} = insert (Suc n) {m..n}"
by (auto simp add: atLeastAtMost_def)

lemma atLeastAtMost_insertL: "m \<le> n \<Longrightarrow> insert m {Suc m..n} = {m ..n}"
by auto

text \<open>The analogous result is useful on @{typ int}:\<close>
(* here, because we don't have an own int section *)
lemma atLeastAtMostPlus1_int_conv:
  "m <= 1+n \<Longrightarrow> {m..1+n} = insert (1+n) {m..n::int}"
  by (auto intro: set_eqI)

lemma atLeastLessThan_add_Un: "i \<le> j \<Longrightarrow> {i..<j+k} = {i..<j} \<union> {j..<j+k::nat}"
  apply (induct k)
  apply (simp_all add: atLeastLessThanSuc)
  done


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

context linordered_field begin

lemma image_mult_atLeastAtMost [simp]:
  "(( * ) d ` {a..b}) = {d*a..d*b}" if "d>0"
  using that
  by (auto simp: field_simps mult_le_cancel_right intro: rev_image_eqI [where x="x/d" for x])

lemma image_mult_atLeastAtMost_if:
  "( * ) c ` {x .. y} =
    (if c > 0 then {c * x .. c * y} else if x \<le> y then {c * y .. c * x} else {})"
proof -
  consider "c < 0" "x \<le> y" | "c = 0" "x \<le> y" | "c > 0" "x \<le> y" | "x > y"
    using local.antisym_conv3 local.leI by blast
  then show ?thesis
  proof cases
    case 1
    have "( * ) c ` {x .. y} = uminus ` ( * ) (- c) ` {x .. y}"
      by (simp add: image_image)
    also have "\<dots> = {c * y .. c * x}"
      using \<open>c < 0\<close>
      by simp
    finally show ?thesis
      using \<open>c < 0\<close> by auto
  qed (auto simp: not_le local.mult_less_cancel_left_pos)
qed

lemma image_mult_atLeastAtMost_if':
  "(\<lambda>x. x * c) ` {x..y} =
    (if x \<le> y then if c > 0 then {x * c .. y * c} else {y * c .. x * c} else {})"
  by (subst mult.commute)
    (simp add: image_mult_atLeastAtMost_if mult.commute mult_le_cancel_left_pos)

lemma image_affinity_atLeastAtMost:
  "((\<lambda>x. m*x + c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 \<le> m then {m*a + c .. m *b + c}
            else {m*b + c .. m*a + c})"
proof -
  have "(\<lambda>x. m*x + c) = ((\<lambda>x. x + c) o ( * ) m)"
    unfolding image_comp[symmetric]
    by (simp add: o_def)
  then show ?thesis
    by (auto simp add: image_comp[symmetric] image_mult_atLeastAtMost_if mult_le_cancel_left)
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
    "(%x. x + (l::int)) ` {0..<u-l} = {l..<u}"
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
apply (rule finite_subset)
 apply (rule_tac [2] finite_lessThan, auto)
done

text \<open>A set of natural numbers is finite iff it is bounded.\<close>
lemma finite_nat_set_iff_bounded:
  "finite(N::nat set) = (\<exists>m. \<forall>n\<in>N. n<m)" (is "?F = ?B")
proof
  assume f:?F  show ?B
    using Max_ge[OF \<open>?F\<close>, simplified less_Suc_eq_le[symmetric]] by blast
next
  assume ?B show ?F using \<open>?B\<close> by(blast intro:bounded_nat_set_is_finite)
qed

lemma finite_nat_set_iff_bounded_le:
  "finite(N::nat set) = (\<exists>m. \<forall>n\<in>N. n<=m)"
apply(simp add:finite_nat_set_iff_bounded)
apply(blast dest:less_imp_le_nat le_imp_less_Suc)
done

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
    with insert have "A <= {k..<k + card A}" and "b = k + card A"
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
  apply (rule subset_antisym)
   apply (rule UN_finite2_subset, blast)
  apply (rule UN_finite2_subset [where k=k])
  apply (force simp add: atLeastLessThan_add_Un [of 0])
  done


subsubsection \<open>Cardinality\<close>

lemma card_lessThan [simp]: "card {..<u} = u"
  by (induct u, simp_all add: lessThan_Suc)

lemma card_atMost [simp]: "card {..u} = Suc u"
  by (simp add: lessThan_Suc_atMost [THEN sym])

lemma card_atLeastLessThan [simp]: "card {l..<u} = u - l"
proof -
  have "{l..<u} = (%x. x + l) ` {..<u-l}"
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

lemma inj_on_iff_card_le:
  assumes FIN: "finite A" and FIN': "finite B"
  shows "(\<exists>f. inj_on f A \<and> f ` A \<le> B) = (card A \<le> card B)"
proof (safe intro!: card_inj_on_le)
  assume *: "card A \<le> card B"
  obtain f where 1: "inj_on f A" and 2: "f ` A = {0 ..< card A}"
  using FIN ex_bij_betw_finite_nat unfolding bij_betw_def by force
  moreover obtain g where "inj_on g {0 ..< card B}" and 3: "g ` {0 ..< card B} = B"
  using FIN' ex_bij_betw_nat_finite unfolding bij_betw_def by force
  ultimately have "inj_on g (f ` A)" using subset_inj_on[of g _ "f ` A"] * by force
  hence "inj_on (g \<circ> f) A" using 1 comp_inj_on by blast
  moreover
  {have "{0 ..< card A} \<le> {0 ..< card B}" using * by force
   with 2 have "f ` A  \<le> {0 ..< card B}" by blast
   hence "(g \<circ> f) ` A \<le> B" unfolding comp_def using 3 by force
  }
  ultimately show "(\<exists>f. inj_on f A \<and> f ` A \<le> B)" by blast
qed (insert assms, auto)

lemma subset_eq_atLeast0_lessThan_card:
  fixes n :: nat
  assumes "N \<subseteq> {0..<n}"
  shows "card N \<le> n"
proof -
  from assms finite_lessThan have "card N \<le> card {0..<n}"
    using card_mono by blast
  then show ?thesis by simp
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
  apply (unfold image_def lessThan_def)
  apply auto
  apply (rule_tac x = "nat x" in exI)
  apply (auto simp add: zless_nat_eq_int_zless [THEN sym])
  done

lemma finite_atLeastZeroLessThan_int: "finite {(0::int)..<u}"
  apply (cases "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_int, assumption)
  apply (rule finite_imageI)
  apply auto
  done

lemma finite_atLeastLessThan_int [iff]: "finite {l..<u::int}"
  apply (subgoal_tac "(%x. x + l) ` {0..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule finite_imageI)
  apply (rule finite_atLeastZeroLessThan_int)
  apply (rule image_add_int_atLeastLessThan)
  done

lemma finite_atLeastAtMost_int [iff]: "finite {l..(u::int)}"
  by (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym], simp)

lemma finite_greaterThanAtMost_int [iff]: "finite {l<..(u::int)}"
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma finite_greaterThanLessThan_int [iff]: "finite {l<..<u::int}"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)


subsubsection \<open>Cardinality\<close>

lemma card_atLeastZeroLessThan_int: "card {(0::int)..<u} = nat u"
  apply (cases "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_int, assumption)
  apply (subst card_image)
  apply (auto simp add: inj_on_def)
  done

lemma card_atLeastLessThan_int [simp]: "card {l..<u} = nat (u - l)"
  apply (subgoal_tac "card {l..<u} = card {0..<u-l}")
  apply (erule ssubst, rule card_atLeastZeroLessThan_int)
  apply (subgoal_tac "(%x. x + l) ` {0..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule card_image)
  apply (simp add: inj_on_def)
  apply (rule image_add_int_atLeastLessThan)
  done

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

lemma card_less_Suc2: "0 \<notin> M \<Longrightarrow> card {k. Suc k \<in> M \<and> k < i} = card {k \<in> M. k < Suc i}"
apply (rule card_bij_eq [of Suc _ _ "\<lambda>x. x - Suc 0"])
apply auto
apply (rule inj_on_diff_nat)
apply auto
apply (case_tac x)
apply auto
apply (case_tac xa)
apply auto
apply (case_tac xa)
apply auto
done

lemma card_less_Suc:
  assumes zero_in_M: "0 \<in> M"
    shows "Suc (card {k. Suc k \<in> M \<and> k < i}) = card {k \<in> M. k < Suc i}"
proof -
  from assms have a: "0 \<in> {k \<in> M. k < Suc i}" by simp
  hence c: "{k \<in> M. k < Suc i} = insert 0 ({k \<in> M. k < Suc i} - {0})"
    by (auto simp only: insert_Diff)
  have b: "{k \<in> M. k < Suc i} - {0} = {k \<in> M - {0}. k < Suc i}"  by auto
  from finite_M_bounded_by_nat[of "\<lambda>x. x \<in> M" "Suc i"]
  have "Suc (card {k. Suc k \<in> M \<and> k < i}) = card (insert 0 ({k \<in> M. k < Suc i} - {0}))"
    apply (subst card_insert)
    apply simp_all
    apply (subst b)
    apply (subst card_less_Suc2[symmetric])
    apply simp_all
    done
  with c show ?thesis by simp
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
  "(l::'a::linorder) <= u ==> {l} Un {l<..u} = {l..u}"
  "(l::'a::linorder) <= u ==> {l..<u} Un {u} = {l..u}"
by auto

text \<open>One- and two-sided intervals\<close>

lemma ivl_disj_un_one:
  "(l::'a::linorder) < u ==> {..l} Un {l<..<u} = {..<u}"
  "(l::'a::linorder) <= u ==> {..<l} Un {l..<u} = {..<u}"
  "(l::'a::linorder) <= u ==> {..l} Un {l<..u} = {..u}"
  "(l::'a::linorder) <= u ==> {..<l} Un {l..u} = {..u}"
  "(l::'a::linorder) <= u ==> {l<..u} Un {u<..} = {l<..}"
  "(l::'a::linorder) < u ==> {l<..<u} Un {u..} = {l<..}"
  "(l::'a::linorder) <= u ==> {l..u} Un {u<..} = {l..}"
  "(l::'a::linorder) <= u ==> {l..<u} Un {u..} = {l..}"
by auto

text \<open>Two- and two-sided intervals\<close>

lemma ivl_disj_un_two:
  "[| (l::'a::linorder) < m; m <= u |] ==> {l<..<m} Un {m..<u} = {l<..<u}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {l<..m} Un {m<..<u} = {l<..<u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..<m} Un {m..<u} = {l..<u}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {l..m} Un {m<..<u} = {l..<u}"
  "[| (l::'a::linorder) < m; m <= u |] ==> {l<..<m} Un {m..u} = {l<..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l<..m} Un {m<..u} = {l<..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..<m} Un {m..u} = {l..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..m} Un {m<..u} = {l..u}"
by auto

lemma ivl_disj_un_two_touch:
  "[| (l::'a::linorder) < m; m < u |] ==> {l<..m} Un {m..<u} = {l<..<u}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {l..m} Un {m..<u} = {l..<u}"
  "[| (l::'a::linorder) < m; m <= u |] ==> {l<..m} Un {m..u} = {l<..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..m} Un {m..u} = {l..u}"
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

lemma ivl_subset [simp]:
 "({i..<j} \<subseteq> {m..<n}) = (j \<le> i \<or> m \<le> i \<and> j \<le> (n::'a::linorder))"
apply(auto simp:linorder_not_le)
apply(rule ccontr)
apply(insert linorder_le_less_linear[of i n])
apply(clarsimp simp:linorder_not_le)
apply(fastforce)
done


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
@{term[source]"\<Sum>x\<in>{a..b}. e"} & @{term"\<Sum>x=a..b. e"} & @{term[mode=latex_sum]"\<Sum>x=a..b. e"}\\
@{term[source]"\<Sum>x\<in>{a..<b}. e"} & @{term"\<Sum>x=a..<b. e"} & @{term[mode=latex_sum]"\<Sum>x=a..<b. e"}\\
@{term[source]"\<Sum>x\<in>{..b}. e"} & @{term"\<Sum>x\<le>b. e"} & @{term[mode=latex_sum]"\<Sum>x\<le>b. e"}\\
@{term[source]"\<Sum>x\<in>{..<b}. e"} & @{term"\<Sum>x<b. e"} & @{term[mode=latex_sum]"\<Sum>x<b. e"}
\end{tabular}
\end{center}
The left column shows the term before introduction of the new syntax,
the middle column shows the new (default) syntax, and the right column
shows a special syntax. The latter is only meaningful for latex output
and has to be activated explicitly by setting the print mode to
\<open>latex_sum\<close> (e.g.\ via \<open>mode = latex_sum\<close> in
antiquotations). It is not the default \LaTeX\ output because it only
works well with italic-style formulae, not tt-style.

Note that for uniformity on @{typ nat} it is better to use
@{term"\<Sum>x::nat=0..<n. e"} rather than \<open>\<Sum>x<n. e\<close>: \<open>sum\<close> may
not provide all lemmas available for @{term"{m..<n}"} also in the
special form for @{term"{..<n}"}.\<close>

text\<open>This congruence rule should be used for sums over intervals as
the standard theorem @{text[source]sum.cong} does not work well
with the simplifier who adds the unsimplified premise @{term"x\<in>B"} to
the context.\<close>

lemmas sum_ivl_cong = sum.ivl_cong

(* FIXME why are the following simp rules but the corresponding eqns
on intervals are not? *)

lemma sum_atMost_Suc [simp]:
  "(\<Sum>i \<le> Suc n. f i) = (\<Sum>i \<le> n. f i) + f (Suc n)"
  by (simp add: atMost_Suc ac_simps)

lemma sum_lessThan_Suc [simp]:
  "(\<Sum>i < Suc n. f i) = (\<Sum>i < n. f i) + f n"
  by (simp add: lessThan_Suc ac_simps)

lemma sum_cl_ivl_Suc [simp]:
  "sum f {m..Suc n} = (if Suc n < m then 0 else sum f {m..n} + f(Suc n))"
  by (auto simp: ac_simps atLeastAtMostSuc_conv)

lemma sum_op_ivl_Suc [simp]:
  "sum f {m..<Suc n} = (if n < m then 0 else sum f {m..<n} + f(n))"
  by (auto simp: ac_simps atLeastLessThanSuc)
(*
lemma sum_cl_ivl_add_one_nat: "(n::nat) <= m + 1 ==>
    (\<Sum>i=n..m+1. f i) = (\<Sum>i=n..m. f i) + f(m + 1)"
by (auto simp:ac_simps atLeastAtMostSuc_conv)
*)

lemma sum_head:
  fixes n :: nat
  assumes mn: "m <= n"
  shows "(\<Sum>x\<in>{m..n}. P x) = P m + (\<Sum>x\<in>{m<..n}. P x)" (is "?lhs = ?rhs")
proof -
  from mn
  have "{m..n} = {m} \<union> {m<..n}"
    by (auto intro: ivl_disj_un_singleton)
  hence "?lhs = (\<Sum>x\<in>{m} \<union> {m<..n}. P x)"
    by (simp add: atLeast0LessThan)
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed

lemma sum_head_Suc:
  "m \<le> n \<Longrightarrow> sum f {m..n} = f m + sum f {Suc m..n}"
  by (fact sum.atLeast_Suc_atMost)

lemma sum_head_upt_Suc:
  "m < n \<Longrightarrow> sum f {m..<n} = f m + sum f {Suc m..<n}"
  by (fact sum.atLeast_Suc_lessThan)

lemma sum_ub_add_nat: assumes "(m::nat) \<le> n + 1"
  shows "sum f {m..n + p} = sum f {m..n} + sum f {n + 1..n + p}"
proof-
  have "{m .. n+p} = {m..n} \<union> {n+1..n+p}" using \<open>m \<le> n+1\<close> by auto
  thus ?thesis by (auto simp: ivl_disj_int sum.union_disjoint
    atLeastSucAtMost_greaterThanAtMost)
qed

lemmas sum_add_nat_ivl = sum.atLeastLessThan_concat

lemma sum_diff_nat_ivl:
fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
shows "\<lbrakk> m \<le> n; n \<le> p \<rbrakk> \<Longrightarrow>
  sum f {m..<p} - sum f {m..<n} = sum f {n..<p}"
using sum_add_nat_ivl [of m n p f,symmetric]
apply (simp add: ac_simps)
done

lemma sum_natinterval_difff:
  fixes f:: "nat \<Rightarrow> ('a::ab_group_add)"
  shows  "sum (\<lambda>k. f k - f(k + 1)) {(m::nat) .. n} =
          (if m <= n then f m - f(n + 1) else 0)"
by (induct n, auto simp add: algebra_simps not_le le_Suc_eq)

lemma sum_nat_group: "(\<Sum>m<n::nat. sum f {m * k ..< m*k + k}) = sum f {..< n * k}"
  apply (subgoal_tac "k = 0 \<or> 0 < k", auto)
  apply (induct "n")
  apply (simp_all add: sum_add_nat_ivl add.commute atLeast0LessThan[symmetric])
  done

lemma sum_triangle_reindex:
  fixes n :: nat
  shows "(\<Sum>(i,j)\<in>{(i,j). i+j < n}. f i j) = (\<Sum>k<n. \<Sum>i\<le>k. f i (k - i))"
  apply (simp add: sum.Sigma)
  apply (rule sum.reindex_bij_witness[where j="\<lambda>(i, j). (i+j, i)" and i="\<lambda>(k, i). (i, k - i)"])
  apply auto
  done

lemma sum_triangle_reindex_eq:
  fixes n :: nat
  shows "(\<Sum>(i,j)\<in>{(i,j). i+j \<le> n}. f i j) = (\<Sum>k\<le>n. \<Sum>i\<le>k. f i (k - i))"
using sum_triangle_reindex [of f "Suc n"]
by (simp only: Nat.less_Suc_eq_le lessThan_Suc_atMost)

lemma nat_diff_sum_reindex: "(\<Sum>i<n. f (n - Suc i)) = (\<Sum>i<n. f i)"
  by (rule sum.reindex_bij_witness[where i="\<lambda>i. n - Suc i" and j="\<lambda>i. n - Suc i"]) auto

lemma sum_diff_distrib: "\<forall>x. Q x \<le> P x  \<Longrightarrow> (\<Sum>x<n. P x) - (\<Sum>x<n. Q x) = (\<Sum>x<n. P x - Q x :: nat)"
  by (subst sum_subtractf_nat) auto

context semiring_parity
begin

lemma take_bit_sum:
  "take_bit n a = (\<Sum>k = 0..<n. push_bit k (of_bool (odd (drop_bit k a))))"
  for n :: nat
proof (induction n arbitrary: a)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "(\<Sum>k = 0..<Suc n. push_bit k (of_bool (odd (drop_bit k a)))) = 
    of_bool (odd a) + (\<Sum>k = Suc 0..<Suc n. push_bit k (of_bool (odd (drop_bit k a))))"
    by (simp add: sum.atLeast_Suc_lessThan ac_simps)
  also have "(\<Sum>k = Suc 0..<Suc n. push_bit k (of_bool (odd (drop_bit k a))))
    = (\<Sum>k = 0..<n. push_bit k (of_bool (odd (drop_bit k (a div 2))))) * 2"
    by (simp only: sum.atLeast_Suc_lessThan_Suc_shift) (simp add: sum_distrib_right push_bit_double)
  finally show ?case
    using Suc [of "a div 2"] by (simp add: ac_simps)
qed

end


subsubsection \<open>Shifting bounds\<close>

lemma sum_shift_bounds_nat_ivl:
  "sum f {m+k..<n+k} = sum (%i. f(i + k)){m..<n::nat}"
by (induct "n", auto simp:atLeastLessThanSuc)

lemma sum_shift_bounds_cl_nat_ivl:
  "sum f {m+k..n+k} = sum (%i. f(i + k)){m..n::nat}"
  by (rule sum.reindex_bij_witness[where i="\<lambda>i. i + k" and j="\<lambda>i. i - k"]) auto

corollary sum_shift_bounds_cl_Suc_ivl:
  "sum f {Suc m..Suc n} = sum (%i. f(Suc i)){m..n}"
by (simp add:sum_shift_bounds_cl_nat_ivl[where k="Suc 0", simplified])

corollary sum_shift_bounds_Suc_ivl:
  "sum f {Suc m..<Suc n} = sum (%i. f(Suc i)){m..<n}"
by (simp add:sum_shift_bounds_nat_ivl[where k="Suc 0", simplified])

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

lemma sum_shift_lb_Suc0_0:
  "sum f {Suc 0..k} = sum f {0..k}"
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

lemma sum_atMost_Suc_shift:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<le>Suc n. f i) = f 0 + (\<Sum>i\<le>n. f (Suc i))"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) note IH = this
  have "(\<Sum>i\<le>Suc (Suc n). f i) = (\<Sum>i\<le>Suc n. f i) + f (Suc (Suc n))"
    by (rule sum_atMost_Suc)
  also have "(\<Sum>i\<le>Suc n. f i) = f 0 + (\<Sum>i\<le>n. f (Suc i))"
    by (rule IH)
  also have "f 0 + (\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)) =
             f 0 + ((\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)))"
    by (rule add.assoc)
  also have "(\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)) = (\<Sum>i\<le>Suc n. f (Suc i))"
    by (rule sum_atMost_Suc [symmetric])
  finally show ?case .
qed

lemma sum_lessThan_Suc_shift:
  "(\<Sum>i<Suc n. f i) = f 0 + (\<Sum>i<n. f (Suc i))"
  by (induction n) (simp_all add: add_ac)

lemma sum_atMost_shift:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<le>n. f i) = f 0 + (\<Sum>i<n. f (Suc i))"
by (metis atLeast0AtMost atLeast0LessThan atLeastLessThanSuc_atLeastAtMost atLeastSucAtMost_greaterThanAtMost le0 sum_head sum_shift_bounds_Suc_ivl)

lemma sum_last_plus: fixes n::nat shows "m <= n \<Longrightarrow> (\<Sum>i = m..n. f i) = f n + (\<Sum>i = m..<n. f i)"
  by (cases n) (auto simp: atLeastLessThanSuc_atLeastAtMost add.commute)

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

lemma nested_sum_swap:
     "(\<Sum>i = 0..n. (\<Sum>j = 0..<i. a i j)) = (\<Sum>j = 0..<n. \<Sum>i = Suc j..n. a i j)"
  by (induction n) (auto simp: sum.distrib)

lemma nested_sum_swap':
     "(\<Sum>i\<le>n. (\<Sum>j<i. a i j)) = (\<Sum>j<n. \<Sum>i = Suc j..n. a i j)"
  by (induction n) (auto simp: sum.distrib)

lemma sum_atLeast1_atMost_eq:
  "sum f {Suc 0..n} = (\<Sum>k<n. f (Suc k))"
proof -
  have "sum f {Suc 0..n} = sum f (Suc ` {..<n})"
    by (simp add: image_Suc_lessThan)
  also have "\<dots> = (\<Sum>k<n. f (Suc k))"
    by (simp add: sum.reindex)
  finally show ?thesis .
qed


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
  shows   "x^n - y^n = (x - y) * (\<Sum>i<n. y^(n - Suc i) * x^i)"
using diff_power_eq_sum[of x "n - 1" y]
by (cases "n = 0") (simp_all add: field_simps)

lemma power_diff_1_eq:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "n \<noteq> 0 \<Longrightarrow> x^n - 1 = (x - 1) * (\<Sum>i<n. (x^i))"
using diff_power_eq_sum [of x _ 1]
  by (cases n) auto

lemma one_diff_power_eq':
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "n \<noteq> 0 \<Longrightarrow> 1 - x^n = (1 - x) * (\<Sum>i<n. x^(n - Suc i))"
using diff_power_eq_sum [of 1 _ x]
  by (cases n) auto

lemma one_diff_power_eq:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "n \<noteq> 0 \<Longrightarrow> 1 - x^n = (1 - x) * (\<Sum>i<n. x^i)"
by (metis one_diff_power_eq' [of n x] nat_diff_sum_reindex)

lemma sum_gp_basic:
  fixes x :: "'a::{comm_ring,monoid_mult}"
  shows "(1 - x) * (\<Sum>i\<le>n. x^i) = 1 - x^Suc n"
  by (simp only: one_diff_power_eq [of "Suc n" x] lessThan_Suc_atMost)

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
  shows   "(\<Sum>i\<le>n. x^i) = (if x = 1 then of_nat(n + 1) else (1 - x^Suc n) / (1 - x))"
  using sum_gp_basic[of x n]
  by (simp add: mult.commute divide_simps)

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
  by (induct n) (auto simp: algebra_simps divide_simps)


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

context semiring_parity
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
  "\<Sum>{m..n} = (n * (n + 1) - m * (m - 1)) div 2"
  if "m \<le> n" for m n :: nat
proof -
  have *: "m * (m - 1) \<le> n * (n + 1)"
    using that by (meson diff_le_self order_trans le_add1 mult_le_mono)
  have "int (\<Sum>{m..n}) = (\<Sum>{int m..int n})"
    by (simp add: sum.atLeast_int_atMost_int_shift)
  also have "\<dots> = (int n * (int n + 1) - int m * (int m - 1)) div 2"
    using that by (simp add: Sum_Icc_int)
  also have "\<dots> = int ((n * (n + 1) - m * (m - 1)) div 2)"
    using le_square * by (simp add: algebra_simps of_nat_div of_nat_diff)
  finally show ?thesis
    by (simp only: of_nat_eq_iff)
qed

lemma Sum_Ico_nat: 
  "\<Sum>{m..<n} = (n * (n - 1) - m * (m - 1)) div 2"
  if "m \<le> n" for m n :: nat
proof -
  from that consider "m < n" | "m = n"
    by (auto simp add: less_le)
  then show ?thesis proof cases
    case 1
    then have "{m..<n} = {m..n - 1}"
      by auto
    then have "\<Sum>{m..<n} = \<Sum>{m..n - 1}"
      by simp
    also have "\<dots> = (n * (n - 1) - m * (m - 1)) div 2"
      using \<open>m < n\<close> by (simp add: Sum_Icc_nat mult.commute)
    finally show ?thesis .
  next
    case 2
    then show ?thesis
      by simp
  qed
qed


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


subsubsection \<open>Shifting bounds\<close>

lemma prod_shift_bounds_nat_ivl:
  "prod f {m+k..<n+k} = prod (%i. f(i + k)){m..<n::nat}"
by (induct "n", auto simp:atLeastLessThanSuc)

lemma prod_shift_bounds_cl_nat_ivl:
  "prod f {m+k..n+k} = prod (%i. f(i + k)){m..n::nat}"
  by (rule prod.reindex_bij_witness[where i="\<lambda>i. i + k" and j="\<lambda>i. i - k"]) auto

corollary prod_shift_bounds_cl_Suc_ivl:
  "prod f {Suc m..Suc n} = prod (%i. f(Suc i)){m..n}"
by (simp add:prod_shift_bounds_cl_nat_ivl[where k="Suc 0", simplified])

corollary prod_shift_bounds_Suc_ivl:
  "prod f {Suc m..<Suc n} = prod (%i. f(Suc i)){m..<n}"
by (simp add:prod_shift_bounds_nat_ivl[where k="Suc 0", simplified])

lemma prod_lessThan_Suc: "prod f {..<Suc n} = prod f {..<n} * f n"
  by (simp add: lessThan_Suc mult.commute)

lemma prod_lessThan_Suc_shift:"(\<Prod>i<Suc n. f i) = f 0 * (\<Prod>i<n. f (Suc i))"
  by (induction n) (simp_all add: lessThan_Suc mult_ac)

lemma prod_atLeastLessThan_Suc: "a \<le> b \<Longrightarrow> prod f {a..<Suc b} = prod f {a..<b} * f b"
  by (simp add: atLeastLessThanSuc mult.commute)

lemma prod_nat_ivl_Suc':
  assumes "m \<le> Suc n"
  shows   "prod f {m..Suc n} = f (Suc n) * prod f {m..n}"
proof -
  from assms have "{m..Suc n} = insert (Suc n) {m..n}" by auto
  also have "prod f \<dots> = f (Suc n) * prod f {m..n}" by simp
  finally show ?thesis .
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
  have "comp_fun_commute (\<lambda>a. ( * ) (f a))"
    by unfold_locales (auto simp: o_def mult_ac)
  thus ?thesis
    by (simp add: prod.eq_fold fold_atLeastAtMost_nat o_def)
qed

(* TODO: Add support for more kinds of intervals here *)

end
