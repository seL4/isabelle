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

section {* Set intervals *}

theory Set_Interval
imports Lattices_Big Nat_Transfer
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


text{* A note of warning when using @{term"{..<n}"} on type @{typ
nat}: it is equivalent to @{term"{0::nat..<n}"} but some lemmas involving
@{term"{m..<n}"} may not exist in @{term"{..<n}"}-form as well. *}

syntax
  "_UNION_le"   :: "'a => 'a => 'b set => 'b set"       ("(3UN _<=_./ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3UN _<_./ _)" [0, 0, 10] 10)
  "_INTER_le"   :: "'a => 'a => 'b set => 'b set"       ("(3INT _<=_./ _)" [0, 0, 10] 10)
  "_INTER_less" :: "'a => 'a => 'b set => 'b set"       ("(3INT _<_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_UNION_le"   :: "'a => 'a => 'b set => 'b set"       ("(3\<Union> _\<le>_./ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Union> _<_./ _)" [0, 0, 10] 10)
  "_INTER_le"   :: "'a => 'a => 'b set => 'b set"       ("(3\<Inter> _\<le>_./ _)" [0, 0, 10] 10)
  "_INTER_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Inter> _<_./ _)" [0, 0, 10] 10)

syntax (latex output)
  "_UNION_le"   :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Union>(00_ \<le> _)/ _)" [0, 0, 10] 10)
  "_UNION_less" :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Union>(00_ < _)/ _)" [0, 0, 10] 10)
  "_INTER_le"   :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Inter>(00_ \<le> _)/ _)" [0, 0, 10] 10)
  "_INTER_less" :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Inter>(00_ < _)/ _)" [0, 0, 10] 10)

translations
  "UN i<=n. A"  == "UN i:{..n}. A"
  "UN i<n. A"   == "UN i:{..<n}. A"
  "INT i<=n. A" == "INT i:{..n}. A"
  "INT i<n. A"  == "INT i:{..<n}. A"


subsection {* Various equivalences *}

lemma (in ord) lessThan_iff [iff]: "(i: lessThan k) = (i<k)"
by (simp add: lessThan_def)

lemma Compl_lessThan [simp]:
    "!!k:: 'a::linorder. -lessThan k = atLeast k"
apply (auto simp add: lessThan_def atLeast_def)
done

lemma single_Diff_lessThan [simp]: "!!k:: 'a::order. {k} - lessThan k = {k}"
by auto

lemma (in ord) greaterThan_iff [iff]: "(i: greaterThan k) = (k<i)"
by (simp add: greaterThan_def)

lemma Compl_greaterThan [simp]:
    "!!k:: 'a::linorder. -greaterThan k = atMost k"
  by (auto simp add: greaterThan_def atMost_def)

lemma Compl_atMost [simp]: "!!k:: 'a::linorder. -atMost k = greaterThan k"
apply (subst Compl_greaterThan [symmetric])
apply (rule double_complement)
done

lemma (in ord) atLeast_iff [iff]: "(i: atLeast k) = (k<=i)"
by (simp add: atLeast_def)

lemma Compl_atLeast [simp]:
    "!!k:: 'a::linorder. -atLeast k = lessThan k"
  by (auto simp add: lessThan_def atLeast_def)

lemma (in ord) atMost_iff [iff]: "(i: atMost k) = (i<=k)"
by (simp add: atMost_def)

lemma atMost_Int_atLeast: "!!n:: 'a::order. atMost n Int atLeast n = {n}"
by (blast intro: order_antisym)

lemma (in linorder) lessThan_Int_lessThan: "{ a <..} \<inter> { b <..} = { max a b <..}"
  by auto

lemma (in linorder) greaterThan_Int_greaterThan: "{..< a} \<inter> {..< b} = {..< min a b}"
  by auto

subsection {* Logical Equivalences for Set Inclusion and Equality *}

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

subsection {*Two-sided intervals*}

context ord
begin

lemma greaterThanLessThan_iff [simp]:
  "(i : {l<..<u}) = (l < i & i < u)"
by (simp add: greaterThanLessThan_def)

lemma atLeastLessThan_iff [simp]:
  "(i : {l..<u}) = (l <= i & i < u)"
by (simp add: atLeastLessThan_def)

lemma greaterThanAtMost_iff [simp]:
  "(i : {l<..u}) = (l < i & i <= u)"
by (simp add: greaterThanAtMost_def)

lemma atLeastAtMost_iff [simp]:
  "(i : {l..u}) = (l <= i & i <= u)"
by (simp add: atLeastAtMost_def)

text {* The above four lemmas could be declared as iffs. Unfortunately this
breaks many proofs. Since it only helps blast, it is better to leave them
alone. *}

lemma greaterThanLessThan_eq: "{ a <..< b} = { a <..} \<inter> {..< b }"
  by auto

end

subsubsection{* Emptyness, singletons, subset *}

context order
begin

lemma atLeastatMost_empty[simp]:
  "b < a \<Longrightarrow> {a..b} = {}"
by(auto simp: atLeastAtMost_def atLeast_def atMost_def)

lemma atLeastatMost_empty_iff[simp]:
  "{a..b} = {} \<longleftrightarrow> (~ a <= b)"
by auto (blast intro: order_trans)

lemma atLeastatMost_empty_iff2[simp]:
  "{} = {a..b} \<longleftrightarrow> (~ a <= b)"
by auto (blast intro: order_trans)

lemma atLeastLessThan_empty[simp]:
  "b <= a \<Longrightarrow> {a..<b} = {}"
by(auto simp: atLeastLessThan_def)

lemma atLeastLessThan_empty_iff[simp]:
  "{a..<b} = {} \<longleftrightarrow> (~ a < b)"
by auto (blast intro: le_less_trans)

lemma atLeastLessThan_empty_iff2[simp]:
  "{} = {a..<b} \<longleftrightarrow> (~ a < b)"
by auto (blast intro: le_less_trans)

lemma greaterThanAtMost_empty[simp]: "l \<le> k ==> {k<..l} = {}"
by(auto simp:greaterThanAtMost_def greaterThan_def atMost_def)

lemma greaterThanAtMost_empty_iff[simp]: "{k<..l} = {} \<longleftrightarrow> ~ k < l"
by auto (blast intro: less_le_trans)

lemma greaterThanAtMost_empty_iff2[simp]: "{} = {k<..l} \<longleftrightarrow> ~ k < l"
by auto (blast intro: less_le_trans)

lemma greaterThanLessThan_empty[simp]:"l \<le> k ==> {k<..<l} = {}"
by(auto simp:greaterThanLessThan_def greaterThan_def lessThan_def)

lemma atLeastAtMost_singleton [simp]: "{a..a} = {a}"
by (auto simp add: atLeastAtMost_def atMost_def atLeast_def)

lemma atLeastAtMost_singleton': "a = b \<Longrightarrow> {a .. b} = {a}" by simp

lemma atLeastatMost_subset_iff[simp]:
  "{a..b} <= {c..d} \<longleftrightarrow> (~ a <= b) | c <= a & b <= d"
unfolding atLeastAtMost_def atLeast_def atMost_def
by (blast intro: order_trans)

lemma atLeastatMost_psubset_iff:
  "{a..b} < {c..d} \<longleftrightarrow>
   ((~ a <= b) | c <= a & b <= d & (c < a | b < d))  &  c <= d"
by(simp add: psubset_eq set_eq_iff less_le_not_le)(blast intro: order_trans)

lemma Icc_eq_Icc[simp]:
  "{l..h} = {l'..h'} = (l=l' \<and> h=h' \<or> \<not> l\<le>h \<and> \<not> l'\<le>h')"
by(simp add: order_class.eq_iff)(auto intro: order_trans)

lemma atLeastAtMost_singleton_iff[simp]:
  "{a .. b} = {c} \<longleftrightarrow> a = b \<and> b = c"
proof
  assume "{a..b} = {c}"
  hence *: "\<not> (\<not> a \<le> b)" unfolding atLeastatMost_empty_iff[symmetric] by simp
  with `{a..b} = {c}` have "c \<le> a \<and> b \<le> c" by auto
  with * show "a = b \<and> b = c" by auto
qed simp

lemma Icc_subset_Ici_iff[simp]:
  "{l..h} \<subseteq> {l'..} = (~ l\<le>h \<or> l\<ge>l')"
by(auto simp: subset_eq intro: order_trans)

lemma Icc_subset_Iic_iff[simp]:
  "{l..h} \<subseteq> {..h'} = (~ l\<le>h \<or> h\<le>h')"
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
  "{a..<b} <= {c..<d} \<Longrightarrow> b <= a | c<=a & b<=d"
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


subsection {* Infinite intervals *}

context dense_linorder
begin

lemma infinite_Ioo:
  assumes "a < b"
  shows "\<not> finite {a<..<b}"
proof
  assume fin: "finite {a<..<b}"
  moreover have ne: "{a<..<b} \<noteq> {}"
    using `a < b` by auto
  ultimately have "a < Max {a <..< b}" "Max {a <..< b} < b"
    using Max_in[of "{a <..< b}"] by auto
  then obtain x where "Max {a <..< b} < x" "x < b"
    using dense[of "Max {a<..<b}" b] by auto
  then have "x \<in> {a <..< b}"
    using `a < Max {a <..< b}` by auto
  then have "x \<le> Max {a <..< b}"
    using fin by auto
  with `Max {a <..< b} < x` show False by auto
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
    using `x < a` by fact
  also note `x < a`
  finally have "Min {..< a} \<le> y"
    by fact
  with `y < Min {..< a}` show False by auto
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

  obtain x where "a < x"
    using gt_ex by auto
  also then have "x \<le> Max {a <..}"
    by fact
  also note `Max {a <..} < y`
  finally have "y \<le> Max { a <..}"
    by fact
  with `Max {a <..} < y` show False by auto
qed

lemma infinite_Ici: "\<not> finite {a :: 'a :: {no_top, linorder} ..}"
  using infinite_Ioi[of a] finite_subset[of "{a <..}" "{a ..}"]
  by (auto simp: subset_eq less_imp_le)

subsubsection {* Intersection *}

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
  using assms by auto

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

subsection {* Intervals of natural numbers *}

subsubsection {* The Constant @{term lessThan} *}

lemma lessThan_0 [simp]: "lessThan (0::nat) = {}"
by (simp add: lessThan_def)

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
by (simp add: lessThan_def less_Suc_eq, blast)

text {* The following proof is convenient in induction proofs where
new elements get indices at the beginning. So it is used to transform
@{term "{..<Suc n}"} to @{term "0::nat"} and @{term "{..< n}"}. *}

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

subsubsection {* The Constant @{term greaterThan} *}

lemma greaterThan_0 [simp]: "greaterThan 0 = range Suc"
apply (simp add: greaterThan_def)
apply (blast dest: gr0_conv_Suc [THEN iffD1])
done

lemma greaterThan_Suc: "greaterThan (Suc k) = greaterThan k - {Suc k}"
apply (simp add: greaterThan_def)
apply (auto elim: linorder_neqE)
done

lemma INT_greaterThan_UNIV: "(INT m::nat. greaterThan m) = {}"
by blast

subsubsection {* The Constant @{term atLeast} *}

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

subsubsection {* The Constant @{term atMost} *}

lemma atMost_0 [simp]: "atMost (0::nat) = {0}"
by (simp add: atMost_def)

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
apply (simp add: atMost_def)
apply (simp add: less_Suc_eq order_le_less, blast)
done

lemma UN_atMost_UNIV: "(UN m::nat. atMost m) = UNIV"
by blast

subsubsection {* The Constant @{term atLeastLessThan} *}

text{*The orientation of the following 2 rules is tricky. The lhs is
defined in terms of the rhs.  Hence the chosen orientation makes sense
in this theory --- the reverse orientation complicates proofs (eg
nontermination). But outside, when the definition of the lhs is rarely
used, the opposite orientation seems preferable because it reduces a
specific concept to a more general one. *}

lemma atLeast0LessThan: "{0::nat..<n} = {..<n}"
by(simp add:lessThan_def atLeastLessThan_def)

lemma atLeast0AtMost: "{0..n::nat} = {..n}"
by(simp add:atMost_def atLeastAtMost_def)

declare atLeast0LessThan[symmetric, code_unfold]
        atLeast0AtMost[symmetric, code_unfold]

lemma atLeastLessThan0: "{m..<0::nat} = {}"
by (simp add: atLeastLessThan_def)

subsubsection {* Intervals of nats with @{term Suc} *}

text{*Not a simprule because the RHS is too messy.*}
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

text {* The analogous result is useful on @{typ int}: *}
(* here, because we don't have an own int section *)
lemma atLeastAtMostPlus1_int_conv:
  "m <= 1+n \<Longrightarrow> {m..1+n} = insert (1+n) {m..n::int}"
  by (auto intro: set_eqI)

lemma atLeastLessThan_add_Un: "i \<le> j \<Longrightarrow> {i..<j+k} = {i..<j} \<union> {j..<j+k::nat}"
  apply (induct k) 
  apply (simp_all add: atLeastLessThanSuc)   
  done

subsubsection {* Intervals and numerals *}

lemma lessThan_nat_numeral:  --{*Evaluation for specific numerals*}
  "lessThan (numeral k :: nat) = insert (pred_numeral k) (lessThan (pred_numeral k))"
  by (simp add: numeral_eq_Suc lessThan_Suc)

lemma atMost_nat_numeral:  --{*Evaluation for specific numerals*}
  "atMost (numeral k :: nat) = insert (numeral k) (atMost (pred_numeral k))"
  by (simp add: numeral_eq_Suc atMost_Suc)

lemma atLeastLessThan_nat_numeral:  --{*Evaluation for specific numerals*}
  "atLeastLessThan m (numeral k :: nat) = 
     (if m \<le> (pred_numeral k) then insert (pred_numeral k) (atLeastLessThan m (pred_numeral k))
                 else {})"
  by (simp add: numeral_eq_Suc atLeastLessThanSuc)

subsubsection {* Image *}

lemma image_add_atLeastAtMost:
  "(%n::nat. n+k) ` {i..j} = {i+k..j+k}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" by auto
next
  show "?B \<subseteq> ?A"
  proof
    fix n assume a: "n : ?B"
    hence "n - k : {i..j}" by auto
    moreover have "n = (n - k) + k" using a by auto
    ultimately show "n : ?A" by blast
  qed
qed

lemma image_add_atLeastLessThan:
  "(%n::nat. n+k) ` {i..<j} = {i+k..<j+k}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" by auto
next
  show "?B \<subseteq> ?A"
  proof
    fix n assume a: "n : ?B"
    hence "n - k : {i..<j}" by auto
    moreover have "n = (n - k) + k" using a by auto
    ultimately show "n : ?A" by blast
  qed
qed

corollary image_Suc_atLeastAtMost[simp]:
  "Suc ` {i..j} = {Suc i..Suc j}"
using image_add_atLeastAtMost[where k="Suc 0"] by simp

corollary image_Suc_atLeastLessThan[simp]:
  "Suc ` {i..<j} = {Suc i..<Suc j}"
using image_add_atLeastLessThan[where k="Suc 0"] by simp

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
      by (auto intro!: image_eqI[of _ _ x] split: split_if_asm)
  qed
qed auto

lemma image_int_atLeastLessThan: "int ` {a..<b} = {int a..<int b}"
  by (auto intro!: image_eqI [where x = "nat x" for x])

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
    by (rule imageI) (insert `y \<le> -x`[THEN le_imp_neg_le], simp)
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
end

subsubsection {* Finiteness *}

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

text {* A bounded set of natural numbers is finite. *}
lemma bounded_nat_set_is_finite:
  "(ALL i:N. i < (n::nat)) ==> finite N"
apply (rule finite_subset)
 apply (rule_tac [2] finite_lessThan, auto)
done

text {* A set of natural numbers is finite iff it is bounded. *}
lemma finite_nat_set_iff_bounded:
  "finite(N::nat set) = (EX m. ALL n:N. n<m)" (is "?F = ?B")
proof
  assume f:?F  show ?B
    using Max_ge[OF `?F`, simplified less_Suc_eq_le[symmetric]] by blast
next
  assume ?B show ?F using `?B` by(blast intro:bounded_nat_set_is_finite)
qed

lemma finite_nat_set_iff_bounded_le:
  "finite(N::nat set) = (EX m. ALL n:N. n<=m)"
apply(simp add:finite_nat_set_iff_bounded)
apply(blast dest:less_imp_le_nat le_imp_less_Suc)
done

lemma finite_less_ub:
     "!!f::nat=>nat. (!!n. n \<le> f n) ==> finite {n. f n \<le> u}"
by (rule_tac B="{..u}" in finite_subset, auto intro: order_trans)


text{* Any subset of an interval of natural numbers the size of the
subset is exactly that interval. *}

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


subsubsection {* Proving Inclusions and Equalities between Unions *}

lemma UN_le_eq_Un0:
  "(\<Union>i\<le>n::nat. M i) = (\<Union>i\<in>{1..n}. M i) \<union> M 0" (is "?A = ?B")
proof
  show "?A <= ?B"
  proof
    fix x assume "x : ?A"
    then obtain i where i: "i\<le>n" "x : M i" by auto
    show "x : ?B"
    proof(cases i)
      case 0 with i show ?thesis by simp
    next
      case (Suc j) with i show ?thesis by auto
    qed
  qed
next
  show "?B <= ?A" by auto
qed

lemma UN_le_add_shift:
  "(\<Union>i\<le>n::nat. M(i+k)) = (\<Union>i\<in>{k..n+k}. M i)" (is "?A = ?B")
proof
  show "?A <= ?B" by fastforce
next
  show "?B <= ?A"
  proof
    fix x assume "x : ?B"
    then obtain i where i: "i : {k..n+k}" "x : M(i)" by auto
    hence "i-k\<le>n & x : M((i-k)+k)" by auto
    thus "x : ?A" by blast
  qed
qed

lemma UN_UN_finite_eq: "(\<Union>n::nat. \<Union>i\<in>{0..<n}. A i) = (\<Union>n. A n)"
  by (auto simp add: atLeast0LessThan) 

lemma UN_finite_subset: "(!!n::nat. (\<Union>i\<in>{0..<n}. A i) \<subseteq> C) \<Longrightarrow> (\<Union>n. A n) \<subseteq> C"
  by (subst UN_UN_finite_eq [symmetric]) blast

lemma UN_finite2_subset: 
     "(!!n::nat. (\<Union>i\<in>{0..<n}. A i) \<subseteq> (\<Union>i\<in>{0..<n+k}. B i)) \<Longrightarrow> (\<Union>n. A n) \<subseteq> (\<Union>n. B n)"
  apply (rule UN_finite_subset)
  apply (subst UN_UN_finite_eq [symmetric, of B]) 
  apply blast
  done

lemma UN_finite2_eq:
  "(!!n::nat. (\<Union>i\<in>{0..<n}. A i) = (\<Union>i\<in>{0..<n+k}. B i)) \<Longrightarrow> (\<Union>n. A n) = (\<Union>n. B n)"
  apply (rule subset_antisym)
   apply (rule UN_finite2_subset, blast)
 apply (rule UN_finite2_subset [where k=k])
 apply (force simp add: atLeastLessThan_add_Un [of 0])
 done


subsubsection {* Cardinality *}

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

lemma ex_bij_betw_nat_finite:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h {0..<card M} M"
apply(drule finite_imp_nat_seg_image_inj_on)
apply(auto simp:atLeast0LessThan[symmetric] lessThan_def[symmetric] card_image bij_betw_def)
done

lemma ex_bij_betw_finite_nat:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h M {0..<card M}"
by (blast dest: ex_bij_betw_nat_finite bij_betw_inv)

lemma finite_same_card_bij:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> card A = card B \<Longrightarrow> EX h. bij_betw h A B"
apply(drule ex_bij_betw_finite_nat)
apply(drule ex_bij_betw_nat_finite)
apply(auto intro!:bij_betw_trans)
done

lemma ex_bij_betw_nat_finite_1:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h {1 .. card M} M"
by (rule finite_same_card_bij) auto

lemma bij_betw_iff_card:
  assumes FIN: "finite A" and FIN': "finite B"
  shows BIJ: "(\<exists>f. bij_betw f A B) \<longleftrightarrow> (card A = card B)"
using assms
proof(auto simp add: bij_betw_same_card)
  assume *: "card A = card B"
  obtain f where "bij_betw f A {0 ..< card A}"
  using FIN ex_bij_betw_finite_nat by blast
  moreover obtain g where "bij_betw g {0 ..< card B} B"
  using FIN' ex_bij_betw_nat_finite by blast
  ultimately have "bij_betw (g o f) A B"
  using * by (auto simp add: bij_betw_trans)
  thus "(\<exists>f. bij_betw f A B)" by blast
qed

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
  hence "inj_on (g o f) A" using 1 comp_inj_on by blast
  moreover
  {have "{0 ..< card A} \<le> {0 ..< card B}" using * by force
   with 2 have "f ` A  \<le> {0 ..< card B}" by blast
   hence "(g o f) ` A \<le> B" unfolding comp_def using 3 by force
  }
  ultimately show "(\<exists>f. inj_on f A \<and> f ` A \<le> B)" by blast
qed (insert assms, auto)

subsection {* Intervals of integers *}

lemma atLeastLessThanPlusOne_atLeastAtMost_int: "{l..<u+1} = {l..(u::int)}"
  by (auto simp add: atLeastAtMost_def atLeastLessThan_def)

lemma atLeastPlusOneAtMost_greaterThanAtMost_int: "{l+1..u} = {l<..(u::int)}"
  by (auto simp add: atLeastAtMost_def greaterThanAtMost_def)

lemma atLeastPlusOneLessThan_greaterThanLessThan_int:
    "{l+1..<u} = {l<..<u::int}"
  by (auto simp add: atLeastLessThan_def greaterThanLessThan_def)

subsubsection {* Finiteness *}

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


subsubsection {* Cardinality *}

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


subsection {*Lemmas useful with the summation operator setsum*}

text {* For examples, see Algebra/poly/UnivPoly2.thy *}

subsubsection {* Disjoint Unions *}

text {* Singletons and open intervals *}

lemma ivl_disj_un_singleton:
  "{l::'a::linorder} Un {l<..} = {l..}"
  "{..<u} Un {u::'a::linorder} = {..u}"
  "(l::'a::linorder) < u ==> {l} Un {l<..<u} = {l..<u}"
  "(l::'a::linorder) < u ==> {l<..<u} Un {u} = {l<..u}"
  "(l::'a::linorder) <= u ==> {l} Un {l<..u} = {l..u}"
  "(l::'a::linorder) <= u ==> {l..<u} Un {u} = {l..u}"
by auto

text {* One- and two-sided intervals *}

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

text {* Two- and two-sided intervals *}

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

lemmas ivl_disj_un = ivl_disj_un_singleton ivl_disj_un_one ivl_disj_un_two

subsubsection {* Disjoint Intersections *}

text {* One- and two-sided intervals *}

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

text {* Two- and two-sided intervals *}

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

subsubsection {* Some Differences *}

lemma ivl_diff[simp]:
 "i \<le> n \<Longrightarrow> {i..<m} - {i..<n} = {n..<(m::'a::linorder)}"
by(auto)

lemma (in linorder) lessThan_minus_lessThan [simp]:
  "{..< n} - {..< m} = {m ..< n}"
  by auto


subsubsection {* Some Subset Conditions *}

lemma ivl_subset [simp]:
 "({i..<j} \<subseteq> {m..<n}) = (j \<le> i | m \<le> i & j \<le> (n::'a::linorder))"
apply(auto simp:linorder_not_le)
apply(rule ccontr)
apply(insert linorder_le_less_linear[of i n])
apply(clarsimp simp:linorder_not_le)
apply(fastforce)
done


subsection {* Summation indexed over intervals *}

syntax
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _<_./ _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _<=_./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_<_./ _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_\<le>_./ _)" [0,0,10] 10)
syntax (HTML output)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_<_./ _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_\<le>_./ _)" [0,0,10] 10)
syntax (latex_sum output)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ = _\<^raw:}^{>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ = _\<^raw:}^{<>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ < _\<^raw:}$> _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ \<le> _\<^raw:}$> _)" [0,0,10] 10)

translations
  "\<Sum>x=a..b. t" == "CONST setsum (%x. t) {a..b}"
  "\<Sum>x=a..<b. t" == "CONST setsum (%x. t) {a..<b}"
  "\<Sum>i\<le>n. t" == "CONST setsum (\<lambda>i. t) {..n}"
  "\<Sum>i<n. t" == "CONST setsum (\<lambda>i. t) {..<n}"

text{* The above introduces some pretty alternative syntaxes for
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
@{text latex_sum} (e.g.\ via @{text "mode = latex_sum"} in
antiquotations). It is not the default \LaTeX\ output because it only
works well with italic-style formulae, not tt-style.

Note that for uniformity on @{typ nat} it is better to use
@{term"\<Sum>x::nat=0..<n. e"} rather than @{text"\<Sum>x<n. e"}: @{text setsum} may
not provide all lemmas available for @{term"{m..<n}"} also in the
special form for @{term"{..<n}"}. *}

text{* This congruence rule should be used for sums over intervals as
the standard theorem @{text[source]setsum.cong} does not work well
with the simplifier who adds the unsimplified premise @{term"x:B"} to
the context. *}

lemma setsum_ivl_cong:
 "\<lbrakk>a = c; b = d; !!x. \<lbrakk> c \<le> x; x < d \<rbrakk> \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow>
 setsum f {a..<b} = setsum g {c..<d}"
by(rule setsum.cong, simp_all)

(* FIXME why are the following simp rules but the corresponding eqns
on intervals are not? *)

lemma setsum_atMost_Suc[simp]: "(\<Sum>i \<le> Suc n. f i) = (\<Sum>i \<le> n. f i) + f(Suc n)"
by (simp add:atMost_Suc ac_simps)

lemma setsum_lessThan_Suc[simp]: "(\<Sum>i < Suc n. f i) = (\<Sum>i < n. f i) + f n"
by (simp add:lessThan_Suc ac_simps)

lemma setsum_cl_ivl_Suc[simp]:
  "setsum f {m..Suc n} = (if Suc n < m then 0 else setsum f {m..n} + f(Suc n))"
by (auto simp:ac_simps atLeastAtMostSuc_conv)

lemma setsum_op_ivl_Suc[simp]:
  "setsum f {m..<Suc n} = (if n < m then 0 else setsum f {m..<n} + f(n))"
by (auto simp:ac_simps atLeastLessThanSuc)
(*
lemma setsum_cl_ivl_add_one_nat: "(n::nat) <= m + 1 ==>
    (\<Sum>i=n..m+1. f i) = (\<Sum>i=n..m. f i) + f(m + 1)"
by (auto simp:ac_simps atLeastAtMostSuc_conv)
*)

lemma setsum_head:
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

lemma setsum_head_Suc:
  "m \<le> n \<Longrightarrow> setsum f {m..n} = f m + setsum f {Suc m..n}"
by (simp add: setsum_head atLeastSucAtMost_greaterThanAtMost)

lemma setsum_head_upt_Suc:
  "m < n \<Longrightarrow> setsum f {m..<n} = f m + setsum f {Suc m..<n}"
apply(insert setsum_head_Suc[of m "n - Suc 0" f])
apply (simp add: atLeastLessThanSuc_atLeastAtMost[symmetric] algebra_simps)
done

lemma setsum_ub_add_nat: assumes "(m::nat) \<le> n + 1"
  shows "setsum f {m..n + p} = setsum f {m..n} + setsum f {n + 1..n + p}"
proof-
  have "{m .. n+p} = {m..n} \<union> {n+1..n+p}" using `m \<le> n+1` by auto
  thus ?thesis by (auto simp: ivl_disj_int setsum.union_disjoint
    atLeastSucAtMost_greaterThanAtMost)
qed

lemma setsum_add_nat_ivl: "\<lbrakk> m \<le> n; n \<le> p \<rbrakk> \<Longrightarrow>
  setsum f {m..<n} + setsum f {n..<p} = setsum f {m..<p::nat}"
by (simp add:setsum.union_disjoint[symmetric] ivl_disj_int ivl_disj_un)

lemma setsum_diff_nat_ivl:
fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
shows "\<lbrakk> m \<le> n; n \<le> p \<rbrakk> \<Longrightarrow>
  setsum f {m..<p} - setsum f {m..<n} = setsum f {n..<p}"
using setsum_add_nat_ivl [of m n p f,symmetric]
apply (simp add: ac_simps)
done

lemma setsum_natinterval_difff:
  fixes f:: "nat \<Rightarrow> ('a::ab_group_add)"
  shows  "setsum (\<lambda>k. f k - f(k + 1)) {(m::nat) .. n} =
          (if m <= n then f m - f(n + 1) else 0)"
by (induct n, auto simp add: algebra_simps not_le le_Suc_eq)

lemma setsum_nat_group: "(\<Sum>m<n::nat. setsum f {m * k ..< m*k + k}) = setsum f {..< n * k}"
  apply (subgoal_tac "k = 0 | 0 < k", auto)
  apply (induct "n")
  apply (simp_all add: setsum_add_nat_ivl add.commute atLeast0LessThan[symmetric])
  done

subsection{* Shifting bounds *}

lemma setsum_shift_bounds_nat_ivl:
  "setsum f {m+k..<n+k} = setsum (%i. f(i + k)){m..<n::nat}"
by (induct "n", auto simp:atLeastLessThanSuc)

lemma setsum_shift_bounds_cl_nat_ivl:
  "setsum f {m+k..n+k} = setsum (%i. f(i + k)){m..n::nat}"
  by (rule setsum.reindex_bij_witness[where i="\<lambda>i. i + k" and j="\<lambda>i. i - k"]) auto

corollary setsum_shift_bounds_cl_Suc_ivl:
  "setsum f {Suc m..Suc n} = setsum (%i. f(Suc i)){m..n}"
by (simp add:setsum_shift_bounds_cl_nat_ivl[where k="Suc 0", simplified])

corollary setsum_shift_bounds_Suc_ivl:
  "setsum f {Suc m..<Suc n} = setsum (%i. f(Suc i)){m..<n}"
by (simp add:setsum_shift_bounds_nat_ivl[where k="Suc 0", simplified])

lemma setsum_shift_lb_Suc0_0:
  "f(0::nat) = (0::nat) \<Longrightarrow> setsum f {Suc 0..k} = setsum f {0..k}"
by(simp add:setsum_head_Suc)

lemma setsum_shift_lb_Suc0_0_upt:
  "f(0::nat) = 0 \<Longrightarrow> setsum f {Suc 0..<k} = setsum f {0..<k}"
apply(cases k)apply simp
apply(simp add:setsum_head_upt_Suc)
done

lemma setsum_atMost_Suc_shift:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<le>Suc n. f i) = f 0 + (\<Sum>i\<le>n. f (Suc i))"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) note IH = this
  have "(\<Sum>i\<le>Suc (Suc n). f i) = (\<Sum>i\<le>Suc n. f i) + f (Suc (Suc n))"
    by (rule setsum_atMost_Suc)
  also have "(\<Sum>i\<le>Suc n. f i) = f 0 + (\<Sum>i\<le>n. f (Suc i))"
    by (rule IH)
  also have "f 0 + (\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)) =
             f 0 + ((\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)))"
    by (rule add.assoc)
  also have "(\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)) = (\<Sum>i\<le>Suc n. f (Suc i))"
    by (rule setsum_atMost_Suc [symmetric])
  finally show ?case .
qed

lemma setsum_last_plus: fixes n::nat shows "m <= n \<Longrightarrow> (\<Sum>i = m..n. f i) = f n + (\<Sum>i = m..<n. f i)"
  by (cases n) (auto simp: atLeastLessThanSuc_atLeastAtMost add.commute)

lemma setsum_Suc_diff:
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
  assumes "m \<le> Suc n"
  shows "(\<Sum>i = m..n. f(Suc i) - f i) = f (Suc n) - f m"
using assms by (induct n) (auto simp: le_Suc_eq)

lemma nested_setsum_swap:
     "(\<Sum>i = 0..n. (\<Sum>j = 0..<i. a i j)) = (\<Sum>j = 0..<n. \<Sum>i = Suc j..n. a i j)"
  by (induction n) (auto simp: setsum.distrib)

lemma nested_setsum_swap':
     "(\<Sum>i\<le>n. (\<Sum>j<i. a i j)) = (\<Sum>j<n. \<Sum>i = Suc j..n. a i j)"
  by (induction n) (auto simp: setsum.distrib)

lemma setsum_zero_power [simp]:
  fixes c :: "nat \<Rightarrow> 'a::division_ring"
  shows "(\<Sum>i\<in>A. c i * 0^i) = (if finite A \<and> 0 \<in> A then c 0 else 0)"
apply (cases "finite A")
  by (induction A rule: finite_induct) auto

lemma setsum_zero_power' [simp]:
  fixes c :: "nat \<Rightarrow> 'a::field"
  shows "(\<Sum>i\<in>A. c i * 0^i / d i) = (if finite A \<and> 0 \<in> A then c 0 / d 0 else 0)"
  using setsum_zero_power [of "\<lambda>i. c i / d i" A]
  by auto


subsection {* The formula for geometric sums *}

lemma geometric_sum:
  assumes "x \<noteq> 1"
  shows "(\<Sum>i<n. x ^ i) = (x ^ n - 1) / (x - 1::'a::field)"
proof -
  from assms obtain y where "y = x - 1" and "y \<noteq> 0" by simp_all
  moreover have "(\<Sum>i<n. (y + 1) ^ i) = ((y + 1) ^ n - 1) / y"
    by (induct n) (simp_all add: field_simps `y \<noteq> 0`)
  ultimately show ?thesis by simp
qed


subsection {* The formula for arithmetic sums *}

lemma gauss_sum:
  "(2::'a::comm_semiring_1)*(\<Sum>i\<in>{1..n}. of_nat i) = of_nat n*((of_nat n)+1)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: algebra_simps add: one_add_one [symmetric] del: one_add_one)
      (* FIXME: make numeral cancellation simprocs work for semirings *)
qed

theorem arith_series_general:
  "(2::'a::comm_semiring_1) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
proof cases
  assume ngt1: "n > 1"
  let ?I = "\<lambda>i. of_nat i" and ?n = "of_nat n"
  have
    "(\<Sum>i\<in>{..<n}. a+?I i*d) =
     ((\<Sum>i\<in>{..<n}. a) + (\<Sum>i\<in>{..<n}. ?I i*d))"
    by (rule setsum.distrib)
  also from ngt1 have "\<dots> = ?n*a + (\<Sum>i\<in>{..<n}. ?I i*d)" by simp
  also from ngt1 have "\<dots> = (?n*a + d*(\<Sum>i\<in>{1..<n}. ?I i))"
    unfolding One_nat_def
    by (simp add: setsum_right_distrib atLeast0LessThan[symmetric] setsum_shift_lb_Suc0_0_upt ac_simps)
  also have "2*\<dots> = 2*?n*a + d*2*(\<Sum>i\<in>{1..<n}. ?I i)"
    by (simp add: algebra_simps)
  also from ngt1 have "{1..<n} = {1..n - 1}"
    by (cases n) (auto simp: atLeastLessThanSuc_atLeastAtMost)
  also from ngt1
  have "2*?n*a + d*2*(\<Sum>i\<in>{1..n - 1}. ?I i) = (2*?n*a + d*?I (n - 1)*?I n)"
    by (simp only: mult.assoc gauss_sum [of "n - 1"], unfold One_nat_def)
      (simp add:  mult.commute trans [OF add.commute of_nat_Suc [symmetric]])
  finally show ?thesis
    unfolding mult_2 by (simp add: algebra_simps)
next
  assume "\<not>(n > 1)"
  hence "n = 1 \<or> n = 0" by auto
  thus ?thesis by (auto simp: mult_2)
qed

lemma arith_series_nat:
  "(2::nat) * (\<Sum>i\<in>{..<n}. a+i*d) = n * (a + (a+(n - 1)*d))"
proof -
  have
    "2 * (\<Sum>i\<in>{..<n::nat}. a + of_nat(i)*d) =
    of_nat(n) * (a + (a + of_nat(n - 1)*d))"
    by (rule arith_series_general)
  thus ?thesis
    unfolding One_nat_def by auto
qed

lemma arith_series_int:
  "2 * (\<Sum>i\<in>{..<n}. a + int i * d) = int n * (a + (a + int(n - 1)*d))"
  by (fact arith_series_general) (* FIXME: duplicate *)

lemma sum_diff_distrib: "\<forall>x. Q x \<le> P x  \<Longrightarrow> (\<Sum>x<n. P x) - (\<Sum>x<n. Q x) = (\<Sum>x<n. P x - Q x :: nat)"
  by (subst setsum_subtractf_nat) auto

lemma nat_diff_setsum_reindex: "(\<Sum>i<n. f (n - Suc i)) = (\<Sum>i<n. f i)"
  by (rule setsum.reindex_bij_witness[where i="\<lambda>i. n - Suc i" and j="\<lambda>i. n - Suc i"]) auto

subsection {* Products indexed over intervals *}

syntax
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _<_./ _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _<=_./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_<_./ _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_\<le>_./ _)" [0,0,10] 10)
syntax (HTML output)
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_<_./ _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_\<le>_./ _)" [0,0,10] 10)
syntax (latex_prod output)
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ = _\<^raw:}^{>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ = _\<^raw:}^{<>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ < _\<^raw:}$> _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ \<le> _\<^raw:}$> _)" [0,0,10] 10)

translations
  "\<Prod>x=a..b. t" == "CONST setprod (%x. t) {a..b}"
  "\<Prod>x=a..<b. t" == "CONST setprod (%x. t) {a..<b}"
  "\<Prod>i\<le>n. t" == "CONST setprod (\<lambda>i. t) {..n}"
  "\<Prod>i<n. t" == "CONST setprod (\<lambda>i. t) {..<n}"

subsection {* Transfer setup *}

lemma transfer_nat_int_set_functions:
    "{..n} = nat ` {0..int n}"
    "{m..n} = nat ` {int m..int n}"  (* need all variants of these! *)
  apply (auto simp add: image_def)
  apply (rule_tac x = "int x" in bexI)
  apply auto
  apply (rule_tac x = "int x" in bexI)
  apply auto
  done

lemma transfer_nat_int_set_function_closures:
    "x >= 0 \<Longrightarrow> nat_set {x..y}"
  by (simp add: nat_set_def)

declare transfer_morphism_nat_int[transfer add
  return: transfer_nat_int_set_functions
    transfer_nat_int_set_function_closures
]

lemma transfer_int_nat_set_functions:
    "is_nat m \<Longrightarrow> is_nat n \<Longrightarrow> {m..n} = int ` {nat m..nat n}"
  by (simp only: is_nat_def transfer_nat_int_set_functions
    transfer_nat_int_set_function_closures
    transfer_nat_int_set_return_embed nat_0_le
    cong: transfer_nat_int_set_cong)

lemma transfer_int_nat_set_function_closures:
    "is_nat x \<Longrightarrow> nat_set {x..y}"
  by (simp only: transfer_nat_int_set_function_closures is_nat_def)

declare transfer_morphism_int_nat[transfer add
  return: transfer_int_nat_set_functions
    transfer_int_nat_set_function_closures
]

lemma setprod_int_plus_eq: "setprod int {i..i+j} =  \<Prod>{int i..int (i+j)}"
  by (induct j) (auto simp add: atLeastAtMostSuc_conv atLeastAtMostPlus1_int_conv)

lemma setprod_int_eq: "setprod int {i..j} =  \<Prod>{int i..int j}"
proof (cases "i \<le> j")
  case True
  then show ?thesis
    by (metis Nat.le_iff_add setprod_int_plus_eq)
next
  case False
  then show ?thesis
    by auto
qed

end
