(*
  File:    Data_Structures/Selection.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>The Median-of-Medians Selection Algorithm\<close>
theory Selection
  imports Complex_Main Sorting Time_Funs
begin

text \<open>
  Note that there is significant overlap between this theory (which is intended mostly for the
  Functional Data Structures book) and the Median-of-Medians AFP entry.
\<close>

subsection \<open>Auxiliary material\<close>

lemma replicate_numeral: "replicate (numeral n) x = x # replicate (pred_numeral n) x"
  by (simp add: numeral_eq_Suc)

lemma isort_correct: "isort xs = sort xs"
  using sorted_isort mset_isort by (metis properties_for_sort)

lemma sum_list_replicate [simp]: "sum_list (replicate n x) = n * x"
  by (induction n) auto

lemma mset_concat: "mset (concat xss) = sum_list (map mset xss)"
  by (induction xss) simp_all

lemma set_mset_sum_list [simp]: "set_mset (sum_list xs) = (\<Union>x\<in>set xs. set_mset x)"
  by (induction xs) auto

lemma filter_mset_image_mset:
  "filter_mset P (image_mset f A) = image_mset f (filter_mset (\<lambda>x. P (f x)) A)"
  by (induction A) auto

lemma filter_mset_sum_list: "filter_mset P (sum_list xs) = sum_list (map (filter_mset P) xs)"
  by (induction xs) simp_all

lemma sum_mset_mset_mono: 
  assumes "(\<And>x. x \<in># A \<Longrightarrow> f x \<subseteq># g x)"
  shows   "(\<Sum>x\<in>#A. f x) \<subseteq># (\<Sum>x\<in>#A. g x)"
  using assms by (induction A) (auto intro!: subset_mset.add_mono)

lemma mset_filter_mono:
  assumes "A \<subseteq># B" "\<And>x. x \<in># A \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows   "filter_mset P A \<subseteq># filter_mset Q B"
  by (rule mset_subset_eqI) (insert assms, auto simp: mset_subset_eq_count count_eq_zero_iff)

lemma size_mset_sum_mset_distrib: "size (sum_mset A :: 'a multiset) = sum_mset (image_mset size A)"
  by (induction A) auto

lemma sum_mset_mono:
  assumes "\<And>x. x \<in># A \<Longrightarrow> f x \<le> (g x :: 'a :: {ordered_ab_semigroup_add,comm_monoid_add})"
  shows   "(\<Sum>x\<in>#A. f x) \<le> (\<Sum>x\<in>#A. g x)"
  using assms by (induction A) (auto intro!: add_mono)

lemma filter_mset_is_empty_iff: "filter_mset P A = {#} \<longleftrightarrow> (\<forall>x. x \<in># A \<longrightarrow> \<not>P x)"
  by (auto simp: multiset_eq_iff count_eq_zero_iff)

lemma sort_eq_Nil_iff [simp]: "sort xs = [] \<longleftrightarrow> xs = []"
  by (metis set_empty set_sort)

lemma sort_mset_cong: "mset xs = mset ys \<Longrightarrow> sort xs = sort ys"
  by (metis sorted_list_of_multiset_mset)

lemma Min_set_sorted: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Min (set xs) = hd xs"
  by (cases xs; force intro: Min_insert2)

lemma hd_sort:
  fixes xs :: "'a :: linorder list"
  shows "xs \<noteq> [] \<Longrightarrow> hd (sort xs) = Min (set xs)"
  by (subst Min_set_sorted [symmetric]) auto

lemma length_filter_conv_size_filter_mset: "length (filter P xs) = size (filter_mset P (mset xs))"
  by (induction xs) auto

lemma sorted_filter_less_subset_take:
  assumes "sorted xs" and "i < length xs"
  shows   "{#x \<in># mset xs. x < xs ! i#} \<subseteq># mset (take i xs)"
  using assms
proof (induction xs arbitrary: i rule: list.induct)
  case (Cons x xs i)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis using Cons.prems by (auto simp: filter_mset_is_empty_iff)
  next
    case (Suc i')
    have "{#y \<in># mset (x # xs). y < (x # xs) ! i#} \<subseteq># add_mset x {#y \<in># mset xs. y < xs ! i'#}"
      using Suc Cons.prems by (auto)
    also have "\<dots> \<subseteq># add_mset x (mset (take i' xs))"
      unfolding mset_subset_eq_add_mset_cancel using Cons.prems Suc
      by (intro Cons.IH) (auto)
    also have "\<dots> = mset (take i (x # xs))" by (simp add: Suc)
    finally show ?thesis .
  qed
qed auto

lemma sorted_filter_greater_subset_drop:
  assumes "sorted xs" and "i < length xs"
  shows   "{#x \<in># mset xs. x > xs ! i#} \<subseteq># mset (drop (Suc i) xs)"
  using assms
proof (induction xs arbitrary: i rule: list.induct)
  case (Cons x xs i)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis by (auto simp: sorted_append filter_mset_is_empty_iff)
  next
    case (Suc i')
    have "{#y \<in># mset (x # xs). y > (x # xs) ! i#} \<subseteq># {#y \<in># mset xs. y > xs ! i'#}"
      using Suc Cons.prems by (auto simp: set_conv_nth)
    also have "\<dots> \<subseteq># mset (drop (Suc i') xs)"
      using Cons.prems Suc by (intro Cons.IH) (auto)
    also have "\<dots> = mset (drop (Suc i) (x # xs))" by (simp add: Suc)
    finally show ?thesis .
  qed
qed auto


subsection \<open>Chopping a list into equally-sized bits\<close>

fun chop :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "chop 0 _  = []"
| "chop _ [] = []"
| "chop n xs = take n xs # chop n (drop n xs)"

lemmas [simp del] = chop.simps

text \<open>
  This is an alternative induction rule for \<^const>\<open>chop\<close>, which is often nicer to use.
\<close>
lemma chop_induct' [case_names trivial reduce]:
  assumes "\<And>n xs. n = 0 \<or> xs = [] \<Longrightarrow> P n xs"
  assumes "\<And>n xs. n > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> P n (drop n xs) \<Longrightarrow> P n xs"
  shows   "P n xs"
  using assms
proof induction_schema
  show "wf (measure (length \<circ> snd))"
    by auto
qed (blast | simp)+

lemma chop_eq_Nil_iff [simp]: "chop n xs = [] \<longleftrightarrow> n = 0 \<or> xs = []"
  by (induction n xs rule: chop.induct; subst chop.simps) auto

lemma chop_0 [simp]: "chop 0 xs = []"
  by (simp add: chop.simps)

lemma chop_Nil [simp]: "chop n [] = []"
  by (cases n) (auto simp: chop.simps)

lemma chop_reduce: "n > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> chop n xs = take n xs # chop n (drop n xs)"
  by (cases n; cases xs) (auto simp: chop.simps)

lemma concat_chop [simp]: "n > 0 \<Longrightarrow> concat (chop n xs) = xs"
  by (induction n xs rule: chop.induct; subst chop.simps) auto

lemma chop_elem_not_Nil [dest]: "ys \<in> set (chop n xs) \<Longrightarrow> ys \<noteq> []"
  by (induction n xs rule: chop.induct; subst (asm) chop.simps)
     (auto simp: eq_commute[of "[]"] split: if_splits)

lemma length_chop_part_le: "ys \<in> set (chop n xs) \<Longrightarrow> length ys \<le> n"
  by (induction n xs rule: chop.induct; subst (asm) chop.simps) (auto split: if_splits)

lemma length_chop:
  assumes "n > 0"
  shows   "length (chop n xs) = nat \<lceil>length xs / n\<rceil>"
proof -
  from \<open>n > 0\<close> have "real n * length (chop n xs) \<ge> length xs"
    by (induction n xs rule: chop.induct; subst chop.simps) (auto simp: field_simps)
  moreover from \<open>n > 0\<close> have "real n * length (chop n xs) < length xs + n"
    by (induction n xs rule: chop.induct; subst chop.simps)
       (auto simp: field_simps split: nat_diff_split_asm)+
  ultimately have "length (chop n xs) \<ge> length xs / n" and "length (chop n xs) < length xs / n + 1"
    using assms by (auto simp: field_simps)
  thus ?thesis by linarith
qed

lemma sum_msets_chop: "n > 0 \<Longrightarrow> (\<Sum>ys\<leftarrow>chop n xs. mset ys) = mset xs"
  by (subst mset_concat [symmetric]) simp_all

lemma UN_sets_chop: "n > 0 \<Longrightarrow> (\<Union>ys\<in>set (chop n xs). set ys) = set xs"
  by (simp only: set_concat [symmetric] concat_chop)

lemma chop_append: "d dvd length xs \<Longrightarrow> chop d (xs @ ys) = chop d xs @ chop d ys"
  by (induction d xs rule: chop_induct') (auto simp: chop_reduce dvd_imp_le)

lemma chop_replicate [simp]: "d > 0 \<Longrightarrow> chop d (replicate d xs) = [replicate d xs]"
  by (subst chop_reduce) auto

lemma chop_replicate_dvd [simp]:
  assumes "d dvd n"
  shows   "chop d (replicate n x) = replicate (n div d) (replicate d x)"
proof (cases "d = 0")
  case False
  from assms obtain k where k: "n = d * k"
    by blast
  have "chop d (replicate (d * k) x) = replicate k (replicate d x)"
    using False by (induction k) (auto simp: replicate_add chop_append)
  thus ?thesis using False by (simp add: k)
qed auto

lemma chop_concat:
  assumes "\<forall>xs\<in>set xss. length xs = d" and "d > 0"
  shows   "chop d (concat xss) = xss"
  using assms 
proof (induction xss)
  case (Cons xs xss)
  have "chop d (concat (xs # xss)) = chop d (xs @ concat xss)"
    by simp
  also have "\<dots> = chop d xs @ chop d (concat xss)"
    using Cons.prems by (intro chop_append) auto
  also have "chop d xs = [xs]"
    using Cons.prems by (subst chop_reduce) auto
  also have "chop d (concat xss) = xss"
    using Cons.prems by (intro Cons.IH) auto
  finally show ?case by simp
qed auto


subsection \<open>Selection\<close>

definition select :: "nat \<Rightarrow> ('a :: linorder) list \<Rightarrow> 'a" where
  "select k xs = sort xs ! k"

lemma select_0: "xs \<noteq> [] \<Longrightarrow> select 0 xs = Min (set xs)"
  by (simp add: hd_sort select_def flip: hd_conv_nth)

lemma select_mset_cong: "mset xs = mset ys \<Longrightarrow> select k xs = select k ys"
  using sort_mset_cong[of xs ys] unfolding select_def by auto

lemma select_in_set [intro,simp]:
  assumes "k < length xs"
  shows   "select k xs \<in> set xs"
proof -
  from assms have "sort xs ! k \<in> set (sort xs)" by (intro nth_mem) auto
  also have "set (sort xs) = set xs" by simp
  finally show ?thesis by (simp add: select_def)
qed

lemma
  assumes "n < length xs"
  shows   size_less_than_select: "size {#y \<in># mset xs. y < select n xs#} \<le> n"
    and   size_greater_than_select: "size {#y \<in># mset xs. y > select n xs#} < length xs - n"
proof -
  have "size {#y \<in># mset (sort xs). y < select n xs#} \<le> size (mset (take n (sort xs)))"
    unfolding select_def using assms
    by (intro size_mset_mono sorted_filter_less_subset_take) auto
  thus "size {#y \<in># mset xs. y < select n xs#} \<le> n"
    by simp
  have "size {#y \<in># mset (sort xs). y > select n xs#} \<le> size (mset (drop (Suc n) (sort xs)))"
    unfolding select_def using assms
    by (intro size_mset_mono sorted_filter_greater_subset_drop) auto
  thus "size {#y \<in># mset xs. y > select n xs#} < length xs - n"
    using assms by simp
qed


subsection \<open>The designated median of a list\<close>

definition median where "median xs = select ((length xs - 1) div 2) xs"

lemma median_in_set [intro, simp]: 
  assumes "xs \<noteq> []"
  shows   "median xs \<in> set xs"
proof -
  from assms have "length xs > 0" by auto
  hence "(length xs - 1) div 2 < length xs" by linarith
  thus ?thesis by (simp add: median_def)
qed

lemma size_less_than_median: "size {#y \<in># mset xs. y < median xs#} \<le> (length xs - 1) div 2"
proof (cases "xs = []")
  case False
  hence "length xs > 0"
    by auto
  hence less: "(length xs - 1) div 2 < length xs"
    by linarith
  show "size {#y \<in># mset xs. y < median xs#} \<le> (length xs - 1) div 2"
    using size_less_than_select[OF less] by (simp add: median_def)
qed auto

lemma size_greater_than_median: "size {#y \<in># mset xs. y > median xs#} \<le> length xs div 2"
proof (cases "xs = []")
  case False
  hence "length xs > 0"
    by auto
  hence less: "(length xs - 1) div 2 < length xs"
    by linarith
  have "size {#y \<in># mset xs. y > median xs#} < length xs - (length xs - 1) div 2"
    using size_greater_than_select[OF less] by (simp add: median_def)
  also have "\<dots> = length xs div 2 + 1"
    using \<open>length xs > 0\<close> by linarith
  finally show "size {#y \<in># mset xs. y > median xs#} \<le> length xs div 2"
    by simp
qed auto

lemmas median_props = size_less_than_median size_greater_than_median


subsection \<open>A recurrence for selection\<close>

definition partition3 :: "'a \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list \<times> 'a list \<times> 'a list" where
  "partition3 x xs = (filter (\<lambda>y. y < x) xs, filter (\<lambda>y. y = x) xs, filter (\<lambda>y. y > x) xs)"

lemma partition3_code [code]:
  "partition3 x [] = ([], [], [])"
  "partition3 x (y # ys) =
     (case partition3 x ys of (ls, es, gs) \<Rightarrow>
        if y < x then (y # ls, es, gs) else if x = y then (ls, y # es, gs) else (ls, es, y # gs))"
  by (auto simp: partition3_def)

lemma sort_append:
  assumes "\<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y"
  shows   "sort (xs @ ys) = sort xs @ sort ys"
  using assms by (intro properties_for_sort) (auto simp: sorted_append)

lemma select_append:
  assumes "\<forall>y\<in>set ys. \<forall>z\<in>set zs. y \<le> z"
  shows   "k < length ys \<Longrightarrow> select k (ys @ zs) = select k ys"
    and   "k \<in> {length ys..<length ys + length zs} \<Longrightarrow>
             select k (ys @ zs) = select (k - length ys) zs"
  using assms by (simp_all add: select_def sort_append nth_append)

lemma select_append':
  assumes "\<forall>y\<in>set ys. \<forall>z\<in>set zs. y \<le> z" and "k < length ys + length zs"
  shows   "select k (ys @ zs) = (if k < length ys then select k ys else select (k - length ys) zs)"
  using assms by (auto intro!: select_append)

theorem select_rec_partition:
  assumes "k < length xs"
  shows "select k xs = (
           let (ls, es, gs) = partition3 x xs
           in
             if k < length ls then select k ls 
             else if k < length ls + length es then x
             else select (k - length ls - length es) gs
          )" (is "_ = ?rhs")
proof -
  define ls es gs where "ls = filter (\<lambda>y. y < x) xs" and "es = filter (\<lambda>y. y = x) xs"
                    and "gs = filter (\<lambda>y. y > x) xs"
  define nl ne where [simp]: "nl = length ls" "ne = length es"
  have mset_eq: "mset xs = mset ls + mset es + mset gs"
    unfolding ls_def es_def gs_def by (induction xs) auto
  have length_eq: "length xs = length ls + length es + length gs"
    unfolding ls_def es_def gs_def by (induction xs) auto
  have [simp]: "select i es = x" if "i < length es" for i
  proof -
    have "select i es \<in> set (sort es)" unfolding select_def
      using that by (intro nth_mem) auto
    thus ?thesis
      by (auto simp: es_def)
  qed

  have "select k xs = select k (ls @ (es @ gs))"
    by (intro select_mset_cong) (simp_all add: mset_eq)
  also have "\<dots> = (if k < nl then select k ls else select (k - nl) (es @ gs))" 
    unfolding nl_ne_def using assms
    by (intro select_append') (auto simp: ls_def es_def gs_def length_eq)
  also have "\<dots> = (if k < nl then select k ls else if k < nl + ne then x
                    else select (k - nl - ne) gs)"
  proof (rule if_cong)
    assume "\<not>k < nl"
    have "select (k - nl) (es @ gs) =
                 (if k - nl < ne then select (k - nl) es else select (k - nl - ne) gs)"
      unfolding nl_ne_def using assms \<open>\<not>k < nl\<close>
      by (intro select_append') (auto simp: ls_def es_def gs_def length_eq)
    also have "\<dots> = (if k < nl + ne then x else select (k - nl - ne) gs)"
      using \<open>\<not>k < nl\<close> by auto
    finally show "select (k - nl) (es @ gs) = \<dots>" .
  qed simp_all
  also have "\<dots> = ?rhs"
    by (simp add: partition3_def ls_def es_def gs_def)
  finally show ?thesis .
qed


subsection \<open>The size of the lists in the recursive calls\<close>

text \<open>
  We now derive an upper bound for the number of elements of a list that are smaller
  (resp. bigger) than the median of medians with chopping size 5. To avoid having to do the
  same proof twice, we do it generically for an operation \<open>\<prec>\<close> that we will later instantiate
  with either \<open><\<close> or \<open>>\<close>.
\<close>

context
  fixes xs :: "'a :: linorder list"
  fixes M defines "M \<equiv> median (map median (chop 5 xs))"
begin

lemma size_median_of_medians_aux:
  fixes R :: "'a :: linorder \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes R: "R \<in> {(<), (>)}"
  shows "size {#y \<in># mset xs. y \<prec> M#} \<le> nat \<lceil>0.7 * length xs + 3\<rceil>"
proof -
  define n and m where [simp]: "n = length xs" and "m = length (chop 5 xs)"
  text \<open>We define an abbreviation for the multiset of all the chopped-up groups:\<close>

  text \<open>We then split that multiset into those groups whose medians is less than @{term M}
        and the rest.\<close>
  define Y_small ("Y\<^sub>\<prec>") where "Y\<^sub>\<prec> = filter_mset (\<lambda>ys. median ys \<prec> M) (mset (chop 5 xs))"
  define Y_big ("Y\<^sub>\<succeq>") where "Y\<^sub>\<succeq> = filter_mset (\<lambda>ys. \<not>(median ys \<prec> M)) (mset (chop 5 xs))"
  have "m = size (mset (chop 5 xs))" by (simp add: m_def)
  also have "mset (chop 5 xs) = Y\<^sub>\<prec> + Y\<^sub>\<succeq>" unfolding Y_small_def Y_big_def
    by (rule multiset_partition)
  finally have m_eq: "m = size Y\<^sub>\<prec> + size Y\<^sub>\<succeq>" by simp

  text \<open>At most half of the lists have a median that is smaller than the median of medians:\<close>
  have "size Y\<^sub>\<prec> = size (image_mset median Y\<^sub>\<prec>)" by simp
  also have "image_mset median Y\<^sub>\<prec> = {#y \<in># mset (map median (chop 5 xs)). y \<prec> M#}"
    unfolding Y_small_def by (subst filter_mset_image_mset [symmetric]) simp_all
  also have "size \<dots> \<le> (length (map median (chop 5 xs))) div 2"
    unfolding M_def using median_props[of "map median (chop 5 xs)"] R by auto
  also have "\<dots> = m div 2" by (simp add: m_def)
  finally have size_Y\<^sub>_small: "size Y\<^sub>\<prec> \<le> m div 2" .

  text \<open>We estimate the number of elements less than @{term M} by grouping them into elements
      coming from @{term "Y\<^sub>\<prec>"} and elements coming from @{term "Y\<^sub>\<succeq>"}:\<close>
  have "{#y \<in># mset xs. y \<prec> M#} = {#y \<in># (\<Sum>ys\<leftarrow>chop 5 xs. mset ys). y \<prec> M#}"
    by (subst sum_msets_chop) simp_all
  also have "\<dots> = (\<Sum>ys\<leftarrow>chop 5 xs. {#y \<in># mset ys. y \<prec> M#})"
    by (subst filter_mset_sum_list) (simp add: o_def)
  also have "\<dots> = (\<Sum>ys\<in>#mset (chop 5 xs). {#y \<in># mset ys. y \<prec> M#})"
    by (subst sum_mset_sum_list [symmetric]) simp_all
  also have "mset (chop 5 xs) = Y\<^sub>\<prec> + Y\<^sub>\<succeq>"
    by (simp add: Y_small_def Y_big_def not_le)
  also have "(\<Sum>ys\<in>#\<dots>. {#y \<in># mset ys. y \<prec> M#}) = 
               (\<Sum>ys\<in>#Y\<^sub>\<prec>. {#y \<in># mset ys. y \<prec> M#}) + (\<Sum>ys\<in>#Y\<^sub>\<succeq>. {#y \<in># mset ys. y \<prec> M#})"
    by simp

  text \<open>Next, we overapproximate the elements contributed by @{term "Y\<^sub>\<prec>"}: instead of those elements
        that are smaller than the median, we take \<^emph>\<open>all\<close> the elements of each group.
        For the elements contributed by @{term "Y\<^sub>\<succeq>"}, we overapproximate by taking all those that
        are less than their median instead of only those that are less than @{term M}.\<close>
  also have "\<dots> \<subseteq># (\<Sum>ys\<in>#Y\<^sub>\<prec>. mset ys) + (\<Sum>ys\<in>#Y\<^sub>\<succeq>. {#y \<in># mset ys. y \<prec> median ys#})"
    using R
    by (intro subset_mset.add_mono sum_mset_mset_mono mset_filter_mono) (auto simp: Y_big_def)
  finally have "size {# y \<in># mset xs. y \<prec> M#} \<le> size \<dots>"
    by (rule size_mset_mono)
  hence "size {# y \<in># mset xs. y \<prec> M#} \<le>
           (\<Sum>ys\<in>#Y\<^sub>\<prec>. length ys) + (\<Sum>ys\<in>#Y\<^sub>\<succeq>. size {#y \<in># mset ys. y \<prec> median ys#})"
    by (simp add: size_mset_sum_mset_distrib multiset.map_comp o_def)

  text \<open>Next, we further overapproximate the first sum by noting that each group has
        at most size 5.\<close>
  also have "(\<Sum>ys\<in>#Y\<^sub>\<prec>. length ys) \<le> (\<Sum>ys\<in>#Y\<^sub>\<prec>. 5)"
    by (intro sum_mset_mono) (auto simp: Y_small_def length_chop_part_le)
  also have "\<dots> = 5 * size Y\<^sub>\<prec>" by simp

  text \<open>Next, we note that each group in @{term "Y\<^sub>\<succeq>"} can have at most 2 elements that are
        smaller than its median.\<close>
  also have "(\<Sum>ys\<in>#Y\<^sub>\<succeq>. size {#y \<in># mset ys. y \<prec> median ys#}) \<le>
               (\<Sum>ys\<in>#Y\<^sub>\<succeq>. length ys div 2)"
  proof (intro sum_mset_mono, goal_cases)
    fix ys assume "ys \<in># Y\<^sub>\<succeq>"
    hence "ys \<noteq> []"
      by (auto simp: Y_big_def)
    thus "size {#y \<in># mset ys. y \<prec> median ys#} \<le> length ys div 2"
      using R median_props[of ys] by auto
  qed
  also have "\<dots> \<le> (\<Sum>ys\<in>#Y\<^sub>\<succeq>. 2)"
    by (intro sum_mset_mono div_le_mono diff_le_mono)
       (auto simp: Y_big_def dest: length_chop_part_le)
  also have "\<dots> = 2 * size Y\<^sub>\<succeq>" by simp

  text \<open>Simplifying gives us the main result.\<close>
  also have "5 * size Y\<^sub>\<prec> + 2 * size Y\<^sub>\<succeq> = 2 * m + 3 * size Y\<^sub>\<prec>"
    by (simp add: m_eq)
  also have "\<dots> \<le> 3.5 * m"
    using \<open>size Y\<^sub>\<prec> \<le> m div 2\<close> by linarith
  also have "\<dots> = 3.5 * \<lceil>n / 5\<rceil>"
    by (simp add: m_def length_chop)
  also have "\<dots> \<le> 0.7 * n + 3.5"
    by linarith
  finally have "size {#y \<in># mset xs. y \<prec> M#} \<le> 0.7 * n + 3.5"
    by simp
  thus "size {#y \<in># mset xs. y \<prec> M#} \<le> nat \<lceil>0.7 * n + 3\<rceil>"
    by linarith
qed

lemma size_less_than_median_of_medians:
  "size {#y \<in># mset xs. y < M#} \<le> nat \<lceil>0.7 * length xs + 3\<rceil>"
  using size_median_of_medians_aux[of "(<)"] by simp

lemma size_greater_than_median_of_medians:
  "size {#y \<in># mset xs. y > M#} \<le> nat \<lceil>0.7 * length xs + 3\<rceil>"
  using size_median_of_medians_aux[of "(>)"] by simp

end


subsection \<open>Efficient algorithm\<close>

text \<open>
  We handle the base cases and computing the median for the chopped-up sublists of size 5
  using the naive selection algorithm where we sort the list using insertion sort.
\<close>
definition slow_select where
  "slow_select k xs = isort xs ! k"

definition slow_median where
  "slow_median xs = slow_select ((length xs - 1) div 2) xs"

lemma slow_select_correct: "slow_select k xs = select k xs"
  by (simp add: slow_select_def select_def isort_correct)

lemma slow_median_correct: "slow_median xs = median xs"
  by (simp add: median_def slow_median_def slow_select_correct)

text \<open>
  The definition of the selection algorithm is complicated somewhat by the fact that its
  termination is contingent on its correctness: if the first recursive call were to return an
  element for \<open>x\<close> that is e.g. smaller than all list elements, the algorithm would not terminate.

  Therefore, we first prove partial correctness, then termination, and then combine the two
  to obtain total correctness.
\<close>
function mom_select where
  "mom_select k xs = (
     if length xs \<le> 20 then
       slow_select k xs
     else
       let M = mom_select (((length xs + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs));
           (ls, es, gs) = partition3 M xs
       in
         if k < length ls then mom_select k ls 
         else if k < length ls + length es then M
         else mom_select (k - length ls - length es) gs
      )"
  by auto

text \<open>
  If @{const "mom_select"} terminates, it agrees with @{const select}:
\<close>
lemma mom_select_correct_aux:
  assumes "mom_select_dom (k, xs)" and "k < length xs"
  shows   "mom_select k xs = select k xs"
  using assms
proof (induction rule: mom_select.pinduct)
  case (1 k xs)
  show "mom_select k xs = select k xs"
  proof (cases "length xs \<le> 20")
    case True
    thus "mom_select k xs = select k xs" using "1.prems" "1.hyps"
      by (subst mom_select.psimps) (auto simp: select_def slow_select_correct)
  next
    case False
    define x where
      "x = mom_select (((length xs + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs))"
    define ls es gs where "ls = filter (\<lambda>y. y < x) xs" and "es = filter (\<lambda>y. y = x) xs"
                      and "gs = filter (\<lambda>y. y > x) xs"
    define nl ne where "nl = length ls" and "ne = length es"
    note defs = nl_def ne_def x_def ls_def es_def gs_def
    have tw: "(ls, es, gs) = partition3 x xs"
      unfolding partition3_def defs One_nat_def ..
    have length_eq: "length xs = nl + ne + length gs"
      unfolding nl_def ne_def ls_def es_def gs_def by (induction xs) auto
    note IH = "1.IH"(2,3)[OF False x_def tw refl refl]

    have "mom_select k xs = (if k < nl then mom_select k ls else if k < nl + ne then x
                                else mom_select (k - nl - ne) gs)" using "1.hyps" False
      by (subst mom_select.psimps) (simp_all add: partition3_def flip: defs One_nat_def)
    also have "\<dots> = (if k < nl then select k ls else if k < nl + ne then x 
                       else select (k - nl - ne) gs)"
      using IH length_eq "1.prems" by (simp add: ls_def es_def gs_def nl_def ne_def)
    also have "\<dots> = select k xs" using \<open>k < length xs\<close>
      by (subst (3) select_rec_partition[of _ _ x]) (simp_all add: nl_def ne_def flip: tw)
    finally show "mom_select k xs = select k xs" .
  qed
qed

text \<open>
  @{const mom_select} indeed terminates for all inputs:
\<close>
lemma mom_select_termination: "All mom_select_dom"
proof (relation "measure (length \<circ> snd)"; (safe)?)
  fix k :: nat and xs :: "'a list"
  assume "\<not> length xs \<le> 20"
  thus "((((length xs + 4) div 5 - 1) div 2, map slow_median (chop 5 xs)), k, xs)
           \<in> measure (length \<circ> snd)"
    by (auto simp: length_chop nat_less_iff ceiling_less_iff)
next
  fix k :: nat and xs ls es gs :: "'a list"
  define x where "x = mom_select (((length xs + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs))"
  assume A: "\<not> length xs \<le> 20" 
            "(ls, es, gs) = partition3 x xs"
            "mom_select_dom (((length xs + 4) div 5 - 1) div 2, 
                             map slow_median (chop 5 xs))"
  have less: "((length xs + 4) div 5 - 1) div 2 < nat \<lceil>length xs / 5\<rceil>"
    using A(1) by linarith

  text \<open>For termination, it suffices to prove that @{term x} is in the list.\<close>
  have "x = select (((length xs + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs))"
    using less unfolding x_def by (intro mom_select_correct_aux A) (auto simp: length_chop)
  also have "\<dots> \<in> set (map slow_median (chop 5 xs))"
    using less by (intro select_in_set) (simp_all add: length_chop)
  also have "\<dots> \<subseteq> set xs"
    unfolding set_map
  proof safe
    fix ys assume ys: "ys \<in> set (chop 5 xs)"
    hence "median ys \<in> set ys"
      by auto
    also have "set ys \<subseteq> \<Union>(set ` set (chop 5 xs))"
      using ys by blast
    also have "\<dots> = set xs"
      by (rule UN_sets_chop) simp_all
    finally show "slow_median ys \<in> set xs"
      by (simp add: slow_median_correct)
  qed
  finally have "x \<in> set xs" .
  thus "((k, ls), k, xs) \<in> measure (length \<circ> snd)"
   and "((k - length ls - length es, gs), k, xs) \<in> measure (length \<circ> snd)"
    using A(1,2) by (auto simp: partition3_def intro!: length_filter_less[of x])
qed

termination mom_select by (rule mom_select_termination)

lemmas [simp del] = mom_select.simps

lemma mom_select_correct: "k < length xs \<Longrightarrow> mom_select k xs = select k xs"
  using mom_select_correct_aux and mom_select_termination by blast



subsection \<open>Running time analysis\<close>

fun T_partition3 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_partition3 x [] = 1"
| "T_partition3 x (y # ys) = T_partition3 x ys + 1"

lemma T_partition3_eq: "T_partition3 x xs = length xs + 1"
  by (induction x xs rule: T_partition3.induct) auto

definition T_slow_select :: "nat \<Rightarrow> 'a :: linorder list \<Rightarrow> nat" where
  "T_slow_select k xs = T_isort xs + T_nth (isort xs) k + 1"

definition T_slow_median :: "'a :: linorder list \<Rightarrow> nat" where
  "T_slow_median xs = T_slow_select ((length xs - 1) div 2) xs + 1"

lemma T_slow_select_le: "T_slow_select k xs \<le> length xs ^ 2 + 3 * length xs + 3"
proof -
  have "T_slow_select k xs \<le> (length xs + 1)\<^sup>2 + (length (isort xs) + 1) + 1"
    unfolding T_slow_select_def
    by (intro add_mono T_isort_length) (auto simp: T_nth_eq)
  also have "\<dots> = length xs ^ 2 + 3 * length xs + 3"
    by (simp add: isort_correct algebra_simps power2_eq_square)
  finally show ?thesis .
qed

lemma T_slow_median_le: "T_slow_median xs \<le> length xs ^ 2 + 3 * length xs + 4"
  unfolding T_slow_median_def using T_slow_select_le[of "(length xs - 1) div 2" xs] by simp


fun T_chop :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "T_chop 0 _  = 1"
| "T_chop _ [] = 1"
| "T_chop n xs = T_take n xs + T_drop n xs + T_chop n (drop n xs)"

lemmas [simp del] = T_chop.simps

lemma T_chop_Nil [simp]: "T_chop d [] = 1"
  by (cases d) (auto simp: T_chop.simps)

lemma T_chop_0 [simp]: "T_chop 0 xs = 1"
  by (auto simp: T_chop.simps)

lemma T_chop_reduce:
  "n > 0 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> T_chop n xs = T_take n xs + T_drop n xs + T_chop n (drop n xs)"
  by (cases n; cases xs) (auto simp: T_chop.simps)

lemma T_chop_le: "T_chop d xs \<le> 5 * length xs + 1"
  by (induction d xs rule: T_chop.induct) (auto simp: T_chop_reduce T_take_eq T_drop_eq)

text \<open>
  The option \<open>domintros\<close> here allows us to explicitly reason about where the function does and
  does not terminate. With this, we can skip the termination proof this time because we can
  reuse the one for \<^const>\<open>mom_select\<close>.
\<close>
function (domintros) T_mom_select :: "nat \<Rightarrow> 'a :: linorder list \<Rightarrow> nat" where
  "T_mom_select k xs = (
     if length xs \<le> 20 then
       T_slow_select k xs
     else
       let xss = chop 5 xs;
           ms = map slow_median xss;
           idx = (((length xs + 4) div 5 - 1) div 2);
           x = mom_select idx ms;
           (ls, es, gs) = partition3 x xs;
           nl = length ls;
           ne = length es
       in
         (if k < nl then T_mom_select k ls 
          else if k < nl + ne then 0
          else T_mom_select (k - nl - ne) gs) +
         T_mom_select idx ms + T_chop 5 xs + T_map T_slow_median xss +
         T_partition3 x xs + T_length ls + T_length es + 1
      )"
  by auto

termination T_mom_select
proof (rule allI, safe)
  fix k :: nat and xs :: "'a :: linorder list"
  have "mom_select_dom (k, xs)"
    using mom_select_termination by blast
  thus "T_mom_select_dom (k, xs)"
    by (induction k xs rule: mom_select.pinduct)
       (rule T_mom_select.domintros, simp_all)
qed

lemmas [simp del] = T_mom_select.simps


function T'_mom_select :: "nat \<Rightarrow> nat" where
  "T'_mom_select n =
     (if n \<le> 20 then
        463
      else
        T'_mom_select (nat \<lceil>0.2*n\<rceil>) + T'_mom_select (nat \<lceil>0.7*n+3\<rceil>) + 17 * n + 50)"
  by force+
termination by (relation "measure id"; simp; linarith)

lemmas [simp del] = T'_mom_select.simps


lemma T'_mom_select_ge: "T'_mom_select n \<ge> 463"
  by (induction n rule: T'_mom_select.induct; subst T'_mom_select.simps) auto

lemma T'_mom_select_mono:
  "m \<le> n \<Longrightarrow> T'_mom_select m \<le> T'_mom_select n"
proof (induction n arbitrary: m rule: less_induct)
  case (less n m)
  show ?case
  proof (cases "m \<le> 20")
    case True
    hence "T'_mom_select m = 463"
      by (subst T'_mom_select.simps) auto
    also have "\<dots> \<le> T'_mom_select n"
      by (rule T'_mom_select_ge)
    finally show ?thesis .
  next
    case False
    hence "T'_mom_select m =
             T'_mom_select (nat \<lceil>0.2*m\<rceil>) + T'_mom_select (nat \<lceil>0.7*m + 3\<rceil>) + 17 * m + 50"
      by (subst T'_mom_select.simps) auto
    also have "\<dots> \<le> T'_mom_select (nat \<lceil>0.2*n\<rceil>) + T'_mom_select (nat \<lceil>0.7*n + 3\<rceil>) + 17 * n + 50"
      using \<open>m \<le> n\<close> and False by (intro add_mono less.IH; linarith)
    also have "\<dots> = T'_mom_select n"
      using \<open>m \<le> n\<close> and False by (subst T'_mom_select.simps) auto
    finally show ?thesis .
  qed
qed

lemma T_mom_select_le_aux: "T_mom_select k xs \<le> T'_mom_select (length xs)"
proof (induction k xs rule: T_mom_select.induct)
  case (1 k xs)
  define n where [simp]: "n = length xs"
  define x where
    "x = mom_select (((length xs + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs))"
  define ls es gs where "ls = filter (\<lambda>y. y < x) xs" and "es = filter (\<lambda>y. y = x) xs"
                    and "gs = filter (\<lambda>y. y > x) xs"
  define nl ne where "nl = length ls" and "ne = length es"
  note defs = nl_def ne_def x_def ls_def es_def gs_def
  have tw: "(ls, es, gs) = partition3 x xs"
    unfolding partition3_def defs One_nat_def ..
  note IH = "1.IH"(1,2,3)[OF _ refl refl refl x_def tw refl refl refl refl]

  show ?case
  proof (cases "length xs \<le> 20")
    case True \<comment> \<open>base case\<close>
    hence "T_mom_select k xs \<le> (length xs)\<^sup>2 + 3 * length xs + 3"
      using T_slow_select_le[of k xs] by (subst T_mom_select.simps) auto
    also have "\<dots> \<le> 20\<^sup>2 + 3 * 20 + 3"
      using True by (intro add_mono power_mono) auto
    also have "\<dots> \<le> 463"
      by simp
    also have "\<dots> = T'_mom_select (length xs)"
      using True by (simp add: T'_mom_select.simps)
    finally show ?thesis by simp
  next
    case False \<comment> \<open>recursive case\<close>
    have "((n + 4) div 5 - 1) div 2 < nat \<lceil>n / 5\<rceil>"
      using False unfolding n_def by linarith
    hence "x = select (((n + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs))"
      unfolding x_def n_def by (intro mom_select_correct) (auto simp: length_chop)
    also have "((n + 4) div 5 - 1) div 2 = (nat \<lceil>n / 5\<rceil> - 1) div 2"
      by linarith
    also have "select \<dots> (map slow_median (chop 5 xs)) = median (map slow_median (chop 5 xs))"
      by (auto simp: median_def length_chop)
    finally have x_eq: "x = median (map slow_median (chop 5 xs))" .

    text \<open>The cost of computing the medians of all the subgroups:\<close>
    define T_ms where "T_ms = T_map T_slow_median (chop 5 xs)"
    have "T_ms \<le> 9 * n + 45"
    proof -
      have "T_ms = (\<Sum>ys\<leftarrow>chop 5 xs. T_slow_median ys) + length (chop 5 xs) + 1"
        by (simp add: T_ms_def T_map_eq)
      also have "(\<Sum>ys\<leftarrow>chop 5 xs. T_slow_median ys) \<le> (\<Sum>ys\<leftarrow>chop 5 xs. 44)"
      proof (intro sum_list_mono)
        fix ys assume "ys \<in> set (chop 5 xs)"
        hence "length ys \<le> 5"
          using length_chop_part_le by blast
        have "T_slow_median ys \<le> (length ys) ^ 2 + 3 * length ys + 4"
          by (rule T_slow_median_le)
        also have "\<dots> \<le> 5 ^ 2 + 3 * 5 + 4"
          using \<open>length ys \<le> 5\<close> by (intro add_mono power_mono) auto
        finally show "T_slow_median ys \<le> 44" by simp
      qed
      also have "(\<Sum>ys\<leftarrow>chop 5 xs. 44) + length (chop 5 xs) + 1 =
                   45 * nat \<lceil>real n / 5\<rceil> + 1"
        by (simp add: map_replicate_const length_chop)
      also have "\<dots> \<le> 9 * n + 45"
        by linarith
      finally show "T_ms \<le> 9 * n + 45" by simp
    qed

    text \<open>The cost of the first recursive call (to compute the median of medians):\<close>
    define T_rec1 where
      "T_rec1 = T_mom_select (((length xs + 4) div 5 - 1) div 2) (map slow_median (chop 5 xs))"
    have "T_rec1 \<le> T'_mom_select (length (map slow_median (chop 5 xs)))"
      using False unfolding T_rec1_def by (intro IH(3)) auto
    hence "T_rec1 \<le> T'_mom_select (nat \<lceil>0.2 * n\<rceil>)"
      by (simp add: length_chop)

    text \<open>The cost of the second recursive call (to compute the final result):\<close>
    define T_rec2 where "T_rec2 = (if k < nl then T_mom_select k ls
                                 else if k < nl + ne then 0
                                 else T_mom_select (k - nl - ne) gs)"
    consider "k < nl" | "k \<in> {nl..<nl+ne}" | "k \<ge> nl+ne"
      by force
    hence "T_rec2 \<le> T'_mom_select (nat \<lceil>0.7 * n + 3\<rceil>)"
    proof cases
      assume "k < nl"
      hence "T_rec2 = T_mom_select k ls"
        by (simp add: T_rec2_def)
      also have "\<dots> \<le> T'_mom_select (length ls)"
        by (rule IH(1)) (use \<open>k < nl\<close> False in \<open>auto simp: defs\<close>)
      also have "length ls \<le> nat \<lceil>0.7 * n + 3\<rceil>"
        unfolding ls_def using size_less_than_median_of_medians[of xs]
        by (auto simp: length_filter_conv_size_filter_mset slow_median_correct[abs_def] x_eq)
      hence "T'_mom_select (length ls) \<le> T'_mom_select (nat \<lceil>0.7 * n + 3\<rceil>)"
        by (rule T'_mom_select_mono)
      finally show ?thesis .
    next
      assume "k \<in> {nl..<nl + ne}"
      hence "T_rec2 = 0"
        by (simp add: T_rec2_def)
      thus ?thesis
        using T'_mom_select_ge[of "nat \<lceil>0.7 * n + 3\<rceil>"] by simp
    next
      assume "k \<ge> nl + ne"
      hence "T_rec2 = T_mom_select (k - nl - ne) gs"
        by (simp add: T_rec2_def)
      also have "\<dots> \<le> T'_mom_select (length gs)"
        unfolding nl_def ne_def by (rule IH(2)) (use \<open>k \<ge> nl + ne\<close> False in \<open>auto simp: defs\<close>)
      also have "length gs \<le> nat \<lceil>0.7 * n + 3\<rceil>"
        unfolding gs_def using size_greater_than_median_of_medians[of xs]
        by (auto simp: length_filter_conv_size_filter_mset slow_median_correct[abs_def] x_eq)
      hence "T'_mom_select (length gs) \<le> T'_mom_select (nat \<lceil>0.7 * n + 3\<rceil>)"
        by (rule T'_mom_select_mono)
      finally show ?thesis .
    qed

    text \<open>Now for the final inequality chain:\<close>
    have "T_mom_select k xs = T_rec2 + T_rec1 + T_ms + n + nl + ne + T_chop 5 xs + 4" using False
      by (subst T_mom_select.simps, unfold Let_def tw [symmetric] defs [symmetric])
         (simp_all add: nl_def ne_def T_rec1_def T_rec2_def T_partition3_eq
                        T_length_eq T_ms_def)
    also have "nl \<le> n" by (simp add: nl_def ls_def)
    also have "ne \<le> n" by (simp add: ne_def es_def)
    also note \<open>T_ms \<le> 9 * n + 45\<close>
    also have "T_chop 5 xs \<le> 5 * n + 1"
      using T_chop_le[of 5 xs] by simp 
    also note \<open>T_rec1 \<le> T'_mom_select (nat \<lceil>0.2*n\<rceil>)\<close>
    also note \<open>T_rec2 \<le> T'_mom_select (nat \<lceil>0.7*n + 3\<rceil>)\<close>
    finally have "T_mom_select k xs \<le>
                    T'_mom_select (nat \<lceil>0.7*n + 3\<rceil>) + T'_mom_select (nat \<lceil>0.2*n\<rceil>) + 17 * n + 50"
      by simp
    also have "\<dots> = T'_mom_select n"
      using False by (subst T'_mom_select.simps) auto
    finally show ?thesis by simp
  qed
qed

subsection \<open>Akra--Bazzi Light\<close>

lemma akra_bazzi_light_aux1:
  fixes a b :: real and n n0 :: nat
  assumes ab: "a > 0" "a < 1" "n > n0"
  assumes "n0 \<ge> (max 0 b + 1) / (1 - a)"
  shows "nat \<lceil>a*n+b\<rceil> < n"
proof -
  have "a * real n + max 0 b \<ge> 0"
    using ab by simp
  hence "real (nat \<lceil>a*n+b\<rceil>) \<le> a * n + max 0 b + 1"
    by linarith
  also {
    have "n0 \<ge> (max 0 b + 1) / (1 - a)"
      by fact
    also have "\<dots> < real n"
      using assms by simp
    finally have "a * real n + max 0 b + 1 < real n"
      using ab by (simp add: field_simps)
  }
  finally show "nat \<lceil>a*n+b\<rceil> < n"
    using \<open>n > n0\<close> by linarith
qed

lemma akra_bazzi_light_aux2:
  fixes f :: "nat \<Rightarrow> real"
  fixes n\<^sub>0 :: nat and a b c d :: real and C1 C2 C\<^sub>1 C\<^sub>2 :: real
  assumes bounds: "a > 0" "c > 0" "a + c < 1" "C\<^sub>1 \<ge> 0"
  assumes rec: "\<forall>n>n\<^sub>0. f n = f (nat \<lceil>a*n+b\<rceil>) + f (nat \<lceil>c*n+d\<rceil>) + C\<^sub>1 * n + C\<^sub>2"
  assumes ineqs: "n\<^sub>0 > (max 0 b + max 0 d + 2) / (1 - a - c)"
                 "C\<^sub>3 \<ge> C\<^sub>1 / (1 - a - c)"
                 "C\<^sub>3 \<ge> (C\<^sub>1 * n\<^sub>0 + C\<^sub>2 + C\<^sub>4) / ((1 - a - c) * n\<^sub>0 - max 0 b - max 0 d - 2)"
                 "\<forall>n\<le>n\<^sub>0. f n \<le> C\<^sub>4"
  shows   "f n \<le> C\<^sub>3 * n + C\<^sub>4"
proof (induction n rule: less_induct)
  case (less n)
  have "0 \<le> C\<^sub>1 / (1 - a - c)"
    using bounds by auto
  also have "\<dots> \<le> C\<^sub>3"
    by fact
  finally have "C\<^sub>3 \<ge> 0" .

  show ?case
  proof (cases "n > n\<^sub>0")
    case False
    hence "f n \<le> C\<^sub>4"
      using ineqs(4) by auto
    also have "\<dots> \<le> C\<^sub>3 * real n + C\<^sub>4"
      using bounds \<open>C\<^sub>3 \<ge> 0\<close> by auto
    finally show ?thesis .
  next
    case True
    have nonneg: "a * n \<ge> 0" "c * n \<ge> 0"
      using bounds by simp_all

    have "(max 0 b + 1) / (1 - a) \<le> (max 0 b + max 0 d + 2) / (1 - a - c)"
      using bounds by (intro frac_le) auto
    hence "n\<^sub>0 \<ge> (max 0 b + 1) / (1 - a)"
      using ineqs(1) by linarith
    hence rec_less1: "nat \<lceil>a*n+b\<rceil> < n"
      using bounds \<open>n > n\<^sub>0\<close> by (intro akra_bazzi_light_aux1[of _ n\<^sub>0]) auto

    have "(max 0 d + 1) / (1 - c) \<le> (max 0 b + max 0 d + 2) / (1 - a - c)"
      using bounds by (intro frac_le) auto
    hence "n\<^sub>0 \<ge> (max 0 d + 1) / (1 - c)"
      using ineqs(1) by linarith
    hence rec_less2: "nat \<lceil>c*n+d\<rceil> < n"
      using bounds \<open>n > n\<^sub>0\<close> by (intro akra_bazzi_light_aux1[of _ n\<^sub>0]) auto

    have "f n = f (nat \<lceil>a*n+b\<rceil>) + f (nat \<lceil>c*n+d\<rceil>) + C\<^sub>1 * n + C\<^sub>2"
      using \<open>n > n\<^sub>0\<close> by (subst rec) auto
    also have "\<dots> \<le> (C\<^sub>3 * nat \<lceil>a*n+b\<rceil> + C\<^sub>4) + (C\<^sub>3 * nat \<lceil>c*n+d\<rceil> + C\<^sub>4) + C\<^sub>1 * n + C\<^sub>2"
      using rec_less1 rec_less2 by (intro add_mono less.IH) auto
    also have "\<dots> \<le> (C\<^sub>3 * (a*n+max 0 b+1) + C\<^sub>4) + (C\<^sub>3 * (c*n+max 0 d+1) + C\<^sub>4) + C\<^sub>1 * n + C\<^sub>2"
      using bounds \<open>C\<^sub>3 \<ge> 0\<close> nonneg by (intro add_mono mult_left_mono order.refl; linarith)      
    also have "\<dots> = C\<^sub>3 * n  +  ((C\<^sub>3 * (max 0 b + max 0 d + 2) + 2 * C\<^sub>4 + C\<^sub>2) -
                                 (C\<^sub>3 * (1 - a - c) - C\<^sub>1) * n)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> C\<^sub>3 * n  +  ((C\<^sub>3 * (max 0 b + max 0 d + 2) + 2 * C\<^sub>4 + C\<^sub>2) -
                                 (C\<^sub>3 * (1 - a - c) - C\<^sub>1) * n\<^sub>0)"
      using \<open>n > n\<^sub>0\<close> ineqs(2) bounds
      by (intro add_mono diff_mono order.refl mult_left_mono) (auto simp: field_simps)
    also have "(C\<^sub>3 * (max 0 b + max 0 d + 2) + 2 * C\<^sub>4 + C\<^sub>2) - (C\<^sub>3 * (1 - a - c) - C\<^sub>1) * n\<^sub>0 \<le> C\<^sub>4"
      using ineqs bounds by (simp add: field_simps)
    finally show "f n \<le> C\<^sub>3 * real n + C\<^sub>4"
      by (simp add: mult_right_mono)
  qed
qed

lemma akra_bazzi_light:
  fixes f :: "nat \<Rightarrow> real"
  fixes n\<^sub>0 :: nat and a b c d C\<^sub>1 C\<^sub>2 :: real
  assumes bounds: "a > 0" "c > 0" "a + c < 1" "C\<^sub>1 \<ge> 0"
  assumes rec: "\<forall>n>n\<^sub>0. f n = f (nat \<lceil>a*n+b\<rceil>) + f (nat \<lceil>c*n+d\<rceil>) + C\<^sub>1 * n + C\<^sub>2"
  shows "\<exists>C\<^sub>3 C\<^sub>4. \<forall>n. f n \<le> C\<^sub>3 * real n + C\<^sub>4"
proof -
  define n\<^sub>0' where "n\<^sub>0' = max n\<^sub>0 (nat \<lceil>(max 0 b + max 0 d + 2) / (1 - a - c) + 1\<rceil>)"
  define C\<^sub>4 where "C\<^sub>4 = Max (f ` {..n\<^sub>0'})"
  define C\<^sub>3 where "C\<^sub>3 = max (C\<^sub>1 / (1 - a - c))
                         ((C\<^sub>1 * n\<^sub>0' + C\<^sub>2 + C\<^sub>4) / ((1 - a - c) * n\<^sub>0' - max 0 b - max 0 d - 2))"

  have "f n \<le> C\<^sub>3 * n + C\<^sub>4" for n
  proof (rule akra_bazzi_light_aux2[OF bounds _])
    show "\<forall>n>n\<^sub>0'. f n = f (nat \<lceil>a*n+b\<rceil>) + f (nat \<lceil>c*n+d\<rceil>) + C\<^sub>1 * n + C\<^sub>2"
      using rec by (auto simp: n\<^sub>0'_def)
  next
    show "C\<^sub>3 \<ge> C\<^sub>1 / (1 - a - c)" 
     and "C\<^sub>3 \<ge> (C\<^sub>1 * n\<^sub>0' + C\<^sub>2 + C\<^sub>4) / ((1 - a - c) * n\<^sub>0' - max 0 b - max 0 d - 2)"
      by (simp_all add: C\<^sub>3_def)
  next
    have "(max 0 b + max 0 d + 2) / (1 - a - c) < nat \<lceil>(max 0 b + max 0 d + 2) / (1 - a - c) + 1\<rceil>"
      by linarith
    also have "\<dots> \<le> n\<^sub>0'"
      by (simp add: n\<^sub>0'_def)
    finally show "(max 0 b + max 0 d + 2) / (1 - a - c) < real n\<^sub>0'" .
  next
    show "\<forall>n\<le>n\<^sub>0'. f n \<le> C\<^sub>4"
      by (auto simp: C\<^sub>4_def)
  qed
  thus ?thesis by blast
qed

lemma akra_bazzi_light_nat:
  fixes f :: "nat \<Rightarrow> nat"
  fixes n\<^sub>0 :: nat and a b c d :: real and C\<^sub>1 C\<^sub>2 :: nat
  assumes bounds: "a > 0" "c > 0" "a + c < 1" "C\<^sub>1 \<ge> 0"
  assumes rec: "\<forall>n>n\<^sub>0. f n = f (nat \<lceil>a*n+b\<rceil>) + f (nat \<lceil>c*n+d\<rceil>) + C\<^sub>1 * n + C\<^sub>2"
  shows "\<exists>C\<^sub>3 C\<^sub>4. \<forall>n. f n \<le> C\<^sub>3 * n + C\<^sub>4"
proof -
  have "\<exists>C\<^sub>3 C\<^sub>4. \<forall>n. real (f n) \<le> C\<^sub>3 * real n + C\<^sub>4"
    using assms by (intro akra_bazzi_light[of a c C\<^sub>1 n\<^sub>0 f b d C\<^sub>2]) auto
  then obtain C\<^sub>3 C\<^sub>4 where le: "\<forall>n. real (f n) \<le> C\<^sub>3 * real n + C\<^sub>4"
    by blast
  have "f n \<le> nat \<lceil>C\<^sub>3\<rceil> * n + nat \<lceil>C\<^sub>4\<rceil>" for n
  proof -
    have "real (f n) \<le> C\<^sub>3 * real n + C\<^sub>4"
      using le by blast
    also have "\<dots> \<le> real (nat \<lceil>C\<^sub>3\<rceil>) * real n + real (nat \<lceil>C\<^sub>4\<rceil>)"
      by (intro add_mono mult_right_mono; linarith)
    also have "\<dots> = real (nat \<lceil>C\<^sub>3\<rceil> * n + nat \<lceil>C\<^sub>4\<rceil>)"
      by simp
    finally show ?thesis by linarith
  qed
  thus ?thesis by blast
qed

lemma T'_mom_select_le': "\<exists>C\<^sub>1 C\<^sub>2. \<forall>n. T'_mom_select n \<le> C\<^sub>1 * n + C\<^sub>2"
proof (rule akra_bazzi_light_nat)
  show "\<forall>n>20. T'_mom_select n = T'_mom_select (nat \<lceil>0.2 * n + 0\<rceil>) +
                 T'_mom_select (nat \<lceil>0.7 * n + 3\<rceil>) + 17 * n + 50"
    using T'_mom_select.simps by auto
qed auto

end