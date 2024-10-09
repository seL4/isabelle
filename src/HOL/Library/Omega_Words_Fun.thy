(*
    Author:     Stefan Merz
    Author:     Salomon Sickert
    Author:     Julian Brunner
    Author:     Peter Lammich
*)

section \<open>$\omega$-words\<close>

theory Omega_Words_Fun

imports Infinite_Set
begin

text \<open>Note: This theory is based on Stefan Merz's work.\<close>

text \<open>
  Automata recognize languages, which are sets of words. For the
  theory of $\omega$-automata, we are mostly interested in
  $\omega$-words, but it is sometimes useful to reason about
  finite words, too. We are modeling finite words as lists; this
  lets us benefit from the existing library. Other formalizations
  could be investigated, such as representing words as functions
  whose domains are initial intervals of the natural numbers.
\<close>


subsection \<open>Type declaration and elementary operations\<close>

text \<open>
  We represent $\omega$-words as functions from the natural numbers
  to the alphabet type. Other possible formalizations include
  a coinductive definition or a uniform encoding of finite and
  infinite words, as studied by Müller et al.
\<close>

type_synonym
  'a word = "nat \<Rightarrow> 'a"

text \<open>
  We can prefix a finite word to an $\omega$-word, and a way
  to obtain an $\omega$-word from a finite, non-empty word is by
  $\omega$-iteration.
\<close>

definition
  conc :: "['a list, 'a word] \<Rightarrow> 'a word"  (infixr \<open>\<frown>\<close> 65)
  where "w \<frown> x == \<lambda>n. if n < length w then w!n else x (n - length w)"

definition
  iter :: "'a list \<Rightarrow> 'a word"  (\<open>(\<open>notation=\<open>postfix \<omega>\<close>\<close>_\<^sup>\<omega>)\<close> [1000])
  where "iter w == if w = [] then undefined else (\<lambda>n. w!(n mod (length w)))"

lemma conc_empty[simp]: "[] \<frown> w = w"
  unfolding conc_def by auto

lemma conc_fst[simp]: "n < length w \<Longrightarrow> (w \<frown> x) n = w!n"
  by (simp add: conc_def)

lemma conc_snd[simp]: "\<not>(n < length w) \<Longrightarrow> (w \<frown> x) n = x (n - length w)"
  by (simp add: conc_def)

lemma iter_nth [simp]: "0 < length w \<Longrightarrow> w\<^sup>\<omega> n = w!(n mod (length w))"
  by (simp add: iter_def)

lemma conc_conc[simp]: "u \<frown> v \<frown> w = (u @ v) \<frown> w" (is "?lhs = ?rhs")
proof
  fix n
  have u: "n < length u \<Longrightarrow> ?lhs n = ?rhs n"
    by (simp add: conc_def nth_append)
  have v: "\<lbrakk> \<not>(n < length u); n < length u + length v \<rbrakk> \<Longrightarrow> ?lhs n = ?rhs n"
    by (simp add: conc_def nth_append, arith)
  have w: "\<not>(n < length u + length v) \<Longrightarrow> ?lhs n = ?rhs n"
    by (simp add: conc_def nth_append, arith)
  from u v w show "?lhs n = ?rhs n" by blast
qed

lemma range_conc[simp]: "range (w\<^sub>1 \<frown> w\<^sub>2) = set w\<^sub>1 \<union> range w\<^sub>2"
proof (intro equalityI subsetI)
  fix a
  assume "a \<in> range (w\<^sub>1 \<frown> w\<^sub>2)"
  then obtain i where 1: "a = (w\<^sub>1 \<frown> w\<^sub>2) i" by auto
  then show "a \<in> set w\<^sub>1 \<union> range w\<^sub>2"
    unfolding 1 by (cases "i < length w\<^sub>1") simp_all
next
  fix a
  assume a: "a \<in> set w\<^sub>1 \<union> range w\<^sub>2"
  then show "a \<in> range (w\<^sub>1 \<frown> w\<^sub>2)"
  proof
    assume "a \<in> set w\<^sub>1"
    then obtain i where 1: "i < length w\<^sub>1" "a = w\<^sub>1 ! i"
      using in_set_conv_nth by metis
    show ?thesis
    proof
      show "a = (w\<^sub>1 \<frown> w\<^sub>2) i" using 1 by auto
      show "i \<in> UNIV" by rule
    qed
  next
    assume "a \<in> range w\<^sub>2"
    then obtain i where 1: "a = w\<^sub>2 i" by auto
    show ?thesis
    proof
      show "a = (w\<^sub>1 \<frown> w\<^sub>2) (length w\<^sub>1 + i)" using 1 by simp
      show "length w\<^sub>1 + i \<in> UNIV" by rule
    qed
  qed
qed


lemma iter_unroll: "0 < length w \<Longrightarrow> w\<^sup>\<omega> = w \<frown> w\<^sup>\<omega>"
  by (simp add: fun_eq_iff mod_if)


subsection \<open>Subsequence, Prefix, and Suffix\<close>

definition suffix :: "[nat, 'a word] \<Rightarrow> 'a word"
  where "suffix k x \<equiv> \<lambda>n. x (k+n)"

definition subsequence :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
    (\<open>(\<open>open_block notation=\<open>mixfix subsequence\<close>\<close>_ [_ \<rightarrow> _])\<close> 900)
  where "subsequence w i j \<equiv> map w [i..<j]"

abbreviation prefix :: "nat \<Rightarrow> 'a word \<Rightarrow> 'a list"
  where "prefix n w \<equiv> subsequence w 0 n"

lemma suffix_nth [simp]: "(suffix k x) n = x (k+n)"
  by (simp add: suffix_def)

lemma suffix_0 [simp]: "suffix 0 x = x"
  by (simp add: suffix_def)

lemma suffix_suffix [simp]: "suffix m (suffix k x) = suffix (k+m) x"
  by (rule ext) (simp add: suffix_def add.assoc)

lemma subsequence_append: "prefix (i + j) w = prefix i w @ (w [i \<rightarrow> i + j])"
  unfolding map_append[symmetric] upt_add_eq_append[OF le0] subsequence_def ..

lemma subsequence_drop[simp]: "drop i (w [j \<rightarrow> k]) = w [j + i \<rightarrow> k]"
  by (simp add: subsequence_def drop_map)

lemma subsequence_empty[simp]: "w [i \<rightarrow> j] = [] \<longleftrightarrow> j \<le> i"
  by (auto simp add: subsequence_def)

lemma subsequence_length[simp]: "length (subsequence w i j) = j - i"
  by (simp add: subsequence_def)

lemma subsequence_nth[simp]: "k < j - i \<Longrightarrow> (w [i \<rightarrow> j]) ! k = w (i + k)"
  unfolding subsequence_def
  by auto

lemma subseq_to_zero[simp]: "w[i\<rightarrow>0] = []"
  by simp

lemma subseq_to_smaller[simp]: "i\<ge>j \<Longrightarrow> w[i\<rightarrow>j] = []"
  by simp

lemma subseq_to_Suc[simp]: "i\<le>j \<Longrightarrow> w [i \<rightarrow> Suc j] = w [ i \<rightarrow> j ] @ [w j]"
  by (auto simp: subsequence_def)

lemma subsequence_singleton[simp]: "w [i \<rightarrow> Suc i] = [w i]"
  by (auto simp: subsequence_def)


lemma subsequence_prefix_suffix: "prefix (j - i) (suffix i w) = w [i \<rightarrow> j]"
proof (cases "i \<le> j")
  case True
  have "w [i \<rightarrow> j] = map w (map (\<lambda>n. n + i) [0..<j - i])"
    unfolding map_add_upt subsequence_def
    using le_add_diff_inverse2[OF True] by force
  also
  have "\<dots> = map (\<lambda>n. w (n + i)) [0..<j - i]"
    unfolding map_map comp_def by blast
  finally
  show ?thesis
    unfolding subsequence_def suffix_def add.commute[of i] by simp
next
  case False
  then show ?thesis
    by (simp add: subsequence_def)
qed

lemma prefix_suffix: "x = prefix n x \<frown> (suffix n x)"
  by (rule ext) (simp add: subsequence_def conc_def)

declare prefix_suffix[symmetric, simp]


lemma word_split: obtains v\<^sub>1 v\<^sub>2 where "v = v\<^sub>1 \<frown> v\<^sub>2" "length v\<^sub>1 = k"
proof
  show "v = prefix k v \<frown> suffix k v"
    by (rule prefix_suffix)
  show "length (prefix k v) = k"
    by simp
qed


lemma set_subsequence[simp]: "set (w[i\<rightarrow>j]) = w`{i..<j}"
  unfolding subsequence_def by auto

lemma subsequence_take[simp]: "take i (w [j \<rightarrow> k]) = w [j \<rightarrow> min (j + i) k]"
  by (simp add: subsequence_def take_map min_def)

lemma subsequence_shift[simp]: "(suffix i w) [j \<rightarrow> k] = w [i + j \<rightarrow> i + k]"
  by (metis add_diff_cancel_left subsequence_prefix_suffix suffix_suffix)

lemma suffix_subseq_join[simp]: "i \<le> j \<Longrightarrow> v [i \<rightarrow> j] \<frown> suffix j v = suffix i v"
  by (metis (no_types, lifting) Nat.add_0_right le_add_diff_inverse prefix_suffix
    subsequence_shift suffix_suffix)

lemma prefix_conc_fst[simp]:
  assumes "j \<le> length w"
  shows "prefix j (w \<frown> w') = take j w"
proof -
  have "\<forall>i < j. (prefix j (w \<frown> w')) ! i = (take j w) ! i"
    using assms by (simp add: conc_fst subsequence_def)
  thus ?thesis
    by (simp add: assms list_eq_iff_nth_eq min.absorb2)
qed

lemma prefix_conc_snd[simp]:
  assumes "n \<ge> length u"
  shows "prefix n (u \<frown> v) = u @ prefix (n - length u) v"
proof (intro nth_equalityI)
  show "length (prefix n (u \<frown> v)) = length (u @ prefix (n - length u) v)"
    using assms by simp
  fix i
  assume "i < length (prefix n (u \<frown> v))"
  then show "prefix n (u \<frown> v) ! i = (u @ prefix (n - length u) v) ! i"
    by (cases "i < length u") (auto simp: nth_append)
qed

lemma prefix_conc_length[simp]: "prefix (length w) (w \<frown> w') = w"
  by simp

lemma suffix_conc_fst[simp]:
  assumes "n \<le> length u"
  shows "suffix n (u \<frown> v) = drop n u \<frown> v"
proof
  show "suffix n (u \<frown> v) i = (drop n u \<frown> v) i" for i
    using assms by (cases "n + i < length u") (auto simp: algebra_simps)
qed

lemma suffix_conc_snd[simp]:
  assumes "n \<ge> length u"
  shows "suffix n (u \<frown> v) = suffix (n - length u) v"
proof
  show "suffix n (u \<frown> v) i = suffix (n - length u) v i" for i
    using assms by simp
qed

lemma suffix_conc_length[simp]: "suffix (length w) (w \<frown> w') = w'"
  unfolding conc_def by force

lemma concat_eq[iff]:
  assumes "length v\<^sub>1 = length v\<^sub>2"
  shows "v\<^sub>1 \<frown> u\<^sub>1 = v\<^sub>2 \<frown> u\<^sub>2 \<longleftrightarrow> v\<^sub>1 = v\<^sub>2 \<and> u\<^sub>1 = u\<^sub>2"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have 1: "(v\<^sub>1 \<frown> u\<^sub>1) i = (v\<^sub>2 \<frown> u\<^sub>2) i" for i by auto
  show ?rhs
  proof (intro conjI ext nth_equalityI)
    show "length v\<^sub>1 = length v\<^sub>2" by (rule assms(1))
  next
    fix i
    assume 2: "i < length v\<^sub>1"
    have 3: "i < length v\<^sub>2" using assms(1) 2 by simp
    show "v\<^sub>1 ! i = v\<^sub>2 ! i" using 1[of i] 2 3 by simp
  next
    show "u\<^sub>1 i = u\<^sub>2 i" for i
      using 1[of "length v\<^sub>1 + i"] assms(1) by simp
  qed
next
  assume ?rhs
  then show ?lhs by simp
qed

lemma same_concat_eq[iff]: "u \<frown> v = u \<frown> w \<longleftrightarrow> v = w"
  by simp

lemma comp_concat[simp]: "f \<circ> u \<frown> v = map f u \<frown> (f \<circ> v)"
proof
  fix i
  show "(f \<circ> u \<frown> v) i = (map f u \<frown> (f \<circ> v)) i"
    by (cases "i < length u") simp_all
qed


subsection \<open>Prepending\<close>

primrec build :: "'a \<Rightarrow> 'a word \<Rightarrow> 'a word"  (infixr \<open>##\<close> 65)
  where "(a ## w) 0 = a" | "(a ## w) (Suc i) = w i"

lemma build_eq[iff]: "a\<^sub>1 ## w\<^sub>1 = a\<^sub>2 ## w\<^sub>2 \<longleftrightarrow> a\<^sub>1 = a\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2"
proof
  assume 1: "a\<^sub>1 ## w\<^sub>1 = a\<^sub>2 ## w\<^sub>2"
  have 2: "(a\<^sub>1 ## w\<^sub>1) i = (a\<^sub>2 ## w\<^sub>2) i" for i
    using 1 by auto
  show "a\<^sub>1 = a\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2"
  proof (intro conjI ext)
    show "a\<^sub>1 = a\<^sub>2"
      using 2[of "0"] by simp
    show "w\<^sub>1 i = w\<^sub>2 i" for i
      using 2[of "Suc i"] by simp
  qed
next
  assume 1: "a\<^sub>1 = a\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2"
  show "a\<^sub>1 ## w\<^sub>1 = a\<^sub>2 ## w\<^sub>2" using 1 by simp
qed

lemma build_cons[simp]: "(a # u) \<frown> v = a ## u \<frown> v"
proof
  fix i
  show "((a # u) \<frown> v) i = (a ## u \<frown> v) i"
  proof (cases i)
    case 0
    show ?thesis unfolding 0 by simp
  next
    case (Suc j)
    show ?thesis unfolding Suc by (cases "j < length u", simp+)
  qed
qed

lemma build_append[simp]: "(w @ a # u) \<frown> v = w \<frown> a ## u \<frown> v"
  unfolding conc_conc[symmetric] by simp

lemma build_first[simp]: "w 0 ## suffix (Suc 0) w = w"
proof
  show "(w 0 ## suffix (Suc 0) w) i = w i" for i
    by (cases i) simp_all
qed

lemma build_split[intro]: "w = w 0 ## suffix 1 w"
  by simp

lemma build_range[simp]: "range (a ## w) = insert a (range w)"
proof safe
  show "(a ## w) i \<notin> range w \<Longrightarrow> (a ## w) i = a" for i
    by (cases i) auto
  show "a \<in> range (a ## w)"
  proof (rule range_eqI)
    show "a = (a ## w) 0" by simp
  qed
  show "w i \<in> range (a ## w)" for i
  proof (rule range_eqI)
    show "w i = (a ## w) (Suc i)" by simp
  qed
qed

lemma suffix_singleton_suffix[simp]: "w i ## suffix (Suc i) w = suffix i w"
  using suffix_subseq_join[of i "Suc i" w]
  by simp

text \<open>Find the first occurrence of a letter from a given set\<close>
lemma word_first_split_set:
  assumes "A \<inter> range w \<noteq> {}"
  obtains u a v where "w = u \<frown> [a] \<frown> v" "A \<inter> set u = {}" "a \<in> A"
proof -
  define i where "i = (LEAST i. w i \<in> A)"
  show ?thesis
  proof
    show "w = prefix i w \<frown> [w i] \<frown> suffix (Suc i) w"
      by simp
    show "A \<inter> set (prefix i w) = {}"
      apply safe
      subgoal premises prems for a
      proof -
        from prems obtain k where 3: "k < i" "w k = a"
          by auto
        have 4: "w k \<notin> A"
          using not_less_Least 3(1) unfolding i_def .
        show ?thesis
          using prems(1) 3(2) 4 by auto
      qed
      done
    show "w i \<in> A"
      using LeastI assms(1) unfolding i_def by fast
  qed
qed


subsection \<open>The limit set of an $\omega$-word\<close>

text \<open>
  The limit set (also called infinity set) of an $\omega$-word
  is the set of letters that appear infinitely often in the word.
  This set plays an important role in defining acceptance conditions
  of $\omega$-automata.
\<close>

definition limit :: "'a word \<Rightarrow> 'a set"
  where "limit x \<equiv> {a . \<exists>\<^sub>\<infinity>n . x n = a}"

lemma limit_iff_frequent: "a \<in> limit x \<longleftrightarrow> (\<exists>\<^sub>\<infinity>n . x n = a)"
  by (simp add: limit_def)

text \<open>
  The following is a different way to define the limit,
  using the reverse image, making the laws about reverse
  image applicable to the limit set.
  (Might want to change the definition above?)
\<close>

lemma limit_vimage: "(a \<in> limit x) = infinite (x -` {a})"
  by (simp add: limit_def Inf_many_def vimage_def)

lemma two_in_limit_iff:
  "({a, b} \<subseteq> limit x) =
    ((\<exists>n. x n =a ) \<and> (\<forall>n. x n = a \<longrightarrow> (\<exists>m>n. x m = b)) \<and> (\<forall>m. x m = b \<longrightarrow> (\<exists>n>m. x n = a)))"
  (is "?lhs = (?r1 \<and> ?r2 \<and> ?r3)")
proof
  assume lhs: "?lhs"
  hence 1: "?r1" by (auto simp: limit_def elim: INFM_EX)
  from lhs have "\<forall>n. \<exists>m>n. x m = b" by (auto simp: limit_def INFM_nat)
  hence 2: "?r2" by simp
  from lhs have "\<forall>m. \<exists>n>m. x n = a" by (auto simp: limit_def INFM_nat)
  hence 3: "?r3" by simp
  from 1 2 3 show "?r1 \<and> ?r2 \<and> ?r3" by simp
next
  assume "?r1 \<and> ?r2 \<and> ?r3"
  hence 1: "?r1" and 2: "?r2" and 3: "?r3" by simp+
  have infa: "\<forall>m. \<exists>n\<ge>m. x n = a"
  proof
    fix m
    show "\<exists>n\<ge>m. x n = a" (is "?A m")
    proof (induct m)
      from 1 show "?A 0" by simp
    next
      fix m
      assume ih: "?A m"
      then obtain n where n: "n \<ge> m" "x n = a" by auto
      with 2 obtain k where k: "k>n" "x k = b" by auto
      with 3 obtain l where l: "l>k" "x l = a" by auto
      from n k l have "l \<ge> Suc m" by auto
      with l show "?A (Suc m)" by auto
    qed
  qed
  hence infa': "\<exists>\<^sub>\<infinity>n. x n = a" by (simp add: INFM_nat_le)
  have "\<forall>n. \<exists>m>n. x m = b"
  proof
    fix n
    from infa obtain k where k1: "k\<ge>n" and k2: "x k = a" by auto
    from 2 k2 obtain l where l1: "l>k" and l2: "x l = b" by auto
    from k1 l1 have "l > n" by auto
    with l2 show "\<exists>m>n. x m = b" by auto
  qed
  hence "\<exists>\<^sub>\<infinity>m. x m = b" by (simp add: INFM_nat)
  with infa' show "?lhs" by (auto simp: limit_def)
qed

text \<open>
  For $\omega$-words over a finite alphabet, the limit set is
  non-empty. Moreover, from some position onward, any such word
  contains only letters from its limit set.
\<close>

lemma limit_nonempty:
  assumes fin: "finite (range x)"
  shows "\<exists>a. a \<in> limit x"
proof -
  from fin obtain a where "a \<in> range x \<and> infinite (x -` {a})"
    by (rule inf_img_fin_domE) auto
  hence "a \<in> limit x"
    by (auto simp add: limit_vimage)
  thus ?thesis ..
qed

lemmas limit_nonemptyE = limit_nonempty[THEN exE]

lemma limit_inter_INF:
  assumes hyp: "limit w \<inter> S \<noteq> {}"
  shows "\<exists>\<^sub>\<infinity> n. w n \<in> S"
proof -
  from hyp obtain x where "\<exists>\<^sub>\<infinity> n. w n = x" and "x \<in> S"
    by (auto simp add: limit_def)
  thus ?thesis
    by (auto elim: INFM_mono)
qed

text \<open>
  The reverse implication is true only if $S$ is finite.
\<close>

lemma INF_limit_inter:
  assumes hyp: "\<exists>\<^sub>\<infinity> n. w n \<in>  S"
    and fin: "finite (S \<inter> range w)"
  shows  "\<exists>a. a \<in> limit w \<inter> S"
proof (rule ccontr)
  assume contra: "\<not>(\<exists>a. a \<in> limit w \<inter> S)"
  hence "\<forall>a\<in>S. finite {n. w n = a}"
    by (auto simp add: limit_def Inf_many_def)
  with fin have "finite (UN a:S \<inter> range w. {n. w n = a})"
    by auto
  moreover
  have "(UN a:S \<inter> range w. {n. w n = a}) = {n. w n \<in> S}"
    by auto
  moreover
  note hyp
  ultimately show "False"
    by (simp add: Inf_many_def)
qed

lemma fin_ex_inf_eq_limit: "finite A \<Longrightarrow> (\<exists>\<^sub>\<infinity>i. w i \<in> A) \<longleftrightarrow> limit w \<inter> A \<noteq> {}"
  by (metis INF_limit_inter equals0D finite_Int limit_inter_INF)

lemma limit_in_range_suffix: "limit x \<subseteq> range (suffix k x)"
proof
  fix a
  assume "a \<in> limit x"
  then obtain l where
    kl: "k < l" and xl: "x l = a"
    by (auto simp add: limit_def INFM_nat)
  from kl obtain m where "l = k+m"
    by (auto simp add:  less_iff_Suc_add)
  with xl show "a \<in> range (suffix k x)"
    by auto
qed

lemma limit_in_range: "limit r \<subseteq> range r"
  using limit_in_range_suffix[of r 0] by simp

lemmas limit_in_range_suffixD = limit_in_range_suffix[THEN subsetD]

lemma limit_subset: "limit f \<subseteq> f ` {n..}"
  using limit_in_range_suffix[of f n] unfolding suffix_def by auto

theorem limit_is_suffix:
  assumes fin: "finite (range x)"
  shows "\<exists>k. limit x = range (suffix k x)"
proof -
  have "\<exists>k. range (suffix k x) \<subseteq> limit x"
  proof -
    \<comment> \<open>The set of letters that are not in the limit is certainly finite.\<close>
    from fin have "finite (range x - limit x)"
      by simp
    \<comment> \<open>Moreover, any such letter occurs only finitely often\<close>
    moreover
    have "\<forall>a \<in> range x - limit x. finite (x -` {a})"
      by (auto simp add: limit_vimage)
    \<comment> \<open>Thus, there are only finitely many occurrences of such letters.\<close>
    ultimately have "finite (UN a : range x - limit x. x -` {a})"
      by (blast intro: finite_UN_I)
    \<comment> \<open>Therefore these occurrences are within some initial interval.\<close>
    then obtain k where "(UN a : range x - limit x. x -` {a}) \<subseteq> {..<k}"
      by (blast dest: finite_nat_bounded)
    \<comment> \<open>This is just the bound we are looking for.\<close>
    hence "\<forall>m. k \<le> m \<longrightarrow> x m \<in> limit x"
      by (auto simp add: limit_vimage)
    hence "range (suffix k x) \<subseteq> limit x"
      by auto
    thus ?thesis ..
  qed
  then obtain k where "range (suffix k x) \<subseteq> limit x" ..
  with limit_in_range_suffix
  have "limit x = range (suffix k x)"
    by (rule subset_antisym)
  thus ?thesis ..
qed

lemmas limit_is_suffixE = limit_is_suffix[THEN exE]


text \<open>
  The limit set enjoys some simple algebraic laws with respect
  to concatenation, suffixes, iteration, and renaming.
\<close>

theorem limit_conc [simp]: "limit (w \<frown> x) = limit x"
proof (auto)
  fix a assume a: "a \<in> limit (w \<frown> x)"
  have "\<forall>m. \<exists>n. m<n \<and> x n = a"
  proof
    fix m
    from a obtain n where "m + length w < n \<and> (w \<frown> x) n = a"
      by (auto simp add: limit_def Inf_many_def infinite_nat_iff_unbounded)
    hence "m < n - length w \<and> x (n - length w) = a"
      by (auto simp add: conc_def)
    thus "\<exists>n. m<n \<and> x n = a" ..
  qed
  hence "infinite {n . x n = a}"
    by (simp add: infinite_nat_iff_unbounded)
  thus "a \<in> limit x"
    by (simp add: limit_def Inf_many_def)
next
  fix a assume a: "a \<in> limit x"
  have "\<forall>m. length w < m \<longrightarrow> (\<exists>n. m<n \<and> (w \<frown> x) n = a)"
  proof (clarify)
    fix m
    assume m: "length w < m"
    with a obtain n where "m - length w < n \<and> x n = a"
      by (auto simp add: limit_def Inf_many_def infinite_nat_iff_unbounded)
    with m have "m < n + length w \<and> (w \<frown> x) (n + length w) = a"
      by (simp add: conc_def, arith)
    thus "\<exists>n. m<n \<and> (w \<frown> x) n = a" ..
  qed
  hence "infinite {n . (w \<frown> x) n = a}"
    by (simp add: unbounded_k_infinite)
  thus "a \<in> limit (w \<frown> x)"
    by (simp add: limit_def Inf_many_def)
qed

theorem limit_suffix [simp]: "limit (suffix n x) = limit x"
proof -
  have "x = (prefix n x) \<frown> (suffix n x)"
    by (simp add: prefix_suffix)
  hence "limit x = limit (prefix n x \<frown> suffix n x)"
    by simp
  also have "\<dots> = limit (suffix n x)"
    by (rule limit_conc)
  finally show ?thesis
    by (rule sym)
qed

theorem limit_iter [simp]:
  assumes nempty: "0 < length w"
  shows "limit w\<^sup>\<omega> = set w"
proof
  have "limit w\<^sup>\<omega> \<subseteq> range w\<^sup>\<omega>"
    by (auto simp add: limit_def dest: INFM_EX)
  also from nempty have "\<dots> \<subseteq> set w"
    by auto
  finally show "limit w\<^sup>\<omega> \<subseteq> set w" .
next
  {
    fix a assume a: "a \<in> set w"
    then obtain k where k: "k < length w \<and> w!k = a"
      by (auto simp add: set_conv_nth)
    \<comment> \<open>the following bound is terrible, but it simplifies the proof\<close>
    from nempty k have "\<forall>m. w\<^sup>\<omega> ((Suc m)*(length w) + k) = a"
      by (simp add: mod_add_left_eq [symmetric])
    moreover
    \<comment> \<open>why is the following so hard to prove??\<close>
    have "\<forall>m. m < (Suc m)*(length w) + k"
    proof
      fix m
      from nempty have "1 \<le> length w" by arith
      hence "m*1 \<le> m*length w" by simp
      hence "m \<le> m*length w" by simp
      with nempty have "m < length w + (m*length w) + k" by arith
      thus "m < (Suc m)*(length w) + k" by simp
    qed
    moreover note nempty
    ultimately have "a \<in> limit w\<^sup>\<omega>"
      by (auto simp add: limit_iff_frequent INFM_nat)
  }
  then show "set w \<subseteq> limit w\<^sup>\<omega>" by auto
qed

lemma limit_o [simp]:
  assumes a: "a \<in> limit w"
  shows "f a \<in> limit (f \<circ> w)"
proof -
  from a
  have "\<exists>\<^sub>\<infinity>n. w n = a"
    by (simp add: limit_iff_frequent)
  hence "\<exists>\<^sub>\<infinity>n. f (w n) = f a"
    by (rule INFM_mono, simp)
  thus "f a \<in> limit (f \<circ> w)"
    by (simp add: limit_iff_frequent)
qed

text \<open>
  The converse relation is not true in general: $f(a)$ can be in the
  limit of $f \circ w$ even though $a$ is not in the limit of $w$.
  However, \<open>limit\<close> commutes with renaming if the function is
  injective. More generally, if $f(a)$ is the image of only finitely
  many elements, some of these must be in the limit of $w$.
\<close>

lemma limit_o_inv:
  assumes fin: "finite (f -` {x})"
    and x: "x \<in> limit (f \<circ> w)"
  shows "\<exists>a \<in> (f -` {x}). a \<in> limit w"
proof (rule ccontr)
  assume contra: "\<not> ?thesis"
  \<comment> \<open>hence, every element in the pre-image occurs only finitely often\<close>
  then have "\<forall>a \<in> (f -` {x}). finite {n. w n = a}"
    by (simp add: limit_def Inf_many_def)
  \<comment> \<open>so there are only finitely many occurrences of any such element\<close>
  with fin have "finite (\<Union> a \<in> (f -` {x}). {n. w n = a})"
    by auto
  \<comment> \<open>these are precisely those positions where $x$ occurs in $f \circ w$\<close>
  moreover
  have "(\<Union> a \<in> (f -` {x}). {n. w n = a}) = {n. f(w n) = x}"
    by auto
  ultimately
  \<comment> \<open>so $x$ can occur only finitely often in the translated word\<close>
  have "finite {n. f(w n) = x}"
    by simp
  \<comment> \<open>\ldots\ which yields a contradiction\<close>
  with x show "False"
    by (simp add: limit_def Inf_many_def)
qed

theorem limit_inj [simp]:
  assumes inj: "inj f"
  shows "limit (f \<circ> w) = f ` (limit w)"
proof
  show "f ` limit w \<subseteq> limit (f \<circ> w)"
    by auto
  show "limit (f \<circ> w) \<subseteq> f ` limit w"
  proof
    fix x
    assume x: "x \<in> limit (f \<circ> w)"
    from inj have "finite (f -` {x})"
      by (blast intro: finite_vimageI)
    with x obtain a where a: "a \<in> (f -` {x}) \<and> a \<in> limit w"
      by (blast dest: limit_o_inv)
    thus "x \<in> f ` (limit w)"
      by auto
  qed
qed

lemma limit_inter_empty:
  assumes fin: "finite (range w)"
  assumes hyp: "limit w \<inter> S = {}"
  shows "\<forall>\<^sub>\<infinity>n. w n \<notin> S"
proof -
  from fin obtain k where k_def: "limit w = range (suffix k w)"
    using limit_is_suffix by blast
  have "w (k + k') \<notin> S" for k'
    using hyp unfolding k_def suffix_def image_def by blast
  thus ?thesis
    unfolding MOST_nat_le using le_Suc_ex by blast
qed

text \<open>If the limit is the suffix of the sequence's range,
  we may increase the suffix index arbitrarily\<close>
lemma limit_range_suffix_incr:
  assumes "limit r = range (suffix i r)"
  assumes "j\<ge>i"
  shows "limit r = range (suffix j r)"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = range (suffix i r)"
    using assms by simp
  moreover
  have "\<dots> \<supseteq> ?rhs" using \<open>j\<ge>i\<close>
    by (metis (mono_tags, lifting) assms(2)
        image_subsetI le_Suc_ex range_eqI suffix_def suffix_suffix)
  moreover
  have "\<dots> \<supseteq> ?lhs" by (rule limit_in_range_suffix)
  ultimately
  show "?lhs = ?rhs"
    by (metis antisym_conv limit_in_range_suffix)
qed

text \<open>For two finite sequences, we can find a common suffix index such
  that the limits can be represented as these suffixes' ranges.\<close>
lemma common_range_limit:
  assumes "finite (range x)"
    and "finite (range y)"
  obtains i where "limit x = range (suffix i x)"
    and "limit y = range (suffix i y)"
proof -
  obtain i j where 1: "limit x = range (suffix i x)"
    and 2: "limit y = range (suffix j y)"
    using assms limit_is_suffix by metis
  have "limit x = range (suffix (max i j) x)"
    and "limit y = range (suffix (max i j) y)"
    using limit_range_suffix_incr[OF 1] limit_range_suffix_incr[OF 2]
    by auto
  thus ?thesis
    using that by metis
qed


subsection \<open>Index sequences and piecewise definitions\<close>

text \<open>
  A word can be defined piecewise: given a sequence of words $w_0, w_1, \ldots$
  and a strictly increasing sequence of integers $i_0, i_1, \ldots$ where $i_0=0$,
  a single word is obtained by concatenating subwords of the $w_n$ as given by
  the integers: the resulting word is
  \[
    (w_0)_{i_0} \ldots (w_0)_{i_1-1} (w_1)_{i_1} \ldots (w_1)_{i_2-1} \ldots
  \]
  We prepare the field by proving some trivial facts about such sequences of
  indexes.
\<close>

definition idx_sequence :: "nat word \<Rightarrow> bool"
  where "idx_sequence idx \<equiv> (idx 0 = 0) \<and> (\<forall>n. idx n < idx (Suc n))"

lemma idx_sequence_less:
  assumes iseq: "idx_sequence idx"
  shows "idx n < idx (Suc(n+k))"
proof (induct k)
  from iseq show "idx n < idx (Suc (n + 0))"
    by (simp add: idx_sequence_def)
next
  fix k
  assume ih: "idx n < idx (Suc(n+k))"
  from iseq have "idx (Suc(n+k)) < idx (Suc(n + Suc k))"
    by (simp add: idx_sequence_def)
  with ih show "idx n < idx (Suc(n + Suc k))"
    by (rule less_trans)
qed

lemma idx_sequence_inj:
  assumes iseq: "idx_sequence idx"
    and eq: "idx m = idx n"
  shows "m = n"
proof (cases m n rule: linorder_cases)
  case greater
  then obtain k where "m = Suc(n+k)"
    by (auto simp add: less_iff_Suc_add)
  with iseq have "idx n < idx m"
    by (simp add: idx_sequence_less)
  with eq show ?thesis
    by simp
next
  case less
  then obtain k where "n = Suc(m+k)"
    by (auto simp add: less_iff_Suc_add)
  with iseq have "idx m < idx n"
    by (simp add: idx_sequence_less)
  with eq show ?thesis
    by simp
qed

lemma idx_sequence_mono:
  assumes iseq: "idx_sequence idx"
    and m: "m \<le> n"
  shows "idx m \<le> idx n"
proof (cases "m=n")
  case True
  thus ?thesis by simp
next
  case False
  with m have "m < n" by simp
  then obtain k where "n = Suc(m+k)"
    by (auto simp add: less_iff_Suc_add)
  with iseq have "idx m < idx n"
    by (simp add: idx_sequence_less)
  thus ?thesis by simp
qed

text \<open>
  Given an index sequence, every natural number is contained in the
  interval defined by two adjacent indexes, and in fact this interval
  is determined uniquely.
\<close>

lemma idx_sequence_idx:
  assumes "idx_sequence idx"
  shows "idx k \<in> {idx k ..< idx (Suc k)}"
using assms by (auto simp add: idx_sequence_def)

lemma idx_sequence_interval:
  assumes iseq: "idx_sequence idx"
  shows "\<exists>k. n \<in> {idx k ..< idx (Suc k) }"
    (is "?P n" is "\<exists>k. ?in n k")
proof (induct n)
  from iseq have "0 = idx 0"
    by (simp add: idx_sequence_def)
  moreover
  from iseq have "idx 0 \<in> {idx 0 ..< idx (Suc 0) }"
    by (rule idx_sequence_idx)
  ultimately
  show "?P 0" by auto
next
  fix n
  assume "?P n"
  then obtain k where k: "?in n k" ..
  show "?P (Suc n)"
  proof (cases "Suc n < idx (Suc k)")
    case True
    with k have "?in (Suc n) k"
      by simp
    thus ?thesis ..
  next
    case False
    with k have "Suc n = idx (Suc k)"
      by auto
    with iseq have "?in (Suc n) (Suc k)"
      by (simp add: idx_sequence_def)
    thus ?thesis ..
  qed
qed

lemma idx_sequence_interval_unique:
  assumes iseq: "idx_sequence idx"
    and k: "n \<in> {idx k ..< idx (Suc k)}"
    and m: "n \<in> {idx m ..< idx (Suc m)}"
  shows "k = m"
proof (cases k m rule: linorder_cases)
  case less
  hence "Suc k \<le> m" by simp
  with iseq have "idx (Suc k) \<le> idx m"
    by (rule idx_sequence_mono)
  with m have "idx (Suc k) \<le> n"
    by auto
  with k have "False"
    by simp
  thus ?thesis ..
next
  case greater
  hence "Suc m \<le> k" by simp
  with iseq have "idx (Suc m) \<le> idx k"
    by (rule idx_sequence_mono)
  with k have "idx (Suc m) \<le> n"
    by auto
  with m have "False"
    by simp
  thus ?thesis ..
qed

lemma idx_sequence_unique_interval:
  assumes iseq: "idx_sequence idx"
  shows "\<exists>! k. n \<in> {idx k ..< idx (Suc k) }"
proof (rule ex_ex1I)
  from iseq show "\<exists>k. n \<in> {idx k ..< idx (Suc k)}"
    by (rule idx_sequence_interval)
next
  fix k y
  assume "n \<in> {idx k..<idx (Suc k)}" and "n \<in> {idx y..<idx (Suc y)}"
  with iseq show "k = y" by (auto elim: idx_sequence_interval_unique)
qed

text \<open>
  Now we can define the piecewise construction of a word using
  an index sequence.
\<close>

definition merge :: "'a word word \<Rightarrow> nat word \<Rightarrow> 'a word"
  where "merge ws idx \<equiv> \<lambda>n. let i = THE i. n \<in> {idx i ..< idx (Suc i) } in ws i n"

lemma merge:
  assumes idx: "idx_sequence idx"
    and n: "n \<in> {idx i ..< idx (Suc i)}"
  shows "merge ws idx n = ws i n"
proof -
  from n have "(THE k. n \<in> {idx k ..< idx (Suc k) }) = i"
    by (rule the_equality[OF _ sym[OF idx_sequence_interval_unique[OF idx n]]]) simp
  thus ?thesis
    by (simp add: merge_def Let_def)
qed

lemma merge0:
  assumes idx: "idx_sequence idx"
  shows "merge ws idx 0 = ws 0 0"
proof (rule merge[OF idx])
  from idx have "idx 0 < idx (Suc 0)"
    unfolding idx_sequence_def by blast
  with idx show "0 \<in> {idx 0 ..< idx (Suc 0)}"
    by (simp add: idx_sequence_def)
qed

lemma merge_Suc:
  assumes idx: "idx_sequence idx"
    and n: "n \<in> {idx i ..< idx (Suc i)}"
  shows "merge ws idx (Suc n) = (if Suc n = idx (Suc i) then ws (Suc i) else ws i) (Suc n)"
proof auto
  assume eq: "Suc n = idx (Suc i)"
  from idx have "idx (Suc i) < idx (Suc(Suc i))"
    unfolding idx_sequence_def by blast
  with eq idx show "merge ws idx (idx (Suc i)) = ws (Suc i) (idx (Suc i))"
    by (simp add: merge)
next
  assume neq: "Suc n \<noteq> idx (Suc i)"
  with n have "Suc n \<in> {idx i ..< idx (Suc i) }"
    by auto
  with idx show "merge ws idx (Suc n) = ws i (Suc n)"
    by (rule merge)
qed

end
