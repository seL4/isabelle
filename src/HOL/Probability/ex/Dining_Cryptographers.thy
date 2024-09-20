theory Dining_Cryptographers
imports "HOL-Probability.Information"
begin

lemma image_ex1_eq: "inj_on f A \<Longrightarrow> (b \<in> f ` A) \<longleftrightarrow> (\<exists>!x \<in> A. b = f x)"
  by (unfold inj_on_def) blast

lemma Ex1_eq: "\<exists>!x. P x \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> x = y"
  by auto

subsection \<open>Define the state space\<close>

text \<open>

We introduce the state space on which the algorithm operates.

This contains:

\begin{description}
\item[n]
  The number of cryptographers on the table.

\item[payer]
  Either one of the cryptographers or the NSA.

\item[coin]
  The result of the coin flipping for each cryptographer.

\item[inversion]
  The public result for each cryptographer, e.g. the sum of the coin flipping
  for the cryptographer, its right neighbour and the information if he paid or
  not.

\end{description}

The observables are the \emph{inversions}

\<close>

locale dining_cryptographers_space =
  fixes n :: nat
  assumes n_gt_3: "n \<ge> 3"
begin

definition "dining_cryptographers =
  ({None} \<union> Some ` {0..<n}) \<times> {xs :: bool list. length xs = n}"
definition "payer dc = fst dc"
definition coin :: "(nat option \<times> bool list) \<Rightarrow> nat \<Rightarrow> bool" where
  "coin dc c = snd dc ! (c mod n)"
definition "inversion dc =
  map (\<lambda>c. (payer dc = Some c) \<noteq> (coin dc c \<noteq> coin dc (c + 1))) [0..<n]"

definition "result dc = foldl (\<lambda> a b. a \<noteq> b) False (inversion dc)"

lemma coin_n[simp]: "coin dc n = coin dc 0"
  unfolding coin_def by simp

theorem correctness:
  assumes "dc \<in> dining_cryptographers"
  shows "result dc \<longleftrightarrow> (payer dc \<noteq> None)"
proof -
  let ?XOR = "\<lambda>f l. foldl (\<noteq>) False (map f [0..<l])"

  have foldl_coin:
    "\<not> ?XOR (\<lambda>c. coin dc c \<noteq> coin dc (c + 1)) n"
  proof -
    define n' where "n' = n" \<comment> \<open>Need to hide n, as it is hidden in coin\<close>
    have "?XOR (\<lambda>c. coin dc c \<noteq> coin dc (c + 1)) n'
        = (coin dc 0 \<noteq> coin dc n')"
      by (induct n') auto
    thus ?thesis using \<open>n' \<equiv> n\<close> by simp
  qed

  from assms have "payer dc = None \<or> (\<exists>k<n. payer dc = Some k)"
    unfolding dining_cryptographers_def payer_def by auto
  thus ?thesis
  proof (rule disjE)
    assume "payer dc = None"
    thus ?thesis unfolding result_def inversion_def
      using foldl_coin by simp
  next
    assume "\<exists>k<n. payer dc = Some k"
    then obtain k where "k < n" and "payer dc = Some k" by auto
    define l where "l = n" \<comment> \<open>Need to hide n, as it is hidden in coin, payer etc.\<close>
    have "?XOR (\<lambda>c. (payer dc = Some c) \<noteq> (coin dc c \<noteq> coin dc (c + 1))) l =
        ((k < l) \<noteq> ?XOR (\<lambda>c. (coin dc c \<noteq> coin dc (c + 1))) l)"
      using \<open>payer dc = Some k\<close> by (induct l) auto
    thus ?thesis
      unfolding result_def inversion_def l_def
      using \<open>payer dc = Some k\<close> foldl_coin \<open>k < n\<close> by simp
  qed
qed

text \<open>

We now restrict the state space for the dining cryptographers to the cases when
one of the cryptographer pays.

\<close>

definition
  "dc_crypto = dining_cryptographers - {None}\<times>UNIV"

lemma dc_crypto: "dc_crypto = Some ` {0..<n} \<times> {xs :: bool list. length xs = n}"
  unfolding dc_crypto_def dining_cryptographers_def by auto

lemma image_payer_dc_crypto: "payer ` dc_crypto = Some ` {0..<n}"
proof -
  have *: "{xs. length xs = n} \<noteq> {}"
    by (auto intro!: exI[of _ "replicate n undefined"])
  show ?thesis
    unfolding payer_def [abs_def] dc_crypto fst_image_times if_not_P[OF *] ..
qed

lemma card_payer_and_inversion:
  assumes "xs \<in> inversion ` dc_crypto" and "i < n"
  shows "card {dc \<in> dc_crypto. payer dc = Some i \<and> inversion dc = xs} = 2"
    (is "card ?S = 2")
proof -
  obtain ys j where xs_inv: "inversion (Some j, ys) = xs" and
    "j < n" and "(Some j, ys) \<in> dc_crypto"
    using assms(1) by (auto simp: dc_crypto)

  hence "length ys = n" by (simp add: dc_crypto)
  have [simp]: "length xs = n" using xs_inv[symmetric] by (simp add: inversion_def)

  { fix b
    have "inj_on (\<lambda>x. inversion (Some i, x)) {ys. ys ! 0 = b \<and> length ys = length xs}"
    proof (rule inj_onI)
      fix x y
      assume "x \<in> {ys. ys ! 0 = b \<and> length ys = length xs}"
        and "y \<in> {ys. ys ! 0 = b \<and> length ys = length xs}"
        and inv: "inversion (Some i, x) = inversion (Some i, y)"
      hence [simp]: "x ! 0 = y ! 0" "length y = n" "length x = n"
        using \<open>length xs = n\<close> by simp_all
      have *: "\<And>j. j < n \<Longrightarrow>
        (x ! j = x ! (Suc j mod n)) = (y ! j = y ! (Suc j mod n))"
        using inv unfolding inversion_def map_eq_conv payer_def coin_def
        by fastforce
      show "x = y"
      proof (rule nth_equalityI, simp)
        fix j assume "j < length x" hence "j < n" using \<open>length xs = n\<close> by simp
        thus "x ! j = y ! j"
        proof (induct j)
          case (Suc j)
          hence "j < n" by simp
          with Suc show ?case using *[OF \<open>j < n\<close>]
            by (cases "y ! j") simp_all
        qed simp
      qed
    qed }
  note inj_inv = this

  txt \<open>
    We now construct the possible inversions for \<^term>\<open>xs\<close> when the payer is
    \<^term>\<open>i\<close>.
\<close>

  define zs where "zs = map (\<lambda>p. if p \<in> {min i j<..max i j} then \<not> ys ! p else ys ! p) [0..<n]"
  hence [simp]: "length zs = n" by simp
  hence [simp]: "0 < length zs" using n_gt_3 by simp

  have "\<And>l. l < max i j \<Longrightarrow> Suc l mod n = Suc l"
    using \<open>i < n\<close> \<open>j < n\<close> by auto
  { fix l assume "l < n"
    hence "(((l < min i j \<or> l = min i j) \<or> (min i j < l \<and> l < max i j)) \<or> l = max i j) \<or> max i j < l" by auto
    hence "((i = l) = (zs ! l = zs ! (Suc l mod n))) = ((j = l) = (ys ! l = ys ! (Suc l mod n)))"
    apply - proof ((erule disjE)+)
      assume "l < min i j"
      hence "l \<noteq> i" and "l \<noteq> j" and "zs ! l = ys ! l" and
        "zs ! (Suc l mod n) = ys ! (Suc l mod n)" using \<open>i < n\<close> \<open>j < n\<close> unfolding zs_def by auto
      thus ?thesis by simp
    next
      assume "l = min i j"
      show ?thesis
      proof (cases rule: linorder_cases)
        assume "i < j"
        hence "l = i" and "Suc l < n" and "i \<noteq> j" and "Suc l \<le> max i j" using \<open>l = min i j\<close> using \<open>j < n\<close> by auto
        hence "zs ! l = ys ! l" and "zs ! (Suc l mod n) = (\<not> ys ! (Suc l mod n))"
          using \<open>l = min i j\<close>[symmetric] by (simp_all add: zs_def)
        thus ?thesis using \<open>l = i\<close> \<open>i \<noteq> j\<close> by simp
      next
        assume "j < i"
        hence "l = j" and "Suc l < n" and "i \<noteq> j" and "Suc l \<le> max i j" using \<open>l = min i j\<close> using \<open>i < n\<close> by auto
        hence "zs ! l = ys ! l" and "zs ! (Suc l mod n) = (\<not> ys ! (Suc l mod n))"
          using \<open>l = min i j\<close>[symmetric] by (simp_all add: zs_def)
        thus ?thesis using \<open>l = j\<close> \<open>i \<noteq> j\<close> by simp
      next
        assume "i = j"
        hence "i = j" and "max i j = l" and "min i j = l" and "zs = ys"
          using \<open>l = min i j\<close> by (simp_all add: zs_def \<open>length ys = n\<close>[symmetric] map_nth)
        thus ?thesis by simp
      qed
    next
      assume "min i j < l \<and> l < max i j"
      hence "i \<noteq> l" and "j \<noteq> l" and "zs ! l = (\<not> ys ! l)"
        "zs ! (Suc l mod n) = (\<not> ys ! (Suc l mod n))"
        using \<open>i < n\<close> \<open>j < n\<close> by (auto simp: zs_def)
      thus ?thesis by simp
    next
      assume "l = max i j"
      show ?thesis
      proof (cases rule: linorder_cases)
        assume "i < j"
        hence "l = j" and "i \<noteq> j" using \<open>l = max i j\<close> using \<open>j < n\<close> by auto
        have "zs ! (Suc l mod n) = ys ! (Suc l mod n)"
          using \<open>j < n\<close> \<open>i < j\<close> \<open>l = j\<close> by (cases "Suc l = n") (auto simp add: zs_def)
        moreover have "zs ! l = (\<not> ys ! l)"
          using \<open>j < n\<close> \<open>i < j\<close> by (auto simp add: \<open>l = j\<close> zs_def)
        ultimately show ?thesis using \<open>l = j\<close> \<open>i \<noteq> j\<close> by simp
      next
        assume "j < i"
        hence "l = i" and "i \<noteq> j" using \<open>l = max i j\<close> by auto
        have "zs ! (Suc l mod n) = ys ! (Suc l mod n)"
          using \<open>i < n\<close> \<open>j < i\<close> \<open>l = i\<close> by (cases "Suc l = n") (auto simp add: zs_def)
        moreover have "zs ! l = (\<not> ys ! l)"
          using \<open>i < n\<close> \<open>j < i\<close> by (auto simp add: \<open>l = i\<close> zs_def)
        ultimately show ?thesis using \<open>l = i\<close> \<open>i \<noteq> j\<close> by auto
      next
        assume "i = j"
        hence "i = j" and "max i j = l" and "min i j = l" and "zs = ys"
          using \<open>l = max i j\<close> by (simp_all add: zs_def \<open>length ys = n\<close>[symmetric] map_nth)
        thus ?thesis by simp
      qed
    next
      assume "max i j < l"
      hence "j \<noteq> l" and "i \<noteq> l" by simp_all
      have "zs ! (Suc l mod n) = ys ! (Suc l mod n)"
        using \<open>l < n\<close> \<open>max i j < l\<close> by (cases "Suc l = n") (auto simp add: zs_def)
      moreover have "zs ! l = ys ! l"
        using \<open>l < n\<close> \<open>max i j < l\<close> by (auto simp add: zs_def)
      ultimately show ?thesis using \<open>j \<noteq> l\<close> \<open>i \<noteq> l\<close> by auto
    qed }
  hence zs: "inversion (Some i, zs) = xs"
    by (simp add: xs_inv[symmetric] inversion_def coin_def payer_def)
  moreover
  from zs have Not_zs: "inversion (Some i, (map Not zs)) = xs"
    by (simp add: xs_inv[symmetric] inversion_def coin_def payer_def)
  ultimately
  have "{dc \<in> dc_crypto. payer dc = Some i \<and> inversion dc = xs} =
    {(Some i, zs), (Some i, map Not zs)}"
    using \<open>i < n\<close> [[ hypsubst_thin = true ]]
  proof (safe, simp_all add:dc_crypto payer_def)
    fix b assume [simp]: "length b = n"
      and *: "inversion (Some i, b) = xs" and "b \<noteq> zs"
    show "b = map Not zs"
    proof (cases "b ! 0 = zs ! 0")
      case True
      hence zs: "zs \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs} \<and> xs = inversion (Some i, zs)"
        using zs by simp
      have b: "b \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs} \<and> xs = inversion (Some i, b)"
        using * by simp
      hence "b \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs}" ..
      with *[symmetric] have "xs \<in> (\<lambda>x. inversion (Some i, x)) ` {ys. ys ! 0 = b ! 0 \<and> length ys = length xs}"
         by (rule image_eqI)
      from this[unfolded image_ex1_eq[OF inj_inv]] b zs
      have "b = zs" by (rule Ex1_eq)
      thus ?thesis using \<open>b \<noteq> zs\<close> by simp
    next
      case False
      hence zs: "map Not zs \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs} \<and> xs = inversion (Some i, map Not zs)"
        using Not_zs by (simp add: nth_map[OF \<open>0 < length zs\<close>])
      have b: "b \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs} \<and> xs = inversion (Some i, b)"
        using * by simp
      hence "b \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs}" ..
      with *[symmetric] have "xs \<in> (\<lambda>x. inversion (Some i, x)) ` {ys. ys ! 0 = b ! 0 \<and> length ys = length xs}"
         by (rule image_eqI)
      from this[unfolded image_ex1_eq[OF inj_inv]] b zs
      show "b = map Not zs" by (rule Ex1_eq)
    qed
  qed
  moreover
  have "zs \<noteq> map Not zs"
    using \<open>0 < length zs\<close> by (cases zs) simp_all
  ultimately show ?thesis by simp
qed

lemma finite_dc_crypto: "finite dc_crypto"
  using finite_lists_length_eq[where A="UNIV :: bool set"]
  unfolding dc_crypto by simp

lemma card_inversion:
  assumes "xs \<in> inversion ` dc_crypto"
  shows "card {dc \<in> dc_crypto. inversion dc = xs} = 2 * n"
proof -
  let ?set = "\<lambda>i. {dc \<in> dc_crypto. payer dc = Some i \<and> inversion dc = xs}"
  let ?sets = "{?set i | i. i < n}"

  have [simp]: "length xs = n" using assms
    by (auto simp: dc_crypto inversion_def [abs_def])

  have "{dc \<in> dc_crypto. inversion dc = xs} = (\<Union>i < n. ?set i)"
    unfolding dc_crypto payer_def by auto
  also have "\<dots> = (\<Union>?sets)" by auto
  finally have eq_Union: "{dc \<in> dc_crypto. inversion dc = xs} = (\<Union>?sets)" by simp

  have card_double: "2 * card ?sets = card (\<Union>?sets)"
  proof (rule card_partition)
    show "finite ?sets" by simp
    { fix i assume "i < n"
      have "?set i \<subseteq> dc_crypto" by auto
      have "finite (?set i)" using finite_dc_crypto by auto }
    thus "finite (\<Union>?sets)" by auto

  next
    fix c assume "c \<in> ?sets"
    thus "card c = 2" using card_payer_and_inversion[OF assms] by auto

  next
    fix x y assume "x \<in> ?sets" and "y \<in> ?sets" "x \<noteq> y"
    then obtain i j where xy: "x = ?set i" "y = ?set j" by auto
    hence "i \<noteq> j" using \<open>x \<noteq> y\<close> by auto
    thus "x \<inter> y = {}" using xy by auto
  qed

  have sets: "?sets = ?set ` {..< n}"
    unfolding image_def by auto
  { fix i j :: nat assume asm: "i \<noteq> j" "i < n" "j < n"
    { assume iasm: "?set i = {}"
      have "card (?set i) = 2"
        using card_payer_and_inversion[OF assms \<open>i < n\<close>] by auto
      hence "False"
        using iasm by auto }
    then obtain c where ci: "c \<in> ?set i" by blast
    hence cj: "c \<notin> ?set j" using asm by auto
    { assume "?set i = ?set j"
      hence "False" using ci cj by auto }
    hence "?set i \<noteq> ?set j" by auto }
  hence "inj_on ?set {..< n}" unfolding inj_on_def by auto
  from card_image[OF this]
  have "card (?set ` {..< n}) = n" by auto
  hence "card ?sets = n" using sets by auto
  thus ?thesis using eq_Union card_double by auto
qed

lemma card_dc_crypto:
  "card dc_crypto = n * 2^n"
  unfolding dc_crypto
  using card_lists_length_eq[of "UNIV :: bool set"]
  by (simp add: card_cartesian_product card_image)

lemma card_image_inversion:
  "card (inversion ` dc_crypto) = 2^(n - 1)"
proof -
  let ?P = "{inversion -` {x} \<inter> dc_crypto |x. x \<in> inversion ` dc_crypto}"
  have "\<Union>?P = dc_crypto" by auto

  { fix a b assume *: "(a, b) \<in> dc_crypto"
    have inv_SOME: "inversion (SOME x. inversion x = inversion (a, b) \<and> x \<in> dc_crypto) = inversion (a, b)"
      apply (rule someI2)
      by (auto simp: *) }
  note inv_SOME = this

  { fix a b assume *: "(a, b) \<in> dc_crypto"
    have "(SOME x. inversion x = inversion (a, b) \<and> x \<in> dc_crypto) \<in> dc_crypto"
      by (rule someI2) (auto simp: *) }
  note SOME_inv_dc = this

  have "bij_betw (\<lambda>s. inversion (SOME x. x \<in> s \<and> x \<in> dc_crypto))
    {inversion -` {x} \<inter> dc_crypto |x. x \<in> inversion ` dc_crypto}
    (inversion ` dc_crypto)"
    unfolding bij_betw_def
    by (auto intro!: inj_onI image_eqI simp: inv_SOME SOME_inv_dc)
  hence card_eq: "card {inversion -` {x} \<inter> dc_crypto |x. x \<in> inversion ` dc_crypto} = card (inversion ` dc_crypto)"
    by (rule bij_betw_same_card)

  have "(2*n) * card (inversion ` dc_crypto) = card (\<Union>?P)"
    unfolding card_eq[symmetric]
  proof (rule card_partition)
    have "\<Union>?P \<subseteq> dc_crypto" by auto
    thus "finite (\<Union>?P)" using finite_dc_crypto by (auto intro: finite_subset)

    have "?P = (\<lambda>x. inversion -` {x} \<inter> dc_crypto) ` (inversion ` dc_crypto)"
      by auto
    thus "finite ?P" using finite_dc_crypto by auto

  next
    fix c assume "c \<in> {inversion -` {x} \<inter> dc_crypto |x. x \<in> inversion ` dc_crypto}"
    then obtain x where "c = inversion -` {x} \<inter> dc_crypto" and x: "x \<in> inversion ` dc_crypto" by auto
    hence "c = {dc \<in> dc_crypto. inversion dc = x}" by auto
    thus "card c = 2 * n" using card_inversion[OF x] by simp

  next
    fix x y assume "x \<in> ?P" "y \<in> ?P" and "x \<noteq> y"
    then obtain i j where
      x: "x = inversion -` {i} \<inter> dc_crypto" and i: "i \<in> inversion ` dc_crypto" and
      y: "y = inversion -` {j} \<inter> dc_crypto" and j: "j \<in> inversion ` dc_crypto" by auto
    show "x \<inter> y = {}" using x y \<open>x \<noteq> y\<close> by auto
  qed
  hence "2 * card (inversion ` dc_crypto) = 2 ^ n" unfolding \<open>\<Union>?P = dc_crypto\<close> card_dc_crypto
    using n_gt_3 by auto
  thus ?thesis by (cases n) auto
qed

end

sublocale dining_cryptographers_space \<subseteq> prob_space "uniform_count_measure dc_crypto"
  by (rule prob_space_uniform_count_measure[OF finite_dc_crypto])
     (insert n_gt_3, auto simp: dc_crypto intro: exI[of _ "replicate n True"])

sublocale dining_cryptographers_space \<subseteq> information_space "uniform_count_measure dc_crypto" 2
  by standard auto

notation (in dining_cryptographers_space)
  mutual_information_Pow (\<open>\<I>'( _ ; _ ')\<close>)

notation (in dining_cryptographers_space)
  entropy_Pow (\<open>\<H>'( _ ')\<close>)

notation (in dining_cryptographers_space)
  conditional_entropy_Pow (\<open>\<H>'( _ | _ ')\<close>)

theorem (in dining_cryptographers_space)
  "\<I>( inversion ; payer ) = 0"
proof (rule mutual_information_eq_0_simple)
  have n: "0 < n" using n_gt_3 by auto
  have card_image_inversion:
    "real (card (inversion ` dc_crypto)) = 2^n / 2"
    unfolding card_image_inversion using \<open>0 < n\<close> by (cases n) auto

  show inversion: "simple_distributed (uniform_count_measure dc_crypto) inversion (\<lambda>x. 2 / 2^n)"
  proof (rule simple_distributedI)
    show "simple_function (uniform_count_measure dc_crypto) inversion"
      using finite_dc_crypto
      by (auto simp: simple_function_def space_uniform_count_measure sets_uniform_count_measure)
    fix x assume "x \<in> inversion ` space (uniform_count_measure dc_crypto)"
    moreover have "inversion -` {x} \<inter> dc_crypto = {dc \<in> dc_crypto. inversion dc = x}" by auto
    ultimately show "2 / 2^n = prob (inversion -` {x} \<inter> space (uniform_count_measure dc_crypto))"
      using \<open>0 < n\<close>
      by (simp add: card_inversion card_dc_crypto finite_dc_crypto
                    subset_eq space_uniform_count_measure measure_uniform_count_measure)
  qed simp

  show "simple_distributed (uniform_count_measure dc_crypto) payer (\<lambda>x. 1 / real n)"
  proof (rule simple_distributedI)
    show "simple_function (uniform_count_measure dc_crypto) payer"
      using finite_dc_crypto
      by (auto simp: simple_function_def space_uniform_count_measure sets_uniform_count_measure)
    fix z assume "z \<in> payer ` space (uniform_count_measure dc_crypto)"
    then have "payer -` {z} \<inter> dc_crypto = {z} \<times> {xs. length xs = n}"
      by (auto simp: dc_crypto payer_def space_uniform_count_measure cong del: image_cong_simp)
    hence "card (payer -` {z} \<inter> dc_crypto) = 2^n"
      using card_lists_length_eq[where A="UNIV::bool set"]
      by (simp add: card_cartesian_product_singleton)
    then show "1 / real n = prob (payer -` {z} \<inter> space (uniform_count_measure dc_crypto))"
      using finite_dc_crypto
      by (subst measure_uniform_count_measure) (auto simp add: card_dc_crypto space_uniform_count_measure)
  qed simp

  show "simple_distributed (uniform_count_measure dc_crypto) (\<lambda>x. (inversion x, payer x)) (\<lambda>x. 2 / (real n *2^n))"
  proof (rule simple_distributedI)
    show "simple_function (uniform_count_measure dc_crypto) (\<lambda>x. (inversion x, payer x))"
      using finite_dc_crypto
      by (auto simp: simple_function_def space_uniform_count_measure sets_uniform_count_measure)
    fix x assume "x \<in> (\<lambda>x. (inversion x, payer x)) ` space (uniform_count_measure dc_crypto)"
    then obtain i xs where x: "x = (inversion (Some i, xs), payer (Some i, xs))"
      and "i < n" "length xs = n"
      by (simp add: image_iff space_uniform_count_measure dc_crypto Bex_def) blast
    then have xs: "inversion (Some i, xs) \<in> inversion`dc_crypto" and i: "Some i \<in> Some ` {0..<n}"
      and x: "x = (inversion (Some i, xs), Some i)" by (simp_all add: payer_def dc_crypto)
    moreover define ys where "ys = inversion (Some i, xs)"
    ultimately have ys: "ys \<in> inversion`dc_crypto"
      and "Some i \<in> Some ` {0..<n}" "x = (ys, Some i)" by simp_all
    then have "(\<lambda>x. (inversion x, payer x)) -` {x} \<inter> space (uniform_count_measure dc_crypto) =
      {dc \<in> dc_crypto. payer dc = Some (the (Some i)) \<and> inversion dc = ys}"
      by (auto simp add: payer_def space_uniform_count_measure)
    then show "2 / (real n * 2 ^ n) = prob ((\<lambda>x. (inversion x, payer x)) -` {x} \<inter> space (uniform_count_measure dc_crypto))"
      using \<open>i < n\<close> ys
      by (simp add: measure_uniform_count_measure card_payer_and_inversion finite_dc_crypto subset_eq card_dc_crypto)
  qed simp

  show "\<forall>x\<in>space (uniform_count_measure dc_crypto). 2 / (real n * 2 ^ n) = 2 / 2 ^ n * (1 / real n) "
    by simp
qed

end
