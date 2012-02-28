theory Dining_Cryptographers
imports "~~/src/HOL/Probability/Information"
begin

lemma image_ex1_eq: "inj_on f A \<Longrightarrow> (b \<in> f ` A) \<longleftrightarrow> (\<exists>!x \<in> A. b = f x)"
  by (unfold inj_on_def) blast

lemma Ex1_eq: "\<exists>! x. P x \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> x = y"
  by auto

locale finite_space =
  fixes S :: "'a set"
  assumes finite[simp]: "finite S"
  and not_empty[simp]: "S \<noteq> {}"

definition (in finite_space) "M = \<lparr> space = S, sets = Pow S,
  measure = \<lambda>A. ereal (card A / card S) \<rparr>"

lemma (in finite_space)
  shows space_M[simp]: "space M = S"
  and sets_M[simp]: "sets M = Pow S"
  by (simp_all add: M_def)

sublocale finite_space \<subseteq> finite_measure_space M
  by (rule finite_measure_spaceI)
     (simp_all add: M_def real_of_nat_def)

sublocale finite_space \<subseteq> information_space M 2
  by default (simp_all add: M_def one_ereal_def)

lemma (in finite_space) \<mu>'_eq[simp]: "\<mu>' A = (if A \<subseteq> S then card A / card S else 0)"
  unfolding \<mu>'_def by (auto simp: M_def)

section "Define the state space"

text {*

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

*}

locale dining_cryptographers_space =
  fixes n :: nat
  assumes n_gt_3: "n \<ge> 3"
begin

definition "dining_cryptographers =
  ({None} \<union> Some ` {0..<n}) \<times> {xs :: bool list. length xs = n}"
definition "payer dc = fst dc"
definition coin :: "(nat option \<times> bool list) => nat \<Rightarrow> bool" where
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
  let ?XOR = "\<lambda>f l. foldl (op \<noteq>) False (map f [0..<l])"

  have foldl_coin:
    "\<not> ?XOR (\<lambda>c. coin dc c \<noteq> coin dc (c + 1)) n"
  proof -
    def n' \<equiv> n -- "Need to hide n, as it is hidden in coin"
    have "?XOR (\<lambda>c. coin dc c \<noteq> coin dc (c + 1)) n'
        = (coin dc 0 \<noteq> coin dc n')"
      by (induct n') auto
    thus ?thesis using `n' \<equiv> n` by simp
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
    def l \<equiv> n -- "Need to hide n, as it is hidden in coin, payer etc."
    have "?XOR (\<lambda>c. (payer dc = Some c) \<noteq> (coin dc c \<noteq> coin dc (c + 1))) l =
        ((k < l) \<noteq> ?XOR (\<lambda>c. (coin dc c \<noteq> coin dc (c + 1))) l)"
      using `payer dc = Some k` by (induct l) auto
    thus ?thesis
      unfolding result_def inversion_def l_def
      using `payer dc = Some k` foldl_coin `k < n` by simp
  qed
qed

text {*

We now restrict the state space for the dining cryptographers to the cases when
one of the cryptographer pays.

*}

definition
  "dc_crypto = dining_cryptographers - {None}\<times>UNIV"

lemma dc_crypto: "dc_crypto = Some ` {0..<n} \<times> {xs :: bool list. length xs = n}"
  unfolding dc_crypto_def dining_cryptographers_def by auto

lemma image_payer_dc_crypto: "payer ` dc_crypto = Some ` {0..<n}"
proof -
  have *: "{xs. length xs = n} \<noteq> {}"
    by (auto intro!: exI[of _ "replicate n undefined"])
  show ?thesis
    unfolding payer_def_raw dc_crypto fst_image_times if_not_P[OF *] ..
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
        using `length xs = n` by simp_all
      have *: "\<And>j. j < n \<Longrightarrow>
        (x ! j = x ! (Suc j mod n)) = (y ! j = y ! (Suc j mod n))"
        using inv unfolding inversion_def map_eq_conv payer_def coin_def
        by fastforce
      show "x = y"
      proof (rule nth_equalityI, simp, rule allI, rule impI)
        fix j assume "j < length x" hence "j < n" using `length xs = n` by simp
        thus "x ! j = y ! j"
        proof (induct j)
          case (Suc j)
          moreover hence "j < n" by simp
          ultimately show ?case using *[OF `j < n`]
            by (cases "y ! j") simp_all
        qed simp
      qed
    qed }
  note inj_inv = this

  txt {*
    We now construct the possible inversions for @{term xs} when the payer is
    @{term i}.
  *}

  def zs \<equiv> "map (\<lambda>p. if p \<in> {min i j<..max i j} then \<not> ys ! p else ys ! p) [0..<n]"
  hence [simp]: "length zs = n" by simp
  hence [simp]: "0 < length zs" using n_gt_3 by simp

  have "\<And>l. l < max i j \<Longrightarrow> Suc l mod n = Suc l"
    using `i < n` `j < n` by auto
  { fix l assume "l < n"
    hence "(((l < min i j \<or> l = min i j) \<or> (min i j < l \<and> l < max i j)) \<or> l = max i j) \<or> max i j < l" by auto
    hence "((i = l) = (zs ! l = zs ! (Suc l mod n))) = ((j = l) = (ys ! l = ys ! (Suc l mod n)))"
    apply - proof ((erule disjE)+)
      assume "l < min i j"
      hence "l \<noteq> i" and "l \<noteq> j" and "zs ! l = ys ! l" and
        "zs ! (Suc l mod n) = ys ! (Suc l mod n)" using `i < n` `j < n` unfolding zs_def by auto
      thus ?thesis by simp
    next
      assume "l = min i j"
      show ?thesis
      proof (cases rule: linorder_cases)
        assume "i < j"
        hence "l = i" and "Suc l < n" and "i \<noteq> j" and "Suc l \<le> max i j" using `l = min i j` using `j < n` by auto
        hence "zs ! l = ys ! l" and "zs ! (Suc l mod n) = (\<not> ys ! (Suc l mod n))"
          using `l = min i j`[symmetric] by (simp_all add: zs_def)
        thus ?thesis using `l = i` `i \<noteq> j` by simp
      next
        assume "j < i"
        hence "l = j" and "Suc l < n" and "i \<noteq> j" and "Suc l \<le> max i j" using `l = min i j` using `i < n` by auto
        hence "zs ! l = ys ! l" and "zs ! (Suc l mod n) = (\<not> ys ! (Suc l mod n))"
          using `l = min i j`[symmetric] by (simp_all add: zs_def)
        thus ?thesis using `l = j` `i \<noteq> j` by simp
      next
        assume "i = j"
        hence "i = j" and "max i j = l" and "min i j = l" and "zs = ys"
          using `l = min i j` by (simp_all add: zs_def `length ys = n`[symmetric] map_nth)
        thus ?thesis by simp
      qed
    next
      assume "min i j < l \<and> l < max i j"
      hence "i \<noteq> l" and "j \<noteq> l" and "zs ! l = (\<not> ys ! l)"
        "zs ! (Suc l mod n) = (\<not> ys ! (Suc l mod n))"
        using `i < n` `j < n` by (auto simp: zs_def)
      thus ?thesis by simp
    next
      assume "l = max i j"
      show ?thesis
      proof (cases rule: linorder_cases)
        assume "i < j"
        hence "l = j" and "i \<noteq> j" using `l = max i j` using `j < n` by auto
        have "zs ! (Suc l mod n) = ys ! (Suc l mod n)"
          using `j < n` `i < j` `l = j` by (cases "Suc l = n") (auto simp add: zs_def)
        moreover have "zs ! l = (\<not> ys ! l)"
          using `j < n` `i < j` by (auto simp add: `l = j` zs_def)
        ultimately show ?thesis using `l = j` `i \<noteq> j` by simp
      next
        assume "j < i"
        hence "l = i" and "i \<noteq> j" using `l = max i j` by auto
        have "zs ! (Suc l mod n) = ys ! (Suc l mod n)"
          using `i < n` `j < i` `l = i` by (cases "Suc l = n") (auto simp add: zs_def)
        moreover have "zs ! l = (\<not> ys ! l)"
          using `i < n` `j < i` by (auto simp add: `l = i` zs_def)
        ultimately show ?thesis using `l = i` `i \<noteq> j` by auto
      next
        assume "i = j"
        hence "i = j" and "max i j = l" and "min i j = l" and "zs = ys"
          using `l = max i j` by (simp_all add: zs_def `length ys = n`[symmetric] map_nth)
        thus ?thesis by simp
      qed
    next
      assume "max i j < l"
      hence "j \<noteq> l" and "i \<noteq> l" by simp_all
      have "zs ! (Suc l mod n) = ys ! (Suc l mod n)"
        using `l < n` `max i j < l` by (cases "Suc l = n") (auto simp add: zs_def)
      moreover have "zs ! l = ys ! l"
        using `l < n` `max i j < l` by (auto simp add: zs_def)
      ultimately show ?thesis using `j \<noteq> l` `i \<noteq> l` by auto
    qed }
  hence zs: "inversion (Some i, zs) = xs"
    by (simp add: xs_inv[symmetric] inversion_def coin_def payer_def)
  moreover
  hence Not_zs: "inversion (Some i, (map Not zs)) = xs"
    by (simp add: xs_inv[symmetric] inversion_def coin_def payer_def)
  ultimately
  have "{dc \<in> dc_crypto. payer dc = Some i \<and> inversion dc = xs} =
    {(Some i, zs), (Some i, map Not zs)}"
    using `i < n`
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
      thus ?thesis using `b \<noteq> zs` by simp
    next
      case False
      hence zs: "map Not zs \<in> {ys. ys ! 0 = b ! 0 \<and> length ys = length xs} \<and> xs = inversion (Some i, map Not zs)"
        using Not_zs by (simp add: nth_map[OF `0 < length zs`])
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
    using `0 < length zs` by (cases zs) simp_all
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
    by (auto simp: dc_crypto inversion_def_raw)

  have "{dc \<in> dc_crypto. inversion dc = xs} = (\<Union> i < n. ?set i)"
    unfolding dc_crypto payer_def by auto
  also have "\<dots> = (\<Union> ?sets)" by auto
  finally have eq_Union: "{dc \<in> dc_crypto. inversion dc = xs} = (\<Union> ?sets)" by simp

  have card_double: "2 * card ?sets = card (\<Union> ?sets)"
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
    hence "i \<noteq> j" using `x \<noteq> y` by auto
    thus "x \<inter> y = {}" using xy by auto
  qed

  have sets: "?sets = ?set ` {..< n}"
    unfolding image_def by auto
  { fix i j :: nat assume asm: "i \<noteq> j" "i < n" "j < n"
    { assume iasm: "?set i = {}"
      have "card (?set i) = 2"
        using card_payer_and_inversion[OF assms `i < n`] by auto
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
    show "x \<inter> y = {}" using x y `x \<noteq> y` by auto
  qed
  hence "2 * card (inversion ` dc_crypto) = 2 ^ n" unfolding `\<Union>?P = dc_crypto` card_dc_crypto
    using n_gt_3 by auto
  thus ?thesis by (cases n) auto
qed

end


sublocale
  dining_cryptographers_space \<subseteq> finite_space "dc_crypto"
proof
  show "finite dc_crypto" using finite_dc_crypto .
  show "dc_crypto \<noteq> {}"
    unfolding dc_crypto
    using n_gt_3 by (auto intro: exI[of _ "replicate n True"])
qed

notation (in dining_cryptographers_space)
  mutual_information_Pow ("\<I>'( _ ; _ ')")

notation (in dining_cryptographers_space)
  entropy_Pow ("\<H>'( _ ')")

notation (in dining_cryptographers_space)
  conditional_entropy_Pow ("\<H>'( _ | _ ')")

theorem (in dining_cryptographers_space)
  "\<I>( inversion ; payer ) = 0"
proof -
  have n: "0 < n" using n_gt_3 by auto
  have lists: "{xs. length xs = n} \<noteq> {}" using Ex_list_of_length by auto
  have card_image_inversion:
    "real (card (inversion ` dc_crypto)) = 2^n / 2"
    unfolding card_image_inversion using `0 < n` by (cases n) auto

  let ?dIP = "distribution (\<lambda>x. (inversion x, payer x))"
  let ?dP = "distribution payer"
  let ?dI = "distribution inversion"

  { have "\<H>(inversion|payer) =
        - (\<Sum>x\<in>inversion`dc_crypto. (\<Sum>z\<in>Some ` {0..<n}. ?dIP {(x, z)} * log 2 (?dIP {(x, z)} / ?dP {z})))"
      unfolding conditional_entropy_eq[OF simple_function_finite simple_function_finite]
      by (simp add: image_payer_dc_crypto setsum_Sigma)
    also have "... =
        - (\<Sum>x\<in>inversion`dc_crypto. (\<Sum>z\<in>Some ` {0..<n}. 2 / (real n * 2^n) * (1 - real n)))"
      unfolding neg_equal_iff_equal
    proof (rule setsum_cong[OF refl], rule setsum_cong[OF refl])
      fix x z assume x: "x \<in> inversion`dc_crypto" and z: "z \<in> Some ` {0..<n}"
      hence "(\<lambda>x. (inversion x, payer x)) -` {(x, z)} \<inter> dc_crypto =
          {dc \<in> dc_crypto. payer dc = Some (the z) \<and> inversion dc = x}"
        by (auto simp add: payer_def)
      moreover from x z obtain i where "z = Some i" and "i < n" by auto
      moreover from x have "length x = n" by (auto simp: inversion_def_raw dc_crypto)
      ultimately
      have "?dIP {(x, z)} = 2 / (real n * 2^n)" using x
        by (auto simp add: card_dc_crypto card_payer_and_inversion distribution_def)
      moreover
      from z have "payer -` {z} \<inter> dc_crypto = {z} \<times> {xs. length xs = n}"
        by (auto simp: dc_crypto payer_def)
      hence "card (payer -` {z} \<inter> dc_crypto) = 2^n"
        using card_lists_length_eq[where A="UNIV::bool set"]
        by (simp add: card_cartesian_product_singleton)
      hence "?dP {z} = 1 / real n"
        by (simp add: distribution_def card_dc_crypto)
      ultimately
      show "?dIP {(x,z)} * log 2 (?dIP {(x,z)} / ?dP {z}) =
       2 / (real n * 2^n) * (1 - real n)"
        by (simp add: log_divide log_nat_power[of 2])
    qed
    also have "... = real n - 1"
      using n finite_space
      by (simp add: card_image_inversion card_image[OF inj_Some] field_simps real_eq_of_nat[symmetric])
    finally have "\<H>(inversion|payer) = real n - 1" . }
  moreover
  { have "\<H>(inversion) = - (\<Sum>x \<in> inversion`dc_crypto. ?dI {x} * log 2 (?dI {x}))"
      unfolding entropy_eq[OF simple_function_finite] by simp
    also have "... = - (\<Sum>x \<in> inversion`dc_crypto. 2 * (1 - real n) / 2^n)"
      unfolding neg_equal_iff_equal
    proof (rule setsum_cong[OF refl])
      fix x assume x_inv: "x \<in> inversion ` dc_crypto"
      hence "length x = n" by (auto simp: inversion_def_raw dc_crypto)
      moreover have "inversion -` {x} \<inter> dc_crypto = {dc \<in> dc_crypto. inversion dc = x}" by auto
      ultimately have "?dI {x} = 2 / 2^n" using `0 < n`
        by (auto simp: card_inversion[OF x_inv] card_dc_crypto distribution_def)
      thus "?dI {x} * log 2 (?dI {x}) = 2 * (1 - real n) / 2^n"
        by (simp add: log_divide log_nat_power power_le_zero_eq inverse_eq_divide)
    qed
    also have "... = real n - 1"
      by (simp add: card_image_inversion real_of_nat_def[symmetric] field_simps)
    finally have "\<H>(inversion) = real n - 1" .
  }
  ultimately show ?thesis
    unfolding mutual_information_eq_entropy_conditional_entropy[OF simple_function_finite simple_function_finite]
    by simp
qed

end
