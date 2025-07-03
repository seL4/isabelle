(*  Title:      HOL/Library/Ramsey.thy
    Author:     Tom Ridge. Full finite version by L C Paulson.
*)

section \<open>Ramsey's Theorem\<close>

theory Ramsey
  imports Infinite_Set Equipollence FuncSet
begin

subsection \<open>Preliminary definitions\<close>

abbreviation strict_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "strict_sorted \<equiv> sorted_wrt (<)"

subsubsection \<open>The $n$-element subsets of a set $A$\<close>

definition nsets :: "['a set, nat] \<Rightarrow> 'a set set" (\<open>(\<open>notation=\<open>mixfix nsets\<close>\<close>[_]\<^bsup>_\<^esup>)\<close> [0,999] 999)
  where "nsets A n \<equiv> {N. N \<subseteq> A \<and> finite N \<and> card N = n}"

lemma finite_imp_finite_nsets: "finite A \<Longrightarrow> finite ([A]\<^bsup>k\<^esup>)"
  by (simp add: nsets_def)

lemma nsets_mono: "A \<subseteq> B \<Longrightarrow> nsets A n \<subseteq> nsets B n"
  by (auto simp: nsets_def)

lemma nsets_Pi_contra: "A' \<subseteq> A \<Longrightarrow> Pi ([A]\<^bsup>n\<^esup>) B \<subseteq> Pi ([A']\<^bsup>n\<^esup>) B"
  by (auto simp: nsets_def)

lemma nsets_2_eq: "[A]\<^bsup>2\<^esup> = (\<Union>x\<in>A. \<Union>y\<in>A - {x}. {{x, y}})"
  by (auto simp: nsets_def card_2_iff)

lemma nsets2_E:
  assumes "e \<in> [A]\<^bsup>2\<^esup>"
  obtains x y where "e = {x,y}" "x \<in> A" "y \<in> A" "x\<noteq>y"
  using assms by (auto simp: nsets_def card_2_iff)

lemma nsets_doubleton_2_eq [simp]: "[{x, y}]\<^bsup>2\<^esup> = (if x=y then {} else {{x, y}})"
  by (auto simp: nsets_2_eq)

lemma doubleton_in_nsets_2 [simp]: "{x,y} \<in> [A]\<^bsup>2\<^esup> \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> x \<noteq> y"
  by (auto simp: nsets_2_eq Set.doubleton_eq_iff)

lemma nsets_3_eq: "[A]\<^bsup>3\<^esup> = (\<Union>x\<in>A. \<Union>y\<in>A - {x}. \<Union>z\<in>A - {x,y}. {{x,y,z}})"
  by (simp add: eval_nat_numeral nsets_def card_Suc_eq) blast

lemma nsets_4_eq: "[A]\<^bsup>4\<^esup> = (\<Union>u\<in>A. \<Union>x\<in>A - {u}. \<Union>y\<in>A - {u,x}. \<Union>z\<in>A - {u,x,y}. {{u,x,y,z}})"
     (is "_ = ?rhs")
proof
  show "[A]\<^bsup>4\<^esup> \<subseteq> ?rhs"
    by (clarsimp simp add: nsets_def eval_nat_numeral card_Suc_eq) blast
  have "\<And>X. X \<in> ?rhs \<Longrightarrow> card X = 4"
    by (force simp: card_2_iff)
  then show "?rhs \<subseteq> [A]\<^bsup>4\<^esup>"
    by (auto simp: nsets_def)
qed

lemma nsets_disjoint_2:
  "X \<inter> Y = {} \<Longrightarrow> [X \<union> Y]\<^bsup>2\<^esup> = [X]\<^bsup>2\<^esup> \<union> [Y]\<^bsup>2\<^esup> \<union> (\<Union>x\<in>X. \<Union>y\<in>Y. {{x,y}})"
  by (fastforce simp: nsets_2_eq Set.doubleton_eq_iff)

lemma ordered_nsets_2_eq:
  fixes A :: "'a::linorder set"
  shows "[A]\<^bsup>2\<^esup> = {{x,y} | x y. x \<in> A \<and> y \<in> A \<and> x<y}"
     (is "_ = ?rhs")
proof
  show "[A]\<^bsup>2\<^esup> \<subseteq> ?rhs"
    by (auto simp: nsets_def card_2_iff doubleton_eq_iff neq_iff)
  show "?rhs \<subseteq> [A]\<^bsup>2\<^esup>"
    unfolding numeral_nat by (auto simp: nsets_def card_Suc_eq)
qed

lemma ordered_nsets_3_eq:
  fixes A :: "'a::linorder set"
  shows "[A]\<^bsup>3\<^esup> = {{x,y,z} | x y z. x \<in> A \<and> y \<in> A \<and> z \<in> A \<and> x<y \<and> y<z}"
     (is "_ = ?rhs")
proof
  show "[A]\<^bsup>3\<^esup> \<subseteq> ?rhs"
    unfolding nsets_def card_3_iff
    by (smt (verit, del_insts) Collect_mono_iff insert_commute insert_subset
        linorder_less_linear)
  have "\<And>X. X \<in> ?rhs \<Longrightarrow> card X = 3"
    by (force simp: card_3_iff)
  then show "?rhs \<subseteq> [A]\<^bsup>3\<^esup>"
    by (auto simp: nsets_def)
qed

lemma ordered_nsets_4_eq:
  fixes A :: "'a::linorder set"
  defines "rhs \<equiv> \<lambda>U. \<exists>u x y z. U = {u,x,y,z} \<and> u \<in> A \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A \<and> u < x \<and> x < y \<and> y < z"
  shows "[A]\<^bsup>4\<^esup> = Collect rhs"
proof -
  have "rhs U" if "U \<in> [A]\<^bsup>4\<^esup>" for U
  proof -
    from that obtain l where "strict_sorted l" "List.set l = U" "length l = 4" "U \<subseteq> A"
      by (simp add: nsets_def) (metis finite_set_strict_sorted)
    then show ?thesis
      unfolding numeral_nat length_Suc_conv rhs_def by auto blast
  qed
  moreover
  have "\<And>X. X \<in> Collect rhs \<Longrightarrow> card X = 4 \<and> finite X \<and> X \<subseteq> A"
    by (auto simp: rhs_def card_insert_if)
  ultimately show ?thesis
    unfolding nsets_def by blast
qed

lemma ordered_nsets_5_eq:
  fixes A :: "'a::linorder set"
  defines "rhs \<equiv> \<lambda>U. \<exists>u v x y z. U = {u,v,x,y,z} \<and> u \<in> A \<and> v \<in> A \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A \<and> u < v \<and> v < x \<and> x < y \<and> y < z"
  shows "[A]\<^bsup>5\<^esup> = Collect rhs"
proof -
  have "rhs U" if "U \<in> [A]\<^bsup>5\<^esup>" for U
  proof -
    from that obtain l where "strict_sorted l" "List.set l = U" "length l = 5" "U \<subseteq> A"
      by (simp add: nsets_def) (metis finite_set_strict_sorted)
    then show ?thesis
      unfolding numeral_nat length_Suc_conv rhs_def by auto blast
  qed
  moreover
  have "\<And>X. X \<in> Collect rhs \<Longrightarrow> card X = 5 \<and> finite X \<and> X \<subseteq> A"
    by (auto simp: rhs_def card_insert_if)
  ultimately show ?thesis
    unfolding nsets_def by blast
qed

lemma binomial_eq_nsets: "n choose k = card (nsets {0..<n} k)"
proof -
  have "{K. K \<subseteq> {0..<n} \<and> card K = k} = {N. N \<subseteq> {0..<n} \<and> finite N \<and> card N = k}"
    using infinite_super by blast
  then show ?thesis
    by (simp add: binomial_def nsets_def)
qed

lemma nsets_eq_empty_iff: "nsets A r = {} \<longleftrightarrow> finite A \<and> card A < r"
  unfolding nsets_def
proof (intro iffI conjI)
  assume that: "{N. N \<subseteq> A \<and> finite N \<and> card N = r} = {}"
  show "finite A"
    using infinite_arbitrarily_large that by auto
  then have "\<not> r \<le> card A"
    using that by (simp add: set_eq_iff) (metis obtain_subset_with_card_n)
  then show "card A < r"
    using not_less by blast
next
  show "{N. N \<subseteq> A \<and> finite N \<and> card N = r} = {}"
    if "finite A \<and> card A < r"
    using that card_mono leD by auto
qed

lemma nsets_eq_empty: "\<lbrakk>finite A; card A < r\<rbrakk> \<Longrightarrow> nsets A r = {}"
  by (simp add: nsets_eq_empty_iff)

lemma nsets_empty_iff: "nsets {} r = (if r=0 then {{}} else {})"
  by (auto simp: nsets_def)

lemma nsets_singleton_iff: "nsets {a} r = (if r=0 then {{}} else if r=1 then {{a}} else {})"
  by (auto simp: nsets_def card_gt_0_iff subset_singleton_iff)

lemma nsets_self [simp]: "nsets {..<m} m = {{..<m}}"
proof
  show "[{..<m}]\<^bsup>m\<^esup> \<subseteq> {{..<m}}"
    by (force simp add: card_subset_eq nsets_def)
qed (simp add: nsets_def)

lemma nsets_zero [simp]: "nsets A 0 = {{}}"
  by (auto simp: nsets_def)

lemma nsets_one: "nsets A (Suc 0) = (\<lambda>x. {x}) ` A"
  using card_eq_SucD by (force simp: nsets_def)

lemma inj_on_nsets:
  assumes "inj_on f A"
  shows "inj_on (\<lambda>X. f ` X) ([A]\<^bsup>n\<^esup>)"
  using assms by (simp add: nsets_def inj_on_def inj_on_image_eq_iff)

lemma bij_betw_nsets:
  assumes "bij_betw f A B"
  shows "bij_betw (\<lambda>X. f ` X) ([A]\<^bsup>n\<^esup>) ([B]\<^bsup>n\<^esup>)"
proof -
  have "\<And>X. \<lbrakk>X \<subseteq> f ` A; finite X\<rbrakk> \<Longrightarrow> \<exists>Y\<subseteq>A. finite Y \<and> card Y = card X \<and> X = f ` Y"
    by (metis card_image inj_on_finite order_refl subset_image_inj)
  then have "(`) f ` [A]\<^bsup>n\<^esup> = [f ` A]\<^bsup>n\<^esup>"
    using assms by (auto simp: nsets_def bij_betw_def image_iff card_image inj_on_subset)
  with assms show ?thesis
    by (auto simp: bij_betw_def inj_on_nsets)
qed

lemma nset_image_obtains:
  assumes "X \<in> [f`A]\<^bsup>k\<^esup>" "inj_on f A"
  obtains Y where "Y \<in> [A]\<^bsup>k\<^esup>" "X = f ` Y"
proof
  show "X = f ` (A \<inter> f -` X)"
    using assms by (auto simp: nsets_def)
  then show "A Int (f -` X) \<in> [A]\<^bsup>k\<^esup>"
    using assms
    unfolding nsets_def mem_Collect_eq
    by (metis card_image finite_image_iff inf_le1 inj_on_subset)
qed

lemma nsets_image_funcset:
  assumes "g \<in> S \<rightarrow> T" and "inj_on g S"
  shows "(\<lambda>X. g ` X) \<in> [S]\<^bsup>k\<^esup> \<rightarrow> [T]\<^bsup>k\<^esup>"
    using assms
    by (fastforce simp: nsets_def card_image inj_on_subset subset_iff simp flip: image_subset_iff_funcset)

lemma nsets_compose_image_funcset:
  assumes f: "f \<in> [T]\<^bsup>k\<^esup> \<rightarrow> D" and "g \<in> S \<rightarrow> T" and "inj_on g S"
  shows "f \<circ> (\<lambda>X. g ` X) \<in> [S]\<^bsup>k\<^esup> \<rightarrow> D"
proof -
  have "(\<lambda>X. g ` X) \<in> [S]\<^bsup>k\<^esup> \<rightarrow> [T]\<^bsup>k\<^esup>"
    using assms by (simp add: nsets_image_funcset)
  then show ?thesis
    using f by fastforce
qed

subsubsection \<open>Further properties, involving equipollence\<close>

lemma nsets_lepoll_cong:
  assumes "A \<lesssim> B"
  shows "[A]\<^bsup>k\<^esup> \<lesssim> [B]\<^bsup>k\<^esup>"
proof -
  obtain f where f: "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  define F where "F \<equiv> \<lambda>N. f ` N"
  have "inj_on F ([A]\<^bsup>k\<^esup>)"
    using F_def f inj_on_nsets by blast
  moreover
  have "F ` ([A]\<^bsup>k\<^esup>) \<subseteq> [B]\<^bsup>k\<^esup>"
    by (metis F_def bij_betw_def bij_betw_nsets f nsets_mono)
  ultimately show ?thesis
    by (meson lepoll_def)
qed

lemma nsets_eqpoll_cong:
  assumes "A\<approx>B"
  shows "[A]\<^bsup>k\<^esup> \<approx> [B]\<^bsup>k\<^esup>"
  by (meson assms eqpoll_imp_lepoll eqpoll_sym lepoll_antisym nsets_lepoll_cong)

lemma infinite_imp_infinite_nsets:
  assumes inf: "infinite A" and "k>0"
  shows "infinite ([A]\<^bsup>k\<^esup>)"
proof -
  obtain B where "B \<subset> A" "A\<approx>B"
    by (meson inf infinite_iff_psubset)
  then obtain a where a: "a \<in> A" "a \<notin> B"
    by blast
  then obtain N where "N \<subseteq> B" "finite N" "card N = k-1" "a \<notin> N"
    by (metis \<open>A \<approx> B\<close> inf eqpoll_finite_iff infinite_arbitrarily_large subset_eq)
  with a \<open>k>0\<close> \<open>B \<subset> A\<close> have "insert a N \<in> [A]\<^bsup>k\<^esup>"
    by (simp add: nsets_def)
  with a have "nsets B k \<noteq> nsets A k"
    by (metis (no_types, lifting) in_mono insertI1 mem_Collect_eq nsets_def)
  moreover have "nsets B k \<subseteq> nsets A k"
    using \<open>B \<subset> A\<close> nsets_mono by auto
  ultimately show ?thesis
    unfolding infinite_iff_psubset_le
    by (meson \<open>A \<approx> B\<close> eqpoll_imp_lepoll nsets_eqpoll_cong psubsetI)
qed

lemma finite_nsets_iff:
  assumes "k>0"
  shows "finite ([A]\<^bsup>k\<^esup>) \<longleftrightarrow> finite A"
  using assms finite_imp_finite_nsets infinite_imp_infinite_nsets by blast

lemma card_nsets [simp]: "card (nsets A k) = card A choose k"
proof (cases "finite A")
  case True
  then show ?thesis
    by (metis bij_betw_nsets bij_betw_same_card binomial_eq_nsets ex_bij_betw_nat_finite)
next
  case False
  then show ?thesis
    by (cases "k=0"; simp add: finite_nsets_iff)
qed

subsubsection \<open>Partition predicates\<close>

definition "monochromatic \<equiv> \<lambda>\<beta> \<alpha> \<gamma> f i. \<exists>H \<in> nsets \<beta> \<alpha>. f ` (nsets H \<gamma>) \<subseteq> {i}"

text \<open>uniform partition sizes\<close>
definition partn :: "'a set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b set \<Rightarrow> bool"
  where "partn \<beta> \<alpha> \<gamma> \<delta> \<equiv> \<forall>f \<in> nsets \<beta> \<gamma>  \<rightarrow>  \<delta>. \<exists>\<xi>\<in>\<delta>. monochromatic \<beta> \<alpha> \<gamma> f \<xi>"

text \<open>partition sizes enumerated in a list\<close>
definition partn_lst :: "'a set \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "partn_lst \<beta> \<alpha> \<gamma> \<equiv> \<forall>f \<in> nsets \<beta> \<gamma>  \<rightarrow>  {..<length \<alpha>}. \<exists>i < length \<alpha>. monochromatic \<beta> (\<alpha>!i) \<gamma> f i"

text \<open>There's always a 0-clique\<close>
lemma partn_lst_0: "\<gamma> > 0 \<Longrightarrow> partn_lst \<beta> (0#\<alpha>) \<gamma>"
  by (force simp: partn_lst_def monochromatic_def nsets_empty_iff)

lemma partn_lst_0': "\<gamma> > 0 \<Longrightarrow> partn_lst \<beta> (a#0#\<alpha>) \<gamma>"
  by (force simp: partn_lst_def monochromatic_def nsets_empty_iff)

lemma partn_lst_greater_resource:
  fixes M::nat
  assumes M: "partn_lst {..<M} \<alpha> \<gamma>" and "M \<le> N"
  shows "partn_lst {..<N} \<alpha> \<gamma>"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> nsets {..<N} \<gamma> \<rightarrow> {..<length \<alpha>}"
  then have "f \<in> nsets {..<M} \<gamma> \<rightarrow> {..<length \<alpha>}"
    by (meson Pi_anti_mono \<open>M \<le> N\<close> lessThan_subset_iff nsets_mono subsetD)
  then obtain i H where i: "i < length \<alpha>" and H: "H \<in> nsets {..<M} (\<alpha> ! i)" and subi: "f ` nsets H \<gamma> \<subseteq> {i}"
    using M unfolding partn_lst_def monochromatic_def by blast
  have "H \<in> nsets {..<N} (\<alpha> ! i)"
    using \<open>M \<le> N\<close> H by (auto simp: nsets_def subset_iff)
  then show "\<exists>i<length \<alpha>. monochromatic {..<N} (\<alpha>!i) \<gamma> f i"
    using i subi unfolding monochromatic_def by blast
qed

lemma partn_lst_fewer_colours:
  assumes major: "partn_lst \<beta> (n#\<alpha>) \<gamma>" and "n \<ge> \<gamma>"
  shows "partn_lst \<beta> \<alpha> \<gamma>"
proof (clarsimp simp: partn_lst_def)
  fix f :: "'a set \<Rightarrow> nat"
  assume f: "f \<in> [\<beta>]\<^bsup>\<gamma>\<^esup> \<rightarrow> {..<length \<alpha>}"
  then obtain i H where i: "i < Suc (length \<alpha>)"
      and H: "H \<in> [\<beta>]\<^bsup>((n # \<alpha>) ! i)\<^esup>"
      and hom: "\<forall>x\<in>[H]\<^bsup>\<gamma>\<^esup>. Suc (f x) = i"
    using \<open>n \<ge> \<gamma>\<close> major [unfolded partn_lst_def, rule_format, of "Suc o f"]
    by (fastforce simp: image_subset_iff nsets_eq_empty_iff monochromatic_def)
  show "\<exists>i<length \<alpha>. monochromatic \<beta> (\<alpha>!i) \<gamma> f i"
  proof (cases i)
    case 0
    then have "[H]\<^bsup>\<gamma>\<^esup> = {}"
      using hom by blast
    then show ?thesis
      using 0 H \<open>n \<ge> \<gamma>\<close>
      by (simp add: nsets_eq_empty_iff) (simp add: nsets_def)
  next
    case (Suc i')
    then show ?thesis
      unfolding monochromatic_def using i H hom by auto
  qed
qed

lemma partn_lst_eq_partn: "partn_lst {..<n} [m,m] 2 = partn {..<n} m 2 {..<2::nat}"
proof -
  have "\<And>i. i < 2 \<Longrightarrow> [m, m] ! i = m"
    using less_2_cases_iff by force
  then show ?thesis
    by (auto simp: partn_lst_def partn_def numeral_2_eq_2 cong: conj_cong)
qed

lemma partn_lstE:
  assumes "partn_lst \<beta> \<alpha> \<gamma>" "f \<in> nsets \<beta> \<gamma>  \<rightarrow>  {..<l}" "length \<alpha> = l"
  obtains i H where "i < length \<alpha>" "H \<in> nsets \<beta> (\<alpha>!i)" "f ` (nsets H \<gamma>) \<subseteq> {i}"
  using partn_lst_def monochromatic_def assms by metis

lemma partn_lst_less:
  assumes M: "partn_lst \<beta> \<alpha> n" and eq: "length \<alpha>' = length \<alpha>"
    and le: "\<And>i. i < length \<alpha> \<Longrightarrow> \<alpha>'!i \<le> \<alpha>!i "
  shows "partn_lst \<beta> \<alpha>' n"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> [\<beta>]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>'}"
  then obtain i H where i: "i < length \<alpha>"
                   and "H \<subseteq> \<beta>"  and H: "card H = (\<alpha>!i)" and "finite H"
                   and fi: "f ` nsets H n \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def monochromatic_def nsets_def)
  then obtain bij where bij: "bij_betw bij H {0..<\<alpha>!i}"
    by (metis ex_bij_betw_finite_nat)
  then have inj: "inj_on (inv_into H bij) {0..<\<alpha>' ! i}"
    by (metis bij_betw_def dual_order.refl i inj_on_inv_into ivl_subset le)
  define H' where "H' = inv_into H bij ` {0..<\<alpha>'!i}"
  show "\<exists>i<length \<alpha>'. monochromatic \<beta> (\<alpha>'!i) n f i"
    unfolding monochromatic_def
  proof (intro exI bexI conjI)
    show "i < length \<alpha>'"
      by (simp add: assms(2) i)
    have "H' \<subseteq> H"
      using bij \<open>i < length \<alpha>\<close> bij_betw_imp_surj_on le
      by (force simp: H'_def image_subset_iff intro: inv_into_into)
    then have "finite H'"
      by (simp add: \<open>finite H\<close> finite_subset)
    with \<open>H' \<subseteq> H\<close> have cardH': "card H' = (\<alpha>'!i)"
      unfolding H'_def by (simp add: inj card_image)
    show "f ` [H']\<^bsup>n\<^esup> \<subseteq> {i}"
      by (meson \<open>H' \<subseteq> H\<close> dual_order.trans fi image_mono nsets_mono)
    show "H' \<in> [\<beta>]\<^bsup>(\<alpha>'! i)\<^esup>"
      using \<open>H \<subseteq> \<beta>\<close> \<open>H' \<subseteq> H\<close> \<open>finite H'\<close> cardH' nsets_def by fastforce
  qed
qed


subsection \<open>Finite versions of Ramsey's theorem\<close>

text \<open>
  To distinguish the finite and infinite ones, lower and upper case
  names are used (ramsey vs Ramsey).
\<close>

subsubsection \<open>The Erdős--Szekeres theorem exhibits an upper bound for Ramsey numbers\<close>

text \<open>The Erdős--Szekeres bound, essentially extracted from the proof\<close>
fun ES :: "[nat,nat,nat] \<Rightarrow> nat"
  where "ES 0 k l = max k l"
  |     "ES (Suc r) k l =
            (if r=0 then k+l-1
             else if k=0 \<or> l=0 then 1 else Suc (ES r (ES (Suc r) (k-1) l) (ES (Suc r) k (l-1))))"

declare ES.simps [simp del]

lemma ES_0 [simp]: "ES 0 k l = max k l"
  using ES.simps(1) by blast

lemma ES_1 [simp]: "ES 1 k l = k+l-1"
  using ES.simps(2) [of 0 k l] by simp

lemma ES_2: "ES 2 k l = (if k=0 \<or> l=0 then 1 else ES 2 (k-1) l + ES 2 k (l-1))"
  unfolding numeral_2_eq_2
  by (smt (verit) ES.elims One_nat_def Suc_pred add_gr_0 neq0_conv nat.inject zero_less_Suc)

text \<open>The Erdős--Szekeres upper bound\<close>
lemma ES2_choose: "ES 2 k l = (k+l) choose k"
proof (induct n \<equiv> "k+l" arbitrary: k l)
  case 0
  then show ?case
    by (auto simp: ES_2)
next
  case (Suc n)
  then have "k>0 \<Longrightarrow> l>0 \<Longrightarrow> ES 2 (k - 1) l + ES 2 k (l - 1) = k + l choose k"
    using choose_reduce_nat by force
  then show ?case
    by (metis ES_2 Nat.add_0_right binomial_n_0 binomial_n_n gr0I)
qed

subsubsection \<open>Trivial cases\<close>

text \<open>Vacuous, since we are dealing with 0-sets!\<close>
lemma ramsey0: "\<exists>N::nat. partn_lst {..<N} [q1,q2] 0"
  by (force simp: partn_lst_def monochromatic_def ex_in_conv less_Suc_eq nsets_eq_empty_iff)

text \<open>Just the pigeon hole principle, since we are dealing with 1-sets\<close>
lemma ramsey1_explicit: "partn_lst {..<q0 + q1 - Suc 0} [q0,q1] 1"
proof -
  have "\<exists>i<Suc (Suc 0). \<exists>H\<in>nsets {..<q0 + q1 - 1} ([q0, q1] ! i). f ` nsets H 1 \<subseteq> {i}"
    if "f \<in> nsets {..<q0 + q1 - 1} (Suc 0) \<rightarrow> {..<Suc (Suc 0)}" for f
  proof -
    define A where "A \<equiv> \<lambda>i. {q. q < q0+q1-1 \<and> f {q} = i}"
    have "A 0 \<union> A 1 = {..<q0 + q1-1}"
      using that by (auto simp: A_def PiE_iff nsets_one lessThan_Suc_atMost le_Suc_eq)
    moreover have "A 0 \<inter> A 1 = {}"
      by (auto simp: A_def)
    ultimately have "q0 + q1 \<le> card (A 0) + card (A 1) + 1"
      by (metis card_Un_le card_lessThan le_diff_conv)
    then consider "card (A 0) \<ge> q0" | "card (A 1) \<ge> q1"
      by linarith
    then obtain i where "i < Suc (Suc 0)" "card (A i) \<ge> [q0, q1] ! i"
      by (metis One_nat_def lessI nth_Cons_0 nth_Cons_Suc zero_less_Suc)
    then obtain B where "B \<subseteq> A i" "card B = [q0, q1] ! i" "finite B"
      by (meson obtain_subset_with_card_n)
    then have "B \<in> nsets {..<q0 + q1 - 1} ([q0, q1] ! i) \<and> f ` nsets B (Suc 0) \<subseteq> {i}"
      by (auto simp: A_def nsets_def card_1_singleton_iff)
    then show ?thesis
      using \<open>i < Suc (Suc 0)\<close> by auto
  qed
  then show ?thesis
    by (simp add: partn_lst_def monochromatic_def)
qed

lemma ramsey1: "\<exists>N::nat. partn_lst {..<N} [q0,q1] 1"
  using ramsey1_explicit by blast


subsubsection \<open>Ramsey's theorem with TWO colours and arbitrary exponents (hypergraph version)\<close>

lemma ramsey_induction_step:
  fixes p::nat
  assumes p1: "partn_lst {..<p1} [q1-1,q2] (Suc r)" and p2: "partn_lst {..<p2} [q1,q2-1] (Suc r)"
    and p: "partn_lst {..<p} [p1,p2] r"
    and "q1>0" "q2>0"
  shows "partn_lst {..<Suc p} [q1, q2] (Suc r)"
proof -
  have "\<exists>i<Suc (Suc 0). \<exists>H\<in>nsets {..p} ([q1,q2] ! i). f ` nsets H (Suc r) \<subseteq> {i}"
    if f: "f \<in> nsets {..p} (Suc r) \<rightarrow> {..<Suc (Suc 0)}" for f
  proof -
    define g where "g \<equiv> \<lambda>R. f (insert p R)"
    have "f (insert p i) \<in> {..<Suc (Suc 0)}" if "i \<in> nsets {..<p} r" for i
      using that card_insert_if by (fastforce simp: nsets_def intro!: Pi_mem [OF f])
    then have g: "g \<in> nsets {..<p} r \<rightarrow> {..<Suc (Suc 0)}"
      by (force simp: g_def PiE_iff)
    then obtain i U where i: "i < Suc (Suc 0)" and gi: "g ` nsets U r \<subseteq> {i}"
      and U: "U \<in> nsets {..<p} ([p1, p2] ! i)"
      using p by (auto simp: partn_lst_def monochromatic_def)
    then have Usub: "U \<subseteq> {..<p}"
      by (auto simp: nsets_def)
    consider (izero) "i = 0" | (ione) "i = Suc 0"
      using i by linarith
    then show ?thesis
    proof cases
      case izero
      then have "U \<in> nsets {..<p} p1"
        using U by simp
      then obtain u where u: "bij_betw u {..<p1} U"
        using ex_bij_betw_nat_finite lessThan_atLeast0 by (fastforce simp: nsets_def)
      have u_nsets: "u ` X \<in> nsets {..p} n" if "X \<in> nsets {..<p1} n" for X n
      proof -
        have "inj_on u X"
          using u that bij_betw_imp_inj_on inj_on_subset by (force simp: nsets_def)
        then show ?thesis
          using Usub u that bij_betwE
          by (fastforce simp: nsets_def card_image)
      qed
      define h where "h \<equiv> \<lambda>R. f (u ` R)"
      have "h \<in> nsets {..<p1} (Suc r) \<rightarrow> {..<Suc (Suc 0)}"
        unfolding h_def using f u_nsets by auto
      then obtain j V where j: "j <Suc (Suc 0)" and hj: "h ` nsets V (Suc r) \<subseteq> {j}"
        and V: "V \<in> nsets {..<p1} ([q1 - Suc 0, q2] ! j)"
        using p1 by (auto simp: partn_lst_def monochromatic_def)
      then have Vsub: "V \<subseteq> {..<p1}"
        by (auto simp: nsets_def)
      have invinv_eq: "u ` inv_into {..<p1} u ` X = X" if "X \<subseteq> u ` {..<p1}" for X
        by (simp add: image_inv_into_cancel that)
      let ?W = "insert p (u ` V)"
      consider (jzero) "j = 0" | (jone) "j = Suc 0"
        using j by linarith
      then show ?thesis
      proof cases
        case jzero
        then have "V \<in> nsets {..<p1} (q1 - Suc 0)"
          using V by simp
        then have "u ` V \<in> nsets {..<p} (q1 - Suc 0)"
          using u_nsets [of _ "q1 - Suc 0"] nsets_mono [OF Vsub] Usub u
          unfolding bij_betw_def nsets_def
          by (fastforce elim!: subsetD)
        then have inq1: "?W \<in> nsets {..p} q1"
          unfolding nsets_def using \<open>q1 > 0\<close> card_insert_if by fastforce
        have invu_nsets: "inv_into {..<p1} u ` X \<in> nsets V r"
          if "X \<in> nsets (u ` V) r" for X r
        proof -
          have "X \<subseteq> u ` V \<and> finite X \<and> card X = r"
            using nsets_def that by auto
          then have [simp]: "card (inv_into {..<p1} u ` X) = card X"
            by (meson Vsub bij_betw_def bij_betw_inv_into card_image image_mono inj_on_subset u)
          show ?thesis
            using that u Vsub by (fastforce simp: nsets_def bij_betw_def)
        qed
        have "f X = i" if X: "X \<in> nsets ?W (Suc r)" for X
        proof (cases "p \<in> X")
          case True
          then have Xp: "X - {p} \<in> nsets (u ` V) r"
            using X by (auto simp: nsets_def)
          moreover have "u ` V \<subseteq> U"
            using Vsub bij_betwE u by blast
          ultimately have "X - {p} \<in> nsets U r"
            by (meson in_mono nsets_mono)
          then have "g (X - {p}) = i"
            using gi by blast
          have "f X = i"
            using gi True \<open>X - {p} \<in> nsets U r\<close> insert_Diff
            by (fastforce simp: g_def image_subset_iff)
          then show ?thesis
            by (simp add: \<open>f X = i\<close> \<open>g (X - {p}) = i\<close>)
        next
          case False
          then have Xim: "X \<in> nsets (u ` V) (Suc r)"
            using X by (auto simp: nsets_def subset_insert)
          then have "u ` inv_into {..<p1} u ` X = X"
            using Vsub bij_betw_imp_inj_on u
            by (fastforce simp: nsets_def image_mono invinv_eq subset_trans)
          then show ?thesis
            using izero jzero hj Xim invu_nsets unfolding h_def
            by (fastforce simp: image_subset_iff)
        qed
        moreover have "insert p (u ` V) \<in> nsets {..p} q1"
          by (simp add: izero inq1)
        ultimately show ?thesis
          by (metis izero image_subsetI insertI1 nth_Cons_0 zero_less_Suc)
      next
        case jone
        then have "u ` V \<in> nsets {..p} q2"
          using V u_nsets by auto
        moreover have "f ` nsets (u ` V) (Suc r) \<subseteq> {j}"
          using hj
          by (force simp: h_def image_subset_iff nsets_def subset_image_inj card_image dest: finite_imageD)
        ultimately show ?thesis
          using jone not_less_eq by fastforce
      qed
    next
      case ione
      then have "U \<in> nsets {..<p} p2"
        using U by simp
      then obtain u where u: "bij_betw u {..<p2} U"
        using ex_bij_betw_nat_finite lessThan_atLeast0 by (fastforce simp: nsets_def)
      have u_nsets: "u ` X \<in> nsets {..p} n" if "X \<in> nsets {..<p2} n" for X n
      proof -
        have "inj_on u X"
          using u that bij_betw_imp_inj_on inj_on_subset by (force simp: nsets_def)
        then show ?thesis
          using Usub u that bij_betwE
          by (fastforce simp: nsets_def card_image)
      qed
      define h where "h \<equiv> \<lambda>R. f (u ` R)"
      have "h \<in> nsets {..<p2} (Suc r) \<rightarrow> {..<Suc (Suc 0)}"
        unfolding h_def using f u_nsets by auto
      then obtain j V where j: "j <Suc (Suc 0)" and hj: "h ` nsets V (Suc r) \<subseteq> {j}"
        and V: "V \<in> nsets {..<p2} ([q1, q2 - Suc 0] ! j)"
        using p2 by (auto simp: partn_lst_def monochromatic_def)
      then have Vsub: "V \<subseteq> {..<p2}"
        by (auto simp: nsets_def)
      have invinv_eq: "u ` inv_into {..<p2} u ` X = X" if "X \<subseteq> u ` {..<p2}" for X
        by (simp add: image_inv_into_cancel that)
      let ?W = "insert p (u ` V)"
      consider (jzero) "j = 0" | (jone) "j = Suc 0"
        using j by linarith
      then show ?thesis
      proof cases
        case jone
        then have "V \<in> nsets {..<p2} (q2 - Suc 0)"
          using V by simp
        then have "u ` V \<in> nsets {..<p} (q2 - Suc 0)"
          using u_nsets [of _ "q2 - Suc 0"] nsets_mono [OF Vsub] Usub u
          unfolding bij_betw_def nsets_def by blast
        then have inq1: "?W \<in> nsets {..p} q2"
          unfolding nsets_def using \<open>q2 > 0\<close> card_insert_if by fastforce
        have invu_nsets: "inv_into {..<p2} u ` X \<in> nsets V r"
          if "X \<in> nsets (u ` V) r" for X r
        proof -
          have "X \<subseteq> u ` V \<and> finite X \<and> card X = r"
            using nsets_def that by auto
          then have [simp]: "card (inv_into {..<p2} u ` X) = card X"
            by (meson Vsub bij_betw_def bij_betw_inv_into card_image image_mono inj_on_subset u)
          show ?thesis
            using that u Vsub by (fastforce simp: nsets_def bij_betw_def)
        qed
        have "f X = i" if X: "X \<in> nsets ?W (Suc r)" for X
        proof (cases "p \<in> X")
          case True
          then have Xp: "X - {p} \<in> nsets (u ` V) r"
            using X by (auto simp: nsets_def)
          moreover have "u ` V \<subseteq> U"
            using Vsub bij_betwE u by blast
          ultimately have "X - {p} \<in> nsets U r"
            by (meson in_mono nsets_mono)
          then have "g (X - {p}) = i"
            using gi by blast
          have "f X = i"
            using gi True \<open>X - {p} \<in> nsets U r\<close> insert_Diff
            by (fastforce simp: g_def image_subset_iff)
          then show ?thesis
            by (simp add: \<open>f X = i\<close> \<open>g (X - {p}) = i\<close>)
        next
          case False
          then have Xim: "X \<in> nsets (u ` V) (Suc r)"
            using X by (auto simp: nsets_def subset_insert)
          then have "u ` inv_into {..<p2} u ` X = X"
            using Vsub bij_betw_imp_inj_on u
            by (fastforce simp: nsets_def image_mono invinv_eq subset_trans)
          then show ?thesis
            using ione jone hj Xim invu_nsets unfolding h_def
            by (fastforce simp: image_subset_iff)
        qed
        moreover have "insert p (u ` V) \<in> nsets {..p} q2"
          by (simp add: ione inq1)
        ultimately show ?thesis
          by (metis ione image_subsetI insertI1 lessI nth_Cons_0 nth_Cons_Suc)
      next
        case jzero
        then have "u ` V \<in> nsets {..p} q1"
          using V u_nsets by auto
        moreover have "f ` nsets (u ` V) (Suc r) \<subseteq> {j}"
          using hj unfolding h_def image_subset_iff nsets_def
          apply (clarsimp simp add: h_def image_subset_iff nsets_def)
          by (metis card_image finite_imageD subset_image_inj)
        ultimately show ?thesis
          using jzero not_less_eq by fastforce
      qed
    qed
  qed
  then show "?thesis"
    using lessThan_Suc lessThan_Suc_atMost
    by (auto simp: partn_lst_def monochromatic_def insert_commute)
qed

proposition ramsey2_full: "partn_lst {..<ES r q1 q2} [q1,q2] r"
proof (induction r arbitrary: q1 q2)
  case 0
  then show ?case
    by (auto simp: partn_lst_def monochromatic_def less_Suc_eq ex_in_conv nsets_eq_empty_iff)
next
  case (Suc r)
  note outer = this
  show ?case
  proof (cases "r = 0")
    case True
    then show ?thesis
      using ramsey1_explicit by (force simp: ES.simps)
  next
    case False
    then have "r > 0"
      by simp
    show ?thesis
      using Suc.prems
    proof (induct k \<equiv> "q1 + q2" arbitrary: q1 q2)
      case 0
      with partn_lst_0 show ?case by auto
    next
      case (Suc k)
      consider "q1 = 0 \<or> q2 = 0" | "q1 \<noteq> 0" "q2 \<noteq> 0" by auto
      then show ?case
      proof cases
        case 1
        with False partn_lst_0 partn_lst_0' show ?thesis
          by blast
      next
        define p1 where "p1 \<equiv> ES (Suc r) (q1-1) q2"
        define p2 where "p2 \<equiv> ES (Suc r) q1 (q2-1)"
        define p where "p \<equiv> ES r p1 p2"
        case 2
        with Suc have "k = (q1-1) + q2" "k = q1 + (q2 - 1)" by auto
        then have p1: "partn_lst {..<p1} [q1-1,q2] (Suc r)"
              and p2: "partn_lst {..<p2} [q1,q2-1] (Suc r)"
          using Suc.hyps unfolding p1_def p2_def by blast+
        then have p: "partn_lst {..<p} [p1,p2] r"
          using outer Suc.prems unfolding p_def by auto
        show ?thesis
          using ramsey_induction_step [OF p1 p2 p] "2" ES.simps(2) False p1_def p2_def p_def by auto
      qed
    qed
  qed
qed

subsubsection \<open>Full Ramsey's theorem with multiple colours and arbitrary exponents\<close>

theorem ramsey_full: "\<exists>N::nat. partn_lst {..<N} qs r"
proof (induction k \<equiv> "length qs" arbitrary: qs)
  case 0
  then show ?case
    by (rule_tac x=" r" in exI) (simp add: partn_lst_def)
next
  case (Suc k)
  note IH = this
  show ?case
  proof (cases k)
    case 0
    with Suc obtain q where "qs = [q]"
      by (metis length_0_conv length_Suc_conv)
    then show ?thesis
      by (rule_tac x=q in exI) (auto simp: partn_lst_def monochromatic_def funcset_to_empty_iff)
  next
    case (Suc k')
    then obtain q1 q2 l where qs: "qs = q1#q2#l"
      by (metis Suc.hyps(2) length_Suc_conv)
    then obtain q::nat where q: "partn_lst {..<q} [q1,q2] r"
      using ramsey2_full by blast
    then obtain p::nat where p: "partn_lst {..<p} (q#l) r"
      using IH \<open>qs = q1 # q2 # l\<close> by fastforce
    have keq: "Suc (length l) = k"
      using IH qs by auto
    show ?thesis
    proof (intro exI conjI)
      show "partn_lst {..<p} qs r"
      proof (auto simp: partn_lst_def)
        fix f
        assume f: "f \<in> nsets {..<p} r \<rightarrow> {..<length qs}"
        define g where "g \<equiv> \<lambda>X. if f X < Suc (Suc 0) then 0 else f X - Suc 0"
        have "g \<in> nsets {..<p} r \<rightarrow> {..<k}"
          unfolding g_def using f Suc IH
          by (auto simp: Pi_def not_less)
        then obtain i U where i: "i < k" and gi: "g ` nsets U r \<subseteq> {i}"
                and U: "U \<in> nsets {..<p} ((q#l) ! i)"
          using p keq by (auto simp: partn_lst_def monochromatic_def)
        show "\<exists>i<length qs. monochromatic {..<p} (qs!i) r f i"
        proof (cases "i = 0")
          case True
          then have "U \<in> nsets {..<p} q" and f01: "f ` nsets U r \<subseteq> {0, Suc 0}"
            using U gi unfolding g_def by (auto simp: image_subset_iff)
          then obtain u where u: "bij_betw u {..<q} U"
            using ex_bij_betw_nat_finite lessThan_atLeast0 by (fastforce simp: nsets_def)
          then have Usub: "U \<subseteq> {..<p}"
            by (smt (verit) U mem_Collect_eq nsets_def)
          have u_nsets: "u ` X \<in> nsets {..<p} n" if "X \<in> nsets {..<q} n" for X n
          proof -
            have "inj_on u X"
              using u that bij_betw_imp_inj_on inj_on_subset
              by (force simp: nsets_def)
            then show ?thesis
              using Usub u that bij_betwE
              by (fastforce simp: nsets_def card_image)
          qed
          define h where "h \<equiv> \<lambda>X. f (u ` X)"
          have "f (u ` X) < Suc (Suc 0)" if "X \<in> nsets {..<q} r" for X
          proof -
            have "u ` X \<in> nsets U r"
              using u u_nsets that by (auto simp: nsets_def bij_betwE subset_eq)
            then show ?thesis
              using f01 by auto
          qed
          then have "h \<in> nsets {..<q} r \<rightarrow> {..<Suc (Suc 0)}"
            unfolding h_def by blast
          then obtain j V where j: "j < Suc (Suc 0)" and hj: "h ` nsets V r \<subseteq> {j}"
            and V: "V \<in> nsets {..<q} ([q1,q2] ! j)"
            using q by (auto simp: partn_lst_def monochromatic_def)
          show ?thesis
            unfolding monochromatic_def
          proof (intro exI conjI bexI)
            show "j < length qs"
              using Suc Suc.hyps(2) j by linarith
            have "nsets (u ` V) r \<subseteq> (\<lambda>x. (u ` x)) ` nsets V r"
              apply (clarsimp simp add: nsets_def image_iff)
              by (metis card_image finite_imageD subset_image_inj)
            then have "f ` nsets (u ` V) r \<subseteq> h ` nsets V r"
              by (auto simp: h_def)
            then show "f ` nsets (u ` V) r \<subseteq> {j}"
              using hj by auto
            show "(u ` V) \<in> nsets {..<p} (qs ! j)"
              using V j less_2_cases numeral_2_eq_2 qs u_nsets by fastforce
          qed
        next
          case False
          then have eq: "\<And>A. \<lbrakk>A \<in> [U]\<^bsup>r\<^esup>\<rbrakk> \<Longrightarrow> f A = Suc i"
            by (metis Suc_pred diff_0_eq_0 g_def gi image_subset_iff not_gr0 singletonD)
          show ?thesis
            unfolding monochromatic_def
          proof (intro exI conjI bexI)
            show "Suc i < length qs"
              using Suc.hyps(2) i by auto
            show "f ` nsets U r \<subseteq> {Suc i}"
              using False by (auto simp: eq)
            show "U \<in> nsets {..<p} (qs ! (Suc i))"
              using False U qs by auto
          qed
        qed
      qed
    qed
  qed
qed

subsubsection \<open>Simple graph version\<close>

text \<open>This is the most basic version in terms of cliques and independent
  sets, i.e. the version for graphs and 2 colours.
\<close>

definition "clique V E \<longleftrightarrow> (\<forall>v\<in>V. \<forall>w\<in>V. v \<noteq> w \<longrightarrow> {v, w} \<in> E)"
definition "indep V E \<longleftrightarrow> (\<forall>v\<in>V. \<forall>w\<in>V. v \<noteq> w \<longrightarrow> {v, w} \<notin> E)"

lemma clique_Un: "\<lbrakk>clique K F; clique L F; \<forall>v\<in>K. \<forall>w\<in>L. v\<noteq>w \<longrightarrow> {v,w} \<in> F\<rbrakk> \<Longrightarrow> clique (K \<union> L) F"
  by (metis UnE clique_def doubleton_eq_iff)

lemma null_clique[simp]: "clique {} E" and null_indep[simp]: "indep {} E"
  by (auto simp: clique_def indep_def)

lemma smaller_clique: "\<lbrakk>clique R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> clique R' E"
  by (auto simp: clique_def)

lemma smaller_indep: "\<lbrakk>indep R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> indep R' E"
  by (auto simp: indep_def)

lemma ramsey2:
  "\<exists>r\<ge>1. \<forall>(V::'a set) (E::'a set set). finite V \<and> card V \<ge> r \<longrightarrow>
    (\<exists>R \<subseteq> V. card R = m \<and> clique R E \<or> card R = n \<and> indep R E)"
proof -
  obtain N where "N \<ge> Suc 0" and N: "partn_lst {..<N} [m,n] 2"
    using ramsey2_full nat_le_linear partn_lst_greater_resource by blast
  have "\<exists>R\<subseteq>V. card R = m \<and> clique R E \<or> card R = n \<and> indep R E"
    if "finite V" "N \<le> card V" for V :: "'a set" and E :: "'a set set"
  proof -
    from that
    obtain v where u: "inj_on v {..<N}" "v ` {..<N} \<subseteq> V"
      by (metis card_le_inj card_lessThan finite_lessThan)
    define f where "f \<equiv> \<lambda>e. if v ` e \<in> E then 0 else Suc 0"
    have f: "f \<in> nsets {..<N} 2 \<rightarrow> {..<Suc (Suc 0)}"
      by (simp add: f_def)
    then obtain i U where i: "i < 2" and gi: "f ` nsets U 2 \<subseteq> {i}"
      and U: "U \<in> nsets {..<N} ([m,n] ! i)"
      using N numeral_2_eq_2 by (auto simp: partn_lst_def monochromatic_def)
    show ?thesis
    proof (intro exI conjI)
      show "v ` U \<subseteq> V"
        using U u by (auto simp: image_subset_iff nsets_def)
      show "card (v ` U) = m \<and> clique (v ` U) E \<or> card (v ` U) = n \<and> indep (v ` U) E"
        using i unfolding numeral_2_eq_2
          using gi U u
          unfolding image_subset_iff nsets_2_eq clique_def indep_def less_Suc_eq
          by (auto simp: f_def nsets_def card_image inj_on_subset split: if_splits)
    qed
  qed
  then show ?thesis
    using \<open>Suc 0 \<le> N\<close> by auto
qed


subsection \<open>Preliminaries for the infinitary version\<close>

subsubsection \<open>``Axiom'' of Dependent Choice\<close>

primrec choice :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> 'a"
  where \<comment> \<open>An integer-indexed chain of choices\<close>
    choice_0: "choice P r 0 = (SOME x. P x)"
  | choice_Suc: "choice P r (Suc n) = (SOME y. P y \<and> (choice P r n, y) \<in> r)"

lemma choice_n:
  assumes P0: "P x0"
    and Pstep: "\<And>x. P x \<Longrightarrow> \<exists>y. P y \<and> (x, y) \<in> r"
  shows "P (choice P r n)"
proof (induct n)
  case 0
  show ?case by (force intro: someI P0)
next
  case Suc
  then show ?case by (auto intro: someI2_ex [OF Pstep])
qed

lemma dependent_choice:
  assumes trans: "trans r"
    and P0: "P x0"
    and Pstep: "\<And>x. P x \<Longrightarrow> \<exists>y. P y \<and> (x, y) \<in> r"
  obtains f :: "nat \<Rightarrow> 'a" where "\<And>n. P (f n)" and "\<And>n m. n < m \<Longrightarrow> (f n, f m) \<in> r"
proof
  fix n
  show "P (choice P r n)"
    by (blast intro: choice_n [OF P0 Pstep])
next
  fix n m :: nat
  assume "n < m"
  from Pstep [OF choice_n [OF P0 Pstep]] have "(choice P r k, choice P r (Suc k)) \<in> r" for k
    by (auto intro: someI2_ex)
  then show "(choice P r n, choice P r m) \<in> r"
    by (auto intro: less_Suc_induct [OF \<open>n < m\<close>] transD [OF trans])
qed


subsubsection \<open>Partition functions\<close>

definition part_fn :: "nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> nat) \<Rightarrow> bool"
  \<comment> \<open>the function \<^term>\<open>f\<close> partitions the \<^term>\<open>r\<close>-subsets of the typically
      infinite set \<^term>\<open>Y\<close> into \<^term>\<open>s\<close> distinct categories.\<close>
  where "part_fn r s Y f \<longleftrightarrow> (f \<in> nsets Y r \<rightarrow> {..<s})"

text \<open>For induction, we decrease the value of \<^term>\<open>r\<close> in partitions.\<close>
lemma part_fn_Suc_imp_part_fn:
  "\<lbrakk>infinite Y; part_fn (Suc r) s Y f; y \<in> Y\<rbrakk> \<Longrightarrow> part_fn r s (Y - {y}) (\<lambda>u. f (insert y u))"
  by (simp add: part_fn_def nsets_def Pi_def subset_Diff_insert)

lemma part_fn_subset: "part_fn r s YY f \<Longrightarrow> Y \<subseteq> YY \<Longrightarrow> part_fn r s Y f"
  unfolding part_fn_def nsets_def by blast


subsection \<open>Ramsey's Theorem: Infinitary Version\<close>

lemma Ramsey_induction:
  fixes s r :: nat
    and YY :: "'a set"
    and f :: "'a set \<Rightarrow> nat"
  assumes "infinite YY" "part_fn r s YY f"
  shows "\<exists>Y' t'. Y' \<subseteq> YY \<and> infinite Y' \<and> t' < s \<and> (\<forall>X. X \<subseteq> Y' \<and> finite X \<and> card X = r \<longrightarrow> f X = t')"
  using assms
proof (induct r arbitrary: YY f)
  case 0
  then show ?case
    by (auto simp add: part_fn_def card_eq_0_iff cong: conj_cong)
next
  case (Suc r)
  show ?case
  proof -
    from Suc.prems infinite_imp_nonempty obtain yy where yy: "yy \<in> YY"
      by blast
    let ?ramr = "{((y, Y, t), (y', Y', t')). y' \<in> Y \<and> Y' \<subseteq> Y}"
    let ?propr = "\<lambda>(y, Y, t).
                 y \<in> YY \<and> y \<notin> Y \<and> Y \<subseteq> YY \<and> infinite Y \<and> t < s
                 \<and> (\<forall>X. X\<subseteq>Y \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert y) X = t)"
    from Suc.prems have infYY': "infinite (YY - {yy})" by auto
    from Suc.prems have partf': "part_fn r s (YY - {yy}) (f \<circ> insert yy)"
      by (simp add: o_def part_fn_Suc_imp_part_fn yy)
    have transr: "trans ?ramr" by (force simp: trans_def)
    from Suc.hyps [OF infYY' partf']
    obtain Y0 and t0 where "Y0 \<subseteq> YY - {yy}" "infinite Y0" "t0 < s"
      "X \<subseteq> Y0 \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert yy) X = t0" for X
      by blast
    with yy have propr0: "?propr(yy, Y0, t0)" by blast
    have proprstep: "\<exists>y. ?propr y \<and> (x, y) \<in> ?ramr" if x: "?propr x" for x
    proof (cases x)
      case (fields yx Yx tx)
      with x obtain yx' where yx': "yx' \<in> Yx"
        by (blast dest: infinite_imp_nonempty)
      from fields x have infYx': "infinite (Yx - {yx'})" by auto
      with fields x yx' Suc.prems have partfx': "part_fn r s (Yx - {yx'}) (f \<circ> insert yx')"
        by (simp add: o_def part_fn_Suc_imp_part_fn part_fn_subset [where YY=YY and Y=Yx])
      from Suc.hyps [OF infYx' partfx'] obtain Y' and t'
        where Y': "Y' \<subseteq> Yx - {yx'}" "infinite Y'" "t' < s"
          "X \<subseteq> Y' \<and> finite X \<and> card X = r \<longrightarrow> (f \<circ> insert yx') X = t'" for X
        by blast
      from fields x Y' yx' have "?propr (yx', Y', t') \<and> (x, (yx', Y', t')) \<in> ?ramr"
        by blast
      then show ?thesis ..
    qed
    from dependent_choice [OF transr propr0 proprstep]
    obtain g where pg: "?propr (g n)" and rg: "n < m \<Longrightarrow> (g n, g m) \<in> ?ramr" for n m :: nat
      by blast
    let ?gy = "fst \<circ> g"
    let ?gt = "snd \<circ> snd \<circ> g"
    have rangeg: "\<exists>k. range ?gt \<subseteq> {..<k}"
    proof (intro exI subsetI)
      fix x
      assume "x \<in> range ?gt"
      then obtain n where "x = ?gt n" ..
      with pg [of n] show "x \<in> {..<s}" by (cases "g n") auto
    qed
    from rangeg have "finite (range ?gt)"
      by (simp add: finite_nat_iff_bounded)
    then obtain s' and n' where s': "s' = ?gt n'" and infeqs': "infinite {n. ?gt n = s'}"
      by (rule inf_img_fin_domE) (auto simp add: vimage_def intro: infinite_UNIV_nat)
    with pg [of n'] have less': "s'<s" by (cases "g n'") auto
    have inj_gy: "inj ?gy"
    proof (rule linorder_injI)
      fix m m' :: nat
      assume "m < m'"
      from rg [OF this] pg [of m] show "?gy m \<noteq> ?gy m'"
        by (cases "g m", cases "g m'") auto
    qed
    show ?thesis
    proof (intro exI conjI)
      from pg show "?gy ` {n. ?gt n = s'} \<subseteq> YY"
        by (auto simp add: Let_def split_beta)
      from infeqs' show "infinite (?gy ` {n. ?gt n = s'})"
        by (blast intro: inj_gy [THEN inj_on_subset] dest: finite_imageD)
      show "s' < s" by (rule less')
      show "\<forall>X. X \<subseteq> ?gy ` {n. ?gt n = s'} \<and> finite X \<and> card X = Suc r \<longrightarrow> f X = s'"
      proof -
        have "f X = s'"
          if X: "X \<subseteq> ?gy ` {n. ?gt n = s'}"
          and cardX: "finite X" "card X = Suc r"
          for X
        proof -
          from X obtain AA where AA: "AA \<subseteq> {n. ?gt n = s'}" and Xeq: "X = ?gy`AA"
            by (auto simp add: subset_image_iff)
          with cardX have "AA \<noteq> {}" by auto
          then have AAleast: "(LEAST x. x \<in> AA) \<in> AA" by (auto intro: LeastI_ex)
          show ?thesis
          proof (cases "g (LEAST x. x \<in> AA)")
            case (fields ya Ya ta)
            with AAleast Xeq have ya: "ya \<in> X" by (force intro!: rev_image_eqI)
            then have "f X = f (insert ya (X - {ya}))" by (simp add: insert_absorb)
            also have "\<dots> = ta"
            proof -
              have *: "X - {ya} \<subseteq> Ya"
              proof
                fix x assume x: "x \<in> X - {ya}"
                then obtain a' where xeq: "x = ?gy a'" and a': "a' \<in> AA"
                  by (auto simp add: Xeq)
                with fields x have "a' \<noteq> (LEAST x. x \<in> AA)" by auto
                with Least_le [of "\<lambda>x. x \<in> AA", OF a'] have "(LEAST x. x \<in> AA) < a'"
                  by arith
                from xeq fields rg [OF this] show "x \<in> Ya" by auto
              qed
              have "card (X - {ya}) = r"
                by (simp add: cardX ya)
              with pg [of "LEAST x. x \<in> AA"] fields cardX * show ?thesis
                by (auto simp del: insert_Diff_single)
            qed
            also from AA AAleast fields have "\<dots> = s'" by auto
            finally show ?thesis .
          qed
        qed
        then show ?thesis by blast
      qed
    qed
  qed
qed


theorem Ramsey:
  fixes s r :: nat
    and Z :: "'a set"
    and f :: "'a set \<Rightarrow> nat"
  shows
   "\<lbrakk>infinite Z;
      \<forall>X. X \<subseteq> Z \<and> finite X \<and> card X = r \<longrightarrow> f X < s\<rbrakk>
    \<Longrightarrow> \<exists>Y t. Y \<subseteq> Z \<and> infinite Y \<and> t < s
            \<and> (\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = r \<longrightarrow> f X = t)"
  by (blast intro: Ramsey_induction [unfolded part_fn_def nsets_def])

corollary Ramsey2:
  fixes s :: nat
    and Z :: "'a set"
    and f :: "'a set \<Rightarrow> nat"
  assumes infZ: "infinite Z"
    and part: "\<forall>x\<in>Z. \<forall>y\<in>Z. x \<noteq> y \<longrightarrow> f {x, y} < s"
  shows "\<exists>Y t. Y \<subseteq> Z \<and> infinite Y \<and> t < s \<and> (\<forall>x\<in>Y. \<forall>y\<in>Y. x\<noteq>y \<longrightarrow> f {x, y} = t)"
proof -
  from part have part2: "\<forall>X. X \<subseteq> Z \<and> finite X \<and> card X = 2 \<longrightarrow> f X < s"
    by (fastforce simp: eval_nat_numeral card_Suc_eq)
  obtain Y t where *:
    "Y \<subseteq> Z" "infinite Y" "t < s" "(\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = 2 \<longrightarrow> f X = t)"
    by (insert Ramsey [OF infZ part2]) auto
  then have "\<forall>x\<in>Y. \<forall>y\<in>Y. x \<noteq> y \<longrightarrow> f {x, y} = t" by auto
  with * show ?thesis by iprover
qed

corollary Ramsey_nsets:
  fixes f :: "'a set \<Rightarrow> nat"
  assumes "infinite Z" "f ` nsets Z r \<subseteq> {..<s}"
  obtains Y t where "Y \<subseteq> Z" "infinite Y" "t < s" "f ` nsets Y r \<subseteq> {t}"
  using Ramsey [of Z r f s] assms by (auto simp: nsets_def image_subset_iff)


subsection \<open>Disjunctive Well-Foundedness\<close>

text \<open>
  An application of Ramsey's theorem to program termination. See
  \<^cite>\<open>"Podelski-Rybalchenko"\<close>.
\<close>

definition disj_wf :: "('a \<times> 'a) set \<Rightarrow> bool"
  where "disj_wf r \<longleftrightarrow> (\<exists>T. \<exists>n::nat. (\<forall>i<n. wf (T i)) \<and> r = (\<Union>i<n. T i))"

definition transition_idx :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> nat set \<Rightarrow> nat"
  where "transition_idx s T A = (LEAST k. \<exists>i j. A = {i, j} \<and> i < j \<and> (s j, s i) \<in> T k)"


lemma transition_idx_less:
  assumes "i < j" "(s j, s i) \<in> T k" "k < n"
  shows "transition_idx s T {i, j} < n"
proof -
  from assms(1,2) have "transition_idx s T {i, j} \<le> k"
    by (simp add: transition_idx_def, blast intro: Least_le)
  with assms(3) show ?thesis by simp
qed

lemma transition_idx_in:
  assumes "i < j" "(s j, s i) \<in> T k"
  shows "(s j, s i) \<in> T (transition_idx s T {i, j})"
  using assms
  by (simp add: transition_idx_def doubleton_eq_iff conj_disj_distribR cong: conj_cong) (erule LeastI)

text \<open>To be equal to the union of some well-founded relations is equivalent
  to being the subset of such a union.\<close>
lemma disj_wf: "disj_wf r \<longleftrightarrow> (\<exists>T. \<exists>n::nat. (\<forall>i<n. wf(T i)) \<and> r \<subseteq> (\<Union>i<n. T i))"
proof -
  have *: "\<And>T n. \<lbrakk>\<forall>i<n. wf (T i); r \<subseteq> \<Union> (T ` {..<n})\<rbrakk>
           \<Longrightarrow> (\<forall>i<n. wf (T i \<inter> r)) \<and> r = (\<Union>i<n. T i \<inter> r)"
    by (force simp: wf_Int1)
  show ?thesis
    unfolding disj_wf_def by auto (metis "*")
qed

theorem trans_disj_wf_implies_wf:
  assumes "trans r"
    and "disj_wf r"
  shows "wf r"
proof (simp only: wf_iff_no_infinite_down_chain, rule notI)
  assume "\<exists>s. \<forall>i. (s (Suc i), s i) \<in> r"
  then obtain s where sSuc: "\<forall>i. (s (Suc i), s i) \<in> r" ..
  from \<open>disj_wf r\<close> obtain T and n :: nat where wfT: "\<forall>k<n. wf(T k)" and r: "r = (\<Union>k<n. T k)"
    by (auto simp add: disj_wf_def)
  have s_in_T: "\<exists>k. (s j, s i) \<in> T k \<and> k<n" if "i < j" for i j
  proof -
    from \<open>i < j\<close> have "(s j, s i) \<in> r"
    proof (induct rule: less_Suc_induct)
      case 1
      then show ?case by (simp add: sSuc)
    next
      case 2
      with \<open>trans r\<close> show ?case
        unfolding trans_def by blast
    qed
    then show ?thesis by (auto simp add: r)
  qed
  have "i < j \<Longrightarrow> transition_idx s T {i, j} < n" for i j
    using s_in_T transition_idx_less by blast
  then have trless: "i \<noteq> j \<Longrightarrow> transition_idx s T {i, j} < n" for i j
    by (metis doubleton_eq_iff less_linear)
  have "\<exists>K k. K \<subseteq> UNIV \<and> infinite K \<and> k < n \<and>
      (\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> transition_idx s T {i, j} = k)"
    by (rule Ramsey2) (auto intro: trless infinite_UNIV_nat)
  then obtain K and k where infK: "infinite K" and "k < n"
    and allk: "\<forall>i\<in>K. \<forall>j\<in>K. i \<noteq> j \<longrightarrow> transition_idx s T {i, j} = k"
    by auto
  have "(s (enumerate K (Suc m)), s (enumerate K m)) \<in> T k" for m :: nat
  proof -
    let ?j = "enumerate K (Suc m)"
    let ?i = "enumerate K m"
    have ij: "?i < ?j" by (simp add: enumerate_step infK)
    have "?j \<in> K" "?i \<in> K" by (simp_all add: enumerate_in_set infK)
    with ij have k: "k = transition_idx s T {?i, ?j}" by (simp add: allk)
    from s_in_T [OF ij] obtain k' where "(s ?j, s ?i) \<in> T k'" "k'<n" by blast
    then show "(s ?j, s ?i) \<in> T k" by (simp add: k transition_idx_in ij)
  qed
  then have "\<not> wf (T k)"
    unfolding wf_iff_no_infinite_down_chain by iprover
  with wfT \<open>k < n\<close> show False by blast
qed

end
