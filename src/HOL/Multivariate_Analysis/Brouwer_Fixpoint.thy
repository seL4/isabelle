(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
*)

(* ========================================================================= *)
(* Results connected with topological dimension.                             *)
(*                                                                           *)
(* At the moment this is just Brouwer's fixpoint theorem. The proof is from  *)
(* Kuhn: "some combinatorial lemmas in topology", IBM J. v4. (1960) p. 518   *)
(* See "http://www.research.ibm.com/journal/rd/045/ibmrd0405K.pdf".          *)
(*                                                                           *)
(* The script below is quite messy, but at least we avoid formalizing any    *)
(* topological machinery; we don't even use barycentric subdivision; this is *)
(* the big advantage of Kuhn's proof over the usual Sperner's lemma one.     *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

header {* Results connected with topological dimension. *}

theory Brouwer_Fixpoint
imports Convex_Euclidean_Space
begin

lemma bij_betw_singleton_eq:
  assumes f: "bij_betw f A B" and g: "bij_betw g A B" and a: "a \<in> A"
  assumes eq: "(\<And>x. x \<in> A \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x = g x)"
  shows "f a = g a"
proof -
  have "f ` (A - {a}) = g ` (A - {a})"
    by (intro image_cong) (simp_all add: eq)
  then have "B - {f a} = B - {g a}"
    using f g a by (auto simp: bij_betw_def inj_on_image_set_diff set_eq_iff)
  moreover have "f a \<in> B" "g a \<in> B"
    using f g a by (auto simp: bij_betw_def)
  ultimately show ?thesis
    by auto
qed

lemma swap_image:
  "Fun.swap i j f ` A = (if i \<in> A then (if j \<in> A then f ` A else f ` ((A - {i}) \<union> {j}))
                                  else (if j \<in> A then f ` ((A - {j}) \<union> {i}) else f ` A))"
  apply (auto simp: Fun.swap_def image_iff)
  apply metis
  apply (metis member_remove remove_def)
  apply (metis member_remove remove_def)
  done

lemma swap_apply1: "Fun.swap x y f x = f y"
  by (simp add: Fun.swap_def)
  
lemma swap_apply2: "Fun.swap x y f y = f x"
  by (simp add: Fun.swap_def)

lemma (in -) lessThan_empty_iff: "{..< n::nat} = {} \<longleftrightarrow> n = 0"
  by auto

lemma Zero_notin_Suc: "0 \<notin> Suc ` A"
  by auto

lemma atMost_Suc_eq_insert_0: "{.. Suc n} = insert 0 (Suc ` {.. n})"
  apply auto
  apply (case_tac x)
  apply auto
  done

lemma divide_nonneg_nonneg:
  fixes a b :: "'a :: {linordered_field, field_inverse_zero}"
  shows "a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> 0 \<le> a / b"
  by (cases "b = 0") (auto intro!: divide_nonneg_pos)

lemma setsum_Un_disjoint':
  assumes "finite A"
    and "finite B"
    and "A \<inter> B = {}"
    and "A \<union> B = C"
  shows "setsum g C = setsum g A + setsum g B"
  using setsum_Un_disjoint[OF assms(1-3)] and assms(4) by auto

lemma pointwise_minimal_pointwise_maximal:
  fixes s :: "(nat \<Rightarrow> nat) set"
  assumes "finite s"
    and "s \<noteq> {}"
    and "\<forall>x\<in>s. \<forall>y\<in>s. x \<le> y \<or> y \<le> x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. a \<le> x"
    and "\<exists>a\<in>s. \<forall>x\<in>s. x \<le> a"
  using assms
proof (induct s rule: finite_ne_induct)
  case (insert b s)
  assume *: "\<forall>x\<in>insert b s. \<forall>y\<in>insert b s. x \<le> y \<or> y \<le> x"
  moreover then obtain u l where "l \<in> s" "\<forall>b\<in>s. l \<le> b" "u \<in> s" "\<forall>b\<in>s. b \<le> u"
    using insert by auto
  ultimately show "\<exists>a\<in>insert b s. \<forall>x\<in>insert b s. a \<le> x" "\<exists>a\<in>insert b s. \<forall>x\<in>insert b s. x \<le> a"
    using *[rule_format, of b u] *[rule_format, of b l] by (metis insert_iff order.trans)+
qed auto

lemma brouwer_compactness_lemma:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "compact s"
    and "continuous_on s f"
    and "\<not> (\<exists>x\<in>s. f x = 0)"
  obtains d where "0 < d" and "\<forall>x\<in>s. d \<le> norm (f x)"
proof (cases "s = {}")
  case True
  show thesis
    by (rule that [of 1]) (auto simp: True)
next
  case False
  have "continuous_on s (norm \<circ> f)"
    by (rule continuous_intros continuous_on_norm assms(2))+
  with False obtain x where x: "x \<in> s" "\<forall>y\<in>s. (norm \<circ> f) x \<le> (norm \<circ> f) y"
    using continuous_attains_inf[OF assms(1), of "norm \<circ> f"]
    unfolding o_def
    by auto
  have "(norm \<circ> f) x > 0"
    using assms(3) and x(1)
    by auto
  then show ?thesis
    by (rule that) (insert x(2), auto simp: o_def)
qed

lemma kuhn_labelling_lemma:
  fixes P Q :: "'a::euclidean_space \<Rightarrow> bool"
  assumes "\<forall>x. P x \<longrightarrow> P (f x)"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i\<in>Basis. Q i \<longrightarrow> 0 \<le> x\<bullet>i \<and> x\<bullet>i \<le> 1)"
  shows "\<exists>l. (\<forall>x.\<forall>i\<in>Basis. l x i \<le> (1::nat)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x\<bullet>i \<le> f x\<bullet>i) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f x\<bullet>i \<le> x\<bullet>i)"
proof -
  { fix x i
    let ?R = "\<lambda>y. (P x \<and> Q i \<and> x \<bullet> i = 0 \<longrightarrow> y = (0::nat)) \<and>
        (P x \<and> Q i \<and> x \<bullet> i = 1 \<longrightarrow> y = 1) \<and>
        (P x \<and> Q i \<and> y = 0 \<longrightarrow> x \<bullet> i \<le> f x \<bullet> i) \<and>
        (P x \<and> Q i \<and> y = 1 \<longrightarrow> f x \<bullet> i \<le> x \<bullet> i)"
    { assume "P x" "Q i" "i \<in> Basis" with assms have "0 \<le> f x \<bullet> i \<and> f x \<bullet> i \<le> 1" by auto }
    then have "i \<in> Basis \<Longrightarrow> ?R 0 \<or> ?R 1" by auto }
  then show ?thesis
    unfolding all_conj_distrib[symmetric] Ball_def (* FIXME: shouldn't this work by metis? *)
    by (subst choice_iff[symmetric])+ blast
qed


subsection {* The key "counting" observation, somewhat abstracted. *}

lemma kuhn_counting_lemma:
  fixes bnd compo compo' face S F
  defines "nF s == card {f\<in>F. face f s \<and> compo' f}"
  assumes [simp, intro]: "finite F" -- "faces" and [simp, intro]: "finite S" -- "simplices"
    and "\<And>f. f \<in> F \<Longrightarrow> bnd f \<Longrightarrow> card {s\<in>S. face f s} = 1"
    and "\<And>f. f \<in> F \<Longrightarrow> \<not> bnd f \<Longrightarrow> card {s\<in>S. face f s} = 2"
    and "\<And>s. s \<in> S \<Longrightarrow> compo s \<Longrightarrow> nF s = 1"
    and "\<And>s. s \<in> S \<Longrightarrow> \<not> compo s \<Longrightarrow> nF s = 0 \<or> nF s = 2"
    and "odd (card {f\<in>F. compo' f \<and> bnd f})"
  shows "odd (card {s\<in>S. compo s})"
proof -
  have "(\<Sum>s | s \<in> S \<and> \<not> compo s. nF s) + (\<Sum>s | s \<in> S \<and> compo s. nF s) = (\<Sum>s\<in>S. nF s)"
    by (subst setsum_Un_disjoint[symmetric]) (auto intro!: setsum_cong)
  also have "\<dots> = (\<Sum>s\<in>S. card {f \<in> {f\<in>F. compo' f \<and> bnd f}. face f s}) +
                  (\<Sum>s\<in>S. card {f \<in> {f\<in>F. compo' f \<and> \<not> bnd f}. face f s})"
    unfolding setsum_addf[symmetric]
    by (subst card_Un_disjoint[symmetric])
       (auto simp: nF_def intro!: setsum_cong arg_cong[where f=card])
  also have "\<dots> = 1 * card {f\<in>F. compo' f \<and> bnd f} + 2 * card {f\<in>F. compo' f \<and> \<not> bnd f}"
    using assms(4,5) by (fastforce intro!: arg_cong2[where f="op +"] setsum_multicount)
  finally have "odd ((\<Sum>s | s \<in> S \<and> \<not> compo s. nF s) + card {s\<in>S. compo s})"
    using assms(6,8) by simp
  moreover have "(\<Sum>s | s \<in> S \<and> \<not> compo s. nF s) =
    (\<Sum>s | s \<in> S \<and> \<not> compo s \<and> nF s = 0. nF s) + (\<Sum>s | s \<in> S \<and> \<not> compo s \<and> nF s = 2. nF s)"
    using assms(7) by (subst setsum_Un_disjoint[symmetric]) (fastforce intro!: setsum_cong)+
  ultimately show ?thesis
    by auto
qed

subsection {* The odd/even result for faces of complete vertices, generalized. *}

lemma kuhn_complete_lemma:
  assumes [simp]: "finite simplices"
    and face: "\<And>f s. face f s \<longleftrightarrow> (\<exists>a\<in>s. f = s - {a})"
    and card_s[simp]:  "\<And>s. s \<in> simplices \<Longrightarrow> card s = n + 2"
    and rl_bd: "\<And>s. s \<in> simplices \<Longrightarrow> rl ` s \<subseteq> {..Suc n}"
    and bnd: "\<And>f s. s \<in> simplices \<Longrightarrow> face f s \<Longrightarrow> bnd f \<Longrightarrow> card {s\<in>simplices. face f s} = 1"
    and nbnd: "\<And>f s. s \<in> simplices \<Longrightarrow> face f s \<Longrightarrow> \<not> bnd f \<Longrightarrow> card {s\<in>simplices. face f s} = 2"
    and odd_card: "odd (card {f. (\<exists>s\<in>simplices. face f s) \<and> rl ` f = {..n} \<and> bnd f})"
  shows "odd (card {s\<in>simplices. (rl ` s = {..Suc n})})"
proof (rule kuhn_counting_lemma)
  have finite_s[simp]: "\<And>s. s \<in> simplices \<Longrightarrow> finite s"
    by (metis add_is_0 zero_neq_numeral card_infinite assms(3)) 

  let ?F = "{f. \<exists>s\<in>simplices. face f s}"
  have F_eq: "?F = (\<Union>s\<in>simplices. \<Union>a\<in>s. {s - {a}})"
    by (auto simp: face)
  show "finite ?F"
    using `finite simplices` unfolding F_eq by auto

  { fix f assume "f \<in> ?F" "bnd f" then show "card {s \<in> simplices. face f s} = 1"
      using bnd by auto }

  { fix f assume "f \<in> ?F" "\<not> bnd f" then show "card {s \<in> simplices. face f s} = 2"
      using nbnd by auto }

  show "odd (card {f \<in> {f. \<exists>s\<in>simplices. face f s}. rl ` f = {..n} \<and> bnd f})"
    using odd_card by simp

  fix s assume s[simp]: "s \<in> simplices"
  let ?S = "{f \<in> {f. \<exists>s\<in>simplices. face f s}. face f s \<and> rl ` f = {..n}}"
  have "?S = (\<lambda>a. s - {a}) ` {a\<in>s. rl ` (s - {a}) = {..n}}"
    using s by (fastforce simp: face)
  then have card_S: "card ?S = card {a\<in>s. rl ` (s - {a}) = {..n}}"
    by (auto intro!: card_image inj_onI)

  { assume rl: "rl ` s = {..Suc n}"
    then have inj_rl: "inj_on rl s"
      by (intro eq_card_imp_inj_on) auto
    moreover obtain a where "rl a = Suc n" "a \<in> s"
      by (metis atMost_iff image_iff le_Suc_eq rl)
    ultimately have n: "{..n} = rl ` (s - {a})"
      by (auto simp add: inj_on_image_set_diff rl)
    have "{a\<in>s. rl ` (s - {a}) = {..n}} = {a}"
      using inj_rl `a \<in> s` by (auto simp add: n inj_on_image_eq_iff[OF inj_rl] Diff_subset)
    then show "card ?S = 1"
      unfolding card_S by simp }

  { assume rl: "rl ` s \<noteq> {..Suc n}"
    show "card ?S = 0 \<or> card ?S = 2"
    proof cases
      assume *: "{..n} \<subseteq> rl ` s"
      with rl rl_bd[OF s] have rl_s: "rl ` s = {..n}"
        by (auto simp add: atMost_Suc subset_insert_iff split: split_if_asm)
      then have "\<not> inj_on rl s"
        by (intro pigeonhole) simp
      then obtain a b where ab: "a \<in> s" "b \<in> s" "rl a = rl b" "a \<noteq> b"
        by (auto simp: inj_on_def)
      then have eq: "rl ` (s - {a}) = rl ` s"
        by auto
      with ab have inj: "inj_on rl (s - {a})"
        by (intro eq_card_imp_inj_on) (auto simp add: rl_s card_Diff_singleton_if)

      { fix x assume "x \<in> s" "x \<notin> {a, b}"
        then have "rl ` s - {rl x} = rl ` ((s - {a}) - {x})"
          by (auto simp: eq inj_on_image_set_diff[OF inj])
        also have "\<dots> = rl ` (s - {x})"
          using ab `x \<notin> {a, b}` by auto
        also assume "\<dots> = rl ` s"
        finally have False
          using `x\<in>s` by auto }
      moreover
      { fix x assume "x \<in> {a, b}" with ab have "x \<in> s \<and> rl ` (s - {x}) = rl ` s"
          by (simp add: set_eq_iff image_iff Bex_def) metis }
      ultimately have "{a\<in>s. rl ` (s - {a}) = {..n}} = {a, b}"
        unfolding rl_s[symmetric] by fastforce
      with `a \<noteq> b` show "card ?S = 0 \<or> card ?S = 2"
        unfolding card_S by simp
    next
      assume "\<not> {..n} \<subseteq> rl ` s"
      then have "\<And>x. rl ` (s - {x}) \<noteq> {..n}"
        by auto
      then show "card ?S = 0 \<or> card ?S = 2"
        unfolding card_S by simp
    qed }
qed fact

locale kuhn_simplex =
  fixes p n and base upd and s :: "(nat \<Rightarrow> nat) set"
  assumes base: "base \<in> {..< n} \<rightarrow> {..< p}"
  assumes base_out: "\<And>i. n \<le> i \<Longrightarrow> base i = p"
  assumes upd: "bij_betw upd {..< n} {..< n}"
  assumes s_pre: "s = (\<lambda>i j. if j \<in> upd`{..< i} then Suc (base j) else base j) ` {.. n}"
begin

definition "enum i j = (if j \<in> upd`{..< i} then Suc (base j) else base j)"

lemma s_eq: "s = enum ` {.. n}"
  unfolding s_pre enum_def[abs_def] ..

lemma upd_space: "i < n \<Longrightarrow> upd i < n"
  using upd by (auto dest!: bij_betwE)

lemma s_space: "s \<subseteq> {..< n} \<rightarrow> {.. p}"
proof -
  { fix i assume "i \<le> n" then have "enum i \<in> {..< n} \<rightarrow> {.. p}"
    proof (induct i)
      case 0 then show ?case
        using base by (auto simp: Pi_iff less_imp_le enum_def)
    next
      case (Suc i) with base show ?case
        by (auto simp: Pi_iff Suc_le_eq less_imp_le enum_def intro: upd_space)
    qed }
  then show ?thesis
    by (auto simp: s_eq)
qed

lemma inj_upd: "inj_on upd {..< n}"
  using upd by (simp add: bij_betw_def)

lemma inj_enum: "inj_on enum {.. n}"
proof -
  { fix x y :: nat assume "x \<noteq> y" "x \<le> n" "y \<le> n"
    with upd have "upd ` {..< x} \<noteq> upd ` {..< y}"
      by (subst inj_on_image_eq_iff[where C="{..< n}"]) (auto simp: bij_betw_def) 
    then have "enum x \<noteq> enum y"
      by (auto simp add: enum_def fun_eq_iff) }
  then show ?thesis
    by (auto simp: inj_on_def)
qed

lemma enum_0: "enum 0 = base"
  by (simp add: enum_def[abs_def])

lemma base_in_s: "base \<in> s"
  unfolding s_eq by (subst enum_0[symmetric]) auto

lemma enum_in: "i \<le> n \<Longrightarrow> enum i \<in> s"
  unfolding s_eq by auto

lemma one_step:
  assumes a: "a \<in> s" "j < n"
  assumes *: "\<And>a'. a' \<in> s \<Longrightarrow> a' \<noteq> a \<Longrightarrow> a' j = p'"
  shows "a j \<noteq> p'"
proof
  assume "a j = p'"
  with * a have "\<And>a'. a' \<in> s \<Longrightarrow> a' j = p'"
    by auto
  then have "\<And>i. i \<le> n \<Longrightarrow> enum i j = p'"
    unfolding s_eq by auto
  from this[of 0] this[of n] have "j \<notin> upd ` {..< n}"
    by (auto simp: enum_def fun_eq_iff split: split_if_asm)
  with upd `j < n` show False
    by (auto simp: bij_betw_def)
qed

lemma upd_inj: "i < n \<Longrightarrow> j < n \<Longrightarrow> upd i = upd j \<longleftrightarrow> i = j"
  using upd by (auto simp: bij_betw_def inj_on_iff)

lemma upd_surj: "upd ` {..< n} = {..< n}"
  using upd by (auto simp: bij_betw_def)

lemma in_upd_image: "A \<subseteq> {..< n} \<Longrightarrow> i < n \<Longrightarrow> upd i \<in> upd ` A \<longleftrightarrow> i \<in> A"
  using inj_on_image_mem_iff[of upd "{..< n}" A i ] upd
  by (auto simp: bij_betw_def)

lemma enum_inj: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i = enum j \<longleftrightarrow> i = j"
  using inj_enum by (auto simp: inj_on_iff)

lemma in_enum_image: "A \<subseteq> {.. n} \<Longrightarrow> i \<le> n \<Longrightarrow> enum i \<in> enum ` A \<longleftrightarrow> i \<in> A"
  using inj_on_image_mem_iff[OF inj_enum, of A i] by auto

lemma enum_mono: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i \<le> enum j \<longleftrightarrow> i \<le> j"
  by (auto simp: enum_def le_fun_def in_upd_image Ball_def[symmetric])

lemma enum_strict_mono: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i < enum j \<longleftrightarrow> i < j"
  using enum_mono[of i j] enum_inj[of i j] by (auto simp add: le_less)

lemma chain: "a \<in> s \<Longrightarrow> b \<in> s \<Longrightarrow> a \<le> b \<or> b \<le> a"
  by (auto simp: s_eq enum_mono)

lemma less: "a \<in> s \<Longrightarrow> b \<in> s \<Longrightarrow> a i < b i \<Longrightarrow> a < b"
  using chain[of a b] by (auto simp: less_fun_def le_fun_def not_le[symmetric])

lemma enum_0_bot: "a \<in> s \<Longrightarrow> a = enum 0 \<longleftrightarrow> (\<forall>a'\<in>s. a \<le> a')"
  unfolding s_eq by (auto simp: enum_mono Ball_def)

lemma enum_n_top: "a \<in> s \<Longrightarrow> a = enum n \<longleftrightarrow> (\<forall>a'\<in>s. a' \<le> a)"
  unfolding s_eq by (auto simp: enum_mono Ball_def)

lemma enum_Suc: "i < n \<Longrightarrow> enum (Suc i) = (enum i)(upd i := Suc (enum i (upd i)))"
  by (auto simp: fun_eq_iff enum_def upd_inj)

lemma enum_eq_p: "i \<le> n \<Longrightarrow> n \<le> j \<Longrightarrow> enum i j = p"
  by (induct i) (auto simp: enum_Suc enum_0 base_out upd_space not_less[symmetric])

lemma out_eq_p: "a \<in> s \<Longrightarrow> n \<le> j \<Longrightarrow> a j = p"
  unfolding s_eq by (auto simp add: enum_eq_p)

lemma s_le_p: "a \<in> s \<Longrightarrow> a j \<le> p"
  using out_eq_p[of a j] s_space by (cases "j < n") auto

lemma le_Suc_base: "a \<in> s \<Longrightarrow> a j \<le> Suc (base j)"
  unfolding s_eq by (auto simp: enum_def)

lemma base_le: "a \<in> s \<Longrightarrow> base j \<le> a j"
  unfolding s_eq by (auto simp: enum_def)

lemma enum_le_p: "i \<le> n \<Longrightarrow> j < n \<Longrightarrow> enum i j \<le> p"
  using enum_in[of i] s_space by auto

lemma enum_less: "a \<in> s \<Longrightarrow> i < n \<Longrightarrow> enum i < a \<longleftrightarrow> enum (Suc i) \<le> a"
  unfolding s_eq by (auto simp: enum_strict_mono enum_mono)

lemma ksimplex_0:
  "n = 0 \<Longrightarrow> s = {(\<lambda>x. p)}"
  using s_eq enum_def base_out by auto

lemma replace_0:
  assumes "j < n" "a \<in> s" and p: "\<forall>x\<in>s - {a}. x j = 0" and "x \<in> s"
  shows "x \<le> a"
proof cases
  assume "x \<noteq> a"
  have "a j \<noteq> 0"
    using assms by (intro one_step[where a=a]) auto
  with less[OF `x\<in>s` `a\<in>s`, of j] p[rule_format, of x] `x \<in> s` `x \<noteq> a`
  show ?thesis
    by auto
qed simp

lemma replace_1:
  assumes "j < n" "a \<in> s" and p: "\<forall>x\<in>s - {a}. x j = p" and "x \<in> s"
  shows "a \<le> x"
proof cases
  assume "x \<noteq> a"
  have "a j \<noteq> p"
    using assms by (intro one_step[where a=a]) auto
  with enum_le_p[of _ j] `j < n` `a\<in>s`
  have "a j < p"
    by (auto simp: less_le s_eq)
  with less[OF `a\<in>s` `x\<in>s`, of j] p[rule_format, of x] `x \<in> s` `x \<noteq> a`
  show ?thesis
    by auto
qed simp

end

locale kuhn_simplex_pair = s: kuhn_simplex p n b_s u_s s + t: kuhn_simplex p n b_t u_t t
  for p n b_s u_s s b_t u_t t
begin

lemma enum_eq:
  assumes l: "i \<le> l" "l \<le> j" and "j + d \<le> n"
  assumes eq: "s.enum ` {i .. j} = t.enum ` {i + d .. j + d}"
  shows "s.enum l = t.enum (l + d)"
using l proof (induct l rule: dec_induct)
  case base
  then have s: "s.enum i \<in> t.enum ` {i + d .. j + d}" and t: "t.enum (i + d) \<in> s.enum ` {i .. j}"
    using eq by auto
  from t `i \<le> j` `j + d \<le> n` have "s.enum i \<le> t.enum (i + d)"
    by (auto simp: s.enum_mono)
  moreover from s `i \<le> j` `j + d \<le> n` have "t.enum (i + d) \<le> s.enum i"
    by (auto simp: t.enum_mono)
  ultimately show ?case
    by auto
next
  case (step l)
  moreover from step.prems `j + d \<le> n` have
      "s.enum l < s.enum (Suc l)"
      "t.enum (l + d) < t.enum (Suc l + d)"
    by (simp_all add: s.enum_strict_mono t.enum_strict_mono)
  moreover have
      "s.enum (Suc l) \<in> t.enum ` {i + d .. j + d}"
      "t.enum (Suc l + d) \<in> s.enum ` {i .. j}"
    using step `j + d \<le> n` eq by (auto simp: s.enum_inj t.enum_inj)
  ultimately have "s.enum (Suc l) = t.enum (Suc (l + d))"
    using `j + d \<le> n`
    by (intro antisym s.enum_less[THEN iffD1] t.enum_less[THEN iffD1]) 
       (auto intro!: s.enum_in t.enum_in)
  then show ?case by simp
qed

lemma ksimplex_eq_bot:
  assumes a: "a \<in> s" "\<And>a'. a' \<in> s \<Longrightarrow> a \<le> a'"
  assumes b: "b \<in> t" "\<And>b'. b' \<in> t \<Longrightarrow> b \<le> b'"
  assumes eq: "s - {a} = t - {b}"
  shows "s = t"
proof cases
  assume "n = 0" with s.ksimplex_0 t.ksimplex_0 show ?thesis by simp
next
  assume "n \<noteq> 0"
  have "s.enum 0 = (s.enum (Suc 0)) (u_s 0 := s.enum (Suc 0) (u_s 0) - 1)"
       "t.enum 0 = (t.enum (Suc 0)) (u_t 0 := t.enum (Suc 0) (u_t 0) - 1)"
    using `n \<noteq> 0` by (simp_all add: s.enum_Suc t.enum_Suc)
  moreover have e0: "a = s.enum 0" "b = t.enum 0"
    using a b by (simp_all add: s.enum_0_bot t.enum_0_bot)
  moreover
  { fix j assume "0 < j" "j \<le> n" 
    moreover have "s - {a} = s.enum ` {Suc 0 .. n}" "t - {b} = t.enum ` {Suc 0 .. n}"
      unfolding s.s_eq t.s_eq e0 by (auto simp: s.enum_inj t.enum_inj)
    ultimately have "s.enum j = t.enum j"
      using enum_eq[of "1" j n 0] eq by auto }
  note enum_eq = this
  then have "s.enum (Suc 0) = t.enum (Suc 0)"
    using `n \<noteq> 0` by auto
  moreover
  { fix j assume "Suc j < n"
    with enum_eq[of "Suc j"] enum_eq[of "Suc (Suc j)"]
    have "u_s (Suc j) = u_t (Suc j)"
      using s.enum_Suc[of "Suc j"] t.enum_Suc[of "Suc j"]
      by (auto simp: fun_eq_iff split: split_if_asm) }
  then have "\<And>j. 0 < j \<Longrightarrow> j < n \<Longrightarrow> u_s j = u_t j"
    by (auto simp: gr0_conv_Suc)
  with `n \<noteq> 0` have "u_t 0 = u_s 0"
    by (intro bij_betw_singleton_eq[OF t.upd s.upd, of 0]) auto
  ultimately have "a = b"
    by simp
  with assms show "s = t"
    by auto
qed

lemma ksimplex_eq_top:
  assumes a: "a \<in> s" "\<And>a'. a' \<in> s \<Longrightarrow> a' \<le> a"
  assumes b: "b \<in> t" "\<And>b'. b' \<in> t \<Longrightarrow> b' \<le> b"
  assumes eq: "s - {a} = t - {b}"
  shows "s = t"
proof (cases n)
  assume "n = 0" with s.ksimplex_0 t.ksimplex_0 show ?thesis by simp
next
  case (Suc n')
  have "s.enum n = (s.enum n') (u_s n' := Suc (s.enum n' (u_s n')))"
       "t.enum n = (t.enum n') (u_t n' := Suc (t.enum n' (u_t n')))"
    using Suc by (simp_all add: s.enum_Suc t.enum_Suc)
  moreover have en: "a = s.enum n" "b = t.enum n"
    using a b by (simp_all add: s.enum_n_top t.enum_n_top)
  moreover
  { fix j assume "j < n" 
    moreover have "s - {a} = s.enum ` {0 .. n'}" "t - {b} = t.enum ` {0 .. n'}"
      unfolding s.s_eq t.s_eq en by (auto simp: s.enum_inj t.enum_inj Suc)
    ultimately have "s.enum j = t.enum j"
      using enum_eq[of "0" j n' 0] eq Suc by auto }
  note enum_eq = this
  then have "s.enum n' = t.enum n'"
    using Suc by auto
  moreover
  { fix j assume "j < n'"
    with enum_eq[of j] enum_eq[of "Suc j"]
    have "u_s j = u_t j"
      using s.enum_Suc[of j] t.enum_Suc[of j]
      by (auto simp: Suc fun_eq_iff split: split_if_asm) }
  then have "\<And>j. j < n' \<Longrightarrow> u_s j = u_t j"
    by (auto simp: gr0_conv_Suc)
  then have "u_t n' = u_s n'"
    by (intro bij_betw_singleton_eq[OF t.upd s.upd, of n']) (auto simp: Suc)
  ultimately have "a = b"
    by simp
  with assms show "s = t"
    by auto
qed

end

inductive ksimplex for p n :: nat where
  ksimplex: "kuhn_simplex p n base upd s \<Longrightarrow> ksimplex p n s"

lemma finite_ksimplexes: "finite {s. ksimplex p n s}"
proof (rule finite_subset)
  { fix a s assume "ksimplex p n s" "a \<in> s"
    then obtain b u where "kuhn_simplex p n b u s" by (auto elim: ksimplex.cases)
    then interpret kuhn_simplex p n b u s .
    from s_space `a \<in> s` out_eq_p[OF `a \<in> s`]
    have "a \<in> (\<lambda>f x. if n \<le> x then p else f x) ` ({..< n} \<rightarrow>\<^sub>E {.. p})"
      by (auto simp: image_iff subset_eq Pi_iff split: split_if_asm
               intro!: bexI[of _ "restrict a {..< n}"]) }
  then show "{s. ksimplex p n s} \<subseteq> Pow ((\<lambda>f x. if n \<le> x then p else f x) ` ({..< n} \<rightarrow>\<^sub>E {.. p}))"
    by auto
qed (simp add: finite_PiE)

lemma ksimplex_card:
  assumes "ksimplex p n s" shows "card s = Suc n"
using assms proof cases
  case (ksimplex u b)
  then interpret kuhn_simplex p n u b s .
  show ?thesis
    by (simp add: card_image s_eq inj_enum)
qed

lemma simplex_top_face:
  assumes "0 < p" "\<forall>x\<in>s'. x n = p"
  shows "ksimplex p n s' \<longleftrightarrow> (\<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> s' = s - {a})"
  using assms
proof safe
  fix s a assume "ksimplex p (Suc n) s" and a: "a \<in> s" and na: "\<forall>x\<in>s - {a}. x n = p"
  then show "ksimplex p n (s - {a})"
  proof cases
    case (ksimplex base upd)
    then interpret kuhn_simplex p "Suc n" base upd "s" .

    have "a n < p"
      using one_step[of a n p] na `a\<in>s` s_space by (auto simp: less_le)
    then have "a = enum 0"
      using `a \<in> s` na by (subst enum_0_bot) (auto simp: le_less intro!: less[of a _ n])
    then have s_eq: "s - {a} = enum ` Suc ` {.. n}"
      using s_eq by (simp add: atMost_Suc_eq_insert_0 insert_ident Zero_notin_Suc in_enum_image subset_eq)
    then have "enum 1 \<in> s - {a}"
      by auto
    then have "upd 0 = n"
      using `a n < p` `a = enum 0` na[rule_format, of "enum 1"]
      by (auto simp: fun_eq_iff enum_Suc split: split_if_asm)
    then have "bij_betw upd (Suc ` {..< n}) {..< n}"
      using upd
      by (subst notIn_Un_bij_betw3[where b=0])
         (auto simp: lessThan_Suc[symmetric] lessThan_Suc_eq_insert_0)
    then have "bij_betw (upd\<circ>Suc) {..<n} {..<n}"
      by (rule bij_betw_trans[rotated]) (auto simp: bij_betw_def)

    have "a n = p - 1"
      using enum_Suc[of 0] na[rule_format, OF `enum 1 \<in> s - {a}`] `a = enum 0` by (auto simp: `upd 0 = n`)

    show ?thesis
    proof (rule ksimplex.intros, default)
      show "bij_betw (upd\<circ>Suc) {..< n} {..< n}" by fact
      show "base(n := p) \<in> {..<n} \<rightarrow> {..<p}" "\<And>i. n\<le>i \<Longrightarrow> (base(n := p)) i = p"
        using base base_out by (auto simp: Pi_iff)

      have "\<And>i. Suc ` {..< i} = {..< Suc i} - {0}"
        by (auto simp: image_iff Ball_def) arith
      then have upd_Suc: "\<And>i. i \<le> n \<Longrightarrow> (upd\<circ>Suc) ` {..< i} = upd ` {..< Suc i} - {n}"
        using `upd 0 = n`
        by (simp add: image_comp[symmetric] inj_on_image_set_diff[OF inj_upd])
      have n_in_upd: "\<And>i. n \<in> upd ` {..< Suc i}"
        using `upd 0 = n` by auto

      def f' \<equiv> "\<lambda>i j. if j \<in> (upd\<circ>Suc)`{..< i} then Suc ((base(n := p)) j) else (base(n := p)) j"
      { fix x i assume i[arith]: "i \<le> n" then have "enum (Suc i) x = f' i x"
          unfolding f'_def enum_def using `a n < p` `a = enum 0` `upd 0 = n` `a n = p - 1`
          by (simp add: upd_Suc enum_0 n_in_upd) }
      then show "s - {a} = f' ` {.. n}"
        unfolding s_eq image_comp by (intro image_cong) auto
    qed
  qed
next
  assume "ksimplex p n s'" and *: "\<forall>x\<in>s'. x n = p"
  then show "\<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> s' = s - {a}"
  proof cases
    case (ksimplex base upd)
    then interpret kuhn_simplex p n base upd s' .
    def b \<equiv> "base (n := p - 1)"
    def u \<equiv> "\<lambda>i. case i of 0 \<Rightarrow> n | Suc i \<Rightarrow> upd i"

    have "ksimplex p (Suc n) (s' \<union> {b})"
    proof (rule ksimplex.intros, default)
      show "b \<in> {..<Suc n} \<rightarrow> {..<p}"
        using base `0 < p` unfolding lessThan_Suc b_def by (auto simp: PiE_iff)
      show "\<And>i. Suc n \<le> i \<Longrightarrow> b i = p"
        using base_out by (auto simp: b_def)

      have "bij_betw u (Suc ` {..< n} \<union> {0}) ({..<n} \<union> {u 0})"
        using upd
        by (intro notIn_Un_bij_betw) (auto simp: u_def bij_betw_def image_comp comp_def inj_on_def)
      then show "bij_betw u {..<Suc n} {..<Suc n}"
        by (simp add: u_def lessThan_Suc[symmetric] lessThan_Suc_eq_insert_0)

      def f' \<equiv> "\<lambda>i j. if j \<in> u`{..< i} then Suc (b j) else b j"

      have u_eq: "\<And>i. i \<le> n \<Longrightarrow> u ` {..< Suc i} = upd ` {..< i} \<union> { n }"
        by (auto simp: u_def image_iff upd_inj Ball_def split: nat.split) arith

      { fix x have "x \<le> n \<Longrightarrow> n \<notin> upd ` {..<x}"
          using upd_space by (simp add: image_iff neq_iff) }
      note n_not_upd = this

      have *: "f' ` {.. Suc n} = f' ` (Suc ` {.. n} \<union> {0})"
        unfolding atMost_Suc_eq_insert_0 by simp
      also have "\<dots> = (f' \<circ> Suc) ` {.. n} \<union> {b}"
        by (auto simp: f'_def)
      also have "(f' \<circ> Suc) ` {.. n} = s'"
        using `0 < p` base_out[of n]
        unfolding s_eq enum_def[abs_def] f'_def[abs_def] upd_space
        by (intro image_cong) (simp_all add: u_eq b_def fun_eq_iff n_not_upd)
      finally show "s' \<union> {b} = f' ` {.. Suc n}" ..
    qed
    moreover have "b \<notin> s'"
      using * `0 < p` by (auto simp: b_def)
    ultimately show ?thesis by auto
  qed
qed

lemma ksimplex_replace_0:
  assumes s: "ksimplex p n s" and a: "a \<in> s"
  assumes j: "j < n" and p: "\<forall>x\<in>s - {a}. x j = 0"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
  using s
proof cases
  case (ksimplex b_s u_s)

  { fix t b assume "ksimplex p n t" 
    then obtain b_t u_t where "kuhn_simplex p n b_t u_t t"
      by (auto elim: ksimplex.cases)
    interpret kuhn_simplex_pair p n b_s u_s s b_t u_t t
      by intro_locales fact+

    assume b: "b \<in> t" "t - {b} = s - {a}"
    with a j p s.replace_0[of _ a] t.replace_0[of _ b] have "s = t"
      by (intro ksimplex_eq_top[of a b]) auto }
  then have "{s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = {s}"
    using s `a \<in> s` by auto
  then show ?thesis
    by simp
qed

lemma ksimplex_replace_1:
  assumes s: "ksimplex p n s" and a: "a \<in> s"
  assumes j: "j < n" and p: "\<forall>x\<in>s - {a}. x j = p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
  using s
proof cases
  case (ksimplex b_s u_s)

  { fix t b assume "ksimplex p n t" 
    then obtain b_t u_t where "kuhn_simplex p n b_t u_t t"
      by (auto elim: ksimplex.cases)
    interpret kuhn_simplex_pair p n b_s u_s s b_t u_t t
      by intro_locales fact+

    assume b: "b \<in> t" "t - {b} = s - {a}"
    with a j p s.replace_1[of _ a] t.replace_1[of _ b] have "s = t"
      by (intro ksimplex_eq_bot[of a b]) auto }
  then have "{s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = {s}"
    using s `a \<in> s` by auto
  then show ?thesis
    by simp
qed

lemma card_2_exists: "card s = 2 \<longleftrightarrow> (\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y))"
  by (auto simp add: card_Suc_eq eval_nat_numeral)

lemma ksimplex_replace_2:
  assumes s: "ksimplex p n s" and "a \<in> s" and "n \<noteq> 0"
    and lb: "\<forall>j<n. \<exists>x\<in>s - {a}. x j \<noteq> 0"
    and ub: "\<forall>j<n. \<exists>x\<in>s - {a}. x j \<noteq> p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 2"
  using s
proof cases
  case (ksimplex base upd)
  then interpret kuhn_simplex p n base upd s .

  from `a \<in> s` obtain i where "i \<le> n" "a = enum i"
    unfolding s_eq by auto

  from `i \<le> n` have "i = 0 \<or> i = n \<or> (0 < i \<and> i < n)"
    by linarith
  then have "\<exists>!s'. s' \<noteq> s \<and> ksimplex p n s' \<and> (\<exists>b\<in>s'. s - {a} = s'- {b})"
  proof (elim disjE conjE)
    assume "i = 0"
    def rot \<equiv> "\<lambda>i. if i + 1 = n then 0 else i + 1"
    let ?upd = "upd \<circ> rot"

    have rot: "bij_betw rot {..< n} {..< n}"
      by (auto simp: bij_betw_def inj_on_def image_iff Ball_def rot_def)
         arith+
    from rot upd have "bij_betw ?upd {..<n} {..<n}"
      by (rule bij_betw_trans)

    def f' \<equiv> "\<lambda>i j. if j \<in> ?upd`{..< i} then Suc (enum (Suc 0) j) else enum (Suc 0) j"

    interpret b: kuhn_simplex p n "enum (Suc 0)" "upd \<circ> rot" "f' ` {.. n}"
    proof
      from `a = enum i` ub `n \<noteq> 0` `i = 0`
      obtain i' where "i' \<le> n" "enum i' \<noteq> enum 0" "enum i' (upd 0) \<noteq> p"
        unfolding s_eq by (auto intro: upd_space simp: enum_inj)
      then have "enum 1 \<le> enum i'" "enum i' (upd 0) < p"
        using enum_le_p[of i' "upd 0"] by (auto simp add: enum_inj enum_mono upd_space)
      then have "enum 1 (upd 0) < p"
        by (auto simp add: le_fun_def intro: le_less_trans)
      then show "enum (Suc 0) \<in> {..<n} \<rightarrow> {..<p}"
        using base `n \<noteq> 0` by (auto simp add: enum_0 enum_Suc PiE_iff extensional_def upd_space)

      { fix i assume "n \<le> i" then show "enum (Suc 0) i = p"
        using `n \<noteq> 0` by (auto simp: enum_eq_p) }
      show "bij_betw ?upd {..<n} {..<n}" by fact
    qed (simp add: f'_def)
    have ks_f': "ksimplex p n (f' ` {.. n})"
      by rule unfold_locales

    have b_enum: "b.enum = f'" unfolding f'_def b.enum_def[abs_def] ..
    with b.inj_enum have inj_f': "inj_on f' {.. n}" by simp

    have [simp]: "\<And>j. j < n \<Longrightarrow> rot ` {..< j} = {0 <..< Suc j}"
      by (auto simp: rot_def image_iff Ball_def)
         arith

    { fix j assume j: "j < n"
      from j `n \<noteq> 0` have "f' j = enum (Suc j)"
        by (auto simp add: f'_def enum_def upd_inj in_upd_image image_comp[symmetric] fun_eq_iff) }
    note f'_eq_enum = this
    then have "enum ` Suc ` {..< n} = f' ` {..< n}"
      by (force simp: enum_inj)
    also have "Suc ` {..< n} = {.. n} - {0}"
      by (auto simp: image_iff Ball_def) arith
    also have "{..< n} = {.. n} - {n}"
      by auto
    finally have eq: "s - {a} = f' ` {.. n} - {f' n}"
      unfolding s_eq `a = enum i` `i = 0`
      by (simp add: inj_on_image_set_diff[OF inj_enum] inj_on_image_set_diff[OF inj_f'])

    have "enum 0 < f' 0"
      using `n \<noteq> 0` by (simp add: enum_strict_mono f'_eq_enum)
    also have "\<dots> < f' n"
      using `n \<noteq> 0` b.enum_strict_mono[of 0 n] unfolding b_enum by simp
    finally have "a \<noteq> f' n"
      using `a = enum i` `i = 0` by auto

    { fix t c assume "ksimplex p n t" "c \<in> t" and eq_sma: "s - {a} = t - {c}"
      obtain b u where "kuhn_simplex p n b u t"
        using `ksimplex p n t` by (auto elim: ksimplex.cases)
      then interpret t: kuhn_simplex p n b u t .

      { fix x assume "x \<in> s" "x \<noteq> a"
         then have "x (upd 0) = enum (Suc 0) (upd 0)"
           by (auto simp: `a = enum i` `i = 0` s_eq enum_def enum_inj) }
      then have eq_upd0: "\<forall>x\<in>t-{c}. x (upd 0) = enum (Suc 0) (upd 0)"
        unfolding eq_sma[symmetric] by auto
      then have "c (upd 0) \<noteq> enum (Suc 0) (upd 0)"
        using `n \<noteq> 0` by (intro t.one_step[OF `c\<in>t` ]) (auto simp: upd_space)
      then have "c (upd 0) < enum (Suc 0) (upd 0) \<or> c (upd 0) > enum (Suc 0) (upd 0)"
        by auto
      then have "t = s \<or> t = f' ` {..n}"
      proof (elim disjE conjE)
        assume *: "c (upd 0) < enum (Suc 0) (upd 0)"
        interpret st: kuhn_simplex_pair p n base upd s b u t ..
        { fix x assume "x \<in> t" with * `c\<in>t` eq_upd0[rule_format, of x] have "c \<le> x"
            by (auto simp: le_less intro!: t.less[of _ _ "upd 0"]) }
        note top = this
        have "s = t"
          using `a = enum i` `i = 0` `c \<in> t`
          by (intro st.ksimplex_eq_bot[OF _ _ _ _ eq_sma])
             (auto simp: s_eq enum_mono t.s_eq t.enum_mono top)
        then show ?thesis by simp
      next
        assume *: "c (upd 0) > enum (Suc 0) (upd 0)"
        interpret st: kuhn_simplex_pair p n "enum (Suc 0)" "upd \<circ> rot" "f' ` {.. n}" b u t ..
        have eq: "f' ` {..n} - {f' n} = t - {c}"
          using eq_sma eq by simp
        { fix x assume "x \<in> t" with * `c\<in>t` eq_upd0[rule_format, of x] have "x \<le> c"
            by (auto simp: le_less intro!: t.less[of _ _ "upd 0"]) }
        note top = this
        have "f' ` {..n} = t"
          using `a = enum i` `i = 0` `c \<in> t`
          by (intro st.ksimplex_eq_top[OF _ _ _ _ eq])
             (auto simp: b.s_eq b.enum_mono t.s_eq t.enum_mono b_enum[symmetric] top)
        then show ?thesis by simp
      qed }
    with ks_f' eq `a \<noteq> f' n` `n \<noteq> 0` show ?thesis
      apply (intro ex1I[of _ "f' ` {.. n}"])
      apply auto []
      apply metis
      done
  next
    assume "i = n"
    from `n \<noteq> 0` obtain n' where n': "n = Suc n'"
      by (cases n) auto

    def rot \<equiv> "\<lambda>i. case i of 0 \<Rightarrow> n' | Suc i \<Rightarrow> i"
    let ?upd = "upd \<circ> rot"

    have rot: "bij_betw rot {..< n} {..< n}"
      by (auto simp: bij_betw_def inj_on_def image_iff Bex_def rot_def n' split: nat.splits)
         arith
    from rot upd have "bij_betw ?upd {..<n} {..<n}"
      by (rule bij_betw_trans)

    def b \<equiv> "base (upd n' := base (upd n') - 1)"
    def f' \<equiv> "\<lambda>i j. if j \<in> ?upd`{..< i} then Suc (b j) else b j"

    interpret b: kuhn_simplex p n b "upd \<circ> rot" "f' ` {.. n}"
    proof
      { fix i assume "n \<le> i" then show "b i = p"
          using base_out[of i] upd_space[of n'] by (auto simp: b_def n') }
      show "b \<in> {..<n} \<rightarrow> {..<p}"
        using base `n \<noteq> 0` upd_space[of n']
        by (auto simp: b_def PiE_def Pi_iff Ball_def upd_space extensional_def n')

      show "bij_betw ?upd {..<n} {..<n}" by fact
    qed (simp add: f'_def)
    have f': "b.enum = f'" unfolding f'_def b.enum_def[abs_def] ..
    have ks_f': "ksimplex p n (b.enum ` {.. n})"
      unfolding f' by rule unfold_locales

    have "0 < n" 
      using `n \<noteq> 0` by auto

    { from `a = enum i` `n \<noteq> 0` `i = n` lb upd_space[of n']
      obtain i' where "i' \<le> n" "enum i' \<noteq> enum n" "0 < enum i' (upd n')"
        unfolding s_eq by (auto simp: enum_inj n')
      moreover have "enum i' (upd n') = base (upd n')"
        unfolding enum_def using `i' \<le> n` `enum i' \<noteq> enum n` by (auto simp: n' upd_inj enum_inj)
      ultimately have "0 < base (upd n')"
        by auto }
    then have benum1: "b.enum (Suc 0) = base"
      unfolding b.enum_Suc[OF `0<n`] b.enum_0 by (auto simp: b_def rot_def)

    have [simp]: "\<And>j. Suc j < n \<Longrightarrow> rot ` {..< Suc j} = {n'} \<union> {..< j}"
      by (auto simp: rot_def image_iff Ball_def split: nat.splits)
    have rot_simps: "\<And>j. rot (Suc j) = j" "rot 0 = n'"
      by (simp_all add: rot_def)

    { fix j assume j: "Suc j \<le> n" then have "b.enum (Suc j) = enum j"
        by (induct j) (auto simp add: benum1 enum_0 b.enum_Suc enum_Suc rot_simps) }
    note b_enum_eq_enum = this
    then have "enum ` {..< n} = b.enum ` Suc ` {..< n}"
      by (auto simp add: image_comp intro!: image_cong)
    also have "Suc ` {..< n} = {.. n} - {0}"
      by (auto simp: image_iff Ball_def) arith
    also have "{..< n} = {.. n} - {n}"
      by auto
    finally have eq: "s - {a} = b.enum ` {.. n} - {b.enum 0}"
      unfolding s_eq `a = enum i` `i = n`
      using inj_on_image_set_diff[OF inj_enum order_refl, of "{n}"]
            inj_on_image_set_diff[OF b.inj_enum order_refl, of "{0}"]
      by (simp add: comp_def)

    have "b.enum 0 \<le> b.enum n"
      by (simp add: b.enum_mono)
    also have "b.enum n < enum n"
      using `n \<noteq> 0` by (simp add: enum_strict_mono b_enum_eq_enum n')
    finally have "a \<noteq> b.enum 0"
      using `a = enum i` `i = n` by auto

    { fix t c assume "ksimplex p n t" "c \<in> t" and eq_sma: "s - {a} = t - {c}"
      obtain b' u where "kuhn_simplex p n b' u t"
        using `ksimplex p n t` by (auto elim: ksimplex.cases)
      then interpret t: kuhn_simplex p n b' u t .

      { fix x assume "x \<in> s" "x \<noteq> a"
         then have "x (upd n') = enum n' (upd n')"
           by (auto simp: `a = enum i` n' `i = n` s_eq enum_def enum_inj in_upd_image) }
      then have eq_upd0: "\<forall>x\<in>t-{c}. x (upd n') = enum n' (upd n')"
        unfolding eq_sma[symmetric] by auto
      then have "c (upd n') \<noteq> enum n' (upd n')"
        using `n \<noteq> 0` by (intro t.one_step[OF `c\<in>t` ]) (auto simp: n' upd_space[unfolded n'])
      then have "c (upd n') < enum n' (upd n') \<or> c (upd n') > enum n' (upd n')"
        by auto
      then have "t = s \<or> t = b.enum ` {..n}"
      proof (elim disjE conjE)
        assume *: "c (upd n') > enum n' (upd n')"
        interpret st: kuhn_simplex_pair p n base upd s b' u t ..
        { fix x assume "x \<in> t" with * `c\<in>t` eq_upd0[rule_format, of x] have "x \<le> c"
            by (auto simp: le_less intro!: t.less[of _ _ "upd n'"]) }
        note top = this
        have "s = t"
          using `a = enum i` `i = n` `c \<in> t`
          by (intro st.ksimplex_eq_top[OF _ _ _ _ eq_sma])
             (auto simp: s_eq enum_mono t.s_eq t.enum_mono top)
        then show ?thesis by simp
      next
        assume *: "c (upd n') < enum n' (upd n')"
        interpret st: kuhn_simplex_pair p n b "upd \<circ> rot" "f' ` {.. n}" b' u t ..
        have eq: "f' ` {..n} - {b.enum 0} = t - {c}"
          using eq_sma eq f' by simp
        { fix x assume "x \<in> t" with * `c\<in>t` eq_upd0[rule_format, of x] have "c \<le> x"
            by (auto simp: le_less intro!: t.less[of _ _ "upd n'"]) }
        note bot = this
        have "f' ` {..n} = t"
          using `a = enum i` `i = n` `c \<in> t`
          by (intro st.ksimplex_eq_bot[OF _ _ _ _ eq])
             (auto simp: b.s_eq b.enum_mono t.s_eq t.enum_mono bot)
        with f' show ?thesis by simp
      qed }
    with ks_f' eq `a \<noteq> b.enum 0` `n \<noteq> 0` show ?thesis
      apply (intro ex1I[of _ "b.enum ` {.. n}"])
      apply auto []
      apply metis
      done
  next
    assume i: "0 < i" "i < n"
    def i' \<equiv> "i - 1"
    with i have "Suc i' < n"
      by simp
    with i have Suc_i': "Suc i' = i"
      by (simp add: i'_def)

    let ?upd = "Fun.swap i' i upd"
    from i upd have "bij_betw ?upd {..< n} {..< n}"
      by (subst bij_betw_swap_iff) (auto simp: i'_def)

    def f' \<equiv> "\<lambda>i j. if j \<in> ?upd`{..< i} then Suc (base j) else base j"
    interpret b: kuhn_simplex p n base ?upd "f' ` {.. n}"
    proof
      show "base \<in> {..<n} \<rightarrow> {..<p}" by fact
      { fix i assume "n \<le> i" then show "base i = p" by fact }
      show "bij_betw ?upd {..<n} {..<n}" by fact
    qed (simp add: f'_def)
    have f': "b.enum = f'" unfolding f'_def b.enum_def[abs_def] ..
    have ks_f': "ksimplex p n (b.enum ` {.. n})"
      unfolding f' by rule unfold_locales

    have "{i} \<subseteq> {..n}"
      using i by auto
    { fix j assume "j \<le> n"
      moreover have "j < i \<or> i = j \<or> i < j" by arith
      moreover note i
      ultimately have "enum j = b.enum j \<longleftrightarrow> j \<noteq> i"
        unfolding enum_def[abs_def] b.enum_def[abs_def]
        by (auto simp add: fun_eq_iff swap_image i'_def
                           in_upd_image inj_on_image_set_diff[OF inj_upd]) }
    note enum_eq_benum = this
    then have "enum ` ({.. n} - {i}) = b.enum ` ({.. n} - {i})"
      by (intro image_cong) auto
    then have eq: "s - {a} = b.enum ` {.. n} - {b.enum i}"
      unfolding s_eq `a = enum i`
      using inj_on_image_set_diff[OF inj_enum order_refl `{i} \<subseteq> {..n}`]
            inj_on_image_set_diff[OF b.inj_enum order_refl `{i} \<subseteq> {..n}`]
      by (simp add: comp_def)

    have "a \<noteq> b.enum i"
      using `a = enum i` enum_eq_benum i by auto

    { fix t c assume "ksimplex p n t" "c \<in> t" and eq_sma: "s - {a} = t - {c}"
      obtain b' u where "kuhn_simplex p n b' u t"
        using `ksimplex p n t` by (auto elim: ksimplex.cases)
      then interpret t: kuhn_simplex p n b' u t .
      have "enum i' \<in> s - {a}" "enum (i + 1) \<in> s - {a}"
        using `a = enum i` i enum_in by (auto simp: enum_inj i'_def)
      then obtain l k where
        l: "t.enum l = enum i'" "l \<le> n" "t.enum l \<noteq> c" and
        k: "t.enum k = enum (i + 1)" "k \<le> n" "t.enum k \<noteq> c"
        unfolding eq_sma by (auto simp: t.s_eq)
      with i have "t.enum l < t.enum k"
        by (simp add: enum_strict_mono i'_def)
      with `l \<le> n` `k \<le> n` have "l < k"
        by (simp add: t.enum_strict_mono)
      { assume "Suc l = k"
        have "enum (Suc (Suc i')) = t.enum (Suc l)"
          using i by (simp add: k `Suc l = k` i'_def)
        then have False
          using `l < k` `k \<le> n` `Suc i' < n`
          by (auto simp: t.enum_Suc enum_Suc l upd_inj fun_eq_iff split: split_if_asm)
             (metis Suc_lessD n_not_Suc_n upd_inj) }
      with `l < k` have "Suc l < k"
        by arith
      have c_eq: "c = t.enum (Suc l)"
      proof (rule ccontr)
        assume "c \<noteq> t.enum (Suc l)"
        then have "t.enum (Suc l) \<in> s - {a}"
          using `l < k` `k \<le> n` by (simp add: t.s_eq eq_sma)
        then obtain j where "t.enum (Suc l) = enum j" "j \<le> n" "enum j \<noteq> enum i"
          unfolding s_eq `a = enum i` by auto
        with i have "t.enum (Suc l) \<le> t.enum l \<or> t.enum k \<le> t.enum (Suc l)"
          by (auto simp add: i'_def enum_mono enum_inj l k)
        with `Suc l < k` `k \<le> n` show False
          by (simp add: t.enum_mono)
      qed

      { have "t.enum (Suc (Suc l)) \<in> s - {a}"
          unfolding eq_sma c_eq t.s_eq using `Suc l < k` `k \<le> n` by (auto simp: t.enum_inj)
        then obtain j where eq: "t.enum (Suc (Suc l)) = enum j" and "j \<le> n" "j \<noteq> i"
          by (auto simp: s_eq `a = enum i`)
        moreover have "enum i' < t.enum (Suc (Suc l))"
          unfolding l(1)[symmetric] using `Suc l < k` `k \<le> n` by (auto simp: t.enum_strict_mono)
        ultimately have "i' < j"
          using i by (simp add: enum_strict_mono i'_def)
        with `j \<noteq> i` `j \<le> n` have "t.enum k \<le> t.enum (Suc (Suc l))"
          unfolding i'_def by (simp add: enum_mono k eq)
        then have "k \<le> Suc (Suc l)"
          using `k \<le> n` `Suc l < k` by (simp add: t.enum_mono) }
      with `Suc l < k` have "Suc (Suc l) = k" by simp
      then have "enum (Suc (Suc i')) = t.enum (Suc (Suc l))"
        using i by (simp add: k i'_def)
      also have "\<dots> = (enum i') (u l := Suc (enum i' (u l)), u (Suc l) := Suc (enum i' (u (Suc l))))"
        using `Suc l < k` `k \<le> n` by (simp add: t.enum_Suc l t.upd_inj)
      finally have "(u l = upd i' \<and> u (Suc l) = upd (Suc i')) \<or> 
        (u l = upd (Suc i') \<and> u (Suc l) = upd i')"
        using `Suc i' < n` by (auto simp: enum_Suc fun_eq_iff split: split_if_asm)

      then have "t = s \<or> t = b.enum ` {..n}"
      proof (elim disjE conjE)
        assume u: "u l = upd i'"
        have "c = t.enum (Suc l)" unfolding c_eq ..
        also have "t.enum (Suc l) = enum (Suc i')"
          using u `l < k` `k \<le> n` `Suc i' < n` by (simp add: enum_Suc t.enum_Suc l)
        also have "\<dots> = a"
          using `a = enum i` i by (simp add: i'_def)
        finally show ?thesis
          using eq_sma `a \<in> s` `c \<in> t` by auto
      next
        assume u: "u l = upd (Suc i')"
        def B \<equiv> "b.enum ` {..n}"
        have "b.enum i' = enum i'"
          using enum_eq_benum[of i'] i by (auto simp add: i'_def gr0_conv_Suc)
        have "c = t.enum (Suc l)" unfolding c_eq ..
        also have "t.enum (Suc l) = b.enum (Suc i')"
          using u `l < k` `k \<le> n` `Suc i' < n`
          by (simp_all add: enum_Suc t.enum_Suc l b.enum_Suc `b.enum i' = enum i'` swap_apply1)
             (simp add: Suc_i')
        also have "\<dots> = b.enum i"
          using i by (simp add: i'_def)
        finally have "c = b.enum i" .
        then have "t - {c} = B - {c}" "c \<in> B"
          unfolding eq_sma[symmetric] eq B_def using i by auto
        with `c \<in> t` have "t = B"
          by auto
        then show ?thesis
          by (simp add: B_def)
      qed }
    with ks_f' eq `a \<noteq> b.enum i` `n \<noteq> 0` `i \<le> n` show ?thesis
      apply (intro ex1I[of _ "b.enum ` {.. n}"])
      apply auto []
      apply metis
      done
  qed
  then show ?thesis
    using s `a \<in> s` by (simp add: card_2_exists Ex1_def) metis
qed

text {* Hence another step towards concreteness. *}

lemma kuhn_simplex_lemma:
  assumes "\<forall>s. ksimplex p (Suc n) s \<longrightarrow> rl ` s \<subseteq> {.. Suc n}"
    and "odd (card {f. \<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> (f = s - {a}) \<and>
      rl ` f = {..n} \<and> ((\<exists>j\<le>n. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>f. x j = p))})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> rl ` s = {..Suc n}})"
proof (rule kuhn_complete_lemma[OF finite_ksimplexes refl, unfolded mem_Collect_eq,
    where bnd="\<lambda>f. (\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = p)"],
    safe del: notI)

  have *: "\<And>x y. x = y \<Longrightarrow> odd (card x) \<Longrightarrow> odd (card y)"
    by auto
  show "odd (card {f. (\<exists>s\<in>{s. ksimplex p (Suc n) s}. \<exists>a\<in>s. f = s - {a}) \<and>
    rl ` f = {..n} \<and> ((\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = p))})"
    apply (rule *[OF _ assms(2)])
    apply (auto simp: atLeast0AtMost)
    done

next

  fix s assume s: "ksimplex p (Suc n) s"
  then show "card s = n + 2"
    by (simp add: ksimplex_card)

  fix a assume a: "a \<in> s" then show "rl a \<le> Suc n"
    using assms(1) s by (auto simp: subset_eq)

  let ?S = "{t. ksimplex p (Suc n) t \<and> (\<exists>b\<in>t. s - {a} = t - {b})}"
  { fix j assume j: "j \<le> n" "\<forall>x\<in>s - {a}. x j = 0"
    with s a show "card ?S = 1"
      using ksimplex_replace_0[of p "n + 1" s a j]
      by (subst eq_commute) simp }

  { fix j assume j: "j \<le> n" "\<forall>x\<in>s - {a}. x j = p"
    with s a show "card ?S = 1"
      using ksimplex_replace_1[of p "n + 1" s a j]
      by (subst eq_commute) simp }

  { assume "card ?S \<noteq> 2" "\<not> (\<exists>j\<in>{..n}. \<forall>x\<in>s - {a}. x j = p)"
    with s a show "\<exists>j\<in>{..n}. \<forall>x\<in>s - {a}. x j = 0"
      using ksimplex_replace_2[of p "n + 1" s a]
      by (subst (asm) eq_commute) auto }
qed

subsection {* Reduced labelling *}

definition reduced :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where "reduced n x = (LEAST k. k = n \<or> x k \<noteq> 0)"

lemma reduced_labelling:
  shows "reduced n x \<le> n"
    and "\<forall>i<reduced n x. x i = 0"
    and "reduced n x = n \<or> x (reduced n x) \<noteq> 0"
proof -
  show "reduced n x \<le> n"
    unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) auto
  show "\<forall>i<reduced n x. x i = 0"
    unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) fastforce+
  show "reduced n x = n \<or> x (reduced n x) \<noteq> 0"
    unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) fastforce+
qed

lemma reduced_labelling_unique:
  "r \<le> n \<Longrightarrow> \<forall>i<r. x i = 0 \<Longrightarrow> r = n \<or> x r \<noteq> 0 \<Longrightarrow> reduced n x = r"
 unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) (metis le_less not_le)+

lemma reduced_labelling_zero: "j < n \<Longrightarrow> x j = 0 \<Longrightarrow> reduced n x \<noteq> j"
  using reduced_labelling[of n x] by auto

lemma reduce_labelling_zero[simp]: "reduced 0 x = 0"
  by (rule reduced_labelling_unique) auto

lemma reduced_labelling_nonzero: "j < n \<Longrightarrow> x j \<noteq> 0 \<Longrightarrow> reduced n x \<le> j"
  using reduced_labelling[of n x] by (elim allE[where x=j]) auto

lemma reduced_labelling_Suc: "reduced (Suc n) x \<noteq> Suc n \<Longrightarrow> reduced (Suc n) x = reduced n x"
  using reduced_labelling[of "Suc n" x]
  by (intro reduced_labelling_unique[symmetric]) auto

lemma complete_face_top:
  assumes "\<forall>x\<in>f. \<forall>j\<le>n. x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x\<in>f. \<forall>j\<le>n. x j = p \<longrightarrow> lab x j = 1"
    and eq: "(reduced (Suc n) \<circ> lab) ` f = {..n}"
  shows "((\<exists>j\<le>n. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>f. x j = p)) \<longleftrightarrow> (\<forall>x\<in>f. x n = p)"
proof (safe del: disjCI)
  fix x j assume j: "j \<le> n" "\<forall>x\<in>f. x j = 0"
  { fix x assume "x \<in> f" with assms j have "reduced (Suc n) (lab x) \<noteq> j"
      by (intro reduced_labelling_zero) auto }
  moreover have "j \<in> (reduced (Suc n) \<circ> lab) ` f"
    using j eq by auto
  ultimately show "x n = p"
    by force
next
  fix x j assume j: "j \<le> n" "\<forall>x\<in>f. x j = p" and x: "x \<in> f"
  have "j = n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    { fix x assume "x \<in> f"
      with assms j have "reduced (Suc n) (lab x) \<le> j"
        by (intro reduced_labelling_nonzero) auto
      then have "reduced (Suc n) (lab x) \<noteq> n"
        using `j \<noteq> n` `j \<le> n` by simp }
    moreover
    have "n \<in> (reduced (Suc n) \<circ> lab) ` f" 
      using eq by auto
    ultimately show False
      by force
  qed
  moreover have "j \<in> (reduced (Suc n) \<circ> lab) ` f"
    using j eq by auto
  ultimately show "x n = p"
    using j x by auto
qed auto

text {* Hence we get just about the nice induction. *}

lemma kuhn_induction:
  assumes "0 < p"
    and lab_0: "\<forall>x. \<forall>j\<le>n. (\<forall>j. x j \<le> p) \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and lab_1: "\<forall>x. \<forall>j\<le>n. (\<forall>j. x j \<le> p) \<and> x j = p \<longrightarrow> lab x j = 1"
    and odd: "odd (card {s. ksimplex p n s \<and> (reduced n\<circ>lab) ` s = {..n}})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> (reduced (Suc n)\<circ>lab) ` s = {..Suc n}})"
proof -
  let ?rl = "reduced (Suc n) \<circ> lab" and ?ext = "\<lambda>f v. \<exists>j\<le>n. \<forall>x\<in>f. x j = v"
  let ?ext = "\<lambda>s. (\<exists>j\<le>n. \<forall>x\<in>s. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>s. x j = p)"
  have "\<forall>s. ksimplex p (Suc n) s \<longrightarrow> ?rl ` s \<subseteq> {..Suc n}"
    by (simp add: reduced_labelling subset_eq)
  moreover
  have "{s. ksimplex p n s \<and> (reduced n \<circ> lab) ` s = {..n}} =
        {f. \<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> f = s - {a} \<and> ?rl ` f = {..n} \<and> ?ext f}"
  proof (intro set_eqI, safe del: disjCI equalityI disjE)
    fix s assume s: "ksimplex p n s" and rl: "(reduced n \<circ> lab) ` s = {..n}"
    from s obtain u b where "kuhn_simplex p n u b s" by (auto elim: ksimplex.cases)
    then interpret kuhn_simplex p n u b s .
    have all_eq_p: "\<forall>x\<in>s. x n = p"
      by (auto simp: out_eq_p)
    moreover
    { fix x assume "x \<in> s"
      with lab_1[rule_format, of n x] all_eq_p s_le_p[of x]
      have "?rl x \<le> n"
        by (auto intro!: reduced_labelling_nonzero)
      then have "?rl x = reduced n (lab x)"
        by (auto intro!: reduced_labelling_Suc) }
    then have "?rl ` s = {..n}"
      using rl by (simp cong: image_cong)
    moreover
    obtain t a where "ksimplex p (Suc n) t" "a \<in> t" "s = t - {a}"
      using s unfolding simplex_top_face[OF `0 < p` all_eq_p] by auto
    ultimately
    show "\<exists>t a. ksimplex p (Suc n) t \<and> a \<in> t \<and> s = t - {a} \<and> ?rl ` s = {..n} \<and> ?ext s"
      by auto
  next
    fix x s a assume s: "ksimplex p (Suc n) s" and rl: "?rl ` (s - {a}) = {.. n}"
      and a: "a \<in> s" and "?ext (s - {a})"
    from s obtain u b where "kuhn_simplex p (Suc n) u b s" by (auto elim: ksimplex.cases)
    then interpret kuhn_simplex p "Suc n" u b s .
    have all_eq_p: "\<forall>x\<in>s. x (Suc n) = p"
      by (auto simp: out_eq_p)

    { fix x assume "x \<in> s - {a}"
      then have "?rl x \<in> ?rl ` (s - {a})"
        by auto
      then have "?rl x \<le> n"
        unfolding rl by auto
      then have "?rl x = reduced n (lab x)"
        by (auto intro!: reduced_labelling_Suc) }
    then show rl': "(reduced n\<circ>lab) ` (s - {a}) = {..n}"
      unfolding rl[symmetric] by (intro image_cong) auto

    from `?ext (s - {a})`
    have all_eq_p: "\<forall>x\<in>s - {a}. x n = p"
    proof (elim disjE exE conjE)
      fix j assume "j \<le> n" "\<forall>x\<in>s - {a}. x j = 0"
      with lab_0[rule_format, of j] all_eq_p s_le_p
      have "\<And>x. x \<in> s - {a} \<Longrightarrow> reduced (Suc n) (lab x) \<noteq> j"
        by (intro reduced_labelling_zero) auto
      moreover have "j \<in> ?rl ` (s - {a})"
        using `j \<le> n` unfolding rl by auto
      ultimately show ?thesis
        by force
    next
      fix j assume "j \<le> n" and eq_p: "\<forall>x\<in>s - {a}. x j = p"
      show ?thesis
      proof cases
        assume "j = n" with eq_p show ?thesis by simp
      next
        assume "j \<noteq> n"
        { fix x assume x: "x \<in> s - {a}"
          have "reduced n (lab x) \<le> j"
          proof (rule reduced_labelling_nonzero)
            show "lab x j \<noteq> 0"
              using lab_1[rule_format, of j x] x s_le_p[of x] eq_p `j \<le> n` by auto
            show "j < n"
              using `j \<le> n` `j \<noteq> n` by simp
          qed
          then have "reduced n (lab x) \<noteq> n"
            using `j \<le> n` `j \<noteq> n` by simp }
        moreover have "n \<in> (reduced n\<circ>lab) ` (s - {a})"
          unfolding rl' by auto
        ultimately show ?thesis
          by force
      qed
    qed
    show "ksimplex p n (s - {a})"
      unfolding simplex_top_face[OF `0 < p` all_eq_p] using s a by auto
  qed
  ultimately show ?thesis
    using assms by (intro kuhn_simplex_lemma) auto
qed

text {* And so we get the final combinatorial result. *}

lemma ksimplex_0: "ksimplex p 0 s \<longleftrightarrow> s = {(\<lambda>x. p)}"
proof
  assume "ksimplex p 0 s" then show "s = {(\<lambda>x. p)}"
    by (blast dest: kuhn_simplex.ksimplex_0 elim: ksimplex.cases)
next
  assume s: "s = {(\<lambda>x. p)}"
  show "ksimplex p 0 s"
  proof (intro ksimplex, unfold_locales)
    show "(\<lambda>_. p) \<in> {..<0::nat} \<rightarrow> {..<p}" by auto
    show "bij_betw id {..<0} {..<0}"
      by simp
  qed (auto simp: s)
qed

lemma kuhn_combinatorial:
  assumes "0 < p"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> j < n \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> j < n  \<and> x j = p \<longrightarrow> lab x j = 1"
  shows "odd (card {s. ksimplex p n s \<and> (reduced n\<circ>lab) ` s = {..n}})"
    (is "odd (card (?M n))")
  using assms
proof (induct n)
  case 0 then show ?case
    by (simp add: ksimplex_0 cong: conj_cong)
next
  case (Suc n)
  then have "odd (card (?M n))"
    by force
  with Suc show ?case
    using kuhn_induction[of p n] by (auto simp: comp_def)
qed

lemma kuhn_lemma:
  fixes n p :: nat
  assumes "0 < p"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. label x i = (0::nat) \<or> label x i = 1)"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = 0 \<longrightarrow> label x i = 0)"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = p \<longrightarrow> label x i = 1)"
  obtains q where "\<forall>i<n. q i < p"
    and "\<forall>i<n. \<exists>r s. (\<forall>j<n. q j \<le> r j \<and> r j \<le> q j + 1) \<and> (\<forall>j<n. q j \<le> s j \<and> s j \<le> q j + 1) \<and> label r i \<noteq> label s i"
proof -
  let ?rl = "reduced n\<circ>label"
  let ?A = "{s. ksimplex p n s \<and> ?rl ` s = {..n}}"
  have "odd (card ?A)"
    using assms by (intro kuhn_combinatorial[of p n label]) auto
  then have "?A \<noteq> {}"
    by (intro notI) simp
  then obtain s b u where "kuhn_simplex p n b u s" and rl: "?rl ` s = {..n}"
    by (auto elim: ksimplex.cases)
  interpret kuhn_simplex p n b u s by fact

  show ?thesis
  proof (intro that[of b] allI impI)
    fix i assume "i < n" then show "b i < p"
      using base by auto
  next
    case goal2
    then have "i \<in> {.. n}" "Suc i \<in> {.. n}"
      by auto
    then obtain u v where u: "u \<in> s" "Suc i = ?rl u" and v: "v \<in> s" "i = ?rl v"
      unfolding rl[symmetric] by blast

    have "label u i \<noteq> label v i"
      using reduced_labelling [of n "label u"] reduced_labelling [of n "label v"]
        u(2)[symmetric] v(2)[symmetric] `i < n`
      by auto
    moreover
    { fix j assume "j < n"
      then have "b j \<le> u j" "u j \<le> b j + 1" "b j \<le> v j" "v j \<le> b j + 1"
        using base_le[OF `u\<in>s`] le_Suc_base[OF `u\<in>s`] base_le[OF `v\<in>s`] le_Suc_base[OF `v\<in>s`] by auto }
    ultimately show ?case
      by blast
  qed
qed

subsection {* The main result for the unit cube *}

lemma kuhn_labelling_lemma':
  assumes "(\<forall>x::nat\<Rightarrow>real. P x \<longrightarrow> P (f x))"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i::nat. Q i \<longrightarrow> 0 \<le> x i \<and> x i \<le> 1)"
  shows "\<exists>l. (\<forall>x i. l x i \<le> (1::nat)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 0 \<longrightarrow> l x i = 0) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 1 \<longrightarrow> l x i = 1) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 0 \<longrightarrow> x i \<le> f x i) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 1 \<longrightarrow> f x i \<le> x i)"
proof -
  have and_forall_thm: "\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)"
    by auto
  have *: "\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x"
    by auto
  show ?thesis
    unfolding and_forall_thm
    apply (subst choice_iff[symmetric])+
    apply rule
    apply rule
  proof -
    case goal1
    let ?R = "\<lambda>y::nat.
      (P x \<and> Q xa \<and> x xa = 0 \<longrightarrow> y = 0) \<and>
      (P x \<and> Q xa \<and> x xa = 1 \<longrightarrow> y = 1) \<and>
      (P x \<and> Q xa \<and> y = 0 \<longrightarrow> x xa \<le> (f x) xa) \<and>
      (P x \<and> Q xa \<and> y = 1 \<longrightarrow> (f x) xa \<le> x xa)"
    {
      assume "P x" and "Q xa"
      then have "0 \<le> f x xa \<and> f x xa \<le> 1"
        using assms(2)[rule_format,of "f x" xa]
        apply (drule_tac assms(1)[rule_format])
        apply auto
        done
    }
    then have "?R 0 \<or> ?R 1"
      by auto
    then show ?case
      by auto
  qed
qed

definition unit_cube :: "'a::euclidean_space set"
  where "unit_cube = {x. \<forall>i\<in>Basis. 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1}"

lemma mem_unit_cube: "x \<in> unit_cube \<longleftrightarrow> (\<forall>i\<in>Basis. 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1)"
  unfolding unit_cube_def by simp

lemma bounded_unit_cube: "bounded unit_cube"
  unfolding bounded_def
proof (intro exI ballI)
  fix y :: 'a assume y: "y \<in> unit_cube"
  have "dist 0 y = norm y" by (rule dist_0_norm)
  also have "\<dots> = norm (\<Sum>i\<in>Basis. (y \<bullet> i) *\<^sub>R i)" unfolding euclidean_representation ..
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. norm ((y \<bullet> i) *\<^sub>R i))" by (rule norm_setsum)
  also have "\<dots> \<le> (\<Sum>i::'a\<in>Basis. 1)"
    by (rule setsum_mono, simp add: y [unfolded mem_unit_cube])
  finally show "dist 0 y \<le> (\<Sum>i::'a\<in>Basis. 1)" .
qed

lemma closed_unit_cube: "closed unit_cube"
  unfolding unit_cube_def Collect_ball_eq Collect_conj_eq
  by (rule closed_INT, auto intro!: closed_Collect_le)

lemma compact_unit_cube: "compact unit_cube" (is "compact ?C")
  unfolding compact_eq_seq_compact_metric
  using bounded_unit_cube closed_unit_cube
  by (rule bounded_closed_imp_seq_compact)

lemma brouwer_cube:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "continuous_on unit_cube f"
    and "f ` unit_cube \<subseteq> unit_cube"
  shows "\<exists>x\<in>unit_cube. f x = x"
proof (rule ccontr)
  def n \<equiv> "DIM('a)"
  have n: "1 \<le> n" "0 < n" "n \<noteq> 0"
    unfolding n_def by (auto simp add: Suc_le_eq DIM_positive)
  assume "\<not> ?thesis"
  then have *: "\<not> (\<exists>x\<in>unit_cube. f x - x = 0)"
    by auto
  obtain d where
      d: "d > 0" "\<And>x. x \<in> unit_cube \<Longrightarrow> d \<le> norm (f x - x)"
    apply (rule brouwer_compactness_lemma[OF compact_unit_cube _ *])
    apply (rule continuous_intros assms)+
    apply blast
    done
  have *: "\<forall>x. x \<in> unit_cube \<longrightarrow> f x \<in> unit_cube"
    "\<forall>x. x \<in> (unit_cube::'a set) \<longrightarrow> (\<forall>i\<in>Basis. True \<longrightarrow> 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1)"
    using assms(2)[unfolded image_subset_iff Ball_def]
    unfolding mem_unit_cube
    by auto
  obtain label :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
    "\<forall>x. \<forall>i\<in>Basis. label x i \<le> 1"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> x \<bullet> i = 0 \<longrightarrow> label x i = 0"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> x \<bullet> i = 1 \<longrightarrow> label x i = 1"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> label x i = 0 \<longrightarrow> x \<bullet> i \<le> f x \<bullet> i"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> label x i = 1 \<longrightarrow> f x \<bullet> i \<le> x \<bullet> i"
    using kuhn_labelling_lemma[OF *] by blast
  note label = this [rule_format]
  have lem1: "\<forall>x\<in>unit_cube. \<forall>y\<in>unit_cube. \<forall>i\<in>Basis. label x i \<noteq> label y i \<longrightarrow>
    abs (f x \<bullet> i - x \<bullet> i) \<le> norm (f y - f x) + norm (y - x)"
  proof safe
    fix x y :: 'a
    assume x: "x \<in> unit_cube"
    assume y: "y \<in> unit_cube"
    fix i
    assume i: "label x i \<noteq> label y i" "i \<in> Basis"
    have *: "\<And>x y fx fy :: real. x \<le> fx \<and> fy \<le> y \<or> fx \<le> x \<and> y \<le> fy \<Longrightarrow>
      abs (fx - x) \<le> abs (fy - fx) + abs (y - x)" by auto
    have "\<bar>(f x - x) \<bullet> i\<bar> \<le> abs ((f y - f x)\<bullet>i) + abs ((y - x)\<bullet>i)"
      unfolding inner_simps
      apply (rule *)
      apply (cases "label x i = 0")
      apply (rule disjI1)
      apply rule
      prefer 3
      apply (rule disjI2)
      apply rule
    proof -
      assume lx: "label x i = 0"
      then have ly: "label y i = 1"
        using i label(1)[of i y]
        by auto
      show "x \<bullet> i \<le> f x \<bullet> i"
        apply (rule label(4)[rule_format])
        using x y lx i(2)
        apply auto
        done
      show "f y \<bullet> i \<le> y \<bullet> i"
        apply (rule label(5)[rule_format])
        using x y ly i(2)
        apply auto
        done
    next
      assume "label x i \<noteq> 0"
      then have l: "label x i = 1" "label y i = 0"
        using i label(1)[of i x] label(1)[of i y]
        by auto
      show "f x \<bullet> i \<le> x \<bullet> i"
        apply (rule label(5)[rule_format])
        using x y l i(2)
        apply auto
        done
      show "y \<bullet> i \<le> f y \<bullet> i"
        apply (rule label(4)[rule_format])
        using x y l i(2)
        apply auto
        done
    qed
    also have "\<dots> \<le> norm (f y - f x) + norm (y - x)"
      apply (rule add_mono)
      apply (rule Basis_le_norm[OF i(2)])+
      done
    finally show "\<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y - f x) + norm (y - x)"
      unfolding inner_simps .
  qed
  have "\<exists>e>0. \<forall>x\<in>unit_cube. \<forall>y\<in>unit_cube. \<forall>z\<in>unit_cube. \<forall>i\<in>Basis.
    norm (x - z) < e \<and> norm (y - z) < e \<and> label x i \<noteq> label y i \<longrightarrow>
      abs ((f(z) - z)\<bullet>i) < d / (real n)"
  proof -
    have d': "d / real n / 8 > 0"
      using d(1) by (simp add: n_def DIM_positive)
    have *: "uniformly_continuous_on unit_cube f"
      by (rule compact_uniformly_continuous[OF assms(1) compact_unit_cube])
    obtain e where e:
        "e > 0"
        "\<And>x x'. x \<in> unit_cube \<Longrightarrow>
          x' \<in> unit_cube \<Longrightarrow>
          norm (x' - x) < e \<Longrightarrow>
          norm (f x' - f x) < d / real n / 8"
      using *[unfolded uniformly_continuous_on_def,rule_format,OF d']
      unfolding dist_norm
      by blast
    show ?thesis
      apply (rule_tac x="min (e/2) (d/real n/8)" in exI)
      apply safe
    proof -
      show "0 < min (e / 2) (d / real n / 8)"
        using d' e by auto
      fix x y z i
      assume as:
        "x \<in> unit_cube" "y \<in> unit_cube" "z \<in> unit_cube"
        "norm (x - z) < min (e / 2) (d / real n / 8)"
        "norm (y - z) < min (e / 2) (d / real n / 8)"
        "label x i \<noteq> label y i"
      assume i: "i \<in> Basis"
      have *: "\<And>z fz x fx n1 n2 n3 n4 d4 d :: real. abs(fx - x) \<le> n1 + n2 \<Longrightarrow>
        abs (fx - fz) \<le> n3 \<Longrightarrow> abs (x - z) \<le> n4 \<Longrightarrow>
        n1 < d4 \<Longrightarrow> n2 < 2 * d4 \<Longrightarrow> n3 < d4 \<Longrightarrow> n4 < d4 \<Longrightarrow>
        (8 * d4 = d) \<Longrightarrow> abs(fz - z) < d"
        by auto
      show "\<bar>(f z - z) \<bullet> i\<bar> < d / real n"
        unfolding inner_simps
      proof (rule *)
        show "\<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y -f x) + norm (y - x)"
          apply (rule lem1[rule_format])
          using as i
          apply auto
          done
        show "\<bar>f x \<bullet> i - f z \<bullet> i\<bar> \<le> norm (f x - f z)" "\<bar>x \<bullet> i - z \<bullet> i\<bar> \<le> norm (x - z)"
          unfolding inner_diff_left[symmetric]
          by (rule Basis_le_norm[OF i])+
        have tria: "norm (y - x) \<le> norm (y - z) + norm (x - z)"
          using dist_triangle[of y x z, unfolded dist_norm]
          unfolding norm_minus_commute
          by auto
        also have "\<dots> < e / 2 + e / 2"
          apply (rule add_strict_mono)
          using as(4,5)
          apply auto
          done
        finally show "norm (f y - f x) < d / real n / 8"
          apply -
          apply (rule e(2))
          using as
          apply auto
          done
        have "norm (y - z) + norm (x - z) < d / real n / 8 + d / real n / 8"
          apply (rule add_strict_mono)
          using as
          apply auto
          done
        then show "norm (y - x) < 2 * (d / real n / 8)"
          using tria
          by auto
        show "norm (f x - f z) < d / real n / 8"
          apply (rule e(2))
          using as e(1)
          apply auto
          done
      qed (insert as, auto)
    qed
  qed
  then
  obtain e where e:
    "e > 0"
    "\<And>x y z i. x \<in> unit_cube \<Longrightarrow>
      y \<in> unit_cube \<Longrightarrow>
      z \<in> unit_cube \<Longrightarrow>
      i \<in> Basis \<Longrightarrow>
      norm (x - z) < e \<and> norm (y - z) < e \<and> label x i \<noteq> label y i \<Longrightarrow>
      \<bar>(f z - z) \<bullet> i\<bar> < d / real n"
    by blast
  obtain p :: nat where p: "1 + real n / e \<le> real p"
    using real_arch_simple ..
  have "1 + real n / e > 0"
    using e(1) n by (simp add: add_pos_pos)
  then have "p > 0"
    using p by auto

  obtain b :: "nat \<Rightarrow> 'a" where b: "bij_betw b {..< n} Basis"
    by atomize_elim (auto simp: n_def intro!: finite_same_card_bij)
  def b' \<equiv> "inv_into {..< n} b"
  then have b': "bij_betw b' Basis {..< n}"
    using bij_betw_inv_into[OF b] by auto
  then have b'_Basis: "\<And>i. i \<in> Basis \<Longrightarrow> b' i \<in> {..< n}"
    unfolding bij_betw_def by (auto simp: set_eq_iff)
  have bb'[simp]:"\<And>i. i \<in> Basis \<Longrightarrow> b (b' i) = i"
    unfolding b'_def
    using b
    by (auto simp: f_inv_into_f bij_betw_def)
  have b'b[simp]:"\<And>i. i < n \<Longrightarrow> b' (b i) = i"
    unfolding b'_def
    using b
    by (auto simp: inv_into_f_eq bij_betw_def)
  have *: "\<And>x :: nat. x = 0 \<or> x = 1 \<longleftrightarrow> x \<le> 1"
    by auto
  have b'': "\<And>j. j < n \<Longrightarrow> b j \<in> Basis"
    using b unfolding bij_betw_def by auto
  have q1: "0 < p" "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow>
    (\<forall>i<n. (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0 \<or>
           (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1)"
    unfolding *
    using `p > 0` `n > 0`
    using label(1)[OF b'']
    by auto
  { fix x :: "nat \<Rightarrow> nat" and i assume "\<forall>i<n. x i \<le> p" "i < n" "x i = p \<or> x i = 0"
    then have "(\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<in> (unit_cube::'a set)"
      using b'_Basis
      by (auto simp add: mem_unit_cube inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1) }
  note cube = this
  have q2: "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = 0 \<longrightarrow>
      (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0)"
    unfolding o_def using cube `p > 0` by (intro allI impI label(2)) (auto simp add: b'')
  have q3: "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = p \<longrightarrow> 
      (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1)"
    using cube `p > 0` unfolding o_def by (intro allI impI label(3)) (auto simp add: b'')
  obtain q where q:
      "\<forall>i<n. q i < p"
      "\<forall>i<n.
         \<exists>r s. (\<forall>j<n. q j \<le> r j \<and> r j \<le> q j + 1) \<and>
               (\<forall>j<n. q j \<le> s j \<and> s j \<le> q j + 1) \<and>
               (label (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i) \<circ> b) i \<noteq>
               (label (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i) \<circ> b) i"
    by (rule kuhn_lemma[OF q1 q2 q3])
  def z \<equiv> "(\<Sum>i\<in>Basis. (real (q (b' i)) / real p) *\<^sub>R i)::'a"
  have "\<exists>i\<in>Basis. d / real n \<le> abs ((f z - z)\<bullet>i)"
  proof (rule ccontr)
    have "\<forall>i\<in>Basis. q (b' i) \<in> {0..p}"
      using q(1) b'
      by (auto intro: less_imp_le simp: bij_betw_def)
    then have "z \<in> unit_cube"
      unfolding z_def mem_unit_cube
      using b'_Basis
      by (auto simp add: bij_betw_def zero_le_divide_iff divide_le_eq_1)
    then have d_fz_z: "d \<le> norm (f z - z)"
      by (rule d)
    assume "\<not> ?thesis"
    then have as: "\<forall>i\<in>Basis. \<bar>f z \<bullet> i - z \<bullet> i\<bar> < d / real n"
      using `n > 0`
      by (auto simp add: not_le inner_diff)
    have "norm (f z - z) \<le> (\<Sum>i\<in>Basis. \<bar>f z \<bullet> i - z \<bullet> i\<bar>)"
      unfolding inner_diff_left[symmetric]
      by (rule norm_le_l1)
    also have "\<dots> < (\<Sum>(i::'a) \<in> Basis. d / real n)"
      apply (rule setsum_strict_mono)
      using as
      apply auto
      done
    also have "\<dots> = d"
      using DIM_positive[where 'a='a]
      by (auto simp: real_eq_of_nat n_def)
    finally show False
      using d_fz_z by auto
  qed
  then obtain i where i: "i \<in> Basis" "d / real n \<le> \<bar>(f z - z) \<bullet> i\<bar>" ..
  have *: "b' i < n"
    using i and b'[unfolded bij_betw_def]
    by auto
  obtain r s where rs:
    "\<And>j. j < n \<Longrightarrow> q j \<le> r j \<and> r j \<le> q j + 1"
    "\<And>j. j < n \<Longrightarrow> q j \<le> s j \<and> s j \<le> q j + 1"
    "(label (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i) \<circ> b) (b' i) \<noteq>
      (label (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i) \<circ> b) (b' i)"
    using q(2)[rule_format,OF *] by blast
  have b'_im: "\<And>i. i \<in> Basis \<Longrightarrow>  b' i < n"
    using b' unfolding bij_betw_def by auto
  def r' \<equiv> "(\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i)::'a"
  have "\<And>i. i \<in> Basis \<Longrightarrow> r (b' i) \<le> p"
    apply (rule order_trans)
    apply (rule rs(1)[OF b'_im,THEN conjunct2])
    using q(1)[rule_format,OF b'_im]
    apply (auto simp add: Suc_le_eq)
    done
  then have "r' \<in> unit_cube"
    unfolding r'_def mem_unit_cube
    using b'_Basis
    by (auto simp add: bij_betw_def zero_le_divide_iff divide_le_eq_1)
  def s' \<equiv> "(\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i)::'a"
  have "\<And>i. i \<in> Basis \<Longrightarrow> s (b' i) \<le> p"
    apply (rule order_trans)
    apply (rule rs(2)[OF b'_im, THEN conjunct2])
    using q(1)[rule_format,OF b'_im]
    apply (auto simp add: Suc_le_eq)
    done
  then have "s' \<in> unit_cube"
    unfolding s'_def mem_unit_cube
    using b'_Basis
    by (auto simp add: bij_betw_def zero_le_divide_iff divide_le_eq_1)
  have "z \<in> unit_cube"
    unfolding z_def mem_unit_cube
    using b'_Basis q(1)[rule_format,OF b'_im] `p > 0`
    by (auto simp add: bij_betw_def zero_le_divide_iff divide_le_eq_1 less_imp_le)
  have *: "\<And>x. 1 + real x = real (Suc x)"
    by auto
  {
    have "(\<Sum>i\<in>Basis. \<bar>real (r (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>(i::'a)\<in>Basis. 1)"
      apply (rule setsum_mono)
      using rs(1)[OF b'_im]
      apply (auto simp add:* field_simps)
      done
    also have "\<dots> < e * real p"
      using p `e > 0` `p > 0`
      by (auto simp add: field_simps n_def real_of_nat_def)
    finally have "(\<Sum>i\<in>Basis. \<bar>real (r (b' i)) - real (q (b' i))\<bar>) < e * real p" .
  }
  moreover
  {
    have "(\<Sum>i\<in>Basis. \<bar>real (s (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>(i::'a)\<in>Basis. 1)"
      apply (rule setsum_mono)
      using rs(2)[OF b'_im]
      apply (auto simp add:* field_simps)
      done
    also have "\<dots> < e * real p"
      using p `e > 0` `p > 0`
      by (auto simp add: field_simps n_def real_of_nat_def)
    finally have "(\<Sum>i\<in>Basis. \<bar>real (s (b' i)) - real (q (b' i))\<bar>) < e * real p" .
  }
  ultimately
  have "norm (r' - z) < e" and "norm (s' - z) < e"
    unfolding r'_def s'_def z_def
    using `p > 0`
    apply (rule_tac[!] le_less_trans[OF norm_le_l1])
    apply (auto simp add: field_simps setsum_divide_distrib[symmetric] inner_diff_left)
    done
  then have "\<bar>(f z - z) \<bullet> i\<bar> < d / real n"
    using rs(3) i
    unfolding r'_def[symmetric] s'_def[symmetric] o_def bb'
    by (intro e(2)[OF `r'\<in>unit_cube` `s'\<in>unit_cube` `z\<in>unit_cube`]) auto
  then show False
    using i by auto
qed


subsection {* Retractions *}

definition "retraction s t r \<longleftrightarrow> t \<subseteq> s \<and> continuous_on s r \<and> r ` s \<subseteq> t \<and> (\<forall>x\<in>t. r x = x)"

definition retract_of (infixl "retract'_of" 12)
  where "(t retract_of s) \<longleftrightarrow> (\<exists>r. retraction s t r)"

lemma retraction_idempotent: "retraction s t r \<Longrightarrow> x \<in> s \<Longrightarrow>  r (r x) = r x"
  unfolding retraction_def by auto

subsection {* Preservation of fixpoints under (more general notion of) retraction *}

lemma invertible_fixpoint_property:
  fixes s :: "'a::euclidean_space set"
    and t :: "'b::euclidean_space set"
  assumes "continuous_on t i"
    and "i ` t \<subseteq> s"
    and "continuous_on s r"
    and "r ` s \<subseteq> t"
    and "\<forall>y\<in>t. r (i y) = y"
    and "\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)"
    and "continuous_on t g"
    and "g ` t \<subseteq> t"
  obtains y where "y \<in> t" and "g y = y"
proof -
  have "\<exists>x\<in>s. (i \<circ> g \<circ> r) x = x"
    apply (rule assms(6)[rule_format])
    apply rule
    apply (rule continuous_on_compose assms)+
    apply ((rule continuous_on_subset)?, rule assms)+
    using assms(2,4,8)
    apply auto
    apply blast
    done
  then obtain x where x: "x \<in> s" "(i \<circ> g \<circ> r) x = x" ..
  then have *: "g (r x) \<in> t"
    using assms(4,8) by auto
  have "r ((i \<circ> g \<circ> r) x) = r x"
    using x by auto
  then show ?thesis
    apply (rule_tac that[of "r x"])
    using x
    unfolding o_def
    unfolding assms(5)[rule_format,OF *]
    using assms(4)
    apply auto
    done
qed

lemma homeomorphic_fixpoint_property:
  fixes s :: "'a::euclidean_space set"
    and t :: "'b::euclidean_space set"
  assumes "s homeomorphic t"
  shows "(\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)) \<longleftrightarrow>
    (\<forall>g. continuous_on t g \<and> g ` t \<subseteq> t \<longrightarrow> (\<exists>y\<in>t. g y = y))"
proof -
  obtain r i where
      "\<forall>x\<in>s. i (r x) = x"
      "r ` s = t"
      "continuous_on s r"
      "\<forall>y\<in>t. r (i y) = y"
      "i ` t = s"
      "continuous_on t i"
    using assms
    unfolding homeomorphic_def homeomorphism_def
    by blast
  then show ?thesis
    apply -
    apply rule
    apply (rule_tac[!] allI impI)+
    apply (rule_tac g=g in invertible_fixpoint_property[of t i s r])
    prefer 10
    apply (rule_tac g=f in invertible_fixpoint_property[of s r t i])
    apply auto
    done
qed

lemma retract_fixpoint_property:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    and s :: "'a set"
  assumes "t retract_of s"
    and "\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)"
    and "continuous_on t g"
    and "g ` t \<subseteq> t"
  obtains y where "y \<in> t" and "g y = y"
proof -
  obtain h where "retraction s t h"
    using assms(1) unfolding retract_of_def ..
  then show ?thesis
    unfolding retraction_def
    apply -
    apply (rule invertible_fixpoint_property[OF continuous_on_id _ _ _ _ assms(2), of t h g])
    prefer 7
    apply (rule_tac y = y in that)
    using assms
    apply auto
    done
qed


subsection {* The Brouwer theorem for any set with nonempty interior *}

lemma convex_unit_cube: "convex unit_cube"
  apply (rule is_interval_convex)
  apply (clarsimp simp add: is_interval_def mem_unit_cube)
  apply (drule (1) bspec)+
  apply auto
  done

lemma brouwer_weak:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "compact s"
    and "convex s"
    and "interior s \<noteq> {}"
    and "continuous_on s f"
    and "f ` s \<subseteq> s"
  obtains x where "x \<in> s" and "f x = x"
proof -
  let ?U = "unit_cube :: 'a set"
  have "\<Sum>Basis /\<^sub>R 2 \<in> interior ?U"
  proof (rule interiorI)
    let ?I = "(\<Inter>i\<in>Basis. {x::'a. 0 < x \<bullet> i} \<inter> {x. x \<bullet> i < 1})"
    show "open ?I"
      by (intro open_INT finite_Basis ballI open_Int, auto intro: open_Collect_less)
    show "\<Sum>Basis /\<^sub>R 2 \<in> ?I"
      by simp
    show "?I \<subseteq> unit_cube"
      unfolding unit_cube_def by force
  qed
  then have *: "interior ?U \<noteq> {}" by fast
  have *: "?U homeomorphic s"
    using homeomorphic_convex_compact[OF convex_unit_cube compact_unit_cube * assms(2,1,3)] .
  have "\<forall>f. continuous_on ?U f \<and> f ` ?U \<subseteq> ?U \<longrightarrow>
    (\<exists>x\<in>?U. f x = x)"
    using brouwer_cube by auto
  then show ?thesis
    unfolding homeomorphic_fixpoint_property[OF *]
    apply (erule_tac x=f in allE)
    apply (erule impE)
    defer
    apply (erule bexE)
    apply (rule_tac x=y in that)
    using assms
    apply auto
    done
qed


text {* And in particular for a closed ball. *}

lemma brouwer_ball:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "e > 0"
    and "continuous_on (cball a e) f"
    and "f ` cball a e \<subseteq> cball a e"
  obtains x where "x \<in> cball a e" and "f x = x"
  using brouwer_weak[OF compact_cball convex_cball, of a e f]
  unfolding interior_cball ball_eq_empty
  using assms by auto

text {*Still more general form; could derive this directly without using the
  rather involved @{text "HOMEOMORPHIC_CONVEX_COMPACT"} theorem, just using
  a scaling and translation to put the set inside the unit cube. *}

lemma brouwer:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "compact s"
    and "convex s"
    and "s \<noteq> {}"
    and "continuous_on s f"
    and "f ` s \<subseteq> s"
  obtains x where "x \<in> s" and "f x = x"
proof -
  have "\<exists>e>0. s \<subseteq> cball 0 e"
    using compact_imp_bounded[OF assms(1)]
    unfolding bounded_pos
    apply (erule_tac exE)
    apply (rule_tac x=b in exI)
    apply (auto simp add: dist_norm)
    done
  then obtain e where e: "e > 0" "s \<subseteq> cball 0 e"
    by blast
  have "\<exists>x\<in> cball 0 e. (f \<circ> closest_point s) x = x"
    apply (rule_tac brouwer_ball[OF e(1), of 0 "f \<circ> closest_point s"])
    apply (rule continuous_on_compose )
    apply (rule continuous_on_closest_point[OF assms(2) compact_imp_closed[OF assms(1)] assms(3)])
    apply (rule continuous_on_subset[OF assms(4)])
    apply (insert closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3)])
    defer
    using assms(5)[unfolded subset_eq]
    using e(2)[unfolded subset_eq mem_cball]
    apply (auto simp add: dist_norm)
    done
  then obtain x where x: "x \<in> cball 0 e" "(f \<circ> closest_point s) x = x" ..
  have *: "closest_point s x = x"
    apply (rule closest_point_self)
    apply (rule assms(5)[unfolded subset_eq,THEN bspec[where x="x"], unfolded image_iff])
    apply (rule_tac x="closest_point s x" in bexI)
    using x
    unfolding o_def
    using closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3), of x]
    apply auto
    done
  show thesis
    apply (rule_tac x="closest_point s x" in that)
    unfolding x(2)[unfolded o_def]
    apply (rule closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3)])
    using *
    apply auto
    done
qed

text {*So we get the no-retraction theorem. *}

lemma no_retraction_cball:
  fixes a :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<not> (frontier (cball a e) retract_of (cball a e))"
proof
  case goal1
  have *: "\<And>xa. a - (2 *\<^sub>R a - xa) = - (a - xa)"
    using scaleR_left_distrib[of 1 1 a] by auto
  obtain x where x:
      "x \<in> {x. norm (a - x) = e}"
      "2 *\<^sub>R a - x = x"
    apply (rule retract_fixpoint_property[OF goal1, of "\<lambda>x. scaleR 2 a - x"])
    apply rule
    apply rule
    apply (erule conjE)
    apply (rule brouwer_ball[OF assms])
    apply assumption+
    apply (rule_tac x=x in bexI)
    apply assumption+
    apply (rule continuous_intros)+
    unfolding frontier_cball subset_eq Ball_def image_iff
    apply rule
    apply rule
    apply (erule bexE)
    unfolding dist_norm
    apply (simp add: * norm_minus_commute)
    apply blast
    done
  then have "scaleR 2 a = scaleR 1 x + scaleR 1 x"
    by (auto simp add: algebra_simps)
  then have "a = x"
    unfolding scaleR_left_distrib[symmetric]
    by auto
  then show False
    using x assms by auto
qed

end
