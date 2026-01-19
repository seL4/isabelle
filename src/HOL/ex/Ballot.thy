(*   Title: HOL/ex/Ballot.thy
     Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
     Author: Johannes Hölzl <hoelzl@in.tum.de>
*)

section \<open>Bertrand's Ballot Theorem\<close>

theory Ballot
imports
  Complex_Main
  "HOL-Library.FuncSet"
begin

subsection \<open>Preliminaries\<close>

lemma card_bij':
  assumes "f \<in> A \<rightarrow> B" "\<And>x. x \<in> A \<Longrightarrow> g (f x) = x"
    and "g \<in> B \<rightarrow> A" "\<And>x. x \<in> B \<Longrightarrow> f (g x) = x"
  shows "card A = card B"
  apply (rule bij_betw_same_card)
  apply (rule bij_betwI)
  apply fact+
  done

subsection \<open>Formalization of Problem Statement\<close>

subsubsection \<open>Basic Definitions\<close>

datatype vote = A | B

definition
  "all_countings a b = card {f \<in> {1 .. a + b} \<rightarrow>\<^sub>E {A, B}.
      card {x \<in> {1 .. a + b}. f x = A} = a \<and> card {x \<in> {1 .. a + b}. f x = B} = b}"

definition
  "valid_countings a b =
    card {f\<in>{1..a+b} \<rightarrow>\<^sub>E {A, B}.
      card {x\<in>{1..a+b}. f x = A} = a \<and> card {x\<in>{1..a+b}. f x = B} = b \<and>
      (\<forall>m\<in>{1..a+b}. card {x\<in>{1..m}. f x = A} > card {x\<in>{1..m}. f x = B})}"

subsubsection \<open>Equivalence with Set Cardinality\<close>

lemma Collect_on_transfer:
  assumes "rel_set R X Y"
  shows "rel_fun (rel_fun R (=)) (rel_set R) (\<lambda>P. {x\<in>X. P x}) (\<lambda>P. {y\<in>Y. P y})"
  using assms unfolding rel_fun_def rel_set_def by fast

lemma rel_fun_trans:
  "rel_fun P Q g g' \<Longrightarrow> rel_fun R P f f' \<Longrightarrow> rel_fun R Q (\<lambda>x. g (f x)) (\<lambda>y. g' (f' y))"
  by (auto simp: rel_fun_def)

lemma rel_fun_trans2:
  "rel_fun P1 (rel_fun P2 Q) g g' \<Longrightarrow> rel_fun R P1 f1 f1' \<Longrightarrow> rel_fun R P2 f2 f2' \<Longrightarrow>
    rel_fun R Q (\<lambda>x. g (f1 x) (f2 x)) (\<lambda>y. g' (f1' y) (f2' y))"
  by (auto simp: rel_fun_def) 

lemma rel_fun_trans2':
  "rel_fun R (=) f1 f1' \<Longrightarrow> rel_fun R (=) f2 f2' \<Longrightarrow>
    rel_fun R (=) (\<lambda>x. g (f1 x) (f2 x)) (\<lambda>y. g (f1' y) (f2' y))"
  by (auto simp: rel_fun_def)

lemma rel_fun_const: "rel_fun R (=) (\<lambda>x. a) (\<lambda>y. a)"
  by auto

lemma rel_fun_conj:
  "rel_fun R (=) f f' \<Longrightarrow> rel_fun R (=) g g' \<Longrightarrow> rel_fun R (=) (\<lambda>x. f x \<and> g x) (\<lambda>y. f' y \<and> g' y)"
  by (auto simp: rel_fun_def)

lemma rel_fun_ball:
  "(\<And>i. i \<in> I \<Longrightarrow> rel_fun R (=) (f i) (f' i)) \<Longrightarrow> rel_fun R (=) (\<lambda>x. \<forall>i\<in>I. f i x) (\<lambda>y. \<forall>i\<in>I. f' i y)"
  by (auto simp: rel_fun_def rel_set_def)

lemma
  shows all_countings_set: "all_countings a b = card {V\<in>Pow {0..<a+b}. card V = a}"
      (is "_ = card ?A")
    and valid_countings_set: "valid_countings a b =
      card {V\<in>Pow {0..<a+b}. card V = a \<and> (\<forall>m\<in>{1..a+b}. card ({0..<m} \<inter> V) > m - card ({0..<m} \<inter> V))}"
      (is "_ = card ?V")
proof -
  define P where "P j i \<longleftrightarrow> i < a + b \<and> j = Suc i" for j i
  have unique_P: "bi_unique P" and total_P: "\<And>m. m \<le> a + b \<Longrightarrow> rel_set P {1..m} {0..<m}"
    by (auto simp add: bi_unique_def rel_set_def P_def Suc_le_eq gr0_conv_Suc)
  have rel_fun_P: "\<And>R f g. (\<And>i. i < a+b \<Longrightarrow> R (f  (Suc i)) (g i)) \<Longrightarrow> rel_fun P R f g"
    by (simp add: rel_fun_def P_def)
    
  define R where "R f V \<longleftrightarrow>
    V \<subseteq> {0..<a+b} \<and> f \<in> extensional {1..a+b} \<and> (\<forall>i<a+b. i \<in> V \<longleftrightarrow> f (Suc i) = A)" for f V
  { fix f g :: "nat \<Rightarrow> vote" assume "f \<in> extensional {1..a + b}" "g \<in> extensional {1..a + b}" 
    moreover assume "\<forall>i<a + b. (f (Suc i) = A) = (g (Suc i) = A)"
    then have "\<forall>i<a + b. f (Suc i) = g (Suc i)"
      by (metis vote.nchotomy)
    ultimately have "f i = g i" for i
      by (cases "i \<in> {1..a+b}") (auto simp: extensional_def Suc_le_eq gr0_conv_Suc) }
  then have unique_R: "bi_unique R"
    by (auto simp: bi_unique_def R_def)

  have "f \<in> extensional {1..a + b} \<Longrightarrow> \<exists>V\<in>Pow {0..<a + b}. R f V" for f
    by (intro bexI[of _ "{i. i < a+b \<and> f (Suc i) = A}"]) (auto simp add: R_def PiE_def)
  moreover have "V \<in> Pow {0..<a + b} \<Longrightarrow> \<exists>f\<in>extensional {1..a+b}. R f V" for V
    by (intro bexI[of _ "\<lambda>i\<in>{1..a+b}. if i - 1 \<in> V then A else B"]) (auto simp add: R_def PiE_def)
  ultimately have total_R: "rel_set R (extensional {1..a+b}) (Pow {0..<a+b})"
    by (auto simp: rel_set_def)

  have P: "rel_fun R (rel_fun P (=)) (\<lambda>f x. f x = A) (\<lambda>V y. y \<in> V)"
    by (auto simp: P_def R_def Suc_le_eq gr0_conv_Suc rel_fun_def)

  have eq_B: "x = B \<longleftrightarrow> x \<noteq> A" for x
    by (cases x; simp)

  { fix f and m :: nat
    have "card {x\<in>{1..m}. f x = B} = card ({1..m} - {x\<in>{1..m}. f x = A})"
      by (simp add: eq_B set_diff_eq cong: conj_cong)
    also have "\<dots> = m - card {x\<in>{1..m}. f x = A}"
      by (subst card_Diff_subset) auto
    finally have "card {x\<in>{1..m}. f x = B} = m - card {x\<in>{1..m}. f x = A}" . }
  note card_B = this

  note transfers = rel_fun_const card_transfer[THEN rel_funD, OF unique_R] rel_fun_conj rel_fun_ball
    Collect_on_transfer[THEN rel_funD, OF total_R] Collect_on_transfer[THEN rel_funD, OF total_P]
    rel_fun_trans[OF card_transfer, OF unique_P] rel_fun_trans[OF Collect_on_transfer[OF total_P]]
    rel_fun_trans2'[where g="(=)"] rel_fun_trans2'[where g="(<)"] rel_fun_trans2'[where g="(-)"]

  have "all_countings a b = card {f \<in> extensional {1..a + b}. card {x \<in> {1..a + b}. f x = A} = a}"
    using card_B by (simp add: all_countings_def PiE_iff vote.nchotomy cong: conj_cong)
  also have "\<dots> = card {V\<in>Pow {0..<a+b}. card ({x\<in>{0 ..< a + b}. x \<in> V}) = a}"
    by (intro P order_refl transfers)
  finally show "all_countings a b = card ?A"
    unfolding Int_def[symmetric] by (simp add: Int_absorb1 cong: conj_cong)

  have "valid_countings a b = card {f\<in>extensional {1..a+b}.
      card {x\<in>{1..a+b}. f x = A} = a \<and> (\<forall>m\<in>{1..a+b}. card {x\<in>{1..m}. f x = A} > m - card {x\<in>{1..m}. f x = A})}"
    using card_B by (simp add: valid_countings_def PiE_iff vote.nchotomy cong: conj_cong)
  also have "\<dots> = card {V\<in>Pow {0..<a+b}. card {x\<in>{0..<a+b}. x\<in>V} = a \<and>
    (\<forall>m\<in>{1..a+b}. card {x\<in>{0..<m}. x\<in>V} > m - card {x\<in>{0..<m}. x\<in>V})}"
    by (intro P order_refl transfers) auto
  finally show "valid_countings a b = card ?V"
    unfolding Int_def[symmetric] by (simp add: Int_absorb1 cong: conj_cong)
qed

lemma all_countings [code]: "all_countings a b = (a + b) choose a"
  unfolding all_countings_set by (simp add: n_subsets)

subsection \<open>Facts About \<^term>\<open>valid_countings\<close>\<close>

subsubsection \<open>Non-Recursive Cases\<close>

lemma card_V_eq_a: "V \<subseteq> {0..<a} \<Longrightarrow> card V = a \<longleftrightarrow> V = {0..<a}"
  using card_subset_eq[of "{0..<a}" V] by auto

lemma valid_countings_a_0: "valid_countings a 0 = 1"
  by (simp add: valid_countings_set card_V_eq_a cong: conj_cong)

lemma valid_countings_eq_zero:
  "a \<le> b \<Longrightarrow> 0 < b \<Longrightarrow> valid_countings a b = 0"
  by (auto simp add: valid_countings_set Int_absorb1 intro!: bexI[of _ "a + b"])

lemma Ico_subset_finite: "i \<subseteq> {a ..< b::nat} \<Longrightarrow> finite i"
  by (auto dest: finite_subset)

lemma Icc_Suc2: "a \<le> b \<Longrightarrow> {a..Suc b} = insert (Suc b) {a..b}"
  by auto

lemma Ico_Suc2: "a \<le> b \<Longrightarrow> {a..<Suc b} = insert b {a..<b}"
  by auto

lemma valid_countings_Suc_Suc:
  assumes "b < a"
  shows "valid_countings (Suc a) (Suc b) = valid_countings a (Suc b) + valid_countings (Suc a) b"
proof -
  let ?l = "Suc (a + b)"
  let ?Q = "\<lambda>V c. \<forall>m\<in>{1..c}. m - card ({0..<m} \<inter> V) < card ({0..<m} \<inter> V)"
  let ?V = "\<lambda>P. {V. (V \<in> Pow {0..<Suc ?l} \<and> P V) \<and> card V = Suc a \<and> ?Q V (Suc ?l)}"
  have "valid_countings (Suc a) (Suc b) = card (?V (\<lambda>V. ?l \<notin> V)) + card (?V (\<lambda>V. ?l \<in> V))"
    unfolding valid_countings_set
    by (subst card_Un_disjoint[symmetric]) (auto simp add: set_eq_iff intro!: arg_cong[where f=card])
  also have "card (?V (\<lambda>V. ?l \<in> V)) = valid_countings a (Suc b)"
    unfolding valid_countings_set
  proof (rule card_bij'[where f="\<lambda>V. V - {?l}" and g="insert ?l"])
    have *: "\<And>m V. m \<in> {1..a + Suc b} \<Longrightarrow> {0..<m} \<inter> (V - {?l}) = {0..<m} \<inter> V"
      by auto
    show "(\<lambda>V. V - {?l}) \<in> ?V (\<lambda>V. ?l \<in> V) \<rightarrow> {V \<in> Pow {0..<a + Suc b}. card V = a \<and> ?Q V (a + Suc b)}"
      by (auto simp: Ico_subset_finite *)
    { fix V assume V: "V \<subseteq> {0..<?l}"
      then have "finite V" "?l \<notin> V" "{0..<Suc ?l} \<inter> V = V"
        by (auto dest: finite_subset)
      with V have "card (insert ?l V) = Suc (card V)"
        "card ({0..<m} \<inter> insert ?l V) = (if m = Suc ?l then Suc (card V) else card ({0..<m} \<inter> V))"
        if "m \<le> Suc ?l" for m
        using that by auto }
    then show "insert ?l \<in> {V \<in> Pow {0..<a + Suc b}. card V = a \<and> ?Q V (a + Suc b)} \<rightarrow> ?V (\<lambda>V. ?l \<in> V)"
      using \<open>b < a\<close> by auto
  qed auto
  also have "card (?V (\<lambda>V. ?l \<notin> V)) = valid_countings (Suc a) b"
    unfolding valid_countings_set
  proof (intro arg_cong[where f="\<lambda>P. card {x. P x}"] ext conj_cong)
    fix V assume "V \<in> Pow {0..<Suc a + b}" and [simp]: "card V = Suc a"
    then have [simp]: "V \<subseteq> {0..<Suc ?l}"
      by auto
    show "?Q V (Suc ?l) = ?Q V (Suc a + b)"
      using \<open>b<a\<close> by (simp add: Int_absorb1 Icc_Suc2)
  qed (auto simp: subset_eq less_Suc_eq)
  finally show ?thesis
    by simp
qed

lemma valid_countings:
  "(a + b) * valid_countings a b = (a - b) * ((a + b) choose a)"
proof (induct a arbitrary: b)
  case 0 show ?case
    by (cases b) (simp_all add: valid_countings_eq_zero)
next
  case (Suc a) note Suc_a = this
  show ?case
  proof (induct b)
    case (Suc b) note Suc_b = this
    show ?case
    proof cases
      assume "a \<le> b" then show ?thesis
        by (simp add: valid_countings_eq_zero)
    next
      assume "\<not> a \<le> b"
      then have "b < a" by simp

      have "Suc a * (a - Suc b) + (Suc a - b) * Suc b =
        (Suc a * a - Suc a * Suc b) + (Suc a * Suc b - Suc b * b)"
        by (simp add: algebra_simps)
      also have "\<dots> = (Suc a * a + (Suc a * Suc b - Suc b * b)) - Suc a * Suc b"
        using \<open>b<a\<close> by (intro add_diff_assoc2 mult_mono) auto
      also have "\<dots> = (Suc a * a + Suc a * Suc b) - Suc b * b - Suc a * Suc b"
        using \<open>b<a\<close> by (intro arg_cong2[where f="(-)"] add_diff_assoc mult_mono) auto
      also have "\<dots> = (Suc a * Suc (a + b)) - (Suc b * Suc (a + b))"
        by (simp add: algebra_simps)
      finally have rearrange: "Suc a * (a - Suc b) + (Suc a - b) * Suc b = (Suc a - Suc b) * Suc (a + b)"
        unfolding diff_mult_distrib by simp

      have "(Suc a * Suc (a + b)) * ((Suc a + Suc b) * valid_countings (Suc a) (Suc b)) =
        (Suc a + Suc b) * Suc a * ((a + Suc b) * valid_countings a (Suc b) + (Suc a + b) * valid_countings (Suc a) b)"
        unfolding valid_countings_Suc_Suc[OF \<open>b < a\<close>] by (simp add: field_simps)
      also have "... = (Suc a + Suc b) * ((a - Suc b) * (Suc a * (Suc (a + b) choose a)) +
        (Suc a - b) * (Suc a * (Suc (a + b) choose Suc a)))"
        unfolding Suc_a Suc_b by (simp add: field_simps)
      also have "... = (Suc a * (a - Suc b) + (Suc a - b) * Suc b) * (Suc (Suc a + b) * (Suc a + b choose a))"
        unfolding Suc_times_binomial_add by (simp add: field_simps)
      also have "... = Suc a * (Suc a * (a - Suc b) + (Suc a - b) * Suc b) * (Suc a + Suc b choose Suc a)"
        unfolding Suc_times_binomial_eq by (simp add: field_simps)
      also have "... = (Suc a * Suc (a + b)) * ((Suc a - Suc b) * (Suc a + Suc b choose Suc a))"
        unfolding rearrange by (simp only: mult_ac)
      finally show ?thesis
        unfolding mult_cancel1 by simp
    qed
  qed (simp add: valid_countings_a_0)
qed

lemma valid_countings_eq[code]:
  "valid_countings a b = (if a + b = 0 then 1 else ((a - b) * ((a + b) choose a)) div (a + b))"
  by (simp add: valid_countings[symmetric] valid_countings_a_0)

subsection \<open>Relation Between \<^term>\<open>valid_countings\<close> and \<^term>\<open>all_countings\<close>\<close>

lemma main_nat: "(a + b) * valid_countings a b = (a - b) * all_countings a b"
  unfolding valid_countings all_countings ..

lemma main_real:
  assumes "b < a"
  shows "valid_countings a b = (a - b) / (a + b) * all_countings a b"
using assms
proof -
  from main_nat[of a b] \<open>b < a\<close> have
    "(real a + real b) * real (valid_countings a b) = (real a - real b) * real (all_countings a b)"
    by (simp only: of_nat_add[symmetric] of_nat_mult[symmetric]) auto
  from this \<open>b < a\<close> show ?thesis
    by (subst mult_left_cancel[of "real a + real b", symmetric]) auto
qed

lemma
  "valid_countings a b = (if a \<le> b then (if b = 0 then 1 else 0) else (a - b) / (a + b) * all_countings a b)"
proof (cases "a \<le> b")
  case False
    from this show ?thesis by (simp add: main_real)
next
  case True
    from this show ?thesis
      by (auto simp add: valid_countings_a_0 all_countings valid_countings_eq_zero)
qed

subsubsection \<open>Executable Definition\<close>

value "all_countings 1 0"
value "all_countings 0 1"
value "all_countings 1 1"
value "all_countings 2 1"
value "all_countings 1 2"
value "all_countings 2 4"
value "all_countings 4 2"

subsubsection \<open>Executable Definition\<close>

value "valid_countings 1 0"
value "valid_countings 0 1"
value "valid_countings 1 1"
value "valid_countings 2 1"
value "valid_countings 1 2"
value "valid_countings 2 4"
value "valid_countings 4 2"

end
