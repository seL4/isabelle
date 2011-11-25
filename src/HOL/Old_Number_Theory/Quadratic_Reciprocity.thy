(*  Title:      HOL/Old_Number_Theory/Quadratic_Reciprocity.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {* The law of Quadratic reciprocity *}

theory Quadratic_Reciprocity
imports Gauss
begin

text {*
  Lemmas leading up to the proof of theorem 3.3 in Niven and
  Zuckerman's presentation.
*}

context GAUSS
begin

lemma QRLemma1: "a * setsum id A =
  p * setsum (%x. ((x * a) div p)) A + setsum id D + setsum id E"
proof -
  from finite_A have "a * setsum id A = setsum (%x. a * x) A"
    by (auto simp add: setsum_const_mult id_def)
  also have "setsum (%x. a * x) = setsum (%x. x * a)"
    by (auto simp add: mult_commute)
  also have "setsum (%x. x * a) A = setsum id B"
    by (simp add: B_def setsum_reindex_id[OF inj_on_xa_A])
  also have "... = setsum (%x. p * (x div p) + StandardRes p x) B"
    by (auto simp add: StandardRes_def zmod_zdiv_equality)
  also have "... = setsum (%x. p * (x div p)) B + setsum (StandardRes p) B"
    by (rule setsum_addf)
  also have "setsum (StandardRes p) B = setsum id C"
    by (auto simp add: C_def setsum_reindex_id[OF SR_B_inj])
  also from C_eq have "... = setsum id (D \<union> E)"
    by auto
  also from finite_D finite_E have "... = setsum id D + setsum id E"
    by (rule setsum_Un_disjoint) (auto simp add: D_def E_def)
  also have "setsum (%x. p * (x div p)) B =
      setsum ((%x. p * (x div p)) o (%x. (x * a))) A"
    by (auto simp add: B_def setsum_reindex inj_on_xa_A)
  also have "... = setsum (%x. p * ((x * a) div p)) A"
    by (auto simp add: o_def)
  also from finite_A have "setsum (%x. p * ((x * a) div p)) A =
    p * setsum (%x. ((x * a) div p)) A"
    by (auto simp add: setsum_const_mult)
  finally show ?thesis by arith
qed

lemma QRLemma2: "setsum id A = p * int (card E) - setsum id E +
  setsum id D"
proof -
  from F_Un_D_eq_A have "setsum id A = setsum id (D \<union> F)"
    by (simp add: Un_commute)
  also from F_D_disj finite_D finite_F
  have "... = setsum id D + setsum id F"
    by (auto simp add: Int_commute intro: setsum_Un_disjoint)
  also from F_def have "F = (%x. (p - x)) ` E"
    by auto
  also from finite_E inj_on_pminusx_E have "setsum id ((%x. (p - x)) ` E) =
      setsum (%x. (p - x)) E"
    by (auto simp add: setsum_reindex)
  also from finite_E have "setsum (op - p) E = setsum (%x. p) E - setsum id E"
    by (auto simp add: setsum_subtractf id_def)
  also from finite_E have "setsum (%x. p) E = p * int(card E)"
    by (intro setsum_const)
  finally show ?thesis
    by arith
qed

lemma QRLemma3: "(a - 1) * setsum id A =
    p * (setsum (%x. ((x * a) div p)) A - int(card E)) + 2 * setsum id E"
proof -
  have "(a - 1) * setsum id A = a * setsum id A - setsum id A"
    by (auto simp add: left_diff_distrib)
  also note QRLemma1
  also from QRLemma2 have "p * (\<Sum>x \<in> A. x * a div p) + setsum id D +
     setsum id E - setsum id A =
      p * (\<Sum>x \<in> A. x * a div p) + setsum id D +
      setsum id E - (p * int (card E) - setsum id E + setsum id D)"
    by auto
  also have "... = p * (\<Sum>x \<in> A. x * a div p) -
      p * int (card E) + 2 * setsum id E"
    by arith
  finally show ?thesis
    by (auto simp only: right_diff_distrib)
qed

lemma QRLemma4: "a \<in> zOdd ==>
    (setsum (%x. ((x * a) div p)) A \<in> zEven) = (int(card E): zEven)"
proof -
  assume a_odd: "a \<in> zOdd"
  from QRLemma3 have a: "p * (setsum (%x. ((x * a) div p)) A - int(card E)) =
      (a - 1) * setsum id A - 2 * setsum id E"
    by arith
  from a_odd have "a - 1 \<in> zEven"
    by (rule odd_minus_one_even)
  hence "(a - 1) * setsum id A \<in> zEven"
    by (rule even_times_either)
  moreover have "2 * setsum id E \<in> zEven"
    by (auto simp add: zEven_def)
  ultimately have "(a - 1) * setsum id A - 2 * setsum id E \<in> zEven"
    by (rule even_minus_even)
  with a have "p * (setsum (%x. ((x * a) div p)) A - int(card E)): zEven"
    by simp
  hence "p \<in> zEven | (setsum (%x. ((x * a) div p)) A - int(card E)): zEven"
    by (rule EvenOdd.even_product)
  with p_odd have "(setsum (%x. ((x * a) div p)) A - int(card E)): zEven"
    by (auto simp add: odd_iff_not_even)
  thus ?thesis
    by (auto simp only: even_diff [symmetric])
qed

lemma QRLemma5: "a \<in> zOdd ==>
   (-1::int)^(card E) = (-1::int)^(nat(setsum (%x. ((x * a) div p)) A))"
proof -
  assume "a \<in> zOdd"
  from QRLemma4 [OF this] have
    "(int(card E): zEven) = (setsum (%x. ((x * a) div p)) A \<in> zEven)" ..
  moreover have "0 \<le> int(card E)"
    by auto
  moreover have "0 \<le> setsum (%x. ((x * a) div p)) A"
    proof (intro setsum_nonneg)
      show "\<forall>x \<in> A. 0 \<le> x * a div p"
      proof
        fix x
        assume "x \<in> A"
        then have "0 \<le> x"
          by (auto simp add: A_def)
        with a_nonzero have "0 \<le> x * a"
          by (auto simp add: zero_le_mult_iff)
        with p_g_2 show "0 \<le> x * a div p"
          by (auto simp add: pos_imp_zdiv_nonneg_iff)
      qed
    qed
  ultimately have "(-1::int)^nat((int (card E))) =
      (-1)^nat(((\<Sum>x \<in> A. x * a div p)))"
    by (intro neg_one_power_parity, auto)
  also have "nat (int(card E)) = card E"
    by auto
  finally show ?thesis .
qed

end

lemma MainQRLemma: "[| a \<in> zOdd; 0 < a; ~([a = 0] (mod p)); zprime p; 2 < p;
  A = {x. 0 < x & x \<le> (p - 1) div 2} |] ==>
  (Legendre a p) = (-1::int)^(nat(setsum (%x. ((x * a) div p)) A))"
  apply (subst GAUSS.gauss_lemma)
  apply (auto simp add: GAUSS_def)
  apply (subst GAUSS.QRLemma5)
  apply (auto simp add: GAUSS_def)
  apply (simp add: GAUSS.A_def [OF GAUSS.intro] GAUSS_def)
  done


subsection {* Stuff about S, S1 and S2 *}

locale QRTEMP =
  fixes p     :: "int"
  fixes q     :: "int"

  assumes p_prime: "zprime p"
  assumes p_g_2: "2 < p"
  assumes q_prime: "zprime q"
  assumes q_g_2: "2 < q"
  assumes p_neq_q:      "p \<noteq> q"
begin

definition P_set :: "int set"
  where "P_set = {x. 0 < x & x \<le> ((p - 1) div 2) }"

definition Q_set :: "int set"
  where "Q_set = {x. 0 < x & x \<le> ((q - 1) div 2) }"
  
definition S :: "(int * int) set"
  where "S = P_set <*> Q_set"

definition S1 :: "(int * int) set"
  where "S1 = { (x, y). (x, y):S & ((p * y) < (q * x)) }"

definition S2 :: "(int * int) set"
  where "S2 = { (x, y). (x, y):S & ((q * x) < (p * y)) }"

definition f1 :: "int => (int * int) set"
  where "f1 j = { (j1, y). (j1, y):S & j1 = j & (y \<le> (q * j) div p) }"

definition f2 :: "int => (int * int) set"
  where "f2 j = { (x, j1). (x, j1):S & j1 = j & (x \<le> (p * j) div q) }"

lemma p_fact: "0 < (p - 1) div 2"
proof -
  from p_g_2 have "2 \<le> p - 1" by arith
  then have "2 div 2 \<le> (p - 1) div 2" by (rule zdiv_mono1, auto)
  then show ?thesis by auto
qed

lemma q_fact: "0 < (q - 1) div 2"
proof -
  from q_g_2 have "2 \<le> q - 1" by arith
  then have "2 div 2 \<le> (q - 1) div 2" by (rule zdiv_mono1, auto)
  then show ?thesis by auto
qed

lemma pb_neq_qa:
  assumes "1 \<le> b" and "b \<le> (q - 1) div 2"
  shows "p * b \<noteq> q * a"
proof
  assume "p * b = q * a"
  then have "q dvd (p * b)" by (auto simp add: dvd_def)
  with q_prime p_g_2 have "q dvd p | q dvd b"
    by (auto simp add: zprime_zdvd_zmult)
  moreover have "~ (q dvd p)"
  proof
    assume "q dvd p"
    with p_prime have "q = 1 | q = p"
      apply (auto simp add: zprime_def QRTEMP_def)
      apply (drule_tac x = q and R = False in allE)
      apply (simp add: QRTEMP_def)
      apply (subgoal_tac "0 \<le> q", simp add: QRTEMP_def)
      apply (insert assms)
      apply (auto simp add: QRTEMP_def)
      done
    with q_g_2 p_neq_q show False by auto
  qed
  ultimately have "q dvd b" by auto
  then have "q \<le> b"
  proof -
    assume "q dvd b"
    moreover from assms have "0 < b" by auto
    ultimately show ?thesis using zdvd_bounds [of q b] by auto
  qed
  with assms have "q \<le> (q - 1) div 2" by auto
  then have "2 * q \<le> 2 * ((q - 1) div 2)" by arith
  then have "2 * q \<le> q - 1"
  proof -
    assume a: "2 * q \<le> 2 * ((q - 1) div 2)"
    with assms have "q \<in> zOdd" by (auto simp add: QRTEMP_def zprime_zOdd_eq_grt_2)
    with odd_minus_one_even have "(q - 1):zEven" by auto
    with even_div_2_prop2 have "(q - 1) = 2 * ((q - 1) div 2)" by auto
    with a show ?thesis by auto
  qed
  then have p1: "q \<le> -1" by arith
  with q_g_2 show False by auto
qed

lemma P_set_finite: "finite (P_set)"
  using p_fact by (auto simp add: P_set_def bdd_int_set_l_le_finite)

lemma Q_set_finite: "finite (Q_set)"
  using q_fact by (auto simp add: Q_set_def bdd_int_set_l_le_finite)

lemma S_finite: "finite S"
  by (auto simp add: S_def  P_set_finite Q_set_finite finite_cartesian_product)

lemma S1_finite: "finite S1"
proof -
  have "finite S" by (auto simp add: S_finite)
  moreover have "S1 \<subseteq> S" by (auto simp add: S1_def S_def)
  ultimately show ?thesis by (auto simp add: finite_subset)
qed

lemma S2_finite: "finite S2"
proof -
  have "finite S" by (auto simp add: S_finite)
  moreover have "S2 \<subseteq> S" by (auto simp add: S2_def S_def)
  ultimately show ?thesis by (auto simp add: finite_subset)
qed

lemma P_set_card: "(p - 1) div 2 = int (card (P_set))"
  using p_fact by (auto simp add: P_set_def card_bdd_int_set_l_le)

lemma Q_set_card: "(q - 1) div 2 = int (card (Q_set))"
  using q_fact by (auto simp add: Q_set_def card_bdd_int_set_l_le)

lemma S_card: "((p - 1) div 2) * ((q - 1) div 2) = int (card(S))"
  using P_set_card Q_set_card P_set_finite Q_set_finite
  by (auto simp add: S_def zmult_int)

lemma S1_Int_S2_prop: "S1 \<inter> S2 = {}"
  by (auto simp add: S1_def S2_def)

lemma S1_Union_S2_prop: "S = S1 \<union> S2"
  apply (auto simp add: S_def P_set_def Q_set_def S1_def S2_def)
proof -
  fix a and b
  assume "~ q * a < p * b" and b1: "0 < b" and b2: "b \<le> (q - 1) div 2"
  with less_linear have "(p * b < q * a) | (p * b = q * a)" by auto
  moreover from pb_neq_qa b1 b2 have "(p * b \<noteq> q * a)" by auto
  ultimately show "p * b < q * a" by auto
qed

lemma card_sum_S1_S2: "((p - 1) div 2) * ((q - 1) div 2) =
    int(card(S1)) + int(card(S2))"
proof -
  have "((p - 1) div 2) * ((q - 1) div 2) = int (card(S))"
    by (auto simp add: S_card)
  also have "... = int( card(S1) + card(S2))"
    apply (insert S1_finite S2_finite S1_Int_S2_prop S1_Union_S2_prop)
    apply (drule card_Un_disjoint, auto)
    done
  also have "... = int(card(S1)) + int(card(S2))" by auto
  finally show ?thesis .
qed

lemma aux1a:
  assumes "0 < a" and "a \<le> (p - 1) div 2"
    and "0 < b" and "b \<le> (q - 1) div 2"
  shows "(p * b < q * a) = (b \<le> q * a div p)"
proof -
  have "p * b < q * a ==> b \<le> q * a div p"
  proof -
    assume "p * b < q * a"
    then have "p * b \<le> q * a" by auto
    then have "(p * b) div p \<le> (q * a) div p"
      by (rule zdiv_mono1) (insert p_g_2, auto)
    then show "b \<le> (q * a) div p"
      apply (subgoal_tac "p \<noteq> 0")
      apply (frule div_mult_self1_is_id, force)
      apply (insert p_g_2, auto)
      done
  qed
  moreover have "b \<le> q * a div p ==> p * b < q * a"
  proof -
    assume "b \<le> q * a div p"
    then have "p * b \<le> p * ((q * a) div p)"
      using p_g_2 by (auto simp add: mult_le_cancel_left)
    also have "... \<le> q * a"
      by (rule zdiv_leq_prop) (insert p_g_2, auto)
    finally have "p * b \<le> q * a" .
    then have "p * b < q * a | p * b = q * a"
      by (simp only: order_le_imp_less_or_eq)
    moreover have "p * b \<noteq> q * a"
      by (rule pb_neq_qa) (insert assms, auto)
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis ..
qed

lemma aux1b:
  assumes "0 < a" and "a \<le> (p - 1) div 2"
    and "0 < b" and "b \<le> (q - 1) div 2"
  shows "(q * a < p * b) = (a \<le> p * b div q)"
proof -
  have "q * a < p * b ==> a \<le> p * b div q"
  proof -
    assume "q * a < p * b"
    then have "q * a \<le> p * b" by auto
    then have "(q * a) div q \<le> (p * b) div q"
      by (rule zdiv_mono1) (insert q_g_2, auto)
    then show "a \<le> (p * b) div q"
      apply (subgoal_tac "q \<noteq> 0")
      apply (frule div_mult_self1_is_id, force)
      apply (insert q_g_2, auto)
      done
  qed
  moreover have "a \<le> p * b div q ==> q * a < p * b"
  proof -
    assume "a \<le> p * b div q"
    then have "q * a \<le> q * ((p * b) div q)"
      using q_g_2 by (auto simp add: mult_le_cancel_left)
    also have "... \<le> p * b"
      by (rule zdiv_leq_prop) (insert q_g_2, auto)
    finally have "q * a \<le> p * b" .
    then have "q * a < p * b | q * a = p * b"
      by (simp only: order_le_imp_less_or_eq)
    moreover have "p * b \<noteq> q * a"
      by (rule  pb_neq_qa) (insert assms, auto)
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis ..
qed

lemma (in -) aux2:
  assumes "zprime p" and "zprime q" and "2 < p" and "2 < q"
  shows "(q * ((p - 1) div 2)) div p \<le> (q - 1) div 2"
proof-
  (* Set up what's even and odd *)
  from assms have "p \<in> zOdd & q \<in> zOdd"
    by (auto simp add:  zprime_zOdd_eq_grt_2)
  then have even1: "(p - 1):zEven & (q - 1):zEven"
    by (auto simp add: odd_minus_one_even)
  then have even2: "(2 * p):zEven & ((q - 1) * p):zEven"
    by (auto simp add: zEven_def)
  then have even3: "(((q - 1) * p) + (2 * p)):zEven"
    by (auto simp: EvenOdd.even_plus_even)
  (* using these prove it *)
  from assms have "q * (p - 1) < ((q - 1) * p) + (2 * p)"
    by (auto simp add: int_distrib)
  then have "((p - 1) * q) div 2 < (((q - 1) * p) + (2 * p)) div 2"
    apply (rule_tac x = "((p - 1) * q)" in even_div_2_l)
    by (auto simp add: even3, auto simp add: mult_ac)
  also have "((p - 1) * q) div 2 = q * ((p - 1) div 2)"
    by (auto simp add: even1 even_prod_div_2)
  also have "(((q - 1) * p) + (2 * p)) div 2 = (((q - 1) div 2) * p) + p"
    by (auto simp add: even1 even2 even_prod_div_2 even_sum_div_2)
  finally show ?thesis
    apply (rule_tac x = " q * ((p - 1) div 2)" and
                    y = "(q - 1) div 2" in div_prop2)
    using assms by auto
qed

lemma aux3a: "\<forall>j \<in> P_set. int (card (f1 j)) = (q * j) div p"
proof
  fix j
  assume j_fact: "j \<in> P_set"
  have "int (card (f1 j)) = int (card {y. y \<in> Q_set & y \<le> (q * j) div p})"
  proof -
    have "finite (f1 j)"
    proof -
      have "(f1 j) \<subseteq> S" by (auto simp add: f1_def)
      with S_finite show ?thesis by (auto simp add: finite_subset)
    qed
    moreover have "inj_on (%(x,y). y) (f1 j)"
      by (auto simp add: f1_def inj_on_def)
    ultimately have "card ((%(x,y). y) ` (f1 j)) = card  (f1 j)"
      by (auto simp add: f1_def card_image)
    moreover have "((%(x,y). y) ` (f1 j)) = {y. y \<in> Q_set & y \<le> (q * j) div p}"
      using j_fact by (auto simp add: f1_def S_def Q_set_def P_set_def image_def)
    ultimately show ?thesis by (auto simp add: f1_def)
  qed
  also have "... = int (card {y. 0 < y & y \<le> (q * j) div p})"
  proof -
    have "{y. y \<in> Q_set & y \<le> (q * j) div p} =
        {y. 0 < y & y \<le> (q * j) div p}"
      apply (auto simp add: Q_set_def)
    proof -
      fix x
      assume x: "0 < x" "x \<le> q * j div p"
      with j_fact P_set_def  have "j \<le> (p - 1) div 2" by auto
      with q_g_2 have "q * j \<le> q * ((p - 1) div 2)"
        by (auto simp add: mult_le_cancel_left)
      with p_g_2 have "q * j div p \<le> q * ((p - 1) div 2) div p"
        by (auto simp add: zdiv_mono1)
      also from QRTEMP_axioms j_fact P_set_def have "... \<le> (q - 1) div 2"
        apply simp
        apply (insert aux2)
        apply (simp add: QRTEMP_def)
        done
      finally show "x \<le> (q - 1) div 2" using x by auto
    qed
    then show ?thesis by auto
  qed
  also have "... = (q * j) div p"
  proof -
    from j_fact P_set_def have "0 \<le> j" by auto
    with q_g_2 have "q * 0 \<le> q * j" by (auto simp only: mult_left_mono)
    then have "0 \<le> q * j" by auto
    then have "0 div p \<le> (q * j) div p"
      apply (rule_tac a = 0 in zdiv_mono1)
      apply (insert p_g_2, auto)
      done
    also have "0 div p = 0" by auto
    finally show ?thesis by (auto simp add: card_bdd_int_set_l_le)
  qed
  finally show "int (card (f1 j)) = q * j div p" .
qed

lemma aux3b: "\<forall>j \<in> Q_set. int (card (f2 j)) = (p * j) div q"
proof
  fix j
  assume j_fact: "j \<in> Q_set"
  have "int (card (f2 j)) = int (card {y. y \<in> P_set & y \<le> (p * j) div q})"
  proof -
    have "finite (f2 j)"
    proof -
      have "(f2 j) \<subseteq> S" by (auto simp add: f2_def)
      with S_finite show ?thesis by (auto simp add: finite_subset)
    qed
    moreover have "inj_on (%(x,y). x) (f2 j)"
      by (auto simp add: f2_def inj_on_def)
    ultimately have "card ((%(x,y). x) ` (f2 j)) = card  (f2 j)"
      by (auto simp add: f2_def card_image)
    moreover have "((%(x,y). x) ` (f2 j)) = {y. y \<in> P_set & y \<le> (p * j) div q}"
      using j_fact by (auto simp add: f2_def S_def Q_set_def P_set_def image_def)
    ultimately show ?thesis by (auto simp add: f2_def)
  qed
  also have "... = int (card {y. 0 < y & y \<le> (p * j) div q})"
  proof -
    have "{y. y \<in> P_set & y \<le> (p * j) div q} =
        {y. 0 < y & y \<le> (p * j) div q}"
      apply (auto simp add: P_set_def)
    proof -
      fix x
      assume x: "0 < x" "x \<le> p * j div q"
      with j_fact Q_set_def  have "j \<le> (q - 1) div 2" by auto
      with p_g_2 have "p * j \<le> p * ((q - 1) div 2)"
        by (auto simp add: mult_le_cancel_left)
      with q_g_2 have "p * j div q \<le> p * ((q - 1) div 2) div q"
        by (auto simp add: zdiv_mono1)
      also from QRTEMP_axioms j_fact have "... \<le> (p - 1) div 2"
        by (auto simp add: aux2 QRTEMP_def)
      finally show "x \<le> (p - 1) div 2" using x by auto
      qed
    then show ?thesis by auto
  qed
  also have "... = (p * j) div q"
  proof -
    from j_fact Q_set_def have "0 \<le> j" by auto
    with p_g_2 have "p * 0 \<le> p * j" by (auto simp only: mult_left_mono)
    then have "0 \<le> p * j" by auto
    then have "0 div q \<le> (p * j) div q"
      apply (rule_tac a = 0 in zdiv_mono1)
      apply (insert q_g_2, auto)
      done
    also have "0 div q = 0" by auto
    finally show ?thesis by (auto simp add: card_bdd_int_set_l_le)
  qed
  finally show "int (card (f2 j)) = p * j div q" .
qed

lemma S1_card: "int (card(S1)) = setsum (%j. (q * j) div p) P_set"
proof -
  have "\<forall>x \<in> P_set. finite (f1 x)"
  proof
    fix x
    have "f1 x \<subseteq> S" by (auto simp add: f1_def)
    with S_finite show "finite (f1 x)" by (auto simp add: finite_subset)
  qed
  moreover have "(\<forall>x \<in> P_set. \<forall>y \<in> P_set. x \<noteq> y --> (f1 x) \<inter> (f1 y) = {})"
    by (auto simp add: f1_def)
  moreover note P_set_finite
  ultimately have "int(card (UNION P_set f1)) =
      setsum (%x. int(card (f1 x))) P_set"
    by(simp add:card_UN_disjoint int_setsum o_def)
  moreover have "S1 = UNION P_set f1"
    by (auto simp add: f1_def S_def S1_def S2_def P_set_def Q_set_def aux1a)
  ultimately have "int(card (S1)) = setsum (%j. int(card (f1 j))) P_set"
    by auto
  also have "... = setsum (%j. q * j div p) P_set"
    using aux3a by(fastforce intro: setsum_cong)
  finally show ?thesis .
qed

lemma S2_card: "int (card(S2)) = setsum (%j. (p * j) div q) Q_set"
proof -
  have "\<forall>x \<in> Q_set. finite (f2 x)"
  proof
    fix x
    have "f2 x \<subseteq> S" by (auto simp add: f2_def)
    with S_finite show "finite (f2 x)" by (auto simp add: finite_subset)
  qed
  moreover have "(\<forall>x \<in> Q_set. \<forall>y \<in> Q_set. x \<noteq> y -->
      (f2 x) \<inter> (f2 y) = {})"
    by (auto simp add: f2_def)
  moreover note Q_set_finite
  ultimately have "int(card (UNION Q_set f2)) =
      setsum (%x. int(card (f2 x))) Q_set"
    by(simp add:card_UN_disjoint int_setsum o_def)
  moreover have "S2 = UNION Q_set f2"
    by (auto simp add: f2_def S_def S1_def S2_def P_set_def Q_set_def aux1b)
  ultimately have "int(card (S2)) = setsum (%j. int(card (f2 j))) Q_set"
    by auto
  also have "... = setsum (%j. p * j div q) Q_set"
    using aux3b by(fastforce intro: setsum_cong)
  finally show ?thesis .
qed

lemma S1_carda: "int (card(S1)) =
    setsum (%j. (j * q) div p) P_set"
  by (auto simp add: S1_card mult_ac)

lemma S2_carda: "int (card(S2)) =
    setsum (%j. (j * p) div q) Q_set"
  by (auto simp add: S2_card mult_ac)

lemma pq_sum_prop: "(setsum (%j. (j * p) div q) Q_set) +
    (setsum (%j. (j * q) div p) P_set) = ((p - 1) div 2) * ((q - 1) div 2)"
proof -
  have "(setsum (%j. (j * p) div q) Q_set) +
      (setsum (%j. (j * q) div p) P_set) = int (card S2) + int (card S1)"
    by (auto simp add: S1_carda S2_carda)
  also have "... = int (card S1) + int (card S2)"
    by auto
  also have "... = ((p - 1) div 2) * ((q - 1) div 2)"
    by (auto simp add: card_sum_S1_S2)
  finally show ?thesis .
qed


lemma (in -) pq_prime_neq: "[| zprime p; zprime q; p \<noteq> q |] ==> (~[p = 0] (mod q))"
  apply (auto simp add: zcong_eq_zdvd_prop zprime_def)
  apply (drule_tac x = q in allE)
  apply (drule_tac x = p in allE)
  apply auto
  done


lemma QR_short: "(Legendre p q) * (Legendre q p) =
    (-1::int)^nat(((p - 1) div 2)*((q - 1) div 2))"
proof -
  from QRTEMP_axioms have "~([p = 0] (mod q))"
    by (auto simp add: pq_prime_neq QRTEMP_def)
  with QRTEMP_axioms Q_set_def have a1: "(Legendre p q) = (-1::int) ^
      nat(setsum (%x. ((x * p) div q)) Q_set)"
    apply (rule_tac p = q in  MainQRLemma)
    apply (auto simp add: zprime_zOdd_eq_grt_2 QRTEMP_def)
    done
  from QRTEMP_axioms have "~([q = 0] (mod p))"
    apply (rule_tac p = q and q = p in pq_prime_neq)
    apply (simp add: QRTEMP_def)+
    done
  with QRTEMP_axioms P_set_def have a2: "(Legendre q p) =
      (-1::int) ^ nat(setsum (%x. ((x * q) div p)) P_set)"
    apply (rule_tac p = p in  MainQRLemma)
    apply (auto simp add: zprime_zOdd_eq_grt_2 QRTEMP_def)
    done
  from a1 a2 have "(Legendre p q) * (Legendre q p) =
      (-1::int) ^ nat(setsum (%x. ((x * p) div q)) Q_set) *
        (-1::int) ^ nat(setsum (%x. ((x * q) div p)) P_set)"
    by auto
  also have "... = (-1::int) ^ (nat(setsum (%x. ((x * p) div q)) Q_set) +
                   nat(setsum (%x. ((x * q) div p)) P_set))"
    by (auto simp add: power_add)
  also have "nat(setsum (%x. ((x * p) div q)) Q_set) +
      nat(setsum (%x. ((x * q) div p)) P_set) =
        nat((setsum (%x. ((x * p) div q)) Q_set) +
          (setsum (%x. ((x * q) div p)) P_set))"
    apply (rule_tac z = "setsum (%x. ((x * p) div q)) Q_set" in
      nat_add_distrib [symmetric])
    apply (auto simp add: S1_carda [symmetric] S2_carda [symmetric])
    done
  also have "... = nat(((p - 1) div 2) * ((q - 1) div 2))"
    by (auto simp add: pq_sum_prop)
  finally show ?thesis .
qed

end

theorem Quadratic_Reciprocity:
     "[| p \<in> zOdd; zprime p; q \<in> zOdd; zprime q;
         p \<noteq> q |]
      ==> (Legendre p q) * (Legendre q p) =
          (-1::int)^nat(((p - 1) div 2)*((q - 1) div 2))"
  by (auto simp add: QRTEMP.QR_short zprime_zOdd_eq_grt_2 [symmetric]
                     QRTEMP_def)

end
