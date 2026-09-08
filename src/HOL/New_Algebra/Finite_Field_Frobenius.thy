section \<open>Frobenius on finite subfields\<close>

theory Finite_Field_Frobenius
  imports Finite_Field_Cardinality Field_Mult_Cyclic Extension_Vector_Space
begin

text \<open>
  A finite subfield is represented here as a carrier set inside an ambient type-class field.
  The existing finite-field cardinality theorem therefore speaks about the characteristic of
  the carrier-set locale, whereas the type-class Freshman's Dream speaks about
  @{term "CHAR('a :: field)"}.  The first lemmas identify those two presentations; the remaining results
  expose Frobenius without introducing a second field representation.
\<close>

definition frobenius_power :: "nat \<Rightarrow> 'a :: monoid_mult \<Rightarrow> 'a"
  where "frobenius_power q x = x ^ q"

context Subfield
begin

interpretation carrier: Field K "(+)" "(*)" 0 1
  by (rule sf_field)

lemma carrier_natmult_eq_of_nat:
  "carrier.natmult n = of_nat n"
  by (induction n) simp_all

lemma carrier_characteristic_eq_CHAR:
  assumes fin: "finite K"
  shows "carrier.characteristic = CHAR('a)"
proof -
  have cpos: "carrier.characteristic > 0"
    using carrier.characteristic_pos[OF fin] by simp
  have cz: "of_nat carrier.characteristic = (0 :: 'a)"
    using carrier.characteristic_pos[OF fin]
    by (simp add: carrier_natmult_eq_of_nat)
  have small_nz: "of_nat n \<noteq> (0 :: 'a)"
    if npos: "n > 0" and nlt: "n < carrier.characteristic" for n
  proof
    assume "of_nat n = (0 :: 'a)"
    then have "carrier.natmult n = 0"
      by (simp add: carrier_natmult_eq_of_nat)
    then have "carrier.characteristic \<le> n"
      by (rule carrier.characteristic_least[OF npos])
    with nlt show False by simp
  qed
  show ?thesis
    by (rule sym, rule CHAR_eq_posI[OF cpos cz small_nz])
qed

theorem finite_subfield_cardinality_char_power:
  assumes fin: "finite K"
  shows "\<exists>n>0. card K = CHAR('a) ^ n"
  using carrier.finite_field_cardinality[OF fin]
  by (simp add: carrier_characteristic_eq_CHAR[OF fin])

lemma finite_subfield_CHAR_prime:
  assumes fin: "finite K"
  shows "prime CHAR('a)"
  using carrier.characteristic_prime[OF fin]
  by (simp add: carrier_characteristic_eq_CHAR[OF fin])

end

lemma frobenius_power_add_char_power:
  fixes x y :: "'a :: field"
  assumes char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
  shows "frobenius_power q (x + y) = frobenius_power q x + frobenius_power q y"
  unfolding frobenius_power_def
  by (rule freshmans_dream'[OF char q])

lemma frobenius_power_mult:
  fixes x y :: "'a :: comm_monoid_mult"
  shows "frobenius_power q (x * y) = frobenius_power q x * frobenius_power q y"
  by (simp add: frobenius_power_def power_mult_distrib)

lemma frobenius_power_one [simp]:
  "frobenius_power q (1 :: 'a :: monoid_mult) = 1"
  by (simp add: frobenius_power_def)

lemma frobenius_power_zero [simp]:
  assumes "q > 0"
  shows "frobenius_power q (0 :: 'a :: semiring_1) = 0"
  using assms by (simp add: frobenius_power_def zero_power)

lemma frobenius_power_uminus_char_power:
  fixes x :: "'a :: field"
  assumes char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
  shows "frobenius_power q (-x) = -(frobenius_power q x)"
proof -
  have qpos: "q > 0"
    using char q prime_gt_0_nat by simp
  have "frobenius_power q (x + -x) =
      frobenius_power q x + frobenius_power q (-x)"
    by (rule frobenius_power_add_char_power[OF char q])
  moreover have "frobenius_power q (x + -x) = 0"
    using qpos by (simp add: frobenius_power_def zero_power)
  ultimately have "frobenius_power q x + frobenius_power q (-x) = 0"
    by simp
  then show ?thesis by (simp only: add_eq_0_iff)
qed

lemma frobenius_power_inj:
  fixes x y :: "'a :: field"
  assumes char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
    and eq: "frobenius_power q x = frobenius_power q y"
  shows "x = y"
proof -
  have qpos: "q > 0"
    using char q prime_gt_0_nat by simp
  have add:
      "frobenius_power q (x + -y) =
        frobenius_power q x + frobenius_power q (-y)"
    by (rule frobenius_power_add_char_power[OF char q])
  have neg: "frobenius_power q (-y) = -(frobenius_power q y)"
    by (rule frobenius_power_uminus_char_power[OF char q])
  have "frobenius_power q (x - y) = frobenius_power q x - frobenius_power q y"
    using add neg by simp
  with eq have "(x - y) ^ q = 0"
    by (simp add: frobenius_power_def)
  with qpos have "x - y = 0"
    by simp
  then show ?thesis by simp
qed

context Subfield
begin

lemma frobenius_power_closed:
  "x \<in> K \<Longrightarrow> frobenius_power q x \<in> K"
  unfolding frobenius_power_def by (rule power_closed)

lemma finite_frobenius_bij_betw:
  assumes fin: "finite K" and char: "prime CHAR('a)" and q: "q = CHAR('a) ^ n"
  shows "bij_betw (frobenius_power q) K K"
proof -
  have maps: "frobenius_power q ` K \<subseteq> K"
    by (auto intro: frobenius_power_closed)
  have inj: "inj_on (frobenius_power q) K"
    using frobenius_power_inj[OF char q] by (auto simp: inj_on_def)
  have image: "frobenius_power q ` K = K"
    by (rule card_subset_eq[OF fin maps]) (simp add: card_image[OF inj])
  show ?thesis
    by (simp add: bij_betw_def inj image)
qed

lemma finite_field_frobenius_identity:
  assumes fin: "finite K" and xK: "x \<in> K"
  shows "frobenius_power (card K) x = x"
proof (cases "x = 0")
  case True
  have "card K > 0"
    using fin zero_closed card_gt_0_iff by blast
  with True show ?thesis by simp
next
  case False
  interpret carrier: Field K "(+)" "(*)" 0 1
    by (rule sf_field)
  interpret G: Group carrier.Fstar "(*)" 1
    by (rule carrier.Group_Fstar)
  have xstar: "x \<in> carrier.Fstar"
    using xK False by simp
  have finstar: "finite carrier.Fstar"
    using fin by (simp add: carrier.Fstar_def)
  have group_power: "G.power x (card carrier.Fstar) = 1"
    by (rule G.power_order_eq_1[OF xstar finstar])
  have carrier_power: "carrier.multiplicative.power x (card carrier.Fstar) = 1"
    using group_power carrier.Fstar_power_eq by simp
  have ambient_power:
      "carrier.multiplicative.power x n = x ^ n" for n
    by (induction n) simp_all
  have cardK_pos: "card K > 0"
    using fin zero_closed card_gt_0_iff by blast
  have cardstar: "card carrier.Fstar = card K - 1"
    using fin False
    by (simp add: carrier.Fstar_def card_Diff_singleton_if)
  have "x ^ (card K - 1) = 1"
    using carrier_power by (simp add: ambient_power cardstar)
  moreover have "card K = Suc (card K - 1)"
    using cardK_pos by simp
  ultimately have "x ^ card K = x"
    by (metis power_Suc mult.right_neutral)
  then show ?thesis by (simp add: frobenius_power_def)
qed

end


end
