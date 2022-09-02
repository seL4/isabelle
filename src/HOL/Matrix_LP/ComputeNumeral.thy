theory ComputeNumeral
imports ComputeHOL ComputeFloat
begin

(* equality for bit strings *)
lemmas biteq = eq_num_simps

(* x < y for bit strings *)
lemmas bitless = less_num_simps

(* x \<le> y for bit strings *)
lemmas bitle = le_num_simps

(* addition for bit strings *)
lemmas bitadd = add_num_simps

(* multiplication for bit strings *)
lemmas bitmul = mult_num_simps

lemmas bitarith = arith_simps

(* Normalization of nat literals *)
lemmas natnorm = one_eq_Numeral1_nat

fun natfac :: "nat \<Rightarrow> nat"
  where "natfac n = (if n = 0 then 1 else n * (natfac (n - 1)))"

lemmas compute_natarith =
  arith_simps rel_simps
  diff_nat_numeral nat_numeral nat_0 nat_neg_numeral
  numeral_One [symmetric]
  numeral_1_eq_Suc_0 [symmetric]
  Suc_numeral natfac.simps

lemmas number_norm = numeral_One[symmetric]

lemmas compute_numberarith =
  arith_simps rel_simps number_norm

lemmas compute_num_conversions =
  of_nat_numeral of_nat_0
  nat_numeral nat_0 nat_neg_numeral
  of_int_numeral of_int_neg_numeral of_int_0

lemmas zpowerarith = power_numeral_even power_numeral_odd zpower_Pls int_pow_1

(* div, mod *)

lemmas compute_div_mod = div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
  one_div_numeral one_mod_numeral minus_one_div_numeral minus_one_mod_numeral
  one_div_minus_numeral one_mod_minus_numeral
  numeral_div_numeral numeral_mod_numeral minus_numeral_div_numeral minus_numeral_mod_numeral
  numeral_div_minus_numeral numeral_mod_minus_numeral
  div_minus_minus mod_minus_minus Euclidean_Division.adjust_div_eq of_bool_eq one_neq_zero
  numeral_neq_zero neg_equal_0_iff_equal arith_simps arith_special divmod_trivial
  divmod_steps divmod_cancel divmod_step_def fst_conv snd_conv numeral_One
  case_prod_beta rel_simps Euclidean_Division.adjust_mod_def div_minus1_right mod_minus1_right
  minus_minus numeral_times_numeral mult_zero_right mult_1_right


(* collecting all the theorems *)

lemma even_0_int: "even (0::int) = True"
  by simp

lemma even_One_int: "even (numeral Num.One :: int) = False"
  by simp

lemma even_Bit0_int: "even (numeral (Num.Bit0 x) :: int) = True"
  by (simp only: even_numeral)

lemma even_Bit1_int: "even (numeral (Num.Bit1 x) :: int) = False"
  by (simp only: odd_numeral)

lemmas compute_even = even_0_int even_One_int even_Bit0_int even_Bit1_int

lemmas compute_numeral = compute_if compute_let compute_pair compute_bool
                         compute_natarith compute_numberarith max_def min_def compute_num_conversions zpowerarith compute_div_mod compute_even

end
