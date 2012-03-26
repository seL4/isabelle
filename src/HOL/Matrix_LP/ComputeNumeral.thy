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
  numeral_1_eq_1 [symmetric]
  numeral_1_eq_Suc_0 [symmetric]
  Suc_numeral natfac.simps

lemmas number_norm = numeral_1_eq_1[symmetric]

lemmas compute_numberarith =
  arith_simps rel_simps number_norm

lemmas compute_num_conversions =
  real_of_nat_numeral real_of_nat_zero
  nat_numeral nat_0 nat_neg_numeral
  real_numeral real_of_int_zero

lemmas zpowerarith = zpower_numeral_even zpower_numeral_odd zpower_Pls int_pow_1

(* div, mod *)

lemma adjust: "adjust b (q, r) = (if 0 \<le> r - b then (2 * q + 1, r - b) else (2 * q, r))"
  by (auto simp only: adjust_def)

lemma divmod: "divmod_int a b = (if 0\<le>a then
                  if 0\<le>b then posDivAlg a b
                  else if a=0 then (0, 0)
                       else apsnd uminus (negDivAlg (-a) (-b))
               else 
                  if 0<b then negDivAlg a b
                  else apsnd uminus (posDivAlg (-a) (-b)))"
  by (auto simp only: divmod_int_def)

lemmas compute_div_mod = div_int_def mod_int_def divmod adjust apsnd_def map_pair_def posDivAlg.simps negDivAlg.simps



(* collecting all the theorems *)

lemma even_0_int: "even (0::int) = True"
  by simp

lemma even_One_int: "even (numeral Num.One :: int) = False"
  by simp

lemma even_Bit0_int: "even (numeral (Num.Bit0 x) :: int) = True"
  by simp

lemma even_Bit1_int: "even (numeral (Num.Bit1 x) :: int) = False"
  by simp

lemmas compute_even = even_0_int even_One_int even_Bit0_int even_Bit1_int

lemmas compute_numeral = compute_if compute_let compute_pair compute_bool 
                         compute_natarith compute_numberarith max_def min_def compute_num_conversions zpowerarith compute_div_mod compute_even

end
