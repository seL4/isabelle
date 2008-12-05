theory ComputeNumeral
imports ComputeHOL "~~/src/HOL/Real/Float"
begin

(* normalization of bit strings *)
lemmas bitnorm = normalize_bin_simps

(* neg for bit strings *)
lemma neg1: "neg Int.Pls = False" by (simp add: Int.Pls_def)
lemma neg2: "neg Int.Min = True" apply (subst Int.Min_def) by auto
lemma neg3: "neg (Int.Bit0 x) = neg x" apply (simp add: neg_def) apply (subst Bit0_def) by auto
lemma neg4: "neg (Int.Bit1 x) = neg x" apply (simp add: neg_def) apply (subst Bit1_def) by auto  
lemmas bitneg = neg1 neg2 neg3 neg4

(* iszero for bit strings *)
lemma iszero1: "iszero Int.Pls = True" by (simp add: Int.Pls_def iszero_def)
lemma iszero2: "iszero Int.Min = False" apply (subst Int.Min_def) apply (subst iszero_def) by simp
lemma iszero3: "iszero (Int.Bit0 x) = iszero x" apply (subst Int.Bit0_def) apply (subst iszero_def)+ by auto
lemma iszero4: "iszero (Int.Bit1 x) = False" apply (subst Int.Bit1_def) apply (subst iszero_def)+  apply simp by arith
lemmas bitiszero = iszero1 iszero2 iszero3 iszero4

(* lezero for bit strings *)
constdefs
  "lezero x == (x \<le> 0)"
lemma lezero1: "lezero Int.Pls = True" unfolding Int.Pls_def lezero_def by auto
lemma lezero2: "lezero Int.Min = True" unfolding Int.Min_def lezero_def by auto
lemma lezero3: "lezero (Int.Bit0 x) = lezero x" unfolding Int.Bit0_def lezero_def by auto
lemma lezero4: "lezero (Int.Bit1 x) = neg x" unfolding Int.Bit1_def lezero_def neg_def by auto
lemmas bitlezero = lezero1 lezero2 lezero3 lezero4

(* equality for bit strings *)
lemma biteq1: "(Int.Pls = Int.Pls) = True" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq2: "(Int.Min = Int.Min) = True" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq3: "(Int.Pls = Int.Min) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq4: "(Int.Min = Int.Pls) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq5: "(Int.Bit0 x = Int.Bit0 y) = (x = y)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq6: "(Int.Bit1 x = Int.Bit1 y) = (x = y)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq7: "(Int.Bit0 x = Int.Bit1 y) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq8: "(Int.Bit1 x = Int.Bit0 y) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq9: "(Int.Pls = Int.Bit0 x) = (Int.Pls = x)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq10: "(Int.Pls = Int.Bit1 x) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq11: "(Int.Min = Int.Bit0 x) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq12: "(Int.Min = Int.Bit1 x) = (Int.Min = x)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq13: "(Int.Bit0 x = Int.Pls) = (x = Int.Pls)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq14: "(Int.Bit1 x = Int.Pls) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq15: "(Int.Bit0 x = Int.Min) = False" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma biteq16: "(Int.Bit1 x = Int.Min) = (x = Int.Min)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemmas biteq = biteq1 biteq2 biteq3 biteq4 biteq5 biteq6 biteq7 biteq8 biteq9 biteq10 biteq11 biteq12 biteq13 biteq14 biteq15 biteq16

(* x < y for bit strings *)
lemma bitless1: "(Int.Pls < Int.Min) = False" by (simp add: less_int_code)
lemma bitless2: "(Int.Pls < Int.Pls) = False" by (simp add: less_int_code)
lemma bitless3: "(Int.Min < Int.Pls) = True" by (simp add: less_int_code)
lemma bitless4: "(Int.Min < Int.Min) = False" by (simp add: less_int_code)
lemma bitless5: "(Int.Bit0 x < Int.Bit0 y) = (x < y)" by (simp add: less_int_code)
lemma bitless6: "(Int.Bit1 x < Int.Bit1 y) = (x < y)" by (simp add: less_int_code)
lemma bitless7: "(Int.Bit0 x < Int.Bit1 y) = (x \<le> y)" by (simp add: less_int_code)
lemma bitless8: "(Int.Bit1 x < Int.Bit0 y) = (x < y)" by (simp add: less_int_code)
lemma bitless9: "(Int.Pls < Int.Bit0 x) = (Int.Pls < x)" by (simp add: less_int_code)
lemma bitless10: "(Int.Pls < Int.Bit1 x) = (Int.Pls \<le> x)" by (simp add: less_int_code)
lemma bitless11: "(Int.Min < Int.Bit0 x) = (Int.Pls \<le> x)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma bitless12: "(Int.Min < Int.Bit1 x) = (Int.Min < x)" by (simp add: less_int_code)
lemma bitless13: "(Int.Bit0 x < Int.Pls) = (x < Int.Pls)" by (simp add: less_int_code)
lemma bitless14: "(Int.Bit1 x < Int.Pls) = (x < Int.Pls)" by (simp add: less_int_code)
lemma bitless15: "(Int.Bit0 x < Int.Min) = (x < Int.Pls)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma bitless16: "(Int.Bit1 x < Int.Min) = (x < Int.Min)" by (simp add: less_int_code)
lemmas bitless = bitless1 bitless2 bitless3 bitless4 bitless5 bitless6 bitless7 bitless8 
                 bitless9 bitless10 bitless11 bitless12 bitless13 bitless14 bitless15 bitless16

(* x \<le> y for bit strings *)
lemma bitle1: "(Int.Pls \<le> Int.Min) = False" by (simp add: less_eq_int_code)
lemma bitle2: "(Int.Pls \<le> Int.Pls) = True" by (simp add: less_eq_int_code)
lemma bitle3: "(Int.Min \<le> Int.Pls) = True" by (simp add: less_eq_int_code)
lemma bitle4: "(Int.Min \<le> Int.Min) = True" by (simp add: less_eq_int_code)
lemma bitle5: "(Int.Bit0 x \<le> Int.Bit0 y) = (x \<le> y)" by (simp add: less_eq_int_code)
lemma bitle6: "(Int.Bit1 x \<le> Int.Bit1 y) = (x \<le> y)" by (simp add: less_eq_int_code)
lemma bitle7: "(Int.Bit0 x \<le> Int.Bit1 y) = (x \<le> y)" by (simp add: less_eq_int_code)
lemma bitle8: "(Int.Bit1 x \<le> Int.Bit0 y) = (x < y)" by (simp add: less_eq_int_code)
lemma bitle9: "(Int.Pls \<le> Int.Bit0 x) = (Int.Pls \<le> x)" by (simp add: less_eq_int_code)
lemma bitle10: "(Int.Pls \<le> Int.Bit1 x) = (Int.Pls \<le> x)" by (simp add: less_eq_int_code)
lemma bitle11: "(Int.Min \<le> Int.Bit0 x) = (Int.Pls \<le> x)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma bitle12: "(Int.Min \<le> Int.Bit1 x) = (Int.Min \<le> x)" by (simp add: less_eq_int_code)
lemma bitle13: "(Int.Bit0 x \<le> Int.Pls) = (x \<le> Int.Pls)" by (simp add: less_eq_int_code)
lemma bitle14: "(Int.Bit1 x \<le> Int.Pls) = (x < Int.Pls)" by (simp add: less_eq_int_code)
lemma bitle15: "(Int.Bit0 x \<le> Int.Min) = (x < Int.Pls)" unfolding Pls_def Min_def Bit0_def Bit1_def by presburger
lemma bitle16: "(Int.Bit1 x \<le> Int.Min) = (x \<le> Int.Min)" by (simp add: less_eq_int_code)
lemmas bitle = bitle1 bitle2 bitle3 bitle4 bitle5 bitle6 bitle7 bitle8 
                 bitle9 bitle10 bitle11 bitle12 bitle13 bitle14 bitle15 bitle16

(* succ for bit strings *)
lemmas bitsucc = succ_bin_simps

(* pred for bit strings *)
lemmas bitpred = pred_bin_simps

(* unary minus for bit strings *)
lemmas bituminus = minus_bin_simps

(* addition for bit strings *)
lemmas bitadd = add_bin_simps

(* multiplication for bit strings *) 
lemma mult_Pls_right: "x * Int.Pls = Int.Pls" by (simp add: Pls_def)
lemma mult_Min_right: "x * Int.Min = - x" by (subst mult_commute, simp add: mult_Min)
lemma multb0x: "(Int.Bit0 x) * y = Int.Bit0 (x * y)" by (rule mult_Bit0)
lemma multxb0: "x * (Int.Bit0 y) = Int.Bit0 (x * y)" unfolding Bit0_def by simp
lemma multb1: "(Int.Bit1 x) * (Int.Bit1 y) = Int.Bit1 (Int.Bit0 (x * y) + x + y)"
  unfolding Bit0_def Bit1_def by (simp add: ring_simps)
lemmas bitmul = mult_Pls mult_Min mult_Pls_right mult_Min_right multb0x multxb0 multb1

lemmas bitarith = bitnorm bitiszero bitneg bitlezero biteq bitless bitle bitsucc bitpred bituminus bitadd bitmul 

constdefs 
  "nat_norm_number_of (x::nat) == x"

lemma nat_norm_number_of: "nat_norm_number_of (number_of w) = (if lezero w then 0 else number_of w)"
  apply (simp add: nat_norm_number_of_def)
  unfolding lezero_def iszero_def neg_def
  apply (simp add: numeral_simps)
  done

(* Normalization of nat literals *)
lemma natnorm0: "(0::nat) = number_of (Int.Pls)" by auto
lemma natnorm1: "(1 :: nat) = number_of (Int.Bit1 Int.Pls)"  by auto 
lemmas natnorm = natnorm0 natnorm1 nat_norm_number_of

(* Suc *)
lemma natsuc: "Suc (number_of x) = (if neg x then 1 else number_of (Int.succ x))" by (auto simp add: number_of_is_id)

(* Addition for nat *)
lemma natadd: "number_of x + ((number_of y)::nat) = (if neg x then (number_of y) else (if neg y then number_of x else (number_of (x + y))))"
  by (auto simp add: number_of_is_id)

(* Subtraction for nat *)
lemma natsub: "(number_of x) - ((number_of y)::nat) = 
  (if neg x then 0 else (if neg y then number_of x else (nat_norm_number_of (number_of (x + (- y))))))"
  unfolding nat_norm_number_of
  by (auto simp add: number_of_is_id neg_def lezero_def iszero_def Let_def nat_number_of_def)

(* Multiplication for nat *)
lemma natmul: "(number_of x) * ((number_of y)::nat) = 
  (if neg x then 0 else (if neg y then 0 else number_of (x * y)))"
  apply (auto simp add: number_of_is_id neg_def iszero_def)
  apply (case_tac "x > 0")
  apply auto
  apply (rule order_less_imp_le)
  apply (simp add: mult_strict_left_mono[where a=y and b=0 and c=x, simplified])
  done

lemma nateq: "(((number_of x)::nat) = (number_of y)) = ((lezero x \<and> lezero y) \<or> (x = y))"
  by (auto simp add: iszero_def lezero_def neg_def number_of_is_id)

lemma natless: "(((number_of x)::nat) < (number_of y)) = ((x < y) \<and> (\<not> (lezero y)))"
  by (auto simp add: number_of_is_id neg_def lezero_def)

lemma natle: "(((number_of x)::nat) \<le> (number_of y)) = (y < x \<longrightarrow> lezero x)"
  by (auto simp add: number_of_is_id lezero_def nat_number_of_def)

fun natfac :: "nat \<Rightarrow> nat"
where
   "natfac n = (if n = 0 then 1 else n * (natfac (n - 1)))"

lemmas compute_natarith = bitarith natnorm natsuc natadd natsub natmul nateq natless natle natfac.simps

lemma number_eq: "(((number_of x)::'a::{number_ring, ordered_idom}) = (number_of y)) = (x = y)"
  unfolding number_of_eq
  apply simp
  done

lemma number_le: "(((number_of x)::'a::{number_ring, ordered_idom}) \<le>  (number_of y)) = (x \<le> y)"
  unfolding number_of_eq
  apply simp
  done

lemma number_less: "(((number_of x)::'a::{number_ring, ordered_idom}) <  (number_of y)) = (x < y)"
  unfolding number_of_eq 
  apply simp
  done

lemma number_diff: "((number_of x)::'a::{number_ring, ordered_idom}) - number_of y = number_of (x + (- y))"
  apply (subst diff_number_of_eq)
  apply simp
  done

lemmas number_norm = number_of_Pls[symmetric] numeral_1_eq_1[symmetric]

lemmas compute_numberarith = number_of_minus[symmetric] number_of_add[symmetric] number_diff number_of_mult[symmetric] number_norm number_eq number_le number_less

lemma compute_real_of_nat_number_of: "real ((number_of v)::nat) = (if neg v then 0 else number_of v)"
  by (simp only: real_of_nat_number_of number_of_is_id)

lemma compute_nat_of_int_number_of: "nat ((number_of v)::int) = (number_of v)"
  by simp

lemmas compute_num_conversions = compute_real_of_nat_number_of compute_nat_of_int_number_of real_number_of

lemmas zpowerarith = zpower_number_of_even
  zpower_number_of_odd[simplified zero_eq_Numeral0_nring one_eq_Numeral1_nring]
  zpower_Pls zpower_Min

(* div, mod *)

lemma adjust: "adjust b (q, r) = (if 0 \<le> r - b then (2 * q + 1, r - b) else (2 * q, r))"
  by (auto simp only: adjust_def)

lemma negateSnd: "negateSnd (q, r) = (q, -r)" 
  by (auto simp only: negateSnd_def)

lemma divAlg: "divAlg (a, b) = (if 0\<le>a then
                  if 0\<le>b then posDivAlg a b
                  else if a=0 then (0, 0)
                       else negateSnd (negDivAlg (-a) (-b))
               else 
                  if 0<b then negDivAlg a b
                  else negateSnd (posDivAlg (-a) (-b)))"
  by (auto simp only: divAlg_def)

lemmas compute_div_mod = div_def mod_def divAlg adjust negateSnd posDivAlg.simps negDivAlg.simps



(* collecting all the theorems *)

lemma even_Pls: "even (Int.Pls) = True"
  apply (unfold Pls_def even_def)
  by simp

lemma even_Min: "even (Int.Min) = False"
  apply (unfold Min_def even_def)
  by simp

lemma even_B0: "even (Int.Bit0 x) = True"
  apply (unfold Bit0_def)
  by simp

lemma even_B1: "even (Int.Bit1 x) = False"
  apply (unfold Bit1_def)
  by simp

lemma even_number_of: "even ((number_of w)::int) = even w"
  by (simp only: number_of_is_id)

lemmas compute_even = even_Pls even_Min even_B0 even_B1 even_number_of

lemmas compute_numeral = compute_if compute_let compute_pair compute_bool 
                         compute_natarith compute_numberarith max_def min_def compute_num_conversions zpowerarith compute_div_mod compute_even

end



