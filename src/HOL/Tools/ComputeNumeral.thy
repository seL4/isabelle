theory ComputeNumeral
imports ComputeHOL Float
begin

(* normalization of bit strings *)
lemmas bitnorm = Pls_0_eq Min_1_eq

(* neg for bit strings *)
lemma neg1: "neg Int.Pls = False" by (simp add: Int.Pls_def)
lemma neg2: "neg Int.Min = True" apply (subst Int.Min_def) by auto
lemma neg3: "neg (x BIT Int.B0) = neg x" apply (simp add: neg_def) apply (subst Bit_def) by auto
lemma neg4: "neg (x BIT Int.B1) = neg x" apply (simp add: neg_def) apply (subst Bit_def) by auto  
lemmas bitneg = neg1 neg2 neg3 neg4

(* iszero for bit strings *)
lemma iszero1: "iszero Int.Pls = True" by (simp add: Int.Pls_def iszero_def)
lemma iszero2: "iszero Int.Min = False" apply (subst Int.Min_def) apply (subst iszero_def) by simp
lemma iszero3: "iszero (x BIT Int.B0) = iszero x" apply (subst Int.Bit_def) apply (subst iszero_def)+ by auto
lemma iszero4: "iszero (x BIT Int.B1) = False" apply (subst Int.Bit_def) apply (subst iszero_def)+  apply simp by arith
lemmas bitiszero = iszero1 iszero2 iszero3 iszero4

(* lezero for bit strings *)
constdefs
  "lezero x == (x \<le> 0)"
lemma lezero1: "lezero Int.Pls = True" unfolding Int.Pls_def lezero_def by auto
lemma lezero2: "lezero Int.Min = True" unfolding Int.Min_def lezero_def by auto
lemma lezero3: "lezero (x BIT Int.B0) = lezero x" unfolding Int.Bit_def lezero_def by auto
lemma lezero4: "lezero (x BIT Int.B1) = neg x" unfolding Int.Bit_def lezero_def neg_def by auto
lemmas bitlezero = lezero1 lezero2 lezero3 lezero4

(* equality for bit strings *)
lemma biteq1: "(Int.Pls = Int.Pls) = True" by auto
lemma biteq2: "(Int.Min = Int.Min) = True" by auto
lemma biteq3: "(Int.Pls = Int.Min) = False" unfolding Pls_def Min_def by auto
lemma biteq4: "(Int.Min = Int.Pls) = False" unfolding Pls_def Min_def by auto
lemma biteq5: "(x BIT Int.B0 = y BIT Int.B0) = (x = y)" unfolding Bit_def by auto
lemma biteq6: "(x BIT Int.B1 = y BIT Int.B1) = (x = y)" unfolding Bit_def by auto
lemma biteq7: "(x BIT Int.B0 = y BIT Int.B1) = False" unfolding Bit_def by (simp, arith) 
lemma biteq8: "(x BIT Int.B1 = y BIT Int.B0) = False" unfolding Bit_def by (simp, arith)
lemma biteq9: "(Int.Pls = x BIT Int.B0) = (Int.Pls = x)" unfolding Bit_def Pls_def by auto
lemma biteq10: "(Int.Pls = x BIT Int.B1) = False" unfolding Bit_def Pls_def by (simp, arith) 
lemma biteq11: "(Int.Min = x BIT Int.B0) = False" unfolding Bit_def Min_def by (simp, arith)
lemma biteq12: "(Int.Min = x BIT Int.B1) = (Int.Min = x)" unfolding Bit_def Min_def by auto
lemma biteq13: "(x BIT Int.B0 = Int.Pls) = (x = Int.Pls)" unfolding Bit_def Pls_def by auto
lemma biteq14: "(x BIT Int.B1 = Int.Pls) = False" unfolding Bit_def Pls_def by (simp, arith)
lemma biteq15: "(x BIT Int.B0 = Int.Min) = False" unfolding Bit_def Pls_def Min_def by (simp, arith)
lemma biteq16: "(x BIT Int.B1 = Int.Min) = (x = Int.Min)" unfolding Bit_def Min_def by (simp, arith)
lemmas biteq = biteq1 biteq2 biteq3 biteq4 biteq5 biteq6 biteq7 biteq8 biteq9 biteq10 biteq11 biteq12 biteq13 biteq14 biteq15 biteq16

(* x < y for bit strings *)
lemma bitless1: "(Int.Pls < Int.Min) = False" unfolding Pls_def Min_def by auto
lemma bitless2: "(Int.Pls < Int.Pls) = False" by auto
lemma bitless3: "(Int.Min < Int.Pls) = True" unfolding Pls_def Min_def by auto
lemma bitless4: "(Int.Min < Int.Min) = False" unfolding Pls_def Min_def by auto
lemma bitless5: "(x BIT Int.B0 < y BIT Int.B0) = (x < y)" unfolding Bit_def by auto
lemma bitless6: "(x BIT Int.B1 < y BIT Int.B1) = (x < y)" unfolding Bit_def by auto
lemma bitless7: "(x BIT Int.B0 < y BIT Int.B1) = (x \<le> y)" unfolding Bit_def by auto
lemma bitless8: "(x BIT Int.B1 < y BIT Int.B0) = (x < y)" unfolding Bit_def by auto
lemma bitless9: "(Int.Pls < x BIT Int.B0) = (Int.Pls < x)" unfolding Bit_def Pls_def by auto
lemma bitless10: "(Int.Pls < x BIT Int.B1) = (Int.Pls \<le> x)" unfolding Bit_def Pls_def by auto
lemma bitless11: "(Int.Min < x BIT Int.B0) = (Int.Pls \<le> x)" unfolding Bit_def Pls_def Min_def by auto
lemma bitless12: "(Int.Min < x BIT Int.B1) = (Int.Min < x)" unfolding Bit_def Min_def by auto
lemma bitless13: "(x BIT Int.B0 < Int.Pls) = (x < Int.Pls)" unfolding Bit_def Pls_def by auto
lemma bitless14: "(x BIT Int.B1 < Int.Pls) = (x < Int.Pls)" unfolding Bit_def Pls_def by auto
lemma bitless15: "(x BIT Int.B0 < Int.Min) = (x < Int.Pls)" unfolding Bit_def Pls_def Min_def by auto
lemma bitless16: "(x BIT Int.B1 < Int.Min) = (x < Int.Min)" unfolding Bit_def Min_def by auto
lemmas bitless = bitless1 bitless2 bitless3 bitless4 bitless5 bitless6 bitless7 bitless8 
                 bitless9 bitless10 bitless11 bitless12 bitless13 bitless14 bitless15 bitless16

(* x \<le> y for bit strings *)
lemma bitle1: "(Int.Pls \<le> Int.Min) = False" unfolding Pls_def Min_def by auto
lemma bitle2: "(Int.Pls \<le> Int.Pls) = True" by auto
lemma bitle3: "(Int.Min \<le> Int.Pls) = True" unfolding Pls_def Min_def by auto
lemma bitle4: "(Int.Min \<le> Int.Min) = True" unfolding Pls_def Min_def by auto
lemma bitle5: "(x BIT Int.B0 \<le> y BIT Int.B0) = (x \<le> y)" unfolding Bit_def by auto
lemma bitle6: "(x BIT Int.B1 \<le> y BIT Int.B1) = (x \<le> y)" unfolding Bit_def by auto
lemma bitle7: "(x BIT Int.B0 \<le> y BIT Int.B1) = (x \<le> y)" unfolding Bit_def by auto
lemma bitle8: "(x BIT Int.B1 \<le> y BIT Int.B0) = (x < y)" unfolding Bit_def by auto
lemma bitle9: "(Int.Pls \<le> x BIT Int.B0) = (Int.Pls \<le> x)" unfolding Bit_def Pls_def by auto
lemma bitle10: "(Int.Pls \<le> x BIT Int.B1) = (Int.Pls \<le> x)" unfolding Bit_def Pls_def by auto
lemma bitle11: "(Int.Min \<le> x BIT Int.B0) = (Int.Pls \<le> x)" unfolding Bit_def Pls_def Min_def by auto
lemma bitle12: "(Int.Min \<le> x BIT Int.B1) = (Int.Min \<le> x)" unfolding Bit_def Min_def by auto
lemma bitle13: "(x BIT Int.B0 \<le> Int.Pls) = (x \<le> Int.Pls)" unfolding Bit_def Pls_def by auto
lemma bitle14: "(x BIT Int.B1 \<le> Int.Pls) = (x < Int.Pls)" unfolding Bit_def Pls_def by auto
lemma bitle15: "(x BIT Int.B0 \<le> Int.Min) = (x < Int.Pls)" unfolding Bit_def Pls_def Min_def by auto
lemma bitle16: "(x BIT Int.B1 \<le> Int.Min) = (x \<le> Int.Min)" unfolding Bit_def Min_def by auto
lemmas bitle = bitle1 bitle2 bitle3 bitle4 bitle5 bitle6 bitle7 bitle8 
                 bitle9 bitle10 bitle11 bitle12 bitle13 bitle14 bitle15 bitle16

(* succ for bit strings *)
lemmas bitsucc = succ_Pls succ_Min succ_1 succ_0

(* pred for bit strings *)
lemmas bitpred = pred_Pls pred_Min pred_1 pred_0

(* unary minus for bit strings *)
lemmas bituminus = minus_Pls minus_Min minus_1 minus_0 

(* addition for bit strings *)
lemmas bitadd = add_Pls add_Pls_right add_Min add_Min_right add_BIT_11 add_BIT_10 add_BIT_0[where b="Int.B0"] add_BIT_0[where b="Int.B1"]

(* multiplication for bit strings *) 
lemma mult_Pls_right: "x * Int.Pls = Int.Pls" by (simp add: Pls_def)
lemma mult_Min_right: "x * Int.Min = - x" by (subst mult_commute, simp add: mult_Min)
lemma multb0x: "(x BIT Int.B0) * y = (x * y) BIT Int.B0" unfolding Bit_def by simp
lemma multxb0: "x * (y BIT Int.B0) = (x * y) BIT Int.B0" unfolding Bit_def by simp
lemma multb1: "(x BIT Int.B1) * (y BIT Int.B1) = (((x * y) BIT Int.B0) + x + y) BIT Int.B1"
  unfolding Bit_def by (simp add: ring_simps)
lemmas bitmul = mult_Pls mult_Min mult_Pls_right mult_Min_right multb0x multxb0 multb1

lemmas bitarith = bitnorm bitiszero bitneg bitlezero biteq bitless bitle bitsucc bitpred bituminus bitadd bitmul 

constdefs 
  "nat_norm_number_of (x::nat) == x"

lemma nat_norm_number_of: "nat_norm_number_of (number_of w) = (if lezero w then 0 else number_of w)"
  apply (simp add: nat_norm_number_of_def)
  unfolding lezero_def iszero_def neg_def
  apply (simp add: number_of_is_id)
  done

(* Normalization of nat literals *)
lemma natnorm0: "(0::nat) = number_of (Int.Pls)" by auto
lemma natnorm1: "(1 :: nat) = number_of (Int.Pls BIT Int.B1)"  by auto 
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

lemma even_B0: "even (x BIT Int.B0) = True"
  apply (unfold Bit_def)
  by simp

lemma even_B1: "even (x BIT Int.B1) = False"
  apply (unfold Bit_def)
  by simp

lemma even_number_of: "even ((number_of w)::int) = even w"
  by (simp only: number_of_is_id)

lemmas compute_even = even_Pls even_Min even_B0 even_B1 even_number_of

lemmas compute_numeral = compute_if compute_let compute_pair compute_bool 
                         compute_natarith compute_numberarith max_def min_def compute_num_conversions zpowerarith compute_div_mod compute_even

end



