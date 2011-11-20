(* 
  Author: Jeremy Dawson and Gerwin Klein, NICTA

  Definitions and basic theorems for bit-wise logical operations 
  for integers expressed using Pls, Min, BIT,
  and converting them to and from lists of bools.
*) 

header {* Bitwise Operations on Binary Integers *}

theory Bit_Int
imports Bit_Representation Bit_Operations
begin

subsection {* Recursion combinators for bitstrings *}

function bin_rec :: "'a \<Rightarrow> 'a \<Rightarrow> (int \<Rightarrow> bit \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a" where 
  "bin_rec f1 f2 f3 bin = (if bin = 0 then f1 
    else if bin = - 1 then f2
    else f3 (bin_rest bin) (bin_last bin) (bin_rec f1 f2 f3 (bin_rest bin)))"
  by pat_completeness auto

termination by (relation "measure (nat o abs o snd o snd o snd)")
  (simp_all add: bin_last_def bin_rest_def)

declare bin_rec.simps [simp del]

lemma bin_rec_PM:
  "f = bin_rec f1 f2 f3 ==> f Int.Pls = f1 & f Int.Min = f2"
  by (unfold Pls_def Min_def) (simp add: bin_rec.simps)

lemma bin_rec_Pls: "bin_rec f1 f2 f3 Int.Pls = f1"
  by (unfold Pls_def Min_def) (simp add: bin_rec.simps)

lemma bin_rec_Min: "bin_rec f1 f2 f3 Int.Min = f2"
  by (unfold Pls_def Min_def) (simp add: bin_rec.simps)

lemma bin_rec_Bit0:
  "f3 Int.Pls (0::bit) f1 = f1 \<Longrightarrow>
    bin_rec f1 f2 f3 (Int.Bit0 w) = f3 w (0::bit) (bin_rec f1 f2 f3 w)"
  by (unfold Pls_def Min_def Bit0_def Bit1_def) (simp add: bin_rec.simps bin_last_def bin_rest_def)

lemma bin_rec_Bit1:
  "f3 Int.Min (1::bit) f2 = f2 \<Longrightarrow>
    bin_rec f1 f2 f3 (Int.Bit1 w) = f3 w (1::bit) (bin_rec f1 f2 f3 w)"
  apply (cases "w = Int.Min")
  apply (simp add: bin_rec_Min)
  apply (cases "w = Int.Pls")
  apply (simp add: bin_rec_Pls number_of_is_id Pls_def [symmetric] bin_rec.simps)
  apply (subst bin_rec.simps)
  apply auto unfolding Pls_def Min_def Bit0_def Bit1_def number_of_is_id apply auto
  done
  
lemma bin_rec_Bit:
  "f = bin_rec f1 f2 f3  ==> f3 Int.Pls (0::bit) f1 = f1 ==> 
    f3 Int.Min (1::bit) f2 = f2 ==> f (w BIT b) = f3 w b (f w)"
  by (cases b, simp add: bin_rec_Bit0, simp add: bin_rec_Bit1)

lemmas bin_rec_simps = refl [THEN bin_rec_Bit] bin_rec_Pls bin_rec_Min
  bin_rec_Bit0 bin_rec_Bit1


subsection {* Logical operations *}

text "bit-wise logical operations on the int type"

instantiation int :: bit
begin

definition
  int_not_def: "bitNOT = bin_rec (- 1) 0
    (\<lambda>w b s. s BIT (NOT b))"

definition
  int_and_def: "bitAND = bin_rec (\<lambda>x. 0) (\<lambda>y. y) 
    (\<lambda>w b s y. s (bin_rest y) BIT (b AND bin_last y))"

definition
  int_or_def: "bitOR = bin_rec (\<lambda>x. x) (\<lambda>y. - 1) 
    (\<lambda>w b s y. s (bin_rest y) BIT (b OR bin_last y))"

definition
  int_xor_def: "bitXOR = bin_rec (\<lambda>x. x) bitNOT 
    (\<lambda>w b s y. s (bin_rest y) BIT (b XOR bin_last y))"

instance ..

end

subsubsection {* Basic simplification rules *}

lemma int_not_simps [simp]:
  "NOT Int.Pls = Int.Min"
  "NOT Int.Min = Int.Pls"
  "NOT (Int.Bit0 w) = Int.Bit1 (NOT w)"
  "NOT (Int.Bit1 w) = Int.Bit0 (NOT w)"
  "NOT (w BIT b) = (NOT w) BIT (NOT b)"
  unfolding int_not_def Pls_def [symmetric] Min_def [symmetric] by (simp_all add: bin_rec_simps)

lemma int_xor_Pls [simp]: 
  "Int.Pls XOR x = x"
  unfolding int_xor_def Pls_def [symmetric] Min_def [symmetric] by (simp add: bin_rec_PM)

lemma int_xor_Min [simp]: 
  "Int.Min XOR x = NOT x"
  unfolding int_xor_def Pls_def [symmetric] Min_def [symmetric] by (simp add: bin_rec_PM)

lemma int_xor_Bits [simp]: 
  "(x BIT b) XOR (y BIT c) = (x XOR y) BIT (b XOR c)"
  apply (unfold int_xor_def Pls_def [symmetric] Min_def [symmetric])
  apply (rule bin_rec_simps (1) [THEN fun_cong, THEN trans])
    apply (rule ext, simp)
   prefer 2
   apply simp
  apply (rule ext)
  apply (simp add: int_not_simps [symmetric])
  done

lemma int_xor_Bits2 [simp]: 
  "(Int.Bit0 x) XOR (Int.Bit0 y) = Int.Bit0 (x XOR y)"
  "(Int.Bit0 x) XOR (Int.Bit1 y) = Int.Bit1 (x XOR y)"
  "(Int.Bit1 x) XOR (Int.Bit0 y) = Int.Bit1 (x XOR y)"
  "(Int.Bit1 x) XOR (Int.Bit1 y) = Int.Bit0 (x XOR y)"
  unfolding BIT_simps [symmetric] int_xor_Bits by simp_all

lemma int_or_Pls [simp]: 
  "Int.Pls OR x = x"
  by (unfold int_or_def) (simp add: bin_rec_PM)
  
lemma int_or_Min [simp]:
  "Int.Min OR x = Int.Min"
  by (unfold int_or_def Pls_def [symmetric] Min_def [symmetric]) (simp add: bin_rec_PM)

lemma int_or_Bits [simp]: 
  "(x BIT b) OR (y BIT c) = (x OR y) BIT (b OR c)"
  unfolding int_or_def Pls_def [symmetric] Min_def [symmetric] by (simp add: bin_rec_simps)

lemma int_or_Bits2 [simp]: 
  "(Int.Bit0 x) OR (Int.Bit0 y) = Int.Bit0 (x OR y)"
  "(Int.Bit0 x) OR (Int.Bit1 y) = Int.Bit1 (x OR y)"
  "(Int.Bit1 x) OR (Int.Bit0 y) = Int.Bit1 (x OR y)"
  "(Int.Bit1 x) OR (Int.Bit1 y) = Int.Bit1 (x OR y)"
  unfolding BIT_simps [symmetric] int_or_Bits by simp_all

lemma int_and_Pls [simp]:
  "Int.Pls AND x = Int.Pls"
  unfolding int_and_def by (simp add: bin_rec_PM)

lemma int_and_Min [simp]:
  "Int.Min AND x = x"
  unfolding int_and_def by (simp add: bin_rec_PM)

lemma int_and_Bits [simp]: 
  "(x BIT b) AND (y BIT c) = (x AND y) BIT (b AND c)" 
  unfolding int_and_def Pls_def [symmetric] Min_def [symmetric] by (simp add: bin_rec_simps)

lemma int_and_Bits2 [simp]: 
  "(Int.Bit0 x) AND (Int.Bit0 y) = Int.Bit0 (x AND y)"
  "(Int.Bit0 x) AND (Int.Bit1 y) = Int.Bit0 (x AND y)"
  "(Int.Bit1 x) AND (Int.Bit0 y) = Int.Bit0 (x AND y)"
  "(Int.Bit1 x) AND (Int.Bit1 y) = Int.Bit1 (x AND y)"
  unfolding BIT_simps [symmetric] int_and_Bits by simp_all

subsubsection {* Binary destructors *}

lemma bin_rest_NOT [simp]: "bin_rest (NOT x) = NOT (bin_rest x)"
  by (cases x rule: bin_exhaust, simp)

lemma bin_last_NOT [simp]: "bin_last (NOT x) = NOT (bin_last x)"
  by (cases x rule: bin_exhaust, simp)

lemma bin_rest_AND [simp]: "bin_rest (x AND y) = bin_rest x AND bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_last_AND [simp]: "bin_last (x AND y) = bin_last x AND bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_rest_OR [simp]: "bin_rest (x OR y) = bin_rest x OR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_last_OR [simp]: "bin_last (x OR y) = bin_last x OR bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_rest_XOR [simp]: "bin_rest (x XOR y) = bin_rest x XOR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bin_last_XOR [simp]: "bin_last (x XOR y) = bin_last x XOR bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust, simp)

lemma bit_NOT_eq_1_iff [simp]: "NOT (b::bit) = 1 \<longleftrightarrow> b = 0"
  by (induct b, simp_all)

lemma bit_AND_eq_1_iff [simp]: "(a::bit) AND b = 1 \<longleftrightarrow> a = 1 \<and> b = 1"
  by (induct a, simp_all)

lemma bin_nth_ops:
  "!!x y. bin_nth (x AND y) n = (bin_nth x n & bin_nth y n)" 
  "!!x y. bin_nth (x OR y) n = (bin_nth x n | bin_nth y n)"
  "!!x y. bin_nth (x XOR y) n = (bin_nth x n ~= bin_nth y n)" 
  "!!x. bin_nth (NOT x) n = (~ bin_nth x n)"
  by (induct n) auto

subsubsection {* Derived properties *}

lemma int_xor_extra_simps [simp]:
  "w XOR Int.Pls = w"
  "w XOR Int.Min = NOT w"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_extra_simps [simp]:
  "w OR Int.Pls = w"
  "w OR Int.Min = Int.Min"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_extra_simps [simp]:
  "w AND Int.Pls = Int.Pls"
  "w AND Int.Min = w"
  by (auto simp add: bin_eq_iff bin_nth_ops)

(* commutativity of the above *)
lemma bin_ops_comm:
  shows
  int_and_comm: "!!y::int. x AND y = y AND x" and
  int_or_comm:  "!!y::int. x OR y = y OR x" and
  int_xor_comm: "!!y::int. x XOR y = y XOR x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bin_ops_same [simp]:
  "(x::int) AND x = x" 
  "(x::int) OR x = x" 
  "(x::int) XOR x = Int.Pls"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_not_not [simp]: "NOT (NOT (x::int)) = x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bin_log_esimps = 
  int_and_extra_simps  int_or_extra_simps  int_xor_extra_simps
  int_and_Pls int_and_Min  int_or_Pls int_or_Min  int_xor_Pls int_xor_Min

(* basic properties of logical (bit-wise) operations *)

lemma bbw_ao_absorb: 
  "!!y::int. x AND (y OR x) = x & x OR (y AND x) = x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = (x::int)"
  "(y OR x) AND x = x \<and> x OR (x AND y) = (x::int)"
  "(x OR y) AND x = x \<and> (x AND y) OR x = (x::int)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not:
  "!!y::int. (NOT x) XOR y = NOT (x XOR y) & 
        x XOR (NOT y) = NOT (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_assoc:
  "(x AND y) AND (z::int) = x AND (y AND z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_assoc:
  "(x OR y) OR (z::int) = x OR (y OR z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_assoc:
  "(x XOR y) XOR (z::int) = x XOR (y XOR z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

(* BH: Why are these declared as simp rules??? *)
lemma bbw_lcs [simp]: 
  "(y::int) AND (x AND z) = x AND (y AND z)"
  "(y::int) OR (x OR z) = x OR (y OR z)"
  "(y::int) XOR (x XOR z) = x XOR (y XOR z)" 
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_not_dist: 
  "!!y::int. NOT (x OR y) = (NOT x) AND (NOT y)" 
  "!!y::int. NOT (x AND y) = (NOT x) OR (NOT y)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_oa_dist: 
  "!!y z::int. (x AND y) OR z = 
          (x OR z) AND (y OR z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_dist: 
  "!!y z::int. (x OR y) AND z = 
          (x AND z) OR (y AND z)"
  by (auto simp add: bin_eq_iff bin_nth_ops)

(*
Why were these declared simp???
declare bin_ops_comm [simp] bbw_assocs [simp] 
*)

subsubsection {* Interactions with arithmetic *}

lemma plus_and_or [rule_format]:
  "ALL y::int. (x AND y) + (x OR y) = x + y"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac y rule: bin_exhaust)
  apply clarsimp
  apply (unfold Bit_def)
  apply clarsimp
  apply (erule_tac x = "x" in allE)
  apply (simp add: bitval_def split: bit.split)
  done

lemma le_int_or:
  "bin_sign (y::int) = Int.Pls ==> x <= x OR y"
  apply (induct y arbitrary: x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac x rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] bit)
     apply (auto simp: less_eq_int_code)
  done

lemmas int_and_le =
  xtr3 [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or]

(* interaction between bit-wise and arithmetic *)
(* good example of bin_induction *)
lemma bin_add_not: "x + NOT x = Int.Min"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac bit, auto)
  done

subsubsection {* Truncating results of bit-wise operations *}

lemma bin_trunc_ao: 
  "!!x y. (bintrunc n x) AND (bintrunc n y) = bintrunc n (x AND y)" 
  "!!x y. (bintrunc n x) OR (bintrunc n y) = bintrunc n (x OR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_xor: 
  "!!x y. bintrunc n (bintrunc n x XOR bintrunc n y) = 
          bintrunc n (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_not: 
  "!!x. bintrunc n (NOT (bintrunc n x)) = bintrunc n (NOT x)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

(* want theorems of the form of bin_trunc_xor *)
lemma bintr_bintr_i:
  "x = bintrunc n y ==> bintrunc n x = bintrunc n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]

subsection {* Setting and clearing bits *}

primrec
  bin_sc :: "nat => bit => int => int"
where
  Z: "bin_sc 0 b w = bin_rest w BIT b"
  | Suc: "bin_sc (Suc n) b w = bin_sc n b (bin_rest w) BIT bin_last w"

(** nth bit, set/clear **)

lemma bin_nth_sc [simp]: 
  "!!w. bin_nth (bin_sc n b w) n = (b = 1)"
  by (induct n)  auto

lemma bin_sc_sc_same [simp]: 
  "!!w. bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induct n) auto

lemma bin_sc_sc_diff:
  "!!w m. m ~= n ==> 
    bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: 
  "!!w m. bin_nth (bin_sc n b w) m = (if m = n then b = 1 else bin_nth w m)"
  by (induct n) (case_tac [!] m, auto)
  
lemma bin_sc_nth [simp]:
  "!!w. (bin_sc n (If (bin_nth w n) 1 0) w) = w"
  by (induct n) auto

lemma bin_sign_sc [simp]:
  "!!w. bin_sign (bin_sc n b w) = bin_sign w"
  by (induct n) auto
  
lemma bin_sc_bintr [simp]: 
  "!!w m. bintrunc m (bin_sc n x (bintrunc m (w))) = bintrunc m (bin_sc n x w)"
  apply (induct n)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (case_tac [!] m, auto)
  done

lemma bin_clr_le:
  "!!w. bin_sc n 0 w <= w"
  apply (induct n) 
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all add: bitval_def split: bit.split)
  done

lemma bin_set_ge:
  "!!w. bin_sc n 1 w >= w"
  apply (induct n) 
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all add: bitval_def split: bit.split)
  done

lemma bintr_bin_clr_le:
  "!!w m. bintrunc n (bin_sc m 0 w) <= bintrunc n w"
  apply (induct n)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all add: bitval_def split: bit.split)
  done

lemma bintr_bin_set_ge:
  "!!w m. bintrunc n (bin_sc m 1 w) >= bintrunc n w"
  apply (induct n)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp del: BIT_simps)
   apply (unfold Bit_def)
   apply (simp_all add: bitval_def split: bit.split)
  done

lemma bin_sc_FP [simp]: "bin_sc n 0 Int.Pls = Int.Pls"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n 1 Int.Min = Int.Min"
  by (induct n) auto
  
lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus:
  "0 < n ==> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus = 
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc]

lemmas bin_sc_Suc_pred [simp] = 
  bin_sc_Suc_minus [of "number_of bin", simplified nobm1] for bin


subsection {* Splitting and concatenation *}

definition bin_rcat :: "nat \<Rightarrow> int list \<Rightarrow> int" where
  "bin_rcat n = foldl (%u v. bin_cat u n v) Int.Pls"

lemma [code]:
  "bin_rcat n = foldl (\<lambda>u v. bin_cat u n v) 0"
  by (simp add: bin_rcat_def Pls_def)

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "bin_rsplit_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split n c 
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list" where
  "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "bin_rsplitl_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split (min m n) c 
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list" where
  "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_sign_cat: 
  "!!y. bin_sign (bin_cat x n y) = bin_sign x"
  by (induct n) auto

lemma bin_cat_Suc_Bit:
  "bin_cat w (Suc n) (v BIT b) = bin_cat w n v BIT b"
  by auto

lemma bin_nth_cat: 
  "!!n y. bin_nth (bin_cat x k y) n = 
    (if n < k then bin_nth y n else bin_nth x (n - k))"
  apply (induct k)
   apply clarsimp
  apply (case_tac n, auto)
  done

lemma bin_nth_split:
  "!!b c. bin_split n c = (a, b) ==> 
    (ALL k. bin_nth a k = bin_nth c (n + k)) & 
    (ALL k. bin_nth b k = (k < n & bin_nth c k))"
  apply (induct n)
   apply clarsimp
  apply (clarsimp simp: Let_def split: ls_splits)
  apply (case_tac k)
  apply auto
  done

lemma bin_cat_assoc: 
  "!!z. bin_cat (bin_cat x m y) n z = bin_cat x (m + n) (bin_cat y n z)" 
  by (induct n) auto

lemma bin_cat_assoc_sym: "!!z m. 
  bin_cat x m (bin_cat y n z) = bin_cat (bin_cat x (m - n) y) (min m n) z"
  apply (induct n, clarsimp)
  apply (case_tac m, auto)
  done

lemma bin_cat_Pls [simp]: 
  "!!w. bin_cat Int.Pls n w = bintrunc n w"
  by (induct n) auto

lemma bintr_cat1: 
  "!!b. bintrunc (k + n) (bin_cat a n b) = bin_cat (bintrunc k a) n b"
  by (induct n) auto
    
lemma bintr_cat: "bintrunc m (bin_cat a n b) = 
    bin_cat (bintrunc (m - n) a) n (bintrunc (min m n) b)"
  by (rule bin_eqI) (auto simp: bin_nth_cat nth_bintr)
    
lemma bintr_cat_same [simp]: 
  "bintrunc n (bin_cat a n b) = bintrunc n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: 
  "!!b. bin_cat a n (bintrunc n b) = bin_cat a n b"
  by (induct n) auto

lemma split_bintrunc: 
  "!!b c. bin_split n c = (a, b) ==> b = bintrunc n c"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_cat_split:
  "!!v w. bin_split n w = (u, v) ==> w = bin_cat u n v"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_cat:
  "!!w. bin_split n (bin_cat v n w) = (v, bintrunc n w)"
  by (induct n) auto

lemma bin_split_Pls [simp]:
  "bin_split n Int.Pls = (Int.Pls, Int.Pls)"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_Min [simp]:
  "bin_split n Int.Min = (Int.Min, bintrunc n Int.Min)"
  by (induct n) (auto simp: Let_def split: ls_splits)

lemma bin_split_trunc:
  "!!m b c. bin_split (min m n) c = (a, b) ==> 
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, b)"
  apply (induct n, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: ls_splits)
  apply (case_tac m)
   apply (auto simp: Let_def split: ls_splits)
  done

lemma bin_split_trunc1:
  "!!m b c. bin_split n c = (a, b) ==> 
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, bintrunc m b)"
  apply (induct n, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: ls_splits)
  apply (case_tac m)
   apply (auto simp: Let_def split: ls_splits)
  done

lemma bin_cat_num:
  "!!b. bin_cat a n b = a * 2 ^ n + bintrunc n b"
  apply (induct n, clarsimp)
  apply (simp add: Bit_def cong: number_of_False_cong)
  done

lemma bin_split_num:
  "!!b. bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  apply (induct n, clarsimp)
  apply (simp add: bin_rest_def zdiv_zmult2_eq)
  apply (case_tac b rule: bin_exhaust)
  apply simp
  apply (simp add: Bit_def mod_mult_mult1 p1mod22k bitval_def
              split: bit.split 
              cong: number_of_False_cong)
  done 

subsection {* Miscellaneous lemmas *}

lemma nth_2p_bin: 
  "!!m. bin_nth (2 ^ n) m = (m = n)"
  apply (induct n)
   apply clarsimp
   apply safe
     apply (case_tac m) 
      apply (auto simp: trans [OF numeral_1_eq_1 [symmetric] number_of_eq])
   apply (case_tac m) 
    apply (auto simp: Bit_B0_2t [symmetric])
  done

(* for use when simplifying with bin_nth_Bit *)

lemma ex_eq_or:
  "(EX m. n = Suc m & (m = k | P m)) = (n = Suc k | (EX m. n = Suc m & P m))"
  by auto

end

