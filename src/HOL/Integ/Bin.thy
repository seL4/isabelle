(*  Title:	HOL/Integ/Bin.thy
    ID:         $Id$
    Authors:	Lawrence C Paulson, Cambridge University Computer Laboratory
		David Spelt, University of Twente
    Copyright	1994  University of Cambridge
    Copyright   1996 University of Twente
*)

header{*Arithmetic on Binary Integers*}

theory Bin = IntDef + Numeral:

text{*The sign @{term Pls} stands for an infinite string of leading Falses.*}
text{*The sign @{term Min} stands for an infinite string of leading Trues.*}

text{*A number can have multiple representations, namely leading Falses with
sign @{term Pls} and leading Trues with sign @{term Min}.
See @{text "ZF/Integ/twos-compl.ML"}, function @{text int_of_binary},
for the numerical interpretation.

The representation expects that @{term "(m mod 2)"} is 0 or 1,
even if m is negative;
For instance, @{term "-5 div 2 = -3"} and @{term "-5 mod 2 = 1"}; thus
@{term "-5 = (-3)*2 + 1"}.
*}

consts
  NCons     :: "[bin,bool]=>bin"
  bin_succ  :: "bin=>bin"
  bin_pred  :: "bin=>bin"
  bin_minus :: "bin=>bin"
  bin_add   :: "[bin,bin]=>bin"
  bin_mult  :: "[bin,bin]=>bin"

(*NCons inserts a bit, suppressing leading 0s and 1s*)
primrec
  NCons_Pls:  "NCons bin.Pls b = (if b then (bin.Pls BIT b) else bin.Pls)"
  NCons_Min:  "NCons bin.Min b = (if b then bin.Min else (bin.Min BIT b))"
  NCons_BIT:  "NCons (w BIT x) b = (w BIT x) BIT b"

instance
  int :: number ..

primrec (*the type constraint is essential!*)
  number_of_Pls: "number_of bin.Pls = 0"
  number_of_Min: "number_of bin.Min = - (1::int)"
  number_of_BIT: "number_of(w BIT x) = (if x then 1 else 0) +
	                               (number_of w) + (number_of w)"

primrec
  bin_succ_Pls: "bin_succ bin.Pls = bin.Pls BIT True"
  bin_succ_Min: "bin_succ bin.Min = bin.Pls"
  bin_succ_BIT: "bin_succ(w BIT x) =
  	            (if x then bin_succ w BIT False
	                  else NCons w True)"

primrec
  bin_pred_Pls: "bin_pred bin.Pls = bin.Min"
  bin_pred_Min: "bin_pred bin.Min = bin.Min BIT False"
  bin_pred_BIT: "bin_pred(w BIT x) =
	            (if x then NCons w False
		          else (bin_pred w) BIT True)"

primrec
  bin_minus_Pls: "bin_minus bin.Pls = bin.Pls"
  bin_minus_Min: "bin_minus bin.Min = bin.Pls BIT True"
  bin_minus_BIT: "bin_minus(w BIT x) =
	             (if x then bin_pred (NCons (bin_minus w) False)
		           else bin_minus w BIT False)"

primrec
  bin_add_Pls: "bin_add bin.Pls w = w"
  bin_add_Min: "bin_add bin.Min w = bin_pred w"
  bin_add_BIT:
    "bin_add (v BIT x) w =
       (case w of Pls => v BIT x
                | Min => bin_pred (v BIT x)
                | (w BIT y) =>
      	            NCons (bin_add v (if (x & y) then bin_succ w else w))
	                  (x~=y))"

primrec
  bin_mult_Pls: "bin_mult bin.Pls w = bin.Pls"
  bin_mult_Min: "bin_mult bin.Min w = bin_minus w"
  bin_mult_BIT: "bin_mult (v BIT x) w =
	            (if x then (bin_add (NCons (bin_mult v w) False) w)
	                  else (NCons (bin_mult v w) False))"


(** extra rules for bin_succ, bin_pred, bin_add, bin_mult **)

lemma NCons_Pls_0: "NCons bin.Pls False = bin.Pls"
by simp

lemma NCons_Pls_1: "NCons bin.Pls True = bin.Pls BIT True"
by simp

lemma NCons_Min_0: "NCons bin.Min False = bin.Min BIT False"
by simp

lemma NCons_Min_1: "NCons bin.Min True = bin.Min"
by simp

lemma bin_succ_1: "bin_succ(w BIT True) = (bin_succ w) BIT False"
by simp

lemma bin_succ_0: "bin_succ(w BIT False) =  NCons w True"
by simp

lemma bin_pred_1: "bin_pred(w BIT True) = NCons w False"
by simp

lemma bin_pred_0: "bin_pred(w BIT False) = (bin_pred w) BIT True"
by simp

lemma bin_minus_1: "bin_minus(w BIT True) = bin_pred (NCons (bin_minus w) False)"
by simp

lemma bin_minus_0: "bin_minus(w BIT False) = (bin_minus w) BIT False"
by simp


(*** bin_add: binary addition ***)

lemma bin_add_BIT_11: "bin_add (v BIT True) (w BIT True) =
     NCons (bin_add v (bin_succ w)) False"
apply simp
done

lemma bin_add_BIT_10: "bin_add (v BIT True) (w BIT False) = NCons (bin_add v w) True"
by simp

lemma bin_add_BIT_0: "bin_add (v BIT False) (w BIT y) = NCons (bin_add v w) y"
by auto

lemma bin_add_Pls_right: "bin_add w bin.Pls = w"
by (induct_tac "w", auto)

lemma bin_add_Min_right: "bin_add w bin.Min = bin_pred w"
by (induct_tac "w", auto)

lemma bin_add_BIT_BIT: "bin_add (v BIT x) (w BIT y) =
     NCons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
apply simp
done


(*** bin_mult: binary multiplication ***)

lemma bin_mult_1: "bin_mult (v BIT True) w = bin_add (NCons (bin_mult v w) False) w"
by simp

lemma bin_mult_0: "bin_mult (v BIT False) w = NCons (bin_mult v w) False"
by simp


(**** The carry/borrow functions, bin_succ and bin_pred ****)


(** number_of **)

lemma number_of_NCons [simp]:
     "number_of(NCons w b) = (number_of(w BIT b)::int)"
apply (induct_tac "w")
apply (simp_all)
done

lemma number_of_succ: "number_of(bin_succ w) = (1 + number_of w :: int)"
apply (induct_tac "w")
apply (simp_all add: zadd_ac)
done

lemma number_of_pred: "number_of(bin_pred w) = (- 1 + number_of w :: int)"
apply (induct_tac "w")
apply (simp_all add: add_assoc [symmetric]) 
apply (simp add: zadd_ac)
done

lemma number_of_minus: "number_of(bin_minus w) = (- (number_of w)::int)"
apply (induct_tac "w", simp, simp)
apply (simp del: bin_pred_Pls bin_pred_Min bin_pred_BIT add: number_of_succ number_of_pred zadd_assoc)
done

(*This proof is complicated by the mutual recursion*)
lemma number_of_add [rule_format (no_asm)]: "! w. number_of(bin_add v w) = (number_of v + number_of w::int)"
apply (induct_tac "v", simp)
apply (simp add: number_of_pred)
apply (rule allI)
apply (induct_tac "w")
apply (simp_all add: bin_add_BIT_BIT number_of_succ number_of_pred add_ac)
apply (simp add: add_left_commute [of "1::int"]) 
done


(*Subtraction*)
lemma diff_number_of_eq:
     "number_of v - number_of w = (number_of(bin_add v (bin_minus w))::int)"
apply (unfold zdiff_def)
apply (simp add: number_of_add number_of_minus)
done

lemmas bin_mult_simps = 
       int_Suc0_eq_1 zmult_zminus number_of_minus number_of_add

lemma number_of_mult: "number_of(bin_mult v w) = (number_of v * number_of w::int)"
apply (induct_tac "v")
apply (simp add: bin_mult_simps)
apply (simp add: bin_mult_simps)
apply (simp add: bin_mult_simps zadd_zmult_distrib zadd_ac)
done


(*The correctness of shifting.  But it doesn't seem to give a measurable
  speed-up.*)
lemma double_number_of_BIT: "(2::int) * number_of w = number_of (w BIT False)"
apply (induct_tac "w")
apply (simp_all add: bin_mult_simps zadd_zmult_distrib zadd_ac)
done


(** Converting numerals 0 and 1 to their abstract versions **)

lemma int_numeral_0_eq_0: "Numeral0 = (0::int)"
by simp

lemma int_numeral_1_eq_1: "Numeral1 = (1::int)"
by (simp add: int_1 int_Suc0_eq_1)

(*Moving negation out of products: so far for type "int" only*)
declare zmult_zminus [simp] zmult_zminus_right [simp]


(** Special-case simplification for small constants **)

lemma zmult_minus1 [simp]: "-1 * z = -(z::int)"
by (simp add: compare_rls int_Suc0_eq_1 zmult_zminus)

lemma zmult_minus1_right [simp]: "z * -1 = -(z::int)"
by (subst zmult_commute, rule zmult_minus1)


(*Negation of a coefficient*)
lemma zminus_number_of_zmult [simp]: "- (number_of w) * z = number_of(bin_minus w) * (z::int)"
by (simp add: number_of_minus zmult_zminus)

(*Integer unary minus for the abstract constant 1. Cannot be inserted
  as a simprule until later: it is number_of_Min re-oriented!*)
lemma zminus_1_eq_m1: "- 1 = (-1::int)"
by simp

lemma zero_less_nat_eq [simp]: "(0 < nat z) = (0 < z)"
by (cut_tac w = 0 in zless_nat_conj, auto)


(** Simplification rules for comparison of binary numbers (Norbert Voelker) **)

(** Equals (=) **)

lemma eq_number_of_eq:
  "((number_of x::int) = number_of y) =
   iszero (number_of (bin_add x (bin_minus y)) :: int)"
apply (unfold iszero_def)
apply (simp add: compare_rls number_of_add number_of_minus)
done

lemma iszero_number_of_Pls: "iszero ((number_of bin.Pls)::int)"
by (unfold iszero_def, simp)

lemma nonzero_number_of_Min: "~ iszero ((number_of bin.Min)::int)"
apply (unfold iszero_def)
apply (simp add: eq_commute)
done

lemma iszero_number_of_BIT:
     "iszero (number_of (w BIT x)::int) = (~x & iszero (number_of w::int))"
apply (unfold iszero_def)
apply (cases "(number_of w)::int" rule: int_cases) 
apply (simp_all (no_asm_simp) add: compare_rls zero_reorient
         zminus_zadd_distrib [symmetric] int_Suc0_eq_1 [symmetric] zadd_int)
done

lemma iszero_number_of_0:
     "iszero (number_of (w BIT False)::int) = iszero (number_of w::int)"
by (simp only: iszero_number_of_BIT simp_thms)

lemma iszero_number_of_1: "~ iszero (number_of (w BIT True)::int)"
by (simp only: iszero_number_of_BIT simp_thms)



(** Less-than (<) **)

lemma less_number_of_eq_neg:
    "((number_of x::int) < number_of y)
     = neg (number_of (bin_add x (bin_minus y)) ::int )"
by (simp add: neg_def number_of_add number_of_minus compare_rls) 


(*But if Numeral0 is rewritten to 0 then this rule can't be applied:
  Numeral0 IS (number_of Pls) *)
lemma not_neg_number_of_Pls: "~ neg (number_of bin.Pls ::int)"
by (simp add: neg_def)

lemma neg_number_of_Min: "neg (number_of bin.Min ::int)"
by (simp add: neg_def int_0_less_1)

lemma neg_number_of_BIT:
     "neg (number_of (w BIT x)::int) = neg (number_of w ::int)"
apply simp
apply (cases "(number_of w)::int" rule: int_cases) 
apply (simp_all (no_asm_simp) add: int_Suc0_eq_1 [symmetric] zadd_int neg_def zdiff_def [symmetric] compare_rls)
done


(** Less-than-or-equals (\<le>) **)

text{*Reduces @{term "a\<le>b"} to @{term "~ (b<a)"} for ALL numerals*}
lemmas le_number_of_eq_not_less =
       linorder_not_less [of "number_of w" "number_of v", symmetric, standard]

declare le_number_of_eq_not_less [simp]


(** Absolute value (abs) **)

lemma zabs_number_of:
 "abs(number_of x::int) =
  (if number_of x < (0::int) then -number_of x else number_of x)"
by (simp add: zabs_def)

(*0 and 1 require special rewrites because they aren't numerals*)
lemma zabs_0: "abs (0::int) = 0"
by (simp add: zabs_def)

lemma zabs_1: "abs (1::int) = 1"
by (simp del: int_0 int_1 add: int_0 [symmetric] int_1 [symmetric] zabs_def)

(*Re-orientation of the equation nnn=x*)
lemma number_of_reorient: "(number_of w = x) = (x = number_of w)"
by auto


(*Delete the original rewrites, with their clumsy conditional expressions*)
declare bin_succ_BIT [simp del] bin_pred_BIT [simp del]
        bin_minus_BIT [simp del]

declare bin_add_BIT [simp del] bin_mult_BIT [simp del]
declare NCons_Pls [simp del] NCons_Min [simp del]

(*Hide the binary representation of integer constants*)
declare number_of_Pls [simp del] number_of_Min [simp del]
        number_of_BIT [simp del]



(*Simplification of arithmetic operations on integer constants.
  Note that bin_pred_Pls, etc. were added to the simpset by primrec.*)

lemmas NCons_simps = NCons_Pls_0 NCons_Pls_1 NCons_Min_0 NCons_Min_1 NCons_BIT

lemmas bin_arith_extra_simps = 
       number_of_add [symmetric]
       number_of_minus [symmetric] zminus_1_eq_m1
       number_of_mult [symmetric]
       bin_succ_1 bin_succ_0
       bin_pred_1 bin_pred_0
       bin_minus_1 bin_minus_0
       bin_add_Pls_right bin_add_Min_right
       bin_add_BIT_0 bin_add_BIT_10 bin_add_BIT_11
       diff_number_of_eq zabs_number_of zabs_0 zabs_1
       bin_mult_1 bin_mult_0 NCons_simps

(*For making a minimal simpset, one must include these default simprules
  of thy.  Also include simp_thms, or at least (~False)=True*)
lemmas bin_arith_simps = 
       bin_pred_Pls bin_pred_Min
       bin_succ_Pls bin_succ_Min
       bin_add_Pls bin_add_Min
       bin_minus_Pls bin_minus_Min
       bin_mult_Pls bin_mult_Min bin_arith_extra_simps

(*Simplification of relational operations*)
lemmas bin_rel_simps = 
       eq_number_of_eq iszero_number_of_Pls nonzero_number_of_Min
       iszero_number_of_0 iszero_number_of_1
       less_number_of_eq_neg
       not_neg_number_of_Pls not_neg_0 not_neg_1 not_iszero_1
       neg_number_of_Min neg_number_of_BIT
       le_number_of_eq_not_less

declare bin_arith_extra_simps [simp]
declare bin_rel_simps [simp]


(** Simplification of arithmetic when nested to the right **)

lemma add_number_of_left [simp]: "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::int)"
by (simp add: zadd_assoc [symmetric])

lemma mult_number_of_left [simp]: "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::int)"
by (simp add: zmult_assoc [symmetric])

lemma add_number_of_diff1:
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::int)"
apply (unfold zdiff_def)
apply (rule add_number_of_left)
done

lemma add_number_of_diff2 [simp]: "number_of v + (c - number_of w) =
     number_of (bin_add v (bin_minus w)) + (c::int)"
apply (subst diff_number_of_eq [symmetric])
apply (simp only: compare_rls)
done



(** Inserting these natural simprules earlier would break many proofs! **)

(* int (Suc n) = 1 + int n *)
declare int_Suc [simp]

(* Numeral0 -> 0 and Numeral1 -> 1 *)
declare int_numeral_0_eq_0 [simp] int_numeral_1_eq_1 [simp]


(*Simplification of  x-y < 0, etc.*)
declare less_iff_diff_less_0 [symmetric, simp]
declare eq_iff_diff_eq_0 [symmetric, simp]
declare le_iff_diff_le_0 [symmetric, simp]


end
