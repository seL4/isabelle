(*  Title:      HOL/Integ/Bin.ML
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
                David Spelt, University of Twente 
                Tobias Nipkow, Technical University Munich
    Copyright   1994  University of Cambridge
    Copyright   1996  University of Twente
    Copyright   1999  TU Munich

Arithmetic on binary integers;
decision procedure for linear arithmetic.
*)

(** extra rules for bin_succ, bin_pred, bin_add, bin_mult **)

Goal "NCons Pls False = Pls";
by (Simp_tac 1);
qed "NCons_Pls_0";

Goal "NCons Pls True = Pls BIT True";
by (Simp_tac 1);
qed "NCons_Pls_1";

Goal "NCons Min False = Min BIT False";
by (Simp_tac 1);
qed "NCons_Min_0";

Goal "NCons Min True = Min";
by (Simp_tac 1);
qed "NCons_Min_1";

Goal "bin_succ(w BIT True) = (bin_succ w) BIT False";
by (Simp_tac 1);
qed "bin_succ_1";

Goal "bin_succ(w BIT False) =  NCons w True";
by (Simp_tac 1);
qed "bin_succ_0";

Goal "bin_pred(w BIT True) = NCons w False";
by (Simp_tac 1);
qed "bin_pred_1";

Goal "bin_pred(w BIT False) = (bin_pred w) BIT True";
by (Simp_tac 1);
qed "bin_pred_0";

Goal "bin_minus(w BIT True) = bin_pred (NCons (bin_minus w) False)";
by (Simp_tac 1);
qed "bin_minus_1";

Goal "bin_minus(w BIT False) = (bin_minus w) BIT False";
by (Simp_tac 1);
qed "bin_minus_0";


(*** bin_add: binary addition ***)

Goal "bin_add (v BIT True) (w BIT True) = \
\    NCons (bin_add v (bin_succ w)) False";
by (Simp_tac 1);
qed "bin_add_BIT_11";

Goal "bin_add (v BIT True) (w BIT False) = NCons (bin_add v w) True";
by (Simp_tac 1);
qed "bin_add_BIT_10";

Goal "bin_add (v BIT False) (w BIT y) = NCons (bin_add v w) y";
by Auto_tac;
qed "bin_add_BIT_0";

Goal "bin_add w Pls = w";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_add_Pls_right";

Goal "bin_add w Min = bin_pred w";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_add_Min_right";

Goal "bin_add (v BIT x) (w BIT y) = \
\    NCons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)";
by (Simp_tac 1);
qed "bin_add_BIT_BIT";


(*** bin_mult: binary multiplication ***)

Goal "bin_mult (v BIT True) w = bin_add (NCons (bin_mult v w) False) w";
by (Simp_tac 1);
qed "bin_mult_1";

Goal "bin_mult (v BIT False) w = NCons (bin_mult v w) False";
by (Simp_tac 1);
qed "bin_mult_0";


(**** The carry/borrow functions, bin_succ and bin_pred ****)


(**** number_of ****)

Goal "number_of(NCons w b) = (number_of(w BIT b)::int)";
by (induct_tac "w" 1);
by (ALLGOALS Asm_simp_tac);
qed "number_of_NCons";

Addsimps [number_of_NCons];

Goal "number_of(bin_succ w) = int 1 + number_of w";
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "number_of_succ";

Goal "number_of(bin_pred w) = - (int 1) + number_of w";
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "number_of_pred";

Goal "number_of(bin_minus w) = (- (number_of w)::int)";
by (induct_tac "w" 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset()
		  delsimps [bin_pred_Pls, bin_pred_Min, bin_pred_BIT]
		  addsimps [number_of_succ,number_of_pred,
			    zadd_assoc]) 1);
qed "number_of_minus";

 
val bin_add_simps = [bin_add_BIT_BIT, number_of_succ, number_of_pred];

(*This proof is complicated by the mutual recursion*)
Goal "! w. number_of(bin_add v w) = (number_of v + number_of w::int)";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (rtac allI 1);
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps bin_add_simps @ zadd_ac)));
qed_spec_mp "number_of_add";


(*Subtraction*)
Goalw [zdiff_def]
     "number_of v - number_of w = (number_of(bin_add v (bin_minus w))::int)";
by (simp_tac (simpset() addsimps [number_of_add, number_of_minus]) 1);
qed "diff_number_of_eq";

val bin_mult_simps = [zmult_zminus, number_of_minus, number_of_add];

Goal "number_of(bin_mult v w) = (number_of v * number_of w::int)";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (asm_simp_tac
    (simpset() addsimps bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac) 1);
qed "number_of_mult";


(*The correctness of shifting.  But it doesn't seem to give a measurable
  speed-up.*)
Goal "(#2::int) * number_of w = number_of (w BIT False)";
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac
    (simpset() addsimps bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac)));
qed "double_number_of_BIT";


(** Simplification rules with integer constants **)

Goal "#0 + z = (z::int)";
by (Simp_tac 1);
qed "zadd_0";

Goal "z + #0 = (z::int)";
by (Simp_tac 1);
qed "zadd_0_right";

Addsimps [zadd_0, zadd_0_right];


(** Converting simple cases of (int n) to numerals **)

(*int 0 = #0 *)
bind_thm ("int_0", number_of_Pls RS sym);

Goal "int (Suc n) = #1 + int n";
by (simp_tac (simpset() addsimps [zadd_int]) 1);
qed "int_Suc";

Goal "- (#0) = (#0::int)";
by (Simp_tac 1);
qed "zminus_0";

Addsimps [zminus_0];


Goal "(#0::int) - x = -x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0";

Goal "x - (#0::int) = x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0_right";

Goal "x - x = (#0::int)";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_self";

Addsimps [zdiff0, zdiff0_right, zdiff_self];


(** Special simplification, for constants only **)

fun inst x t = read_instantiate_sg (sign_of Bin.thy) [(x,t)];

(*Distributive laws for literals*)
Addsimps (map (inst "w" "number_of ?v")
	  [zadd_zmult_distrib, zadd_zmult_distrib2,
	   zdiff_zmult_distrib, zdiff_zmult_distrib2]);

Addsimps (map (inst "x" "number_of ?v") 
	  [zless_zminus, zle_zminus, equation_zminus]);
Addsimps (map (inst "y" "number_of ?v") 
	  [zminus_zless, zminus_zle, zminus_equation]);

(*Moving negation out of products*)
Addsimps [zmult_zminus, zmult_zminus_right];

(** Special-case simplification for small constants **)

Goal "#0 * z = (#0::int)";
by (Simp_tac 1);
qed "zmult_0";

Goal "z * #0 = (#0::int)";
by (Simp_tac 1);
qed "zmult_0_right";

Goal "#1 * z = (z::int)";
by (Simp_tac 1);
qed "zmult_1";

Goal "z * #1 = (z::int)";
by (Simp_tac 1);
qed "zmult_1_right";

Goal "#-1 * z = -(z::int)";
by (simp_tac (simpset() addsimps zcompare_rls@[zmult_zminus]) 1);
qed "zmult_minus1";

Goal "z * #-1 = -(z::int)";
by (simp_tac (simpset() addsimps zcompare_rls@[zmult_zminus_right]) 1);
qed "zmult_minus1_right";

Addsimps [zmult_0, zmult_0_right, 
	  zmult_1, zmult_1_right,
	  zmult_minus1, zmult_minus1_right];

(*For specialist use: NOT as default simprules*)
Goal "#2 * z = (z+z::int)";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib]) 1);
qed "zmult_2";

Goal "z * #2 = (z+z::int)";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
qed "zmult_2_right";


(** Inequality reasoning **)

Goal "(m*n = (#0::int)) = (m = #0 | n = #0)";
by (stac (int_0 RS sym) 1 THEN rtac zmult_eq_int0_iff 1);
qed "zmult_eq_0_iff";

Goal "(w < z + (#1::int)) = (w<z | w=z)";
by (simp_tac (simpset() addsimps [zless_add_int_Suc_eq]) 1);
qed "zless_add1_eq";

Goal "(w + (#1::int) <= z) = (w<z)";
by (simp_tac (simpset() addsimps [add_int_Suc_zle_eq]) 1);
qed "add1_zle_eq";

Goal "((#1::int) + w <= z) = (w<z)";
by (stac zadd_commute 1);
by (rtac add1_zle_eq 1);
qed "add1_left_zle_eq";

Goal "neg x = (x < #0)";
by (simp_tac (simpset() addsimps [neg_eq_less_int0]) 1); 
qed "neg_eq_less_0"; 

Goal "(~neg x) = (#0 <= x)";
by (simp_tac (simpset() addsimps [not_neg_eq_ge_int0]) 1); 
qed "not_neg_eq_ge_0"; 

Goal "#0 <= int m";
by (Simp_tac 1);
qed "zero_zle_int";
AddIffs [zero_zle_int];


(** Needed because (int 0) rewrites to #0.
    Can these be generalized without evaluating large numbers?**)

Goal "~ (int k < #0)";
by (Simp_tac 1);
qed "int_less_0_conv";

Goal "(int k <= #0) = (k=0)";
by (Simp_tac 1);
qed "int_le_0_conv";

Goal "(int k = #0) = (k=0)";
by (Simp_tac 1);
qed "int_eq_0_conv";

Goal "(#0 = int k) = (k=0)";
by Auto_tac;
qed "int_eq_0_conv'";

Addsimps [int_less_0_conv, int_le_0_conv, int_eq_0_conv, int_eq_0_conv'];


(** Simplification rules for comparison of binary numbers (Norbert Voelker) **)

(** Equals (=) **)

Goalw [iszero_def]
  "((number_of x::int) = number_of y) = \
\  iszero (number_of (bin_add x (bin_minus y)))"; 
by (simp_tac (simpset() addsimps
              (zcompare_rls @ [number_of_add, number_of_minus])) 1); 
qed "eq_number_of_eq"; 

Goalw [iszero_def] "iszero ((number_of Pls)::int)"; 
by (Simp_tac 1); 
qed "iszero_number_of_Pls"; 

Goalw [iszero_def] "~ iszero ((number_of Min)::int)"; 
by (Simp_tac 1);
qed "nonzero_number_of_Min"; 

Goalw [iszero_def]
     "iszero (number_of (w BIT x)) = (~x & iszero (number_of w::int))"; 
by (Simp_tac 1);
by (int_case_tac "number_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps zcompare_rls @ 
				  [zminus_zadd_distrib RS sym, 
				   zadd_int]))); 
qed "iszero_number_of_BIT"; 

Goal "iszero (number_of (w BIT False)) = iszero (number_of w::int)"; 
by (simp_tac (HOL_ss addsimps [iszero_number_of_BIT]) 1); 
qed "iszero_number_of_0"; 

Goal "~ iszero (number_of (w BIT True)::int)"; 
by (simp_tac (HOL_ss addsimps [iszero_number_of_BIT]) 1); 
qed "iszero_number_of_1"; 



(** Less-than (<) **)

Goalw [zless_def,zdiff_def] 
    "(number_of x::int) < number_of y \
\    = neg (number_of (bin_add x (bin_minus y)))";
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
qed "less_number_of_eq_neg"; 

Goal "~ neg (number_of Pls)"; 
by (Simp_tac 1); 
qed "not_neg_number_of_Pls"; 

Goal "neg (number_of Min)"; 
by (Simp_tac 1);
qed "neg_number_of_Min"; 

Goal "neg (number_of (w BIT x)) = neg (number_of w)"; 
by (Asm_simp_tac 1); 
by (int_case_tac "number_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps [zadd_int, neg_eq_less_int0, 
				   symmetric zdiff_def] @ zcompare_rls))); 
qed "neg_number_of_BIT"; 


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::int)) = \
\     (~ number_of y < (number_of x::int))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_number_of_eq_not_less"; 

(*Delete the original rewrites, with their clumsy conditional expressions*)
Delsimps [bin_succ_BIT, bin_pred_BIT, bin_minus_BIT, 
          NCons_Pls, NCons_Min, bin_add_BIT, bin_mult_BIT];

(*Hide the binary representation of integer constants*)
Delsimps [number_of_Pls, number_of_Min, number_of_BIT];

(*simplification of arithmetic operations on integer constants*)
val bin_arith_extra_simps =
    [number_of_add RS sym,
     number_of_minus RS sym,
     number_of_mult RS sym,
     bin_succ_1, bin_succ_0, 
     bin_pred_1, bin_pred_0, 
     bin_minus_1, bin_minus_0,  
     bin_add_Pls_right, bin_add_Min_right,
     bin_add_BIT_0, bin_add_BIT_10, bin_add_BIT_11,
     diff_number_of_eq, 
     bin_mult_1, bin_mult_0, 
     NCons_Pls_0, NCons_Pls_1, 
     NCons_Min_0, NCons_Min_1, NCons_BIT];

(*For making a minimal simpset, one must include these default simprules
  of thy.  Also include simp_thms, or at least (~False)=True*)
val bin_arith_simps =
    [bin_pred_Pls, bin_pred_Min,
     bin_succ_Pls, bin_succ_Min,
     bin_add_Pls, bin_add_Min,
     bin_minus_Pls, bin_minus_Min,
     bin_mult_Pls, bin_mult_Min] @ bin_arith_extra_simps;

(*Simplification of relational operations*)
val bin_rel_simps =
    [eq_number_of_eq, iszero_number_of_Pls, nonzero_number_of_Min,
     iszero_number_of_0, iszero_number_of_1,
     less_number_of_eq_neg,
     not_neg_number_of_Pls, neg_number_of_Min, neg_number_of_BIT,
     le_number_of_eq_not_less];

Addsimps bin_arith_extra_simps;
Addsimps bin_rel_simps;


(** Constant folding inside parentheses **)

Goal "number_of v + (number_of w + c) = number_of(bin_add v w) + (c::int)";
by (stac (zadd_assoc RS sym) 1);
by (stac number_of_add 1);
by Auto_tac;
qed "nested_number_of_add";

Goalw [zdiff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::int)";
by (rtac nested_number_of_add 1);
qed "nested_diff1_number_of_add";

Goal "number_of v + (c - number_of w) = \
\    number_of (bin_add v (bin_minus w)) + (c::int)";
by (stac (diff_number_of_eq RS sym) 1);
by Auto_tac;
qed "nested_diff2_number_of_add";

Goal "number_of v * (number_of w * c) = number_of(bin_mult v w) * (c::int)";
by (stac (zmult_assoc RS sym) 1);
by (stac number_of_mult 1);
by Auto_tac;
qed "nested_number_of_mult";
Addsimps [nested_number_of_add, nested_diff1_number_of_add,
	  nested_diff2_number_of_add, nested_number_of_mult]; 

use "bin_simprocs";

(*---------------------------------------------------------------------------*)
(* Linear arithmetic                                                         *)
(*---------------------------------------------------------------------------*)

(*
Instantiation of the generic linear arithmetic package for int.
FIXME: multiplication with constants (eg #2 * i) does not work yet.
Solution: the cancellation simprocs in Int_Cancel should be able to deal with
it (eg simplify #3 * i <= 2 * i to i <= #0) or `add_rules' below should
include rules for turning multiplication with constants into addition.
(The latter option is very inefficient!)
*)

structure Int_LA_Data(*: LIN_ARITH_DATA*) =
struct

val lessD = Nat_LA_Data.lessD @ [add1_zle_eq RS iffD2];

(* reduce contradictory <= to False *)
val add_rules = simp_thms @ bin_arith_simps @ bin_rel_simps @
                [int_0,zmult_0,zmult_0_right];

val cancel_sums_ss = Nat_LA_Data.cancel_sums_ss addsimps add_rules
          addsimprocs [Int_Cancel.sum_conv, Int_Cancel.rel_conv,
                       Int_CC.sum_conv, Int_CC.rel_conv];

val simp = simplify cancel_sums_ss;

val add_mono_thms = Nat_LA_Data.add_mono_thms @
  map (fn s => prove_goal Int.thy s
                 (fn prems => [cut_facts_tac prems 1,
                      asm_simp_tac (simpset() addsimps [zadd_zle_mono]) 1]))
    ["(i <= j) & (k <= l) ==> i + k <= j + (l::int)",
     "(i  = j) & (k <= l) ==> i + k <= j + (l::int)",
     "(i <= j) & (k  = l) ==> i + k <= j + (l::int)",
     "(i  = j) & (k  = l) ==> i + k  = j + (l::int)"
    ];

end;

(* Update parameters of arithmetic prover *)
LA_Data_Ref.add_mono_thms := Int_LA_Data.add_mono_thms;
LA_Data_Ref.lessD :=         Int_LA_Data.lessD;
LA_Data_Ref.simp :=          Int_LA_Data.simp;
LA_Data_Ref.discrete := !LA_Data_Ref.discrete @ [("IntDef.int",true)];


val int_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of Int.thy) (s, HOLogic.boolT))
      ["(m::int) < n","(m::int) <= n", "(m::int) = n"];

val fast_int_arith_simproc = mk_simproc "fast_int_arith" int_arith_simproc_pats
                                        Fast_Arith.lin_arith_prover;

Addsimprocs [fast_int_arith_simproc];

(* FIXME: K true should be replaced by a sensible test to speed things up
   in case there are lots of irrelevant terms involved.

val arith_tac =
  refute_tac (K true) (REPEAT o split_tac[nat_diff_split])
             ((REPEAT_DETERM o etac linorder_neqE) THEN' fast_arith_tac);
*)

(* Some test data
Goal "!!a::int. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a-d+ #2 <= b+(-c)";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a+c+ #1 < b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b <= i+j; a<=b; i<=j |] \
\     ==> a+a <= j+j";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b < i+j; a<b; i<j |] \
\     ==> a+a - - #-1 < j+j - #3";
by (fast_arith_tac 1);
Goal "!!a::int. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
*)

(*---------------------------------------------------------------------------*)
(* End of linear arithmetic                                                  *)
(*---------------------------------------------------------------------------*)

(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::int)";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "add_number_of_left";

Goal "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::int)";
by (simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
qed "mult_number_of_left";

Addsimps [add_number_of_left, mult_number_of_left];

(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z + (#1::int)) = (w<=z | w = z + (#1::int))";
by (arith_tac 1);
qed "zle_add1_eq";

Goal "(w <= z - (#1::int)) = (w<(z::int))";
by (arith_tac 1);
qed "zle_diff1_eq";
Addsimps [zle_diff1_eq];

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w <= z; #0 <= v |] ==> w <= z + (v::int)";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd";

Goal "w <= z ==> w <= z + (#1::int)";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd1";

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w < z; #0 <= v |] ==> w < z + (v::int)";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd";

Goal "w < z ==> w < z + (#1::int)";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd1";

Goal "(w < z + #1) = (w<=(z::int))";
by (arith_tac 1);
qed "zle_add1_eq_le";
Addsimps [zle_add1_eq_le];

Goal "(z = z + w) = (w = (#0::int))";
by (arith_tac 1);
qed "zadd_left_cancel0";
Addsimps [zadd_left_cancel0];

(*LOOPS as a simprule!*)
Goal "[| w + v < z; #0 <= v |] ==> w < (z::int)";
by (fast_arith_tac 1);
qed "zless_zadd_imp_zless";

(*LOOPS as a simprule!  Analogous to Suc_lessD*)
Goal "w + #1 < z ==> w < (z::int)";
by (fast_arith_tac 1);
qed "zless_zadd1_imp_zless";

Goal "w + #-1 = w - (#1::int)";
by (Simp_tac 1);
qed "zplus_minus1_conv";


(*** nat ***)

Goal "#0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z <= #0 ==> nat z = 0"; 
by (case_tac "z = #0" 1);
by (asm_simp_tac (simpset() addsimps [nat_le_int0]) 1); 
by (asm_full_simp_tac 
    (simpset() addsimps [neg_eq_less_0, neg_nat, linorder_neq_iff]) 1);
qed "nat_le_0"; 

Addsimps [nat_0_le, nat_le_0];

val [major,minor] = Goal "[| #0 <= z;  !!m. z = int m ==> P |] ==> P"; 
by (rtac (major RS nat_0_le RS sym RS minor) 1);
qed "nonneg_eq_int"; 

Goal "#0 <= w ==> (nat w = m) = (w = int m)";
by Auto_tac;
qed "nat_eq_iff";

Goal "#0 <= w ==> (nat w < m) = (w < int m)";
by (rtac iffI 1);
by (asm_full_simp_tac 
    (simpset() delsimps [zless_int] addsimps [zless_int RS sym]) 2);
by (etac (nat_0_le RS subst) 1);
by (Simp_tac 1);
qed "nat_less_iff";


(*Users don't want to see (int 0), int(Suc 0) or w + - z*)
Addsimps [int_0, int_Suc, symmetric zdiff_def];

Goal "nat #0 = 0";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_0";

Goal "nat #1 = 1";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_1";

Goal "nat #2 = 2";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_2";

Goal "#0 <= w ==> (nat w < nat z) = (w<z)";
by (case_tac "neg z" 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
by (auto_tac (claset() addIs [zless_trans], 
	      simpset() addsimps [neg_eq_less_0, zle_def]));
qed "nat_less_eq_zless";

Goal "#0 < w | #0 <= z ==> (nat w <= nat z) = (w<=z)";
by (auto_tac (claset(), 
	      simpset() addsimps [linorder_not_less RS sym, 
				  zless_nat_conj]));
qed "nat_le_eq_zle";

(*Analogous to zadd_int, but more easily provable using the arithmetic in Bin*)
Goal "n<=m --> int m - int n = int (m-n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by Auto_tac;
qed_spec_mp "zdiff_int";


(** Products of signs **)

Goal "(m::int) < #0 ==> (#0 < m*n) = (n < #0)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1_neg], simpset()) 2);
by (eres_inst_tac [("P", "#0 < m * n")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [inst "k" "m" zmult_zless_mono1_neg], 
	       simpset()addsimps [order_le_less, zmult_commute]) 1);
qed "neg_imp_zmult_pos_iff";

Goal "(m::int) < #0 ==> (m*n < #0) = (#0 < n)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1], simpset()) 2);
by (eres_inst_tac [("P", "m * n < #0")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [zmult_zless_mono1_neg], 
	       simpset() addsimps [order_le_less]) 1);
qed "neg_imp_zmult_neg_iff";

Goal "#0 < (m::int) ==> (m*n < #0) = (n < #0)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1_neg], simpset()) 2);
by (eres_inst_tac [("P", "m * n < #0")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [zmult_zless_mono1], 
	       simpset() addsimps [order_le_less]) 1);
qed "pos_imp_zmult_neg_iff";

Goal "#0 < (m::int) ==> (#0 < m*n) = (#0 < n)";
by Auto_tac;
by (force_tac (claset() addDs [zmult_zless_mono1], simpset()) 2);
by (eres_inst_tac [("P", "#0 < m * n")] rev_mp 1);
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (force_tac (claset() addDs [inst "k" "m" zmult_zless_mono1], 
	       simpset() addsimps [order_le_less, zmult_commute]) 1);
qed "pos_imp_zmult_pos_iff";

(** <= versions of the theorems above **)

Goal "(m::int) < #0 ==> (m*n <= #0) = (#0 <= n)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      neg_imp_zmult_pos_iff]) 1);
qed "neg_imp_zmult_nonpos_iff";

Goal "(m::int) < #0 ==> (#0 <= m*n) = (n <= #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      neg_imp_zmult_neg_iff]) 1);
qed "neg_imp_zmult_nonneg_iff";

Goal "#0 < (m::int) ==> (m*n <= #0) = (n <= #0)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      pos_imp_zmult_pos_iff]) 1);
qed "pos_imp_zmult_nonpos_iff";

Goal "#0 < (m::int) ==> (#0 <= m*n) = (#0 <= n)";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym,
				      pos_imp_zmult_neg_iff]) 1);
qed "pos_imp_zmult_nonneg_iff";
