(*  Title:      HOL/Integ/Bin.ML
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

qed_goal "NCons_Pls_0" Bin.thy
    "NCons Pls False = Pls"
 (fn _ => [(Simp_tac 1)]);

qed_goal "NCons_Pls_1" Bin.thy
    "NCons Pls True = Pls BIT True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "NCons_Min_0" Bin.thy
    "NCons Min False = Min BIT False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "NCons_Min_1" Bin.thy
    "NCons Min True = Min"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_1" Bin.thy
    "bin_succ(w BIT True) = (bin_succ w) BIT False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_succ_0" Bin.thy
    "bin_succ(w BIT False) =  NCons w True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_1" Bin.thy
    "bin_pred(w BIT True) = NCons w False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_pred_0" Bin.thy
    "bin_pred(w BIT False) = (bin_pred w) BIT True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_1" Bin.thy
    "bin_minus(w BIT True) = bin_pred (NCons (bin_minus w) False)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_minus_0" Bin.thy
    "bin_minus(w BIT False) = (bin_minus w) BIT False"
 (fn _ => [(Simp_tac 1)]);


(*** bin_add: binary addition ***)

qed_goal "bin_add_BIT_11" Bin.thy
    "bin_add (v BIT True) (w BIT True) = \
\    NCons (bin_add v (bin_succ w)) False"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_BIT_10" Bin.thy
    "bin_add (v BIT True) (w BIT False) = NCons (bin_add v w) True"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_BIT_0" Bin.thy
    "bin_add (v BIT False) (w BIT y) = NCons (bin_add v w) y"
 (fn _ => [Auto_tac]);

Goal "bin_add w Pls = w";
by (induct_tac "w" 1);
by Auto_tac;
qed "bin_add_Pls_right";

qed_goal "bin_add_BIT_Min" Bin.thy
    "bin_add (v BIT x) Min = bin_pred (v BIT x)"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_add_BIT_BIT" Bin.thy
    "bin_add (v BIT x) (w BIT y) = \
\    NCons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
 (fn _ => [(Simp_tac 1)]);


(*** bin_mult: binary multiplication ***)

qed_goal "bin_mult_1" Bin.thy
    "bin_mult (v BIT True) w = bin_add (NCons (bin_mult v w) False) w"
 (fn _ => [(Simp_tac 1)]);

qed_goal "bin_mult_0" Bin.thy
    "bin_mult (v BIT False) w = NCons (bin_mult v w) False"
 (fn _ => [(Simp_tac 1)]);


(**** The carry/borrow functions, bin_succ and bin_pred ****)


(**** integ_of ****)

qed_goal "integ_of_NCons" Bin.thy
    "integ_of(NCons w b) = integ_of(w BIT b)"
 (fn _ =>[(induct_tac "w" 1),
          (ALLGOALS Asm_simp_tac) ]);

Addsimps [integ_of_NCons];

qed_goal "integ_of_succ" Bin.thy
    "integ_of(bin_succ w) = int 1 + integ_of w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac (simpset() addsimps zadd_ac))) ]);

qed_goal "integ_of_pred" Bin.thy
    "integ_of(bin_pred w) = - (int 1) + integ_of w"
 (fn _ =>[(rtac bin.induct 1),
          (ALLGOALS(asm_simp_tac (simpset() addsimps zadd_ac))) ]);

Goal "integ_of(bin_minus w) = - (integ_of w)";
by (rtac bin.induct 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset()
		  delsimps [bin_pred_Pls, bin_pred_Min, bin_pred_BIT]
		  addsimps [integ_of_succ,integ_of_pred,
			    zadd_assoc]) 1);
qed "integ_of_minus";

 
val bin_add_simps = [bin_add_BIT_BIT, integ_of_succ, integ_of_pred];

(*This proof is complicated by the mutual recursion*)
Goal "! w. integ_of(bin_add v w) = integ_of v + integ_of w";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (simp_tac (simpset() addsimps bin_add_simps) 1);
by (rtac allI 1);
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps bin_add_simps @ zadd_ac)));
qed_spec_mp "integ_of_add";


(*Subtraction*)
Goalw [zdiff_def]
     "integ_of v - integ_of w = integ_of(bin_add v (bin_minus w))";
by (simp_tac (simpset() addsimps [integ_of_add, integ_of_minus]) 1);
qed "diff_integ_of_eq";

val bin_mult_simps = [zmult_zminus, integ_of_minus, integ_of_add];

Goal "integ_of(bin_mult v w) = integ_of v * integ_of w";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (asm_simp_tac
    (simpset() addsimps bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac) 1);
qed "integ_of_mult";


(** Simplification rules with integer constants **)

Goal "#0 + z = z";
by (Simp_tac 1);
qed "zadd_0";

Goal "z + #0 = z";
by (Simp_tac 1);
qed "zadd_0_right";

Addsimps [zadd_0, zadd_0_right];


(** Converting simple cases of (int n) to numerals **)

(*int 0 = #0 *)
bind_thm ("int_0", integ_of_Pls RS sym);

Goal "int (Suc n) = #1 + int n";
by (simp_tac (simpset() addsimps [zadd_int]) 1);
qed "int_Suc";

Goal "- (#0) = #0";
by (Simp_tac 1);
qed "zminus_0";

Addsimps [zminus_0];


Goal "#0 - x = -x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0";

Goal "x - #0 = x";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff0_right";

Goal "x - x = #0";
by (simp_tac (simpset() addsimps [zdiff_def]) 1);
qed "zdiff_self";

Addsimps [zdiff0, zdiff0_right, zdiff_self];

Goal "#0 * z = #0";
by (Simp_tac 1);
qed "zmult_0";

Goal "#1 * z = z";
by (Simp_tac 1);
qed "zmult_1";

Goal "#2 * z = z+z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib]) 1);
qed "zmult_2";

Goal "z * #0 = #0";
by (Simp_tac 1);
qed "zmult_0_right";

Goal "z * #1 = z";
by (Simp_tac 1);
qed "zmult_1_right";

Goal "z * #2 = z+z";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib2]) 1);
qed "zmult_2_right";

Addsimps [zmult_0, zmult_0_right, 
	  zmult_1, zmult_1_right, 
	  zmult_2, zmult_2_right];

Goal "(w < z + #1) = (w<z | w=z)";
by (simp_tac (simpset() addsimps [zless_add_int_Suc_eq]) 1);
qed "zless_add1_eq";

Goal "(w + #1 <= z) = (w<z)";
by (simp_tac (simpset() addsimps [add_int_Suc_zle_eq]) 1);
qed "add1_zle_eq";
Addsimps [add1_zle_eq];

Goal "neg x = (x < #0)";
by (simp_tac (simpset() addsimps [neg_eq_less_nat0]) 1); 
qed "neg_eq_less_0"; 

Goal "(~neg x) = (int 0 <= x)";
by (simp_tac (simpset() addsimps [not_neg_eq_ge_nat0]) 1); 
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
  "(integ_of x = integ_of y) = iszero(integ_of (bin_add x (bin_minus y)))"; 
by (simp_tac (simpset() addsimps
              (zcompare_rls @ [integ_of_add, integ_of_minus])) 1); 
qed "eq_integ_of_eq"; 

Goalw [iszero_def] "iszero (integ_of Pls)"; 
by (Simp_tac 1); 
qed "iszero_integ_of_Pls"; 

Goalw [iszero_def] "~ iszero(integ_of Min)"; 
by (Simp_tac 1);
qed "nonzero_integ_of_Min"; 

Goalw [iszero_def]
     "iszero (integ_of (w BIT x)) = (~x & iszero (integ_of w))"; 
by (Simp_tac 1);
by (int_case_tac "integ_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps zcompare_rls @ 
				  [zminus_zadd_distrib RS sym, 
				   zadd_int]))); 
qed "iszero_integ_of_BIT"; 

Goal "iszero (integ_of (w BIT False)) = iszero (integ_of w)"; 
by (simp_tac (HOL_ss addsimps [iszero_integ_of_BIT]) 1); 
qed "iszero_integ_of_0"; 

Goal "~ iszero (integ_of (w BIT True))"; 
by (simp_tac (HOL_ss addsimps [iszero_integ_of_BIT]) 1); 
qed "iszero_integ_of_1"; 



(** Less-than (<) **)

Goalw [zless_def,zdiff_def] 
    "integ_of x < integ_of y \
\    = neg (integ_of (bin_add x (bin_minus y)))";
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
qed "less_integ_of_eq_neg"; 

Goal "~ neg (integ_of Pls)"; 
by (Simp_tac 1); 
qed "not_neg_integ_of_Pls"; 

Goal "neg (integ_of Min)"; 
by (Simp_tac 1);
qed "neg_integ_of_Min"; 

Goal "neg (integ_of (w BIT x)) = neg (integ_of w)"; 
by (Asm_simp_tac 1); 
by (int_case_tac "integ_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps [zadd_int, neg_eq_less_nat0, 
				   symmetric zdiff_def] @ zcompare_rls))); 
qed "neg_integ_of_BIT"; 


(** Less-than-or-equals (<=) **)

Goal "(integ_of x <= integ_of y) = (~ integ_of y < integ_of x)";
by (simp_tac (simpset() addsimps [zle_def]) 1);
qed "le_integ_of_eq_not_less"; 

(*Delete the original rewrites, with their clumsy conditional expressions*)
Delsimps [bin_succ_BIT, bin_pred_BIT, bin_minus_BIT, 
          NCons_Pls, NCons_Min, bin_add_BIT, bin_mult_BIT];

(*Hide the binary representation of integer constants*)
Delsimps [integ_of_Pls, integ_of_Min, integ_of_BIT];

(*simplification of arithmetic operations on integer constants*)
val bin_arith_extra_simps =
    [integ_of_add RS sym,
     integ_of_minus RS sym,
     integ_of_mult RS sym,
     bin_succ_1, bin_succ_0, 
     bin_pred_1, bin_pred_0, 
     bin_minus_1, bin_minus_0,  
     bin_add_Pls_right, bin_add_BIT_Min,
     bin_add_BIT_0, bin_add_BIT_10, bin_add_BIT_11,
     diff_integ_of_eq, 
     bin_mult_1, bin_mult_0, 
     NCons_Pls_0, NCons_Pls_1, 
     NCons_Min_0, NCons_Min_1, NCons_BIT];

(*For making a minimal simpset, one must include these default simprules
  of Bin.thy.  Also include simp_thms, or at least (~False)=True*)
val bin_arith_simps =
    [bin_pred_Pls, bin_pred_Min,
     bin_succ_Pls, bin_succ_Min,
     bin_add_Pls, bin_add_Min,
     bin_minus_Pls, bin_minus_Min,
     bin_mult_Pls, bin_mult_Min] @ bin_arith_extra_simps;

(*Simplification of relational operations*)
val bin_rel_simps =
    [eq_integ_of_eq, iszero_integ_of_Pls, nonzero_integ_of_Min,
     iszero_integ_of_0, iszero_integ_of_1,
     less_integ_of_eq_neg,
     not_neg_integ_of_Pls, neg_integ_of_Min, neg_integ_of_BIT,
     le_integ_of_eq_not_less];

Addsimps bin_arith_extra_simps;
Addsimps bin_rel_simps;

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

(* borrowed from Bin.thy: *)
fun dest_bit (Const ("False", _)) = 0
  | dest_bit (Const ("True", _)) = 1
  | dest_bit _ = raise Match;

fun dest_bin tm =
  let
    fun bin_of (Const ("Bin.bin.Pls", _)) = []
      | bin_of (Const ("Bin.bin.Min", _)) = [~1]
      | bin_of (Const ("Bin.bin.op BIT", _) $ bs $ b) = dest_bit b :: bin_of bs
      | bin_of _ = raise Match;

    fun int_of [] = 0
      | int_of (b :: bs) = b + 2 * int_of bs;

  in int_of(bin_of tm) end;

fun add_atom(t,m,(p,i)) = (case assoc(p,t) of None => ((t,m)::p,i)
                           | Some n => (overwrite(p,(t,n+m:int)), i));

(* Turn term into list of summand * multiplicity plus a constant *)
fun poly(Const("op +",_) $ s $ t, m, pi) = poly(s,m,poly(t,m,pi))
  | poly(Const("op -",_) $ s $ t, m, pi) = poly(s,m,poly(t,~1*m,pi))
  | poly(Const("uminus",_) $ t, m, pi) =   poly(t,~1*m,pi)
  | poly(all as Const("op *",_) $ (Const("Bin.integ_of",_)$c) $ t, m, pi) =
      (poly(t,m*dest_bin c,pi) handle Match => add_atom(all,m,pi))
  | poly(all as Const("Bin.integ_of",_)$t,m,(p,i)) =
     ((p,i + m*dest_bin t) handle Match => add_atom(all,m,(p,i)))
  | poly x  = add_atom x;

fun decomp2(rel,lhs,rhs) =
  let val (p,i) = poly(lhs,1,([],0)) and (q,j) = poly(rhs,1,([],0))
  in case rel of
       "op <"  => Some(p,i,"<",q,j)
     | "op <=" => Some(p,i,"<=",q,j)
     | "op ="  => Some(p,i,"=",q,j)
     | _       => None
  end;

val intT = Type("IntDef.int",[]);
fun iib T = T = ([intT,intT] ---> HOLogic.boolT);

fun decomp1(T,xxx) =
  if iib T then decomp2 xxx else Nat_LA_Data.decomp1(T,xxx);

fun decomp(_$(Const(rel,T)$lhs$rhs)) = decomp1(T,(rel,lhs,rhs))
  | decomp(_$(Const("Not",_)$(Const(rel,T)$lhs$rhs))) =
      Nat_LA_Data.negate(decomp1(T,(rel,lhs,rhs)))
  | decomp _ = None

(* reduce contradictory <= to False *)
val add_rules = simp_thms@bin_arith_simps@bin_rel_simps@[int_0];

val cancel_sums_ss = Nat_LA_Data.cancel_sums_ss addsimps add_rules
          addsimprocs [Int_Cancel.sum_conv, Int_Cancel.rel_conv];

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
LA_Data_Ref.decomp :=        Int_LA_Data.decomp;
LA_Data_Ref.simp :=          Int_LA_Data.simp;


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

Goal "integ_of v + (integ_of w + z) = integ_of(bin_add v w) + z";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "add_integ_of_left";

Goal "integ_of v * (integ_of w * z) = integ_of(bin_mult v w) * z";
by (simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
qed "mult_integ_of_left";

Addsimps [add_integ_of_left, mult_integ_of_left];

(** Simplification of inequalities involving numerical constants **)

Goal "(w <= z + #1) = (w<=z | w = z + #1)";
by (arith_tac 1);
qed "zle_add1_eq";

Goal "(w <= z - #1) = (w<z)";
by (arith_tac 1);
qed "zle_diff1_eq";
Addsimps [zle_diff1_eq];

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w <= z; #0 <= v |] ==> w <= z + v";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd";

Goal "w <= z ==> w <= z + #1";
by (fast_arith_tac 1);
qed "zle_imp_zle_zadd1";

(*2nd premise can be proved automatically if v is a literal*)
Goal "[| w < z; #0 <= v |] ==> w < z + v";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd";

Goal "w < z ==> w < z + #1";
by (fast_arith_tac 1);
qed "zless_imp_zless_zadd1";

Goal "(w < z + #1) = (w<=z)";
by (arith_tac 1);
qed "zle_add1_eq_le";
Addsimps [zle_add1_eq_le];

Goal "(z = z + w) = (w = #0)";
by (arith_tac 1);
qed "zadd_left_cancel0";
Addsimps [zadd_left_cancel0];

(*LOOPS as a simprule!*)
Goal "[| w + v < z; #0 <= v |] ==> w < z";
by (fast_arith_tac 1);
qed "zless_zadd_imp_zless";

(*LOOPS as a simprule!  Analogous to Suc_lessD*)
Goal "w + #1 < z ==> w < z";
by (fast_arith_tac 1);
qed "zless_zadd1_imp_zless";

Goal "w + #-1 = w - #1";
by (Simp_tac 1);
qed "zplus_minus1_conv";


(*** nat ***)

Goal "#0 <= z ==> int (nat z) = z"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, not_neg_nat]) 1); 
qed "nat_0_le"; 

Goal "z < #0 ==> nat z = 0"; 
by (asm_full_simp_tac
    (simpset() addsimps [neg_eq_less_0, zle_def, neg_nat]) 1); 
qed "nat_less_0"; 

Addsimps [nat_0_le, nat_less_0];

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

Goal "nat #3 = Suc 2";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_3";

Goal "nat #4 = Suc (Suc 2)";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_4";

Goal "nat #5 = Suc (Suc (Suc 2))";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_5";

Goal "nat #6 = Suc (Suc (Suc (Suc 2)))";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_6";

Goal "nat #7 = Suc (Suc (Suc (Suc (Suc 2))))";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_7";

Goal "nat #8 = Suc (Suc (Suc (Suc (Suc (Suc 2)))))";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_8";

Goal "nat #9 = Suc (Suc (Suc (Suc (Suc (Suc (Suc 2))))))";
by (simp_tac (simpset() addsimps [nat_eq_iff]) 1);
qed "nat_9";

(*Users also don't want to see (nat 0), (nat 1), ...*)
Addsimps [nat_0, nat_1, nat_2, nat_3, nat_4, 
	  nat_5, nat_6, nat_7, nat_8, nat_9];


Goal "#0 <= w ==> (nat w < nat z) = (w<z)";
by (case_tac "neg z" 1);
by (auto_tac (claset(), simpset() addsimps [nat_less_iff]));
by (auto_tac (claset() addIs [zless_trans], 
	      simpset() addsimps [neg_eq_less_0, zle_def]));
qed "nat_less_eq_zless";

