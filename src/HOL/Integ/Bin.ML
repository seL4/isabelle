(*  Title:      HOL/Integ/Bin.ML
    ID:         $Id$
    Authors:    Lawrence C Paulson, Cambridge University Computer Laboratory
                David Spelt, University of Twente 
                Tobias Nipkow, Technical University Munich
    Copyright   1994  University of Cambridge
    Copyright   1996  University of Twente
    Copyright   1999  TU Munich

Arithmetic on binary integers.
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


(** number_of **)

Goal "number_of(NCons w b) = (number_of(w BIT b)::int)";
by (induct_tac "w" 1);
by (ALLGOALS Asm_simp_tac);
qed "number_of_NCons";

Addsimps [number_of_NCons];

Goal "number_of(bin_succ w) = (1 + number_of w :: int)";
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps zadd_ac)));
qed "number_of_succ";

Goal "number_of(bin_pred w) = (- 1 + number_of w :: int)";
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

(*This proof is complicated by the mutual recursion*)
Goal "! w. number_of(bin_add v w) = (number_of v + number_of w::int)";
by (induct_tac "v" 1); 
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [number_of_pred]) 1);
by (rtac allI 1);
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps 
               [bin_add_BIT_BIT, number_of_succ, number_of_pred] @ zadd_ac)));
qed_spec_mp "number_of_add";


(*Subtraction*)
Goalw [zdiff_def]
     "number_of v - number_of w = (number_of(bin_add v (bin_minus w))::int)";
by (simp_tac (simpset() addsimps [number_of_add, number_of_minus]) 1);
qed "diff_number_of_eq";

bind_thms ("bin_mult_simps", 
           [int_Suc0_eq_1, zmult_zminus, number_of_minus, number_of_add]);

Goal "number_of(bin_mult v w) = (number_of v * number_of w::int)";
by (induct_tac "v" 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
by (asm_simp_tac
    (simpset() addsimps bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac) 1);
qed "number_of_mult";


(*The correctness of shifting.  But it doesn't seem to give a measurable
  speed-up.*)
Goal "(2::int) * number_of w = number_of (w BIT False)";
by (induct_tac "w" 1);
by (ALLGOALS (asm_simp_tac
    (simpset() addsimps bin_mult_simps @ [zadd_zmult_distrib] @ zadd_ac)));
qed "double_number_of_BIT";


(** Converting numerals 0 and 1 to their abstract versions **)

Goal "Numeral0 = (0::int)";
by (Simp_tac 1);
qed "int_numeral_0_eq_0";

Goal "Numeral1 = (1::int)";
by (simp_tac (simpset() addsimps [int_1, int_Suc0_eq_1]) 1);
qed "int_numeral_1_eq_1";


(** Special simplification, for constants only **)

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

(*Cancellation of constant factors in comparisons (< and <=) *)
Addsimps (map (inst "k" "number_of ?v")
	  [zmult_zless_cancel1, zmult_zless_cancel2,
	   zmult_zle_cancel1, zmult_zle_cancel2]);


(** Special-case simplification for small constants **)

Goal "-1 * z = -(z::int)";
by (simp_tac (simpset() addsimps zcompare_rls@[int_Suc0_eq_1, zmult_zminus]) 1);
qed "zmult_minus1";

Goal "z * -1 = -(z::int)";
by (stac zmult_commute 1 THEN rtac zmult_minus1 1);
qed "zmult_minus1_right";

Addsimps [zmult_minus1, zmult_minus1_right];

(*Negation of a coefficient*)
Goal "- (number_of w) * z = number_of(bin_minus w) * (z::int)";
by (simp_tac (simpset() addsimps [number_of_minus, zmult_zminus]) 1);
qed "zminus_number_of_zmult";
Addsimps [zminus_number_of_zmult];

(*Integer unary minus for the abstract constant 1. Cannot be inserted
  as a simprule until later: it is number_of_Min re-oriented!*)
Goal "- 1 = (-1::int)";
by (Simp_tac 1);
qed "zminus_1_eq_m1";

Goal "(0 < nat z) = (0 < z)";
by (cut_inst_tac [("w","0")] zless_nat_conj 1);
by Auto_tac;  
qed "zero_less_nat_eq";
Addsimps [zero_less_nat_eq];


(** Simplification rules for comparison of binary numbers (Norbert Voelker) **)

(** Equals (=) **)

Goalw [iszero_def]
  "((number_of x::int) = number_of y) = \
\  iszero (number_of (bin_add x (bin_minus y)))"; 
by (simp_tac (simpset()
                 addsimps zcompare_rls @ [number_of_add, number_of_minus]) 1); 
qed "eq_number_of_eq"; 

Goalw [iszero_def] "iszero ((number_of Pls)::int)"; 
by (Simp_tac 1); 
qed "iszero_number_of_Pls"; 

Goalw [iszero_def] "~ iszero ((number_of Min)::int)"; 
by (Simp_tac 1);
qed "nonzero_number_of_Min"; 

Goalw [iszero_def]
     "iszero (number_of (w BIT x)) = (~x & iszero (number_of w::int))"; 
by (int_case_tac "number_of w" 1); 
by (ALLGOALS 
    (asm_simp_tac 
     (simpset() addsimps zcompare_rls @ 
  	                 [zero_reorient, zminus_zadd_distrib RS sym, 
                          int_Suc0_eq_1 RS sym, zadd_int]))); 
qed "iszero_number_of_BIT"; 

Goal "iszero (number_of (w BIT False)) = iszero (number_of w::int)"; 
by (simp_tac (HOL_ss addsimps [iszero_number_of_BIT]) 1); 
qed "iszero_number_of_0"; 

Goal "~ iszero (number_of (w BIT True)::int)"; 
by (simp_tac (HOL_ss addsimps [iszero_number_of_BIT]) 1); 
qed "iszero_number_of_1"; 



(** Less-than (<) **)

Goalw [zless_def,zdiff_def] 
    "((number_of x::int) < number_of y) \
\    = neg (number_of (bin_add x (bin_minus y)))";
by (simp_tac (simpset() addsimps bin_mult_simps) 1);
qed "less_number_of_eq_neg"; 

(*But if Numeral0 is rewritten to 0 then this rule can't be applied:
  Numeral0 IS (number_of Pls) *)
Goal "~ neg (number_of Pls)";
by (simp_tac (simpset() addsimps [neg_eq_less_0]) 1);  
qed "not_neg_number_of_Pls"; 

Goal "neg (number_of Min)"; 
by (simp_tac (simpset() addsimps [neg_eq_less_0, int_0_less_1]) 1);
qed "neg_number_of_Min"; 

Goal "neg (number_of (w BIT x)) = neg (number_of w)"; 
by (Asm_simp_tac 1); 
by (int_case_tac "number_of w" 1); 
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps [int_Suc0_eq_1 RS sym, zadd_int, 
                         neg_eq_less_0, symmetric zdiff_def] @ zcompare_rls)));
qed "neg_number_of_BIT"; 


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::int)) = \
\     (~ number_of y < (number_of x::int))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_number_of_eq_not_less"; 

(** Absolute value (abs) **)

Goalw [zabs_def]
 "abs(number_of x::int) = \
\ (if number_of x < (0::int) then -number_of x else number_of x)";
by(rtac refl 1);
qed "zabs_number_of";

(*0 and 1 require special rewrites because they aren't numerals*)
Goal "abs (0::int) = 0";
by (simp_tac (simpset() addsimps [zabs_def]) 1); 
qed "zabs_0";

Goal "abs (1::int) = 1";
by (simp_tac (simpset() delsimps [int_0, int_1] 
                       addsimps [int_0 RS sym, int_1 RS sym, zabs_def]) 1); 
qed "zabs_1";

(*Re-orientation of the equation nnn=x*)
Goal "(number_of w = x) = (x = number_of w)";
by Auto_tac;  
qed "number_of_reorient";


structure Bin_Simprocs =
  struct
  fun prove_conv name tacs sg (hyps: thm list) (t,u) =
    if t aconv u then None
    else
    let val ct = cterm_of sg (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u)))
    in Some
       (prove_goalw_cterm [] ct (K tacs)
	handle ERROR => error 
	    ("The error(s) above occurred while trying to prove " ^
	     string_of_cterm ct ^ "\nInternal failure of simproc " ^ name))
    end

  (*version without the hyps argument*)
  fun prove_conv_nohyps name tacs sg = prove_conv name tacs sg []

  fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc
  fun prep_pat s = Thm.read_cterm (Theory.sign_of (the_context())) (s, HOLogic.termT)
  val prep_pats = map prep_pat

  fun is_numeral (Const("Numeral.number_of", _) $ w) = true
    | is_numeral _ = false

  fun simplify_meta_eq f_number_of_eq f_eq =
      mk_meta_eq ([f_eq, f_number_of_eq] MRS trans)

  structure IntAbstractNumeralsData =
    struct
    val dest_eq		= HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
    val is_numeral	= is_numeral
    val numeral_0_eq_0    = int_numeral_0_eq_0
    val numeral_1_eq_1    = int_numeral_1_eq_1
    val prove_conv	= prove_conv_nohyps "int_abstract_numerals"
    fun norm_tac simps	= ALLGOALS (simp_tac (HOL_ss addsimps simps))
    val simplify_meta_eq  = simplify_meta_eq 
    end

  structure IntAbstractNumerals = AbstractNumeralsFun (IntAbstractNumeralsData)


  (*For addition, we already have rules for the operand 0.
    Multiplication is omitted because there are already special rules for 
    both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
    For the others, having three patterns is a compromise between just having
    one (many spurious calls) and having nine (just too many!) *)
  val eval_numerals = 
    map prep_simproc
     [("int_add_eval_numerals",
       prep_pats ["(m::int) + 1", "(m::int) + number_of v"], 
       IntAbstractNumerals.proc (number_of_add RS sym)),
      ("int_diff_eval_numerals",
       prep_pats ["(m::int) - 1", "(m::int) - number_of v"], 
       IntAbstractNumerals.proc diff_number_of_eq),
      ("int_eq_eval_numerals",
       prep_pats ["(m::int) = 0", "(m::int) = 1", "(m::int) = number_of v"], 
       IntAbstractNumerals.proc eq_number_of_eq),
      ("int_less_eval_numerals",
       prep_pats ["(m::int) < 0", "(m::int) < 1", "(m::int) < number_of v"], 
       IntAbstractNumerals.proc less_number_of_eq_neg),
      ("int_le_eval_numerals",
       prep_pats ["(m::int) <= 0", "(m::int) <= 1", "(m::int) <= number_of v"],
       IntAbstractNumerals.proc le_number_of_eq_not_less)]

  (*reorientation simprules using ==, for the following simproc*)
  val meta_zero_reorient = zero_reorient RS eq_reflection
  val meta_one_reorient = one_reorient RS eq_reflection
  val meta_number_of_reorient = number_of_reorient RS eq_reflection

  (*reorientation simplification procedure: reorients (polymorphic) 
    0 = x, 1 = x, nnn = x provided x isn't 0, 1 or a numeral.*)
  fun reorient_proc sg _ (_ $ t $ u) =
    case u of
	Const("0", _) => None
      | Const("1", _) => None
      | Const("Numeral.number_of", _) $ _ => None
      | _ => Some (case t of
		  Const("0", _) => meta_zero_reorient
		| Const("1", _) => meta_one_reorient
		| Const("Numeral.number_of", _) $ _ => meta_number_of_reorient)

  val reorient_simproc = 
      prep_simproc ("reorient_simproc",
	            prep_pats ["0=x", "1=x", "number_of w = x"], 
                    reorient_proc)

  end;


Addsimprocs Bin_Simprocs.eval_numerals;
Addsimprocs [Bin_Simprocs.reorient_simproc];


(*Delete the original rewrites, with their clumsy conditional expressions*)
Delsimps [bin_succ_BIT, bin_pred_BIT, bin_minus_BIT, 
          NCons_Pls, NCons_Min, bin_add_BIT, bin_mult_BIT];

(*Hide the binary representation of integer constants*)
Delsimps [number_of_Pls, number_of_Min, number_of_BIT];



(*Simplification of arithmetic operations on integer constants.
  Note that bin_pred_Pls, etc. were added to the simpset by primrec.*)

bind_thms ("NCons_simps", 
           [NCons_Pls_0, NCons_Pls_1, NCons_Min_0, NCons_Min_1, NCons_BIT]);

bind_thms ("bin_arith_extra_simps",
    [number_of_add RS sym,
     number_of_minus RS sym, zminus_1_eq_m1,
     number_of_mult RS sym,
     bin_succ_1, bin_succ_0, 
     bin_pred_1, bin_pred_0, 
     bin_minus_1, bin_minus_0,  
     bin_add_Pls_right, bin_add_Min_right,
     bin_add_BIT_0, bin_add_BIT_10, bin_add_BIT_11,
     diff_number_of_eq, zabs_number_of, zabs_0, zabs_1,
     bin_mult_1, bin_mult_0] @ NCons_simps);

(*For making a minimal simpset, one must include these default simprules
  of thy.  Also include simp_thms, or at least (~False)=True*)
bind_thms ("bin_arith_simps",
    [bin_pred_Pls, bin_pred_Min,
     bin_succ_Pls, bin_succ_Min,
     bin_add_Pls, bin_add_Min,
     bin_minus_Pls, bin_minus_Min,
     bin_mult_Pls, bin_mult_Min] @ bin_arith_extra_simps);

(*Simplification of relational operations*)
bind_thms ("bin_rel_simps",
    [eq_number_of_eq, iszero_number_of_Pls, nonzero_number_of_Min,
     iszero_number_of_0, iszero_number_of_1,
     less_number_of_eq_neg,
     not_neg_number_of_Pls, not_neg_0, not_neg_1, not_iszero_1, 
     neg_number_of_Min, neg_number_of_BIT,
     le_number_of_eq_not_less]);

Addsimps bin_arith_extra_simps;
Addsimps bin_rel_simps;


(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::int)";
by (simp_tac (simpset() addsimps [zadd_assoc RS sym]) 1);
qed "add_number_of_left";

Goal "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::int)";
by (simp_tac (simpset() addsimps [zmult_assoc RS sym]) 1);
qed "mult_number_of_left";

Goalw [zdiff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::int)";
by (rtac add_number_of_left 1);
qed "add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\    number_of (bin_add v (bin_minus w)) + (c::int)";
by (stac (diff_number_of_eq RS sym) 1);
by Auto_tac;
qed "add_number_of_diff2";

Addsimps [add_number_of_left, mult_number_of_left,
	  add_number_of_diff1, add_number_of_diff2]; 


(** Inserting these natural simprules earlier would break many proofs! **) 

(* int (Suc n) = 1 + int n *)
Addsimps [int_Suc];

(* Numeral0 -> 0 and Numeral1 -> 1 *)
Addsimps [int_numeral_0_eq_0, int_numeral_1_eq_1];


