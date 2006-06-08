(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Ferrante and Rackoff Algorithm.
*)

structure Ferrante_Rackoff:
sig
  val trace : bool ref
  val ferrack_tac : bool -> int -> tactic
  val setup : theory -> theory
end =
struct

val trace = ref false;
fun trace_msg s = if !trace then tracing s else ();

val context_ss = simpset_of (the_context ());

val nT = HOLogic.natT;
val binarith = map thm
  ["Pls_0_eq", "Min_1_eq",
 "bin_pred_Pls","bin_pred_Min","bin_pred_1","bin_pred_0",
  "bin_succ_Pls", "bin_succ_Min", "bin_succ_1", "bin_succ_0",
  "bin_add_Pls", "bin_add_Min", "bin_add_BIT_0", "bin_add_BIT_10",
  "bin_add_BIT_11", "bin_minus_Pls", "bin_minus_Min", "bin_minus_1", 
  "bin_minus_0", "bin_mult_Pls", "bin_mult_Min", "bin_mult_1", "bin_mult_0", 
  "bin_add_Pls_right", "bin_add_Min_right"];
 val intarithrel = 
     (map thm ["int_eq_number_of_eq","int_neg_number_of_BIT", 
		"int_le_number_of_eq","int_iszero_number_of_0",
		"int_less_number_of_eq_neg"]) @
     (map (fn s => thm s RS thm "lift_bool") 
	  ["int_iszero_number_of_Pls","int_iszero_number_of_1",
	   "int_neg_number_of_Min"])@
     (map (fn s => thm s RS thm "nlift_bool") 
	  ["int_nonzero_number_of_Min","int_not_neg_number_of_Pls"]);
     
val intarith = map thm ["int_number_of_add_sym", "int_number_of_minus_sym",
			"int_number_of_diff_sym", "int_number_of_mult_sym"];
val natarith = map thm ["add_nat_number_of", "diff_nat_number_of",
			"mult_nat_number_of", "eq_nat_number_of",
			"less_nat_number_of"]
val powerarith = 
    (map thm ["nat_number_of", "zpower_number_of_even", 
	      "zpower_Pls", "zpower_Min"]) @ 
    [(Tactic.simplify true [thm "zero_eq_Numeral0_nring", 
			   thm "one_eq_Numeral1_nring"] 
  (thm "zpower_number_of_odd"))]

val comp_arith = binarith @ intarith @ intarithrel @ natarith 
	    @ powerarith @[thm"not_false_eq_true", thm "not_true_eq_false"];

fun prepare_for_linr sg q fm = 
  let
    val ps = Logic.strip_params fm
    val hs = map HOLogic.dest_Trueprop (Logic.strip_assums_hyp fm)
    val c = HOLogic.dest_Trueprop (Logic.strip_assums_concl fm)
    fun mk_all ((s, T), (P,n)) =
      if 0 mem loose_bnos P then
        (HOLogic.all_const T $ Abs (s, T, P), n)
      else (incr_boundvars ~1 P, n-1)
    fun mk_all2 (v, t) = HOLogic.all_const (fastype_of v) $ lambda v t;
      val rhs = hs
(*    val (rhs,irhs) = List.partition (relevant (rev ps)) hs *)
    val np = length ps
    val (fm',np) =  foldr (fn ((x, T), (fm,n)) => mk_all ((x, T), (fm,n)))
      (foldr HOLogic.mk_imp c rhs, np) ps
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = nT)
      (term_frees fm' @ term_vars fm');
    val fm2 = foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun ferrack_tac q i = 
    (ObjectLogic.atomize_tac i) 
	THEN (REPEAT_DETERM (split_tac [split_min, split_max,abs_split] i))
	THEN (fn st =>
  let
    val g = List.nth (prems_of st, i - 1)
    val sg = sign_of_thm st
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linr sg q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val simpset0 = HOL_basic_ss addsimps comp_arith addsplits [split_min, split_max]
    (* simp rules for elimination of abs *)
    val simpset3 = HOL_basic_ss addsplits [abs_split]
    val ct = cterm_of sg (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac simpset0 1, TRY (simp_tac context_ss 1)]
      (trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const ("Trueprop", _) $ t1) $ _ =>
    let val pth = Ferrante_Rackoff_Proof.qelim (cterm_of sg (Pattern.eta_long [] t1))
    in 
          (trace_msg ("calling procedure with term:\n" ^
             Sign.string_of_term sg t1);
           ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i)))
    end
      | _ => (pre_thm, assm_tac i)
  in (rtac (((mp_step nh) o (spec_step np)) th) i 
      THEN tac) st
  end handle Subscript => no_tac st | Ferrante_Rackoff_Proof.FAILURE _ => no_tac st);

fun ferrack_args meth =
 let val parse_flag = 
         Args.$$$ "no_quantify" >> (K (K false));
 in
   Method.simple_args 
  (Scan.optional (Args.$$$ "(" |-- Scan.repeat1 parse_flag --| Args.$$$ ")") [] >>
    curry (Library.foldl op |>) true)
    (fn q => fn _ => meth q 1)
  end;

val setup =
  Method.add_method ("ferrack",
     ferrack_args (Method.SIMPLE_METHOD oo ferrack_tac),
     "LCF-proof-producing decision procedure for linear real arithmetic");

end
