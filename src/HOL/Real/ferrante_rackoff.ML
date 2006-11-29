(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Ferrante and Rackoff Algorithm.
*)

signature FERRANTE_RACKOFF =
sig
  val ferrack_tac: bool -> int -> tactic
  val setup: theory -> theory
  val trace: bool ref
end;

structure Ferrante_Rackoff : FERRANTE_RACKOFF =
struct

val trace = ref false;
fun trace_msg s = if !trace then tracing s else ();

val binarith = map thm ["Pls_0_eq", "Min_1_eq", "pred_Pls", "pred_Min","pred_1","pred_0",
  "succ_Pls", "succ_Min", "succ_1", "succ_0",
  "add_Pls", "add_Min", "add_BIT_0", "add_BIT_10", "add_BIT_11",
  "minus_Pls", "minus_Min", "minus_1", "minus_0",
  "mult_Pls", "mult_Min", "mult_1", "mult_0", 
  "add_Pls_right", "add_Min_right"];

val intarithrel = 
  map thm ["int_eq_number_of_eq", "int_neg_number_of_BIT", "int_le_number_of_eq",
    "int_iszero_number_of_0", "int_less_number_of_eq_neg"]
  @ map (fn s => thm s RS thm "lift_bool") ["int_iszero_number_of_Pls",
    "int_iszero_number_of_1", "int_neg_number_of_Min"]
  @ map (fn s => thm s RS thm "nlift_bool") ["int_nonzero_number_of_Min",
    "int_not_neg_number_of_Pls"];
 
val intarith = map thm ["int_number_of_add_sym", "int_number_of_minus_sym",
  "int_number_of_diff_sym", "int_number_of_mult_sym"];

val natarith = map thm ["add_nat_number_of", "diff_nat_number_of",
  "mult_nat_number_of", "eq_nat_number_of", "less_nat_number_of"];

val powerarith =
  map thm ["nat_number_of", "zpower_number_of_even",
  "zpower_Pls", "zpower_Min"]
  @ [Tactic.simplify true [thm "zero_eq_Numeral0_nring", thm "one_eq_Numeral1_nring"]
    (thm "zpower_number_of_odd")]

val comp_arith = binarith @ intarith @ intarithrel @ natarith 
  @ powerarith @ [thm "not_false_eq_true", thm "not_true_eq_false"];

fun prepare_for_linr q fm = 
  let
    val ps = Logic.strip_params fm
    val hs = map HOLogic.dest_Trueprop (Logic.strip_assums_hyp fm)
    val c = HOLogic.dest_Trueprop (Logic.strip_assums_concl fm)
    fun mk_all ((s, T), (P, n)) =
      if 0 mem loose_bnos P then
        (HOLogic.all_const T $ Abs (s, T, P), n)
      else (incr_boundvars ~1 P, n-1)
    fun mk_all2 (v, t) = HOLogic.all_const (fastype_of v) $ lambda v t;
    val rhs = hs;
    val np = length ps;
    val (fm', np) = Library.foldr mk_all (ps, (Library.foldr HOLogic.mk_imp (rhs, c), np));
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = HOLogic.natT)
      (term_frees fm' @ term_vars fm');
    val fm2 = Library.foldr mk_all2 (vs, fm');
  in (fm2, np + length vs, length rhs) end;

fun spec_step n th = if n = 0 then th else spec_step (n - 1) th RS spec ;
fun mp_step n th = if n = 0 then th else mp_step (n - 1) th RS mp;

val context_ss = simpset_of (the_context ());

fun ferrack_tac q i =  ObjectLogic.atomize_tac i
  THEN REPEAT_DETERM (split_tac [split_min, split_max,abs_split] i)
  THEN (fn st =>
  let
    val g = nth (prems_of st) (i - 1)
    val thy = sign_of_thm st
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linr q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val simpset0 = HOL_basic_ss addsimps comp_arith addsplits [split_min, split_max]
    (* simp rules for elimination of abs *)
    val simpset3 = HOL_basic_ss addsplits [abs_split]
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac simpset0 1, TRY (simp_tac context_ss 1)]
      (trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const ("Trueprop", _) $ t1) $ _ =>
    let val pth = Ferrante_Rackoff_Proof.qelim (cterm_of thy (Pattern.eta_long [] t1))
    in 
          (trace_msg ("calling procedure with term:\n" ^
             Sign.string_of_term thy t1);
           ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i)))
    end
      | _ => (pre_thm, assm_tac i)
  in (rtac (((mp_step nh) o (spec_step np)) th) i 
      THEN tac) st
  end handle Subscript => no_tac st | Ferrante_Rackoff_Proof.FAILURE _ => no_tac st);

val ferrack_meth =
  let
    val parse_flag =  Args.$$$ "no_quantify" >> (K (K false));
  in
    Method.simple_args 
      (Scan.optional (Args.$$$ "(" |-- Scan.repeat1 parse_flag --| Args.$$$ ")") [] >>
        curry (Library.foldl op |>) true)
      (fn q => K (Method.SIMPLE_METHOD' (ferrack_tac q)))
  end;

val setup =
  Method.add_method ("ferrack", ferrack_meth,
    "LCF-proof-producing decision procedure for linear real arithmetic");

end;
