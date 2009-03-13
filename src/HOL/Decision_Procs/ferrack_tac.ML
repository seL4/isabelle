(*  Title:      HOL/Decision_Procs/ferrack_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

structure Ferrack_Tac =
struct

val trace = ref false;
fun trace_msg s = if !trace then tracing s else ();

val ferrack_ss = let val ths = [@{thm real_of_int_inject}, @{thm real_of_int_less_iff}, 
				@{thm real_of_int_le_iff}]
	     in @{simpset} delsimps ths addsimps (map (fn th => th RS sym) ths)
	     end;

val binarith =
  @{thms normalize_bin_simps} @ @{thms pred_bin_simps} @ @{thms succ_bin_simps} @
  @{thms add_bin_simps} @ @{thms minus_bin_simps} @  @{thms mult_bin_simps};
val comp_arith = binarith @ simp_thms

val zdvd_int = @{thm zdvd_int};
val zdiff_int_split = @{thm zdiff_int_split};
val all_nat = @{thm all_nat};
val ex_nat = @{thm ex_nat};
val number_of1 = @{thm number_of1};
val number_of2 = @{thm number_of2};
val split_zdiv = @{thm split_zdiv};
val split_zmod = @{thm split_zmod};
val mod_div_equality' = @{thm mod_div_equality'};
val split_div' = @{thm split_div'};
val Suc_plus1 = @{thm Suc_plus1};
val imp_le_cong = @{thm imp_le_cong};
val conj_le_cong = @{thm conj_le_cong};
val mod_add_left_eq = @{thm mod_add_left_eq} RS sym;
val mod_add_right_eq = @{thm mod_add_right_eq} RS sym;
val nat_div_add_eq = @{thm div_add1_eq} RS sym;
val int_div_add_eq = @{thm zdiv_zadd1_eq} RS sym;
val ZDIVISION_BY_ZERO_MOD = @{thm DIVISION_BY_ZERO} RS conjunct2;
val ZDIVISION_BY_ZERO_DIV = @{thm DIVISION_BY_ZERO} RS conjunct1;

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
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = HOLogic.natT)
      (OldTerm.term_frees fm' @ OldTerm.term_vars fm');
    val fm2 = foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun linr_tac ctxt q i = 
    (ObjectLogic.atomize_prems_tac i) 
	THEN (REPEAT_DETERM (split_tac [@{thm split_min}, @{thm split_max}, @{thm abs_split}] i))
	THEN (fn st =>
  let
    val g = List.nth (prems_of st, i - 1)
    val thy = ProofContext.theory_of ctxt
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linr thy q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val simpset0 = Simplifier.theory_context thy HOL_basic_ss addsimps comp_arith
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
   val pre_thm = Seq.hd (EVERY
      [simp_tac simpset0 1,
       TRY (simp_tac (Simplifier.theory_context thy ferrack_ss) 1)]
      (trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const ("Trueprop", _) $ t1) $ _ =>
    let val pth = linr_oracle (cterm_of thy (Pattern.eta_long [] t1))
    in 
          (trace_msg ("calling procedure with term:\n" ^
             Syntax.string_of_term ctxt t1);
           ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i)))
    end
      | _ => (pre_thm, assm_tac i)
  in (rtac (((mp_step nh) o (spec_step np)) th) i 
      THEN tac) st
  end handle Subscript => no_tac st);

fun linr_meth src =
  Method.syntax (Args.mode "no_quantify") src
  #> (fn (q, ctxt) => SIMPLE_METHOD' (linr_tac ctxt (not q)));

val setup =
  Method.add_method ("rferrack", linr_meth,
     "decision procedure for linear real arithmetic");

end
