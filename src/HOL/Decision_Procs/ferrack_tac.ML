(*  Title:      HOL/Decision_Procs/ferrack_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature FERRACK_TAC =
sig
  val trace: bool Unsynchronized.ref
  val linr_tac: Proof.context -> bool -> int -> tactic
  val setup: theory -> theory
end

structure Ferrack_Tac =
struct

val trace = Unsynchronized.ref false;
fun trace_msg s = if !trace then tracing s else ();

val ferrack_ss = let val ths = [@{thm real_of_int_inject}, @{thm real_of_int_less_iff}, 
                                @{thm real_of_int_le_iff}]
             in @{simpset} delsimps ths addsimps (map (fn th => th RS sym) ths)
             end;

val binarith = @{thms arith_simps}
val comp_arith = binarith @ @{thms simp_thms}

val zdvd_int = @{thm zdvd_int};
val zdiff_int_split = @{thm zdiff_int_split};
val all_nat = @{thm all_nat};
val ex_nat = @{thm ex_nat};
val split_zdiv = @{thm split_zdiv};
val split_zmod = @{thm split_zmod};
val mod_div_equality' = @{thm mod_div_equality'};
val split_div' = @{thm split_div'};
val Suc_eq_plus1 = @{thm Suc_eq_plus1};
val imp_le_cong = @{thm imp_le_cong};
val conj_le_cong = @{thm conj_le_cong};
val mod_add_left_eq = @{thm mod_add_left_eq} RS sym;
val mod_add_right_eq = @{thm mod_add_right_eq} RS sym;
val nat_div_add_eq = @{thm div_add1_eq} RS sym;
val int_div_add_eq = @{thm zdiv_zadd1_eq} RS sym;

fun prepare_for_linr sg q fm = 
  let
    val ps = Logic.strip_params fm
    val hs = map HOLogic.dest_Trueprop (Logic.strip_assums_hyp fm)
    val c = HOLogic.dest_Trueprop (Logic.strip_assums_concl fm)
    fun mk_all ((s, T), (P,n)) =
      if Term.is_dependent P then
        (HOLogic.all_const T $ Abs (s, T, P), n)
      else (incr_boundvars ~1 P, n-1)
    fun mk_all2 (v, t) = HOLogic.all_const (fastype_of v) $ lambda v t;
      val rhs = hs
(*    val (rhs,irhs) = List.partition (relevant (rev ps)) hs *)
    val np = length ps
    val (fm',np) =  List.foldr (fn ((x, T), (fm,n)) => mk_all ((x, T), (fm,n)))
      (List.foldr HOLogic.mk_imp c rhs, np) ps
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = HOLogic.natT)
      (Misc_Legacy.term_frees fm' @ Misc_Legacy.term_vars fm');
    val fm2 = List.foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun linr_tac ctxt q =
    Object_Logic.atomize_prems_tac
        THEN' (REPEAT_DETERM o split_tac [@{thm split_min}, @{thm split_max}, @{thm abs_split}])
        THEN' SUBGOAL (fn (g, i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linr thy q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val simpset0 = Simplifier.context ctxt HOL_basic_ss addsimps comp_arith
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
   val pre_thm = Seq.hd (EVERY
      [simp_tac simpset0 1,
       TRY (simp_tac (Simplifier.context ctxt ferrack_ss) 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case prop_of pre_thm of
        Const ("==>", _) $ (Const (@{const_name Trueprop}, _) $ t1) $ _ =>
    let val pth = linr_oracle (ctxt, Pattern.eta_long [] t1)
    in 
          (trace_msg ("calling procedure with term:\n" ^
             Syntax.string_of_term ctxt t1);
           ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i)))
    end
      | _ => (pre_thm, assm_tac i)
  in rtac ((mp_step nh o spec_step np) th) i THEN tac end);

val setup =
  Method.setup @{binding rferrack}
    (Args.mode "no_quantify" >> (fn q => fn ctxt =>
      SIMPLE_METHOD' (linr_tac ctxt (not q))))
    "decision procedure for linear real arithmetic";

end
