(*  Title:      HOL/Decision_Procs/ferrack_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature FERRACK_TAC =
sig
  val linr_tac: Proof.context -> bool -> int -> tactic
end

structure Ferrack_Tac: FERRACK_TAC =
struct

val ferrack_ss = let val ths = [@{thm of_int_eq_iff}, @{thm of_int_less_iff}, 
                                @{thm of_int_le_iff}]
             in \<^context> delsimps ths addsimps (map (fn th => th RS sym) ths)
             end |> simpset_of;

val binarith = @{thms arith_simps}
val comp_arith = binarith @ @{thms simp_thms}

fun prepare_for_linr q fm = 
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
    Object_Logic.atomize_prems_tac ctxt
        THEN' (REPEAT_DETERM o split_tac ctxt [@{thm split_min}, @{thm split_max}, @{thm abs_split}])
        THEN' SUBGOAL (fn (g, i) =>
  let
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linr q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val simpset0 = put_simpset HOL_basic_ss ctxt addsimps comp_arith
    val ct = Thm.cterm_of ctxt (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
   val pre_thm = Seq.hd (EVERY
      [simp_tac simpset0 1,
       TRY (simp_tac (put_simpset ferrack_ss ctxt) 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac ctxt i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case Thm.prop_of pre_thm of
        \<^Const_>\<open>Pure.imp for \<^Const_>\<open>Trueprop for t1\<close> _\<close> =>
    let val pth = linr_oracle (ctxt, Envir.eta_long [] t1)
    in 
       ((pth RS iffD2) RS pre_thm,
        assm_tac (i + 1) THEN (if q then I else TRY) (resolve_tac ctxt [TrueI] i))
    end
      | _ => (pre_thm, assm_tac i)
  in resolve_tac ctxt [(mp_step nh o spec_step np) th] i THEN tac end);

end
