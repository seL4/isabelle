(*  Title:      HOL/Decision_Procs/cooper_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature COOPER_TAC =
sig
  val linz_tac: Proof.context -> bool -> int -> tactic
end

structure Cooper_Tac: COOPER_TAC =
struct

val cooper_ss = simpset_of @{context};

fun prepare_for_linz q fm =
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
    val np = length ps
    val (fm',np) = List.foldr (fn ((x, T), (fm,n)) => mk_all ((x, T), (fm,n)))
      (List.foldr HOLogic.mk_imp c rhs, np) ps
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = @{typ nat})
      (Misc_Legacy.term_frees fm' @ Misc_Legacy.term_vars fm');
    val fm2 = List.foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if n = 0 then th else (spec_step (n - 1) th) RS spec;

(* object implication to meta---*)
fun mp_step n th = if n = 0 then th else (mp_step (n - 1) th) RS mp;


fun linz_tac ctxt q = Object_Logic.atomize_prems_tac ctxt THEN' SUBGOAL (fn (g, i) =>
  let
    val thy = Proof_Context.theory_of ctxt;
    (* Transform the term*)
    val (t, np, nh) = prepare_for_linz q g;
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset =
      put_simpset HOL_basic_ss ctxt
      addsimps @{thms refl mod_add_eq [symmetric] mod_add_left_eq [symmetric]
          mod_add_right_eq [symmetric]
          div_add1_eq [symmetric] zdiv_zadd1_eq [symmetric]
          mod_self
          div_by_0 mod_by_0 div_0 mod_0
          div_by_1 mod_by_1 div_1 mod_1
          Suc_eq_plus1}
      addsimps @{thms add_ac}
      addsimprocs [@{simproc cancel_div_mod_nat}, @{simproc cancel_div_mod_int}]
    val simpset0 =
      put_simpset HOL_basic_ss ctxt
      addsimps @{thms mod_div_equality' Suc_eq_plus1 simp_thms}
      |> fold Splitter.add_split @{thms split_zdiv split_zmod split_div' split_min split_max}
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 =
      put_simpset HOL_basic_ss ctxt
      addsimps @{thms zdvd_int} @
        map (fn r => r RS sym) @{thms int_numeral int_int_eq zle_int zless_int zadd_int zmult_int}
      |> Splitter.add_split @{thm zdiff_int_split}
    (*simp rules for elimination of int n*)

    val simpset2 =
      put_simpset HOL_basic_ss ctxt
      addsimps [@{thm nat_0_le}, @{thm all_nat}, @{thm ex_nat}, @{thm zero_le_numeral}, @{thm order_refl}(* FIXME: necessary? *), @{thm int_0}, @{thm int_1}]
      |> fold Simplifier.add_cong @{thms conj_le_cong imp_le_cong}
    (* simp rules for elimination of abs *)
    val simpset3 = put_simpset HOL_basic_ss ctxt |> Splitter.add_split @{thm abs_split}
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1),
       TRY (simp_tac simpset3 1), TRY (simp_tac (put_simpset cooper_ss ctxt) 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) =
      (case (prop_of pre_thm) of
        Const (@{const_name Pure.imp}, _) $ (Const (@{const_name Trueprop}, _) $ t1) $ _ =>
          let
            val pth = linzqe_oracle (cterm_of thy (Envir.eta_long [] t1))
          in
            ((pth RS iffD2) RS pre_thm,
              assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i))
          end
      | _ => (pre_thm, assm_tac i))
  in rtac (mp_step nh (spec_step np th)) i THEN tac end);

end
