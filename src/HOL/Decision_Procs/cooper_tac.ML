(*  Title:      HOL/Decision_Procs/cooper_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature COOPER_TAC =
sig
  val linz_tac: Proof.context -> bool -> int -> tactic
end

structure Cooper_Tac: COOPER_TAC =
struct

val cooper_ss = simpset_of \<^context>;

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
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = \<^Type>\<open>nat\<close>)
      (Misc_Legacy.term_frees fm' @ Misc_Legacy.term_vars fm');
    val fm2 = List.foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if n = 0 then th else (spec_step (n - 1) th) RS spec;

(* object implication to meta---*)
fun mp_step n th = if n = 0 then th else (mp_step (n - 1) th) RS mp;


fun linz_tac ctxt q = Object_Logic.atomize_prems_tac ctxt THEN' SUBGOAL (fn (g, i) =>
  let
    (* Transform the term*)
    val (t, np, nh) = prepare_for_linz q g;
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset =
      put_simpset HOL_basic_ss ctxt
      addsimps @{thms refl mod_add_eq mod_add_left_eq
          mod_add_right_eq
          div_add1_eq [symmetric] div_add1_eq [symmetric]
          mod_self
          div_by_0 mod_by_0 div_0 mod_0
          div_by_1 mod_by_1 div_by_Suc_0 mod_by_Suc_0
          Suc_eq_plus1}
      addsimps @{thms ac_simps}
      addsimprocs [\<^simproc>\<open>cancel_div_mod_nat\<close>, \<^simproc>\<open>cancel_div_mod_int\<close>]
    val simpset0 =
      put_simpset HOL_basic_ss ctxt
      addsimps @{thms minus_div_mult_eq_mod [symmetric] Suc_eq_plus1 simp_thms}
      |> fold Splitter.add_split @{thms split_zdiv split_zmod split_div' split_min split_max}
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 =
      put_simpset HOL_basic_ss ctxt
      addsimps @{thms int_dvd_int_iff [symmetric] of_nat_add of_nat_mult} @
        map (fn r => r RS sym) @{thms of_nat_numeral [where ?'a = int] int_int_eq zle_int of_nat_less_iff [where ?'a = int]}
      |> Splitter.add_split @{thm zdiff_int_split}
    (*simp rules for elimination of int n*)

    val simpset2 =
      put_simpset HOL_basic_ss ctxt
      addsimps [@{thm nat_0_le}, @{thm all_nat}, @{thm ex_nat}, @{thm zero_le_numeral}, @{thm order_refl}(* FIXME: necessary? *),
        @{thm of_nat_0 [where ?'a = int]}, @{thm of_nat_1  [where ?'a = int]}]
      |> fold Simplifier.add_cong @{thms conj_le_cong imp_le_cong}
    (* simp rules for elimination of abs *)
    val simpset3 = put_simpset HOL_basic_ss ctxt |> Splitter.add_split @{thm abs_split}
    val ct = Thm.cterm_of ctxt (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1),
       TRY (simp_tac simpset3 1), TRY (simp_tac (put_simpset cooper_ss ctxt) 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac ctxt i)
    (* The result of the quantifier elimination *)
    val (th, tac) =
      (case Thm.prop_of pre_thm of
        \<^Const_>\<open>Pure.imp for \<^Const_>\<open>Trueprop for t1\<close> _\<close> =>
          let
            val pth = linzqe_oracle (ctxt, Envir.eta_long [] t1)
          in
            ((pth RS iffD2) RS pre_thm,
              assm_tac (i + 1) THEN (if q then I else TRY) (resolve_tac ctxt [TrueI] i))
          end
      | _ => (pre_thm, assm_tac i))
  in resolve_tac ctxt [mp_step nh (spec_step np th)] i THEN tac end);

end
