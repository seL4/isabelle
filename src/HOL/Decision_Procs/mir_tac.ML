(*  Title:      HOL/Decision_Procs/mir_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature MIR_TAC =
sig
  val mir_tac: Proof.context -> bool -> int -> tactic
end

structure Mir_Tac: MIR_TAC =
struct

val mir_ss = 
  simpset_of (\<^context> delsimps [@{thm "of_int_eq_iff"}, @{thm "of_int_less_iff"}, @{thm "of_int_le_iff"}] 
               addsimps @{thms "iff_real_of_int"});

val nT = HOLogic.natT;
  val nat_arith = [@{thm diff_nat_numeral}];

  val comp_arith = [@{thm "Let_def"}, @{thm "if_False"}, @{thm "if_True"}, @{thm "add_0"},
                 @{thm "add_Suc"}, @{thm add_numeral_left}, @{thm mult_numeral_left(1)}] @
                 (map (fn th => th RS sym) [@{thm "numeral_One"}])
                 @ @{thms arith_simps} @ nat_arith @ @{thms rel_simps} 
  val ths = [@{thm "mult_numeral_1"}, @{thm "mult_numeral_1_right"}, 
             @{thm of_nat_numeral},
             @{thm "of_nat_Suc"}, @{thm "of_nat_1"},
             @{thm "of_int_0"}, @{thm "of_nat_0"},
             @{thm "div_by_0"}, 
             @{thm "divide_divide_eq_left"}, @{thm "times_divide_eq_right"}, 
             @{thm "times_divide_eq_left"}, @{thm "divide_divide_eq_right"},
             @{thm uminus_add_conv_diff [symmetric]}, @{thm "minus_divide_left"}]
val comp_ths = distinct Thm.eq_thm (ths @ comp_arith @ @{thms simp_thms});

fun prepare_for_mir q fm = 
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
    val (fm',np) = List.foldr (fn ((x, T), (fm,n)) => mk_all ((x, T), (fm,n)))
      (List.foldr HOLogic.mk_imp c rhs, np) ps
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = nT)
      (Misc_Legacy.term_frees fm' @ Misc_Legacy.term_vars fm');
    val fm2 = List.foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun mir_tac ctxt q = 
    Object_Logic.atomize_prems_tac ctxt
        THEN' simp_tac (put_simpset HOL_basic_ss ctxt
          addsimps [@{thm "abs_ge_zero"}] addsimps @{thms simp_thms})
        THEN' (REPEAT_DETERM o split_tac ctxt [@{thm "split_min"}, @{thm "split_max"}, @{thm "abs_split"}])
        THEN' SUBGOAL (fn (g, i) =>
  let
    (* Transform the term*)
    val (t,np,nh) = prepare_for_mir q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset = put_simpset HOL_basic_ss ctxt
                        addsimps [refl, @{thm mod_add_eq}, 
                                  @{thm mod_self},
                                  @{thm div_0}, @{thm mod_0},
                                  @{thm div_by_1}, @{thm mod_by_1}, @{thm div_by_Suc_0}, @{thm mod_by_Suc_0},
                                  @{thm "Suc_eq_plus1"}]
                        addsimps @{thms add.assoc add.commute add.left_commute}
                        addsimprocs [\<^simproc>\<open>cancel_div_mod_nat\<close>, \<^simproc>\<open>cancel_div_mod_int\<close>]
    val simpset0 = put_simpset HOL_basic_ss ctxt
      addsimps @{thms minus_div_mult_eq_mod [symmetric] Suc_eq_plus1}
      addsimps comp_ths
      |> fold Splitter.add_split
          [@{thm "split_zdiv"}, @{thm "split_zmod"}, @{thm "split_div'"},
            @{thm "split_min"}, @{thm "split_max"}]
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 = put_simpset HOL_basic_ss ctxt
      addsimps @{thms int_dvd_int_iff [symmetric] of_nat_add of_nat_mult} @ 
          map (fn r => r RS sym) [@{thm "int_int_eq"}, @{thm "zle_int"}, @{thm "of_nat_less_iff"}, @{thm nat_numeral}]
      |> Splitter.add_split @{thm "zdiff_int_split"}
    (*simp rules for elimination of int n*)

    val simpset2 = put_simpset HOL_basic_ss ctxt
      addsimps [@{thm "nat_0_le"}, @{thm "all_nat"}, @{thm "ex_nat"}, @{thm zero_le_numeral}, 
                @{thm "of_nat_0"}, @{thm "of_nat_1"}]
      |> fold Simplifier.add_cong [@{thm "conj_le_cong"}, @{thm "imp_le_cong"}]
    (* simp rules for elimination of abs *)
    val ct = Thm.cterm_of ctxt (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1),
       TRY (simp_tac (put_simpset mir_ss ctxt) 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac ctxt i)
    (* The result of the quantifier elimination *)
    val (th, tac) =
      case Thm.prop_of pre_thm of
        \<^Const_>\<open>Pure.imp for \<^Const_>\<open>Trueprop for t1\<close> _\<close> =>
    let
      val pth = mirfr_oracle (ctxt, Envir.eta_long [] t1)
    in 
       ((pth RS iffD2) RS pre_thm,
        assm_tac (i + 1) THEN (if q then I else TRY) (resolve_tac ctxt [TrueI] i))
    end
      | _ => (pre_thm, assm_tac i)
  in resolve_tac ctxt [((mp_step nh) o (spec_step np)) th] i THEN tac end);

end
