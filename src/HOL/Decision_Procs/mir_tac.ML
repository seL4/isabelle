(*  Title:      HOL/Decision_Procs/mir_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature MIR_TAC =
sig
  val trace: bool Unsynchronized.ref
  val mir_tac: Proof.context -> bool -> int -> tactic
end

structure Mir_Tac =
struct

val trace = Unsynchronized.ref false;
fun trace_msg s = if !trace then tracing s else ();

val mir_ss = 
let val ths = [@{thm "real_of_int_inject"}, @{thm "real_of_int_less_iff"}, @{thm "real_of_int_le_iff"}]
in @{simpset} delsimps ths addsimps (map (fn th => th RS sym) ths)
end;

val nT = HOLogic.natT;
  val nat_arith = [@{thm diff_nat_numeral}];

  val comp_arith = [@{thm "Let_def"}, @{thm "if_False"}, @{thm "if_True"}, @{thm "add_0"},
                 @{thm "add_Suc"}, @{thm add_numeral_left}, @{thm mult_numeral_left(1)},
                 @{thm "Suc_eq_plus1"}] @
                 (map (fn th => th RS sym) [@{thm "numeral_1_eq_1"}])
                 @ @{thms arith_simps} @ nat_arith @ @{thms rel_simps} 
  val ths = [@{thm "mult_numeral_1"}, @{thm "mult_numeral_1_right"}, 
             @{thm real_of_nat_numeral},
             @{thm "real_of_nat_Suc"}, @{thm "real_of_nat_one"}, @{thm "real_of_one"},
             @{thm "real_of_int_zero"}, @{thm "real_of_nat_zero"},
             @{thm "divide_zero"}, 
             @{thm "divide_divide_eq_left"}, @{thm "times_divide_eq_right"}, 
             @{thm "times_divide_eq_left"}, @{thm "divide_divide_eq_right"},
             @{thm "diff_minus"}, @{thm "minus_divide_left"}]
val comp_ths = ths @ comp_arith @ @{thms simp_thms};


val zdvd_int = @{thm "zdvd_int"};
val zdiff_int_split = @{thm "zdiff_int_split"};
val all_nat = @{thm "all_nat"};
val ex_nat = @{thm "ex_nat"};
val split_zdiv = @{thm "split_zdiv"};
val split_zmod = @{thm "split_zmod"};
val mod_div_equality' = @{thm "mod_div_equality'"};
val split_div' = @{thm "split_div'"};
val imp_le_cong = @{thm "imp_le_cong"};
val conj_le_cong = @{thm "conj_le_cong"};
val mod_add_eq = @{thm "mod_add_eq"} RS sym;
val mod_add_left_eq = @{thm "mod_add_left_eq"} RS sym;
val mod_add_right_eq = @{thm "mod_add_right_eq"} RS sym;
val nat_div_add_eq = @{thm "div_add1_eq"} RS sym;
val int_div_add_eq = @{thm "zdiv_zadd1_eq"} RS sym;

fun prepare_for_mir thy q fm = 
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
    Object_Logic.atomize_prems_tac
        THEN' simp_tac (HOL_basic_ss addsimps [@{thm "abs_ge_zero"}] addsimps @{thms simp_thms})
        THEN' (REPEAT_DETERM o split_tac [@{thm "split_min"}, @{thm "split_max"}, @{thm "abs_split"}])
        THEN' SUBGOAL (fn (g, i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    (* Transform the term*)
    val (t,np,nh) = prepare_for_mir thy q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset = HOL_basic_ss 
                        addsimps [refl, mod_add_eq, 
                                  @{thm mod_self},
                                  @{thm div_0}, @{thm mod_0},
                                  @{thm "div_by_1"}, @{thm "mod_by_1"}, @{thm "div_1"}, @{thm "mod_1"},
                                  @{thm "Suc_eq_plus1"}]
                        addsimps @{thms add_ac}
                        addsimprocs [@{simproc cancel_div_mod_nat}, @{simproc cancel_div_mod_int}]
    val simpset0 = HOL_basic_ss
      addsimps [mod_div_equality', @{thm Suc_eq_plus1}]
      addsimps comp_ths
      |> fold Splitter.add_split
          [@{thm "split_zdiv"}, @{thm "split_zmod"}, @{thm "split_div'"},
            @{thm "split_min"}, @{thm "split_max"}]
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 = HOL_basic_ss
      addsimps [@{thm "zdvd_int"}] @ map (fn r => r RS sym)
        [@{thm "int_int_eq"}, @{thm "zle_int"}, @{thm "zless_int"}, @{thm "zadd_int"}, 
         @{thm nat_numeral}, @{thm "zmult_int"}]
      |> Splitter.add_split @{thm "zdiff_int_split"}
    (*simp rules for elimination of int n*)

    val simpset2 = HOL_basic_ss
      addsimps [@{thm "nat_0_le"}, @{thm "all_nat"}, @{thm "ex_nat"}, @{thm zero_le_numeral}, 
                @{thm "int_0"}, @{thm "int_1"}]
      |> fold Simplifier.add_cong [@{thm "conj_le_cong"}, @{thm "imp_le_cong"}]
    (* simp rules for elimination of abs *)
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1), TRY (simp_tac mir_ss 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const (@{const_name Trueprop}, _) $ t1) $ _ =>
    let val pth =
          (* If quick_and_dirty then run without proof generation as oracle*)
             if !quick_and_dirty
             then mirfr_oracle (false, cterm_of thy (Pattern.eta_long [] t1))
             else mirfr_oracle (true, cterm_of thy (Pattern.eta_long [] t1))
    in 
          (trace_msg ("calling procedure with term:\n" ^
             Syntax.string_of_term ctxt t1);
           ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i)))
    end
      | _ => (pre_thm, assm_tac i)
  in rtac (((mp_step nh) o (spec_step np)) th) i THEN tac end);

end
