(*  Title:      HOL/Decision_Procs/mir_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

structure Mir_Tac =
struct

val trace = ref false;
fun trace_msg s = if !trace then tracing s else ();

val mir_ss = 
let val ths = map thm ["real_of_int_inject", "real_of_int_less_iff", "real_of_int_le_iff"]
in @{simpset} delsimps ths addsimps (map (fn th => th RS sym) ths)
end;

val nT = HOLogic.natT;
  val nat_arith = map thm ["add_nat_number_of", "diff_nat_number_of", 
                       "mult_nat_number_of", "eq_nat_number_of", "less_nat_number_of"];

  val comp_arith = (map thm ["Let_def", "if_False", "if_True", "add_0", 
                 "add_Suc", "add_number_of_left", "mult_number_of_left", 
                 "Suc_eq_add_numeral_1"])@
                 (map (fn s => thm s RS sym) ["numeral_1_eq_1", "numeral_0_eq_0"])
                 @ @{thms arith_simps} @ nat_arith @ @{thms rel_simps} 
  val ths = [@{thm "mult_numeral_1"}, @{thm "mult_numeral_1_right"}, 
             @{thm "real_of_nat_number_of"},
             @{thm "real_of_nat_Suc"}, @{thm "real_of_nat_one"}, @{thm "real_of_one"},
             @{thm "real_of_int_zero"}, @{thm "real_of_nat_zero"},
             @{thm "Ring_and_Field.divide_zero"}, 
             @{thm "divide_divide_eq_left"}, @{thm "times_divide_eq_right"}, 
             @{thm "times_divide_eq_left"}, @{thm "divide_divide_eq_right"},
             @{thm "diff_def"}, @{thm "minus_divide_left"}]
val comp_ths = ths @ comp_arith @ simp_thms 


val zdvd_int = @{thm "zdvd_int"};
val zdiff_int_split = @{thm "zdiff_int_split"};
val all_nat = @{thm "all_nat"};
val ex_nat = @{thm "ex_nat"};
val number_of1 = @{thm "number_of1"};
val number_of2 = @{thm "number_of2"};
val split_zdiv = @{thm "split_zdiv"};
val split_zmod = @{thm "split_zmod"};
val mod_div_equality' = @{thm "mod_div_equality'"};
val split_div' = @{thm "split_div'"};
val Suc_plus1 = @{thm "Suc_plus1"};
val imp_le_cong = @{thm "imp_le_cong"};
val conj_le_cong = @{thm "conj_le_cong"};
val mod_add_eq = @{thm "mod_add_eq"} RS sym;
val mod_add_left_eq = @{thm "mod_add_left_eq"} RS sym;
val mod_add_right_eq = @{thm "mod_add_right_eq"} RS sym;
val nat_div_add_eq = @{thm "div_add1_eq"} RS sym;
val int_div_add_eq = @{thm "zdiv_zadd1_eq"} RS sym;
val ZDIVISION_BY_ZERO_MOD = @{thm "DIVISION_BY_ZERO"} RS conjunct2;
val ZDIVISION_BY_ZERO_DIV = @{thm "DIVISION_BY_ZERO"} RS conjunct1;

fun prepare_for_mir thy q fm = 
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
      (OldTerm.term_frees fm' @ OldTerm.term_vars fm');
    val fm2 = foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun mir_tac ctxt q i = 
    (ObjectLogic.atomize_prems_tac i)
        THEN (simp_tac (HOL_basic_ss addsimps [@{thm "abs_ge_zero"}] addsimps simp_thms) i)
        THEN (REPEAT_DETERM (split_tac [@{thm "split_min"}, @{thm "split_max"},@{thm "abs_split"}] i))
        THEN (fn st =>
  let
    val g = List.nth (prems_of st, i - 1)
    val thy = ProofContext.theory_of ctxt
    (* Transform the term*)
    val (t,np,nh) = prepare_for_mir thy q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset = HOL_basic_ss 
                        addsimps [refl, mod_add_eq, 
                                  @{thm "mod_self"}, @{thm "zmod_self"},
                                  @{thm "zdiv_zero"},@{thm "zmod_zero"},@{thm "div_0"}, @{thm "mod_0"},
                                  @{thm "div_by_1"}, @{thm "mod_by_1"}, @{thm "div_1"}, @{thm "mod_1"},
                                  @{thm "Suc_plus1"}]
                        addsimps @{thms add_ac}
                        addsimprocs [cancel_div_mod_proc]
    val simpset0 = HOL_basic_ss
      addsimps [mod_div_equality', Suc_plus1]
      addsimps comp_ths
      addsplits [@{thm "split_zdiv"}, @{thm "split_zmod"}, @{thm "split_div'"}, @{thm "split_min"}, @{thm "split_max"}]
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 = HOL_basic_ss
      addsimps [@{thm "nat_number_of_def"}, @{thm "zdvd_int"}] @ map (fn r => r RS sym)
        [@{thm "int_int_eq"}, @{thm "zle_int"}, @{thm "zless_int"}, @{thm "zadd_int"}, 
         @{thm "zmult_int"}]
      addsplits [@{thm "zdiff_int_split"}]
    (*simp rules for elimination of int n*)

    val simpset2 = HOL_basic_ss
      addsimps [@{thm "nat_0_le"}, @{thm "all_nat"}, @{thm "ex_nat"}, @{thm "number_of1"}, 
                @{thm "number_of2"}, @{thm "int_0"}, @{thm "int_1"}]
      addcongs [@{thm "conj_le_cong"}, @{thm "imp_le_cong"}]
    (* simp rules for elimination of abs *)
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1), TRY (simp_tac mir_ss 1)]
      (trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const ("Trueprop", _) $ t1) $ _ =>
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
  in (rtac (((mp_step nh) o (spec_step np)) th) i 
      THEN tac) st
  end handle Subscript => no_tac st);

fun mir_args meth =
 let val parse_flag = 
         Args.$$$ "no_quantify" >> (K (K false));
 in
   Method.simple_args 
  (Scan.optional (Args.$$$ "(" |-- Scan.repeat1 parse_flag --| Args.$$$ ")") [] >>
    curry (Library.foldl op |>) true)
    (fn q => fn ctxt => meth ctxt q)
  end;

fun mir_method ctxt q = SIMPLE_METHOD' (mir_tac ctxt q);

val setup =
  Method.add_method ("mir",
     mir_args mir_method,
     "decision procedure for MIR arithmetic");


end
