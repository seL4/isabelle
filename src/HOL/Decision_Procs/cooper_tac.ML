(*  Title:      HOL/Decision_Procs/cooper_tac.ML
    Author:     Amine Chaieb, TU Muenchen
*)

signature COOPER_TAC =
sig
  val trace: bool Unsynchronized.ref
  val linz_tac: Proof.context -> bool -> int -> tactic
  val setup: theory -> theory
end

structure Cooper_Tac: COOPER_TAC =
struct

val trace = Unsynchronized.ref false;
fun trace_msg s = if !trace then tracing s else ();

val cooper_ss = @{simpset};

val nT = HOLogic.natT;
val comp_arith = @{thms simp_thms}

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
val mod_add_eq = @{thm mod_add_eq} RS sym;
val nat_div_add_eq = @{thm div_add1_eq} RS sym;
val int_div_add_eq = @{thm zdiv_zadd1_eq} RS sym;

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
    val (vs, _) = List.partition (fn t => q orelse (type_of t) = nT)
      (Misc_Legacy.term_frees fm' @ Misc_Legacy.term_vars fm');
    val fm2 = List.foldr mk_all2 fm' vs
  in (fm2, np + length vs, length rhs) end;

(*Object quantifier to meta --*)
fun spec_step n th = if (n=0) then th else (spec_step (n-1) th) RS spec ;

(* object implication to meta---*)
fun mp_step n th = if (n=0) then th else (mp_step (n-1) th) RS mp;


fun linz_tac ctxt q = Object_Logic.atomize_prems_tac THEN' SUBGOAL (fn (g, i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    (* Transform the term*)
    val (t,np,nh) = prepare_for_linz q g
    (* Some simpsets for dealing with mod div abs and nat*)
    val mod_div_simpset = HOL_basic_ss
      addsimps [refl,mod_add_eq, mod_add_left_eq,
          mod_add_right_eq,
          nat_div_add_eq, int_div_add_eq,
          @{thm mod_self},
          @{thm div_by_0}, @{thm mod_by_0}, @{thm div_0}, @{thm mod_0},
          @{thm div_by_1}, @{thm mod_by_1}, @{thm div_1}, @{thm mod_1},
          Suc_eq_plus1]
      addsimps @{thms add_ac}
      addsimprocs [@{simproc cancel_div_mod_nat}, @{simproc cancel_div_mod_int}]
    val simpset0 = HOL_basic_ss
      addsimps [mod_div_equality', Suc_eq_plus1]
      addsimps comp_arith
      |> fold Splitter.add_split
          [split_zdiv, split_zmod, split_div', @{thm "split_min"}, @{thm "split_max"}]
    (* Simp rules for changing (n::int) to int n *)
    val simpset1 = HOL_basic_ss
      addsimps [zdvd_int] @ map (fn r => r RS sym)
        [@{thm int_numeral}, @{thm int_int_eq}, @{thm zle_int}, @{thm zless_int}, @{thm zadd_int}, @{thm zmult_int}]
      |> Splitter.add_split zdiff_int_split
    (*simp rules for elimination of int n*)

    val simpset2 = HOL_basic_ss
      addsimps [@{thm nat_0_le}, @{thm all_nat}, @{thm ex_nat}, @{thm zero_le_numeral}, @{thm order_refl}(* FIXME: necessary? *), @{thm int_0}, @{thm int_1}]
      |> fold Simplifier.add_cong [@{thm conj_le_cong}, @{thm imp_le_cong}]
    (* simp rules for elimination of abs *)
    val simpset3 = HOL_basic_ss |> Splitter.add_split @{thm abs_split}
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
    (* Theorem for the nat --> int transformation *)
    val pre_thm = Seq.hd (EVERY
      [simp_tac mod_div_simpset 1, simp_tac simpset0 1,
       TRY (simp_tac simpset1 1), TRY (simp_tac simpset2 1),
       TRY (simp_tac simpset3 1), TRY (simp_tac cooper_ss 1)]
      (Thm.trivial ct))
    fun assm_tac i = REPEAT_DETERM_N nh (assume_tac i)
    (* The result of the quantifier elimination *)
    val (th, tac) = case (prop_of pre_thm) of
        Const ("==>", _) $ (Const (@{const_name Trueprop}, _) $ t1) $ _ =>
    let val pth = linzqe_oracle (cterm_of thy (Pattern.eta_long [] t1))
    in
          ((pth RS iffD2) RS pre_thm,
            assm_tac (i + 1) THEN (if q then I else TRY) (rtac TrueI i))
    end
      | _ => (pre_thm, assm_tac i)
  in rtac (((mp_step nh) o (spec_step np)) th) i THEN tac end);

val setup =
  Method.setup @{binding cooper}
    let
      val parse_flag = Args.$$$ "no_quantify" >> K (K false)
    in
      Scan.lift (Scan.optional (Args.$$$ "(" |-- Scan.repeat1 parse_flag --| Args.$$$ ")") [] >>
        curry (Library.foldl op |>) true) >>
      (fn q => fn ctxt => SIMPLE_METHOD' (linz_tac ctxt q))
    end
    "decision procedure for linear integer arithmetic";

end
