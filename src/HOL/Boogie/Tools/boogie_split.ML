(*  Title:      HOL/Boogie/Tools/boogie_split.ML
    Author:     Sascha Boehme, TU Muenchen

Method to split Boogie-generate verification conditions and pass the splinters
to user-supplied automated sub-tactics.
*)

signature BOOGIE_SPLIT =
sig
  val add_sub_tactic: string * (Proof.context -> int -> tactic) -> theory ->
    theory
  val sub_tactic_names: theory -> string list
  val setup: theory -> theory
end

structure Boogie_Split: BOOGIE_SPLIT =
struct

(* sub-tactics store *)

structure Sub_Tactics = Theory_Data
(
  type T = (Proof.context -> int -> tactic) Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun add_sub_tactic tac = Sub_Tactics.map (Symtab.update_new tac)

val sub_tactic_names = Symtab.keys o Sub_Tactics.get

fun lookup_sub_tactic ctxt name =
  (case Symtab.lookup (Sub_Tactics.get (ProofContext.theory_of ctxt)) name of
    SOME tac => SOME (name, tac)
  | NONE => (warning ("Unknown sub-tactic: " ^ quote name); NONE))

fun as_meta_eq eq = eq RS @{thm eq_reflection}

fun full_implies_conv cv ct =
  (case try Thm.dest_implies ct of
    NONE => cv ct
  | SOME (cp, cc) => Drule.imp_cong_rule (cv cp) (full_implies_conv cv cc))

fun sub_tactics_tac ctxt (verbose, sub_tac_names) case_name =
  let
    fun trace msg = if verbose then tracing msg else ()
    fun trying name = trace ("Trying tactic " ^ quote name ^ " on case " ^
      quote case_name ^ " ...")
    fun solved () = trace ("Case solved: " ^ quote case_name)
    fun failed () = trace ("Case remains unsolved: " ^ quote case_name)

    infix IF_UNSOLVED
    fun (tac1 IF_UNSOLVED tac2) i st = st |> (tac1 i THEN (fn st' =>
      let val j = i + Thm.nprems_of st' - Thm.nprems_of st
      in
        if i > j then (solved (); Tactical.all_tac st')
        else Seq.INTERVAL tac2 i j st'
      end))
    
    fun TRY_ALL [] _ st = (failed (); Tactical.no_tac st)
      | TRY_ALL ((name, tac) :: tacs) i st = (trying name;
          (TRY o tac ctxt IF_UNSOLVED TRY_ALL tacs) i st)

    val unfold_labels = Conv.try_conv (Conv.arg_conv
      (More_Conv.rewrs_conv (map as_meta_eq @{thms labels})))
  in
    CONVERSION (full_implies_conv unfold_labels)
    THEN' TRY_ALL (map_filter (lookup_sub_tactic ctxt) sub_tac_names)
  end


(* case names *)

fun case_name_of t =
  (case HOLogic.dest_Trueprop (Logic.strip_imp_concl t) of
    @{term assert_at} $ Free (n, _) $ _ => n
  | _ => raise TERM ("case_name_of", [t]))

local
  fun make_case_name (i, t) =
    the_default ("B_" ^ string_of_int (i + 1)) (try case_name_of t)

  val assert_intro = Thm.symmetric (as_meta_eq @{thm assert_at_def})
  val l = Thm.dest_arg1 (Thm.rhs_of assert_intro)
  fun intro new =
    Conv.rewr_conv (Thm.instantiate ([], [(l, new)]) assert_intro)

  val assert_eq = @{lemma "assert_at x t == assert_at y t"
    by (simp add: assert_at_def)}
  val (x, y) = pairself Thm.dest_arg1 (Thm.dest_binop (Thm.cprop_of assert_eq))
  fun rename old new =
    Conv.rewr_conv (Thm.instantiate ([], [(x, old), (y, new)]) assert_eq)

  fun at_concl cv = Conv.concl_conv ~1 (Conv.arg_conv cv)
  fun make_label thy name = Thm.cterm_of thy (Free (name, @{typ bool}))

  fun rename_case thy new ct =
    (case try case_name_of (Thm.term_of ct) of
      NONE => at_concl (intro (make_label thy new))
    | SOME old => if new = old then Conv.all_conv
        else at_concl (rename (make_label thy old) (make_label thy new))) ct
in
fun unique_case_names thy st =
  let
    val names = map_index make_case_name (Thm.prems_of st)
      |> ` (duplicates (op =)) |-> Name.variant_list
  in ALLGOALS (fn i => CONVERSION (rename_case thy (nth names (i-1))) i) st end
end


(* splitting method *)

local
  val split_rules = [@{thm impI}, @{thm conjI}, @{thm TrueI}]

  fun prep_tac ctxt args facts =
    HEADGOAL (Method.insert_tac facts)
    THEN HEADGOAL (REPEAT_ALL_NEW (Tactic.resolve_tac split_rules))
    THEN unique_case_names (ProofContext.theory_of ctxt)
    THEN ALLGOALS (SUBGOAL (fn (t, i) =>
      TRY (sub_tactics_tac ctxt args (case_name_of t) i)))

  val drop_assert_at = Conv.concl_conv ~1 (Conv.try_conv (Conv.arg_conv
    (Conv.rewr_conv (as_meta_eq @{thm assert_at_def}))))

  fun split_vc args ctxt = METHOD_CASES (fn facts =>
    prep_tac ctxt args facts #>
    Seq.maps (fn st =>
      st
      |> ALLGOALS (CONVERSION drop_assert_at)
      |> Seq.map (pair (map (rpair [] o case_name_of) (Thm.prems_of st)))) #>
    Seq.maps (fn (names, st) =>
      CASES
        (Rule_Cases.make_common false
          (ProofContext.theory_of ctxt, Thm.prop_of st) names)
        Tactical.all_tac st))

  val verbose_opt = Args.parens (Args.$$$ "verbose") >> K true
  val sub_tactics = Args.$$$ "try" -- Args.colon |-- Scan.repeat1 Args.name
in
val setup_split_vc = Method.setup @{binding split_vc}
  (Scan.lift (Scan.optional verbose_opt false -- Scan.optional sub_tactics [])
    >> split_vc)
  ("Splits a Boogie-generated verification conditions into smaller problems" ^
   " and tries to solve the splinters with the supplied sub-tactics.")
end


(* predefined sub-tactics *)

fun fast_sub_tac ctxt = Classical.fast_tac (Classical.claset_of ctxt)
fun simp_sub_tac ctxt =
  Simplifier.asm_full_simp_tac (Simplifier.simpset_of ctxt)
fun smt_sub_tac ctxt = SMT_Solver.smt_tac ctxt (Split_VC_SMT_Rules.get ctxt)


(* setup *)

val setup =
  setup_split_vc #>
  add_sub_tactic ("fast", fast_sub_tac) #>
  add_sub_tactic ("simp", simp_sub_tac) #>
  add_sub_tactic ("smt", smt_sub_tac)  

end
