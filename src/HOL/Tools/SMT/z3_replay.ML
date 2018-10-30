(*  Title:      HOL/Tools/SMT/z3_replay.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Z3 proof parsing and replay.
*)

signature Z3_REPLAY =
sig
  val parse_proof: Proof.context -> SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
  val replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure Z3_Replay: Z3_REPLAY =
struct

local
  fun extract (Z3_Proof.Z3_Step {id, rule, concl, fixes, ...}) = (id, rule, concl, fixes)
  fun cond rule = Z3_Proof.is_assumption rule andalso rule <> Z3_Proof.Hypothesis
in

val add_asserted = SMT_Replay.add_asserted Inttab.update Inttab.empty extract cond

end

fun add_paramTs names t =
  fold2 (fn n => fn (_, T) => AList.update (op =) (n, T)) names (SMT_Replay.params_of t)

fun new_fixes ctxt nTs =
  let
    val (ns, ctxt') = Variable.variant_fixes (replicate (length nTs) "") ctxt
    fun mk (n, T) n' = (n, Thm.cterm_of ctxt' (Free (n', T)))
  in (ctxt', Symtab.make (map2 mk nTs ns)) end

fun forall_elim_term ct (Const (@{const_name Pure.all}, _) $ (a as Abs _)) =
      Term.betapply (a, Thm.term_of ct)
  | forall_elim_term _ qt = raise TERM ("forall_elim'", [qt])

fun apply_fixes elim env = fold (elim o the o Symtab.lookup env)

val apply_fixes_prem = uncurry o apply_fixes Thm.forall_elim
val apply_fixes_concl = apply_fixes forall_elim_term

fun export_fixes env names = Drule.forall_intr_list (map (the o Symtab.lookup env) names)

fun under_fixes f ctxt (prems, nthms) names concl =
  let
    val thms1 = map (SMT_Replay.varify ctxt) prems
    val (ctxt', env) =
      add_paramTs names concl []
      |> fold (uncurry add_paramTs o apsnd Thm.prop_of) nthms
      |> new_fixes ctxt
    val thms2 = map (apply_fixes_prem env) nthms
    val t = apply_fixes_concl env names concl
  in export_fixes env names (f ctxt' (thms1 @ thms2) t) end

fun replay_thm ctxt assumed nthms (Z3_Proof.Z3_Step {id, rule, concl, fixes, is_fix_step, ...}) =
  if Z3_Proof.is_assumption rule then
    (case Inttab.lookup assumed id of
      SOME (_, thm) => thm
    | NONE => Thm.assume (Thm.cterm_of ctxt concl))
  else
    under_fixes (Z3_Replay_Methods.method_for rule) ctxt
      (if is_fix_step then (map snd nthms, []) else ([], nthms)) fixes concl

fun replay_step ctxt assumed (step as Z3_Proof.Z3_Step {id, rule, prems, fixes, ...}) state =
  let
    val (proofs, stats) = state
    val nthms = map (the o Inttab.lookup proofs) prems
    val replay = Timing.timing (replay_thm ctxt assumed nthms)
    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay step
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    val stats' = Symtab.cons_list (Z3_Proof.string_of_rule rule, Time.toMilliseconds elapsed) stats
  in (Inttab.update (id, (fixes, thm)) proofs, stats') end

(* |- (EX x. P x) = P c     |- ~ (ALL x. P x) = ~ P c *)
local
  val sk_rules = @{lemma
    "c = (SOME x. P x) \<Longrightarrow> (\<exists>x. P x) = P c"
    "c = (SOME x. \<not> P x) \<Longrightarrow> (\<not> (\<forall>x. P x)) = (\<not> P c)"
    by (metis someI_ex)+}
in

fun discharge_sk_tac ctxt i st =
  (resolve_tac ctxt @{thms trans} i
   THEN resolve_tac ctxt sk_rules i
   THEN (resolve_tac ctxt @{thms refl} ORELSE' discharge_sk_tac ctxt) (i+1)
   THEN resolve_tac ctxt @{thms refl} i) st

end

val true_thm = @{lemma "\<not>False" by simp}
fun make_discharge_rules rules = rules @ [@{thm allI}, @{thm refl}, @{thm reflexive}, true_thm]

val intro_def_rules = @{lemma
  "(\<not> P \<or> P) \<and> (P \<or> \<not> P)"
  "(P \<or> \<not> P) \<and> (\<not> P \<or> P)"
  by fast+}

fun discharge_assms_tac ctxt rules =
  REPEAT
    (HEADGOAL (resolve_tac ctxt (intro_def_rules @ rules) ORELSE'
      SOLVED' (discharge_sk_tac ctxt)))

fun discharge_assms ctxt rules thm =
  (if Thm.nprems_of thm = 0 then
     thm
   else
     (case Seq.pull (discharge_assms_tac ctxt rules thm) of
       SOME (thm', _) => thm'
     | NONE => raise THM ("failed to discharge premise", 1, [thm])))
  |> Goal.norm_result ctxt

fun discharge rules outer_ctxt inner_ctxt =
  singleton (Proof_Context.export inner_ctxt outer_ctxt)
  #> discharge_assms outer_ctxt (make_discharge_rules rules)

fun parse_proof outer_ctxt
    ({context = ctxt, typs, terms, ll_defs, rewrite_rules, assms} : SMT_Translate.replay_data)
    xfacts prems concl output =
  let
    val (steps, ctxt2) = Z3_Proof.parse typs terms output ctxt
    val ((iidths, _), _) = add_asserted outer_ctxt rewrite_rules assms steps ctxt2

    fun id_of_index i = the_default ~1 (Option.map fst (AList.lookup (op =) iidths i))

    val conjecture_i = 0
    val prems_i = 1
    val facts_i = prems_i + length prems

    val conjecture_id = id_of_index conjecture_i
    val prem_ids = map id_of_index (prems_i upto facts_i - 1)
    val fact_ids' =
      map_filter (fn (i, (id, _)) => try (apsnd (nth xfacts)) (id, i - facts_i)) iidths
    val helper_ids' = map_filter (try (fn (~1, idth) => idth)) iidths

    val fact_helper_ts =
      map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, Thm.prop_of th)) helper_ids' @
      map (fn (_, ((s, _), th)) => (s, Thm.prop_of th)) fact_ids'
    val fact_helper_ids' =
      map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids' @ map (apsnd (fst o fst)) fact_ids'
  in
    {outcome = NONE, fact_ids = SOME fact_ids',
     atp_proof = fn () => Z3_Isar.atp_proof_of_z3_proof ctxt ll_defs rewrite_rules prems concl
       fact_helper_ts prem_ids conjecture_id fact_helper_ids' steps}
  end

fun replay outer_ctxt
    ({context = ctxt, typs, terms, rewrite_rules, assms, ...} : SMT_Translate.replay_data) output =
  let
    val (steps, ctxt2) = Z3_Proof.parse typs terms output ctxt
    val ((_, rules), (ctxt3, assumed)) =
      add_asserted outer_ctxt rewrite_rules assms steps ctxt2
    val ctxt4 =
      ctxt3
      |> put_simpset (SMT_Replay.make_simpset ctxt3 [])
      |> Config.put SAT.solver (Config.get ctxt3 SMT_Config.sat_solver)
    val len = length steps
    val start = Timing.start ()
    val print_runtime_statistics = SMT_Replay.intermediate_statistics ctxt4 start len
    fun blockwise f (i, x) y =
      (if i > 0 andalso i mod 100 = 0 then print_runtime_statistics i else (); f x y)
    val (proofs, stats) =
      fold_index (blockwise (replay_step ctxt4 assumed)) steps (assumed, Symtab.empty)
    val _ = print_runtime_statistics len
    val total = Time.toMilliseconds (#elapsed (Timing.result start))
    val (_, Z3_Proof.Z3_Step {id, ...}) = split_last steps
    val _ = SMT_Config.statistics_msg ctxt4 (Pretty.string_of o SMT_Replay.pretty_statistics "Z3" total) stats
  in
    Inttab.lookup proofs id |> the |> snd |> discharge rules outer_ctxt ctxt4
  end

end;
