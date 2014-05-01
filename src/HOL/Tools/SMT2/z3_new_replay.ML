(*  Title:      HOL/Tools/SMT2/z3_new_replay.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Z3 proof replay.
*)

signature Z3_NEW_REPLAY =
sig
  val replay: Proof.context -> SMT2_Translate.replay_data -> string list ->
    ((int * (int * thm)) list * Z3_New_Proof.z3_step list) * thm
end

structure Z3_New_Replay: Z3_NEW_REPLAY =
struct

fun params_of t = Term.strip_qnt_vars @{const_name Pure.all} t

fun varify ctxt thm =
  let
    val maxidx = Thm.maxidx_of thm + 1
    val vs = params_of (Thm.prop_of thm)
    val vars = map_index (fn (i, (n, T)) => Var ((n, i + maxidx), T)) vs
  in Drule.forall_elim_list (map (SMT2_Util.certify ctxt) vars) thm end

fun add_paramTs names t =
  fold2 (fn n => fn (_, T) => AList.update (op =) (n, T)) names (params_of t)

fun new_fixes ctxt nTs =
  let
    val (ns, ctxt') = Variable.variant_fixes (replicate (length nTs) "") ctxt
    fun mk (n, T) n' = (n, SMT2_Util.certify ctxt' (Free (n', T)))
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
    val thms1 = map (varify ctxt) prems
    val (ctxt', env) =
      add_paramTs names concl []
      |> fold (uncurry add_paramTs o apsnd Thm.prop_of) nthms
      |> new_fixes ctxt
    val thms2 = map (apply_fixes_prem env) nthms
    val t = apply_fixes_concl env names concl
  in export_fixes env names (f ctxt' (thms1 @ thms2) t) end

fun replay_thm ctxt assumed nthms
    (Z3_New_Proof.Z3_Step {id, rule, concl, fixes, is_fix_step, ...}) =
  if Z3_New_Replay_Methods.is_assumption rule then
    (case Inttab.lookup assumed id of
      SOME (_, thm) => thm
    | NONE => Thm.assume (SMT2_Util.certify ctxt concl))
  else
    under_fixes (Z3_New_Replay_Methods.method_for rule) ctxt
      (if is_fix_step then (map snd nthms, []) else ([], nthms)) fixes concl

fun replay_step ctxt assumed (step as Z3_New_Proof.Z3_Step {id, prems, fixes, ...}) proofs =
  let val nthms = map (the o Inttab.lookup proofs) prems
  in Inttab.update (id, (fixes, replay_thm ctxt assumed nthms step)) proofs end

local
  val remove_trigger = mk_meta_eq @{thm SMT2.trigger_def}
  val remove_weight = mk_meta_eq @{thm SMT2.weight_def}
  val remove_fun_app = mk_meta_eq @{thm SMT2.fun_app_def}

  fun rewrite_conv _ [] = Conv.all_conv
    | rewrite_conv ctxt eqs = Simplifier.full_rewrite (empty_simpset ctxt addsimps eqs)

  val prep_rules = [@{thm Let_def}, remove_trigger, remove_weight,
    remove_fun_app, Z3_New_Replay_Literals.rewrite_true]

  fun rewrite _ [] = I
    | rewrite ctxt eqs = Conv.fconv_rule (rewrite_conv ctxt eqs)

  fun lookup_assm assms_net ct =
    Z3_New_Replay_Util.net_instances assms_net ct
    |> map (fn ithm as (_, thm) => (ithm, Thm.cprop_of thm aconvc ct))
in

fun add_asserted outer_ctxt rewrite_rules assms steps ctxt =
  let
    val eqs = map (rewrite ctxt [Z3_New_Replay_Literals.rewrite_true]) rewrite_rules
    val eqs' = union Thm.eq_thm eqs prep_rules

    val assms_net =
      assms
      |> map (apsnd (rewrite ctxt eqs'))
      |> map (apsnd (Conv.fconv_rule Thm.eta_conversion))
      |> Z3_New_Replay_Util.thm_net_of snd 

    fun revert_conv ctxt = rewrite_conv ctxt eqs' then_conv Thm.eta_conversion

    fun assume thm ctxt =
      let
        val ct = Thm.cprem_of thm 1
        val (thm', ctxt') = yield_singleton Assumption.add_assumes ct ctxt
      in (thm' RS thm, ctxt') end

    fun add1 id fixes thm1 ((i, th), exact) ((iidths, thms), (ctxt, ptab)) =
      let
        val (thm, ctxt') = if exact then (Thm.implies_elim thm1 th, ctxt) else assume thm1 ctxt
        val thms' = if exact then thms else th :: thms
      in (((i, (id, th)) :: iidths, thms'), (ctxt', Inttab.update (id, (fixes, thm)) ptab)) end

    fun add (Z3_New_Proof.Z3_Step {id, rule, concl, fixes, ...})
        (cx as ((iidths, thms), (ctxt, ptab))) =
      if Z3_New_Replay_Methods.is_assumption rule andalso rule <> Z3_New_Proof.Hypothesis then
        let
          val ct = SMT2_Util.certify ctxt concl
          val thm1 = Thm.trivial ct |> Conv.fconv_rule (Conv.arg1_conv (revert_conv outer_ctxt))
          val thm2 = singleton (Variable.export ctxt outer_ctxt) thm1
        in
          (case lookup_assm assms_net (Thm.cprem_of thm2 1) of
            [] =>
              let val (thm, ctxt') = assume thm1 ctxt
              in ((iidths, thms), (ctxt', Inttab.update (id, (fixes, thm)) ptab)) end
          | ithms => fold (add1 id fixes thm1) ithms cx)
        end
      else
        cx
  in fold add steps (([], []), (ctxt, Inttab.empty)) end

end

(* |- (EX x. P x) = P c     |- ~ (ALL x. P x) = ~ P c *)
local
  val sk_rules = @{lemma
    "c = (SOME x. P x) ==> (EX x. P x) = P c"
    "c = (SOME x. ~ P x) ==> (~ (ALL x. P x)) = (~ P c)"
    by (metis someI_ex)+}
in

fun discharge_sk_tac i st =
  (rtac @{thm trans} i
   THEN resolve_tac sk_rules i
   THEN (rtac @{thm refl} ORELSE' discharge_sk_tac) (i+1)
   THEN rtac @{thm refl} i) st

end

fun make_discharge_rules rules = rules @ [@{thm allI}, @{thm refl},
  @{thm reflexive}, Z3_New_Replay_Literals.true_thm]

val intro_def_rules = @{lemma
  "(~ P | P) & (P | ~ P)"
  "(P | ~ P) & (~ P | P)"
  by fast+}

fun discharge_assms_tac rules =
  REPEAT (HEADGOAL (resolve_tac (intro_def_rules @ rules) ORELSE' SOLVED' discharge_sk_tac))
  
fun discharge_assms ctxt rules thm =
  (if Thm.nprems_of thm = 0 then
     thm
   else
     (case Seq.pull (discharge_assms_tac rules thm) of
       SOME (thm', _) => thm'
     | NONE => raise THM ("failed to discharge premise", 1, [thm])))
  |> Goal.norm_result ctxt

fun discharge rules outer_ctxt inner_ctxt =
  singleton (Proof_Context.export inner_ctxt outer_ctxt)
  #> discharge_assms outer_ctxt (make_discharge_rules rules)

fun replay outer_ctxt
    ({context=ctxt, typs, terms, rewrite_rules, assms} : SMT2_Translate.replay_data) output =
  let
    val (steps, ctxt2) = Z3_New_Proof.parse typs terms output ctxt
    val ((iidths, rules), (ctxt3, assumed)) = add_asserted outer_ctxt rewrite_rules assms steps ctxt2
  in
    if Config.get ctxt3 SMT2_Config.filter_only_facts then
      ((iidths, steps), TrueI)
    else
      let
        val ctxt4 =
          ctxt3
          |> put_simpset (Z3_New_Replay_Util.make_simpset ctxt3 [])
          |> Config.put SAT.solver (Config.get ctxt3 SMT2_Config.sat_solver)
        val proofs = fold (replay_step ctxt4 assumed) steps assumed
        val (_, Z3_New_Proof.Z3_Step {id, ...}) = split_last steps
        val thm = Inttab.lookup proofs id |> the |> snd |> discharge rules outer_ctxt ctxt4
      in (([], steps), thm) end
  end

end
