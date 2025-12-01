(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_instantiations.ML
    Author:     Lukas Bartl, Universitaet Augsburg

Inference of Variable Instantiations with Metis.
*)

signature SLEDGEHAMMER_INSTANTIATIONS =
sig
  type stature = ATP_Problem_Generate.stature

  val instantiate_facts : Proof.state -> bool -> Time.time -> thm -> int ->
    (string * stature) list -> (Pretty.T * stature) list option
end;

structure Sledgehammer_Instantiations : SLEDGEHAMMER_INSTANTIATIONS =
struct

open ATP_Util
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Proof_Methods
open Sledgehammer_Util

(* metis with different options, last two with extensionality *)
fun metis_methods ctxt =
  let
    val ext_facts = [short_thm_name ctxt ext]
  in
    [Metis_Method (NONE, NONE, []),
     Metis_Method (SOME really_full_type_enc, SOME liftingN, []),
     Metis_Method (SOME no_typesN, SOME liftingN, ext_facts),
     Metis_Method (SOME full_typesN, SOME liftingN, ext_facts)]
  end

(* Infer variable instantiations using metis with the given options
 * (cf. tac_of_metis in Sledgehammer_Proof_Methods.tac_of_proof_method) *)
fun infer_thm_insts (Metis_Method (type_enc_opt, lam_trans_opt, additional_fact_names)) thms ctxt =
  let
    val additional_facts = maps (thms_of_name ctxt) additional_fact_names
    val ctxt = ctxt
      |> Config.put Metis_Tactic.verbose false
      |> Config.put Metis_Tactic.trace false
  in
    Metis_Tactic.metis_infer_thm_insts ((Option.map single type_enc_opt, lam_trans_opt),
      additional_facts @ thms) ctxt
  end

(* Infer variable instantiations of theorems with timeout *)
fun timed_infer_thm_insts ctxt verbose timeout chained goal subgoal fact_thms metis_method =
  let
    val thms = maps snd fact_thms
    val timing = Timing.start ()
    val opt_thm_insts =
      try (Timeout.apply timeout (infer_thm_insts metis_method thms ctxt chained subgoal)) goal
      |> Option.join
    val {cpu = time, ...} = Timing.result timing
    val _ =
      if verbose then
       (let
          val meth_str = string_of_proof_method (map (fst o fst) fact_thms) metis_method
          val time_str = string_of_time time
        in
          if is_some opt_thm_insts then
            writeln ("Inferred variable instantiations with " ^ meth_str ^
              " (" ^ time_str ^ ")")
          else
            writeln ("Could not infer variable instantiations with " ^ meth_str ^
              " (tried " ^ time_str ^ ")")
        end)
      else
        ()
  in
    opt_thm_insts
  end

(* Try to infer variable instantiations of facts and instantiate them
 * using of-instantiations (e.g. "assms(1)[of x]") *)
fun instantiate_facts state verbose timeout goal subgoal facts =
  let
    val ctxt = Proof.context_of state
    val {facts = chained, ...} = Proof.goal state
    val goal = Thm.solve_constraints goal (* avoid exceptions *)
    val fact_thms = AList.make (thms_of_name ctxt o fst) facts
    val timed_infer_thm_insts =
      timed_infer_thm_insts ctxt verbose timeout chained goal subgoal fact_thms
    fun infer_thm_insts [] = NONE
      | infer_thm_insts (metis_method :: metis_methods) =
        (case timed_infer_thm_insts metis_method of
          NONE => infer_thm_insts metis_methods
        | SOME (_ (* using_thm_insts *), arg_thm_insts) => SOME arg_thm_insts)
    fun instantiate_fact ((name, stature), ths) thm_insts =
      List.partition (member Thm.eq_thm ths o fst) thm_insts
      |>> map (fn (_, inst) => (Metis_Tactic.pretty_name_inst ctxt (name, inst), stature))
  in
    infer_thm_insts (metis_methods ctxt)
    |> Option.map (flat o fst o fold_map instantiate_fact fact_thms)
    |> verbose ? tap (Option.app (fn inst_facts =>
        Pretty.str "Instantiated facts:" :: map fst inst_facts
        |> Pretty.block o Pretty.breaks
        |> Pretty.writeln))
  end

end;
