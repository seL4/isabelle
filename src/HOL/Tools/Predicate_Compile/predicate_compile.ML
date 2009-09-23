(* Author: Lukas Bulwahn, TU Muenchen

*)
signature PREDICATE_COMPILE =
sig
  val setup : theory -> theory
end;

structure Predicate_Compile : PREDICATE_COMPILE =
struct

open Predicate_Compile_Aux;

val priority = tracing;

(* Some last processing *)
fun remove_pointless_clauses intro =
  if Logic.strip_imp_prems (prop_of intro) = [@{prop "False"}] then
    []
  else [intro]

fun preprocess_strong_conn_constnames gr constnames thy =
  let
    val get_specs = map (fn k => (k, Graph.get_node gr k))
    val _ = priority ("Preprocessing scc of " ^ commas constnames)
    val (prednames, funnames) = List.partition (is_pred thy) constnames
    (* untangle recursion by defining predicates for all functions *)
    val _ = priority "Compiling functions to predicates..."
    val _ = Output.tracing ("funnames: " ^ commas funnames)
    val thy' =
      thy |> not (null funnames) ? Predicate_Compile_Fun.define_predicates
      (get_specs funnames)
    val _ = priority "Compiling predicates to flat introrules..."
    val (intross, thy'') = apfst flat (fold_map Predicate_Compile_Pred.preprocess
      (get_specs prednames) thy')
    val _ = tracing ("intross: " ^ commas (map (Display.string_of_thm_global thy'') (flat intross)))
    val _ = priority "Replacing functions in introrules..."
    val intross' = burrow (maps (Predicate_Compile_Fun.rewrite_intro thy'')) intross
    val intross'' = burrow (maps remove_pointless_clauses) intross
    val thy''' = fold Predicate_Compile_Core.register_intros intross'' thy''
  in
    thy'''
  end;

fun code_pred_cmd ((inductify_all, rpred), raw_const) lthy =
  if inductify_all then
    let
      val thy = ProofContext.theory_of lthy
      val const = Code.read_const thy raw_const
      val _ = Output.tracing ("fetching definition from theory")
      val table = Pred_Compile_Data.make_const_spec_table thy
      val gr = Pred_Compile_Data.obtain_specification_graph table const
      val _ = Output.tracing (commas (Graph.all_succs gr [const]))
      val gr = Graph.subgraph (member (op =) (Graph.all_succs gr [const])) gr
	    val lthy' = LocalTheory.theory (fold_rev (preprocess_strong_conn_constnames gr)
      (Graph.strong_conn gr)) lthy
        |> LocalTheory.checkpoint
    in Predicate_Compile_Core.code_pred_cmd rpred raw_const lthy' end
  else
    Predicate_Compile_Core.code_pred_cmd rpred raw_const lthy

val setup = Predicate_Compile_Fun.setup_oracle #> Predicate_Compile_Core.setup

val _ = List.app OuterKeyword.keyword ["inductify_all", "rpred"]

local structure P = OuterParse
in

val _ = OuterSyntax.local_theory_to_proof "code_pred"
  "prove equations for predicate specified by intro/elim rules"
  OuterKeyword.thy_goal (P.opt_keyword "inductify_all" -- P.opt_keyword "rpred" -- P.term_group >> code_pred_cmd)

end

end
