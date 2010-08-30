(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer_filter.ML
    Author:     Jasmin Blanchette, TU Munich
*)

structure Mirabelle_Sledgehammer_Filter : MIRABELLE_ACTION =
struct

structure Prooftab =
  Table(type key = int * int val ord = prod_ord int_ord int_ord);

val proof_table = Unsynchronized.ref Prooftab.empty

fun init id thy =
  let
    fun do_line line =
      case line |> space_explode ":" of
        [line_num, col_num, proof] =>
        SOME (pairself (the o Int.fromString) (line_num, col_num),
              proof |> space_explode " " |> filter_out (curry (op =) ""))
       | _ => NONE
    val proofs = File.read (Path.explode "$HOME/Judgement/AllProofs/NS_Shared.txt")
    val proof_tab =
      proofs |> space_explode "\n"
             |> map_filter do_line
             |> AList.coalesce (op =)
             |> Prooftab.make
  in proof_table := proof_tab; thy end

fun done id (args : Mirabelle.done_args) = ()

val default_max_relevant = 300

fun action args id ({pre, pos, ...} : Mirabelle.run_args) =
  case (Position.line_of pos, Position.column_of pos) of
    (SOME line_num, SOME col_num) =>
    (case Prooftab.lookup (!proof_table) (line_num, col_num) of
       SOME proofs =>
       let
         val {context = ctxt, facts, goal} = Proof.goal pre
         val thy = ProofContext.theory_of ctxt
         val {relevance_thresholds, full_types, max_relevant, theory_relevant,
              ...} = Sledgehammer_Isar.default_params thy args
         val subgoal = 1
         val (_, hyp_ts, concl_t) = Sledgehammer_Util.strip_subgoal goal subgoal
         val facts =
           Sledgehammer_Fact_Filter.relevant_facts ctxt full_types
               relevance_thresholds
               (the_default default_max_relevant max_relevant)
               (the_default false theory_relevant)
               {add = [], del = [], only = false} facts hyp_ts concl_t
           |> map (fst o fst)
         val (found_facts, missing_facts) =
           List.concat proofs |> sort_distinct string_ord
           |> List.partition (member (op =) facts)
         val found_proofs = filter (forall (member (op =) facts)) proofs
         val _ =
           case length found_proofs of
             0 => writeln "Failure"
           | n => writeln ("Success (" ^ Int.toString n ^ " of " ^
                           Int.toString (length proofs) ^ " proofs)")
         val _ = writeln ("Found facts: " ^ commas found_facts)
         val _ = writeln ("Missing facts: " ^ commas missing_facts)
       in () end
     | NONE => ())
  | _ => ()

fun invoke args = Mirabelle.register (init, action args, done)

end;
