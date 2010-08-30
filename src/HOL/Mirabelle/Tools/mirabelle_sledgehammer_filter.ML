(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer_filter.ML
    Author:     Jasmin Blanchette, TU Munich
*)

structure Mirabelle_Sledgehammer_Filter : MIRABELLE_ACTION =
struct

structure Prooftab =
  Table(type key = int * int val ord = prod_ord int_ord int_ord);

val proof_table = Unsynchronized.ref Prooftab.empty

val num_successes = Unsynchronized.ref 0
val num_failures = Unsynchronized.ref 0
val num_found_proofs = Unsynchronized.ref 0
val num_lost_proofs = Unsynchronized.ref 0
val num_found_facts = Unsynchronized.ref 0
val num_lost_facts = Unsynchronized.ref 0

fun init proof_file _ thy =
  let
    fun do_line line =
      case line |> space_explode ":" of
        [line_num, col_num, proof] =>
        SOME (pairself (the o Int.fromString) (line_num, col_num),
              proof |> space_explode " " |> filter_out (curry (op =) ""))
       | _ => NONE
    val proofs = File.read (Path.explode proof_file)
    val proof_tab =
      proofs |> space_explode "\n"
             |> map_filter do_line
             |> AList.coalesce (op =)
             |> Prooftab.make
  in proof_table := proof_tab; thy end

fun percentage a b = if b = 0 then "N/A" else string_of_int (a * 100 div b)
fun percentage_alt a b = percentage a (a + b)

fun done _ ({log, ...} : Mirabelle.done_args) =
  if !num_successes + !num_failures > 0 then
    (log ("Number of overall success: " ^ Int.toString (!num_successes));
     log ("Number of overall failures: " ^ Int.toString (!num_failures));
     log ("Overall success rate: " ^
          percentage_alt (!num_successes) (!num_failures) ^ "%");
     log ("Number of found proofs: " ^ Int.toString (!num_found_proofs));
     log ("Number of lost proofs: " ^ Int.toString (!num_lost_proofs));
     log ("Proof found rate: " ^
          percentage_alt (!num_found_proofs) (!num_lost_proofs) ^ "%");
     log ("Number of found facts: " ^ Int.toString (!num_found_facts));
     log ("Number of lost facts: " ^ Int.toString (!num_lost_facts));
     log ("Fact found rate: " ^
          percentage_alt (!num_found_facts) (!num_lost_facts) ^ "%"))
  else
    ()

val default_max_relevant = 300

fun action args _ ({pre, pos, log, ...} : Mirabelle.run_args) =
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
         val (found_facts, lost_facts) =
           List.concat proofs |> sort_distinct string_ord
           |> List.partition (member (op =) facts)
         val found_proofs = filter (forall (member (op =) facts)) proofs
         val n = length found_proofs
         val _ =
           if n = 0 then
             (num_failures := !num_failures + 1; log "Failure")
           else
             (num_successes := !num_successes + 1;
              num_found_proofs := !num_found_proofs + n;
              log ("Success (" ^ Int.toString n ^ " of " ^
                   Int.toString (length proofs) ^ " proofs)"))
         val _ = num_lost_proofs := !num_lost_proofs + length proofs - n
         val _ = num_found_facts := !num_found_facts + (length found_facts)
         val _ = num_lost_facts := !num_lost_facts + (length lost_facts)
         val _ = if null found_facts then ()
                 else log ("Found facts: " ^ commas found_facts)
         val _ = if null lost_facts then ()
                 else log ("Lost facts: " ^ commas lost_facts)
       in () end
     | NONE => log "No known proof")
  | _ => ()

val proof_fileK = "proof_file"

fun invoke args =
  let
    val (pf_args, other_args) =
      args |> List.partition (curry (op =) proof_fileK o fst)
    val proof_file = case pf_args of
                       [] => error "No \"proof_file\" specified"
                     | (_, s) :: _ => s
  in Mirabelle.register (init proof_file, action other_args, done) end

end;

(* Workaround to keep the "mirabelle.pl" script happy *)
structure Mirabelle_Sledgehammer_filter = Mirabelle_Sledgehammer_Filter;
