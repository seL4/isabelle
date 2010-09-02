(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer_filter.ML
    Author:     Jasmin Blanchette, TU Munich
*)

structure Mirabelle_Sledgehammer_Filter : MIRABELLE_ACTION =
struct

structure SF = Sledgehammer_Filter

val relevance_filter_args =
  [("worse_irrel_freq", SF.worse_irrel_freq),
   ("higher_order_irrel_weight", SF.higher_order_irrel_weight),
   ("abs_rel_weight", SF.abs_rel_weight),
   ("abs_irrel_weight", SF.abs_irrel_weight),
   ("skolem_irrel_weight", SF.skolem_irrel_weight),
   ("theory_const_rel_weight", SF.theory_const_rel_weight),
   ("theory_const_irrel_weight", SF.theory_const_irrel_weight),
   ("intro_bonus", SF.intro_bonus),
   ("elim_bonus", SF.elim_bonus),
   ("simp_bonus", SF.simp_bonus),
   ("local_bonus", SF.local_bonus),
   ("assum_bonus", SF.assum_bonus),
   ("chained_bonus", SF.chained_bonus),
   ("max_imperfect", SF.max_imperfect),
   ("max_imperfect_exp", SF.max_imperfect_exp),
   ("threshold_divisor", SF.threshold_divisor),
   ("ridiculous_threshold", SF.ridiculous_threshold)]

structure Prooftab =
  Table(type key = int * int val ord = prod_ord int_ord int_ord);

val proof_table = Unsynchronized.ref Prooftab.empty

val num_successes = Unsynchronized.ref ([] : (int * int) list)
val num_failures = Unsynchronized.ref ([] : (int * int) list)
val num_found_proofs = Unsynchronized.ref ([] : (int * int) list)
val num_lost_proofs = Unsynchronized.ref ([] : (int * int) list)
val num_found_facts = Unsynchronized.ref ([] : (int * int) list)
val num_lost_facts = Unsynchronized.ref ([] : (int * int) list)

fun get id c = the_default 0 (AList.lookup (op =) (!c) id)
fun add id c n =
  c := (case AList.lookup (op =) (!c) id of
          SOME m => AList.update (op =) (id, m + n) (!c)
        | NONE => (id, n) :: !c)

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

fun done id ({log, ...} : Mirabelle.done_args) =
  if get id num_successes + get id num_failures > 0 then
    (log "";
     log ("Number of overall successes: " ^
          string_of_int (get id num_successes));
     log ("Number of overall failures: " ^ string_of_int (get id num_failures));
     log ("Overall success rate: " ^
          percentage_alt (get id num_successes) (get id num_failures) ^ "%");
     log ("Number of found proofs: " ^ string_of_int (get id num_found_proofs));
     log ("Number of lost proofs: " ^ string_of_int (get id num_lost_proofs));
     log ("Proof found rate: " ^
          percentage_alt (get id num_found_proofs) (get id num_lost_proofs) ^
          "%");
     log ("Number of found facts: " ^ string_of_int (get id num_found_facts));
     log ("Number of lost facts: " ^ string_of_int (get id num_lost_facts));
     log ("Fact found rate: " ^
          percentage_alt (get id num_found_facts) (get id num_lost_facts) ^
          "%"))
  else
    ()

val default_max_relevant = 300

fun with_index (i, s) = s ^ "@" ^ string_of_int i

fun action args id ({pre, pos, log, ...} : Mirabelle.run_args) =
  case (Position.line_of pos, Position.column_of pos) of
    (SOME line_num, SOME col_num) =>
    (case Prooftab.lookup (!proof_table) (line_num, col_num) of
       SOME proofs =>
       let
         val {context = ctxt, facts, goal} = Proof.goal pre
         val thy = ProofContext.theory_of ctxt
         val args =
           args
           |> filter (fn (key, value) =>
                         case AList.lookup (op =) relevance_filter_args key of
                           SOME rf => (rf := the (Real.fromString value); false)
                         | NONE => true)

         val {relevance_thresholds, full_types, max_relevant, ...} =
           Sledgehammer_Isar.default_params thy args
         val subgoal = 1
         val (_, hyp_ts, concl_t) = Sledgehammer_Util.strip_subgoal goal subgoal
         val facts =
           SF.relevant_facts ctxt full_types
               relevance_thresholds
               (the_default default_max_relevant max_relevant)
               {add = [], del = [], only = false} facts hyp_ts concl_t
           |> map (fst o fst)
         val (found_facts, lost_facts) =
           List.concat proofs |> sort_distinct string_ord
           |> map (fn fact => (find_index (curry (op =) fact) facts, fact))
           |> List.partition (curry (op <=) 0 o fst)
           |>> sort (prod_ord int_ord string_ord) ||> map snd
         val found_proofs = filter (forall (member (op =) facts)) proofs
         val n = length found_proofs
         val _ =
           if n = 0 then
             (add id num_failures 1; log "Failure")
           else
             (add id num_successes 1;
              add id num_found_proofs n;
              log ("Success (" ^ string_of_int n ^ " of " ^
                   string_of_int (length proofs) ^ " proofs)"))
         val _ = add id num_lost_proofs (length proofs - n)
         val _ = add id num_found_facts (length found_facts)
         val _ = add id num_lost_facts (length lost_facts)
         val _ =
           if null found_facts then
             ()
           else
             let
               val found_weight =
                 Real.fromInt (fold (fn (n, _) =>
                                        Integer.add (n * n)) found_facts 0)
                   / Real.fromInt (length found_facts)
                 |> Math.sqrt |> Real.ceil
             in
               log ("Found facts (among " ^ string_of_int (length facts) ^
                    ", weight " ^ string_of_int found_weight ^ "): " ^
                    commas (map with_index found_facts))
             end
         val _ = if null lost_facts then
                   ()
                 else
                   log ("Lost facts (among " ^ string_of_int (length facts) ^
                        "): " ^ commas lost_facts)
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
