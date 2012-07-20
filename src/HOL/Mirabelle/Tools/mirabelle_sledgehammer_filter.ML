(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer_filter.ML
    Author:     Jasmin Blanchette, TU Munich
*)

structure Mirabelle_Sledgehammer_Filter : MIRABELLE_ACTION =
struct

fun get args name default_value =
  case AList.lookup (op =) args name of
    SOME value => the (Real.fromString value)
  | NONE => default_value

fun extract_relevance_fudge args
      {local_const_multiplier, worse_irrel_freq, higher_order_irrel_weight,
       abs_rel_weight, abs_irrel_weight, skolem_irrel_weight,
       theory_const_rel_weight, theory_const_irrel_weight,
       chained_const_irrel_weight, intro_bonus, elim_bonus, simp_bonus,
       local_bonus, assum_bonus, chained_bonus, max_imperfect, max_imperfect_exp,
       threshold_divisor, ridiculous_threshold} =
  {local_const_multiplier =
       get args "local_const_multiplier" local_const_multiplier,
   worse_irrel_freq = get args "worse_irrel_freq" worse_irrel_freq,
   higher_order_irrel_weight =
       get args "higher_order_irrel_weight" higher_order_irrel_weight,
   abs_rel_weight = get args "abs_rel_weight" abs_rel_weight,
   abs_irrel_weight = get args "abs_irrel_weight" abs_irrel_weight,
   skolem_irrel_weight = get args "skolem_irrel_weight" skolem_irrel_weight,
   theory_const_rel_weight =
       get args "theory_const_rel_weight" theory_const_rel_weight,
   theory_const_irrel_weight =
       get args "theory_const_irrel_weight" theory_const_irrel_weight,
   chained_const_irrel_weight =
       get args "chained_const_irrel_weight" chained_const_irrel_weight,
   intro_bonus = get args "intro_bonus" intro_bonus,
   elim_bonus = get args "elim_bonus" elim_bonus,
   simp_bonus = get args "simp_bonus" simp_bonus,
   local_bonus = get args "local_bonus" local_bonus,
   assum_bonus = get args "assum_bonus" assum_bonus,
   chained_bonus = get args "chained_bonus" chained_bonus,
   max_imperfect = get args "max_imperfect" max_imperfect,
   max_imperfect_exp = get args "max_imperfect_exp" max_imperfect_exp,
   threshold_divisor = get args "threshold_divisor" threshold_divisor,
   ridiculous_threshold = get args "ridiculous_threshold" ridiculous_threshold}

structure Prooftab =
  Table(type key = int * int val ord = prod_ord int_ord int_ord)

val proof_table = Unsynchronized.ref (Prooftab.empty: string list list Prooftab.table)

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
        [line_num, offset, proof] =>
        SOME (pairself (the o Int.fromString) (line_num, offset),
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

val default_prover = ATP_Systems.eN (* arbitrary ATP *)

fun with_index (i, s) = s ^ "@" ^ string_of_int i

fun action args id ({pre, pos, log, ...} : Mirabelle.run_args) =
  case (Position.line_of pos, Position.offset_of pos) of
    (SOME line_num, SOME offset) =>
    (case Prooftab.lookup (!proof_table) (line_num, offset) of
       SOME proofs =>
       let
         val {context = ctxt, facts = chained_ths, goal} = Proof.goal pre
         val prover = AList.lookup (op =) args "prover"
                      |> the_default default_prover
         val params as {max_facts, slice, ...} =
           Sledgehammer_Isar.default_params ctxt args
         val default_max_facts =
           Sledgehammer_Provers.default_max_facts_for_prover ctxt slice prover
         val is_appropriate_prop =
           Sledgehammer_Provers.is_appropriate_prop_for_prover ctxt
               default_prover
         val relevance_fudge =
           extract_relevance_fudge args
               (Sledgehammer_Provers.relevance_fudge_for_prover ctxt prover)
         val subgoal = 1
         val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal subgoal
         val ho_atp = Sledgehammer_Provers.is_ho_atp ctxt prover
         val reserved = Sledgehammer_Util.reserved_isar_keyword_table ()
         val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
         val facts =
           Sledgehammer_Fact.nearly_all_facts ctxt ho_atp
               Sledgehammer_Fact.no_fact_override reserved css_table chained_ths
               hyp_ts concl_t
           |> filter (is_appropriate_prop o prop_of o snd)
           |> Sledgehammer_MePo.iterative_relevant_facts ctxt params
                  default_prover (the_default default_max_facts max_facts)
                  (SOME relevance_fudge) hyp_ts concl_t
            |> map ((fn name => name ()) o fst o fst)
         val (found_facts, lost_facts) =
           flat proofs |> sort_distinct string_ord
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
