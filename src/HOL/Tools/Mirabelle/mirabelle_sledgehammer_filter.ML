(*  Title:      HOL/Mirabelle/Tools/mirabelle_sledgehammer_filter.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Makarius

Mirabelle action: "sledgehammer_filter".
*)

structure Mirabelle_Sledgehammer_Filter: sig end =
struct

fun get args name default_value =
  case AList.lookup (op =) args name of
    SOME value => Value.parse_real value
  | NONE => default_value

fun extract_relevance_fudge args
      {local_const_multiplier, worse_irrel_freq, higher_order_irrel_weight, abs_rel_weight,
       abs_irrel_weight, theory_const_rel_weight, theory_const_irrel_weight,
       chained_const_irrel_weight, intro_bonus, elim_bonus, simp_bonus, local_bonus, assum_bonus,
       chained_bonus, max_imperfect, max_imperfect_exp, threshold_divisor, ridiculous_threshold} =
  {local_const_multiplier = get args "local_const_multiplier" local_const_multiplier,
   worse_irrel_freq = get args "worse_irrel_freq" worse_irrel_freq,
   higher_order_irrel_weight = get args "higher_order_irrel_weight" higher_order_irrel_weight,
   abs_rel_weight = get args "abs_rel_weight" abs_rel_weight,
   abs_irrel_weight = get args "abs_irrel_weight" abs_irrel_weight,
   theory_const_rel_weight = get args "theory_const_rel_weight" theory_const_rel_weight,
   theory_const_irrel_weight = get args "theory_const_irrel_weight" theory_const_irrel_weight,
   chained_const_irrel_weight = get args "chained_const_irrel_weight" chained_const_irrel_weight,
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

fun print_int x = Value.print_int (! x)

fun percentage a b = if b = 0 then "N/A" else Value.print_int (a * 100 div b)
fun percentage_alt a b = percentage a (a + b)

val default_prover = ATP_Proof.eN (* arbitrary ATP *)

fun with_index (i, s) = s ^ "@" ^ Value.print_int i

val proof_fileK = "proof_file"

val _ =
  Theory.setup (Mirabelle.theory_action \<^binding>\<open>sledgehammer_filter\<close>
    (fn context => fn commands =>
      let
        val (proof_table, args) =
          let
            val (pf_args, other_args) =
              #arguments context |> List.partition (curry (op =) proof_fileK o fst)
            val proof_file =
              (case pf_args of
                [] => error "No \"proof_file\" specified"
              | (_, s) :: _ => s)
            fun do_line line =
              (case line |> space_explode ":" of
                [line_num, offset, proof] =>
                  SOME (apply2 (the o Int.fromString) (line_num, offset),
                    proof |> space_explode " " |> filter_out (curry (op =) ""))
              | _ => NONE)
            val proof_table =
              File.read (Path.explode proof_file)
              |> space_explode "\n"
              |> map_filter do_line
              |> AList.coalesce (op =)
              |> Prooftab.make
          in (proof_table, other_args) end

        val num_successes = Unsynchronized.ref 0
        val num_failures = Unsynchronized.ref 0
        val num_found_proofs = Unsynchronized.ref 0
        val num_lost_proofs = Unsynchronized.ref 0
        val num_found_facts = Unsynchronized.ref 0
        val num_lost_facts = Unsynchronized.ref 0

        val results =
          commands |> maps (fn {pos, pre, ...} =>
            (case (Position.line_of pos, Position.offset_of pos) of
              (SOME line_num, SOME offset) =>
                (case Prooftab.lookup proof_table (line_num, offset) of
                  SOME proofs =>
                    let
                      val thy = Proof.theory_of pre
                      val {context = ctxt, facts = chained_ths, goal} = Proof.goal pre
                      val prover = AList.lookup (op =) args "prover" |> the_default default_prover
                      val params as {max_facts, ...} = Sledgehammer_Commands.default_params thy args
                      val default_max_facts =
                        Sledgehammer_Prover_Minimize.default_max_facts_of_prover ctxt prover
                      val relevance_fudge =
                        extract_relevance_fudge args Sledgehammer_MePo.default_relevance_fudge
                      val subgoal = 1
                      val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal subgoal ctxt
                      val ho_atp = Sledgehammer_Prover_ATP.is_ho_atp ctxt prover
                      val keywords = Thy_Header.get_keywords' ctxt
                      val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
                      val facts =
                        Sledgehammer_Fact.nearly_all_facts ctxt ho_atp
                          Sledgehammer_Fact.no_fact_override keywords css_table chained_ths
                          hyp_ts concl_t
                        |> Sledgehammer_Fact.drop_duplicate_facts
                        |> Sledgehammer_MePo.mepo_suggested_facts ctxt params
                            (the_default default_max_facts max_facts)
                            (SOME relevance_fudge) hyp_ts concl_t
                        |> map (fst o fst)
                      val (found_facts, lost_facts) =
                        flat proofs |> sort_distinct string_ord
                        |> map (fn fact => (find_index (curry (op =) fact) facts, fact))
                        |> List.partition (curry (op <=) 0 o fst)
                        |>> sort (prod_ord int_ord string_ord) ||> map snd
                      val found_proofs = filter (forall (member (op =) facts)) proofs
                      val n = length found_proofs
                      val log1 =
                        if n = 0 then
                          (Unsynchronized.inc num_failures; "Failure")
                        else
                          (Unsynchronized.inc num_successes;
                           Unsynchronized.add num_found_proofs n;
                           "Success (" ^ Value.print_int n ^ " of " ^
                             Value.print_int (length proofs) ^ " proofs)")
                      val _ = Unsynchronized.add num_lost_proofs (length proofs - n)
                      val _ = Unsynchronized.add num_found_facts (length found_facts)
                      val _ = Unsynchronized.add num_lost_facts (length lost_facts)
                      val log2 =
                        if null found_facts then []
                        else
                          let
                            val found_weight =
                              Real.fromInt (fold (fn (n, _) => Integer.add (n * n)) found_facts 0)
                                / Real.fromInt (length found_facts)
                              |> Math.sqrt |> Real.ceil
                          in
                            ["Found facts (among " ^ Value.print_int (length facts) ^
                             ", weight " ^ Value.print_int found_weight ^ "): " ^
                             commas (map with_index found_facts)]
                          end
                      val log3 =
                        if null lost_facts then []
                        else
                          ["Lost facts (among " ^ Value.print_int (length facts) ^ "): " ^
                           commas lost_facts]
                    in [XML.Text (cat_lines (log1 :: log2 @ log3))] end
                | NONE => [XML.Text "No known proof"])
            | _ => []))

        val report =
          if ! num_successes + ! num_failures > 0 then
            let
              val props =
                [("num_successes", print_int num_successes),
                 ("num_failures", print_int num_failures),
                 ("num_found_proofs", print_int num_found_proofs),
                 ("num_lost_proofs", print_int num_lost_proofs),
                 ("num_found_facts", print_int num_found_facts),
                 ("num_lost_facts", print_int num_lost_facts)]
              val text =
                "\nNumber of overall successes: " ^ print_int num_successes ^
                "\nNumber of overall failures: " ^ print_int num_failures ^
                "\nOverall success rate: " ^
                    percentage_alt (! num_successes) (! num_failures) ^ "%" ^
                "\nNumber of found proofs: " ^ print_int num_found_proofs ^
                "\nNumber of lost proofs: " ^ print_int num_lost_proofs ^
                "\nProof found rate: " ^
                    percentage_alt (! num_found_proofs) (! num_lost_proofs) ^ "%" ^
                "\nNumber of found facts: " ^ print_int num_found_facts ^
                "\nNumber of lost facts: " ^ print_int num_lost_facts ^
                "\nFact found rate: " ^
                    percentage_alt (! num_found_facts) (! num_lost_facts) ^ "%"
            in [Mirabelle.log_report props [XML.Text text]] end
          else []
      in results @ report end))

end
