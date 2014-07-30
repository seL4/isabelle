(*  Title:      HOL/Tools/ATP/atp_satallax.ML
    Author:     Mathias Fleury, ENS Rennes
    Author:     Jasmin Blanchette, TU Muenchen

Satallax proof parser and transformation for Sledgehammer.
*)

signature ATP_SATALLAX =
sig
  val atp_proof_of_tstplike_proof : string -> string ATP_Proof.atp_problem -> string ->
    string ATP_Proof.atp_proof
end;

structure ATP_Satallax : ATP_SATALLAX =
struct

open ATP_Proof
open ATP_Util
open ATP_Problem

(*Undocumented format:
thf (number, plain | Axiom | ..., inference(rule, [status(thm), assumptions ([hypotheses list]),
detailed_rule(discharge,used_hypothese_list) *], used_hypotheses_list, premises))
(seen by tab_mat)

Also seen -- but we can ignore it:
"tab_inh (a) __11." meaning that the type a is inhabited usueful of variable eigen__11,
*)
fun parse_satallax_tstp_information x =
  ((Symbol.scan_ascii_id || ($$ "$" |-- Symbol.scan_ascii_id))
  -- Scan.option ( $$ "(" |-- Scan.option (Symbol.scan_ascii_id --| $$ ",")
  -- ((Scan.option (($$ "[" |-- (Scan.option ((scan_general_id
           -- Scan.repeat ($$ "," |-- scan_general_id)) >> uncurry cons) --| $$ "]"))
        || skip_term >> K NONE) >> (fn (SOME x) => x | NONE => NONE)) --| $$ ")"))) x

fun parse_prem x =
  ((Symbol.scan_ascii_id || scan_general_id) --| Scan.option ($$ ":" -- skip_term)) x

fun parse_prems x =
  (($$ "[" |-- parse_prem -- Scan.repeat ($$ "," |-- parse_prem) --| $$ "]")
     >> uncurry cons) x

fun parse_tstp_satallax_extra_arguments x =
  ($$ "," |-- scan_general_id -- (($$ "(" |-- Symbol.scan_ascii_id --| $$ "," )
  -- ($$ "[" |-- Scan.option ((parse_satallax_tstp_information
  -- Scan.repeat ($$ "," |-- parse_satallax_tstp_information)) >> uncurry cons)
  --| $$ "]") --
  (Scan.optional ($$ "," |-- parse_prems) [] -- Scan.optional ($$ "," |-- parse_prems) []
    >> (fn (x, []) => x | (_, x) => x))
   --| $$ ")")) x

val dummy_satallax_step = ((("~1", "tab_inh"), AAtom (ATerm(("False", []), []))), NONE)
fun parse_tstp_thf0_satallax_line x =
  (((Scan.this_string tptp_thf
  -- $$ "(") |-- scan_general_id --| $$ "," -- Symbol.scan_ascii_id --| $$ ","
  -- parse_thf0_formula -- Scan.option parse_tstp_satallax_extra_arguments --| $$ ")" --| $$ ".")
  || (Scan.this_string "tab_inh" |-- skip_term --| $$ ".")
     >> K dummy_satallax_step) x


datatype satallax_step = Satallax_Step of {
  id: string,
  role: string,
  theorem: (string, string, (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, string)
    ATP_Problem.atp_formula,
  assumptions: string list,
  rule: string,
  used_assumptions: string list,
  generated_goal_assumptions: (string * string list) list}

fun mk_satallax_step id role theorem assumptions rule used_assumptions
      generated_goal_assumptions =
    Satallax_Step {id = id, role = role, theorem = theorem, assumptions = assumptions, rule = rule,
      used_assumptions = used_assumptions, generated_goal_assumptions = generated_goal_assumptions}

fun get_assumptions (("assumptions", SOME (_ , assumptions)) :: _) =
    the_default [] assumptions
  | get_assumptions (_ :: l) = get_assumptions l
  | get_assumptions [] = []

fun seperate_dependices dependencies =
    let
      fun sep_dep [] used_assumptions new_goals generated_assumptions _ =
          (used_assumptions, new_goals, generated_assumptions)
        | sep_dep (x :: l) used_assumptions new_goals generated_assumptions state =
          if hd (raw_explode x) = "h" orelse Int.fromString x = NONE  then
            if state = 0 then
              sep_dep l (x :: used_assumptions) new_goals generated_assumptions state
            else
              sep_dep l used_assumptions new_goals (x :: generated_assumptions) 3
          else
            if state = 1 orelse state = 0 then
              sep_dep l used_assumptions (x :: new_goals) generated_assumptions 1
            else
              raise Fail ("incorrect Satallax proof" ^ PolyML.makestring l)
    in
      sep_dep dependencies [] [] [] 0
    end

fun create_grouped_goal_assumption rule new_goals generated_assumptions =
    if length new_goals = length generated_assumptions then
      new_goals ~~ (map single generated_assumptions)
    else if 2 * length new_goals = length generated_assumptions then
      let
        fun group_by_pair (new_goal :: new_goals) (assumpt1 :: assumpt2 :: generated_assumptions) =
            (new_goal, [assumpt1, assumpt2]) :: group_by_pair new_goals generated_assumptions
          | group_by_pair [] [] = []
      in
        group_by_pair new_goals generated_assumptions
      end
    else
      raise Fail ("the rule " ^ rule ^" is not supported in the reconstruction.")

fun to_satallax_step (((id, role), formula), (SOME (_,((rule, l), used_rules)))) =
    let
      val (used_assumptions, new_goals, generated_assumptions) = seperate_dependices used_rules
    in
      mk_satallax_step id role formula (get_assumptions (the_default [] l)) rule used_assumptions
        (create_grouped_goal_assumption rule new_goals generated_assumptions)
    end
  | to_satallax_step (((id, role), formula), NONE) =
    mk_satallax_step id role formula [] "assumption" [] []

fun is_assumption (Satallax_Step {role, ...}) = role = "assumption" orelse role = "axiom" orelse
  role = "negated_conjecture" orelse role = "conjecture"

fun seperate_assumptions_and_steps l =
    let
      fun seperate_assumption [] l l' = (l, l')
        | seperate_assumption (step :: steps) l l' =
          if is_assumption step then
            seperate_assumption steps (step :: l) l'
          else
            seperate_assumption steps l (step :: l')
    in
      seperate_assumption l [] []
    end

datatype satallax_proof_graph =
  Node_Source of {node: satallax_step, succs: satallax_proof_graph list} |
  Node_Conclusion of {node: satallax_step, deps: satallax_proof_graph list}

fun find_proof_step ((x as Satallax_Step {id, ...}) :: l) h =
    if h = id then x else find_proof_step l h
  | find_proof_step [] h = raise Fail ("not_found: " ^ PolyML.makestring h)

fun remove_not_not (x as ATerm ((op1, _), [ATerm ((op2, _), [th])])) =
    if op1 = op2 andalso op1 = tptp_not then th else x
  | remove_not_not th = th

fun tptp_term_equal (ATerm((op1, _), l1), ATerm((op2, _), l2)) = op1 = op2 andalso
    fold2 (fn t1 => fn t2 => fn c => c andalso t1 = t2) l1 l2 true
  | tptp_term_equal (_, _) = false

fun find_assumptions_to_inline ths (assm :: assms) to_inline no_inline =
    (case List.find (curry (op =) assm o fst) no_inline of
      SOME _ => find_assumptions_to_inline ths assms to_inline no_inline
    | NONE =>
      (case List.find (curry (op =) assm o fst) to_inline of
        NONE => find_assumptions_to_inline ths assms to_inline no_inline
      | SOME (_, th) =>
        let
          val simplified_ths_with_inlined_assumption =
              (case List.partition (curry tptp_term_equal th o remove_not_not) ths of
                ([], ths) => ATerm ((tptp_not, [dummy_atype]), [th]) :: ths
              | (_, _) => [])
        in
          find_assumptions_to_inline simplified_ths_with_inlined_assumption assms to_inline no_inline
        end))
  | find_assumptions_to_inline ths [] _ _ = ths

fun inline_if_needed_and_simplify th assms to_inline no_inline =
    (case find_assumptions_to_inline [th] assms to_inline no_inline of
      [] => ATerm (("$true", [dummy_atype]), [])
  | l => foldl1 (fn (a, b) => ATerm ((tptp_or, [dummy_atype]), [a, b])) l)


fun get_conclusion (Satallax_Step {theorem = AAtom theorem, ...}) = theorem

fun add_assumption new_used_assumptions  ((Satallax_Step {id, role, theorem, assumptions,
      rule, generated_goal_assumptions, used_assumptions})) =
    mk_satallax_step id role theorem assumptions rule (new_used_assumptions @ used_assumptions)
      generated_goal_assumptions

fun set_rule new_rule (Satallax_Step {id, role, theorem, assumptions,
      generated_goal_assumptions, used_assumptions, ...}) =
    mk_satallax_step id role theorem assumptions new_rule used_assumptions
      generated_goal_assumptions

fun transform_inline_assumption hypotheses_step proof_sketch =
  let
    fun inline_in_step (Node_Source {node as Satallax_Step {generated_goal_assumptions,
                                                            used_assumptions, rule, ...}, succs}) =
        if generated_goal_assumptions = [] then
            Node_Source {node = node, succs = []}
        else
          let
            (*one singel goal is created, two hypothesis can be created, for the "and" rule:
              (A /\ B) create two hypotheses A, and B.*)
            fun set_hypotheses_as_goal [hypothesis] succs =
                Node_Source {node = set_rule rule
                    (add_assumption used_assumptions (find_proof_step hypotheses_step hypothesis)),
                  succs = map inline_in_step succs}
              | set_hypotheses_as_goal (hypothesis :: new_goal_hypotheses) succs =
                Node_Source {node = set_rule rule
                    (add_assumption used_assumptions (find_proof_step hypotheses_step hypothesis)),
                  succs = [set_hypotheses_as_goal new_goal_hypotheses succs]}
          in
            set_hypotheses_as_goal (snd (hd generated_goal_assumptions)) succs
          end
      | inline_in_step (Node_Conclusion {node = node, deps}) =
        Node_Conclusion {node = node, deps = map inline_in_step deps}

    fun inline_contradictory_assumptions (Node_Source {node as Satallax_Step{id, theorem, ...},
           succs}) (to_inline, no_inline) =
        let
          val (succs, inliner) = fold_map inline_contradictory_assumptions
                                          succs (to_inline, (id, theorem) :: no_inline)
        in
          (Node_Source {node = node, succs = succs}, inliner)
        end
      | inline_contradictory_assumptions (Node_Conclusion {node = Satallax_Step {id, role,
          theorem = AAtom theorem, assumptions, rule, generated_goal_assumptions,
          used_assumptions}, deps}) (to_inline, no_inline) =
        let
          val (dep', (to_inline', no_inline')) = fold_map inline_contradictory_assumptions
                                                          deps (to_inline, no_inline)
          val to_inline'' = map (fn s => (s, get_conclusion (find_proof_step hypotheses_step s)))
                                (List.filter (fn s => nth_string s 0 = "h")
                                             (used_assumptions @
                                               (map snd generated_goal_assumptions |> flat)))
                            @ to_inline'
          val node' = Satallax_Step {id = id, role = role, theorem =
                AAtom (inline_if_needed_and_simplify theorem assumptions to_inline'' no_inline'),
              assumptions = assumptions, rule = rule,
              generated_goal_assumptions = generated_goal_assumptions,
              used_assumptions =
                List.filter (fn s => List.find (curry (op =) s o fst) to_inline = NONE)
                used_assumptions}
        in
          (Node_Conclusion {node = node', deps = dep'}, (to_inline'', no_inline'))
        end
  in
    fst (inline_contradictory_assumptions (inline_in_step proof_sketch) ([], []))
  end

fun correct_dependencies (Node_Source {node, succs}) =
    Node_Source {node = node, succs = map correct_dependencies succs}
  | correct_dependencies (Node_Conclusion {node, deps}) =
    let
      val new_used_assumptions =
          map (fn Node_Source {node = (Satallax_Step{id, ...}), ...} => id
                | Node_Conclusion {node = (Satallax_Step{id, ...}), ...} => id) deps
    in
      Node_Conclusion {node = add_assumption new_used_assumptions node,
        deps = map correct_dependencies deps}
    end

fun create_satallax_proof_graph (hypotheses_step, proof_sketch) =
    let
      fun create_step (step as Satallax_Step {generated_goal_assumptions, ...}) =
        Node_Source {node = step,
          succs = map (create_step o (find_proof_step (hypotheses_step @ proof_sketch)))
            (map fst generated_goal_assumptions)}
      fun reverted_discharged_steps is_branched (Node_Source {node as
            Satallax_Step {generated_goal_assumptions, ...}, succs}) =
          if is_branched orelse length generated_goal_assumptions > 1 then
            Node_Conclusion {node = node, deps = map (reverted_discharged_steps true) succs}
          else
            Node_Source {node = node, succs = map (reverted_discharged_steps is_branched) succs}
      val proof_with_correct_sense =
          correct_dependencies (reverted_discharged_steps false
            (create_step (find_proof_step proof_sketch "0" )))
    in
      transform_inline_assumption hypotheses_step proof_with_correct_sense
    end

val satallax_known_theorems = ["eq_ind", "eq_trans2", "eq_trans3", "eq_neg_neg_id", "eq_true",
    "eq_and_nor", "eq_or_nand", "eq_or_imp", "eq_and_imp", "eq_imp_or", "eq_iff", "eq_sym_eq",
    "eq_forall_nexists", "eq_exists_nforall", "eq_leib1", "eq_leib2", "eq_leib3", "eq_leib4",
    "eq_eta", "SinhE", "eq_forall_Seps", "eq_SPi_Seps", "eq_exists_Seps"]
val is_special_satallax_rule = member (op =) satallax_known_theorems


fun transform_to_standard_atp_step proof =
    let
      fun create_fact_step id =
        ((id, [id]), Axiom, AAtom (ATerm((id, []), [])), "", [])
      fun transform_one_step (Satallax_Step {id, theorem, used_assumptions, role, rule, ...}) =
        let
          val role' = role_of_tptp_string role
        in
          map create_fact_step
            (List.filter (fn s => size s >=4 andalso not (is_special_satallax_rule s))
            used_assumptions)
          @ [((id, []), if role' = Unknown then Plain else role', theorem, rule,
              map (fn s => (s, [])) used_assumptions)]
        end

      fun transform_steps (Node_Source {node, succs}) =
          transform_one_step node @ (map transform_steps succs |> flat)
        | transform_steps (Node_Conclusion {node, deps}) =
          ((map transform_steps deps) |> flat) @ (transform_one_step node)
    in
      transform_steps proof
    end


fun parse_proof local_name problem =
    strip_spaces_except_between_idents
    #> raw_explode
    #>
      (if local_name <> satallaxN then
        (Scan.error (!! (fn _ => raise UNRECOGNIZED_ATP_PROOF ())
          (Scan.finite Symbol.stopper (Scan.repeat1 (parse_line local_name problem) >> flat)))
           #> fst)
      else
        (Scan.error (!! (fn _ => raise UNRECOGNIZED_ATP_PROOF ())
          (Scan.finite Symbol.stopper (Scan.repeat1 (parse_tstp_thf0_satallax_line))))
          #> fst
          #> rev
          #> map to_satallax_step
          #> seperate_assumptions_and_steps
          #> create_satallax_proof_graph
          #> transform_to_standard_atp_step))


fun atp_proof_of_tstplike_proof _ _ "" = []
  | atp_proof_of_tstplike_proof local_prover problem tstp =
    (case core_of_agsyhol_proof tstp of
      SOME facts => facts |> map (core_inference agsyhol_core_rule)
    | NONE =>
      tstp ^ "$" (* the $ sign acts as a sentinel (FIXME: needed?) *)
      |> parse_proof local_prover problem
      |> local_prover = vampireN ? perhaps (try (sort (vampire_step_name_ord o pairself #1)))
      |> local_prover = zipperpositionN ? rev)


end;
