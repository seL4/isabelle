(*  Title:      HOL/TPTP/atp_theory_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2011

Export Isabelle theories as first-order TPTP inferences.
*)

signature ATP_THEORY_EXPORT =
sig
  type atp_format = ATP_Problem.atp_format

  datatype inference_policy =
    No_Inferences | Unchecked_Inferences | Checked_Inferences

  val generate_atp_inference_file_for_theory : Proof.context -> theory -> atp_format ->
    inference_policy -> string -> string -> unit
  val generate_casc_lbt_isa_files_for_theory : Proof.context -> theory -> atp_format ->
    inference_policy -> string -> string -> unit
end;

structure ATP_Theory_Export : ATP_THEORY_EXPORT =
struct

open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open Sledgehammer_ATP_Systems

val max_dependencies = 100
val max_facts = 512
val atp_timeout = seconds 0.5

datatype inference_policy =
  No_Inferences | Unchecked_Inferences | Checked_Inferences

val prefix = Library.prefix
val fact_name_of = prefix fact_prefix o ascii_of

fun atp_of_format (THF (_, Polymorphic, _)) = leo3N
  | atp_of_format (THF (_, Monomorphic, _)) = satallaxN
  | atp_of_format (DFG Polymorphic) = pirateN
  | atp_of_format (DFG Monomorphic) = spassN
  | atp_of_format (TFF (_, Polymorphic)) = alt_ergoN
  | atp_of_format (TFF (_, Monomorphic)) = vampireN
  | atp_of_format FOF = eN (* FIXME? *)
  | atp_of_format CNF_UEQ = waldmeisterN
  | atp_of_format CNF = eN (* FIXME? *)

fun run_atp ctxt format problem =
  let
    val thy = Proof_Context.theory_of ctxt
    val prob_file = File.tmp_path (Path.explode "prob")
    val atp = atp_of_format format
    val {exec, arguments, proof_delims, known_failures, ...} = get_atp thy atp ()
    val ord = effective_term_order ctxt atp
    val _ = problem
      |> lines_of_atp_problem format ord (K [])
      |> File.write_list prob_file
    val exec = exec false
    val path = getenv (List.last (fst exec)) ^ "/" ^ List.last (snd exec)
    val command =
      File.bash_path (Path.explode path) ^ " " ^
      arguments ctxt false "" atp_timeout (File.bash_path prob_file)
                (ord, K [], K [])
    val outcome =
      Timeout.apply atp_timeout Isabelle_System.bash_output command
      |> fst
      |> extract_tstplike_proof_and_outcome false proof_delims known_failures
      |> snd
      handle Timeout.TIMEOUT _ => SOME TimedOut
    val _ =
      tracing ("Ran ATP: " ^
               (case outcome of
                  NONE => "Success"
                | SOME failure => string_of_atp_failure failure))
  in outcome end

fun is_problem_line_reprovable ctxt format prelude axioms deps (Formula (ident', _, phi, _, _)) =
    is_none (run_atp ctxt format
      ((factsN,
        Formula (ident', Conjecture, phi, NONE, []) :: map_filter (Symtab.lookup axioms) deps) ::
       prelude))
  | is_problem_line_reprovable _ _ _ _ _ _ = false

fun inference_term _ [] = NONE
  | inference_term check_infs ss =
    ATerm (("inference", []),
        [ATerm (("checked_isabelle" |> not check_infs ? prefix "un", []), []),
         ATerm ((tptp_empty_list, []), []),
         ATerm ((tptp_empty_list, []),
         map (fn s => ATerm ((s, []), [])) ss)])
    |> SOME

fun add_inferences_to_problem_line ctxt format check_infs prelude axioms infers
      (line as Formula ((ident, alt), Axiom, phi, NONE, info)) =
    let
      val deps =
        case these (AList.lookup (op =) infers ident) of
          [] => []
        | deps =>
          if check_infs andalso
             not (is_problem_line_reprovable ctxt format prelude axioms deps
                                             line) then
            []
          else
            deps
    in
      Formula ((ident, alt), Lemma, phi, inference_term check_infs deps, info)
    end
  | add_inferences_to_problem_line _ _ _ _ _ _ line = line

fun add_inferences_to_problem ctxt format check_infs prelude infers problem =
  let
    fun add_if_axiom (axiom as Formula ((ident, _), Axiom, _, _, _)) = Symtab.default (ident, axiom)
      | add_if_axiom _ = I

    val add_axioms_of_problem = fold (fold add_if_axiom o snd)
    val axioms = Symtab.empty |> check_infs ? add_axioms_of_problem problem
  in
    map (apsnd (map (add_inferences_to_problem_line ctxt format check_infs prelude axioms infers)))
      problem
  end

fun ident_of_problem_line (Class_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Type_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Sym_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Class_Memb (ident, _, _, _)) = ident
  | ident_of_problem_line (Formula ((ident, _), _, _, _, _)) = ident

fun order_facts ord = sort (ord o apply2 ident_of_problem_line)

fun order_problem_facts _ [] = []
  | order_problem_facts ord ((heading, lines) :: problem) =
    if heading = factsN then (heading, order_facts ord lines) :: problem
    else (heading, lines) :: order_problem_facts ord problem

(* A fairly random selection of types used for monomorphizing. *)
val ground_types =
  [\<^typ>\<open>nat\<close>, HOLogic.intT, HOLogic.realT, \<^typ>\<open>nat => bool\<close>, \<^typ>\<open>bool\<close>,
   \<^typ>\<open>unit\<close>]

fun ground_type_of_tvar _ [] tvar = raise TYPE ("ground_type_of_tvar", [TVar tvar], [])
  | ground_type_of_tvar thy (T :: Ts) tvar =
    if can (Sign.typ_match thy (TVar tvar, T)) Vartab.empty then T
    else ground_type_of_tvar thy Ts tvar

fun monomorphize_term ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    t |> map_types (map_type_tvar (ground_type_of_tvar thy ground_types))
    handle TYPE _ => \<^prop>\<open>True\<close>
  end

fun heading_sort_key heading =
  if String.isPrefix factsN heading then "_" ^ heading else heading

fun problem_of_theory ctxt thy format infer_policy type_enc =
  let
    val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val type_enc =
      type_enc |> type_enc_of_string Non_Strict
               |> adjust_type_enc format
    val mono = not (is_type_enc_polymorphic type_enc)

    val facts =
      Sledgehammer_Fact.all_facts (Proof_Context.init_global thy) true false
                                  Keyword.empty_keywords [] [] css_table
      |> sort (Sledgehammer_MaSh.crude_thm_ord ctxt o apply2 snd)
    val problem =
      facts
      |> map (fn ((_, loc), th) =>
        ((Thm.get_name_hint th, loc), th |> Thm.prop_of |> mono ? monomorphize_term ctxt))
      |> generate_atp_problem ctxt true format Axiom type_enc Exporter combsN false false true []
        \<^prop>\<open>False\<close>
      |> #1 |> sort_by (heading_sort_key o fst)
    val prelude = fst (split_last problem)
    val name_tabs = Sledgehammer_Fact.build_name_tables Thm.get_name_hint facts
    val infers =
      if infer_policy = No_Inferences then
        []
      else
        facts
        |> map (fn (_, th) =>
                   (fact_name_of (Thm.get_name_hint th),
                    th |> Sledgehammer_Util.thms_in_proof max_dependencies (SOME name_tabs)
                       |> these |> map fact_name_of))
    val all_problem_names =
      problem |> maps (map ident_of_problem_line o snd) |> distinct (op =)
    val all_problem_name_set = Symtab.make (map (rpair ()) all_problem_names)
    val infers =
      infers |> filter (Symtab.defined all_problem_name_set o fst)
             |> map (apsnd (filter (Symtab.defined all_problem_name_set)))
    val maybe_add_edge = perhaps o try o String_Graph.add_edge_acyclic
    val ordered_names =
      String_Graph.empty
      |> fold (String_Graph.new_node o rpair ()) all_problem_names
      |> fold (fn (to, froms) => fold (fn from => maybe_add_edge (from, to)) froms) infers
      |> fold (fn (to, from) => maybe_add_edge (from, to))
        (tl all_problem_names ~~ fst (split_last all_problem_names))
      |> String_Graph.topological_order
    val order_tab =
      Symtab.empty
      |> fold (Symtab.insert (op =)) (ordered_names ~~ (1 upto length ordered_names))
    val name_ord = int_ord o apply2 (the o Symtab.lookup order_tab)
  in
    (facts,
     problem
     |> (case format of
          DFG _ => I
        | _ => add_inferences_to_problem ctxt format (infer_policy = Checked_Inferences) prelude
          infers)
     |> order_problem_facts name_ord)
  end

fun lines_of_problem ctxt format =
  lines_of_atp_problem format (effective_term_order ctxt eN (* dummy *)) (K [])

fun write_lines path ss =
  let
    val _ = File.write path ""
    val _ = app (File.append path) ss
  in () end

fun generate_atp_inference_file_for_theory ctxt thy format infer_policy type_enc file_name =
  let
    val (_, problem) = problem_of_theory ctxt thy format infer_policy type_enc
    val ss = lines_of_problem ctxt format problem
  in write_lines (Path.explode file_name) ss end

fun ap dir = Path.append dir o Path.explode

fun chop_maximal_groups eq xs =
  let
    val rev_xs = rev xs
    fun chop_group _ [] = []
      | chop_group n (xs as x :: _) =
        let
          val n' = find_index (curry eq x) rev_xs
          val (ws', xs') = chop (n - n') xs
        in ws' :: chop_group n' xs' end
   in chop_group (length xs) xs end

fun theory_name_of_fact (Formula ((_, alt), _, _, _, _)) =
    (case first_field Long_Name.separator alt of
       NONE => alt
     | SOME (thy, _) => thy)
  | theory_name_of_fact _ = ""

val problem_suffix = ".p"
val suggestion_suffix = ".sugg"
val include_suffix = ".ax"

val file_order_name = "FilesInProcessingOrder"
val problem_order_name = "ProblemsInProcessingOrder"
val problem_name = "problems"
val suggestion_name = "suggestions"
val include_name = "incl"
val prelude_base_name = "prelude"
val prelude_name = prelude_base_name ^ include_suffix

val encode_meta = Sledgehammer_MaSh.encode_str

fun include_base_name_of_fact x = encode_meta (theory_name_of_fact x)

fun include_line base_name =
  "include('" ^ include_name ^ "/" ^ base_name ^ include_suffix ^ "').\n"

val hol_base_name = encode_meta "HOL"

fun should_generate_problem thy base_name (Formula ((_, alt), _, _, _, _)) =
  (case try (Global_Theory.get_thm thy) alt of
    SOME th =>
    (* This is a crude hack to detect theorems stated and proved by the user (as opposed to those
       derived by various packages). In addition, we leave out everything in "HOL" as too basic to
       be interesting. *)
    Thm.legacy_get_kind th <> "" andalso base_name <> hol_base_name
  | NONE => false)

(* Convention: theoryname__goalname *)
fun problem_name_of base_name n alt =
  base_name ^ "__" ^ string_of_int n ^ "_" ^
  perhaps (try (unprefix (base_name ^ "_"))) alt ^ problem_suffix

fun suggestion_name_of base_name n alt =
  base_name ^ "__" ^ string_of_int n ^ "_" ^
  perhaps (try (unprefix (base_name ^ "_"))) alt ^ suggestion_suffix

fun generate_casc_lbt_isa_files_for_theory ctxt thy format infer_policy type_enc dir_name =
  let
    val dir = Path.explode dir_name
    val _ = Isabelle_System.mkdir dir
    val file_order_path = ap dir file_order_name
    val _ = File.write file_order_path ""
    val problem_order_path = ap dir problem_order_name
    val _ = File.write problem_order_path ""
    val problem_dir = ap dir problem_name
    val _ = Isabelle_System.mkdir problem_dir
    val suggestion_dir = ap dir suggestion_name
    val _ = Isabelle_System.mkdir suggestion_dir
    val include_dir = ap problem_dir include_name
    val _ = Isabelle_System.mkdir include_dir

    val (facts, (prelude, groups)) =
      problem_of_theory ctxt thy format infer_policy type_enc
      ||> split_last
      ||> apsnd (snd
           #> chop_maximal_groups (op = o apply2 theory_name_of_fact)
           #> map (`(include_base_name_of_fact o hd)))

    val fact_tab = Symtab.make (map (fn fact as (_, th) => (Thm.get_name_hint th, fact)) facts)

    fun write_prelude () =
      let val ss = lines_of_problem ctxt format prelude in
        File.append file_order_path (prelude_base_name ^ "\n");
        write_lines (ap include_dir prelude_name) ss
      end

    fun write_include_file (base_name, fact_lines) =
      let
        val name = base_name ^ include_suffix
        val ss = lines_of_problem ctxt format [(factsN, fact_lines)]
      in
        File.append file_order_path (base_name ^ "\n");
        write_lines (ap include_dir name) ss
      end

    fun select_facts_for_fact facts fact =
      let
        val (hyp_ts, conj_t) = Logic.strip_horn (Thm.prop_of (snd fact))
        val mepo = Sledgehammer_MePo.mepo_suggested_facts ctxt
          (Sledgehammer_Commands.default_params thy []) max_facts NONE hyp_ts conj_t facts
      in
        map (suffix "\n" o fact_name_of o Thm.get_name_hint o snd) mepo
      end

    fun write_problem_files _ _ _ _ [] = ()
      | write_problem_files _ seen_facts includes [] groups =
        write_problem_files 1 seen_facts includes includes groups
      | write_problem_files n seen_facts includes _ ((base_name, []) :: groups) =
        write_problem_files n seen_facts (includes @ [include_line base_name]) [] groups
      | write_problem_files n seen_facts includes seen_ss
          ((base_name, fact_line :: fact_lines) :: groups) =
        let
          val (alt, pname, sname, conj) =
            (case fact_line of
              Formula ((ident, alt), _, phi, _, _) =>
              (alt, problem_name_of base_name n (encode_meta alt),
               suggestion_name_of base_name n (encode_meta alt),
               Formula ((ident, alt), Conjecture, phi, NONE, [])))
          val fact = the (Symtab.lookup fact_tab alt)
          val fact_s = tptp_string_of_line format fact_line
        in
          (if should_generate_problem thy base_name fact_line then
             let
               val conj_s = tptp_string_of_line format conj
             in
               File.append problem_order_path (pname ^ "\n");
               write_lines (ap problem_dir pname) (seen_ss @ [conj_s]);
               write_lines (ap suggestion_dir sname) (select_facts_for_fact facts fact)
             end
           else
             ();
           write_problem_files (n + 1) (fact :: seen_facts) includes (seen_ss @ [fact_s])
             ((base_name, fact_lines) :: groups))
        end

    val _ = write_prelude ()
    val _ = app write_include_file groups
    val _ = write_problem_files 1 [] [include_line prelude_base_name] [] groups
  in () end

end;
