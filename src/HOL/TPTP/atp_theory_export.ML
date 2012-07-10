(*  Title:      HOL/TPTP/atp_theory_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2011

Export Isabelle theories as first-order TPTP inferences.
*)

signature ATP_THEORY_EXPORT =
sig
  type atp_format = ATP_Problem.atp_format
  type stature = Sledgehammer_Filter.stature

  val theorems_mentioned_in_proof_term :
    string list option -> thm -> string list
  val all_facts_of_theory : theory -> (((unit -> string) * stature) * thm) list
  val generate_atp_inference_file_for_theory :
    Proof.context -> theory -> atp_format -> string -> string -> unit
end;

structure ATP_Theory_Export : ATP_THEORY_EXPORT =
struct

open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open ATP_Systems

val fact_name_of = prefix fact_prefix o ascii_of

(* FIXME: Similar yet different code in "mirabelle.ML". The code here has a few
   fixes that seem to be missing over there; or maybe the two code portions are
   not doing the same? *)
fun fold_body_thms thm_name f =
  let
    fun app n (PBody {thms, ...}) =
      thms |> fold (fn (_, (name, prop, body)) => fn x =>
        let
          val body' = Future.join body
          val n' =
            n + (if name = "" orelse
                    (* uncommon case where the proved theorem occurs twice
                       (e.g., "Transitive_Closure.trancl_into_trancl") *)
                    (n = 1 andalso name = thm_name) then
                   0
                 else
                   1)
          val x' = x |> n' <= 1 ? app n' body'
        in (x' |> n = 1 ? f (name, prop, body')) end)
  in fold (app 0) end

fun theorems_mentioned_in_proof_term all_names th =
  let
    val is_name_ok =
      case all_names of
        SOME names => member (op =) names
      | NONE => (fn s => s <> "" andalso not (String.isPrefix "Pure." s))
    fun collect (s, _, _) = is_name_ok s ? insert (op =) s
    val names =
      [] |> fold_body_thms (Thm.get_name_hint th) collect [Thm.proof_body_of th]
  in names end

fun all_facts_of_theory thy =
  let val ctxt = Proof_Context.init_global thy in
    Sledgehammer_Filter.all_facts ctxt false Symtab.empty true [] []
        (Sledgehammer_Filter.clasimpset_rule_table_of ctxt)
    |> rev (* try to restore the original order of facts, for MaSh *)
  end

fun inference_term [] = NONE
  | inference_term ss =
    ATerm (("inference", []),
           [ATerm (("isabelle", []), []),
            ATerm ((tptp_empty_list, []), []),
            ATerm ((tptp_empty_list, []),
            map (fn s => ATerm ((s, []), [])) ss)])
    |> SOME
fun inference infers ident =
  these (AList.lookup (op =) infers ident) |> inference_term
fun add_inferences_to_problem_line infers
                                   (Formula (ident, Axiom, phi, NONE, tms)) =
    Formula (ident, Lemma, phi, inference infers ident, tms)
  | add_inferences_to_problem_line _ line = line
fun add_inferences_to_problem infers =
  map (apsnd (map (add_inferences_to_problem_line infers)))

fun ident_of_problem_line (Class_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Type_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Sym_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Class_Memb (ident, _, _, _)) = ident
  | ident_of_problem_line (Formula (ident, _, _, _, _)) = ident

fun run_some_atp ctxt format problem =
  let
    val thy = Proof_Context.theory_of ctxt
    val prob_file = File.tmp_path (Path.explode "prob")
    val atp = case format of DFG _ => spassN | _ => eN
    val {exec, arguments, proof_delims, known_failures, ...} =
      get_atp thy atp ()
    val ord = effective_term_order ctxt atp
    val _ = problem |> lines_for_atp_problem format ord (K [])
                    |> File.write_list prob_file
    val path = getenv (List.last (fst exec)) ^ "/" ^ snd exec
    val command =
      File.shell_path (Path.explode path) ^
      " " ^ arguments ctxt false "" (seconds 1.0) (ord, K [], K []) ^ " " ^
      File.shell_path prob_file
  in
    TimeLimit.timeLimit (seconds 0.3) Isabelle_System.bash_output command
    |> fst
    |> extract_tstplike_proof_and_outcome false true proof_delims known_failures
    |> snd
  end
  handle TimeLimit.TimeOut => SOME TimedOut

val tautology_prefixes =
  [@{theory HOL}, @{theory Meson}, @{theory ATP}, @{theory Metis}]
  |> map (fact_name_of o Context.theory_name)

fun is_problem_line_tautology ctxt format (Formula (ident, _, phi, _, _)) =
    exists (fn prefix => String.isPrefix prefix ident)
           tautology_prefixes andalso
    is_none (run_some_atp ctxt format
                 [(factsN, [Formula (ident, Conjecture, phi, NONE, [])])])
  | is_problem_line_tautology _ _ _ = false

fun order_facts ord = sort (ord o pairself ident_of_problem_line)
fun order_problem_facts _ [] = []
  | order_problem_facts ord ((heading, lines) :: problem) =
    if heading = factsN then (heading, order_facts ord lines) :: problem
    else (heading, lines) :: order_problem_facts ord problem

(* A fairly random selection of types used for monomorphizing. *)
val ground_types =
  [@{typ nat}, HOLogic.intT, HOLogic.realT, @{typ "nat => bool"}, @{typ bool},
   @{typ unit}]

fun ground_type_for_tvar _ [] tvar =
    raise TYPE ("ground_type_for_sorts", [TVar tvar], [])
  | ground_type_for_tvar thy (T :: Ts) tvar =
    if can (Sign.typ_match thy (TVar tvar, T)) Vartab.empty then T
    else ground_type_for_tvar thy Ts tvar

fun monomorphize_term ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    t |> map_types (map_type_tvar (ground_type_for_tvar thy ground_types))
    handle TYPE _ => @{prop True}
  end

fun generate_atp_inference_file_for_theory ctxt thy format type_enc file_name =
  let
    val type_enc = type_enc |> type_enc_from_string Strict
                            |> adjust_type_enc format
    val mono = not (is_type_enc_polymorphic type_enc)
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = all_facts_of_theory thy
    val atp_problem =
      facts
      |> map (fn ((_, loc), th) =>
                 ((Thm.get_name_hint th, loc),
                   th |> prop_of |> mono ? monomorphize_term ctxt))
      |> prepare_atp_problem ctxt format Axiom type_enc Exporter combsN false
                             false true [] @{prop False}
      |> #1
    val atp_problem =
      atp_problem
      |> map (apsnd (filter_out (is_problem_line_tautology ctxt format)))
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    val infers =
      facts |> map (fn (_, th) =>
                       (fact_name_of (Thm.get_name_hint th),
                        th |> theorems_mentioned_in_proof_term (SOME all_names)
                           |> map fact_name_of))
    val all_atp_problem_names =
      atp_problem |> maps (map ident_of_problem_line o snd)
    val infers =
      infers |> filter (member (op =) all_atp_problem_names o fst)
             |> map (apsnd (filter (member (op =) all_atp_problem_names)))
    val ordered_names =
      String_Graph.empty
      |> fold (String_Graph.new_node o rpair ()) all_atp_problem_names
      |> fold (fn (to, froms) =>
                  fold (fn from => String_Graph.add_edge (from, to)) froms)
              infers
      |> String_Graph.topological_order
    val order_tab =
      Symtab.empty
      |> fold (Symtab.insert (op =))
              (ordered_names ~~ (1 upto length ordered_names))
    val name_ord = int_ord o pairself (the o Symtab.lookup order_tab)
    val atp_problem =
      atp_problem
      |> (case format of DFG _ => I | _ => add_inferences_to_problem infers)
      |> order_problem_facts name_ord
    val ord = effective_term_order ctxt eN (* dummy *)
    val ss = lines_for_atp_problem format ord (K []) atp_problem
    val _ = app (File.append path) ss
  in () end

end;
