(*  Title:      HOL/ex/atp_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2011

Export Isabelle theories as first-order TPTP inferences, exploiting
Sledgehammer's translation.
*)

signature ATP_EXPORT =
sig
  val theorems_mentioned_in_proof_term :
    string list option -> thm -> string list
  val generate_tptp_graph_file_for_theory :
    Proof.context -> theory -> string -> unit
  val generate_tptp_inference_file_for_theory :
    Proof.context -> theory -> string -> string -> unit
end;

structure ATP_Export : ATP_EXPORT =
struct

open ATP_Problem
open ATP_Translate

val fact_name_of = prefix fact_prefix o ascii_of

fun facts_of thy =
  Sledgehammer_Filter.all_facts (Proof_Context.init_global thy) Symtab.empty
                                true [] []

(* FIXME: Similar yet different code in "mirabelle.ML". The code here has a few
   fixes that seem to be missing over there; or maybe the two code portions are
   not doing the same? *)
fun fold_body_thms thm_name all_names f =
  let
    fun app n (PBody {thms, ...}) =
      thms |> fold (fn (_, (name, prop, body)) => fn x =>
        let
          val body' = Future.join body
          val n' =
            n + (if name = "" orelse
                    (is_some all_names andalso
                     not (member (op =) (the all_names) name)) orelse
                    (* uncommon case where the proved theorem occurs twice
                       (e.g., "Transitive_Closure.trancl_into_trancl") *)
                    n = 1 andalso name = thm_name then
                   0
                 else
                   1)
          val x' = x |> n' <= 1 ? app n' body'
        in (x' |> n = 1 ? f (name, prop, body')) end)
  in fold (app 0) end

fun theorems_mentioned_in_proof_term all_names thm =
  let
    fun collect (s, _, _) = if s <> "" then insert (op =) s else I
    val names =
      [] |> fold_body_thms (Thm.get_name_hint thm) all_names collect
                           [Thm.proof_body_of thm]
         |> map fact_name_of
  in names end

fun interesting_const_names ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    Sledgehammer_Filter.const_names_in_fact thy
        (Sledgehammer_Provers.is_built_in_const_for_prover ctxt ATP_Systems.eN)
  end

fun generate_tptp_graph_file_for_theory ctxt thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val axioms = Theory.all_axioms_of thy |> map fst
    fun do_thm thm =
      let
        val name = Thm.get_name_hint thm
        val s =
          "[" ^ Thm.legacy_get_kind thm ^ "] " ^
          (if member (op =) axioms name then "A" else "T") ^ " " ^
          prefix fact_prefix (ascii_of name) ^ ": " ^
          commas (theorems_mentioned_in_proof_term NONE thm) ^ "; " ^
          commas (map (prefix const_prefix o ascii_of)
                      (interesting_const_names ctxt (Thm.prop_of thm))) ^ " \n"
      in File.append path s end
    val thms = facts_of thy |> map snd
    val _ = map do_thm thms
  in () end

fun inference_term [] = NONE
  | inference_term ss =
    ATerm ("inference",
           [ATerm ("isabelle", []),
            ATerm (tptp_empty_list, []),
            ATerm (tptp_empty_list, map (fn s => ATerm (s, [])) ss)])
    |> SOME
fun inference infers ident =
  these (AList.lookup (op =) infers ident) |> inference_term
fun add_inferences_to_problem_line infers
                                   (Formula (ident, Axiom, phi, NONE, NONE)) =
    Formula (ident, Lemma, phi, inference infers ident, NONE)
  | add_inferences_to_problem_line _ line = line
val add_inferences_to_problem =
  map o apsnd o map o add_inferences_to_problem_line

fun ident_of_problem_line (Decl (ident, _, _)) = ident
  | ident_of_problem_line (Formula (ident, _, _, _, _)) = ident

fun generate_tptp_inference_file_for_theory ctxt thy type_sys file_name =
  let
    val format = FOF
    val type_sys = type_sys |> type_sys_from_string
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts0 = facts_of thy
    val facts =
      facts0 |> map (fn ((_, loc), th) =>
                        ((Thm.get_name_hint th, loc), prop_of th))
    val (atp_problem, _, _, _, _, _, _) =
      prepare_atp_problem ctxt format Axiom Axiom type_sys true false true []
                          @{prop False} facts
    val all_names = facts0 |> map (Thm.get_name_hint o snd)
    val infers =
      facts0 |> map (fn (_, th) =>
                        (fact_name_of (Thm.get_name_hint th),
                         theorems_mentioned_in_proof_term (SOME all_names) th))
    val all_atp_problem_names =
      atp_problem |> maps (map ident_of_problem_line o snd)
    val infers =
      infers |> map (apsnd (filter (member (op =) all_atp_problem_names)))
    val atp_problem = atp_problem |> add_inferences_to_problem infers
    val ss = tptp_lines_for_atp_problem FOF atp_problem
    val _ = app (File.append path) ss
  in () end

end;
