(*  Title:      HOL/ex/tptp_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2011

Export Isabelle theories as first-order TPTP inferences, exploiting
Sledgehammer's translation.
*)

signature TPTP_EXPORT =
sig
  val generate_tptp_graph_file_for_theory :
    Proof.context -> theory -> string -> unit
  val generate_tptp_inference_file_for_theory :
    Proof.context -> theory -> bool -> string -> unit
end;

structure TPTP_Export : TPTP_EXPORT =
struct

val ascii_of = Metis_Translate.ascii_of

val fact_name_of = prefix Sledgehammer_ATP_Translate.fact_prefix o ascii_of

fun facts_of thy =
  Sledgehammer_Filter.all_facts (ProofContext.init_global thy) Symtab.empty
                                true [] []

fun fold_body_thms f =
  let
    fun app n (PBody {thms, ...}) = thms |> fold (fn (i, (name, prop, body)) => fn (x, seen) =>
      if Inttab.defined seen i then (x, seen)
      else
        let
          val body' = Future.join body;
          val (x', seen') = app (n + (if name = "" then 0 else 1)) body' (x, Inttab.update (i, ()) seen);
        in (x' |> n = 1 ? f (name, prop, body'), seen') end);
  in fn bodies => fn x => #1 (fold (app 0) bodies (x, Inttab.empty)) end;

fun theorems_mentioned_in_proof_term thm =
  let
    fun collect (s, _, _) = if s <> "" then insert (op =) s else I
    val names =
      [] |> fold_body_thms collect [Thm.proof_body_of thm] |> map fact_name_of
  in names end

fun interesting_const_names ctxt =
  let val thy = ProofContext.theory_of ctxt in
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
          prefix Sledgehammer_ATP_Translate.fact_prefix (ascii_of name) ^ ": " ^
          commas (theorems_mentioned_in_proof_term thm) ^ "; " ^
          commas (map (prefix Metis_Translate.const_prefix o ascii_of)
                      (interesting_const_names ctxt (Thm.prop_of thm))) ^ " \n"
      in File.append path s end
    val thms = facts_of thy |> map (snd o snd)
    val _ = map do_thm thms
  in () end

fun inference_term [] = NONE
  | inference_term ss =
    ATP_Problem.ATerm ("inference",
           [ATP_Problem.ATerm ("isabelle", []),
            ATP_Problem.ATerm ("[]", []),
            ATP_Problem.ATerm ("[]",
                map (fn s => ATP_Problem.ATerm (s, [])) ss)])
    |> SOME
fun inference infers ident =
  these (AList.lookup (op =) infers ident) |> inference_term
fun add_inferences_to_problem_line infers
        (ATP_Problem.Formula (ident, ATP_Problem.Axiom, phi, NONE, NONE)) =
    ATP_Problem.Formula (ident, ATP_Problem.Lemma, phi, inference infers ident,
                         NONE)
  | add_inferences_to_problem_line _ line = line
val add_inferences_to_problem =
  map o apsnd o map o add_inferences_to_problem_line

fun generate_tptp_inference_file_for_theory ctxt thy full_types file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts0 = facts_of thy
    val facts =
      facts0 |> map_filter (try (fn ((_, loc), (_, th)) =>
                    Sledgehammer_ATP_Translate.translate_atp_fact ctxt true
                    ((Thm.get_name_hint th, loc), th)))
    val type_sys =
      Sledgehammer_ATP_Translate.Preds
          (Sledgehammer_ATP_Translate.Polymorphic,
           if full_types then Sledgehammer_ATP_Translate.All_Types
           else Sledgehammer_ATP_Translate.Const_Arg_Types,
           Sledgehammer_ATP_Translate.Deep)
    val explicit_apply = false
    val (atp_problem, _, _, _, _, _) =
      Sledgehammer_ATP_Translate.prepare_atp_problem ctxt ATP_Problem.Axiom
          ATP_Problem.Axiom type_sys explicit_apply [] @{prop False} facts
    val infers =
      facts0 |> map (fn (_, (_, th)) =>
                        (fact_name_of (Thm.get_name_hint th),
                         theorems_mentioned_in_proof_term th))
    val infers =
      infers |> map (apsnd (filter (member (op = o apsnd fst) infers)))
    val atp_problem = atp_problem |> add_inferences_to_problem infers
    val ss =
      ATP_Problem.tptp_strings_for_atp_problem ATP_Problem.Fof atp_problem
    val _ = app (File.append path) ss
  in () end

end;
