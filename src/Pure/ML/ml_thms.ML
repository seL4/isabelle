(*  Title:      Pure/ML/ml_thms.ML
    ID:         $Id$
    Author:     Makarius

Isar theorem values within ML.
*)

signature ML_THMS =
sig
  val the_thms: Proof.context -> int -> thm list
  val the_thm: Proof.context -> int -> thm
end;

structure ML_Thms: ML_THMS =
struct

(* auxiliary facts table *)

structure AuxFacts = ProofDataFun
(
  type T = thm list Inttab.table;
  fun init _ = Inttab.empty;
);

val put_thms = AuxFacts.map o Inttab.update;

fun the_thms ctxt name = the (Inttab.lookup (AuxFacts.get ctxt) name);
fun the_thm ctxt name = the_single (the_thms ctxt name);

fun thm_bind kind a i =
  "val " ^ a ^ " = ML_Thms.the_" ^ kind ^
    " (ML_Context.the_local_context ()) " ^ string_of_int i ^ ";\n";


(* fact references *)

fun thm_antiq kind scan = ML_Context.add_antiq kind
  (scan >> (fn ths => fn {struct_name, background} =>
    let
      val i = serial ();
      val (a, background') = background
        |> ML_Antiquote.variant kind ||> put_thms (i, ths);
      val ml = (thm_bind kind a i, struct_name ^ "." ^ a);
    in (K ml, background') end));

val _ = thm_antiq "thm" (Attrib.thm >> single);
val _ = thm_antiq "thms" Attrib.thms;


(* ad-hoc goals *)

fun by x = Scan.lift (Args.$$$ "by") x;
val goal = Scan.unless by Args.prop;

val _ = ML_Context.add_antiq "lemma"
  ((Args.context -- Scan.repeat1 goal -- (by |-- Scan.lift Method.parse_args)) >>
    (fn ((ctxt, props), method_text) => fn {struct_name, background} =>
      let
        val i = serial ();
        fun after_qed [res] goal_ctxt =
          put_thms (i, map Goal.norm_result (ProofContext.export goal_ctxt ctxt res)) goal_ctxt;
        val ctxt' = ctxt
          |> Proof.theorem_i NONE after_qed [map (rpair []) props]
          |> Proof.global_terminal_proof (method_text, NONE);
        val (a, background') = background
          |> ML_Antiquote.variant "lemma" ||> put_thms (i, the_thms ctxt' i);
        val ml = (thm_bind (if length props = 1 then "thm" else "thms") a i, struct_name ^ "." ^ a);
      in (K ml, background') end));

end;

