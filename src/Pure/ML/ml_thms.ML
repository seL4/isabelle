(*  Title:      Pure/ML/ml_thms.ML
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

structure AuxFacts = Proof_Data
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
  (fn _ => scan >> (fn ths => fn {struct_name, background} =>
    let
      val i = serial ();
      val (a, background') = background
        |> ML_Antiquote.variant kind ||> put_thms (i, ths);
      val ml = (thm_bind kind a i, struct_name ^ "." ^ a);
    in (K ml, background') end));

val _ = thm_antiq "thm" (Attrib.thm >> single);
val _ = thm_antiq "thms" Attrib.thms;


(* ad-hoc goals *)

val and_ = Args.$$$ "and";
val by = Args.$$$ "by";
val goal = Scan.unless (by || and_) Args.name;

val _ = ML_Context.add_antiq "lemma"
  (fn pos => Args.context -- Args.mode "open" --
      Scan.lift (OuterParse.and_list1 (Scan.repeat1 goal) --
        (by |-- Method.parse -- Scan.option Method.parse)) >>
    (fn ((ctxt, is_open), (raw_propss, methods)) => fn {struct_name, background} =>
      let
        val propss = burrow (map (rpair []) o Syntax.read_props ctxt) raw_propss;
        val i = serial ();
        val prep_result =
          Goal.norm_result #> Thm.default_position pos #> not is_open ? Thm.close_derivation;
        fun after_qed res goal_ctxt =
          put_thms (i, map prep_result (ProofContext.export goal_ctxt ctxt (flat res))) goal_ctxt;
        val ctxt' = ctxt
          |> Proof.theorem_i NONE after_qed propss
          |> Proof.global_terminal_proof methods;
        val (a, background') = background
          |> ML_Antiquote.variant "lemma" ||> put_thms (i, the_thms ctxt' i);
        val ml =
         (thm_bind (if length (flat propss) = 1 then "thm" else "thms") a i,
          struct_name ^ "." ^ a);
      in (K ml, background') end));

end;

