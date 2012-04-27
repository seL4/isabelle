(*  Title:      Pure/ML/ml_thms.ML
    Author:     Makarius

Attribute source and theorem values within ML.
*)

signature ML_THMS =
sig
  val the_attributes: Proof.context -> int -> Args.src list
  val the_thms: Proof.context -> int -> thm list
  val the_thm: Proof.context -> int -> thm
end;

structure ML_Thms: ML_THMS =
struct

(* auxiliary data *)

structure Data = Proof_Data
(
  type T = Args.src list Inttab.table * thm list Inttab.table;
  fun init _ = (Inttab.empty, Inttab.empty);
);

val put_attributes = Data.map o apfst o Inttab.update;
fun the_attributes ctxt name = the (Inttab.lookup (fst (Data.get ctxt)) name);

val put_thms = Data.map o apsnd o Inttab.update;

fun the_thms ctxt name = the (Inttab.lookup (snd (Data.get ctxt)) name);
fun the_thm ctxt name = the_single (the_thms ctxt name);


(* attribute source *)

val _ =
  Context.>> (Context.map_theory
    (ML_Context.add_antiq (Binding.name "attributes")
      (fn _ => Scan.lift Parse_Spec.attribs >> (fn raw_srcs => fn background =>
        let
          val thy = Proof_Context.theory_of background;

          val i = serial ();
          val srcs = map (Attrib.intern_src thy) raw_srcs;
          val _ = map (Attrib.attribute background) srcs;
          val (a, background') = background
            |> ML_Antiquote.variant "attributes" ||> put_attributes (i, srcs);
          val ml =
            ("val " ^ a ^ " = ML_Thms.the_attributes (ML_Context.the_local_context ()) " ^
              string_of_int i ^ ";\n", "Isabelle." ^ a);
        in (K ml, background') end))));


(* fact references *)

fun thm_bind kind a i =
  "val " ^ a ^ " = ML_Thms.the_" ^ kind ^
    " (ML_Context.the_local_context ()) " ^ string_of_int i ^ ";\n";

fun thm_antiq kind scan = ML_Context.add_antiq (Binding.name kind)
  (fn _ => scan >> (fn ths => fn background =>
    let
      val i = serial ();
      val (a, background') = background
        |> ML_Antiquote.variant kind ||> put_thms (i, ths);
      val ml = (thm_bind kind a i, "Isabelle." ^ a);
    in (K ml, background') end));

val _ =
  Context.>> (Context.map_theory
   (thm_antiq "thm" (Attrib.thm >> single) #>
    thm_antiq "thms" Attrib.thms));


(* ad-hoc goals *)

val and_ = Args.$$$ "and";
val by = Args.$$$ "by";
val goal = Scan.unless (by || and_) Args.name_source;

val _ =
  Context.>> (Context.map_theory
   (ML_Context.add_antiq (Binding.name "lemma")
    (fn _ => Args.context -- Args.mode "open" --
        Scan.lift (Parse.and_list1 (Scan.repeat1 goal) --
          (by |-- Method.parse -- Scan.option Method.parse)) >>
      (fn ((ctxt, is_open), (raw_propss, methods)) => fn background =>
        let
          val propss = burrow (map (rpair []) o Syntax.read_props ctxt) raw_propss;
          val i = serial ();
          val prep_result = Goal.norm_result #> not is_open ? Thm.close_derivation;
          fun after_qed res goal_ctxt =
            put_thms (i, map prep_result (Proof_Context.export goal_ctxt ctxt (flat res))) goal_ctxt;
          val ctxt' = ctxt
            |> Proof.theorem NONE after_qed propss
            |> Proof.global_terminal_proof methods;
          val (a, background') = background
            |> ML_Antiquote.variant "lemma" ||> put_thms (i, the_thms ctxt' i);
          val ml =
            (thm_bind (if length (flat propss) = 1 then "thm" else "thms") a i, "Isabelle." ^ a);
        in (K ml, background') end))));

end;

