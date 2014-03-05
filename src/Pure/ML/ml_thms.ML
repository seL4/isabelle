(*  Title:      Pure/ML/ml_thms.ML
    Author:     Makarius

Attribute source and theorem values within ML.
*)

signature ML_THMS =
sig
  val the_attributes: Proof.context -> int -> Args.src list
  val the_thmss: Proof.context -> thm list list
end;

structure ML_Thms: ML_THMS =
struct

(* auxiliary data *)

type thms = (string * bool) * thm list;  (*name, single, value*)

structure Data = Proof_Data
(
  type T = Args.src list Inttab.table * thms list;
  fun init _ = (Inttab.empty, []);
);

val put_attributes = Data.map o apfst o Inttab.update;
fun the_attributes ctxt name = the (Inttab.lookup (fst (Data.get ctxt)) name);

val get_thmss = snd o Data.get;
val the_thmss = map snd o get_thmss;
val cons_thms = Data.map o apsnd o cons;



(* attribute source *)

val _ = Theory.setup
  (ML_Context.add_antiq @{binding attributes}
    (Scan.depend (fn context => Parse_Spec.attribs >> (fn raw_srcs =>
      let
        val ctxt = Context.the_proof context;
        val thy = Proof_Context.theory_of ctxt;

        val i = serial ();
        val srcs = map (Attrib.intern_src thy) raw_srcs;
        val _ = map (Attrib.attribute ctxt) srcs;
        val (a, ctxt') = ctxt
          |> ML_Antiquote.variant "attributes" ||> put_attributes (i, srcs);
        val ml =
          ("val " ^ a ^ " = ML_Thms.the_attributes ML_context " ^
            string_of_int i ^ ";\n", "Isabelle." ^ a);
      in (Context.Proof ctxt', K ml) end))));


(* fact references *)

fun thm_binding kind is_single context thms =
  let
    val ctxt = Context.the_proof context;

    val initial = null (get_thmss ctxt);
    val (name, ctxt') = ML_Antiquote.variant kind ctxt;
    val ctxt'' = cons_thms ((name, is_single), thms) ctxt';

    val ml_body = "Isabelle." ^ name;
    fun decl final_ctxt =
      if initial then
        let
          val binds = get_thmss final_ctxt |> map (fn ((a, b), _) => (b ? enclose "[" "]") a);
          val ml_env = "val [" ^ commas binds ^ "] = ML_Thms.the_thmss ML_context;\n";
        in (ml_env, ml_body) end
      else ("", ml_body);
  in (Context.Proof ctxt'', decl) end;

val _ = Theory.setup
  (ML_Context.add_antiq @{binding thm}
    (Scan.depend (fn context =>
      Scan.pass context Attrib.thm >> (thm_binding "thm" true context o single))) #>
   ML_Context.add_antiq @{binding thms}
    (Scan.depend (fn context =>
      Scan.pass context Attrib.thms >> thm_binding "thms" false context)));


(* ad-hoc goals *)

val and_ = Args.$$$ "and";
val by = Args.$$$ "by";
val goal = Scan.unless (by || and_) Args.name_inner_syntax;

val _ = Theory.setup
  (ML_Context.add_antiq @{binding lemma}
    (Scan.depend (fn context =>
      Args.mode "open" -- Parse.enum1 "and" (Scan.repeat1 goal) --
      (by |-- Method.parse -- Scan.option Method.parse)
     >> (fn ((is_open, raw_propss), (m1, m2)) =>
          let
            val ctxt = Context.proof_of context;

            val _ = Context_Position.reports ctxt (maps Method.reports_of (m1 :: the_list m2));

            val propss = burrow (map (rpair []) o Syntax.read_props ctxt) raw_propss;
            val prep_result = Goal.norm_result ctxt #> not is_open ? Thm.close_derivation;
            fun after_qed res goal_ctxt =
              Proof_Context.put_thms false (Auto_Bind.thisN,
                SOME (map prep_result (Proof_Context.export goal_ctxt ctxt (flat res)))) goal_ctxt;

            val ctxt' = ctxt
              |> Proof.theorem NONE after_qed propss
              |> Proof.global_terminal_proof (m1, m2);
            val thms =
              Proof_Context.get_fact ctxt'
                (Facts.named (Proof_Context.full_name ctxt' (Binding.name Auto_Bind.thisN)));
          in thm_binding "lemma" (length (flat propss) = 1) context thms end))));

end;

