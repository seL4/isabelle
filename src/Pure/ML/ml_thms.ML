(*  Title:      Pure/ML/ml_thms.ML
    Author:     Makarius

Attribute source and theorem values within ML.
*)

signature ML_THMS =
sig
  val the_attributes: Proof.context -> int -> Token.src list
  val the_thmss: Proof.context -> thm list list
  val embedded_lemma: (Proof.context -> thm list * (term list * Proof.context)) parser
  val get_stored_thms: unit -> thm list
  val get_stored_thm: unit -> thm
  val store_thms: string * thm list -> unit
  val store_thm: string * thm -> unit
  val bind_thm: string * thm -> unit
  val bind_thms: string * thm list -> unit
end;

structure ML_Thms: ML_THMS =
struct

(* auxiliary data *)

type thms = (string * bool) * thm list;  (*name, single, value*)

structure Data = Proof_Data
(
  type T = Token.src list Inttab.table * thms list;
  fun init _ = (Inttab.empty, []);
);

val put_attributes = Data.map o apfst o Inttab.update;
fun the_attributes ctxt name = the (Inttab.lookup (fst (Data.get ctxt)) name);

val get_thmss = snd o Data.get;
val the_thmss = map snd o get_thmss;
val cons_thms = Data.map o apsnd o cons;


(* attribute source *)

val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>attributes\<close> Attrib.attribs
    (fn _ => fn srcs => fn ctxt =>
      let val i = serial () in
        ctxt
        |> put_attributes (i, srcs)
        |> ML_Antiquotation.value_decl "attributes"
            ("ML_Thms.the_attributes ML_context " ^ string_of_int i)
      end));


(* fact references *)

fun thm_binding kind is_single thms ctxt =
  let
    val initial = null (get_thmss ctxt);
    val (name, ctxt') = ML_Context.variant kind ctxt;
    val ctxt'' = cons_thms ((name, is_single), thms) ctxt';

    val ml_body = ML_Context.struct_name ctxt ^ "." ^ name;
    fun decl final_ctxt =
      if initial then
        let
          val binds = get_thmss final_ctxt |> map (fn ((a, b), _) => (b ? enclose "[" "]") a);
          val ml_env = "val [" ^ commas binds ^ "] = ML_Thms.the_thmss ML_context;\n";
        in (ml_env, ml_body) end
      else ("", ml_body);
  in (decl, ctxt'') end;

val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>thm\<close> (Attrib.thm >> single) (K (thm_binding "thm" true)) #>
   ML_Antiquotation.declaration \<^binding>\<open>thms\<close> Attrib.thms (K (thm_binding "thms" false)));


(* embedded lemma *)

val embedded_lemma =
  Args.mode "open" -- Parse.and_list1 (Scan.repeat1 Parse.embedded_inner_syntax)
    -- Parse.for_fixes -- Method.parse_by
    >> (fn (((is_open, raw_stmt), fixes), (methods, reports)) => fn ctxt =>
        let
          val _ = Context_Position.reports ctxt reports;

          val fixes_ctxt = #2 (Proof_Context.add_fixes_cmd fixes ctxt);
          val stmt = burrow (map (rpair []) o Syntax.read_props fixes_ctxt) raw_stmt;
          val stmt_ctxt = (fold o fold) (Proof_Context.augment o #1) stmt fixes_ctxt;

          val prep_result = Goal.norm_result ctxt #> not is_open ? Thm.close_derivation \<^here>;
          fun after_qed res goal_ctxt =
            Proof_Context.put_thms false (Auto_Bind.thisN,
              SOME (map prep_result (Proof_Context.export goal_ctxt ctxt (flat res)))) goal_ctxt;

          val thms_ctxt = stmt_ctxt
            |> Proof.theorem NONE after_qed stmt
            |> Proof.global_terminal_proof methods;
          val thms =
            Proof_Context.get_fact thms_ctxt
              (Facts.named (Proof_Context.full_name thms_ctxt (Binding.name Auto_Bind.thisN)))
        in (thms, (map #1 (flat stmt), stmt_ctxt)) end);

val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>lemma\<close> (Scan.lift embedded_lemma)
    (fn _ => fn make_lemma => fn ctxt =>
      let val thms = #1 (make_lemma ctxt)
      in thm_binding "lemma" (length thms = 1) thms ctxt end));


(* old-style theorem bindings *)

structure Data = Theory_Data
(
  type T = thm list;
  val empty = [];
  val merge = #1;
);

fun get_stored_thms () = Data.get (Context.the_global_context ());
val get_stored_thm = hd o get_stored_thms;

fun ml_store get (name, ths) =
  let
    val (_, ths') =
      Context.>>> (Context.map_theory_result
        (Global_Theory.note_thms "" ((Binding.name name, []), [(ths, [])])));
    val _ = Theory.setup (Data.put ths');
    val _ =
      if name = "" then ()
      else if not (ML_Syntax.is_identifier name) then
        error ("Cannot bind theorem(s) " ^ quote name ^ " as ML value")
      else
        ML_Compiler.eval (ML_Compiler.verbose true ML_Compiler.flags) Position.none
          (ML_Lex.tokenize ("val " ^ name ^ " = " ^ get ^ " ();"));
    val _ = Theory.setup (Data.put []);
  in () end;

val store_thms = ml_store "ML_Thms.get_stored_thms";
fun store_thm (name, th) = ml_store "ML_Thms.get_stored_thm" (name, [th]);

fun bind_thm (name, thm) = store_thm (name, Drule.export_without_context thm);
fun bind_thms (name, thms) = store_thms (name, map Drule.export_without_context thms);

end;
