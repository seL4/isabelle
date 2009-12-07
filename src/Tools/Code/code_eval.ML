(*  Title:      Tools/code/code_eval.ML_
    Author:     Florian Haftmann, TU Muenchen

Runtime services building on code generation into implementation language SML.
*)

signature CODE_EVAL =
sig
  val target: string
  val eval: string option -> string * (unit -> 'a) option Unsynchronized.ref
    -> ((term -> term) -> 'a -> 'a) -> theory -> term -> string list -> 'a
  val evaluation_code: theory -> string list -> string list
    -> string * ((string * string) list * (string * string) list)
  val setup: theory -> theory
end;

structure Code_Eval : CODE_EVAL =
struct

(** generic **)

val target = "Eval";

val eval_struct_name = "Code"

fun evaluation_code thy tycos consts =
  let
    val (consts', (naming, program)) = Code_Thingol.consts_program thy consts;
    val tycos' = map (the o Code_Thingol.lookup_tyco naming) tycos;
    val (ml_code, target_names) = Code_ML.evaluation_code_of thy target
      (SOME eval_struct_name) naming program (consts' @ tycos');
    val (consts'', tycos'') = chop (length consts') target_names;
    val consts_map = map2 (fn const => fn NONE =>
        error ("Constant " ^ (quote o Code.string_of_const thy) const
          ^ "\nhas a user-defined serialization")
      | SOME const'' => (const, const'')) consts consts''
    val tycos_map = map2 (fn tyco => fn NONE =>
        error ("Type " ^ (quote o Sign.extern_type thy) tyco
          ^ "\nhas a user-defined serialization")
      | SOME tyco'' => (tyco, tyco'')) tycos tycos'';
  in (ml_code, (tycos_map, consts_map)) end;


(** evaluation **)

fun eval some_target reff postproc thy t args =
  let
    val ctxt = ProofContext.init thy;
    fun evaluator naming program ((_, (_, ty)), t) deps =
      let
        val _ = if Code_Thingol.contains_dictvar t then
          error "Term to be evaluated contains free dictionaries" else ();
        val value_name = "Value.VALUE.value"
        val program' = program
          |> Graph.new_node (value_name,
              Code_Thingol.Fun (Term.dummy_patternN, (([], ty), [(([], t), (Drule.dummy_thm, true))])))
          |> fold (curry Graph.add_edge value_name) deps;
        val (value_code, [SOME value_name']) = Code_ML.evaluation_code_of thy
          (the_default target some_target) NONE naming program' [value_name];
        val sml_code = "let\n" ^ value_code ^ "\nin " ^ value_name'
          ^ space_implode " " (map (enclose "(" ")") args) ^ " end";
      in ML_Context.evaluate ctxt false reff sml_code end;
  in Code_Thingol.eval thy postproc evaluator t end;


(** instrumentalization by antiquotation **)

local

structure CodeAntiqData = Proof_Data
(
  type T = (string list * string list) * (bool * (string
    * (string * ((string * string) list * (string * string) list)) lazy));
  fun init _ = (([], []), (true, ("", Lazy.value ("", ([], [])))));
);

val is_first_occ = fst o snd o CodeAntiqData.get;

fun register_code new_tycos new_consts ctxt =
  let
    val ((tycos, consts), (_, (struct_name, _))) = CodeAntiqData.get ctxt;
    val tycos' = fold (insert (op =)) new_tycos tycos;
    val consts' = fold (insert (op =)) new_consts consts;
    val (struct_name', ctxt') = if struct_name = ""
      then ML_Antiquote.variant eval_struct_name ctxt
      else (struct_name, ctxt);
    val acc_code = Lazy.lazy (fn () => evaluation_code (ProofContext.theory_of ctxt) tycos' consts');
  in CodeAntiqData.put ((tycos', consts'), (false, (struct_name', acc_code))) ctxt' end;

fun register_const const = register_code [] [const];

fun register_datatype tyco constrs = register_code [tyco] constrs;

fun print_const const all_struct_name tycos_map consts_map =
  (Long_Name.append all_struct_name o the o AList.lookup (op =) consts_map) const;

fun print_datatype tyco constrs all_struct_name tycos_map consts_map =
  let
    val upperize = implode o nth_map 0 Symbol.to_ascii_upper o explode;
    fun check_base name name'' =
      if upperize (Long_Name.base_name name) = upperize name''
      then () else error ("Name as printed " ^ quote name''
        ^ "\ndiffers from logical base name " ^ quote (Long_Name.base_name name) ^ "; sorry.");
    val tyco'' = (the o AList.lookup (op =) tycos_map) tyco;
    val constrs'' = map (the o AList.lookup (op =) consts_map) constrs;
    val _ = check_base tyco tyco'';
    val _ = map2 check_base constrs constrs'';
  in "datatype " ^ tyco'' ^ " = datatype " ^ Long_Name.append all_struct_name tyco'' end;

fun print_code struct_name is_first print_it ctxt =
  let
    val (_, (_, (struct_code_name, acc_code))) = CodeAntiqData.get ctxt;
    val (ml_code, (tycos_map, consts_map)) = Lazy.force acc_code;
    val ml_code = if is_first then ml_code
      else "";
    val all_struct_name = Long_Name.append struct_name struct_code_name;
  in (ml_code, print_it all_struct_name tycos_map consts_map) end;

in

fun ml_code_antiq raw_const {struct_name, background} =
  let
    val const = Code.check_const (ProofContext.theory_of background) raw_const;
    val is_first = is_first_occ background;
    val background' = register_const const background;
  in (print_code struct_name is_first (print_const const), background') end;

fun ml_code_datatype_antiq (raw_tyco, raw_constrs) {struct_name, background} =
  let
    val thy = ProofContext.theory_of background;
    val tyco = Sign.intern_type thy raw_tyco;
    val constrs = map (Code.check_const thy) raw_constrs;
    val constrs' = (map fst o snd o Code.get_datatype thy) tyco;
    val _ = if eq_set (op =) (constrs, constrs') then ()
      else error ("Type " ^ quote tyco ^ ": given constructors diverge from real constructors")
    val is_first = is_first_occ background;
    val background' = register_datatype tyco constrs background;
  in (print_code struct_name is_first (print_datatype tyco constrs), background') end;

end; (*local*)


(** Isar setup **)

val _ = ML_Context.add_antiq "code" (fn _ => Args.term >> ml_code_antiq);
val _ = ML_Context.add_antiq "code_datatype" (fn _ =>
  (Args.tyname --| Scan.lift (Args.$$$ "=")
    -- (Args.term ::: Scan.repeat (Scan.lift (Args.$$$ "|") |-- Args.term)))
      >> ml_code_datatype_antiq);

val setup = Code_Target.extend_target (target, (Code_ML.target_SML, K I));

end; (*struct*)
