(*  Title:      Tools/Code/code_runtime.ML
    Author:     Florian Haftmann, TU Muenchen

Runtime services building on code generation into implementation language SML.
*)

signature CODE_RUNTIME =
sig
  val target: string
  val value: string option
    -> (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string
    -> ((term -> term) -> 'a -> 'a) -> theory -> term -> string list -> 'a
  val code_reflect: (string * string list) list -> string list -> string -> string option
    -> theory -> theory
  val setup: theory -> theory
end;

structure Code_Runtime : CODE_RUNTIME =
struct

(** evaluation **)

val target = "Eval";

val truth_struct = "Code_Truth";

fun value some_target cookie postproc thy t args =
  let
    val ctxt = ProofContext.init_global thy;
    fun evaluator naming program ((_, (_, ty)), t) deps =
      let
        val _ = if Code_Thingol.contains_dictvar t then
          error "Term to be evaluated contains free dictionaries" else ();
        val value_name = "Value.VALUE.value"
        val program' = program
          |> Graph.new_node (value_name,
              Code_Thingol.Fun (Term.dummy_patternN, ((([], ty), [(([], t), (NONE, true))]), NONE)))
          |> fold (curry Graph.add_edge value_name) deps;
        val (program_code, [SOME value_name']) = Code_Target.produce_code_for thy
          (the_default target some_target) NONE "Code" [] naming program' [value_name];
        val value_code = space_implode " "
          (value_name' :: map (enclose "(" ")") args);
      in ML_Context.value ctxt cookie (program_code, value_code) end;
  in Code_Thingol.dynamic_eval_value thy postproc evaluator t end;


(** instrumentalization **)

fun evaluation_code thy module_name tycos consts =
  let
    val (consts', (naming, program)) = Code_Thingol.consts_program thy false consts;
    val tycos' = map (the o Code_Thingol.lookup_tyco naming) tycos;
    val (ml_code, target_names) = Code_Target.produce_code_for thy
      target NONE module_name [] naming program (consts' @ tycos');
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


(* by antiquotation *)

local

structure Code_Antiq_Data = Proof_Data
(
  type T = (string list * string list) * (bool
    * (string * ((string * string) list * (string * string) list)) lazy);
  fun init _ = (([], []), (true, (Lazy.value ("", ([], [])))));
);

val is_first_occ = fst o snd o Code_Antiq_Data.get;

fun register_code new_tycos new_consts ctxt =
  let
    val ((tycos, consts), _) = Code_Antiq_Data.get ctxt;
    val tycos' = fold (insert (op =)) new_tycos tycos;
    val consts' = fold (insert (op =)) new_consts consts;
    val acc_code = Lazy.lazy (fn () =>
      evaluation_code (ProofContext.theory_of ctxt) "Code" tycos' consts');
  in Code_Antiq_Data.put ((tycos', consts'), (false, acc_code)) ctxt end;

fun register_const const = register_code [] [const];

fun register_datatype tyco constrs = register_code [tyco] constrs;

fun print_const const all_struct_name tycos_map consts_map =
  (Long_Name.append all_struct_name o the o AList.lookup (op =) consts_map) const;

fun print_code is_first print_it ctxt =
  let
    val (_, (_, acc_code)) = Code_Antiq_Data.get ctxt;
    val (ml_code, (tycos_map, consts_map)) = Lazy.force acc_code;
    val ml_code = if is_first then ml_code
      else "";
    val all_struct_name = "Isabelle";
  in (ml_code, print_it all_struct_name tycos_map consts_map) end;

in

fun ml_code_antiq raw_const background =
  let
    val const = Code.check_const (ProofContext.theory_of background) raw_const;
    val is_first = is_first_occ background;
    val background' = register_const const background;
  in (print_code is_first (print_const const), background') end;

end; (*local*)


(* reflection support *)

fun check_datatype thy tyco consts =
  let
    val constrs = (map (fst o fst) o snd o Code.get_type thy) tyco;
    val missing_constrs = subtract (op =) consts constrs;
    val _ = if null missing_constrs then []
      else error ("Missing constructor(s) " ^ commas (map quote missing_constrs)
        ^ " for datatype " ^ quote tyco);
    val false_constrs = subtract (op =) constrs consts;
    val _ = if null false_constrs then []
      else error ("Non-constructor(s) " ^ commas (map quote false_constrs)
        ^ " for datatype " ^ quote tyco);
  in () end;

fun add_eval_tyco (tyco, tyco') thy =
  let
    val k = Sign.arity_number thy tyco;
    fun pr pr' fxy [] = tyco'
      | pr pr' fxy [ty] =
          Code_Printer.concat [pr' Code_Printer.BR ty, tyco']
      | pr pr' fxy tys =
          Code_Printer.concat [Code_Printer.enum "," "(" ")" (map (pr' Code_Printer.BR) tys), tyco']
  in
    thy
    |> Code_Target.add_tyco_syntax target tyco (SOME (k, pr))
  end;

fun add_eval_constr (const, const') thy =
  let
    val k = Code.args_number thy const;
    fun pr pr' fxy ts = Code_Printer.brackify fxy
      (const' :: the_list (Code_Printer.tuplify pr' Code_Printer.BR (map fst ts)));
  in
    thy
    |> Code_Target.add_const_syntax target const (SOME (Code_Printer.simple_const_syntax (k, pr)))
  end;

fun add_eval_const (const, const') = Code_Target.add_const_syntax target
  const (SOME (Code_Printer.simple_const_syntax (0, (K o K o K) const')));

fun process (code_body, (tyco_map, (constr_map, const_map))) module_name NONE thy =
      thy
      |> Code_Target.add_reserved target module_name
      |> Context.theory_map
        (ML_Context.exec (fn () => ML_Context.eval_text true Position.none code_body))
      |> fold (add_eval_tyco o apsnd Code_Printer.str) tyco_map
      |> fold (add_eval_constr o apsnd Code_Printer.str) constr_map
      |> fold (add_eval_const o apsnd Code_Printer.str) const_map
  | process (code_body, _) _ (SOME file_name) thy =
      let
        val preamble =
          "(* Generated from " ^ Path.implode (Thy_Header.thy_path (Context.theory_name thy))
          ^ "; DO NOT EDIT! *)";
        val _ = File.write (Path.explode file_name) (preamble ^ "\n\n" ^ code_body);
      in
        thy
      end;

fun gen_code_reflect prep_type prep_const raw_datatypes raw_functions module_name some_file thy  =
  let
    val datatypes = map (fn (raw_tyco, raw_cos) =>
      (prep_type thy raw_tyco, map (prep_const thy) raw_cos)) raw_datatypes;
    val _ = map (uncurry (check_datatype thy)) datatypes;
    val tycos = map fst datatypes;
    val constrs = maps snd datatypes;
    val functions = map (prep_const thy) raw_functions;
    val result = evaluation_code thy module_name tycos (constrs @ functions)
      |> (apsnd o apsnd) (chop (length constrs));
  in
    thy
    |> process result module_name some_file
  end;

val code_reflect = gen_code_reflect Code_Target.cert_tyco (K I);
val code_reflect_cmd = gen_code_reflect Code_Target.read_tyco Code.read_const;


(** Isar setup **)

val _ = ML_Context.add_antiq "code" (fn _ => Args.term >> ml_code_antiq);

local

val datatypesK = "datatypes";
val functionsK = "functions";
val fileK = "file";
val andK = "and"

val _ = List.app Keyword.keyword [datatypesK, functionsK];

val parse_datatype =
  Parse.name --| Parse.$$$ "=" -- (Parse.term ::: (Scan.repeat (Parse.$$$ "|" |-- Parse.term)));

in

val _ =
  Outer_Syntax.command "code_reflect" "enrich runtime environment with generated code"
    Keyword.thy_decl (Parse.name -- Scan.optional (Parse.$$$ datatypesK |-- (parse_datatype
      ::: Scan.repeat (Parse.$$$ andK |-- parse_datatype))) []
    -- Scan.optional (Parse.$$$ functionsK |-- Scan.repeat1 Parse.name) []
    -- Scan.option (Parse.$$$ fileK |-- Parse.name)
  >> (fn (((module_name, raw_datatypes), raw_functions), some_file) => Toplevel.theory
    (code_reflect_cmd raw_datatypes raw_functions module_name some_file)));

end; (*local*)

val setup = Code_Target.extend_target (target, (Code_ML.target_SML, K I));

end; (*struct*)
