(*  Title:      Tools/Code/code_runtime.ML
    Author:     Florian Haftmann, TU Muenchen

Runtime services building on code generation into implementation language SML.
*)

signature CODE_RUNTIME =
sig
  val target: string
  type 'a cookie = (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string
  val dynamic_value: 'a cookie -> theory -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a option
  val dynamic_value_strict: 'a cookie -> theory -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a
  val dynamic_value_exn: 'a cookie -> theory -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a Exn.result
  val static_value: 'a cookie -> theory -> string option
    -> ((term -> term) -> 'a -> 'a) -> string list -> term -> 'a option
  val static_value_strict: 'a cookie -> theory -> string option
    -> ((term -> term) -> 'a -> 'a) -> string list -> term -> 'a
  val static_value_exn: 'a cookie -> theory -> string option
    -> ((term -> term) -> 'a -> 'a) -> string list -> term -> 'a Exn.result
  val dynamic_holds_conv: conv
  val static_holds_conv: theory -> string list -> conv
  val code_reflect: (string * string list) list -> string list -> string -> string option
    -> theory -> theory
  datatype truth = Holds
  val put_truth: (unit -> truth) -> Proof.context -> Proof.context
end;

structure Code_Runtime : CODE_RUNTIME =
struct

open Basic_Code_Thingol;

(** evaluation **)

(* technical prerequisites *)

val this = "Code_Runtime";
val s_truth = Long_Name.append this "truth";
val s_Holds = Long_Name.append this "Holds";

val target = "Eval";

datatype truth = Holds;

val _ = Context.>> (Context.map_theory
  (Code_Target.extend_target (target, (Code_ML.target_SML, K I))
  #> Code_Target.add_tyco_syntax target @{type_name prop}
       (SOME (0, (K o K o K) (Code_Printer.str s_truth)))
  #> Code_Target.add_const_syntax target @{const_name Code_Generator.holds}
       (SOME (Code_Printer.plain_const_syntax s_Holds))
  #> Code_Target.add_reserved target this
  #> fold (Code_Target.add_reserved target) ["oo", "ooo", "oooo", "upto", "downto", "orf", "andf"]));
       (*avoid further pervasive infix names*)


(* evaluation into target language values *)

type 'a cookie = (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string;

fun obtain_serializer thy some_target = Code_Target.produce_code_for thy
  (the_default target some_target) NONE "Code" [];

fun base_evaluator cookie serializer naming thy program ((vs, ty), t) deps args =
  let
    val ctxt = ProofContext.init_global thy;
    val _ = if Code_Thingol.contains_dictvar t then
      error "Term to be evaluated contains free dictionaries" else ();
    val v' = Name.variant (map fst vs) "a";
    val vs' = (v', []) :: vs
    val ty' = Code_Thingol.fun_tyco `%% [ITyVar v', ty];
    val value_name = "Value.value.value"
    val program' = program
      |> Graph.new_node (value_name,
          Code_Thingol.Fun (Term.dummy_patternN, (((vs', ty'), [(([IVar NONE], t), (NONE, true))]), NONE)))
      |> fold (curry Graph.add_edge value_name) deps;
    val (program_code, [SOME value_name']) = serializer naming program' [value_name];
    val value_code = space_implode " "
      (value_name' :: "()" :: map (enclose "(" ")") args);
  in Exn.capture (ML_Context.value ctxt cookie) (program_code, value_code) end;

fun partiality_as_none e = SOME (Exn.release e)
  handle General.Match => NONE
    | General.Bind => NONE
    | General.Fail _ => NONE;

fun dynamic_value_exn cookie thy some_target postproc t args =
  let
    fun evaluator naming program ((_, vs_ty), t) deps =
      base_evaluator cookie (obtain_serializer thy some_target) naming thy program (vs_ty, t) deps args;
  in Code_Thingol.dynamic_eval_value thy (Exn.map_result o postproc) evaluator t end;

fun dynamic_value_strict cookie thy some_target postproc t args =
  Exn.release (dynamic_value_exn cookie thy some_target postproc t args);

fun dynamic_value cookie thy some_target postproc t args =
  partiality_as_none (dynamic_value_exn cookie thy some_target postproc t args);

fun static_value_exn cookie thy some_target postproc consts =
  let
    val serializer = obtain_serializer thy some_target;
    fun evaluator naming program thy ((_, vs_ty), t) deps =
      base_evaluator cookie serializer naming thy program (vs_ty, t) deps [];
  in Code_Thingol.static_eval_value thy (Exn.map_result o postproc) consts evaluator end;

fun static_value_strict cookie thy some_target postproc consts t =
  Exn.release (static_value_exn cookie thy some_target postproc consts t);

fun static_value cookie thy some_target postproc consts t =
  partiality_as_none (static_value_exn cookie thy some_target postproc consts t);


(* evaluation for truth or nothing *)

structure Truth_Result = Proof_Data (
  type T = unit -> truth
  fun init _ () = error "Truth_Result"
);
val put_truth = Truth_Result.put;
val truth_cookie = (Truth_Result.get, put_truth, Long_Name.append this "put_truth");

fun check_holds serializer naming thy program vs_t deps ct =
  let
    val t = Thm.term_of ct;
    val _ = if fastype_of t <> propT
      then error ("Not a proposition: " ^ Syntax.string_of_term_global thy t)
      else ();
    val iff = Thm.cterm_of thy (Term.Const ("==", propT --> propT --> propT));
    val result = case partiality_as_none (base_evaluator truth_cookie serializer naming thy program vs_t deps [])
     of SOME Holds => true
      | _ => false;
  in
    Thm.mk_binop iff ct (if result then @{cprop "PROP Code_Generator.holds"} else ct)
  end;

val (_, raw_check_holds_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (Binding.name "holds_by_evaluation",
  fn (serializer, naming, thy, program, vs_t, deps, ct) => check_holds serializer naming thy program vs_t deps ct)));

fun check_holds_oracle serializer naming thy program ((_, vs_ty), t) deps ct =
  raw_check_holds_oracle (serializer, naming, thy, program, (vs_ty, t), deps, ct);

val dynamic_holds_conv = Conv.tap_thy (fn thy => Code_Thingol.dynamic_eval_conv thy
  (fn naming => check_holds_oracle (obtain_serializer thy NONE) naming thy));

fun static_holds_conv thy consts =
  let
    val serializer = obtain_serializer thy NONE;
  in
    Code_Thingol.static_eval_conv thy consts
      (fn naming => fn program => fn thy => check_holds_oracle serializer naming thy program)
  end;


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

fun process_reflection (code_body, (tyco_map, (constr_map, const_map))) module_name NONE thy =
      thy
      |> Code_Target.add_reserved target module_name
      |> Context.theory_map
        (ML_Context.exec (fn () => ML_Context.eval_text true Position.none code_body))
      |> fold (add_eval_tyco o apsnd Code_Printer.str) tyco_map
      |> fold (add_eval_constr o apsnd Code_Printer.str) constr_map
      |> fold (add_eval_const o apsnd Code_Printer.str) const_map
  | process_reflection (code_body, _) _ (SOME file_name) thy =
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
    |> process_reflection result module_name some_file
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

end; (*struct*)
