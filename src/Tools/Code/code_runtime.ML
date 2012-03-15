(*  Title:      Tools/Code/code_runtime.ML
    Author:     Florian Haftmann, TU Muenchen

Runtime services building on code generation into implementation language SML.
*)

signature CODE_RUNTIME =
sig
  val target: string
  val value: Proof.context ->
    (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string ->
    string * string -> 'a
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
  val dynamic_holds_conv: theory -> conv
  val static_holds_conv: theory -> string list -> conv
  val code_reflect: (string * string list option) list -> string list -> string
    -> string option -> theory -> theory
  datatype truth = Holds
  val put_truth: (unit -> truth) -> Proof.context -> Proof.context
  val trace: bool Unsynchronized.ref
  val polyml_as_definition: (binding * typ) list -> Path.T list -> theory -> theory
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
val structure_generated = "Generated_Code";

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

val trace = Unsynchronized.ref false;

fun exec verbose code =
  (if ! trace then tracing code else ();
  ML_Context.exec (fn () => Secure.use_text ML_Env.local_context (0, "generated code") verbose code));

fun value ctxt (get, put, put_ml) (prelude, value) =
  let
    val code = (prelude
      ^ "\nval _ = Context.set_thread_data (SOME (Context.map_proof (" ^ put_ml
      ^ " (fn () => " ^ value ^ ")) (ML_Context.the_generic_context ())))");
    val ctxt' = ctxt
      |> put (fn () => error ("Bad evaluation for " ^ quote put_ml))
      |> Context.proof_map (exec false code);
  in get ctxt' () end;


(* evaluation into target language values *)

type 'a cookie = (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string;

fun reject_vars thy t =
  let
    val ctxt = Proof_Context.init_global thy;
  in ((Sign.no_frees ctxt o Sign.no_vars ctxt o map_types (K dummyT)) t; t) end;

fun obtain_evaluator thy some_target = Code_Target.evaluator thy (the_default target some_target);

fun evaluation cookie thy evaluator vs_t args =
  let
    val ctxt = Proof_Context.init_global thy;
    val (program_code, value_name) = evaluator vs_t;
    val value_code = space_implode " "
      (value_name :: "()" :: map (enclose "(" ")") args);
  in Exn.interruptible_capture (value ctxt cookie) (program_code, value_code) end;

fun partiality_as_none e = SOME (Exn.release e)
  handle General.Match => NONE
    | General.Bind => NONE
    | General.Fail _ => NONE;

fun dynamic_value_exn cookie thy some_target postproc t args =
  let
    val _ = reject_vars thy t;
    val _ = if ! trace
      then tracing ("Evaluation of term " ^ quote (Syntax.string_of_term_global thy t))
      else ()
    fun evaluator naming program ((_, vs_ty), t) deps =
      evaluation cookie thy (obtain_evaluator thy some_target naming program deps) (vs_ty, t) args;
  in Code_Thingol.dynamic_value thy (Exn.map_result o postproc) evaluator t end;

fun dynamic_value_strict cookie thy some_target postproc t args =
  Exn.release (dynamic_value_exn cookie thy some_target postproc t args);

fun dynamic_value cookie thy some_target postproc t args =
  partiality_as_none (dynamic_value_exn cookie thy some_target postproc t args);

fun static_evaluator cookie thy some_target naming program consts' =
  let
    val evaluator = obtain_evaluator thy some_target naming program consts'
  in fn ((_, vs_ty), t) => fn _ => evaluation cookie thy evaluator (vs_ty, t) [] end;

fun static_value_exn cookie thy some_target postproc consts =
  Code_Thingol.static_value thy (Exn.map_result o postproc) consts
    (static_evaluator cookie thy some_target) o reject_vars thy;

fun static_value_strict cookie thy some_target postproc consts =
  Exn.release o static_value_exn cookie thy some_target postproc consts;

fun static_value cookie thy some_target postproc consts =
  partiality_as_none o static_value_exn cookie thy some_target postproc consts;


(* evaluation for truth or nothing *)

structure Truth_Result = Proof_Data
(
  type T = unit -> truth
  (* FIXME avoid user error with non-user text *)
  fun init _ () = error "Truth_Result"
);
val put_truth = Truth_Result.put;
val truth_cookie = (Truth_Result.get, put_truth, Long_Name.append this "put_truth");

val reject_vars = fn thy => tap (reject_vars thy o Thm.term_of);

local

fun check_holds thy evaluator vs_t deps ct =
  let
    val t = Thm.term_of ct;
    val _ = if fastype_of t <> propT
      then error ("Not a proposition: " ^ Syntax.string_of_term_global thy t)
      else ();
    val iff = Thm.cterm_of thy (Term.Const ("==", propT --> propT --> propT));
    val result = case partiality_as_none (evaluation truth_cookie thy evaluator vs_t [])
     of SOME Holds => true
      | _ => false;
  in
    Thm.mk_binop iff ct (if result then @{cprop "PROP Code_Generator.holds"} else ct)
  end;

val (_, raw_check_holds_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (@{binding holds_by_evaluation},
  fn (thy, evaluator, vs_t, deps, ct) => check_holds thy evaluator vs_t deps ct)));

fun check_holds_oracle thy evaluator ((_, vs_ty), t) deps ct =
  raw_check_holds_oracle (thy, evaluator, (vs_ty, t), deps, ct);

in

fun dynamic_holds_conv thy = Code_Thingol.dynamic_conv thy
  (fn naming => fn program => fn vs_t => fn deps =>
    check_holds_oracle thy (obtain_evaluator thy NONE naming program deps) vs_t deps)
      o reject_vars thy;

fun static_holds_conv thy consts = Code_Thingol.static_conv thy consts
  (fn naming => fn program => fn consts' =>
    check_holds_oracle thy (obtain_evaluator thy NONE naming program consts'))
      o reject_vars thy;

end; (*local*)


(** instrumentalization **)

fun evaluation_code thy module_name tycos consts =
  let
    val ctxt = Proof_Context.init_global thy;
    val (consts', (naming, program)) = Code_Thingol.consts_program thy false consts;
    val tycos' = map (the o Code_Thingol.lookup_tyco naming) tycos;
    val (ml_code, target_names) =
      Code_Target.produce_code_for thy
        target NONE module_name [] naming program (consts' @ tycos');
    val (consts'', tycos'') = chop (length consts') target_names;
    val consts_map = map2 (fn const =>
      fn NONE =>
          error ("Constant " ^ (quote o Code.string_of_const thy) const ^
            "\nhas a user-defined serialization")
       | SOME const'' => (const, const'')) consts consts''
    val tycos_map = map2 (fn tyco =>
      fn NONE =>
          error ("Type " ^ quote (Proof_Context.extern_type ctxt tyco) ^
            "\nhas a user-defined serialization")
        | SOME tyco'' => (tyco, tyco'')) tycos tycos'';
  in (ml_code, (tycos_map, consts_map)) end;


(* by antiquotation *)

local

structure Code_Antiq_Data = Proof_Data
(
  type T = (string list * string list) * (bool
    * (string * (string * string) list) lazy);
  fun init _ = (([], []), (true, (Lazy.value ("", []))));
);

val is_first_occ = fst o snd o Code_Antiq_Data.get;

fun register_code new_tycos new_consts ctxt =
  let
    val ((tycos, consts), _) = Code_Antiq_Data.get ctxt;
    val tycos' = fold (insert (op =)) new_tycos tycos;
    val consts' = fold (insert (op =)) new_consts consts;
    val acc_code = Lazy.lazy (fn () =>
      evaluation_code (Proof_Context.theory_of ctxt) structure_generated tycos' consts'
      |> apsnd snd);
  in Code_Antiq_Data.put ((tycos', consts'), (false, acc_code)) ctxt end;

fun register_const const = register_code [] [const];

fun print_code is_first const ctxt =
  let
    val (_, (_, acc_code)) = Code_Antiq_Data.get ctxt;
    val (ml_code, consts_map) = Lazy.force acc_code;
    val ml_code = if is_first then ml_code else "";
    val body = "Isabelle." ^ the (AList.lookup (op =) consts_map const);
  in (ml_code, body) end;

in

fun ml_code_antiq raw_const background =
  let
    val const = Code.check_const (Proof_Context.theory_of background) raw_const;
    val is_first = is_first_occ background;
    val background' = register_const const background;
  in (print_code is_first const, background') end;

end; (*local*)


(* reflection support *)

fun check_datatype thy tyco some_consts =
  let
    val constrs = (map fst o snd o fst o Code.get_type thy) tyco;
    val _ = case some_consts
     of SOME consts =>
          let
            val missing_constrs = subtract (op =) consts constrs;
            val _ = if null missing_constrs then []
              else error ("Missing constructor(s) " ^ commas_quote missing_constrs
                ^ " for datatype " ^ quote tyco);
            val false_constrs = subtract (op =) constrs consts;
            val _ = if null false_constrs then []
              else error ("Non-constructor(s) " ^ commas_quote false_constrs
                ^ " for datatype " ^ quote tyco)
          in () end
      | NONE => ();
  in (tyco, constrs) end;

fun add_eval_tyco (tyco, tyco') thy =
  let
    val k = Sign.arity_number thy tyco;
    fun pr pr' _ [] = tyco'
      | pr pr' _ [ty] =
          Code_Printer.concat [pr' Code_Printer.BR ty, tyco']
      | pr pr' _ tys =
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

fun process_reflection (code, (tyco_map, (constr_map, const_map))) module_name NONE thy =
      thy
      |> Code_Target.add_reserved target module_name
      |> Context.theory_map (exec true code)
      |> fold (add_eval_tyco o apsnd Code_Printer.str) tyco_map
      |> fold (add_eval_constr o apsnd Code_Printer.str) constr_map
      |> fold (add_eval_const o apsnd Code_Printer.str) const_map
  | process_reflection (code, _) _ (SOME file_name) thy =
      let
        val preamble =
          "(* Generated from " ^
            Path.implode (Thy_Load.thy_path (Path.basic (Context.theory_name thy))) ^
          "; DO NOT EDIT! *)";
        val _ = File.write (Path.explode file_name) (preamble ^ "\n\n" ^ code);
      in
        thy
      end;

fun gen_code_reflect prep_type prep_const raw_datatypes raw_functions module_name some_file thy  =
  let
    val datatypes = map (fn (raw_tyco, raw_cos) =>
      (prep_type thy raw_tyco, (Option.map o map) (prep_const thy) raw_cos)) raw_datatypes;
    val (tycos, constrs) = map_split (uncurry (check_datatype thy)) datatypes
      |> apsnd flat;
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

val _ =
  Context.>> (Context.map_theory
    (ML_Context.add_antiq @{binding code} (fn _ => Args.term >> ml_code_antiq)));

local

val parse_datatype =
  Parse.name --| @{keyword "="} --
    (((Parse.sym_ident || Parse.string) >> (fn "_" => NONE | _ => Scan.fail ()))
    || ((Parse.term ::: (Scan.repeat (@{keyword "|"} |-- Parse.term))) >> SOME));

in

val _ =
  Outer_Syntax.command "code_reflect" "enrich runtime environment with generated code"
    Keyword.thy_decl (Parse.name -- Scan.optional (@{keyword "datatypes"} |-- (parse_datatype
      ::: Scan.repeat (@{keyword "and"} |-- parse_datatype))) []
    -- Scan.optional (@{keyword "functions"} |-- Scan.repeat1 Parse.name) []
    -- Scan.option (@{keyword "file"} |-- Parse.name)
  >> (fn (((module_name, raw_datatypes), raw_functions), some_file) => Toplevel.theory
    (code_reflect_cmd raw_datatypes raw_functions module_name some_file)));

end; (*local*)


(** using external SML files as substitute for proper definitions -- only for polyml!  **)

local

structure Loaded_Values = Theory_Data
(
  type T = string list
  val empty = []
  val extend = I
  fun merge data : T = Library.merge (op =) data
);

fun notify_val (string, value) = 
  let
    val _ = #enterVal ML_Env.name_space (string, value);
    val _ = Context.>> ((Context.map_theory o Loaded_Values.map) (insert (op =) string));
  in () end;

fun abort _ = error "Only value bindings allowed.";

val notifying_context : use_context =
 {tune_source = #tune_source ML_Env.local_context,
  name_space =
   {lookupVal    = #lookupVal ML_Env.name_space,
    lookupType   = #lookupType ML_Env.name_space,
    lookupFix    = #lookupFix ML_Env.name_space,
    lookupStruct = #lookupStruct ML_Env.name_space,
    lookupSig    = #lookupSig ML_Env.name_space,
    lookupFunct  = #lookupFunct ML_Env.name_space,
    enterVal     = notify_val,
    enterType    = abort,
    enterFix     = abort,
    enterStruct  = abort,
    enterSig     = abort,
    enterFunct   = abort,
    allVal       = #allVal ML_Env.name_space,
    allType      = #allType ML_Env.name_space,
    allFix       = #allFix ML_Env.name_space,
    allStruct    = #allStruct ML_Env.name_space,
    allSig       = #allSig ML_Env.name_space,
    allFunct     = #allFunct ML_Env.name_space},
  str_of_pos = #str_of_pos ML_Env.local_context,
  print = #print ML_Env.local_context,
  error = #error ML_Env.local_context};

in

fun use_file filepath thy =
  let
    val thy' = Loaded_Values.put [] thy;
    val _ = Context.set_thread_data ((SOME o Context.Theory) thy');
    val _ = Secure.use_text notifying_context
      (0, Path.implode filepath) false (File.read filepath);
    val thy'' = Context.the_theory (Context.the_thread_data ());
    val names = Loaded_Values.get thy'';
  in (names, thy'') end;

end;

fun add_definiendum (ml_name, (b, T)) thy =
  thy
  |> Code_Target.add_reserved target ml_name
  |> Specification.axiomatization [(b, SOME T, NoSyn)] []
  |-> (fn ([Const (const, _)], _) =>
     Code_Target.add_const_syntax target const
       (SOME (Code_Printer.simple_const_syntax (0, (K o K o K o Code_Printer.str) ml_name)))
  #> tap (fn thy => Code_Target.produce_code thy [const] target NONE structure_generated []));

fun process_file filepath (definienda, thy) =
  let
    val (ml_names, thy') = use_file filepath thy;
    val superfluous = subtract (fn ((name1, _), name2) => name1 = name2) definienda ml_names;
    val _ = if null superfluous then ()
      else error ("Value binding(s) " ^ commas_quote superfluous
        ^ " found in external file " ^ Path.print filepath
        ^ " not present among the given contants binding(s).");
    val these_definienda = AList.make (the o AList.lookup (op =) definienda) ml_names;
    val thy'' = fold add_definiendum these_definienda thy';
    val definienda' = fold (AList.delete (op =)) ml_names definienda;
  in (definienda', thy'') end;

fun polyml_as_definition bTs filepaths thy =
  let
    val definienda = map (fn bT => ((Binding.name_of o fst) bT, bT)) bTs;
    val (remaining, thy') = fold process_file filepaths (definienda, thy);
    val _ = if null remaining then ()
      else error ("Constant binding(s) " ^ commas_quote (map fst remaining)
        ^ " not present in external file(s).");
  in thy' end;

end; (*struct*)
