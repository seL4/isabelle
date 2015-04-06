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
  val dynamic_value: 'a cookie -> Proof.context -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a option
  val dynamic_value_strict: 'a cookie -> Proof.context -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a
  val dynamic_value_exn: 'a cookie -> Proof.context -> string option
    -> ((term -> term) -> 'a -> 'a) -> term -> string list -> 'a Exn.result
  val static_value: 'a cookie -> { ctxt: Proof.context, target: string option,
    lift_postproc: (term -> term) -> 'a -> 'a, consts: string list }
    -> Proof.context -> term -> 'a option
  val static_value_strict: 'a cookie -> { ctxt: Proof.context, target: string option,
    lift_postproc: (term -> term) -> 'a -> 'a, consts: string list }
    -> Proof.context -> term -> 'a
  val static_value_exn: 'a cookie -> { ctxt: Proof.context, target: string option,
    lift_postproc: (term -> term) -> 'a -> 'a, consts: string list }
    -> Proof.context -> term -> 'a Exn.result
  val dynamic_holds_conv: Proof.context -> conv
  val static_holds_conv: { ctxt: Proof.context, consts: string list } -> Proof.context -> conv
  val static_value': (Proof.context -> term -> 'a) cookie
    -> { ctxt: Proof.context, lift_postproc: (term -> term) -> 'a -> 'a,
           consts: (string * typ) list, T: typ }
    -> Proof.context -> term -> 'a option (*EXPERIMENTAL!*)
  val static_value_strict': (Proof.context -> term -> 'a) cookie
    -> { ctxt: Proof.context, lift_postproc: (term -> term) -> 'a -> 'a,
           consts: (string * typ) list, T: typ }
    -> Proof.context -> term -> 'a (*EXPERIMENTAL!*)
  val static_value_exn': (Proof.context -> term -> 'a) cookie
    -> { ctxt: Proof.context, lift_postproc: (term -> term) -> 'a -> 'a,
           consts: (string * typ) list, T: typ }
    -> Proof.context -> term -> 'a Exn.result (*EXPERIMENTAL!*)
  val code_reflect: (string * string list option) list -> string list -> string
    -> string option -> theory -> theory
  datatype truth = Holds
  val put_truth: (unit -> truth) -> Proof.context -> Proof.context
  val trace: bool Config.T
  val polyml_as_definition: (binding * typ) list -> Path.T list -> theory -> theory
end;

structure Code_Runtime : CODE_RUNTIME =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;

(** evaluation **)

(* technical prerequisites *)

val this = "Code_Runtime";
val s_truth = Long_Name.append this "truth";
val s_Holds = Long_Name.append this "Holds";

val target = "Eval";
val structure_generated = "Generated_Code";

datatype truth = Holds;

val _ = Theory.setup
  (Code_Target.add_derived_target (target, [(Code_ML.target_SML, I)])
  #> Code_Target.set_printings (Type_Constructor (@{type_name prop},
    [(target, SOME (0, (K o K o K) (Code_Printer.str s_truth)))]))
  #> Code_Target.set_printings (Constant (@{const_name Code_Generator.holds},
    [(target, SOME (Code_Printer.plain_const_syntax s_Holds))]))
  #> Code_Target.add_reserved target this
  #> fold (Code_Target.add_reserved target) ["oo", "ooo", "oooo", "upto", "downto", "orf", "andf"]);
       (*avoid further pervasive infix names*)

val trace = Attrib.setup_config_bool @{binding "code_runtime_trace"} (K false);

fun exec ctxt verbose code =
  (if Config.get ctxt trace then tracing code else ();
  ML_Context.exec (fn () => Secure.use_text ML_Env.local_context (0, "generated code") verbose code));

fun value ctxt (get, put, put_ml) (prelude, value) =
  let
    val code = (prelude
      ^ "\nval _ = Context.set_thread_data (SOME (Context.map_proof (" ^ put_ml
      ^ " (fn () => " ^ value ^ ")) (ML_Context.the_generic_context ())))");
    val ctxt' = ctxt
      |> put (fn () => error ("Bad evaluation for " ^ quote put_ml))
      |> Context.proof_map (exec ctxt false code);
  in get ctxt' () end;


(* evaluation into target language values *)

type 'a cookie = (Proof.context -> unit -> 'a) * ((unit -> 'a) -> Proof.context -> Proof.context) * string;

fun reject_vars ctxt t =
  ((Sign.no_frees ctxt o Sign.no_vars ctxt o map_types (K dummyT)) t; t);

fun obtain_evaluator ctxt some_target program consts =
  let
    val evaluator' = Code_Target.evaluator ctxt (the_default target some_target) program consts false;
  in
    evaluator'
    #> apfst (fn ml_modules => space_implode "\n\n" (map snd ml_modules))
  end;

fun evaluation cookie ctxt evaluator vs_t args =
  let
    val (program_code, value_name) = evaluator vs_t;
    val value_code = space_implode " "
      (value_name :: "()" :: map (enclose "(" ")") args);
  in Exn.interruptible_capture (value ctxt cookie) (program_code, value_code) end;

fun partiality_as_none e = SOME (Exn.release e)
  handle General.Match => NONE
    | General.Bind => NONE
    | General.Fail _ => NONE;

fun dynamic_value_exn cookie ctxt some_target postproc t args =
  let
    val _ = reject_vars ctxt t;
    val _ = if Config.get ctxt trace
      then tracing ("Evaluation of term " ^ quote (Syntax.string_of_term ctxt t))
      else ()
    fun evaluator program _ vs_ty_t deps =
      evaluation cookie ctxt (obtain_evaluator ctxt some_target program deps) vs_ty_t args;
  in Code_Thingol.dynamic_value ctxt (Exn.map_result o postproc) evaluator t end;

fun dynamic_value_strict cookie ctxt some_target postproc t args =
  Exn.release (dynamic_value_exn cookie ctxt some_target postproc t args);

fun dynamic_value cookie ctxt some_target postproc t args =
  partiality_as_none (dynamic_value_exn cookie ctxt some_target postproc t args);

fun static_evaluator cookie ctxt some_target { program, deps } =
  let
    val evaluator = obtain_evaluator ctxt some_target program (map Constant deps);
    val evaluation' = evaluation cookie ctxt evaluator;
  in fn _ => fn _ => fn vs_ty_t => fn _ => evaluation' vs_ty_t [] end;

fun static_value_exn cookie { ctxt, target, lift_postproc, consts } =
  let
    val evaluator = Code_Thingol.static_value { ctxt = ctxt,
      lift_postproc = Exn.map_result o lift_postproc, consts = consts }
      (static_evaluator cookie ctxt target);
  in fn ctxt' => evaluator ctxt' o reject_vars ctxt' end;

fun static_value_strict cookie = Exn.release ooo static_value_exn cookie;

fun static_value cookie = partiality_as_none ooo static_value_exn cookie;


(* evaluation for truth or nothing *)

structure Truth_Result = Proof_Data
(
  type T = unit -> truth;
  val empty: T = fn () => raise Fail "Truth_Result";
  fun init _ = empty;
);
val put_truth = Truth_Result.put;
val truth_cookie = (Truth_Result.get, put_truth, Long_Name.append this "put_truth");

local

val reject_vars = fn ctxt => tap (reject_vars ctxt o Thm.term_of);

fun check_holds ctxt evaluator vs_t ct =
  let
    val t = Thm.term_of ct;
    val _ = if fastype_of t <> propT
      then error ("Not a proposition: " ^ Syntax.string_of_term ctxt t)
      else ();
    val iff = Thm.cterm_of ctxt (Term.Const (@{const_name Pure.eq}, propT --> propT --> propT));
    val result = case partiality_as_none (evaluation truth_cookie ctxt evaluator vs_t [])
     of SOME Holds => true
      | _ => false;
  in
    Thm.mk_binop iff ct (if result then @{cprop "PROP Code_Generator.holds"} else ct)
  end;

val (_, raw_check_holds_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (@{binding holds_by_evaluation},
  fn (ctxt, evaluator, vs_t, ct) => check_holds ctxt evaluator vs_t ct)));

fun check_holds_oracle ctxt evaluator vs_ty_t ct =
  raw_check_holds_oracle (ctxt, evaluator, vs_ty_t, ct);

in

fun dynamic_holds_conv ctxt = Code_Thingol.dynamic_conv ctxt
  (fn program => fn vs_t => fn deps =>
    check_holds_oracle ctxt (obtain_evaluator ctxt NONE program deps) vs_t)
      o reject_vars ctxt;

fun static_holds_conv (ctxt_consts as { ctxt, ... }) =
  Code_Thingol.static_conv ctxt_consts (fn { program, deps } => fn ctxt' => fn vs_t =>
    K (check_holds_oracle ctxt' (obtain_evaluator ctxt NONE program (map Constant deps)) vs_t o reject_vars ctxt'));

end; (*local*)


(** full static evaluation -- still with limited coverage! **)

fun evaluation_code ctxt module_name program tycos consts =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (ml_modules, target_names) =
      Code_Target.produce_code_for ctxt
        target NONE module_name [] program false (map Constant consts @ map Type_Constructor tycos);
    val ml_code = space_implode "\n\n" (map snd ml_modules);
    val (consts', tycos') = chop (length consts) target_names;
    val consts_map = map2 (fn const =>
      fn NONE =>
          error ("Constant " ^ (quote o Code.string_of_const thy) const ^
            "\nhas a user-defined serialization")
       | SOME const' => (const, const')) consts consts'
    val tycos_map = map2 (fn tyco =>
      fn NONE =>
          error ("Type " ^ quote (Proof_Context.markup_type ctxt tyco) ^
            "\nhas a user-defined serialization")
        | SOME tyco' => (tyco, tyco')) tycos tycos';
  in (ml_code, (tycos_map, consts_map)) end;

fun typ_signatures_for T =
  let
    val (Ts, T') = strip_type T;
  in map_range (fn n => (drop n Ts ---> T', take n Ts)) (length Ts + 1) end;

fun typ_signatures cTs =
  let
    fun add (c, T) =
      fold (fn (T, Ts) => Typtab.map_default (T, []) (cons (c, Ts)))
        (typ_signatures_for T);
  in
    Typtab.empty
    |> fold add cTs
    |> Typtab.lookup_list
  end;

fun print_of_term_funs { typ_sign_for, ml_name_for_const, ml_name_for_typ } Ts =
  let
    val var_names = map_range (fn n => "t" ^ string_of_int (n + 1));
    fun print_lhs c xs = "Const (" ^ quote c ^ ", _)"
      |> fold (fn x => fn s => s ^ " $ " ^ x) xs
      |> enclose "(" ")"
      |> prefix "ctxt ";
    fun print_rhs c Ts xs = ml_name_for_const c
      |> fold2 (fn T => fn x => fn s =>
         s ^ (" (" ^ ml_name_for_typ T ^ " ctxt " ^ x ^ ")")) Ts xs
    fun print_eq (c, Ts) =
      let
        val xs = var_names (length Ts);
      in print_lhs c xs ^ " = " ^ print_rhs c Ts xs end;
    val err_eq =
      "ctxt t = error (" ^ quote "Bad term: " ^ " ^ Syntax.string_of_term ctxt t)";
    fun print_eqs T =
      let
        val typ_signs = typ_sign_for T;
        val name = ml_name_for_typ T;
      in
        (map print_eq typ_signs @ [err_eq])
        |> map (prefix (name ^ " "))
        |> space_implode "\n  | "
      end;
  in
    map print_eqs Ts
    |> space_implode "\nand "
    |> prefix "fun "
    |> pair (map ml_name_for_typ Ts)
  end;

fun print_of_term ctxt ml_name_for_const T cTs =
  let
    val typ_sign_for = typ_signatures cTs;
    fun add_typ T Ts =
      if member (op =) Ts T
      then Ts
      else Ts
        |> cons T
        |> fold (fold add_typ o snd) (typ_sign_for T);
    val Ts = add_typ T [];
    fun tycos_of (Type (tyco, Ts)) = maps tycos_of Ts @ [tyco]
      | tycos_of _ = [];
    val ml_name_of = Name.desymbolize NONE o Long_Name.base_name;
    val ml_names = map (suffix "_of_term" o space_implode "_" o map ml_name_of o tycos_of) Ts
      |> Name.variant_list [];
    val ml_name_for_typ = the o AList.lookup (op =) (Ts ~~ ml_names);
  in
    print_of_term_funs { typ_sign_for = typ_sign_for,
      ml_name_for_const = ml_name_for_const,
      ml_name_for_typ = ml_name_for_typ } Ts
  end;

fun compile_evaluator cookie ctxt cs_code cTs T { program, deps } =
  let
    val (context_code, (_, const_map)) =
      evaluation_code ctxt structure_generated program [] cs_code;
    val ml_name_for_const = the o AList.lookup (op =) const_map;
    val (ml_names, of_term_code) = print_of_term ctxt ml_name_for_const T cTs
    val of_term = value ctxt cookie (context_code ^ "\n" ^ of_term_code, List.last ml_names);
  in fn ctxt' => fn t => fn _ => fn _ => Exn.interruptible_capture (of_term ctxt') t end;

fun static_value_exn' cookie { ctxt, lift_postproc, consts, T } =
  let
    val thy = Proof_Context.theory_of ctxt;
    val cs_code = map (Axclass.unoverload_const thy) consts;
    val cTs = map2 (fn (_, T) => fn c => (c, T)) consts cs_code;
    val evaluator = Code_Thingol.static_value { ctxt = ctxt,
      lift_postproc = Exn.map_result o lift_postproc, consts = cs_code }
      (compile_evaluator cookie ctxt cs_code cTs T);
  in fn ctxt' =>
    evaluator ctxt' o reject_vars ctxt' o Syntax.check_term ctxt' o Type.constraint T
  end;

fun static_value_strict' cookie = Exn.release ooo static_value_exn' cookie;

fun static_value' cookie = partiality_as_none ooo static_value_exn' cookie;

fun static_value_strict' cookie = Exn.release ooo static_value_exn' cookie;

fun static_value' cookie = partiality_as_none ooo static_value_exn' cookie;


(** code antiquotation **)

local

structure Code_Antiq_Data = Proof_Data
(
  type T = (string list * string list) * (bool
    * (string * (string * string) list) lazy);
  val empty: T = (([], []), (true, (Lazy.value ("", []))));
  fun init _ = empty;
);

val is_first_occ = fst o snd o Code_Antiq_Data.get;

fun register_code new_tycos new_consts ctxt =
  let
    val ((tycos, consts), _) = Code_Antiq_Data.get ctxt;
    val tycos' = fold (insert (op =)) new_tycos tycos;
    val consts' = fold (insert (op =)) new_consts consts;
    val program = Code_Thingol.consts_program (Proof_Context.theory_of ctxt) consts';
    val acc_code = Lazy.lazy (fn () =>
      evaluation_code ctxt structure_generated program tycos' consts'
      |> apsnd snd);
  in Code_Antiq_Data.put ((tycos', consts'), (false, acc_code)) ctxt end;

fun register_const const = register_code [] [const];

fun print_code is_first const ctxt =
  let
    val (_, (_, acc_code)) = Code_Antiq_Data.get ctxt;
    val (ml_code, consts_map) = Lazy.force acc_code;
    val ml_code = if is_first then ml_code else "";
    val body = ML_Context.struct_name ctxt ^ "." ^ the (AList.lookup (op =) consts_map const);
  in (ml_code, body) end;

in

fun ml_code_antiq raw_const ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val const = Code.check_const thy raw_const;
    val is_first = is_first_occ ctxt;
  in (print_code is_first const, register_const const ctxt) end;

end; (*local*)


(** reflection support **)

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
    |> Code_Target.set_printings (Type_Constructor (tyco, [(target, SOME (k, pr))]))
  end;

fun add_eval_constr (const, const') thy =
  let
    val k = Code.args_number thy const;
    fun pr pr' fxy ts = Code_Printer.brackify fxy
      (const' :: the_list (Code_Printer.tuplify pr' Code_Printer.BR (map fst ts)));
  in
    thy
    |> Code_Target.set_printings (Constant (const,
      [(target, SOME (Code_Printer.simple_const_syntax (k, pr)))]))
  end;

fun add_eval_const (const, const') = Code_Target.set_printings (Constant
  (const, [(target, SOME (Code_Printer.simple_const_syntax (0, (K o K o K) const')))]));

fun process_reflection (code, (tyco_map, (constr_map, const_map))) module_name NONE thy =
      thy
      |> Code_Target.add_reserved target module_name
      |> Context.theory_map (exec (Proof_Context.init_global thy (*FIXME*)) true code)
      |> fold (add_eval_tyco o apsnd Code_Printer.str) tyco_map
      |> fold (add_eval_constr o apsnd Code_Printer.str) constr_map
      |> fold (add_eval_const o apsnd Code_Printer.str) const_map
  | process_reflection (code, _) _ (SOME file_name) thy =
      let
        val preamble =
          "(* Generated from " ^
            Path.implode (Resources.thy_path (Path.basic (Context.theory_name thy))) ^
          "; DO NOT EDIT! *)";
        val _ = File.write (Path.explode file_name) (preamble ^ "\n\n" ^ code);
      in
        thy
      end;

fun gen_code_reflect prep_type prep_const raw_datatypes raw_functions module_name some_file thy  =
  let
    val ctxt = Proof_Context.init_global thy;
    val datatypes = map (fn (raw_tyco, raw_cos) =>
      (prep_type ctxt raw_tyco, (Option.map o map) (prep_const thy) raw_cos)) raw_datatypes;
    val (tycos, constrs) = map_split (uncurry (check_datatype thy)) datatypes
      |> apsnd flat;
    val functions = map (prep_const thy) raw_functions;
    val consts = constrs @ functions;
    val program = Code_Thingol.consts_program (Proof_Context.theory_of ctxt) consts;
    val result = evaluation_code ctxt module_name program tycos consts
      |> (apsnd o apsnd) (chop (length constrs));
  in
    thy
    |> process_reflection result module_name some_file
  end;

val code_reflect = gen_code_reflect Code_Target.cert_tyco (K I);
val code_reflect_cmd = gen_code_reflect Code_Target.read_tyco Code.read_const;


(** Isar setup **)

val _ =
  Theory.setup (ML_Antiquotation.declaration @{binding code} Args.term (fn _ => ml_code_antiq));

local

val parse_datatype =
  Parse.name --| @{keyword "="} --
    (((Parse.sym_ident || Parse.string) >> (fn "_" => NONE | _ => Scan.fail ()))
    || ((Parse.term ::: (Scan.repeat (@{keyword "|"} |-- Parse.term))) >> SOME));

in

val _ =
  Outer_Syntax.command @{command_keyword code_reflect}
    "enrich runtime environment with generated code"
    (Parse.name -- Scan.optional (@{keyword "datatypes"} |-- Parse.!!!  (parse_datatype
      ::: Scan.repeat (@{keyword "and"} |-- parse_datatype))) []
    -- Scan.optional (@{keyword "functions"} |-- Parse.!!!  (Scan.repeat1 Parse.name)) []
    -- Scan.option (@{keyword "file"} |-- Parse.!!! Parse.name)
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
    val _ = #enterVal ML_Env.local_name_space (string, value);
    val _ = Theory.setup (Loaded_Values.map (insert (op =) string));
  in () end;

fun abort _ = error "Only value bindings allowed.";

val notifying_context : use_context =
 {tune_source = #tune_source ML_Env.local_context,
  name_space =
   {lookupVal    = #lookupVal ML_Env.local_name_space,
    lookupType   = #lookupType ML_Env.local_name_space,
    lookupFix    = #lookupFix ML_Env.local_name_space,
    lookupStruct = #lookupStruct ML_Env.local_name_space,
    lookupSig    = #lookupSig ML_Env.local_name_space,
    lookupFunct  = #lookupFunct ML_Env.local_name_space,
    enterVal     = notify_val,
    enterType    = abort,
    enterFix     = abort,
    enterStruct  = abort,
    enterSig     = abort,
    enterFunct   = abort,
    allVal       = #allVal ML_Env.local_name_space,
    allType      = #allType ML_Env.local_name_space,
    allFix       = #allFix ML_Env.local_name_space,
    allStruct    = #allStruct ML_Env.local_name_space,
    allSig       = #allSig ML_Env.local_name_space,
    allFunct     = #allFunct ML_Env.local_name_space},
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
    Code_Target.set_printings (Constant (const,
      [(target, SOME (Code_Printer.simple_const_syntax (0, (K o K o K o Code_Printer.str) ml_name)))]))
  #> tap (fn thy => Code_Target.produce_code (Proof_Context.init_global thy) false [const] target NONE structure_generated []));

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
