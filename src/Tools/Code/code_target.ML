(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for target language data.
*)

signature CODE_TARGET =
sig
  val cert_tyco: theory -> string -> string
  val read_tyco: theory -> string -> string
  val read_const_exprs: theory -> string list -> string list

  val export_code_for: theory -> Path.T option -> string -> int option -> string -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> unit
  val produce_code_for: theory -> string -> int option -> string -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> string * string option list
  val present_code_for: theory -> string -> int option -> string -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list * string list -> string
  val check_code_for: theory -> string -> bool -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> unit

  val export_code: theory -> string list
    -> (((string * string) * Path.T option) * Token.T list) list -> unit
  val produce_code: theory -> string list
    -> string -> int option -> string -> Token.T list -> string * string option list
  val present_code: theory -> string list -> (Code_Thingol.naming -> string list)
    -> string -> int option -> string -> Token.T list -> string
  val check_code: theory -> string list
    -> ((string * bool) * Token.T list) list -> unit

  val evaluator: theory -> string -> Code_Thingol.naming -> Code_Thingol.program
    -> string list -> ((string * class list) list * Code_Thingol.itype) * Code_Thingol.iterm
    -> string * string

  type serializer
  type literals = Code_Printer.literals
  val add_target: string * { serializer: serializer, literals: literals,
    check: { env_var: string, make_destination: Path.T -> Path.T, make_command: string -> string } }
    -> theory -> theory
  val extend_target: string *
      (string * (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program))
    -> theory -> theory
  val assert_target: theory -> string -> string
  val the_literals: theory -> string -> literals
  type serialization
  val parse_args: 'a parser -> Token.T list -> 'a
  val serialization: (int -> Path.T option -> 'a -> unit)
    -> (string list -> int -> 'a -> string * (string -> string option))
    -> 'a -> serialization
  val set_default_code_width: int -> theory -> theory

  val allow_abort: string -> theory -> theory
  type tyco_syntax = Code_Printer.tyco_syntax
  type const_syntax = Code_Printer.const_syntax
  val add_class_syntax: string -> class -> string option -> theory -> theory
  val add_instance_syntax: string -> class * string -> unit option -> theory -> theory
  val add_tyco_syntax: string -> string -> tyco_syntax option -> theory -> theory
  val add_const_syntax: string -> string -> const_syntax option -> theory -> theory
  val add_reserved: string -> string -> theory -> theory
  val add_include: string -> string * (string * string list) option -> theory -> theory

  val codegen_tool: string (*theory name*) -> string (*export_code expr*) -> unit

  val setup: theory -> theory
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Thingol;

type literals = Code_Printer.literals;
type tyco_syntax = Code_Printer.tyco_syntax;
type const_syntax = Code_Printer.const_syntax;


(** abstract nonsense **)

datatype destination = Export of Path.T option | Produce | Present of string list;
type serialization = int -> destination -> (string * (string -> string option)) option;

fun serialization output _ content width (Export some_path) =
      (output width some_path content; NONE)
  | serialization _ string content width Produce =
      string [] width content |> SOME
  | serialization _ string content width (Present stmt_names) =
     string stmt_names width content
     |> apfst (Pretty.output (SOME width) o Pretty.str)
     |> SOME;

fun export some_path f = (f (Export some_path); ());
fun produce f = the (f Produce);
fun present stmt_names f = fst (the (f (Present stmt_names)));


(** theory data **)

datatype symbol_syntax_data = Symbol_Syntax_Data of {
  class: string Symtab.table,
  instance: unit Symreltab.table,
  tyco: Code_Printer.tyco_syntax Symtab.table,
  const: Code_Printer.const_syntax Symtab.table
};

fun make_symbol_syntax_data ((class, instance), (tyco, const)) =
  Symbol_Syntax_Data { class = class, instance = instance, tyco = tyco, const = const };
fun map_symbol_syntax_data f (Symbol_Syntax_Data { class, instance, tyco, const }) =
  make_symbol_syntax_data (f ((class, instance), (tyco, const)));
fun merge_symbol_syntax_data
  (Symbol_Syntax_Data { class = class1, instance = instance1, tyco = tyco1, const = const1 },
    Symbol_Syntax_Data { class = class2, instance = instance2, tyco = tyco2, const = const2 }) =
  make_symbol_syntax_data (
    (Symtab.join (K snd) (class1, class2),
       Symreltab.join (K snd) (instance1, instance2)),
    (Symtab.join (K snd) (tyco1, tyco2),
       Symtab.join (K snd) (const1, const2))
  );

type serializer = Token.T list
  -> {
    labelled_name: string -> string,
    reserved_syms: string list,
    includes: (string * Pretty.T) list,
    module_alias: string -> string option,
    class_syntax: string -> string option,
    tyco_syntax: string -> Code_Printer.tyco_syntax option,
    const_syntax: string -> Code_Printer.activated_const_syntax option }
  -> Code_Thingol.program
  -> serialization;

datatype description = Fundamental of { serializer: serializer,
      literals: literals,
      check: { env_var: string, make_destination: Path.T -> Path.T,
        make_command: string -> string } }
  | Extension of string *
      (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program);

datatype target = Target of {
  serial: serial,
  description: description,
  reserved: string list,
  includes: (Pretty.T * string list) Symtab.table,
  module_alias: string Symtab.table,
  symbol_syntax: symbol_syntax_data
};

fun make_target ((serial, description), ((reserved, includes), (module_alias, symbol_syntax))) =
  Target { serial = serial, description = description, reserved = reserved,
    includes = includes, module_alias = module_alias, symbol_syntax = symbol_syntax };
fun map_target f ( Target { serial, description, reserved, includes, module_alias, symbol_syntax } ) =
  make_target (f ((serial, description), ((reserved, includes), (module_alias, symbol_syntax))));
fun merge_target strict target (Target { serial = serial1, description = description,
  reserved = reserved1, includes = includes1,
  module_alias = module_alias1, symbol_syntax = symbol_syntax1 },
    Target { serial = serial2, description = _,
      reserved = reserved2, includes = includes2,
      module_alias = module_alias2, symbol_syntax = symbol_syntax2 }) =
  if serial1 = serial2 orelse not strict then
    make_target ((serial1, description),
      ((merge (op =) (reserved1, reserved2), Symtab.join (K snd) (includes1, includes2)),
        (Symtab.join (K snd) (module_alias1, module_alias2),
          merge_symbol_syntax_data (symbol_syntax1, symbol_syntax2))
    ))
  else
    error ("Incompatible targets: " ^ quote target);

fun the_description (Target { description, ... }) = description;
fun the_reserved (Target { reserved, ... }) = reserved;
fun the_includes (Target { includes, ... }) = includes;
fun the_module_alias (Target { module_alias , ... }) = module_alias;
fun the_symbol_syntax (Target { symbol_syntax = Symbol_Syntax_Data x, ... }) = x;

structure Targets = Theory_Data
(
  type T = (target Symtab.table * string list) * int;
  val empty = ((Symtab.empty, []), 80);
  val extend = I;
  fun merge (((target1, exc1), width1), ((target2, exc2), width2)) : T =
    ((Symtab.join (merge_target true) (target1, target2),
      Library.merge (op =) (exc1, exc2)), Int.max (width1, width2));
);

val abort_allowed = snd o fst o Targets.get;

fun assert_target thy target = if Symtab.defined ((fst o fst) (Targets.get thy)) target
  then target
  else error ("Unknown code target language: " ^ quote target);

fun put_target (target, seri) thy =
  let
    val lookup_target = Symtab.lookup ((fst o fst) (Targets.get thy));
    val _ = case seri
     of Extension (super, _) => if is_some (lookup_target super) then ()
          else error ("Unknown code target language: " ^ quote super)
      | _ => ();
    val overwriting = case (Option.map the_description o lookup_target) target
     of NONE => false
      | SOME (Extension _) => true
      | SOME (Fundamental _) => (case seri
         of Extension _ => error ("Will not overwrite existing target " ^ quote target)
          | _ => true);
    val _ = if overwriting
      then warning ("Overwriting existing target " ^ quote target)
      else ();
  in
    thy
    |> (Targets.map o apfst o apfst o Symtab.update)
          (target, make_target ((serial (), seri), (([], Symtab.empty),
            (Symtab.empty, make_symbol_syntax_data ((Symtab.empty, Symreltab.empty),
              (Symtab.empty, Symtab.empty))))))
  end;

fun add_target (target, seri) = put_target (target, Fundamental seri);
fun extend_target (target, (super, modify)) =
  put_target (target, Extension (super, modify));

fun map_target_data target f thy =
  let
    val _ = assert_target thy target;
  in
    thy
    |> (Targets.map o apfst o apfst o Symtab.map_entry target o map_target) f
  end;

fun map_reserved target =
  map_target_data target o apsnd o apfst o apfst;
fun map_includes target =
  map_target_data target o apsnd o apfst o apsnd;
fun map_module_alias target =
  map_target_data target o apsnd o apsnd o apfst;
fun map_symbol_syntax target =
  map_target_data target o apsnd o apsnd o apsnd o map_symbol_syntax_data;

fun set_default_code_width k = (Targets.map o apsnd) (K k);


(** serializer usage **)

(* montage *)

fun the_fundamental thy =
  let
    val ((targets, _), _) = Targets.get thy;
    fun fundamental target = case Symtab.lookup targets target
     of SOME data => (case the_description data
         of Fundamental data => data
          | Extension (super, _) => fundamental super)
      | NONE => error ("Unknown code target language: " ^ quote target);
  in fundamental end;

fun the_literals thy = #literals o the_fundamental thy;

fun collapse_hierarchy thy =
  let
    val ((targets, _), _) = Targets.get thy;
    fun collapse target =
      let
        val data = case Symtab.lookup targets target
         of SOME data => data
          | NONE => error ("Unknown code target language: " ^ quote target);
      in case the_description data
       of Fundamental _ => (K I, data)
        | Extension (super, modify) => let
            val (modify', data') = collapse super
          in (fn naming => modify' naming #> modify naming, merge_target false target (data', data)) end
      end;
  in collapse end;

local

fun activate_target thy target =
  let
    val ((targets, abortable), default_width) = Targets.get thy;
    val (modify, data) = collapse_hierarchy thy target;
  in (default_width, abortable, data, modify) end;

fun activate_syntax lookup_name src_tab = Symtab.empty
  |> fold_map (fn thing_identifier => fn tab => case lookup_name thing_identifier
       of SOME name => (SOME name,
            Symtab.update_new (name, the (Symtab.lookup src_tab thing_identifier)) tab)
        | NONE => (NONE, tab)) (Symtab.keys src_tab)
  |>> map_filter I;

fun activate_const_syntax thy literals src_tab naming = (Symtab.empty, naming)
  |> fold_map (fn c => fn (tab, naming) =>
      case Code_Thingol.lookup_const naming c
       of SOME name => let
              val (syn, naming') = Code_Printer.activate_const_syntax thy
                literals c (the (Symtab.lookup src_tab c)) naming
            in (SOME name, (Symtab.update_new (name, syn) tab, naming')) end
        | NONE => (NONE, (tab, naming))) (Symtab.keys src_tab)
  |>> map_filter I;

fun activate_symbol_syntax thy literals naming
    class_syntax instance_syntax tyco_syntax const_syntax =
  let
    val (names_class, class_syntax') =
      activate_syntax (Code_Thingol.lookup_class naming) class_syntax;
    val names_inst = map_filter (Code_Thingol.lookup_instance naming)
      (Symreltab.keys instance_syntax);
    val (names_tyco, tyco_syntax') =
      activate_syntax (Code_Thingol.lookup_tyco naming) tyco_syntax;
    val (names_const, (const_syntax', _)) =
      activate_const_syntax thy literals const_syntax naming;
  in
    (names_class @ names_inst @ names_tyco @ names_const,
      (class_syntax', tyco_syntax', const_syntax'))
  end;

fun project_program thy abortable names_hidden names1 program2 =
  let
    val ctxt = Proof_Context.init_global thy;
    val names2 = subtract (op =) names_hidden names1;
    val program3 = Graph.restrict (not o member (op =) names_hidden) program2;
    val names4 = Graph.all_succs program3 names2;
    val empty_funs = filter_out (member (op =) abortable)
      (Code_Thingol.empty_funs program3);
    val _ =
      if null empty_funs then ()
      else error ("No code equations for " ^
        commas (map (Proof_Context.extern_const ctxt) empty_funs));
    val program4 = Graph.restrict (member (op =) names4) program3;
  in (names4, program4) end;

fun prepare_serializer thy abortable serializer literals reserved all_includes
    module_alias proto_class_syntax proto_instance_syntax proto_tyco_syntax proto_const_syntax
    module_name args naming proto_program names =
  let
    val (names_hidden, (class_syntax, tyco_syntax, const_syntax)) =
      activate_symbol_syntax thy literals naming
        proto_class_syntax proto_instance_syntax proto_tyco_syntax proto_const_syntax;
    val (names_all, program) = project_program thy abortable names_hidden names proto_program;
    fun select_include (name, (content, cs)) =
      if null cs orelse exists (fn c => case Code_Thingol.lookup_const naming c
       of SOME name => member (op =) names_all name
        | NONE => false) cs
      then SOME (name, content) else NONE;
    val includes = map_filter select_include (Symtab.dest all_includes);
  in
    (serializer args {
      labelled_name = Code_Thingol.labelled_name thy proto_program,
      reserved_syms = reserved,
      includes = includes,
      module_alias = if module_name = "" then Symtab.lookup module_alias else K (SOME module_name),
      class_syntax = Symtab.lookup class_syntax,
      tyco_syntax = Symtab.lookup tyco_syntax,
      const_syntax = Symtab.lookup const_syntax },
      program)
  end;

fun mount_serializer thy target some_width module_name args naming program names =
  let
    val (default_width, abortable, data, modify) = activate_target thy target;
    val serializer = case the_description data
     of Fundamental seri => #serializer seri;
    val reserved = the_reserved data;
    val module_alias = the_module_alias data
    val { class, instance, tyco, const } = the_symbol_syntax data;
    val literals = the_literals thy target;
    val (prepared_serializer, prepared_program) = prepare_serializer thy
      abortable serializer literals reserved (the_includes data) module_alias
        class instance tyco const module_name args
          naming (modify naming program) names
    val width = the_default default_width some_width;
  in (fn program => prepared_serializer program width, prepared_program) end;

fun invoke_serializer thy target some_width module_name args naming program names =
  let
    val (mounted_serializer, prepared_program) = mount_serializer thy
      target some_width module_name args naming program names;
  in mounted_serializer prepared_program end;

fun assert_module_name "" = error ("Empty module name not allowed.")
  | assert_module_name module_name = module_name;

in

fun export_code_for thy some_path target some_width module_name args =
  export some_path ooo invoke_serializer thy target some_width module_name args;

fun produce_code_for thy target some_width module_name args =
  let
    val serializer = invoke_serializer thy target some_width (assert_module_name module_name) args;
  in fn naming => fn program => fn names =>
    produce (serializer naming program names) |> apsnd (fn deresolve => map deresolve names)
  end;

fun present_code_for thy target some_width module_name args =
  let
    val serializer = invoke_serializer thy target some_width (assert_module_name module_name) args;
  in fn naming => fn program => fn (names, selects) =>
    present selects (serializer naming program names)
  end;

fun check_code_for thy target strict args naming program names_cs =
  let
    val module_name = "Generated_Code";
    val { env_var, make_destination, make_command } =
      (#check o the_fundamental thy) target;
    fun ext_check p =
      let
        val destination = make_destination p;
        val _ = export (SOME destination) (invoke_serializer thy target (SOME 80)
          module_name args naming program names_cs);
        val cmd = make_command module_name;
      in
        if Isabelle_System.bash ("cd " ^ File.shell_path p ^ " && " ^ cmd ^ " 2>&1") <> 0
        then error ("Code check failed for " ^ target ^ ": " ^ cmd)
        else ()
      end;
  in
    if getenv env_var = ""
    then if strict
      then error (env_var ^ " not set; cannot check code for " ^ target)
      else warning (env_var ^ " not set; skipped checking code for " ^ target)
    else Isabelle_System.with_tmp_dir "Code_Test" ext_check
  end;

fun evaluation mounted_serializer prepared_program consts ((vs, ty), t) =
  let
    val _ = if Code_Thingol.contains_dict_var t then
      error "Term to be evaluated contains free dictionaries" else ();
    val v' = singleton (Name.variant_list (map fst vs)) "a";
    val vs' = (v', []) :: vs;
    val ty' = Code_Thingol.fun_tyco `%% [ITyVar v', ty];
    val value_name = "Value.value.value"
    val program = prepared_program
      |> Graph.new_node (value_name,
          Code_Thingol.Fun (Term.dummy_patternN, (((vs', ty'), [(([IVar NONE], t), (NONE, true))]), NONE)))
      |> fold (curry (perhaps o try o Graph.add_edge) value_name) consts;
    val (program_code, deresolve) = produce (mounted_serializer program);
    val value_name' = the (deresolve value_name);
  in (program_code, value_name') end;

fun evaluator thy target naming program consts =
  let
    val (mounted_serializer, prepared_program) = mount_serializer thy
      target NONE "Generated_Code" [] naming program consts;
  in evaluation mounted_serializer prepared_program consts end;

end; (* local *)


(* code generation *)

fun transitivly_non_empty_funs thy naming program =
  let
    val cs = subtract (op =) (abort_allowed thy) (Code_Thingol.empty_funs program);
    val names = map_filter (Code_Thingol.lookup_const naming) cs;
  in subtract (op =) (Graph.all_preds program names) (Graph.keys program) end;

fun read_const_exprs thy cs =
  let
    val (cs1, cs2) = Code_Thingol.read_const_exprs thy cs;
    val (names2, (naming, program)) = Code_Thingol.consts_program thy true cs2;
    val names3 = transitivly_non_empty_funs thy naming program;
    val cs3 = map_filter (fn (c, name) =>
      if member (op =) names3 name then SOME c else NONE) (cs2 ~~ names2);
  in union (op =) cs3 cs1 end;

fun prep_destination "" = NONE
  | prep_destination "-" = NONE
  | prep_destination s = SOME (Path.explode s);

fun export_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
    val _ = map (fn (((target, module_name), some_path), args) =>
      export_code_for thy some_path target NONE module_name args naming program names_cs) seris;
  in () end;

fun export_code_cmd raw_cs seris thy = export_code thy (read_const_exprs thy raw_cs)
  ((map o apfst o apsnd) prep_destination seris);

fun produce_code thy cs target some_width some_module_name args =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
  in produce_code_for thy target some_width some_module_name args naming program names_cs end;

fun present_code thy cs names_stmt target some_width some_module_name args =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
  in present_code_for thy target some_width some_module_name args naming program (names_cs, names_stmt naming) end;

fun check_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
    val _ = map (fn ((target, strict), args) =>
      check_code_for thy target strict args naming program names_cs) seris;
  in () end;

fun check_code_cmd raw_cs seris thy = check_code thy (read_const_exprs thy raw_cs) seris;

local

val parse_const_terms = Scan.repeat1 Args.term
  >> (fn ts => fn thy => map (Code.check_const thy) ts);

fun parse_names category parse internalize lookup =
  Scan.lift (Args.parens (Args.$$$ category)) |-- Scan.repeat1 parse
  >> (fn xs => fn thy => fn naming => map_filter (lookup naming o internalize thy) xs);

val parse_consts = parse_names "consts" Args.term
  Code.check_const Code_Thingol.lookup_const ;

val parse_types = parse_names "types" (Scan.lift Args.name)
  Sign.intern_type Code_Thingol.lookup_tyco;

val parse_classes = parse_names "classes" (Scan.lift Args.name)
  Sign.intern_class Code_Thingol.lookup_class;

val parse_instances = parse_names "instances" (Scan.lift (Args.name --| Args.$$$ "::" -- Args.name))
  (fn thy => fn (raw_tyco, raw_class) => (Sign.intern_class thy raw_class, Sign.intern_type thy raw_tyco))
    Code_Thingol.lookup_instance;

in

val antiq_setup =
  Thy_Output.antiquotation @{binding code_stmts}
    (parse_const_terms --
      Scan.repeat (parse_consts || parse_types || parse_classes || parse_instances)
      -- Scan.lift (Args.parens (Args.name -- Scan.option Parse.int)))
    (fn {context = ctxt, ...} => fn ((mk_cs, mk_stmtss), (target, some_width)) =>
      let val thy = Proof_Context.theory_of ctxt in
        present_code thy (mk_cs thy)
          (fn naming => maps (fn f => f thy naming) mk_stmtss)
          target some_width "Example" []
      end);

end;


(** serializer configuration **)

(* data access *)

fun cert_class thy class =
  let
    val _ = AxClass.get_info thy class;
  in class end;

fun read_class thy = cert_class thy o Sign.intern_class thy;

fun cert_tyco thy tyco =
  let
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote tyco);
  in tyco end;

fun read_tyco thy = cert_tyco thy o Sign.intern_type thy;

fun cert_inst thy (class, tyco) =
  (cert_class thy class, cert_tyco thy tyco);

fun read_inst thy (raw_tyco, raw_class) =
  (read_class thy raw_class, read_tyco thy raw_tyco);

fun gen_add_syntax (mapp, upd, del) prep_x prep_syn target raw_x some_raw_syn thy =
  let
    val x = prep_x thy raw_x;
    val change = case some_raw_syn
     of SOME raw_syn => upd (x, prep_syn thy x raw_syn)
      | NONE => del x;
  in (map_symbol_syntax target o mapp) change thy end;

fun gen_add_class_syntax prep_class =
  gen_add_syntax (apfst o apfst, Symtab.update, Symtab.delete_safe) prep_class ((K o K) I);

fun gen_add_instance_syntax prep_inst =
  gen_add_syntax (apfst o apsnd, Symreltab.update, Symreltab.delete_safe) prep_inst ((K o K) I);

fun gen_add_tyco_syntax prep_tyco =
  gen_add_syntax (apsnd o apfst, Symtab.update, Symtab.delete_safe) prep_tyco
    (fn thy => fn tyco => fn syn => if fst syn <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syn);

fun gen_add_const_syntax prep_const =
  gen_add_syntax (apsnd o apsnd, Symtab.update, Symtab.delete_safe) prep_const
    (fn thy => fn c => fn syn =>
      if Code_Printer.requires_args syn > Code.args_number thy c
      then error ("Too many arguments in syntax for constant " ^ quote c)
      else syn);

fun add_reserved target sym thy =
  let
    val (_, data) = collapse_hierarchy thy target;
    val _ = if member (op =) (the_reserved data) sym
      then error ("Reserved symbol " ^ quote sym ^ " already declared")
      else ();
  in
    thy
    |> map_reserved target (insert (op =) sym)
  end;

fun gen_add_include read_const target args thy =
  let
    fun add (name, SOME (content, raw_cs)) incls =
          let
            val _ = if Symtab.defined incls name
              then warning ("Overwriting existing include " ^ name)
              else ();
            val cs = map (read_const thy) raw_cs;
          in Symtab.update (name, (Code_Printer.str content, cs)) incls end
      | add (name, NONE) incls = Symtab.delete name incls;
  in map_includes target (add args) thy end;

val add_include = gen_add_include (K I);
val add_include_cmd = gen_add_include Code.read_const;

fun add_module_alias target (thyname, "") =
      map_module_alias target (Symtab.delete thyname)
  | add_module_alias target (thyname, modlname) =
      let
        val xs = Long_Name.explode modlname;
        val xs' = map (Name.desymbolize true) xs;
      in if xs' = xs
        then map_module_alias target (Symtab.update (thyname, modlname))
        else error ("Invalid module name: " ^ quote modlname ^ "\n"
          ^ "perhaps try " ^ quote (Long_Name.implode xs'))
      end;

fun gen_allow_abort prep_const raw_c thy =
  let
    val c = prep_const thy raw_c;
  in thy |> (Targets.map o apfst o apsnd) (insert (op =) c) end;


(* concrete syntax *)

local

fun zip_list (x::xs) f g =
  f
  :|-- (fn y =>
    fold_map (fn x => g |-- f >> pair x) xs
    :|-- (fn xys => pair ((x, y) :: xys)));

fun process_multi_syntax parse_thing parse_syntax change =
  (Parse.and_list1 parse_thing
  :|-- (fn things => Scan.repeat1 (Parse.$$$ "(" |-- Parse.name --
        (zip_list things parse_syntax (Parse.$$$ "and")) --| Parse.$$$ ")")))
  >> (Toplevel.theory oo fold)
    (fn (target, syns) => fold (fn (raw_x, syn) => change target raw_x syn) syns);

in

val add_class_syntax = gen_add_class_syntax cert_class;
val add_instance_syntax = gen_add_instance_syntax cert_inst;
val add_tyco_syntax = gen_add_tyco_syntax cert_tyco;
val add_const_syntax = gen_add_const_syntax (K I);
val allow_abort = gen_allow_abort (K I);
val add_reserved = add_reserved;
val add_include = add_include;

val add_class_syntax_cmd = gen_add_class_syntax read_class;
val add_instance_syntax_cmd = gen_add_instance_syntax read_inst;
val add_tyco_syntax_cmd = gen_add_tyco_syntax read_tyco;
val add_const_syntax_cmd = gen_add_const_syntax Code.read_const;
val allow_abort_cmd = gen_allow_abort Code.read_const;

fun parse_args f args =
  case Scan.read Token.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(** Isar setup **)

val (inK, module_nameK, fileK, checkingK) = ("in", "module_name", "file", "checking");

val code_expr_argsP = Scan.optional (Parse.$$$ "(" |-- Args.parse --| Parse.$$$ ")") [];

val code_exprP =
  Scan.repeat1 Parse.term_group :|-- (fn raw_cs =>
    ((Parse.$$$ checkingK |-- Scan.repeat (Parse.name
      -- ((Parse.$$$ "?" |-- Scan.succeed false) || Scan.succeed true) -- code_expr_argsP))
      >> (fn seris => check_code_cmd raw_cs seris)
    || Scan.repeat (Parse.$$$ inK |-- Parse.name
       -- Scan.optional (Parse.$$$ module_nameK |-- Parse.name) ""
       -- Scan.optional (Parse.$$$ fileK |-- Parse.name) ""
       -- code_expr_argsP) >> (fn seris => export_code_cmd raw_cs seris)));

val _ = List.app Keyword.keyword [inK, module_nameK, fileK, checkingK];

val _ =
  Outer_Syntax.command "code_class" "define code syntax for class" Keyword.thy_decl (
    process_multi_syntax Parse.xname (Scan.option Parse.string)
    add_class_syntax_cmd);

val _ =
  Outer_Syntax.command "code_instance" "define code syntax for instance" Keyword.thy_decl (
    process_multi_syntax (Parse.xname --| Parse.$$$ "::" -- Parse.xname)
      (Scan.option (Parse.minus >> K ()))
    add_instance_syntax_cmd);

val _ =
  Outer_Syntax.command "code_type" "define code syntax for type constructor" Keyword.thy_decl (
    process_multi_syntax Parse.xname Code_Printer.parse_tyco_syntax
    add_tyco_syntax_cmd);

val _ =
  Outer_Syntax.command "code_const" "define code syntax for constant" Keyword.thy_decl (
    process_multi_syntax Parse.term_group Code_Printer.parse_const_syntax
    add_const_syntax_cmd);

val _ =
  Outer_Syntax.command "code_reserved" "declare words as reserved for target language"
    Keyword.thy_decl (
    Parse.name -- Scan.repeat1 Parse.name
    >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds)
  );

val _ =
  Outer_Syntax.command "code_include" "declare piece of code to be included in generated code"
    Keyword.thy_decl (
    Parse.name -- Parse.name -- (Parse.text :|-- (fn "-" => Scan.succeed NONE
      | s => Scan.optional (Parse.$$$ "attach" |-- Scan.repeat1 Parse.term) [] >> pair s >> SOME))
    >> (fn ((target, name), content_consts) =>
        (Toplevel.theory o add_include_cmd target) (name, content_consts))
  );

val _ =
  Outer_Syntax.command "code_modulename" "alias module to other name" Keyword.thy_decl (
    Parse.name -- Scan.repeat1 (Parse.name -- Parse.name)
    >> (fn (target, modlnames) => (Toplevel.theory o fold (add_module_alias target)) modlnames)
  );

val _ =
  Outer_Syntax.command "code_abort" "permit constant to be implemented as program abort"
    Keyword.thy_decl (
    Scan.repeat1 Parse.term_group >> (Toplevel.theory o fold allow_abort_cmd)
  );

val _ =
  Outer_Syntax.command "export_code" "generate executable code for constants"
    Keyword.diag (Parse.!!! code_exprP >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

end; (*local*)


(** external entrance point -- for codegen tool **)

fun codegen_tool thyname cmd_expr =
  let
    val thy = Thy_Info.get_theory thyname;
    val parse = Scan.read Token.stopper (Parse.!!! code_exprP) o
      (filter Token.is_proper o Outer_Syntax.scan Position.none);
  in case parse cmd_expr
   of SOME f => (writeln "Now generating code..."; f thy)
    | NONE => error ("Bad directive " ^ quote cmd_expr)
  end;


(** theory setup **)

val setup = antiq_setup;

end; (*struct*)
