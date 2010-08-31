(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for target language data.
*)

signature CODE_TARGET =
sig
  val cert_tyco: theory -> string -> string
  val read_tyco: theory -> string -> string

  val export_code_for: theory -> Path.T option -> string -> int option -> string option -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> unit
  val produce_code_for: theory -> string -> int option -> string option -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list * string list -> string * string option list
  val check_code_for: theory -> string -> bool -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> unit

  val export_code: theory -> string list
    -> (((string * string option) * Path.T option) * Token.T list) list -> unit
  val produce_code: theory -> string list -> (Code_Thingol.naming -> string list)
    -> string -> int option -> string option -> Token.T list -> string * string option list
  val check_code: theory -> string list
    -> ((string * bool) * Token.T list) list -> unit

  val shell_command: string (*theory name*) -> string (*export_code expr*) -> unit

  type serializer
  type literals = Code_Printer.literals
  val add_target: string * { serializer: serializer, literals: literals,
    check: { env_var: string, make_destination: Path.T -> Path.T,
      make_command: string -> string -> string } } -> theory -> theory
  val extend_target: string *
      (string * (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program))
    -> theory -> theory
  val assert_target: theory -> string -> string
  val the_literals: theory -> string -> literals
  type serialization
  val parse_args: 'a parser -> Token.T list -> 'a
  val serialization: (int -> Path.T option -> 'a -> unit)
    -> (int -> 'a -> string * string option list)
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
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Thingol;

type literals = Code_Printer.literals;
type tyco_syntax = Code_Printer.tyco_syntax;
type const_syntax = Code_Printer.const_syntax;


(** abstract nonsense **)

datatype destination = File of Path.T option | String of string list;
type serialization = int -> destination -> (string * string option list) option;

fun stmt_names_of_destination (String stmt_names) = stmt_names
  | stmt_names_of_destination _ = [];

fun serialization output _ content width (File some_path) = (output width some_path content; NONE)
  | serialization _ string content width (String _) = SOME (string width content);

fun file some_path f = (f (File some_path); ());
fun string stmt_names f = the (f (String stmt_names));


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

type serializer = Token.T list (*arguments*) -> {
    labelled_name: string -> string,
    reserved_syms: string list,
    includes: (string * Pretty.T) list,
    single_module: bool,
    module_alias: string -> string option,
    class_syntax: string -> string option,
    tyco_syntax: string -> Code_Printer.tyco_syntax option,
    const_syntax: string -> Code_Printer.activated_const_syntax option,
    program: Code_Thingol.program,
    names: string list,
    presentation_names: string list }
  -> serialization;

datatype description = Fundamental of { serializer: serializer,
      literals: literals,
      check: { env_var: string, make_destination: Path.T -> Path.T,
        make_command: string -> string -> string } }
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

local

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

fun invoke_serializer thy abortable serializer literals reserved abs_includes 
    module_alias class instance tyco const module_name args naming program2 (names1, presentation_names) width =
  let
    val (names_class, class') =
      activate_syntax (Code_Thingol.lookup_class naming) class;
    val names_inst = map_filter (Code_Thingol.lookup_instance naming)
      (Symreltab.keys instance);
    val (names_tyco, tyco') =
      activate_syntax (Code_Thingol.lookup_tyco naming) tyco;
    val (names_const, (const', _)) =
      activate_const_syntax thy literals const naming;
    val names_hidden = names_class @ names_inst @ names_tyco @ names_const;
    val names2 = subtract (op =) names_hidden names1;
    val program3 = Graph.subgraph (not o member (op =) names_hidden) program2;
    val names_all = Graph.all_succs program3 names2;
    val includes = abs_includes names_all;
    val program4 = Graph.subgraph (member (op =) names_all) program3;
    val empty_funs = filter_out (member (op =) abortable)
      (Code_Thingol.empty_funs program3);
    val _ = if null empty_funs then () else error ("No code equations for "
      ^ commas (map (Sign.extern_const thy) empty_funs));
  in
    serializer args {
      labelled_name = Code_Thingol.labelled_name thy program2,
      reserved_syms = reserved,
      includes = includes,
      single_module = is_some module_name,
      module_alias = if is_some module_name then K module_name else Symtab.lookup module_alias,
      class_syntax = Symtab.lookup class',
      tyco_syntax = Symtab.lookup tyco',
      const_syntax = Symtab.lookup const',
      program = program3,
      names = names1,
      presentation_names = presentation_names } width
  end;

fun mount_serializer thy target some_width raw_module_name args naming program names destination =
  let
    val ((targets, abortable), default_width) = Targets.get thy;
    fun collapse_hierarchy target =
      let
        val data = case Symtab.lookup targets target
         of SOME data => data
          | NONE => error ("Unknown code target language: " ^ quote target);
      in case the_description data
       of Fundamental _ => (I, data)
        | Extension (super, modify) => let
            val (modify', data') = collapse_hierarchy super
          in (modify' #> modify naming, merge_target false target (data', data)) end
      end;
    val (modify, data) = collapse_hierarchy target;
    val serializer = case the_description data
    of Fundamental seri => #serializer seri;
    val presentation_names = stmt_names_of_destination destination;
    val module_name = if null presentation_names
      then raw_module_name else SOME "Code";
    val reserved = the_reserved data;
    fun select_include names_all (name, (content, cs)) =
      if null cs then SOME (name, content)
      else if exists (fn c => case Code_Thingol.lookup_const naming c
       of SOME name => member (op =) names_all name
        | NONE => false) cs
      then SOME (name, content) else NONE;
    fun includes names_all = map_filter (select_include names_all)
      ((Symtab.dest o the_includes) data);
    val module_alias = the_module_alias data 
    val { class, instance, tyco, const } = the_symbol_syntax data;
    val literals = the_literals thy target;
    val width = the_default default_width some_width;
  in
    invoke_serializer thy abortable serializer literals reserved
      includes module_alias class instance tyco const module_name args
        naming (modify program) (names, presentation_names) width destination
  end;

in

fun export_code_for thy some_path target some_width some_module_name args naming program names =
  file some_path (mount_serializer thy target some_width some_module_name args naming program names);

fun produce_code_for thy target some_width some_module_name args naming program (names, selects) =
  string selects (mount_serializer thy target some_width some_module_name args naming program names);

fun check_code_for thy target strict args naming program names_cs =
  let
    val module_name = "Code_Test";
    val { env_var, make_destination, make_command } =
      (#check o the_fundamental thy) target;
    val env_param = getenv env_var;
    fun ext_check env_param p =
      let 
        val destination = make_destination p;
        val _ = file (SOME destination) (mount_serializer thy target (SOME 80)
          (SOME module_name) args naming program names_cs);
        val cmd = make_command env_param module_name;
      in if bash ("cd " ^ File.shell_path p ^ " && " ^ cmd ^ " 2>&1") <> 0
        then error ("Code check failed for " ^ target ^ ": " ^ cmd)
        else ()
      end;
  in if env_param = ""
    then if strict
      then error (env_var ^ " not set; cannot check code for " ^ target)
      else warning (env_var ^ " not set; skipped checking code for " ^ target)
    else Cache_IO.with_tmp_dir "Code_Test" (ext_check env_param)
  end;

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

fun produce_code thy cs names_stmt target some_width some_module_name args =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
  in produce_code_for thy target some_width some_module_name args naming program (names_cs, names_stmt naming) end;

fun check_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
    val _ = map (fn ((target, strict), args) =>
      check_code_for thy target strict args naming program names_cs) seris;
  in () end;

fun check_code_cmd raw_cs seris thy = check_code thy (read_const_exprs thy raw_cs) seris;


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

fun add_reserved target =
  let
    fun add sym syms = if member (op =) syms sym
      then error ("Reserved symbol " ^ quote sym ^ " already declared")
      else insert (op =) sym syms
  in map_reserved target o add end;

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

fun add_module_alias target (thyname, modlname) =
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
       -- Scan.option (Parse.$$$ module_nameK |-- Parse.name)
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

fun shell_command thyname cmd = Toplevel.program (fn _ =>
  (use_thy thyname; case Scan.read Token.stopper (Parse.!!! code_exprP)
    ((filter Token.is_proper o Outer_Syntax.scan Position.none) cmd)
   of SOME f => (writeln "Now generating code..."; f (Thy_Info.get_theory thyname))
    | NONE => error ("Bad directive " ^ quote cmd)))
  handle Runtime.TOPLEVEL_ERROR => OS.Process.exit OS.Process.failure;

end; (*local*)

end; (*struct*)
