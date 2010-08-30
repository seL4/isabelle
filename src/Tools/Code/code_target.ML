(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for serializers from intermediate language ("Thin-gol"
to target languages.
*)

signature CODE_TARGET =
sig
  val cert_tyco: theory -> string -> string
  val read_tyco: theory -> string -> string

  type serializer
  type literals = Code_Printer.literals
  val add_target: string * { serializer: serializer, literals: literals,
    check: { env_var: string, make_destination: Path.T -> Path.T,
      make_command: string -> string -> string } } -> theory -> theory
  val extend_target: string *
      (string * (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program))
    -> theory -> theory
  val assert_target: theory -> string -> string

  type destination
  type serialization
  val parse_args: 'a parser -> Token.T list -> 'a
  val stmt_names_of_destination: destination -> string list
  val mk_serialization: string -> (Path.T option -> 'a -> unit)
    -> ('a -> string * string option list)
    -> 'a -> serialization
  val serialize: theory -> string -> int option -> string option -> Token.T list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> serialization
  val serialize_custom: theory -> string * serializer -> string option
    -> Code_Thingol.naming -> Code_Thingol.program -> string list
    -> string * string option list
  val the_literals: theory -> string -> literals
  val export: serialization -> unit
  val file: Path.T -> serialization -> unit
  val string: string list -> serialization -> string
  val code_of: theory -> string -> int option -> string
    -> string list -> (Code_Thingol.naming -> string list) -> string
  val set_default_code_width: int -> theory -> theory
  val shell_command: string (*theory name*) -> string (*export_code expr*) -> unit

  val allow_abort: string -> theory -> theory
  type tyco_syntax = Code_Printer.tyco_syntax
  type const_syntax = Code_Printer.const_syntax
  val add_syntax_class: string -> class -> string option -> theory -> theory
  val add_syntax_inst: string -> class * string -> unit option -> theory -> theory
  val add_syntax_tyco: string -> string -> tyco_syntax option -> theory -> theory
  val add_syntax_const: string -> string -> const_syntax option -> theory -> theory
  val add_reserved: string -> string -> theory -> theory
  val add_include: string -> string * (string * string list) option -> theory -> theory
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Thingol;

type literals = Code_Printer.literals;
type tyco_syntax = Code_Printer.tyco_syntax;
type const_syntax = Code_Printer.const_syntax;


(** basics **)

datatype destination = Export | File of Path.T | String of string list;
type serialization = destination -> (string * string option list) option;

fun export f = (f Export; ());
fun file p f = (f (File p); ());
fun string stmts f = fst (the (f (String stmts)));

fun stmt_names_of_destination (String stmts) = stmts
  | stmt_names_of_destination _ = [];

fun mk_serialization target output _ code Export = (output NONE code ; NONE)
  | mk_serialization target output _ code (File file) = (output (SOME file) code; NONE)
  | mk_serialization target _ string code (String _) = SOME (string code);


(** theory data **)

datatype name_syntax_table = NameSyntaxTable of {
  class: string Symtab.table,
  instance: unit Symreltab.table,
  tyco: Code_Printer.tyco_syntax Symtab.table,
  const: Code_Printer.const_syntax Symtab.table
};

fun mk_name_syntax_table ((class, instance), (tyco, const)) =
  NameSyntaxTable { class = class, instance = instance, tyco = tyco, const = const };
fun map_name_syntax_table f (NameSyntaxTable { class, instance, tyco, const }) =
  mk_name_syntax_table (f ((class, instance), (tyco, const)));
fun merge_name_syntax_table
  (NameSyntaxTable { class = class1, instance = instance1, tyco = tyco1, const = const1 },
    NameSyntaxTable { class = class2, instance = instance2, tyco = tyco2, const = const2 }) =
  mk_name_syntax_table (
    (Symtab.join (K snd) (class1, class2),
       Symreltab.join (K snd) (instance1, instance2)),
    (Symtab.join (K snd) (tyco1, tyco2),
       Symtab.join (K snd) (const1, const2))
  );

type serializer =
  string option                         (*module name*)
  -> Token.T list                       (*arguments*)
  -> (string -> string)                 (*labelled_name*)
  -> string list                        (*reserved symbols*)
  -> (string * Pretty.T) list           (*includes*)
  -> (string -> string option)          (*module aliasses*)
  -> (string -> string option)          (*class syntax*)
  -> (string -> Code_Printer.tyco_syntax option)
  -> (string -> Code_Printer.activated_const_syntax option)
  -> ((Pretty.T -> string) * (Pretty.T -> unit))
  -> Code_Thingol.program
  -> (string list * string list)        (*selected statements*)
  -> serialization;

datatype description = Fundamental of { serializer: serializer,
      literals: Code_Printer.literals,
      check: { env_var: string, make_destination: Path.T -> Path.T,
        make_command: string -> string -> string } }
  | Extension of string *
      (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program);

datatype target = Target of {
  serial: serial,
  description: description,
  reserved: string list,
  includes: (Pretty.T * string list) Symtab.table,
  name_syntax_table: name_syntax_table,
  module_alias: string Symtab.table
};

fun make_target ((serial, description), ((reserved, includes), (name_syntax_table, module_alias))) =
  Target { serial = serial, description = description, reserved = reserved, 
    includes = includes, name_syntax_table = name_syntax_table, module_alias = module_alias };
fun map_target f ( Target { serial, description, reserved, includes, name_syntax_table, module_alias } ) =
  make_target (f ((serial, description), ((reserved, includes), (name_syntax_table, module_alias))));
fun merge_target strict target (Target { serial = serial1, description = description,
  reserved = reserved1, includes = includes1,
  name_syntax_table = name_syntax_table1, module_alias = module_alias1 },
    Target { serial = serial2, description = _,
      reserved = reserved2, includes = includes2,
      name_syntax_table = name_syntax_table2, module_alias = module_alias2 }) =
  if serial1 = serial2 orelse not strict then
    make_target ((serial1, description),
      ((merge (op =) (reserved1, reserved2), Symtab.join (K snd) (includes1, includes2)),
        (merge_name_syntax_table (name_syntax_table1, name_syntax_table2),
          Symtab.join (K snd) (module_alias1, module_alias2))
    ))
  else
    error ("Incompatible targets: " ^ quote target);

fun the_description (Target { description, ... }) = description;
fun the_reserved (Target { reserved, ... }) = reserved;
fun the_includes (Target { includes, ... }) = includes;
fun the_name_syntax (Target { name_syntax_table = NameSyntaxTable x, ... }) = x;
fun the_module_alias (Target { module_alias , ... }) = module_alias;

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
            (mk_name_syntax_table ((Symtab.empty, Symreltab.empty),
              (Symtab.empty, Symtab.empty)), Symtab.empty))))
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
fun map_name_syntax target =
  map_target_data target o apsnd o apsnd o apfst o map_name_syntax_table;
fun map_module_alias target =
  map_target_data target o apsnd o apsnd o apsnd;

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
    module_alias class instance tyco const module_name width args naming program2 (names1, presentation_names) =
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
    serializer module_name args (Code_Thingol.labelled_name thy program2) reserved includes
      (if is_some module_name then K module_name else Symtab.lookup module_alias)
      (Symtab.lookup class') (Symtab.lookup tyco') (Symtab.lookup const')
      (Code_Printer.string_of_pretty width, Code_Printer.writeln_pretty width)
      program4 (names1, presentation_names)
  end;

fun mount_serializer thy alt_serializer target some_width raw_module_name args naming program names destination =
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
    val serializer = the_default (case the_description data
     of Fundamental seri => #serializer seri) alt_serializer;
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
    val { class, instance, tyco, const } = the_name_syntax data;
    val literals = the_literals thy target;
    val width = the_default default_width some_width;
  in
    invoke_serializer thy abortable serializer literals reserved
      includes module_alias class instance tyco const module_name width args
        naming (modify program) (names, presentation_names) destination
  end;

in

fun serialize thy = mount_serializer thy NONE;

fun check thy names_cs naming program target strict args =
  let
    val module_name = "Code_Test";
    val { env_var, make_destination, make_command } =
      (#check o the_fundamental thy) target;
    val env_param = getenv env_var;
    fun ext_check env_param p =
      let 
        val destination = make_destination p;
        val _ = file destination (serialize thy target (SOME 80)
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

fun serialize_custom thy (target_name, seri) module_name naming program names =
  mount_serializer thy (SOME seri) target_name NONE module_name [] naming program names (String [])
  |> the;

end; (* local *)


(* code presentation *)

fun code_of thy target some_width module_name cs names_stmt =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
  in
    string (names_stmt naming)
      (serialize thy target some_width (SOME module_name) [] naming program names_cs)
  end;


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

fun export_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
    fun mk_seri_dest dest = if dest = "" orelse dest = "-" then export
      else file (Path.explode dest);
    val _ = map (fn (((target, module), dest), args) =>
      (mk_seri_dest dest (serialize thy target NONE module args naming program names_cs))) seris;
  in () end;

fun export_code_cmd raw_cs seris thy = export_code thy (read_const_exprs thy raw_cs) seris;

fun check_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs;
    val _ = map (fn ((target, strict), args) => check thy names_cs naming program
      target strict args) seris;
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
  in (map_name_syntax target o mapp) change thy end;

fun gen_add_syntax_class prep_class =
  gen_add_syntax (apfst o apfst, Symtab.update, Symtab.delete_safe) prep_class ((K o K) I);

fun gen_add_syntax_inst prep_inst =
  gen_add_syntax (apfst o apsnd, Symreltab.update, Symreltab.delete_safe) prep_inst ((K o K) I);

fun gen_add_syntax_tyco prep_tyco =
  gen_add_syntax (apsnd o apfst, Symtab.update, Symtab.delete_safe) prep_tyco
    (fn thy => fn tyco => fn syn => if fst syn <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syn);

fun gen_add_syntax_const prep_const =
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

val add_syntax_class = gen_add_syntax_class cert_class;
val add_syntax_inst = gen_add_syntax_inst cert_inst;
val add_syntax_tyco = gen_add_syntax_tyco cert_tyco;
val add_syntax_const = gen_add_syntax_const (K I);
val allow_abort = gen_allow_abort (K I);
val add_reserved = add_reserved;
val add_include = add_include;

val add_syntax_class_cmd = gen_add_syntax_class read_class;
val add_syntax_inst_cmd = gen_add_syntax_inst read_inst;
val add_syntax_tyco_cmd = gen_add_syntax_tyco read_tyco;
val add_syntax_const_cmd = gen_add_syntax_const Code.read_const;
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
    add_syntax_class_cmd);

val _ =
  Outer_Syntax.command "code_instance" "define code syntax for instance" Keyword.thy_decl (
    process_multi_syntax (Parse.xname --| Parse.$$$ "::" -- Parse.xname)
      (Scan.option (Parse.minus >> K ()))
    add_syntax_inst_cmd);

val _ =
  Outer_Syntax.command "code_type" "define code syntax for type constructor" Keyword.thy_decl (
    process_multi_syntax Parse.xname Code_Printer.parse_tyco_syntax
    add_syntax_tyco_cmd);

val _ =
  Outer_Syntax.command "code_const" "define code syntax for constant" Keyword.thy_decl (
    process_multi_syntax Parse.term_group Code_Printer.parse_const_syntax
    add_syntax_const_cmd);

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
