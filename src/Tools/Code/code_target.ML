(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for target language data.
*)

signature CODE_TARGET =
sig
  val cert_tyco: theory -> string -> string
  val read_tyco: theory -> string -> string

  val export_code_for: theory -> Path.T option -> string -> int option -> string -> Token.T list
    -> Code_Thingol.program -> Code_Symbol.T list -> unit
  val produce_code_for: theory -> string -> int option -> string -> Token.T list
    -> Code_Thingol.program -> Code_Symbol.T list -> (string * string) list * string option list
  val present_code_for: theory -> string -> int option -> string -> Token.T list
    -> Code_Thingol.program -> Code_Symbol.T list * Code_Symbol.T list -> string
  val check_code_for: theory -> string -> bool -> Token.T list
    -> Code_Thingol.program -> Code_Symbol.T list -> unit

  val export_code: theory -> string list
    -> (((string * string) * Path.T option) * Token.T list) list -> unit
  val produce_code: theory -> string list
    -> string -> int option -> string -> Token.T list -> (string * string) list * string option list
  val present_code: theory -> string list -> Code_Symbol.T list
    -> string -> int option -> string -> Token.T list -> string
  val check_code: theory -> string list
    -> ((string * bool) * Token.T list) list -> unit

  val generatedN: string
  val evaluator: theory -> string -> Code_Thingol.program
    -> Code_Symbol.T list -> ((string * class list) list * Code_Thingol.itype) * Code_Thingol.iterm
    -> (string * string) list * string

  type serializer
  type literals = Code_Printer.literals
  val add_target: string * { serializer: serializer, literals: literals,
    check: { env_var: string, make_destination: Path.T -> Path.T, make_command: string -> string } }
    -> theory -> theory
  val extend_target: string *
      (string * (Code_Thingol.program -> Code_Thingol.program))
    -> theory -> theory
  val assert_target: theory -> string -> string
  val the_literals: theory -> string -> literals
  type serialization
  val parse_args: 'a parser -> Token.T list -> 'a
  val serialization: (int -> Path.T option -> 'a -> unit)
    -> (Code_Symbol.T list -> int -> 'a -> (string * string) list * (Code_Symbol.T -> string option))
    -> 'a -> serialization
  val set_default_code_width: int -> theory -> theory

  type ('a, 'b, 'c, 'd, 'e, 'f) symbol_attr_decl
  type identifier_data
  val set_identifiers: (string, string, string, string, string, string) symbol_attr_decl
    -> theory -> theory
  type raw_const_syntax = Code_Printer.raw_const_syntax
  type tyco_syntax = Code_Printer.tyco_syntax
  val set_printings: (raw_const_syntax, tyco_syntax, string, unit, unit, (string * string list)) symbol_attr_decl
    -> theory -> theory
  val add_const_syntax: string -> string -> raw_const_syntax option -> theory -> theory
  val add_tyco_syntax: string -> string -> tyco_syntax option -> theory -> theory
  val add_class_syntax: string -> class -> string option -> theory -> theory
  val add_instance_syntax: string -> class * string -> unit option -> theory -> theory
  val add_reserved: string -> string -> theory -> theory
  val add_include: string -> string * (string * string list) option -> theory -> theory

  val codegen_tool: string (*theory name*) -> string (*export_code expr*) -> unit

  val setup: theory -> theory
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;

type literals = Code_Printer.literals;
type ('a, 'b, 'c, 'd, 'e, 'f) symbol_attr_decl =
  (string * (string * 'a option) list, string * (string * 'b option) list,
    class * (string * 'c option) list, (class * class) * (string * 'd option) list,
    (class * string) * (string * 'e option) list,
    string * (string * 'f option) list) Code_Symbol.attr;
type identifier_data = (string, string, string, string, string, string) Code_Symbol.data;

type tyco_syntax = Code_Printer.tyco_syntax;
type raw_const_syntax = Code_Printer.raw_const_syntax;


(** checking and parsing of symbols **)

fun cert_const thy const =
  let
    val _ = if Sign.declared_const thy const then ()
      else error ("No such constant: " ^ quote const);
  in const end;

fun cert_tyco thy tyco =
  let
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote tyco);
  in tyco end;

fun read_tyco thy = #1 o dest_Type
  o Proof_Context.read_type_name_proper (Proof_Context.init_global thy) true;

fun cert_class thy class =
  let
    val _ = Axclass.get_info thy class;
  in class end;

fun read_class thy = Proof_Context.read_class (Proof_Context.init_global thy);

val parse_classrel_ident = Parse.class --| @{keyword "<"} -- Parse.class;

fun cert_inst thy (class, tyco) =
  (cert_class thy class, cert_tyco thy tyco);

fun read_inst thy (raw_tyco, raw_class) =
  (read_tyco thy raw_tyco, read_class thy raw_class);

val parse_inst_ident = Parse.xname --| @{keyword "::"} -- Parse.class;

fun cert_syms thy =
  Code_Symbol.map_attr (apfst (cert_const thy)) (apfst (cert_tyco thy))
    (apfst (cert_class thy)) ((apfst o pairself) (cert_class thy)) (apfst (cert_inst thy)) I;

fun read_syms thy =
  Code_Symbol.map_attr (apfst (Code.read_const thy)) (apfst (read_tyco thy))
    (apfst (read_class thy)) ((apfst o pairself) (read_class thy)) (apfst (read_inst thy)) I;

fun check_name is_module s =
  let
    val _ = if s = "" then error "Bad empty code name" else ();
    val xs = Long_Name.explode s;
    val xs' = if is_module
        then map (Name.desymbolize true) xs
      else if length xs < 2
        then error ("Bad code name without module component: " ^ quote s)
      else
        let
          val (ys, y) = split_last xs;
          val ys' = map (Name.desymbolize true) ys;
          val y' = Name.desymbolize false y;
        in ys' @ [y'] end;
  in if xs' = xs
    then s
    else error ("Invalid code name: " ^ quote s ^ "\n"
      ^ "better try " ^ quote (Long_Name.implode xs'))
  end;


(** serializations and serializer **)

(* serialization: abstract nonsense to cover different destinies for generated code *)

datatype destination = Export of Path.T option | Produce | Present of Code_Symbol.T list;
type serialization = int -> destination -> ((string * string) list * (Code_Symbol.T -> string option)) option;

fun serialization output _ content width (Export some_path) =
      (output width some_path content; NONE)
  | serialization _ string content width Produce =
      string [] width content |> SOME
  | serialization _ string content width (Present syms) =
     string syms width content
     |> (apfst o map o apsnd) (Pretty.output (SOME width) o Pretty.str)
     |> SOME;

fun export some_path f = (f (Export some_path); ());
fun produce f = the (f Produce);
fun present syms f = space_implode "\n\n" (map snd (fst (the (f (Present syms)))));


(* serializers: functions producing serializations *)

type serializer = Token.T list
  -> Proof.context
  -> {
    module_name: string,
    reserved_syms: string list,
    identifiers: identifier_data,
    includes: (string * Pretty.T) list,
    class_syntax: string -> string option,
    tyco_syntax: string -> Code_Printer.tyco_syntax option,
    const_syntax: string -> Code_Printer.const_syntax option }
  -> Code_Thingol.program
  -> serialization;

datatype description =
    Fundamental of { serializer: serializer,
      literals: literals,
      check: { env_var: string, make_destination: Path.T -> Path.T,
        make_command: string -> string } }
  | Extension of string *
      (Code_Thingol.program -> Code_Thingol.program);


(** theory data **)

datatype target = Target of {
  serial: serial,
  description: description,
  reserved: string list,
  identifiers: identifier_data,
  printings: (Code_Printer.const_syntax, Code_Printer.tyco_syntax, string, unit, unit,
    (Pretty.T * string list)) Code_Symbol.data
};

fun make_target ((serial, description), (reserved, (identifiers, printings))) =
  Target { serial = serial, description = description, reserved = reserved,
    identifiers = identifiers, printings = printings };
fun map_target f (Target { serial, description, reserved, identifiers, printings }) =
  make_target (f ((serial, description), (reserved, (identifiers, printings))));
fun merge_target strict target (Target { serial = serial1, description = description,
  reserved = reserved1, identifiers = identifiers1, printings = printings1 },
    Target { serial = serial2, description = _,
      reserved = reserved2, identifiers = identifiers2, printings = printings2 }) =
  if serial1 = serial2 orelse not strict then
    make_target ((serial1, description), (merge (op =) (reserved1, reserved2),
      (Code_Symbol.merge_data (identifiers1, identifiers2),
        Code_Symbol.merge_data (printings1, printings2))))
  else
    error ("Incompatible targets: " ^ quote target);

fun the_description (Target { description, ... }) = description;
fun the_reserved (Target { reserved, ... }) = reserved;
fun the_identifiers (Target { identifiers , ... }) = identifiers;
fun the_printings (Target { printings, ... }) = printings;

structure Targets = Theory_Data
(
  type T = target Symtab.table * int;
  val empty = (Symtab.empty, 80);
  val extend = I;
  fun merge ((target1, width1), (target2, width2)) : T =
    (Symtab.join (merge_target true) (target1, target2), Int.max (width1, width2));
);

fun assert_target thy target = if Symtab.defined (fst (Targets.get thy)) target
  then target
  else error ("Unknown code target language: " ^ quote target);

fun put_target (target, seri) thy =
  let
    val lookup_target = Symtab.lookup (fst (Targets.get thy));
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
    |> (Targets.map o apfst o Symtab.update)
        (target, make_target ((serial (), seri),
          ([], (Code_Symbol.empty_data, Code_Symbol.empty_data))))
  end;

fun add_target (target, seri) = put_target (target, Fundamental seri);
fun extend_target (target, (super, modify)) =
  put_target (target, Extension (super, modify));

fun map_target_data target f thy =
  let
    val _ = assert_target thy target;
  in
    thy
    |> (Targets.map o apfst o Symtab.map_entry target o map_target o apsnd) f
  end;

fun map_reserved target =
  map_target_data target o apfst;
fun map_identifiers target =
  map_target_data target o apsnd o apfst;
fun map_printings target =
  map_target_data target o apsnd o apsnd;

fun set_default_code_width k = (Targets.map o apsnd) (K k);


(** serializer usage **)

(* montage *)

fun the_fundamental thy =
  let
    val (targets, _) = Targets.get thy;
    fun fundamental target = case Symtab.lookup targets target
     of SOME data => (case the_description data
         of Fundamental data => data
          | Extension (super, _) => fundamental super)
      | NONE => error ("Unknown code target language: " ^ quote target);
  in fundamental end;

fun the_literals thy = #literals o the_fundamental thy;

fun collapse_hierarchy thy =
  let
    val (targets, _) = Targets.get thy;
    fun collapse target =
      let
        val data = case Symtab.lookup targets target
         of SOME data => data
          | NONE => error ("Unknown code target language: " ^ quote target);
      in case the_description data
       of Fundamental _ => (I, data)
        | Extension (super, modify) => let
            val (modify', data') = collapse super
          in (modify' #> modify, merge_target false target (data', data)) end
      end;
  in collapse end;

local

fun activate_target thy target =
  let
    val (_, default_width) = Targets.get thy;
    val (modify, data) = collapse_hierarchy thy target;
  in (default_width, data, modify) end;

fun project_program thy syms_hidden syms1 program2 =
  let
    val ctxt = Proof_Context.init_global thy;
    val syms2 = subtract (op =) syms_hidden syms1;
    val program3 = Code_Symbol.Graph.restrict (not o member (op =) syms_hidden) program2;
    val syms4 = Code_Symbol.Graph.all_succs program3 syms2;
    val unimplemented = Code_Thingol.unimplemented program3;
    val _ =
      if null unimplemented then ()
      else error ("No code equations for " ^
        commas (map (Proof_Context.extern_const ctxt) unimplemented));
    val program4 = Code_Symbol.Graph.restrict (member (op =) syms4) program3;
  in (syms4, program4) end;

fun prepare_serializer thy (serializer : serializer) reserved identifiers
    printings module_name args proto_program syms =
  let
    val syms_hidden = Code_Symbol.symbols_of printings;
    val (syms_all, program) = project_program thy syms_hidden syms proto_program;
    fun select_include (name, (content, cs)) =
      if null cs orelse exists (fn c => member (op =) syms_all (Constant c)) cs
      then SOME (name, content) else NONE;
    val includes = map_filter select_include (Code_Symbol.dest_module_data printings);
  in
    (serializer args (Proof_Context.init_global thy) {
      module_name = module_name,
      reserved_syms = reserved,
      identifiers = identifiers,
      includes = includes,
      const_syntax = Code_Symbol.lookup_constant_data printings,
      tyco_syntax = Code_Symbol.lookup_type_constructor_data printings,
      class_syntax = Code_Symbol.lookup_type_class_data printings },
      program)
  end;

fun mount_serializer thy target some_width module_name args program syms =
  let
    val (default_width, data, modify) = activate_target thy target;
    val serializer = case the_description data
     of Fundamental seri => #serializer seri;
    val (prepared_serializer, prepared_program) =
      prepare_serializer thy serializer
        (the_reserved data) (the_identifiers data) (the_printings data)
        module_name args (modify program) syms
    val width = the_default default_width some_width;
  in (fn program => prepared_serializer program width, prepared_program) end;

fun invoke_serializer thy target some_width module_name args program syms =
  let
    val check = if module_name = "" then I else check_name true;
    val (mounted_serializer, prepared_program) = mount_serializer thy
      target some_width (check module_name) args program syms;
  in mounted_serializer prepared_program end;

fun assert_module_name "" = error "Empty module name not allowed here"
  | assert_module_name module_name = module_name;

fun using_master_directory thy =
  Option.map (Path.append (File.pwd ()) o Path.append (Thy_Load.master_directory thy));

in

val generatedN = "Generated_Code";

fun export_code_for thy some_path target some_width module_name args =
  export (using_master_directory thy some_path)
  oo invoke_serializer thy target some_width module_name args;

fun produce_code_for thy target some_width module_name args =
  let
    val serializer = invoke_serializer thy target some_width (assert_module_name module_name) args;
  in fn program => fn syms =>
    produce (serializer program syms) |> apsnd (fn deresolve => map deresolve syms)
  end;

fun present_code_for thy target some_width module_name args =
  let
    val serializer = invoke_serializer thy target some_width (assert_module_name module_name) args;
  in fn program => fn (syms, selects) =>
    present selects (serializer program syms)
  end;

fun check_code_for thy target strict args program syms =
  let
    val { env_var, make_destination, make_command } =
      (#check o the_fundamental thy) target;
    fun ext_check p =
      let
        val destination = make_destination p;
        val _ = export (SOME destination) (invoke_serializer thy target (SOME 80)
          generatedN args program syms);
        val cmd = make_command generatedN;
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

fun evaluation mounted_serializer prepared_program syms ((vs, ty), t) =
  let
    val _ = if Code_Thingol.contains_dict_var t then
      error "Term to be evaluated contains free dictionaries" else ();
    val v' = singleton (Name.variant_list (map fst vs)) "a";
    val vs' = (v', []) :: vs;
    val ty' = ITyVar v' `-> ty;
    val program = prepared_program
      |> Code_Symbol.Graph.new_node (Code_Symbol.value,
          Code_Thingol.Fun (((vs', ty'), [(([IVar NONE], t), (NONE, true))]), NONE))
      |> fold (curry (perhaps o try o
          Code_Symbol.Graph.add_edge) Code_Symbol.value) syms;
    val (program_code, deresolve) = produce (mounted_serializer program);
    val value_name = the (deresolve Code_Symbol.value);
  in (program_code, value_name) end;

fun evaluator thy target program syms =
  let
    val (mounted_serializer, prepared_program) =
      mount_serializer thy target NONE generatedN [] program syms;
  in evaluation mounted_serializer prepared_program syms end;

end; (* local *)


(* code generation *)

fun prep_destination "" = NONE
  | prep_destination s = SOME (Path.explode s);

fun export_code thy cs seris =
  let
    val program = Code_Thingol.consts_program thy cs;
    val _ = map (fn (((target, module_name), some_path), args) =>
      export_code_for thy some_path target NONE module_name args program (map Constant cs)) seris;
  in () end;

fun export_code_cmd raw_cs seris thy = export_code thy
  (Code_Thingol.read_const_exprs thy raw_cs)
  ((map o apfst o apsnd) prep_destination seris);

fun produce_code thy cs target some_width some_module_name args =
  let
    val program = Code_Thingol.consts_program thy cs;
  in produce_code_for thy target some_width some_module_name args program (map Constant cs) end;

fun present_code thy cs syms target some_width some_module_name args =
  let
    val program = Code_Thingol.consts_program thy cs;
  in present_code_for thy target some_width some_module_name args program (map Constant cs, syms) end;

fun check_code thy cs seris =
  let
    val program = Code_Thingol.consts_program thy cs;
    val _ = map (fn ((target, strict), args) =>
      check_code_for thy target strict args program (map Constant cs)) seris;
  in () end;

fun check_code_cmd raw_cs seris thy = check_code thy
  (Code_Thingol.read_const_exprs thy raw_cs) seris;

local

val parse_const_terms = Scan.repeat1 Args.term
  >> (fn ts => fn thy => map (Code.check_const thy) ts);

fun parse_names category parse internalize mark_symbol =
  Scan.lift (Args.parens (Args.$$$ category)) |-- Scan.repeat1 parse
  >> (fn xs => fn thy => map (mark_symbol o internalize thy) xs);

val parse_consts = parse_names "consts" Args.term
  Code.check_const Constant;

val parse_types = parse_names "types" (Scan.lift Args.name)
  Sign.intern_type Type_Constructor;

val parse_classes = parse_names "classes" (Scan.lift Args.name)
  Sign.intern_class Type_Class;

val parse_instances = parse_names "instances" (Scan.lift (Args.name --| Args.$$$ "::" -- Args.name))
  (fn thy => fn (raw_tyco, raw_class) => (Sign.intern_class thy raw_tyco, Sign.intern_type thy raw_class))
    Class_Instance;

in

val antiq_setup =
  Thy_Output.antiquotation @{binding code_stmts}
    (parse_const_terms --
      Scan.repeat (parse_consts || parse_types || parse_classes || parse_instances)
      -- Scan.lift (Args.parens (Args.name -- Scan.option Parse.int)))
    (fn {context = ctxt, ...} => fn ((mk_cs, mk_stmtss), (target, some_width)) =>
      let val thy = Proof_Context.theory_of ctxt in
        present_code thy (mk_cs thy)
          (maps (fn f => f thy) mk_stmtss)
          target some_width "Example" []
      end);

end;


(** serializer configuration **)

(* reserved symbol names *)

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


(* checking of syntax *)

fun check_const_syntax thy target c syn =
  if Code_Printer.requires_args syn > Code.args_number thy c
  then error ("Too many arguments in syntax for constant " ^ quote c)
  else Code_Printer.prep_const_syntax thy (the_literals thy target) c syn;

fun check_tyco_syntax thy target tyco syn =
  if fst syn <> Sign.arity_number thy tyco
  then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
  else syn;


(* custom symbol names *)

fun arrange_name_decls x =
  let
    fun arrange is_module (sym, target_names) = map (fn (target, some_name) =>
      (target, (sym, Option.map (check_name is_module) some_name))) target_names;
  in
    Code_Symbol.maps_attr' (arrange false) (arrange false) (arrange false)
      (arrange false) (arrange false) (arrange true) x
  end;

fun cert_name_decls thy = cert_syms thy #> arrange_name_decls;

fun read_name_decls thy = read_syms thy #> arrange_name_decls;

fun set_identifier (target, sym_name) = map_identifiers target (Code_Symbol.set_data sym_name);

fun gen_set_identifiers prep_name_decl raw_name_decls thy =
  fold set_identifier (prep_name_decl thy raw_name_decls) thy;

val set_identifiers = gen_set_identifiers cert_name_decls;
val set_identifiers_cmd = gen_set_identifiers read_name_decls;

fun add_module_alias_cmd target aliasses thy =
  let
    val _ = legacy_feature "prefer \"code_identifier\" over \"code_modulename\"";
  in
    fold (fn (sym, name) => set_identifier
      (target, Code_Symbol.Module (sym, if name = "" then NONE else SOME (check_name true name))))
      aliasses thy
  end;


(* custom printings *)

fun arrange_printings prep_const thy =
  let
    fun arrange check (sym, target_syns) =
      map (fn (target, some_syn) => (target, (sym, Option.map (check thy target sym) some_syn))) target_syns;
  in
    Code_Symbol.maps_attr'
      (arrange check_const_syntax) (arrange check_tyco_syntax)
        (arrange ((K o K o K) I)) (arrange ((K o K o K) I)) (arrange ((K o K o K) I))
        (arrange (fn thy => fn _ => fn _ => fn (raw_content, raw_cs) =>
          (Code_Printer.str raw_content, map (prep_const thy) raw_cs)))
  end;

fun cert_printings thy = cert_syms thy #> arrange_printings cert_const thy;

fun read_printings thy = read_syms thy #> arrange_printings Code.read_const thy;

fun set_printing (target, sym_syn) = map_printings target (Code_Symbol.set_data sym_syn);

fun gen_set_printings prep_print_decl raw_print_decls thy =
  fold set_printing (prep_print_decl thy raw_print_decls) thy;

val set_printings = gen_set_printings cert_printings;
val set_printings_cmd = gen_set_printings read_printings;

fun gen_add_syntax Symbol prep_x prep_syn target raw_x some_raw_syn thy =
  let
    val _ = legacy_feature "prefer \"code_printing\" for custom serialisations"
    val x = prep_x thy raw_x;
  in set_printing (target, Symbol (x, Option.map (prep_syn thy target x) some_raw_syn)) thy end;

fun gen_add_const_syntax prep_const =
  gen_add_syntax Constant prep_const check_const_syntax;

fun gen_add_tyco_syntax prep_tyco =
  gen_add_syntax Type_Constructor prep_tyco check_tyco_syntax;

fun gen_add_class_syntax prep_class =
  gen_add_syntax Type_Class prep_class ((K o K o K) I);

fun gen_add_instance_syntax prep_inst =
  gen_add_syntax Class_Instance prep_inst ((K o K o K) I);

fun gen_add_include prep_const target (name, some_content) thy =
  gen_add_syntax Module (K I)
    (fn thy => fn _ => fn _ => fn (raw_content, raw_cs) => (Code_Printer.str raw_content, map (prep_const thy) raw_cs))
    target name some_content thy;


(* concrete syntax *)

local

fun zip_list (x :: xs) f g =
  f
  :|-- (fn y =>
    fold_map (fn x => g |-- f >> pair x) xs
    :|-- (fn xys => pair ((x, y) :: xys)));

fun process_multi_syntax parse_thing parse_syntax change =
  (Parse.and_list1 parse_thing
  :|-- (fn things => Scan.repeat1 (@{keyword "("} |-- Parse.name --
        (zip_list things (Scan.option parse_syntax) @{keyword "and"}) --| @{keyword ")"})))
  >> (Toplevel.theory oo fold)
    (fn (target, syns) => fold (fn (raw_x, syn) => change target raw_x syn) syns);

in

val add_reserved = add_reserved;
val add_const_syntax = gen_add_const_syntax (K I);
val add_tyco_syntax = gen_add_tyco_syntax cert_tyco;
val add_class_syntax = gen_add_class_syntax cert_class;
val add_instance_syntax = gen_add_instance_syntax cert_inst;
val add_include = gen_add_include (K I);

val add_const_syntax_cmd = gen_add_const_syntax Code.read_const;
val add_tyco_syntax_cmd = gen_add_tyco_syntax read_tyco;
val add_class_syntax_cmd = gen_add_class_syntax read_class;
val add_instance_syntax_cmd = gen_add_instance_syntax read_inst;
val add_include_cmd = gen_add_include Code.read_const;

fun parse_args f args =
  case Scan.read Token.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(** Isar setup **)

fun parse_single_symbol_pragma parse_keyword parse_isa parse_target =
  parse_keyword |-- Parse.!!! (parse_isa --| (@{keyword "\<rightharpoonup>"} || @{keyword "=>"})
    -- Parse.and_list1 (@{keyword "("} |-- (Parse.name --| @{keyword ")"} -- Scan.option parse_target)));

fun parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  parse_single_symbol_pragma @{keyword "constant"} Parse.term parse_const
    >> Constant
  || parse_single_symbol_pragma @{keyword "type_constructor"} Parse.type_const parse_tyco
    >> Type_Constructor
  || parse_single_symbol_pragma @{keyword "type_class"} Parse.class parse_class
    >> Type_Class
  || parse_single_symbol_pragma @{keyword "class_relation"} parse_classrel_ident parse_classrel
    >> Class_Relation
  || parse_single_symbol_pragma @{keyword "class_instance"} parse_inst_ident parse_inst
    >> Class_Instance
  || parse_single_symbol_pragma @{keyword "code_module"} Parse.name parse_module
    >> Code_Symbol.Module;

fun parse_symbol_pragmas parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  Parse.enum1 "|" (Parse.group (fn () => "code symbol pragma")
    (parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module));

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Args.parse --| @{keyword ")"}) [];

fun code_expr_inP raw_cs =
  Scan.repeat (@{keyword "in"} |-- Parse.!!! (Parse.name
    -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
    -- Scan.optional (@{keyword "file"} |-- Parse.name) ""
    -- code_expr_argsP))
      >> (fn seri_args => export_code_cmd raw_cs seri_args);

fun code_expr_checkingP raw_cs =
  (@{keyword "checking"} |-- Parse.!!!
    (Scan.repeat (Parse.name -- ((@{keyword "?"} |-- Scan.succeed false) || Scan.succeed true)
    -- code_expr_argsP)))
      >> (fn seri_args => check_code_cmd raw_cs seri_args);

val code_exprP = Scan.repeat1 Parse.term
  :|-- (fn raw_cs => (code_expr_checkingP raw_cs || code_expr_inP raw_cs));

val _ =
  Outer_Syntax.command @{command_spec "code_reserved"}
    "declare words as reserved for target language"
    (Parse.name -- Scan.repeat1 Parse.name
      >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds));

val _ =
  Outer_Syntax.command @{command_spec "code_identifier"} "declare mandatory names for code symbols"
    (parse_symbol_pragmas Parse.name Parse.name Parse.name Parse.name Parse.name Parse.name
      >> (Toplevel.theory o fold set_identifiers_cmd));

val _ =
  Outer_Syntax.command @{command_spec "code_modulename"} "alias module to other name"
    (Parse.name -- Scan.repeat1 (Parse.name -- Parse.name)
      >> (fn (target, modlnames) => (Toplevel.theory o add_module_alias_cmd target) modlnames));

val _ =
  Outer_Syntax.command @{command_spec "code_printing"} "declare dedicated printing for code symbols"
    (parse_symbol_pragmas (Code_Printer.parse_const_syntax) (Code_Printer.parse_tyco_syntax)
      Parse.string (Parse.minus >> K ()) (Parse.minus >> K ())
      (Parse.text -- Scan.optional (@{keyword "attach"} |-- Scan.repeat1 Parse.term) [])
      >> (Toplevel.theory o fold set_printings_cmd));

val _ =
  Outer_Syntax.command @{command_spec "code_const"} "define code syntax for constant"
    (process_multi_syntax Parse.term Code_Printer.parse_const_syntax
      add_const_syntax_cmd);

val _ =
  Outer_Syntax.command @{command_spec "code_type"} "define code syntax for type constructor"
    (process_multi_syntax Parse.type_const Code_Printer.parse_tyco_syntax
      add_tyco_syntax_cmd);

val _ =
  Outer_Syntax.command @{command_spec "code_class"} "define code syntax for class"
    (process_multi_syntax Parse.class Parse.string
      add_class_syntax_cmd);

val _ =
  Outer_Syntax.command @{command_spec "code_instance"} "define code syntax for instance"
    (process_multi_syntax parse_inst_ident (Parse.minus >> K ())
      add_instance_syntax_cmd);

val _ =
  Outer_Syntax.command @{command_spec "code_include"}
    "declare piece of code to be included in generated code"
    (Parse.name -- Parse.name -- (Parse.text :|--
      (fn "-" => Scan.succeed NONE
        | s => Scan.optional (@{keyword "attach"} |-- Scan.repeat1 Parse.term) [] >> pair s >> SOME))
      >> (fn ((target, name), content_consts) =>
          (Toplevel.theory o add_include_cmd target) (name, content_consts)));

val _ =
  Outer_Syntax.command @{command_spec "export_code"} "generate executable code for constants"
    (Parse.!!! code_exprP >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

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
