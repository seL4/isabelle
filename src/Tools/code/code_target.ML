(*  Title:      Tools/code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to target languages.
*)

signature CODE_TARGET =
sig
  include CODE_PRINTER

  type serializer
  val add_target: string * (serializer * literals) -> theory -> theory
  val extend_target: string *
      (string * (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program))
    -> theory -> theory
  val assert_target: theory -> string -> string

  type destination
  type serialization
  val parse_args: (OuterLex.token list -> 'a * OuterLex.token list)
    -> OuterLex.token list -> 'a
  val stmt_names_of_destination: destination -> string list
  val code_of_pretty: Pretty.T -> string
  val code_writeln: Pretty.T -> unit
  val mk_serialization: string -> ('a -> unit) option
    -> (Path.T option -> 'a -> unit)
    -> ('a -> string * string option list)
    -> 'a -> serialization
  val serialize: theory -> string -> string option -> OuterLex.token list
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> serialization
  val serialize_custom: theory -> string * (serializer * literals)
    -> Code_Thingol.naming -> Code_Thingol.program -> string list -> string * string option list
  val the_literals: theory -> string -> literals
  val compile: serialization -> unit
  val export: serialization -> unit
  val file: Path.T -> serialization -> unit
  val string: string list -> serialization -> string
  val code_of: theory -> string -> string
    -> string list -> (Code_Thingol.naming -> string list) -> string
  val shell_command: string (*theory name*) -> string (*export_code expr*) -> unit
  val code_width: int ref

  val allow_abort: string -> theory -> theory
  val add_syntax_class: string -> class -> string option -> theory -> theory
  val add_syntax_inst: string -> string * class -> bool -> theory -> theory
  val add_syntax_tyco: string -> string -> tyco_syntax option -> theory -> theory
  val add_syntax_const: string -> string -> const_syntax option -> theory -> theory
  val add_reserved: string -> string -> theory -> theory
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Thingol;
open Code_Printer;

(** basics **)

datatype destination = Compile | Export | File of Path.T | String of string list;
type serialization = destination -> (string * string option list) option;

val code_width = ref 80; (*FIXME after Pretty module no longer depends on print mode*)
fun code_setmp f = PrintMode.setmp [] (Pretty.setmp_margin (!code_width) f);
fun code_of_pretty p = code_setmp Pretty.string_of p ^ "\n";
fun code_writeln p = Pretty.setmp_margin (!code_width) Pretty.writeln p;

(*FIXME why another code_setmp?*)
fun compile f = (code_setmp f Compile; ());
fun export f = (code_setmp f Export; ());
fun file p f = (code_setmp f (File p); ());
fun string stmts f = fst (the (code_setmp f (String stmts)));

fun stmt_names_of_destination (String stmts) = stmts
  | stmt_names_of_destination _ = [];

fun mk_serialization target (SOME comp) _ _ code Compile = (comp code; NONE)
  | mk_serialization target NONE _ _ _ Compile = error (target ^ ": no internal compilation")
  | mk_serialization target _ output _ code Export = (output NONE code ; NONE)
  | mk_serialization target _ output _ code (File file) = (output (SOME file) code; NONE)
  | mk_serialization target _ _ string code (String _) = SOME (string code);


(** theory data **)

datatype name_syntax_table = NameSyntaxTable of {
  class: string Symtab.table,
  instance: unit Symreltab.table,
  tyco: tyco_syntax Symtab.table,
  const: const_syntax Symtab.table
};

fun mk_name_syntax_table ((class, instance), (tyco, const)) =
  NameSyntaxTable { class = class, instance = instance, tyco = tyco, const = const };
fun map_name_syntax_table f (NameSyntaxTable { class, instance, tyco, const }) =
  mk_name_syntax_table (f ((class, instance), (tyco, const)));
fun merge_name_syntax_table (NameSyntaxTable { class = class1, instance = instance1, tyco = tyco1, const = const1 },
    NameSyntaxTable { class = class2, instance = instance2, tyco = tyco2, const = const2 }) =
  mk_name_syntax_table (
    (Symtab.join (K snd) (class1, class2),
       Symreltab.join (K snd) (instance1, instance2)),
    (Symtab.join (K snd) (tyco1, tyco2),
       Symtab.join (K snd) (const1, const2))
  );

type serializer =
  string option                         (*module name*)
  -> OuterLex.token list                (*arguments*)
  -> (string -> string)                 (*labelled_name*)
  -> string list                        (*reserved symbols*)
  -> (string * Pretty.T) list           (*includes*)
  -> (string -> string option)          (*module aliasses*)
  -> (string -> string option)          (*class syntax*)
  -> (string -> tyco_syntax option)
  -> (string -> const_syntax option)
  -> Code_Thingol.naming
  -> Code_Thingol.program
  -> string list                        (*selected statements*)
  -> serialization;

datatype serializer_entry = Serializer of serializer * literals
  | Extends of string * (Code_Thingol.naming -> Code_Thingol.program -> Code_Thingol.program);

datatype target = Target of {
  serial: serial,
  serializer: serializer_entry,
  reserved: string list,
  includes: (Pretty.T * string list) Symtab.table,
  name_syntax_table: name_syntax_table,
  module_alias: string Symtab.table
};

fun mk_target ((serial, serializer), ((reserved, includes), (name_syntax_table, module_alias))) =
  Target { serial = serial, serializer = serializer, reserved = reserved, 
    includes = includes, name_syntax_table = name_syntax_table, module_alias = module_alias };
fun map_target f ( Target { serial, serializer, reserved, includes, name_syntax_table, module_alias } ) =
  mk_target (f ((serial, serializer), ((reserved, includes), (name_syntax_table, module_alias))));
fun merge_target strict target (Target { serial = serial1, serializer = serializer,
  reserved = reserved1, includes = includes1,
  name_syntax_table = name_syntax_table1, module_alias = module_alias1 },
    Target { serial = serial2, serializer = _,
      reserved = reserved2, includes = includes2,
      name_syntax_table = name_syntax_table2, module_alias = module_alias2 }) =
  if serial1 = serial2 orelse not strict then
    mk_target ((serial1, serializer),
      ((merge (op =) (reserved1, reserved2), Symtab.merge (op =) (includes1, includes2)),
        (merge_name_syntax_table (name_syntax_table1, name_syntax_table2),
          Symtab.join (K snd) (module_alias1, module_alias2))
    ))
  else
    error ("Incompatible serializers: " ^ quote target);

structure CodeTargetData = TheoryDataFun
(
  type T = target Symtab.table * string list;
  val empty = (Symtab.empty, []);
  val copy = I;
  val extend = I;
  fun merge _ ((target1, exc1) : T, (target2, exc2)) =
    (Symtab.join (merge_target true) (target1, target2), Library.merge (op =) (exc1, exc2));
);

fun the_serializer (Target { serializer, ... }) = serializer;
fun the_reserved (Target { reserved, ... }) = reserved;
fun the_includes (Target { includes, ... }) = includes;
fun the_name_syntax (Target { name_syntax_table = NameSyntaxTable x, ... }) = x;
fun the_module_alias (Target { module_alias , ... }) = module_alias;

val abort_allowed = snd o CodeTargetData.get;

fun assert_target thy target =
  case Symtab.lookup (fst (CodeTargetData.get thy)) target
   of SOME data => target
    | NONE => error ("Unknown code target language: " ^ quote target);

fun put_target (target, seri) thy =
  let
    val lookup_target = Symtab.lookup (fst (CodeTargetData.get thy));
    val _ = case seri
     of Extends (super, _) => if is_some (lookup_target super) then ()
          else error ("Unknown code target language: " ^ quote super)
      | _ => ();
    val overwriting = case (Option.map the_serializer o lookup_target) target
     of NONE => false
      | SOME (Extends _) => true
      | SOME (Serializer _) => (case seri
         of Extends _ => error ("Will not overwrite existing target " ^ quote target)
          | _ => true);
    val _ = if overwriting
      then warning ("Overwriting existing target " ^ quote target)
      else (); 
  in
    thy
    |> (CodeTargetData.map o apfst oo Symtab.map_default)
          (target, mk_target ((serial (), seri), (([], Symtab.empty),
            (mk_name_syntax_table ((Symtab.empty, Symreltab.empty), (Symtab.empty, Symtab.empty)),
              Symtab.empty))))
          ((map_target o apfst o apsnd o K) seri)
  end;

fun add_target (target, seri) = put_target (target, Serializer seri);
fun extend_target (target, (super, modify)) =
  put_target (target, Extends (super, modify));

fun map_target_data target f thy =
  let
    val _ = assert_target thy target;
  in
    thy
    |> (CodeTargetData.map o apfst o Symtab.map_entry target o map_target) f
  end;

fun map_reserved target =
  map_target_data target o apsnd o apfst o apfst;
fun map_includes target =
  map_target_data target o apsnd o apfst o apsnd;
fun map_name_syntax target =
  map_target_data target o apsnd o apsnd o apfst o map_name_syntax_table;
fun map_module_alias target =
  map_target_data target o apsnd o apsnd o apsnd;


(** serializer configuration **)

(* data access *)

local

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

fun gen_add_syntax_class prep_class prep_const target raw_class raw_syn thy =
  let
    val class = prep_class thy raw_class;
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apfst o apfst)
           (Symtab.update (class, syntax))
    | NONE =>
      thy
      |> (map_name_syntax target o apfst o apfst)
           (Symtab.delete_safe class)
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) add_del thy =
  let
    val inst = (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in if add_del then
    thy
    |> (map_name_syntax target o apfst o apsnd)
        (Symreltab.update (inst, ()))
  else
    thy
    |> (map_name_syntax target o apfst o apsnd)
        (Symreltab.delete_safe inst)
  end;

fun gen_add_syntax_tyco prep_tyco target raw_tyco raw_syn thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    fun check_args (syntax as (n, _)) = if n <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syntax
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apsnd o apfst)
           (Symtab.update (tyco, check_args syntax))
    | NONE =>
      thy
      |> (map_name_syntax target o apsnd o apfst)
           (Symtab.delete_safe tyco)
  end;

fun gen_add_syntax_const prep_const target raw_c raw_syn thy =
  let
    val c = prep_const thy raw_c;
    fun check_args (syntax as (n, _)) = if n > Code_Unit.no_args thy c
      then error ("Too many arguments in syntax for constant " ^ quote c)
      else syntax;
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apsnd o apsnd)
           (Symtab.update (c, check_args syntax))
    | NONE =>
      thy
      |> (map_name_syntax target o apsnd o apsnd)
           (Symtab.delete_safe c)
  end;

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
          in Symtab.update (name, (str content, cs)) incls end
      | add (name, NONE) incls = Symtab.delete name incls;
  in map_includes target (add args) thy end;

val add_include = gen_add_include Code_Unit.check_const;
val add_include_cmd = gen_add_include Code_Unit.read_const;

fun add_module_alias target (thyname, modlname) =
  let
    val xs = Long_Name.explode modlname;
    val xs' = map (Code_Name.purify_name true) xs;
  in if xs' = xs
    then map_module_alias target (Symtab.update (thyname, modlname))
    else error ("Invalid module name: " ^ quote modlname ^ "\n"
      ^ "perhaps try " ^ quote (Long_Name.implode xs'))
  end;

fun gen_allow_abort prep_const raw_c thy =
  let
    val c = prep_const thy raw_c;
  in thy |> (CodeTargetData.map o apsnd) (insert (op =) c) end;

fun zip_list (x::xs) f g =
  f
  #-> (fn y =>
    fold_map (fn x => g |-- f >> pair x) xs
    #-> (fn xys => pair ((x, y) :: xys)));


(* concrete syntax *)

structure P = OuterParse
and K = OuterKeyword

fun parse_multi_syntax parse_thing parse_syntax =
  P.and_list1 parse_thing
  #-> (fn things => Scan.repeat1 (P.$$$ "(" |-- P.name --
        (zip_list things parse_syntax (P.$$$ "and")) --| P.$$$ ")"));

in

val add_syntax_class = gen_add_syntax_class cert_class (K I);
val add_syntax_inst = gen_add_syntax_inst cert_class cert_tyco;
val add_syntax_tyco = gen_add_syntax_tyco cert_tyco;
val add_syntax_const = gen_add_syntax_const (K I);
val allow_abort = gen_allow_abort (K I);
val add_reserved = add_reserved;

val add_syntax_class_cmd = gen_add_syntax_class read_class Code_Unit.read_const;
val add_syntax_inst_cmd = gen_add_syntax_inst read_class read_tyco;
val add_syntax_tyco_cmd = gen_add_syntax_tyco read_tyco;
val add_syntax_const_cmd = gen_add_syntax_const Code_Unit.read_const;
val allow_abort_cmd = gen_allow_abort Code_Unit.read_const;

fun the_literals thy =
  let
    val (targets, _) = CodeTargetData.get thy;
    fun literals target = case Symtab.lookup targets target
     of SOME data => (case the_serializer data
         of Serializer (_, literals) => literals
          | Extends (super, _) => literals super)
      | NONE => error ("Unknown code target language: " ^ quote target);
  in literals end;


(** serializer usage **)

(* montage *)

local

fun labelled_name thy program name = case Graph.get_node program name
 of Code_Thingol.Fun (c, _) => quote (Code_Unit.string_of_const thy c)
  | Code_Thingol.Datatype (tyco, _) => "type " ^ quote (Sign.extern_type thy tyco)
  | Code_Thingol.Datatypecons (c, _) => quote (Code_Unit.string_of_const thy c)
  | Code_Thingol.Class (class, _) => "class " ^ quote (Sign.extern_class thy class)
  | Code_Thingol.Classrel (sub, super) => let
        val Code_Thingol.Class (sub, _) = Graph.get_node program sub
        val Code_Thingol.Class (super, _) = Graph.get_node program super
      in quote (Sign.extern_class thy sub ^ " < " ^ Sign.extern_class thy super) end
  | Code_Thingol.Classparam (c, _) => quote (Code_Unit.string_of_const thy c)
  | Code_Thingol.Classinst ((class, (tyco, _)), _) => let
        val Code_Thingol.Class (class, _) = Graph.get_node program class
        val Code_Thingol.Datatype (tyco, _) = Graph.get_node program tyco
      in quote (Sign.extern_type thy tyco ^ " :: " ^ Sign.extern_class thy class) end

fun invoke_serializer thy abortable serializer reserved abs_includes 
    module_alias class instance tyco const module args naming program2 names1 =
  let
    fun distill_names lookup_name src_tab = Symtab.empty
      |> fold_map (fn thing_identifier => fn tab => case lookup_name naming thing_identifier
           of SOME name => (SOME name, Symtab.update_new (name, the (Symtab.lookup src_tab thing_identifier)) tab)
            | NONE => (NONE, tab)) (Symtab.keys src_tab)
      |>> map_filter I;
    val (names_class, class') = distill_names Code_Thingol.lookup_class class;
    val names_inst = map_filter (Code_Thingol.lookup_instance naming)
      (Symreltab.keys instance);
    val (names_tyco, tyco') = distill_names Code_Thingol.lookup_tyco tyco;
    val (names_const, const') = distill_names Code_Thingol.lookup_const const;
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
    serializer module args (labelled_name thy program2) reserved includes
      (Symtab.lookup module_alias) (Symtab.lookup class')
      (Symtab.lookup tyco') (Symtab.lookup const')
      naming program4 names2
  end;

fun mount_serializer thy alt_serializer target module args naming program names =
  let
    val (targets, abortable) = CodeTargetData.get thy;
    fun collapse_hierarchy target =
      let
        val data = case Symtab.lookup targets target
         of SOME data => data
          | NONE => error ("Unknown code target language: " ^ quote target);
      in case the_serializer data
       of Serializer _ => (I, data)
        | Extends (super, modify) => let
            val (modify', data') = collapse_hierarchy super
          in (modify' #> modify naming, merge_target false target (data', data)) end
      end;
    val (modify, data) = collapse_hierarchy target;
    val (serializer, _) = the_default (case the_serializer data
     of Serializer seri => seri) alt_serializer;
    val reserved = the_reserved data;
    fun select_include names_all (name, (content, cs)) =
      if null cs then SOME (name, content)
      else if exists (fn c => case Code_Thingol.lookup_const naming c
       of SOME name => member (op =) names_all name
        | NONE => false) cs
      then SOME (name, content) else NONE;
    fun includes names_all = map_filter (select_include names_all)
      ((Symtab.dest o the_includes) data);
    val module_alias = the_module_alias data;
    val { class, instance, tyco, const } = the_name_syntax data;
  in
    invoke_serializer thy abortable serializer reserved
      includes module_alias class instance tyco const module args naming (modify program) names
  end;

in

fun serialize thy = mount_serializer thy NONE;

fun serialize_custom thy (target_name, seri) naming program names =
  mount_serializer thy (SOME seri) target_name NONE [] naming program names (String [])
  |> the;

end; (* local *)

fun parse_args f args =
  case Scan.read OuterLex.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(* code presentation *)

fun code_of thy target module_name cs names_stmt =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy cs;
  in
    string (names_stmt naming) (serialize thy target (SOME module_name) []
      naming program names_cs)
  end;


(* code generation *)

fun transitivly_non_empty_funs thy naming program =
  let
    val cs = subtract (op =) (abort_allowed thy) (Code_Thingol.empty_funs program);
    val names = map_filter (Code_Thingol.lookup_const naming) cs;
  in subtract (op =) (Graph.all_preds program names) (Graph.keys program) end;

fun read_const_exprs thy cs =
  let
    val (cs1, cs2) = Code_Name.read_const_exprs thy cs;
    val (names3, (naming, program)) = Code_Thingol.consts_program thy cs2;
    val names4 = transitivly_non_empty_funs thy naming program;
    val cs5 = map_filter
      (fn (c, name) => if member (op =) names4 name then SOME c else NONE) (cs2 ~~ names3);
  in fold (insert (op =)) cs5 cs1 end;

fun cached_program thy = 
  let
    val (naming, program) = Code_Thingol.cached_program thy;
  in (transitivly_non_empty_funs thy naming program, (naming, program)) end

fun export_code thy cs seris =
  let
    val (cs', (naming, program)) = if null cs then cached_program thy
      else Code_Thingol.consts_program thy cs;
    fun mk_seri_dest dest = case dest
     of NONE => compile
      | SOME "-" => export
      | SOME f => file (Path.explode f)
    val _ = map (fn (((target, module), dest), args) =>
      (mk_seri_dest dest (serialize thy target module args naming program cs'))) seris;
  in () end;

fun export_code_cmd raw_cs seris thy = export_code thy (read_const_exprs thy raw_cs) seris;


(** Isar setup **)

val (inK, module_nameK, fileK) = ("in", "module_name", "file");

val code_exprP =
  (Scan.repeat P.term_group
  -- Scan.repeat (P.$$$ inK |-- P.name
     -- Scan.option (P.$$$ module_nameK |-- P.name)
     -- Scan.option (P.$$$ fileK |-- P.name)
     -- Scan.optional (P.$$$ "(" |-- Args.parse --| P.$$$ ")") []
  ) >> (fn (raw_cs, seris) => export_code_cmd raw_cs seris));

val _ = List.app OuterKeyword.keyword [inK, module_nameK, fileK];

val _ =
  OuterSyntax.command "code_class" "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname (Scan.option P.string)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => add_syntax_class_cmd target raw_class syn) syns)
  );

val _ =
  OuterSyntax.command "code_instance" "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      ((P.minus >> K true) || Scan.succeed false)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, add_del) => add_syntax_inst_cmd target raw_inst add_del) syns)
  );

val _ =
  OuterSyntax.command "code_type" "define code syntax for type constructor" K.thy_decl (
    parse_multi_syntax P.xname (parse_syntax I)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_tyco, syn) => add_syntax_tyco_cmd target raw_tyco syn) syns)
  );

val _ =
  OuterSyntax.command "code_const" "define code syntax for constant" K.thy_decl (
    parse_multi_syntax P.term_group (parse_syntax fst)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
      fold (fn (raw_const, syn) => add_syntax_const_cmd target raw_const
        (Code_Printer.simple_const_syntax syn)) syns)
  );

val _ =
  OuterSyntax.command "code_reserved" "declare words as reserved for target language" K.thy_decl (
    P.name -- Scan.repeat1 P.name
    >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds)
  );

val _ =
  OuterSyntax.command "code_include" "declare piece of code to be included in generated code" K.thy_decl (
    P.name -- P.name -- (P.text :|-- (fn "-" => Scan.succeed NONE
      | s => Scan.optional (P.$$$ "attach" |-- Scan.repeat1 P.term) [] >> pair s >> SOME))
    >> (fn ((target, name), content_consts) =>
        (Toplevel.theory o add_include_cmd target) (name, content_consts))
  );

val _ =
  OuterSyntax.command "code_modulename" "alias module to other name" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- P.name)
    >> (fn (target, modlnames) => (Toplevel.theory o fold (add_module_alias target)) modlnames)
  );

val _ =
  OuterSyntax.command "code_abort" "permit constant to be implemented as program abort" K.thy_decl (
    Scan.repeat1 P.term_group >> (Toplevel.theory o fold allow_abort_cmd)
  );

val _ =
  OuterSyntax.command "export_code" "generate executable code for constants"
    K.diag (P.!!! code_exprP >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun shell_command thyname cmd = Toplevel.program (fn _ =>
  (use_thy thyname; case Scan.read OuterLex.stopper (P.!!! code_exprP)
    ((filter OuterLex.is_proper o OuterSyntax.scan Position.none) cmd)
   of SOME f => (writeln "Now generating code..."; f (theory thyname))
    | NONE => error ("Bad directive " ^ quote cmd)))
  handle TOPLEVEL_ERROR => OS.Process.exit OS.Process.failure;

end; (*local*)

end; (*struct*)
