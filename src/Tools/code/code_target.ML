(*  Title:      Tools/code/code_target.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to target languages.
*)

signature CODE_TARGET =
sig
  include CODE_PRINTER

  type serializer
  val add_target: string * (serializer * literals) -> theory -> theory
  val extend_target: string * (string * (Code_Thingol.program -> Code_Thingol.program))
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
    -> ('a -> string * string list)
    -> 'a -> serialization
  val serialize: theory -> string -> string option -> Args.T list
    -> Code_Thingol.program -> string list -> serialization
  val serialize_custom: theory -> string * (serializer * literals)
    -> Code_Thingol.program -> string list -> string * string list
  val compile: serialization -> unit
  val export: serialization -> unit
  val file: Path.T -> serialization -> unit
  val string: string list -> serialization -> string

  val code_of: theory -> string -> string -> string list -> string list -> string
  val shell_command: string (*theory name*) -> string (*export_code expr*) -> unit
  val code_width: int ref

  val allow_abort: string -> theory -> theory
  val add_syntax_class: string -> class
    -> (string * (string * string) list) option -> theory -> theory
  val add_syntax_inst: string -> string * class -> bool -> theory -> theory
  val add_syntax_tyco: string -> string -> tyco_syntax option -> theory -> theory
  val add_syntax_tycoP: string -> string -> OuterParse.token list
    -> (theory -> theory) * OuterParse.token list
  val add_syntax_const: string -> string -> const_syntax option -> theory -> theory
  val add_syntax_constP: string -> string -> OuterParse.token list
    -> (theory -> theory) * OuterParse.token list
  val add_reserved: string -> string -> theory -> theory

  val add_literal_list: string -> string -> string -> theory -> theory
  val add_literal_list_string: string -> string -> string
    -> string -> string list -> theory -> theory
  val add_literal_char: string -> string -> string list -> theory -> theory
  val add_literal_numeral: string -> bool -> bool -> string -> string -> string
    -> string -> string -> theory -> theory
  val add_literal_message: string -> string -> string list -> string
    -> string -> string -> theory -> theory
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Thingol;
open Code_Printer;

(** basics **)

datatype destination = Compile | Export | File of Path.T | String of string list;
type serialization = destination -> (string * string list) option;

val code_width = ref 80; (*FIXME after Pretty module no longer depends on print mode*)
fun code_setmp f = PrintMode.setmp [] (Pretty.setmp_margin (!code_width) f);
fun code_of_pretty p = code_setmp Pretty.string_of p ^ "\n";
fun code_writeln p = Pretty.setmp_margin (!code_width) Pretty.writeln p;

(*FIXME why another code_setmp?*)
fun compile f = (code_setmp f Compile; ());
fun export f = (code_setmp f Export; ());
fun file p f = (code_setmp f (File p); ());
fun string cs f = fst (the (code_setmp f (String cs)));

fun stmt_names_of_destination (String stmts) = stmts
  | stmt_names_of_destination _ = [];

fun mk_serialization target (SOME comp) _ _ code Compile = (comp code; NONE)
  | mk_serialization target NONE _ _ _ Compile = error (target ^ ": no internal compilation")
  | mk_serialization target _ output _ code Export = (output NONE code ; NONE)
  | mk_serialization target _ output _ code (File file) = (output (SOME file) code; NONE)
  | mk_serialization target _ _ string code (String _) = SOME (string code);


(** pretty syntax **)

(* list, char, string, numeral and monad abstract syntax transformations *)

fun implode_list c_nil c_cons t =
  let
    fun dest_cons (IConst (c, _) `$ t1 `$ t2) =
          if c = c_cons
          then SOME (t1, t2)
          else NONE
      | dest_cons _ = NONE;
    val (ts, t') = Code_Thingol.unfoldr dest_cons t;
  in case t'
   of IConst (c, _) => if c = c_nil then SOME ts else NONE
    | _ => NONE
  end;

fun decode_char c_nibbles (IConst (c1, _), IConst (c2, _)) =
      let
        fun idx c = find_index (curry (op =) c) c_nibbles;
        fun decode ~1 _ = NONE
          | decode _ ~1 = NONE
          | decode n m = SOME (chr (n * 16 + m));
      in decode (idx c1) (idx c2) end
  | decode_char _ _ = NONE;

fun implode_string c_char c_nibbles mk_char mk_string ts =
  let
    fun implode_char (IConst (c, _) `$ t1 `$ t2) =
          if c = c_char then decode_char c_nibbles (t1, t2) else NONE
      | implode_char _ = NONE;
    val ts' = map implode_char ts;
  in if forall is_some ts'
    then (SOME o str o mk_string o implode o map_filter I) ts'
    else NONE
  end;

fun implode_numeral thm negative c_pls c_min c_bit0 c_bit1 =
  let
    fun dest_bit (IConst (c, _)) = if c = c_bit0 then 0
          else if c = c_bit1 then 1
          else nerror thm "Illegal numeral expression: illegal bit"
      | dest_bit _ = nerror thm "Illegal numeral expression: illegal bit";
    fun dest_numeral (IConst (c, _)) = if c = c_pls then SOME 0
          else if c = c_min then
            if negative then SOME ~1 else NONE
          else nerror thm "Illegal numeral expression: illegal leading digit"
      | dest_numeral (t1 `$ t2) =
          let val (n, b) = (dest_numeral t2, dest_bit t1)
          in case n of SOME n => SOME (2 * n + b) | NONE => NONE end
      | dest_numeral _ = nerror thm "Illegal numeral expression: illegal term";
  in dest_numeral #> the_default 0 end;


(* literal syntax printing *)

fun default_list (target_fxy, target_cons) pr fxy t1 t2 =
  brackify_infix (target_fxy, R) fxy [
    pr (INFX (target_fxy, X)) t1,
    str target_cons,
    pr (INFX (target_fxy, R)) t2
  ];

fun pretty_list c_nil c_cons literals =
  let
    val mk_list = literal_list literals;
    fun pretty pr thm pat vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts => mk_list (map (pr vars NOBR) ts)
        | NONE => default_list (infix_cons literals) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_list_string c_nil c_cons c_char c_nibbles literals =
  let
    val mk_list = literal_list literals;
    val mk_char = literal_char literals;
    val mk_string = literal_string literals;
    fun pretty pr thm pat vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts => (case implode_string c_char c_nibbles mk_char mk_string ts
           of SOME p => p
            | NONE => mk_list (map (pr vars NOBR) ts))
        | NONE => default_list (infix_cons literals) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_char c_char c_nibbles literals =
  let
    val mk_char = literal_char literals;
    fun pretty _ thm _ _ _ [(t1, _), (t2, _)] =
      case decode_char c_nibbles (t1, t2)
       of SOME c => (str o mk_char) c
        | NONE => nerror thm "Illegal character expression";
  in (2, pretty) end;

fun pretty_numeral unbounded negative c_pls c_min c_bit0 c_bit1 literals =
  let
    val mk_numeral = literal_numeral literals;
    fun pretty _ thm _ _ _ [(t, _)] =
      (str o mk_numeral unbounded o implode_numeral thm negative c_pls c_min c_bit0 c_bit1) t;
  in (1, pretty) end;

fun pretty_message c_char c_nibbles c_nil c_cons literals =
  let
    val mk_char = literal_char literals;
    val mk_string = literal_string literals;
    fun pretty _ thm _ _ _ [(t, _)] =
      case implode_list c_nil c_cons t
       of SOME ts => (case implode_string c_char c_nibbles mk_char mk_string ts
           of SOME p => p
            | NONE => nerror thm "Illegal message expression")
        | NONE => nerror thm "Illegal message expression";
  in (1, pretty) end;


(** theory data **)

datatype name_syntax_table = NameSyntaxTable of {
  class: class_syntax Symtab.table,
  inst: unit Symtab.table,
  tyco: tyco_syntax Symtab.table,
  const: const_syntax Symtab.table
};

fun mk_name_syntax_table ((class, inst), (tyco, const)) =
  NameSyntaxTable { class = class, inst = inst, tyco = tyco, const = const };
fun map_name_syntax_table f (NameSyntaxTable { class, inst, tyco, const }) =
  mk_name_syntax_table (f ((class, inst), (tyco, const)));
fun merge_name_syntax_table (NameSyntaxTable { class = class1, inst = inst1, tyco = tyco1, const = const1 },
    NameSyntaxTable { class = class2, inst = inst2, tyco = tyco2, const = const2 }) =
  mk_name_syntax_table (
    (Symtab.join (K snd) (class1, class2),
       Symtab.join (K snd) (inst1, inst2)),
    (Symtab.join (K snd) (tyco1, tyco2),
       Symtab.join (K snd) (const1, const2))
  );

type serializer =
  string option                         (*module name*)
  -> Args.T list                        (*arguments*)
  -> (string -> string)                 (*labelled_name*)
  -> string list                        (*reserved symbols*)
  -> (string * Pretty.T) list           (*includes*)
  -> (string -> string option)          (*module aliasses*)
  -> (string -> class_syntax option)
  -> (string -> tyco_syntax option)
  -> (string -> const_syntax option)
  -> Code_Thingol.program
  -> string list                        (*selected statements*)
  -> serialization;

datatype serializer_entry = Serializer of serializer * literals
  | Extends of string * (Code_Thingol.program -> Code_Thingol.program);

datatype target = Target of {
  serial: serial,
  serializer: serializer_entry,
  reserved: string list,
  includes: Pretty.T Symtab.table,
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
    val defined_target = is_some o Symtab.lookup (fst (CodeTargetData.get thy));
    val _ = case seri
     of Extends (super, _) => if defined_target super then ()
          else error ("Unknown code target language: " ^ quote super)
      | _ => ();
    val _ = if defined_target target
      then warning ("Overwriting existing target " ^ quote target)
      else ();
  in
    thy
    |> (CodeTargetData.map o apfst oo Symtab.map_default)
          (target, mk_target ((serial (), seri), (([], Symtab.empty),
            (mk_name_syntax_table ((Symtab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)),
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
    val class' = Code_Name.class thy class;
    fun mk_classparam c = case AxClass.class_of_param thy c
     of SOME class'' => if class = class'' then Code_Name.const thy c
          else error ("Not a class operation for class " ^ quote class ^ ": " ^ quote c)
      | NONE => error ("Not a class operation: " ^ quote c);
    fun mk_syntax_params raw_params = AList.lookup (op =)
      ((map o apfst) (mk_classparam o prep_const thy) raw_params);
  in case raw_syn
   of SOME (syntax, raw_params) =>
      thy
      |> (map_name_syntax target o apfst o apfst)
           (Symtab.update (class', (syntax, mk_syntax_params raw_params)))
    | NONE =>
      thy
      |> (map_name_syntax target o apfst o apfst)
           (Symtab.delete_safe class')
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) add_del thy =
  let
    val inst = Code_Name.instance thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in if add_del then
    thy
    |> (map_name_syntax target o apfst o apsnd)
        (Symtab.update (inst, ()))
  else
    thy
    |> (map_name_syntax target o apfst o apsnd)
        (Symtab.delete_safe inst)
  end;

fun gen_add_syntax_tyco prep_tyco target raw_tyco raw_syn thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    val tyco' = if tyco = "fun" then "fun" else Code_Name.tyco thy tyco;
    fun check_args (syntax as (n, _)) = if n <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syntax
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apsnd o apfst)
           (Symtab.update (tyco', check_args syntax))
   | NONE =>
      thy
      |> (map_name_syntax target o apsnd o apfst)
           (Symtab.delete_safe tyco')
  end;

fun gen_add_syntax_const prep_const target raw_c raw_syn thy =
  let
    val c = prep_const thy raw_c;
    val c' = Code_Name.const thy c;
    fun check_args (syntax as (n, _)) = if n > Code_Unit.no_args thy c
      then error ("Too many arguments in syntax for constant " ^ quote c)
      else syntax;
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_name_syntax target o apsnd o apsnd)
           (Symtab.update (c', check_args syntax))
   | NONE =>
      thy
      |> (map_name_syntax target o apsnd o apsnd)
           (Symtab.delete_safe c')
  end;

fun add_reserved target =
  let
    fun add sym syms = if member (op =) syms sym
      then error ("Reserved symbol " ^ quote sym ^ " already declared")
      else insert (op =) sym syms
  in map_reserved target o add end;

fun add_include target =
  let
    fun add (name, SOME content) incls =
          let
            val _ = if Symtab.defined incls name
              then warning ("Overwriting existing include " ^ name)
              else ();
          in Symtab.update (name, str content) incls end
      | add (name, NONE) incls =
          Symtab.delete name incls;
  in map_includes target o add end;

fun add_module_alias target =
  map_module_alias target o Symtab.update o apsnd Code_Name.check_modulename;

fun gen_allow_abort prep_cs raw_c thy =
  let
    val c = prep_cs thy raw_c;
    val c' = Code_Name.const thy c;
  in thy |> (CodeTargetData.map o apsnd) (insert (op =) c') end;

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

val parse_syntax = parse_syntax;

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

fun add_syntax_tycoP target tyco = parse_syntax I
  >> add_syntax_tyco_cmd target tyco;
fun add_syntax_constP target c = parse_syntax fst
  >> (add_syntax_const_cmd target c o Code_Printer.simple_const_syntax);

fun the_literals thy =
  let
    val (targets, _) = CodeTargetData.get thy;
    fun literals target = case Symtab.lookup targets target
     of SOME data => (case the_serializer data
         of Serializer (_, literals) => literals
          | Extends (super, _) => literals super)
      | NONE => error ("Unknown code target language: " ^ quote target);
  in literals end;

fun add_literal_list target nill cons thy =
  let
    val nil' = Code_Name.const thy nill;
    val cons' = Code_Name.const thy cons;
    val pr = pretty_list nil' cons' (the_literals thy target);
  in
    thy
    |> add_syntax_const target cons (SOME pr)
  end;

fun add_literal_list_string target nill cons charr nibbles thy =
  let
    val nil' = Code_Name.const thy nill;
    val cons' = Code_Name.const thy cons;
    val charr' = Code_Name.const thy charr;
    val nibbles' = map (Code_Name.const thy) nibbles;
    val pr = pretty_list_string nil' cons' charr' nibbles' (the_literals thy target);
  in
    thy
    |> add_syntax_const target cons (SOME pr)
  end;

fun add_literal_char target charr nibbles thy =
  let
    val charr' = Code_Name.const thy charr;
    val nibbles' = map (Code_Name.const thy) nibbles;
    val pr = pretty_char charr' nibbles' (the_literals thy target);
  in
    thy
    |> add_syntax_const target charr (SOME pr)
  end;

fun add_literal_numeral target unbounded negative number_of pls min bit0 bit1 thy =
  let
    val pls' = Code_Name.const thy pls;
    val min' = Code_Name.const thy min;
    val bit0' = Code_Name.const thy bit0;
    val bit1' = Code_Name.const thy bit1;
    val pr = pretty_numeral unbounded negative pls' min' bit0' bit1' (the_literals thy target);
  in
    thy
    |> add_syntax_const target number_of (SOME pr)
  end;

fun add_literal_message target charr nibbles nill cons str thy =
  let
    val charr' = Code_Name.const thy charr;
    val nibbles' = map (Code_Name.const thy) nibbles;
    val nil' = Code_Name.const thy nill;
    val cons' = Code_Name.const thy cons;
    val pr = pretty_message charr' nibbles' nil' cons' (the_literals thy target);
  in
    thy
    |> add_syntax_const target str (SOME pr)
  end;


(** serializer usage **)

(* montage *)

fun invoke_serializer thy modify abortable serializer reserved includes 
    module_alias class inst tyco const module args program1 cs1 =
  let
    val program2 = modify program1;
    val hidden = Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const;
    val cs2 = subtract (op =) hidden cs1;
    val program3 = Graph.subgraph (not o member (op =) hidden) program2;
    val all_cs = Graph.all_succs program2 cs2;
    val program4 = Graph.subgraph (member (op =) all_cs) program3;
    val empty_funs = filter_out (member (op =) abortable)
      (Code_Thingol.empty_funs program3);
    val _ = if null empty_funs then () else error ("No defining equations for "
      ^ commas (map (Code_Name.labelled_name thy) empty_funs));
  in
    serializer module args (Code_Name.labelled_name thy) reserved includes
      (Symtab.lookup module_alias) (Symtab.lookup class)
      (Symtab.lookup tyco) (Symtab.lookup const)
      program4 cs2
  end;

fun mount_serializer thy alt_serializer target =
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
          in (modify' #> modify, merge_target false target (data', data)) end
      end;
    val (modify, data) = collapse_hierarchy target;
    val (serializer, _) = the_default (case the_serializer data
     of Serializer seri => seri) alt_serializer;
    val reserved = the_reserved data;
    val includes = Symtab.dest (the_includes data);
    val module_alias = the_module_alias data;
    val { class, inst, tyco, const } = the_name_syntax data;
  in
    invoke_serializer thy modify abortable serializer reserved
      includes module_alias class inst tyco const
  end;

fun serialize thy = mount_serializer thy NONE;

fun serialize_custom thy (target_name, seri) program cs =
  mount_serializer thy (SOME seri) target_name NONE [] program cs (String [])
  |> the;

fun parse_args f args =
  case Scan.read OuterLex.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(* code presentation *)

fun code_of thy target module_name cs stmt_names =
  let
    val (cs', program) = Code_Thingol.consts_program thy cs;
  in
    string stmt_names (serialize thy target (SOME module_name) [] program cs')
  end;


(* code generation *)

fun read_const_exprs thy cs =
  let
    val (cs1, cs2) = Code_Name.read_const_exprs thy cs;
    val (cs3, program) = Code_Thingol.consts_program thy cs2;
    val cs4 = Code_Thingol.transitivly_non_empty_funs program (abort_allowed thy);
    val cs5 = map_filter
      (fn (c, c') => if member (op =) cs4 c' then SOME c else NONE) (cs2 ~~ cs3);
  in fold (insert (op =)) cs5 cs1 end;

fun cached_program thy = 
  let
    val program = Code_Thingol.cached_program thy;
  in (Code_Thingol.transitivly_non_empty_funs program (abort_allowed thy), program) end

fun export_code thy cs seris =
  let
    val (cs', program) = if null cs then cached_program thy
      else Code_Thingol.consts_program thy cs;
    fun mk_seri_dest dest = case dest
     of NONE => compile
      | SOME "-" => export
      | SOME f => file (Path.explode f)
    val _ = map (fn (((target, module), dest), args) =>
      (mk_seri_dest dest (serialize thy target module args program cs'))) seris;
  in () end;

fun export_code_cmd raw_cs seris thy = export_code thy (read_const_exprs thy raw_cs) seris;


(** Isar setup **)

val (inK, module_nameK, fileK) = ("in", "module_name", "file");

fun code_exprP cmd =
  (Scan.repeat P.term_group
  -- Scan.repeat (P.$$$ inK |-- P.name
     -- Scan.option (P.$$$ module_nameK |-- P.name)
     -- Scan.option (P.$$$ fileK |-- P.name)
     -- Scan.optional (P.$$$ "(" |-- Args.parse --| P.$$$ ")") []
  ) >> (fn (raw_cs, seris) => cmd raw_cs seris));

val _ = List.app OuterKeyword.keyword [inK, module_nameK, fileK];

val _ =
  OuterSyntax.command "code_class" "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (Scan.option (P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term_group --| (P.$$$ "\<equiv>" || P.$$$ "==") -- P.string)) []))
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
    P.name -- P.name -- (P.text >> (fn "-" => NONE | s => SOME s))
    >> (fn ((target, name), content) => (Toplevel.theory o add_include target)
      (name, content))
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
    K.diag (P.!!! (code_exprP export_code_cmd) >> (fn f => Toplevel.keep (f o Toplevel.theory_of)));

fun shell_command thyname cmd = Toplevel.program (fn _ =>
  (use_thy thyname; case Scan.read OuterLex.stopper (P.!!! (code_exprP export_code_cmd))
    ((filter OuterLex.is_proper o OuterSyntax.scan Position.none) cmd)
   of SOME f => (writeln "Now generating code..."; f (theory thyname))
    | NONE => error ("Bad directive " ^ quote cmd)))
  handle TOPLEVEL_ERROR => OS.Process.exit OS.Process.failure;

end; (*local*)

end; (*struct*)
