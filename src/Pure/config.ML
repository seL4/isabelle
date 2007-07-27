(*  Title:      Pure/config.ML
    ID:         $Id$
    Author:     Makarius

Configuration options as values within the local context.  Global
environment of named options, with type declaration.
*)

signature CONFIG =
sig
  datatype value = Bool of bool | Int of int | String of string
  type 'a T
  val get: Proof.context -> 'a T -> 'a
  val get_thy: theory -> 'a T -> 'a
  val get_generic: Context.generic -> 'a T -> 'a
  val map: 'a T -> ('a -> 'a) -> Proof.context -> Proof.context
  val map_thy: 'a T -> ('a -> 'a) -> theory -> theory
  val map_generic: 'a T -> ('a -> 'a) -> Context.generic -> Context.generic
  val put: 'a T -> 'a -> Proof.context -> Proof.context
  val put_thy: 'a T -> 'a -> theory -> theory
  val put_generic: 'a T -> 'a -> Context.generic -> Context.generic
  val print_configs: Proof.context -> unit
  val the_config: string -> value T * value
  val bool: string -> bool -> bool T
  val int: string -> int -> int T
  val string: string -> string -> string T
end;

structure Config: CONFIG =
struct

(* mixed values *)

datatype value =
  Bool of bool |
  Int of int |
  String of string;

fun print_value (Bool true) = "true"
  | print_value (Bool false) = "false"
  | print_value (Int i) = signed_string_of_int i
  | print_value (String s) = quote s;

fun print_type (Bool _) = "boolean"
  | print_type (Int _) = "integer"
  | print_type (String _) = "string";

fun same_type (Bool _) (Bool _) = true
  | same_type (Int _) (Int _) = true
  | same_type (String _) (String _) = true
  | same_type _ _ = false;

fun type_check f value =
  let
    val value' = f value;
    val _ = same_type value value' orelse
      error ("Ill-typed configuration option: " ^ print_type value ^
        " expected,\nbut " ^ print_type value' ^ " was found");
  in value' end;

structure ConfigData = GenericDataFun
(
  type T = value Inttab.table;
  val empty = Inttab.empty;
  val extend = I;
  fun merge _ = Inttab.merge (K true);
);


(* abstract configuration options *)

datatype 'a T = Config of
 {get_value: Context.generic -> 'a,
  map_value: ('a -> 'a) -> Context.generic -> Context.generic};

fun get_generic context (Config {get_value, ...}) = get_value context;
fun get_ctxt ctxt = get_generic (Context.Proof ctxt);
fun get_thy thy = get_generic (Context.Theory thy);

fun map_generic (Config {map_value, ...}) f context = map_value f context;
fun map_ctxt config f = Context.proof_map (map_generic config f);
fun map_thy config f = Context.theory_map (map_generic config f);

fun put_generic config value = map_generic config (K value);
fun put_ctxt config value = map_ctxt config (K value);
fun put_thy config value = map_thy config (K value);


(* global declarations *)

local val global_configs = ref (Symtab.empty: (value T * value) Symtab.table) in

fun print_configs ctxt =
  let
    fun prt (name, (config, default)) =
      Pretty.block [Pretty.str (name ^ ": " ^ print_type default ^ " ="), Pretty.brk 1,
        Pretty.str (print_value (get_ctxt ctxt config))];
    val configs = sort_wrt #1 (Symtab.dest (! global_configs));
  in Pretty.writeln (Pretty.big_list "configuration options" (map prt configs)) end;

fun the_config name =
  (case Symtab.lookup (! global_configs) name of SOME cfg => cfg
  | NONE => error ("Unknown configuration option " ^ quote name));

fun declare make dest name default =
  let
    val id = serial ();

    val default_value = make default;
    fun get_value context =
      the_default default_value (Inttab.lookup (ConfigData.get context) id);
    fun map_value f = ConfigData.map (Inttab.map_default (id, default_value) (type_check f));
    val config_value = Config {get_value = get_value, map_value = map_value};

    val _ = CRITICAL (fn () =>
     (if Symtab.defined (! global_configs) name
      then warning ("Hiding existing configuration option " ^ quote name) else ();
      change global_configs (Symtab.update (name, (config_value, default_value)))));

  in Config {get_value = dest o get_value, map_value = fn f => map_value (make o f o dest)} end;

end;

val bool = declare Bool (fn Bool b => b);
val int = declare Int (fn Int i => i);
val string = declare String (fn String s => s);


(*final declarations of this structure!*)
val get = get_ctxt;
val map = map_ctxt;
val put = put_ctxt;

end;
