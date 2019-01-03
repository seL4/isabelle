(*  Title:      Pure/config.ML
    Author:     Makarius

Configuration options as values within the local context.
*)

signature CONFIG =
sig
  datatype value = Bool of bool | Int of int | Real of real | String of string
  val print_value: value -> string
  val print_type: value -> string
  type 'a T
  val name_of: 'a T -> string
  val pos_of: 'a T -> Position.T
  val get: Proof.context -> 'a T -> 'a
  val map: 'a T -> ('a -> 'a) -> Proof.context -> Proof.context
  val put: 'a T -> 'a -> Proof.context -> Proof.context
  val restore: 'a T -> Proof.context -> Proof.context -> Proof.context
  val get_global: theory -> 'a T -> 'a
  val map_global: 'a T -> ('a -> 'a) -> theory -> theory
  val put_global: 'a T -> 'a -> theory -> theory
  val restore_global: 'a T -> theory -> theory -> theory
  val get_generic: Context.generic -> 'a T -> 'a
  val map_generic: 'a T -> ('a -> 'a) -> Context.generic -> Context.generic
  val put_generic: 'a T -> 'a -> Context.generic -> Context.generic
  val restore_generic: 'a T -> Context.generic -> Context.generic -> Context.generic
  val bool: value T -> bool T
  val bool_value: bool T -> value T
  val int: value T -> int T
  val int_value: int T -> value T
  val real: value T -> real T
  val real_value: real T -> value T
  val string: value T -> string T
  val string_value: string T -> value T
  val declare: string * Position.T -> (Context.generic -> value) -> value T
  val declare_bool: string * Position.T -> (Context.generic -> bool) -> bool T
  val declare_int: string * Position.T -> (Context.generic -> int) -> int T
  val declare_real: string * Position.T -> (Context.generic -> real) -> real T
  val declare_string: string * Position.T -> (Context.generic -> string) -> string T
  val declare_option: string * Position.T -> value T
  val declare_option_bool: string * Position.T -> bool T
  val declare_option_int: string * Position.T -> int T
  val declare_option_real: string * Position.T -> real T
  val declare_option_string: string * Position.T -> string T
end;

structure Config: CONFIG =
struct

(* simple values *)

datatype value =
  Bool of bool |
  Int of int |
  Real of real |
  String of string;

fun print_value (Bool true) = "true"
  | print_value (Bool false) = "false"
  | print_value (Int i) = Value.print_int i
  | print_value (Real x) = Value.print_real x
  | print_value (String s) = quote s;

fun print_type (Bool _) = "bool"
  | print_type (Int _) = "int"
  | print_type (Real _) = "real"
  | print_type (String _) = "string";

fun same_type (Bool _) (Bool _) = true
  | same_type (Int _) (Int _) = true
  | same_type (Real _) (Real _) = true
  | same_type (String _) (String _) = true
  | same_type _ _ = false;

fun type_check (name, pos) f value =
  let
    val value' = f value;
    val _ = same_type value value' orelse
      error ("Ill-typed configuration option " ^ quote name ^ Position.here pos ^ ": " ^
        print_type value ^ " expected,\nbut " ^ print_type value' ^ " was found");
  in value' end;


(* abstract configuration options *)

datatype 'a T = Config of
 {name: string,
  pos: Position.T,
  get_value: Context.generic -> 'a,
  map_value: ('a -> 'a) -> Context.generic -> Context.generic};

fun name_of (Config {name, ...}) = name;
fun pos_of (Config {pos, ...}) = pos;

fun get_generic context (Config {get_value, ...}) = get_value context;
fun map_generic (Config {map_value, ...}) f context = map_value f context;
fun put_generic config value = map_generic config (K value);
fun restore_generic config context = put_generic config (get_generic context config);

fun get_ctxt ctxt = get_generic (Context.Proof ctxt);
fun map_ctxt config f = Context.proof_map (map_generic config f);
fun put_ctxt config value = map_ctxt config (K value);
fun restore_ctxt config ctxt = put_ctxt config (get_ctxt ctxt config);

fun get_global thy = get_generic (Context.Theory thy);
fun map_global config f = Context.theory_map (map_generic config f);
fun put_global config value = map_global config (K value);
fun restore_global config thy = put_global config (get_global thy config);


(* coerce type *)

fun coerce make dest (Config {name, pos, get_value, map_value}) = Config
 {name = name,
  pos = pos,
  get_value = dest o get_value,
  map_value = fn f => map_value (make o f o dest)};

fun coerce_pair make dest = (coerce make dest, coerce dest make);

val (bool, bool_value) = coerce_pair Bool (fn Bool b => b);
val (int, int_value) = coerce_pair Int (fn Int i => i);
val (real, real_value) = coerce_pair Real (fn Real x => x);
val (string, string_value) = coerce_pair String (fn String s => s);


(* context data *)

structure Data = Generic_Data
(
  type T = value Inttab.table;
  val empty = Inttab.empty;
  val extend = I;
  fun merge data = Inttab.merge (K true) data;
);

fun declare (name, pos) default =
  let
    val id = serial ();

    fun get_value context =
      (case Inttab.lookup (Data.get context) id of
        SOME value => value
      | NONE => default context);

    fun map_value f context =
      Data.map (Inttab.update (id, type_check (name, pos) f (get_value context))) context;
  in
    Config {name = name, pos = pos, get_value = get_value, map_value = map_value}
  end;

fun declare_bool name default = bool (declare name (Bool o default));
fun declare_int name default = int (declare name (Int o default));
fun declare_real name default = real (declare name (Real o default));
fun declare_string name default = string (declare name (String o default));


(* system options *)

fun declare_option (name, pos) =
  let
    val typ = Options.default_typ name;
    val default =
      if typ = Options.boolT then fn _ => Bool (Options.default_bool name)
      else if typ = Options.intT then fn _ => Int (Options.default_int name)
      else if typ = Options.realT then fn _ => Real (Options.default_real name)
      else if typ = Options.stringT then fn _ => String (Options.default_string name)
      else error ("Unknown type for option " ^ quote name ^ Position.here pos ^ " : " ^ quote typ);
  in declare (name, pos) default end;

val declare_option_bool = bool o declare_option;
val declare_option_int = int o declare_option;
val declare_option_real = real o declare_option;
val declare_option_string = string o declare_option;

(*final declarations of this structure!*)
val get = get_ctxt;
val map = map_ctxt;
val put = put_ctxt;
val restore = restore_ctxt;

end;
