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
  type raw = value T
  val bool: raw -> bool T
  val int: raw -> int T
  val real: raw -> real T
  val string: raw -> string T
  val get: Proof.context -> 'a T -> 'a
  val map: 'a T -> ('a -> 'a) -> Proof.context -> Proof.context
  val put: 'a T -> 'a -> Proof.context -> Proof.context
  val get_global: theory -> 'a T -> 'a
  val map_global: 'a T -> ('a -> 'a) -> theory -> theory
  val put_global: 'a T -> 'a -> theory -> theory
  val get_generic: Context.generic -> 'a T -> 'a
  val map_generic: 'a T -> ('a -> 'a) -> Context.generic -> Context.generic
  val put_generic: 'a T -> 'a -> Context.generic -> Context.generic
  val declare_generic: {global: bool} -> string -> (Context.generic -> value) -> raw
  val declare_global: string -> (Context.generic -> value) -> raw
  val declare: string -> (Context.generic -> value) -> raw
  val name_of: 'a T -> string
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
  | print_value (Int i) = signed_string_of_int i
  | print_value (Real x) = signed_string_of_real x
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

fun type_check name f value =
  let
    val value' = f value;
    val _ = same_type value value' orelse
      error ("Ill-typed configuration option " ^ quote name ^ ": " ^
        print_type value ^ " expected,\nbut " ^ print_type value' ^ " was found");
  in value' end;


(* abstract configuration options *)

datatype 'a T = Config of
 {name: string,
  get_value: Context.generic -> 'a,
  map_value: ('a -> 'a) -> Context.generic -> Context.generic};

type raw = value T;

fun coerce make dest (Config {name, get_value, map_value}) = Config
 {name = name,
  get_value = dest o get_value,
  map_value = fn f => map_value (make o f o dest)};

val bool = coerce Bool (fn Bool b => b);
val int = coerce Int (fn Int i => i);
val real = coerce Real (fn Real x => x);
val string = coerce String (fn String s => s);

fun get_generic context (Config {get_value, ...}) = get_value context;
fun map_generic (Config {map_value, ...}) f context = map_value f context;
fun put_generic config value = map_generic config (K value);

fun get_ctxt ctxt = get_generic (Context.Proof ctxt);
fun map_ctxt config f = Context.proof_map (map_generic config f);
fun put_ctxt config value = map_ctxt config (K value);

fun get_global thy = get_generic (Context.Theory thy);
fun map_global config f = Context.theory_map (map_generic config f);
fun put_global config value = map_global config (K value);


(* context information *)

structure Value = Generic_Data
(
  type T = value Inttab.table;
  val empty = Inttab.empty;
  val extend = I;
  fun merge data = Inttab.merge (K true) data;
);

fun declare_generic {global} name default =
  let
    val id = serial ();

    fun get_value context =
      (case Inttab.lookup (Value.get context) id of
        SOME value => value
      | NONE => default context);

    fun update_value f context =
      Value.map (Inttab.update (id, type_check name f (get_value context))) context;

    fun map_value f (context as Context.Proof ctxt) =
          let val context' = update_value f context in
            if global andalso
              Context_Position.is_visible ctxt andalso
              print_value (get_value (Context.Theory (Context.theory_of context'))) <>
                print_value (get_value context')
            then
              (Context_Position.if_visible ctxt warning
                ("Ignoring local change of global option " ^ quote name); context)
            else context'
          end
      | map_value f context = update_value f context;
  in Config {name = name, get_value = get_value, map_value = map_value} end;

val declare_global = declare_generic {global = true};
val declare = declare_generic {global = false};

fun name_of (Config {name, ...}) = name;


(*final declarations of this structure!*)
val get = get_ctxt;
val map = map_ctxt;
val put = put_ctxt;

end;
