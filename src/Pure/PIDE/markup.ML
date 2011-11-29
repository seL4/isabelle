(*  Title:      Pure/PIDE/markup.ML
    Author:     Makarius

Generic markup elements.
*)

signature MARKUP =
sig
  val parse_int: string -> int
  val print_int: int -> string
  type T = string * Properties.T
  val empty: T
  val is_empty: T -> bool
  val properties: Properties.T -> T -> T
  val nameN: string
  val name: string -> T -> T
  val kindN: string
  val no_output: Output.output * Output.output
  val default_output: T -> Output.output * Output.output
  val add_mode: string -> (T -> Output.output * Output.output) -> unit
  val output: T -> Output.output * Output.output
  val enclose: T -> Output.output -> Output.output
  val markup: T -> string -> string
  val markup_only: T -> string
end;

structure Markup: MARKUP =
struct

(** markup elements **)

(* integers *)

fun parse_int s =
  let val i = Int.fromString s in
    if is_none i orelse String.isPrefix "~" s
    then raise Fail ("Bad integer: " ^ quote s)
    else the i
  end;

val print_int = signed_string_of_int;


(* basic markup *)

type T = string * Properties.T;

val empty = ("", []);

fun is_empty ("", _) = true
  | is_empty _ = false;


fun properties more_props ((elem, props): T) =
  (elem, fold_rev Properties.put more_props props);


(* misc properties *)

val nameN = "name";
fun name a = properties [(nameN, a)];

val kindN = "kind";



(** print mode operations **)

val no_output = ("", "");
fun default_output (_: T) = no_output;

local
  val default = {output = default_output};
  val modes = Synchronized.var "Markup.modes" (Symtab.make [("", default)]);
in
  fun add_mode name output =
    Synchronized.change modes (Symtab.update_new (name, {output = output}));
  fun get_mode () =
    the_default default
      (Library.get_first (Symtab.lookup (Synchronized.value modes)) (print_mode_value ()));
end;

fun output m = if is_empty m then no_output else #output (get_mode ()) m;

val enclose = output #-> Library.enclose;

fun markup m =
  let val (bg, en) = output m
  in Library.enclose (Output.escape bg) (Output.escape en) end;

fun markup_only m = markup m "";

end;
