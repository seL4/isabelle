(*  Title:      Pure/name.ML
    ID:         $Id$
    Author:     Makarius

Names of basic logical entities (variables etc.).  Generic name bindings.
*)

signature NAME =
sig
  val uu: string
  val aT: string
  val bound: int -> string
  val is_bound: string -> bool
  val internal: string -> string
  val dest_internal: string -> string
  val skolem: string -> string
  val dest_skolem: string -> string
  val clean_index: string * int -> string * int
  val clean: string -> string
  type context
  val context: context
  val make_context: string list -> context
  val declare: string -> context -> context
  val is_declared: context -> string -> bool
  val invents: context -> string -> int -> string list
  val names: context -> string -> 'a list -> (string * 'a) list
  val invent_list: string list -> string -> int -> string list
  val variants: string list -> context -> string list * context
  val variant_list: string list -> string list -> string list
  val variant: string list -> string -> string
  type binding
  val binding_pos: string * Position.T -> binding
  val binding: string -> binding
  val no_binding: binding
  val name_of: binding -> string
  val pos_of: binding -> Position.T
  val map_name: (string -> string) -> binding -> binding
  val qualified: string -> binding -> binding
end;

structure Name: NAME =
struct

(** common defaults **)

val uu = "uu";
val aT = "'a";



(** special variable names **)

(* encoded bounds *)

(*names for numbered variables --
  preserves order wrt. int_ord vs. string_ord, avoids allocating new strings*)

val small_int = Vector.tabulate (1000, fn i =>
  let val leading = if i < 10 then "00" else if i < 100 then "0" else ""
  in ":" ^ leading ^ string_of_int i end);

fun bound n =
  if n < 1000 then Vector.sub (small_int, n)
  else ":" ^ bound (n div 1000) ^ Vector.sub (small_int, n mod 1000);

val is_bound = String.isPrefix ":";


(* internal names *)

val internal = suffix "_";
val dest_internal = unsuffix "_";

val skolem = suffix "__";
val dest_skolem = unsuffix "__";

fun clean_index (x, i) =
  (case try dest_internal x of
    NONE => (x, i)
  | SOME x' => clean_index (x', i + 1));

fun clean x = #1 (clean_index (x, 0));



(** generating fresh names **)

(* context *)

datatype context =
  Context of string option Symtab.table;    (*declared names with latest renaming*)

fun declare x (Context tab) =
  Context (Symtab.default (clean x, NONE) tab);

fun declare_renaming (x, x') (Context tab) =
  Context (Symtab.update (clean x, SOME (clean x')) tab);

fun is_declared (Context tab) = Symtab.defined tab;
fun declared (Context tab) = Symtab.lookup tab;

val context = Context Symtab.empty |> fold declare ["", "'"];
fun make_context used = fold declare used context;


(* invents *)

fun invents ctxt =
  let
    fun invs _ 0 = []
      | invs x n =
          let val x' = Symbol.bump_string x in
            if is_declared ctxt x then invs x' n
            else x :: invs x' (n - 1)
          end;
  in invs o clean end;

fun names ctxt x xs = invents ctxt x (length xs) ~~ xs;

val invent_list = invents o make_context;


(* variants *)

(*makes a variant of a name distinct from already used names in a
  context; preserves a suffix of underscores "_"*)
val variants = fold_map (fn name => fn ctxt =>
  let
    fun vary x =
      (case declared ctxt x of
        NONE => x
      | SOME x' => vary (Symbol.bump_string (the_default x x')));

    val (x, n) = clean_index (name, 0);
    val (x', ctxt') =
      if not (is_declared ctxt x) then (x, declare x ctxt)
      else
        let
          val x0 = Symbol.bump_init x;
          val x' = vary x0;
          val ctxt' = ctxt
            |> x0 <> x' ? declare_renaming (x0, x')
            |> declare x';
        in (x', ctxt') end;
  in (x' ^ replicate_string n "_", ctxt') end);

fun variant_list used names = #1 (make_context used |> variants names);
fun variant used = singleton (variant_list used);



(** generic name bindings **)

datatype binding = Binding of string * Position.T;

val binding_pos = Binding;
fun binding name = binding_pos (name, Position.none);
val no_binding = binding "";

fun name_of (Binding (name, _)) = name;
fun pos_of (Binding (_, pos)) = pos;

fun map_name f (Binding (name, pos)) = Binding (f name, pos);
val qualified = map_name o NameSpace.qualified;

end;
