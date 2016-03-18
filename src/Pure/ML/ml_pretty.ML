(*  Title:      Pure/ML/ml_pretty.ML
    Author:     Makarius

Minimal support for raw ML pretty printing, notably for toplevel pp.
*)

signature ML_PRETTY =
sig
  datatype pretty =
    Block of (string * string) * bool * FixedInt.int * pretty list |
    String of string * FixedInt.int |
    Break of bool * FixedInt.int * FixedInt.int
  val block: pretty list -> pretty
  val str: string -> pretty
  val brk: FixedInt.int -> pretty
  val pair: ('a * int -> pretty) -> ('b * int -> pretty) -> ('a * 'b) * int -> pretty
  val enum: string -> string -> string -> ('a * int -> pretty) -> 'a list * int -> pretty
  val to_polyml: pretty -> PolyML.pretty
  val from_polyml: PolyML.pretty -> pretty
  val get_print_depth: unit -> int
  val print_depth: int -> unit
  val format_polyml: int -> PolyML.pretty -> string
  val format: int -> pretty -> string
  val make_string_fn: string -> string
end;

structure ML_Pretty: ML_PRETTY =
struct

(* datatype pretty *)

datatype pretty =
  Block of (string * string) * bool * FixedInt.int * pretty list |
  String of string * FixedInt.int |
  Break of bool * FixedInt.int * FixedInt.int;

fun block prts = Block (("", ""), false, 2, prts);
fun str s = String (s, FixedInt.fromInt (size s));
fun brk width = Break (false, width, 0);

fun pair pretty1 pretty2 ((x, y), depth: FixedInt.int) =
  block [str "(", pretty1 (x, depth), str ",", brk 1, pretty2 (y, depth - 1), str ")"];

fun enum sep lpar rpar pretty (args, depth: FixedInt.int) =
  let
    fun elems _ [] = []
      | elems 0 _ = [str "..."]
      | elems d [x] = [pretty (x, d)]
      | elems d (x :: xs) = pretty (x, d) :: str sep :: brk 1 :: elems (d - 1) xs;
  in block (str lpar :: (elems (FixedInt.max (depth, 0)) args @ [str rpar])) end;


(* convert *)

fun to_polyml (Break (false, width, offset)) = PolyML.PrettyBreak (width, offset)
  | to_polyml (Break (true, _, _)) =
      PolyML.PrettyBlock (0, false, [PolyML.ContextProperty ("fbrk", "")],
        [PolyML.PrettyString " "])
  | to_polyml (Block ((bg, en), consistent, ind, prts)) =
      let val context =
        (if bg = "" then [] else [PolyML.ContextProperty ("begin", bg)]) @
        (if en = "" then [] else [PolyML.ContextProperty ("end", en)])
      in PolyML.PrettyBlock (ind, consistent, context, map to_polyml prts) end
  | to_polyml (String (s, len)) =
      if len = FixedInt.fromInt (size s) then PolyML.PrettyString s
      else
        PolyML.PrettyBlock
          (0, false,
            [PolyML.ContextProperty ("length", FixedInt.toString len)], [PolyML.PrettyString s]);

val from_polyml =
  let
    fun convert _ (PolyML.PrettyBreak (width, offset)) = Break (false, width, offset)
      | convert _ (PolyML.PrettyBlock (_, _,
            [PolyML.ContextProperty ("fbrk", _)], [PolyML.PrettyString " "])) =
          Break (true, 1, 0)
      | convert len (PolyML.PrettyBlock (ind, consistent, context, prts)) =
          let
            fun property name default =
              (case List.find (fn PolyML.ContextProperty (a, _) => name = a | _ => false) context of
                SOME (PolyML.ContextProperty (_, b)) => b
              | _ => default);
            val bg = property "begin" "";
            val en = property "end" "";
            val len' = property "length" len;
          in Block ((bg, en), consistent, ind, map (convert len') prts) end
      | convert len (PolyML.PrettyString s) =
          String (s, FixedInt.fromInt (case Int.fromString len of SOME i => i | NONE => size s))
  in convert "" end;


(* default print depth *)

local
  val depth = Unsynchronized.ref 0;
in
  fun get_print_depth () = ! depth;
  fun print_depth n = (depth := n; PolyML.print_depth n);
  val _ = print_depth 20;
end;


(* format *)

fun format_polyml margin prt =
  let
    val result = Unsynchronized.ref [];
    val () = PolyML.prettyPrint (fn s => result := s :: ! result, margin) prt
  in String.concat (List.rev (! result)) end;

fun format margin = format_polyml margin o to_polyml;


(* make string *)

local
  fun pretty_string_of s = "(fn x => Pretty.string_of (Pretty.from_polyml (" ^ s ^ ")))";
  fun pretty_value depth = "PolyML.prettyRepresentation (x, FixedInt.fromInt (" ^ depth ^ "))";
in

fun make_string_fn local_env =
  if local_env <> "" then
    pretty_string_of (pretty_value (local_env ^ ".ML_print_depth ()"))
  else if List.exists (fn (a, _) => a = "Pretty") (#allStruct ML_Name_Space.global ()) then
    pretty_string_of (pretty_value "ML_Pretty.get_print_depth ()")
  else "(fn x => ML_Pretty.format_polyml 78 (" ^ pretty_value "ML_Pretty.get_print_depth ()" ^ "))";

end;

end;
