(*  Title:      Pure/System/options.ML
    Author:     Makarius

Stand-alone options with external string representation.
*)

signature OPTIONS =
sig
  type T
  val empty: T
  val bool: T -> string -> bool
  val int: T -> string -> int
  val real: T -> string -> real
  val string: T -> string -> string
  val declare: {name: string, typ: string, value: string} -> T -> T
  val decode: XML.body -> T
end;

structure Options: OPTIONS =
struct

(* representation *)

val boolT = "bool";
val intT = "int";
val realT = "real";
val stringT = "string";

datatype T = Options of {typ: string, value: string} Symtab.table;

val empty = Options Symtab.empty;


(* get *)

fun get T parse (Options tab) name =
  (case Symtab.lookup tab name of
    SOME {typ, value} =>
      if typ = T then
        (case parse value of
          SOME x => x
        | NONE =>
            error ("Malformed value for option " ^ quote name ^ " : " ^ T ^ " =\n" ^ quote value))
      else error ("Ill-typed option " ^ quote name ^ " : " ^ typ ^ " vs. " ^ T)
  | NONE => error ("Unknown option " ^ quote name));

val bool = get boolT Bool.fromString;
val int = get intT Int.fromString;
val real = get realT Real.fromString;
val string = get stringT SOME;


(* declare *)

fun declare {name, typ, value} (Options tab) =
  let
    val check_value =
      if typ = boolT then ignore oo bool
      else if typ = intT then ignore oo int
      else if typ = realT then ignore oo real
      else if typ = stringT then ignore oo string
      else error ("Unknown type for option " ^ quote name ^ " : " ^ quote typ);
    val options' = Options (Symtab.update_new (name, {typ = typ, value = value}) tab)
      handle Symtab.DUP _ => error ("Duplicate declaration of option " ^ quote name);
    val _ = check_value options' name;
  in options' end;


(* decode *)

fun decode body =
  fold (declare o (fn (name, typ, value) => {name = name, typ = typ, value = value}))
    (let open XML.Decode in list (triple string string string) end body) empty;

end;

