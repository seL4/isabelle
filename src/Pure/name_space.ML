(*  Title:      Pure/name_space.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Hierarchically structured name spaces.

More general than ML-like nested structures, but also slightly more
ad-hoc.  Does not support absolute addressing.  Unknown names are
implicitely considered to be declared outermost.
*)

signature NAME_SPACE =
sig
  val separator: string                 (*single char!*)
  val append: string -> string -> string
  val unpack: string -> string list
  val pack: string list -> string
  val base: string -> string
  val qualified: string -> bool
  type T
  val empty: T
  val extend: T * string list -> T
  val merge: T * T -> T
  val intern: T -> string -> string
  val extern: T -> string -> string
  val dest: T -> (string * string list) list
end;

structure NameSpace: NAME_SPACE =
struct


(** utils **)

fun prefixes1 [] = []
  | prefixes1 (x :: xs) = map (cons x) ([] :: prefixes1 xs);

fun suffixes1 xs = map rev (prefixes1 (rev xs));



(** long identifiers **)

val separator = ".";

fun append name1 name2 = name1 ^ separator ^ name2;

val unpack = space_explode separator;
val pack = space_implode separator;

val base = last_elem o unpack;
fun qualified name = length (unpack name) > 1;

fun accesses name =
  let
    val uname = unpack name;
    val (q, b) = split_last uname;
    val sfxs = suffixes1 uname;
    val pfxs = map (fn x => x @ [b]) (prefixes1 q);
  in
    map (rpair name o pack) (sfxs @ pfxs)
  end;



(** name spaces **)

(* datatype T *)

datatype T =
  NameSpace of string Symtab.table;

val empty = NameSpace Symtab.empty;


(* extend, merge operations *)

fun add (tab, entry) = Symtab.update (entry, tab);

fun extend (NameSpace tab, names) =
  NameSpace (foldl add (tab, flat (map accesses names)));

fun merge (NameSpace tab1, NameSpace tab2) =    (*2nd overrides 1st*)
  NameSpace (foldl add (tab1, Symtab.dest tab2));


(* intern / extern names *)

fun intern (NameSpace tab) name =
  if_none (Symtab.lookup (tab, name)) name;

fun extern space name =
  let
    fun try [] = "??" ^ separator ^ name      (*hidden name*)
      | try (nm :: nms) =
          if intern space nm = name then nm
          else try nms;
  in try (map pack (suffixes1 (unpack name))) end;


(* dest *)

fun dest (NameSpace tab) =
  map (apsnd (sort (int_ord o pairself size)))
    (Symtab.dest (Symtab.make_multi (map swap (Symtab.dest tab))));


end;
