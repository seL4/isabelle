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
  val separator: string         (*single char!*)
  val unpack: string -> string list
  val pack: string list -> string
  val base: string -> string
  val qualified: string -> bool
  type T
  val dest: T -> string list
  val empty: T
  val extend: string list * T -> T
  val merge: T * T -> T
  val declared: T -> string -> bool
  val intern: T -> string -> string
  val extern: T -> string -> string
end;

structure NameSpace: NAME_SPACE =
struct


(** long identifiers **)

val separator = ".";

val unpack = space_explode separator;
val pack = space_implode separator;

val base = last_elem o unpack;
fun qualified name = length (unpack name) > 1;



(** name spaces **)

(* utils *)

fun prefixes1 [] = []
  | prefixes1 (x :: xs) = map (cons x) ([] :: prefixes1 xs);

fun suffixes1 xs = map rev (prefixes1 (rev xs));


(* datatype T *)

datatype T =
  NameSpace of string list list * string Symtab.table;

fun entries_of (NameSpace (entries, _)) = entries;
fun tab_of (NameSpace (_, tab)) = tab;

fun make entries =
  let
    fun accesses [] = []
      | accesses entry =
          let
            val p = pack entry;
            val (q, b) = split_last entry;
            val sfxs = suffixes1 entry;
            val pfxs = map (fn x => x @ [b]) (prefixes1 q);
          in
            map (rpair p o pack) (sfxs @ pfxs)
          end;
    val mapping = filter_out (op =) (distinct_fst_string (flat (map accesses entries)));
  in
    NameSpace (entries, Symtab.make mapping)
  end;

fun dest space = rev (map pack (entries_of space));



(* empty, extend, merge operations *)

val empty = make [];

fun extend (entries, space) =
  make (map unpack (rev entries) @ entries_of space);

fun merge (space1, space2) =    (*2nd overrides 1st*)
  make (merge_lists (entries_of space2) (entries_of space1));

fun declared space name = unpack name mem (entries_of space);


(* intern / extern names *)

fun intern space name =
  if_none (Symtab.lookup (tab_of space, name)) name;

fun extern space name =
  let
    fun try [] = "??" ^ separator ^ name      (*hidden name*)
      | try (nm :: nms) =
          if intern space nm = name then nm
          else try nms;
  in try (map pack (suffixes1 (unpack name))) end;


end;
