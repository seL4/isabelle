(*  Title:      Pure/name_space.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Hierarchically structured name spaces.

More general than ML-like nested structures, but also slightly more
ad-hoc.  Does not support absolute addressing.  Unknown names are
implicitely considered to be declared outermost.

TODO:
  - absolute paths?
*)

signature NAME_SPACE =
sig
  val separator: string		(*single char!*)
  val unpack: string -> string list
  val pack: string list -> string
  val base: string -> string
  val qualified: string -> bool
  type T
  val dest: T -> string list
  val empty: T
  val extend: string list * T -> T
  val merge: T * T -> T
  val lookup: T -> string -> string
  val prune: T -> string -> string
end;

structure NameSpace: NAME_SPACE =
struct


(** long identifiers **)

val separator = "'";

fun unpack_aux name =
  let
    (*handle trailing separators gracefully*)
    val (chars, seps) = take_suffix (equal separator) name;
    fun expl chs =
      (case take_prefix (not_equal separator) chs of
        (cs, []) => [implode (cs @ seps)]
      | (cs, _ :: cs') => implode cs :: expl cs');
  in expl chars end;

val unpack = unpack_aux o explode;
val pack = space_implode separator;

val base = last_elem o unpack;

fun qualified name =
  let val chs = explode name in
    exists (equal separator) chs andalso (length (unpack_aux chs) > 1)
  end;



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
    fun accesses entry =
      let val packed = pack entry in
        map (rpair packed o pack) (suffixes1 entry)
      end;
    val mapping = gen_distinct eq_fst (flat (map accesses entries));
  in
    NameSpace (entries, Symtab.make mapping)
  end;

fun dest space = rev (map pack (entries_of space));



(* empty, extend, merge operations *)

val empty = make [];

fun extend (entries, space) =
  make (map unpack (rev entries) @ entries_of space);

fun merge (space1, space2) =
  make (merge_lists (entries_of space1) (entries_of space2));


(* lookup / prune names *)

fun lookup space name =
  if_none (Symtab.lookup (tab_of space, name)) name;

fun prune space name =
  if not (qualified name) then name
  else
    let
      fun try [] = name
        | try (nm :: nms) =
            if lookup space nm = name then nm
            else try nms;
    in try (map pack (suffixes1 (unpack name))) end;


end;
