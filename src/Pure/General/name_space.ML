(*  Title:      Pure/General/name_space.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Hierarchically structured name spaces.

More general than ML-like nested structures, but also slightly more
ad-hoc.  Does not support absolute addressing.  Unknown names are
implicitely considered to be declared outermost.
*)

signature NAME_SPACE =
sig
  val separator: string                 (*single char!*)
  val hidden: string -> string
  val append: string -> string -> string
  val unpack: string -> string list
  val pack: string list -> string
  val base: string -> string
  val map_base: (string -> string) -> string -> string
  val is_qualified: string -> bool
  val accesses: string -> string list
  type T
  val empty: T
  val extend: T * string list -> T
  val merge: T * T -> T
  val hide: T * string list -> T
  val intern: T -> string -> string
  val extern: T -> string -> string
  val long_names: bool ref
  val cond_extern: T -> string -> string
  val cond_extern_table: T -> 'a Symtab.table -> (string * 'a) list
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
fun hidden name = "??." ^ name;
fun is_hidden name = (case explode name of "?" :: "?" :: "." :: _ => true | _ => false);

fun append name1 name2 = name1 ^ separator ^ name2;

val unpack = space_explode separator;
val pack = space_implode separator;

val base = last_elem o unpack;

fun map_base f name =
  let val uname = unpack name
  in pack (map_nth_elem (length uname - 1) f uname) end;

fun is_qualified name = length (unpack name) > 1;

fun accesses name =
  let
    val uname = unpack name;
    val (q, b) = split_last uname;
    val sfxs = suffixes1 uname;
    val pfxs = map (fn x => x @ [b]) (prefixes1 q);
  in map pack (sfxs @ pfxs) end;



(** name spaces **)

(* basic operations *)

fun map_space f xname tab =
  Symtab.update ((xname, f (if_none (Symtab.lookup (tab, xname)) ([], []))), tab);

fun change f xname (name, tab) =
  map_space (fn (names, names') => (f names name, names')) xname tab;

fun change' f xname (name', tab) =
  map_space (fn (names, names') => (names, f names' name')) xname tab;

fun del names nm = if nm mem_string names then Library.gen_rem (op =) (names, nm) else names;
fun add names nm = nm :: del names nm;


(* datatype T *)

datatype T =
  NameSpace of (string list * string list) Symtab.table;

val empty = NameSpace Symtab.empty;


(* extend *)            (*later entries preferred*)

fun extend_aux (name, tab) =
  if is_hidden name then
    error ("Attempt to declare hidden name " ^ quote name)
  else foldl (fn (tb, xname) => change add xname (name, tb)) (tab, accesses name);

fun extend (NameSpace tab, names) = NameSpace (foldr extend_aux (names, tab));


(* merge *)             (*1st preferred over 2nd*)

fun merge_aux (tab, (xname, (names, names'))) =
  foldr (change add xname) (names, foldr (change' add xname) (names', tab));

fun merge (NameSpace tab1, NameSpace tab2) =
  NameSpace (Symtab.foldl merge_aux (tab2, tab1));


(* hide *)

fun hide_aux (name, tab) =
  if not (is_qualified name) then
    error ("Attempt to hide global name " ^ quote name)
  else if is_hidden name then
    error ("Attempt to hide hidden name " ^ quote name)
  else (change' add name (name,
    foldl (fn (tb, xname) => change del xname (name, tb)) (tab, accesses name)));

fun hide (NameSpace tab, names) = NameSpace (foldr hide_aux (names, tab));


(* intern / extern names *)

fun lookup (NameSpace tab) xname =
  (case Symtab.lookup (tab, xname) of
    None => (xname, true)
  | Some ([name], _) => (name, true)
  | Some (name :: _, _) => (name, false)
  | Some ([], []) => (xname, true)
  | Some ([], name' :: _) => (hidden name', true));

fun intern spc xname = #1 (lookup spc xname);

fun extern space name =
  let
    fun try [] = hidden name
      | try (nm :: nms) =
          let val (full_nm, uniq) = lookup space nm
          in if full_nm = name andalso uniq then nm else try nms end
  in try (map pack (suffixes1 (unpack name))) end;

(*prune names on output by default*)
val long_names = ref false;

fun cond_extern space = if ! long_names then I else extern space;

fun cond_extern_table space tab =
  Library.sort_wrt #1 (map (apfst (cond_extern space)) (Symtab.dest tab));


(* dest *)

fun dest_entry (xname, ([], _)) = None
  | dest_entry (xname, (name :: _, _)) = Some (name, xname);

fun dest (NameSpace tab) =
  map (apsnd (sort (int_ord o pairself size)))
    (Symtab.dest (Symtab.make_multi (mapfilter dest_entry (Symtab.dest tab))));


end;


val long_names = NameSpace.long_names;
