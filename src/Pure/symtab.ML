(*  Title:      Pure/symtab.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1989  University of Cambridge

Unbalanced binary trees indexed by strings; no way to delete an entry.
*)

signature SYMTAB =
sig
  exception DUPLICATE of string
  exception DUPS of string list
  type 'a table
  val null: 'a table
  val is_null: 'a table -> bool
  val lookup: 'a table * string -> 'a option
  val find_first: (string * 'a -> bool) -> 'a table -> (string * 'a) option
  val update: (string * 'a) * 'a table -> 'a table
  val update_new: (string * 'a) * 'a table -> 'a table
  val map: ('a -> 'b) -> 'a table -> 'b table
  val balance: 'a table -> 'a table
  val st_of_declist: (string list * 'a) list * 'a table -> 'a table
  val make: (string * 'a) list -> 'a table
  val dest: 'a table -> (string * 'a) list
  val extend: ('a * 'a -> bool) -> 'a table * (string * 'a) list -> 'a table
  val extend_new: 'a table * (string * 'a) list -> 'a table
  val merge: ('a * 'a -> bool) -> 'a table * 'a table -> 'a table
  val lookup_multi: 'a list table * string -> 'a list
  val make_multi: (string * 'a) list -> 'a list table
  val dest_multi: 'a list table -> (string * 'a) list
end;

structure Symtab: SYMTAB =
struct

(*symbol table errors, such as from update_new*)
exception DUPLICATE of string;
exception DUPS of string list;

datatype 'a table = Tip | Branch of (string * 'a * 'a table * 'a table);


val null = Tip;

fun is_null Tip = true
  | is_null _ = false;


fun lookup (symtab: 'a table, key: string) : 'a option =
  let fun look  Tip  = None
        | look (Branch (key', entry, left, right)) =
            if      key < key' then look left
            else if key' < key then look right
            else  Some entry
  in look symtab end;


fun find_first _ Tip = None
  | find_first pred (Branch (key, entry, left, right)) =
      (case find_first pred left of
        None =>
          if pred (key, entry) then Some (key, entry)
          else find_first pred right
      | some => some);


(*update, allows overwriting of an entry*)
fun update ((key: string, entry: 'a), symtab : 'a table)
  : 'a table =
  let fun upd  Tip  = Branch (key, entry, Tip, Tip)
        | upd (Branch(key', entry', left, right)) =
            if      key < key' then Branch (key', entry', upd left, right)
            else if key' < key then Branch (key', entry', left, upd right)
            else                    Branch (key, entry, left, right)
  in  upd symtab  end;

(*Like update but fails if key is already defined in table.*)
fun update_new ((key: string, entry: 'a), symtab : 'a table)
  : 'a table =
  let fun upd Tip = Branch (key, entry, Tip, Tip)
        | upd (Branch(key', entry', left, right)) =
            if      key < key' then Branch (key', entry', upd left, right)
            else if key' < key then Branch (key', entry', left, upd right)
            else  raise DUPLICATE(key)
  in  upd symtab  end;


(*conversion of symbol table to sorted association list*)
fun dest (symtab : 'a table) : (string * 'a) list =
  let fun ali (symtab, cont) = case symtab of
                Tip => cont
        | Branch (key, entry, left, right) =>
            ali(left, (key, entry) :: ali(right, cont))
  in  ali (symtab, [])  end;


(*Make a balanced tree of the first n members of the sorted alist (sal).
  Utility for the function balance.*)
fun bal_of (sal, 0) = Tip
  | bal_of (sal, n) =
      let val mid = n div 2
      in  case  drop (mid, sal) of
            [] => bal_of (sal, mid)   (*should not occur*)
          | ((key, entry):: pairs) =>
                Branch(key, entry, bal_of(sal, mid), bal_of(pairs, n-mid-1))
      end;


fun balance symtab =
  let val sal = dest symtab
  in  bal_of (sal, length sal)  end;


(*A "declaration" associates the same entry with a list of keys;
  does not allow overwriting of an entry*)
fun decl_update_new ((keys : string list, entry: 'a), symtab)
  : 'a table =
  let fun decl (key, symtab) = update_new ((key, entry), symtab)
  in foldr decl (keys, symtab) end;

(*Addition of a list of declarations to a symbol table*)
fun st_of_declist (dl, symtab) =
  balance (foldr decl_update_new (dl, symtab));


(* make, extend, merge tables *)

fun eq_pair eq ((key1, entry1), (key2, entry2)) =
  key1 = key2 andalso eq (entry1, entry2);

fun make alst =
  (case gen_duplicates eq_fst alst of
    [] => balance (foldr update_new (alst, Tip))
  | dups => raise DUPS (map fst dups));

fun extend eq (tab, alst) =
  generic_extend (eq_pair eq) dest make tab alst;

val extend_new = extend (K false);

fun merge eq (tab1, tab2) =
  generic_merge (eq_pair eq) dest make tab1 tab2;


(* tables with multiple entries per key *)
(*order of entries with same key is preserved*)

fun lookup_multi (tab, key) =
  (case lookup (tab, key) of
    Some entries => entries
  | None => []);

fun cons_entry ((key, entry), tab) =
  update ((key, entry :: lookup_multi (tab, key)), tab);

fun make_multi alst =
  balance (foldr cons_entry (alst, Tip));

fun dest_multi tab =
  flat (map (fn (key, entries) => map (pair key) entries) (dest tab));


(* map tables *)

fun map _ Tip = Tip
  | map f (Branch (key, entry, left, right)) =
      Branch (key, f entry, map f left, map f right);

end;

