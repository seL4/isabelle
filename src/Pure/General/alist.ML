(*  Title:      Pure/General/alist.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Association lists -- lists of (key, value) pairs with unique keys.
A light-weight representation of finite mappings;
see also Pure/General/table.ML for a more scalable implementation.
*)

signature ALIST =
sig
  exception DUP
  val lookup: ('a * 'b -> bool) -> ('b * 'c) list -> 'a -> 'c option
  val defined: ('a * 'b -> bool) -> ('b * 'c) list -> 'a -> bool
  val update: ('a * 'a -> bool) -> ('a * 'b)
    -> ('a * 'b) list -> ('a * 'b) list
  val default: ('a * 'a -> bool) -> ('a * 'b)
    -> ('a * 'b) list -> ('a * 'b) list
  val delete: ('a * 'b -> bool) -> 'a
    -> ('b * 'c) list -> ('b * 'c) list
  val map_entry: ('a * 'b -> bool) -> 'a -> ('c -> 'c)
    -> ('b * 'c) list -> ('b * 'c) list
  val make: ('a -> 'b) -> 'a list -> ('a * 'b) list
  val join: ('a * 'a -> bool) -> ('a -> 'b * 'b -> 'b option) ->
    ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list         (*exception DUP*)
  val merge: ('a * 'a -> bool) -> ('b * 'b -> bool)
    -> ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list      (*exception DUP*)
  val find: ('a * 'b -> bool) -> ('c * 'b) list -> 'a -> 'c list
  val string_of_alist: ('a -> string) -> ('b -> string) -> ('a * 'b) list -> string
end;

structure AList: ALIST =
struct

fun find_index eq xs key =
  let
    fun find [] _ = 0
      | find ((key', value)::xs) i =
          if eq (key, key')
          then i
          else find xs (i+1);
  in find xs 1 end;

fun lookup _ [] _ = NONE
  | lookup eq ((key, value)::xs) key' =
      if eq (key', key) then SOME value
      else lookup eq xs key';

fun defined _ [] _ = false
  | defined eq ((key, value)::xs) key' =
      eq (key', key) orelse defined eq xs key';

fun update eq (x as (key, value)) xs =
  let
    val i = find_index eq xs key;
    fun upd 1 (_::xs) = (x::xs)
      | upd i (x::xs) = x :: upd (i-1) xs;
  in if i = 0 then x::xs else upd i xs end;

fun default eq (key, value) xs =
  if defined eq xs key then xs else (key, value)::xs;

fun delete eq key xs =
  let
    val i = find_index eq xs key;
    fun del 1 (_::xs) = xs
      | del i (x::xs) = x :: del (i-1) xs;
  in if i = 0 then xs else del i xs end;

fun map_entry eq key f xs =
  let
    val i = find_index eq xs key;
    fun mapp 1 ((x as (key, value))::xs) = (key, f value) :: xs
      | mapp i (x::xs) = x :: mapp (i-1) xs;
  in if i = 0 then xs else mapp i xs end;

exception DUP;

fun join eq f (xs, ys) =
  let
    fun add (key, x) xs =
      (case lookup eq xs key of
        NONE => update eq (key, x) xs
      | SOME y =>
          (case f key (y, x) of
            SOME z => update eq (key, z) xs
          | NONE => raise DUP));
  in fold_rev add xs ys end;

fun merge eq_key eq_val (xs, ys) =
  let
    fun add (x as (key, value)) ys =
      case lookup eq_key ys key
       of NONE => update eq_key x ys
        | SOME value' =>
            if eq_val (value, value')
            then ys
            else raise DUP;
  in fold_rev add xs ys end;

fun make keyfun =
  let fun keypair x = (x, keyfun x)
  in map keypair end;

fun find eq [] _ = []
  | find eq ((key, value) :: xs) value' =
      let
        val values = find eq xs value';
      in if eq (value', value) then key :: values else values end;

fun string_of_alist string_of_key string_of_value =
  map (fn (key, value) => string_of_key key ^ " -> " ^ string_of_value value)
  #> commas
  #> enclose "[" "]"

end;
