(*  Title:      Pure/General/alist.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Association lists -- lists of (key, value) pairs with unique keys.
A light-weight representation of finite mappings;
see also Pure/General/table.ML for a more scalable implementation.
*)

signature ALIST =
sig
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
  val find: ('a * 'b -> bool) -> ('c * 'b) list -> 'a -> 'c list
end;

structure AList: ALIST =
struct

fun lookup _ [] _ = NONE
  | lookup eq ((key, value)::xs) key' =
      if eq (key', key) then SOME value
      else lookup eq xs key';

fun defined _ [] _ = false
  | defined eq ((key, value)::xs) key' =
      eq (key', key) orelse defined eq xs key';

fun update eq (key, value) xs =
  let
    fun upd ((x as (key', _))::xs) =
      if eq (key, key')
      then (key, value)::xs
      else x :: upd xs
  in if defined eq xs key then upd xs else (key, value)::xs end;

fun default eq (key, value) xs =
  if defined eq xs key then xs else (key, value)::xs;

fun delete eq key xs =
  let
    fun del ((x as (key', _))::xs) =
      if eq (key, key') then xs
      else x :: del xs;
  in if defined eq xs key then del xs else xs end;

fun map_entry eq key' f xs =
  let
    fun mapp ((x as (key, value))::xs) =
      if eq (key', key) then (key, f value)::xs
      else x :: mapp xs
  in if defined eq xs key' then mapp xs else xs end;

fun make keyfun =
  let fun keypair x = (x, keyfun x)
  in map keypair end;

fun find eq [] _ = []
  | find eq ((key, value) :: xs) value' =
      let
        val values = find eq xs value'
      in if eq (value', value) then key :: values else values end;

end;
