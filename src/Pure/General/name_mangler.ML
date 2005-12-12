(*  Title:      Pure/General/name_mangler.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Generic name mangler -- provides bijective mappings from any expressions
to strings and vice versa.
*)

signature NAME_MANGLER =
sig
  type ctxt
  type src
  type T
  exception DUP of src
  val mk_unique: ('b * 'b -> bool) -> ('a * int -> 'b) -> 'a -> 'b list -> 'b * 'b list
  val get: ctxt -> T -> src -> string
  val rev: ctxt -> T -> string -> src
  val declare: ctxt -> src -> T -> string * T
end;

functor NameManglerFun (
  type ctxt
  type src
  val ord: src * src -> order
  val mk: ctxt -> src * int -> string
  val is_valid: ctxt -> string -> bool
  val maybe_unique: ctxt -> src -> string option
  val re_mangle: ctxt -> string -> src
) : NAME_MANGLER =
struct

structure Srctab = TableFun (
  type key = src
  val ord = ord
);

type ctxt = ctxt;
type src = src;
type T = string Srctab.table * src Symtab.table;

exception DUP of src;

fun mk_unique eq mk seed used =
  let
    fun mk_name i =
      let
        val name = mk (seed, i)
      in
        if member eq used name
        then mk_name (i+1)
        else name
      end;
    val name = mk_name 0;
  in (name, name :: used) end;

fun get ctxt (tab_f, _) x =
  case Srctab.lookup tab_f x
   of SOME s => s
    | NONE => (the o maybe_unique ctxt) x;

fun rev ctxt (_, tab_r) s =
  case Symtab.lookup tab_r s
   of SOME x => x
    | NONE => re_mangle ctxt s;

fun declare ctxt x (tabs as (tab_f, tab_r)) =
  case maybe_unique ctxt x
   of NONE => 
        let
          fun mk_it (seed, i) =
            let
              val name = mk ctxt (seed, i)
            in if is_valid ctxt name then name
            else mk_it (seed, i+1) end;
          val name = (fst oooo mk_unique) (op =) mk_it x [];
        in
          (name,
           (tab_f |> Srctab.update (x, name),
            tab_r |> Symtab.update (name, x)))
        end
    | SOME s => (s, tabs)

end;