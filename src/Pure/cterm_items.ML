(*  Title:      Pure/cterm_items.ML
    Author:     Makarius

Scalable collections of term items: for type thm and cterm.
See als Pure/term_items.ML.
*)

structure Ctermtab:
sig
  include TABLE
  val cterm_cache: (cterm -> 'a) -> cterm -> 'a
end =
struct

structure Table = Table(type key = cterm val ord = Thm.fast_term_ord);
open Table;

fun cterm_cache f = Cache.create empty lookup update f;

end;


structure Thmtab:
sig
  include TABLE
  val thm_cache: (thm -> 'a) -> thm -> 'a
end =
struct

structure Table = Table(type key = thm val ord = Thm.thm_ord);
open Table;

fun thm_cache f = Cache.create empty lookup update f;

end;


structure Cterms: TERM_ITEMS = Term_Items(type key = cterm val ord = Thm.fast_term_ord);
