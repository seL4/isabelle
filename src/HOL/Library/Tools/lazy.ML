(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

signature LAZY =
sig
  type 'a lazy;
  val lazy : (unit -> 'a) -> 'a lazy;
  val force : 'a lazy -> 'a;
  val peek : 'a lazy -> 'a option
  val termify_lazy :
   (string -> 'typerep -> 'term) ->
   ('term -> 'term -> 'term) ->
   (string -> 'typerep -> 'term -> 'term) ->
   'typerep -> ('typerep -> 'typerep -> 'typerep) -> ('typerep -> 'typerep) ->
   ('a -> 'term) -> 'typerep -> 'a lazy -> 'term -> 'term;
end;

structure Lazy : LAZY =
struct

datatype 'a content =
   Delay of unit -> 'a
 | Value of 'a
 | Exn of exn;

datatype 'a lazy = Lazy of 'a content ref;

fun lazy f = Lazy (ref (Delay f));

fun force (Lazy x) = case !x of
   Delay f => (
     let val res = f (); val _ = x := Value res; in res end
     handle exn => (x := Exn exn; raise exn))
  | Value x => x
  | Exn exn => raise exn;

fun peek (Lazy x) = case !x of
    Value x => SOME x
  | _ => NONE;

fun termify_lazy const app abs unitT funT lazyT term_of T x _ =
  app (const "Code_Lazy.delay" (funT (funT unitT T) (lazyT T)))
    (case peek x of SOME y => abs "_" unitT (term_of y)
     | _ => const "Pure.dummy_pattern" (funT unitT T));

end;
