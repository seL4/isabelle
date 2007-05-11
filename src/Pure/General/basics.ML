(*  Title:      Pure/General/basics.ML
    ID:         $Id$
    Author:     Florian Haftmann and Makarius, TU Muenchen

Fundamental concepts.
*)

infix 1 |> |-> |>> ||> ||>>
infix 1 #> #-> #>> ##> ##>>

signature BASICS =
sig
  (*functions*)
  val |> : 'a * ('a -> 'b) -> 'b
  val |-> : ('c * 'a) * ('c -> 'a -> 'b) -> 'b
  val |>> : ('a * 'c) * ('a -> 'b) -> 'b * 'c
  val ||> : ('c * 'a) * ('a -> 'b) -> 'c * 'b
  val ||>> : ('c * 'a) * ('a -> 'd * 'b) -> ('c * 'd) * 'b
  val #> : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
  val #-> : ('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd
  val #>> : ('a -> 'c * 'b) * ('c -> 'd) -> 'a -> 'd * 'b
  val ##> : ('a -> 'c * 'b) * ('b -> 'd) -> 'a -> 'c * 'd
  val ##>> : ('a -> 'c * 'b) * ('b -> 'e * 'd) -> 'a -> ('c * 'e) * 'd
  val ` : ('b -> 'a) -> 'b -> 'a * 'b
  val tap: ('b -> 'a) -> 'b -> 'b
  val flip: ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

  (*options*)
  val is_some: 'a option -> bool
  val is_none: 'a option -> bool
  val the: 'a option -> 'a
  val these: 'a list option -> 'a list
  val the_list: 'a option -> 'a list
  val the_default: 'a -> 'a option -> 'a
  val perhaps: ('a -> 'a option) -> 'a -> 'a

  (*partiality*)
  val try: ('a -> 'b) -> 'a -> 'b option
  val can: ('a -> 'b) -> 'a -> bool

  (*lists*)
  val cons: 'a -> 'a list -> 'a list
  val dest: 'a list -> 'a * 'a list
  val append: 'a list -> 'a list -> 'a list
  val fold: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_rev: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_map: ('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b
  val unfold: int -> ('b -> 'a * 'b) -> 'b -> 'a list * 'b
  val unfold_rev: int -> ('b -> 'a * 'b) -> 'b -> 'a list * 'b
end;

structure Basics: BASICS =
struct

(* functions *)

(*application and structured results*)
fun x |> f = f x;
fun (x, y) |-> f = f x y;
fun (x, y) |>> f = (f x, y);
fun (x, y) ||> f = (x, f y);
fun (x, y) ||>> f = let val (z, y') = f y in ((x, z), y') end;

(*composition and structured results*)
fun (f #> g) x   = x |> f |> g;
fun (f #-> g) x  = x |> f |-> g;
fun (f #>> g) x  = x |> f |>> g;
fun (f ##> g) x  = x |> f ||> g;
fun (f ##>> g) x = x |> f ||>> g;

(*result views*)
fun `f = fn x => (f x, x);
fun tap f = fn x => (f x; x);

fun flip f x y = f y x;


(* options *)

fun is_some (SOME _) = true
  | is_some NONE = false;

fun is_none (SOME _) = false
  | is_none NONE = true;

fun the (SOME x) = x
  | the NONE = raise Option;

fun these (SOME x) = x
  | these _ = [];

fun the_list (SOME x) = [x]
  | the_list _ = []

fun the_default x (SOME y) = y
  | the_default x _ = x;

fun perhaps f x = the_default x (f x);


(* partiality *)

exception Interrupt = Interrupt;   (*signals intruding execution :-[*)

fun try f x = SOME (f x)
  handle Interrupt => raise Interrupt | _ => NONE;

fun can f x = is_some (try f x);


(* lists *)

fun cons x xs = x :: xs;

fun dest (x :: xs) = (x, xs)
  | dest [] = raise Empty;

fun append xs ys = xs @ ys;


(* fold *)

fun fold f =
  let
    fun fld [] y = y
      | fld (x :: xs) y = fld xs (f x y);
  in fld end;

fun fold_rev f =
  let
    fun fld [] y = y
      | fld (x :: xs) y = f x (fld xs y);
  in fld end;

fun fold_map f =
  let
    fun fld [] y = ([], y)
      | fld (x :: xs) y =
          let
            val (x', y') = f x y;
            val (xs', y'') = fld xs y';
          in (x' :: xs', y'') end;
  in fld end;


(* unfold -- with optional limit *)

fun unfold lim f =
  let
    fun unfld 0 ys x = (ys, x)
      | unfld n ys x =
          (case try f x of
            NONE => (ys, x)
          | SOME (y, x') => unfld (n - 1) (y :: ys) x');
  in unfld lim [] end;

fun unfold_rev lim f =
  let
    fun unfld 0 x = ([], x)
      | unfld n x =
          (case try f x of
            NONE => ([], x)
          | SOME (y, x') => unfld (n - 1) x' |>> cons y);
  in unfld lim end;

end;

open Basics;
