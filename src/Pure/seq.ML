(*  Title:      Pure/seq.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Unbounded sequences implemented by closures.  RECOMPUTES if sequence
is re-inspected.  Memoing, using polymorphic refs, was found to be
slower!  (More GCs)
*)

signature SEQ =
sig
  type 'a seq
  val make: (unit -> ('a * 'a seq) option) -> 'a seq
  val pull: 'a seq -> ('a * 'a seq) option
  val empty: 'a seq
  val cons: 'a * 'a seq -> 'a seq
  val single: 'a -> 'a seq
  val hd: 'a seq -> 'a
  val tl: 'a seq -> 'a seq
  val chop: int * 'a seq -> 'a list * 'a seq
  val list_of: 'a seq -> 'a list
  val of_list: 'a list -> 'a seq
  val map: ('a -> 'b) -> 'a seq -> 'b seq
  val mapp: ('a -> 'b) -> 'a seq -> 'b seq -> 'b seq
  val append: 'a seq * 'a seq -> 'a seq
  val filter: ('a -> bool) -> 'a seq -> 'a seq
  val flat: 'a seq seq -> 'a seq
  val interleave: 'a seq * 'a seq -> 'a seq
  val print: (int -> 'a -> unit) -> int -> 'a seq -> unit
  val it_right : ('a * 'b seq -> 'b seq) -> 'a seq * 'b seq -> 'b seq
  val succeed: 'a -> 'a seq
  val fail: 'a -> 'b seq
  val THEN: ('a -> 'b seq) * ('b -> 'c seq) -> 'a -> 'c seq
  val ORELSE: ('a -> 'b seq) * ('a -> 'b seq) -> 'a -> 'b seq
  val APPEND: ('a -> 'b seq) * ('a -> 'b seq) -> 'a -> 'b seq
  val EVERY: ('a -> 'a seq) list -> 'a -> 'a seq
  val FIRST: ('a -> 'b seq) list -> 'a -> 'b seq
  val TRY: ('a -> 'a seq) -> 'a -> 'a seq
  val REPEAT: ('a -> 'a seq) -> 'a -> 'a seq
end;

structure Seq: SEQ =
struct


(** lazy sequences **)

datatype 'a seq = Seq of unit -> ('a * 'a seq) option;

(*the abstraction for making a sequence*)
val make = Seq;

(*return next sequence element as None or Some (x, xq)*)
fun pull (Seq f) = f ();


(*the empty sequence*)
val empty = Seq (fn () => None);

(*prefix an element to the sequence -- use cons (x, xq) only if
  evaluation of xq need not be delayed, otherwise use
  make (fn () => Some (x, xq))*)
fun cons x_xq = make (fn () => Some x_xq);

fun single x = cons (x, empty);

(*head and tail -- beware of calling the sequence function twice!!*)
fun hd xq = #1 (the (pull xq))
and tl xq = #2 (the (pull xq));


(*the list of the first n elements, paired with rest of sequence;
  if length of list is less than n, then sequence had less than n elements*)
fun chop (n, xq) =
  if n <= 0 then ([], xq)
  else
    (case pull xq of
      None => ([], xq)
    | Some (x, xq') => apfst (Library.cons x) (chop (n - 1, xq')));

(*conversion from sequence to list*)
fun list_of xq =
  (case pull xq of
    None => []
  | Some (x, xq') => x :: list_of xq');

(*conversion from list to sequence*)
fun of_list xs = foldr cons (xs, empty);


(*map the function f over the sequence, making a new sequence*)
fun map f xq =
  make (fn () =>
    (case pull xq of
      None => None
    | Some (x, xq') => Some (f x, map f xq')));

(*map over a sequence xq, append the sequence yq*)
fun mapp f xq yq =
  let
    fun copy s =
      make (fn () =>
        (case pull s of
          None => pull yq
        | Some (x, s') => Some (f x, copy s')))
  in copy xq end;

(*sequence append:  put the elements of xq in front of those of yq*)
fun append (xq, yq) =
  let
    fun copy s =
      make (fn () =>
        (case pull s of
          None => pull yq
        | Some (x, s') => Some (x, copy s')))
  in copy xq end;

(*filter sequence by predicate*)
fun filter pred xq =
  let
    fun copy s =
      make (fn () =>
        (case pull s of
          None => None
        | Some (x, s') => if pred x then Some (x, copy s') else pull (copy s')));
  in copy xq end;

(*flatten a sequence of sequences to a single sequence*)
fun flat xqq =
  make (fn () =>
    (case pull xqq of
      None => None
    | Some (xq, xqq') => pull (append (xq, flat xqq'))));

(*interleave elements of xq with those of yq -- fairer than append*)
fun interleave (xq, yq) =
  make (fn () =>
    (case pull xq of
      None => pull yq
    | Some (x, xq') => Some (x, interleave (yq, xq'))));


(*functional to print a sequence, up to "count" elements;
  the function prelem should print the element number and also the element*)
fun print prelem count seq =
  let
    fun pr (k, xq) =
      if k > count then ()
      else
        (case pull xq of
          None => ()
        | Some (x, xq') => (prelem k x; writeln ""; pr (k + 1, xq')))
  in pr (1, seq) end;

(*accumulating a function over a sequence; this is lazy*)
fun it_right f (xq, yq) =
  let
    fun its s =
      make (fn () =>
        (case pull s of
          None => pull yq
        | Some (a, s') => pull (f (a, its s'))))
  in its xq end;



(** sequence functions **)      (*some code duplicated from Pure/tctical.ML*)

fun succeed x = single x;
fun fail _ = empty;


fun THEN (f, g) x = flat (map g (f x));

fun ORELSE (f, g) x =
  (case pull (f x) of
    None => g x
  | some => make (fn () => some));

fun APPEND (f, g) x =
  append (f x, make (fn () => pull (g x)));


fun EVERY fs = foldr THEN (fs, succeed);
fun FIRST fs = foldr ORELSE (fs, fail);


fun TRY f = ORELSE (f, succeed);

fun REPEAT f =
  let
    fun rep qs x =
      (case pull (f x) of
        None => Some (x, make (fn () => repq qs))
      | Some (x', q) => rep (q :: qs) x')
    and repq [] = None
      | repq (q :: qs) =
          (case pull q of
            None => repq qs
          | Some (x, q) => rep (q :: qs) x);
  in fn x => make (fn () => rep [] x) end;


end;
