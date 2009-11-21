(*  Title:      HOL/Tools/dseq.ML
    Author:     Stefan Berghofer, TU Muenchen

Sequences with recursion depth limit.
*)

signature DSEQ =
sig
  type 'a seq = int * int * int -> 'a Seq.seq;
  val maps: ('a -> 'b seq) -> 'a seq -> 'b seq
  val map: ('a -> 'b) -> 'a seq -> 'b seq
  val append: 'a seq -> 'a seq -> 'a seq
  val interleave: 'a seq -> 'a seq -> 'a seq
  val single: 'a -> 'a seq
  val empty: 'a seq
  val guard: bool -> unit seq
  val of_list: 'a list -> 'a seq
  val list_of: 'a seq -> 'a list
  val pull: 'a seq -> ('a * 'a Seq.seq) option
  val hd: 'a seq -> 'a
  val generator: (int -> 'a * 'b) -> 'a seq
end;

structure DSeq : DSEQ =
struct

type 'a seq = int * int * int -> 'a Seq.seq;

fun maps f s (0, _, _) = Seq.empty
  | maps f s (i, j, k) = Seq.maps (fn a => f a (i, j, k)) (s (i - 1, j, k));

fun map f s p = Seq.map f (s p);

fun append s1 s2 p = Seq.append (s1 p) (s2 p);

fun interleave s1 s2 p = Seq.interleave (s1 p, s2 p);

fun single x _ = Seq.single x;

fun empty _ = Seq.empty;

fun guard b = if b then single () else empty;

fun of_list xs _ = Seq.of_list xs;

fun list_of s = Seq.list_of (s (~1, 0, 0));

fun pull s = Seq.pull (s (~1, 0, 0));

fun hd s = Seq.hd (s (~1, 0, 0));

fun generator g (i, 0, k) = Seq.empty
  | generator g (i, j, k) =
      Seq.make (fn () => SOME (fst (g k), generator g (i, j-1, k)));

end;


(* combinators for code generated from inductive predicates *)

infix 5 :->;
infix 3 ++;

fun s :-> f = DSeq.maps f s;

fun f ++ g = DSeq.append f g;

val ?? = DSeq.guard;

fun ??? f g = f o g;

fun ?! s = is_some (DSeq.pull s);

fun equal__1 x = DSeq.single x;

val equal__2 = equal__1;

fun equal__1_2 (x, y) = ?? (x = y);
