(*  Title:      HOL/Tools/dseq.ML
    Author:     Stefan Berghofer, TU Muenchen

Sequences with recursion depth limit.
*)

signature DSEQ =
sig
  type 'a seq = int -> 'a Seq.seq;
  val maps: ('a -> 'b seq) -> 'a seq -> 'b seq
  val map: ('a -> 'b) -> 'a seq -> 'b seq
  val append: 'a seq -> 'a seq -> 'a seq
  val interleave: 'a seq -> 'a seq -> 'a seq
  val single: 'a -> 'a seq
  val empty: 'a seq
  val guard: bool -> unit seq
  val of_list: 'a list -> 'a seq
  val list_of: 'a seq -> 'a list
  val pull: 'a seq -> ('a * 'a seq) option
  val hd: 'a seq -> 'a
end;

structure DSeq : DSEQ =
struct

type 'a seq = int -> 'a Seq.seq;

fun maps f s 0 = Seq.empty
  | maps f s i = Seq.maps (fn a => f a i) (s (i - 1));

fun map f s i = Seq.map f (s i);

fun append s1 s2 i = Seq.append (s1 i) (s2 i);

fun interleave s1 s2 i = Seq.interleave (s1 i, s2 i);

fun single x i = Seq.single x;

fun empty i = Seq.empty;

fun guard b = if b then single () else empty;

fun of_list xs i = Seq.of_list xs;

fun list_of s = Seq.list_of (s ~1);

fun pull s = Seq.pull (s ~1) |> (Option.map o apsnd) K; (*FIXME*)

fun hd s = Seq.hd (s ~1);

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
