(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Heap :> Heap =
struct

(* Leftist heaps as in Purely Functional Data Structures, by Chris Okasaki *)

datatype 'a node = E | T of int * 'a * 'a node * 'a node;

datatype 'a heap = Heap of ('a * 'a -> order) * int * 'a node;

fun rank E = 0
  | rank (T (r,_,_,_)) = r;

fun makeT (x,a,b) =
  if rank a >= rank b then T (rank b + 1, x, a, b) else T (rank a + 1, x, b, a);

fun merge cmp =
    let
      fun mrg (h,E) = h
        | mrg (E,h) = h
        | mrg (h1 as T (_,x,a1,b1), h2 as T (_,y,a2,b2)) =
          case cmp (x,y) of
            GREATER => makeT (y, a2, mrg (h1,b2))
          | _ => makeT (x, a1, mrg (b1,h2))
    in
      mrg
    end;

fun new cmp = Heap (cmp,0,E);

fun add (Heap (f,n,a)) x = Heap (f, n + 1, merge f (T (1,x,E,E), a));

fun size (Heap (_, n, _)) = n;

fun null h = size h = 0;

fun top (Heap (_,_,E)) = raise Empty
  | top (Heap (_, _, T (_,x,_,_))) = x;

fun remove (Heap (_,_,E)) = raise Empty
  | remove (Heap (f, n, T (_,x,a,b))) = (x, Heap (f, n - 1, merge f (a,b)));

fun app f =
    let
      fun ap [] = ()
        | ap (E :: rest) = ap rest
        | ap (T (_,d,a,b) :: rest) = (f d; ap (a :: b :: rest))
    in
      fn Heap (_,_,a) => ap [a]
    end;

fun toList h =
    if null h then []
    else
      let
        val (x,h) = remove h
      in
        x :: toList h
      end;

fun toStream h =
    if null h then Stream.NIL
    else
      let
        val (x,h) = remove h
      in
        Stream.CONS (x, fn () => toStream h)
      end;

fun toString h =
    "Heap[" ^ (if null h then "" else Int.toString (size h)) ^ "]";

end
