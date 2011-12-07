(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Copyright (c) 2001 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Stream :> Stream =
struct

val K = Useful.K;

val pair = Useful.pair;

val funpow = Useful.funpow;

(* ------------------------------------------------------------------------- *)
(* The stream type.                                                          *)
(* ------------------------------------------------------------------------- *)

datatype 'a stream =
    Nil
  | Cons of 'a * (unit -> 'a stream);

(* ------------------------------------------------------------------------- *)
(* Stream constructors.                                                      *)
(* ------------------------------------------------------------------------- *)

fun repeat x = let fun rep () = Cons (x,rep) in rep () end;

fun count n = Cons (n, fn () => count (n + 1));

fun funpows f x = Cons (x, fn () => funpows f (f x));

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these should all terminate.  *)
(* ------------------------------------------------------------------------- *)

fun cons h t = Cons (h,t);

fun null Nil = true
  | null (Cons _) = false;

fun hd Nil = raise Empty
  | hd (Cons (h,_)) = h;

fun tl Nil = raise Empty
  | tl (Cons (_,t)) = t ();

fun hdTl s = (hd s, tl s);

fun singleton s = Cons (s, K Nil);

fun append Nil s = s ()
  | append (Cons (h,t)) s = Cons (h, fn () => append (t ()) s);

fun map f =
    let
      fun m Nil = Nil
        | m (Cons (h,t)) = Cons (f h, m o t)
    in
      m
    end;

fun maps f g =
    let
      fun mm s Nil = g s
        | mm s (Cons (x,xs)) =
          let
            val (y,s') = f x s
          in
            Cons (y, mm s' o xs)
          end
    in
      mm
    end;

fun zipwith f =
    let
      fun z Nil _ = Nil
        | z _ Nil = Nil
        | z (Cons (x,xs)) (Cons (y,ys)) =
          Cons (f x y, fn () => z (xs ()) (ys ()))
    in
      z
    end;

fun zip s t = zipwith pair s t;

fun take 0 _ = Nil
  | take n Nil = raise Subscript
  | take 1 (Cons (x,_)) = Cons (x, K Nil)
  | take n (Cons (x,xs)) = Cons (x, fn () => take (n - 1) (xs ()));

fun drop n s = funpow n tl s handle Empty => raise Subscript;

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these might not terminate.   *)
(* ------------------------------------------------------------------------- *)

local
  fun len n Nil = n
    | len n (Cons (_,t)) = len (n + 1) (t ());
in
  fun length s = len 0 s;
end;

fun exists pred =
    let
      fun f Nil = false
        | f (Cons (h,t)) = pred h orelse f (t ())
    in
      f
    end;

fun all pred = not o exists (not o pred);

fun filter p Nil = Nil
  | filter p (Cons (x,xs)) =
    if p x then Cons (x, fn () => filter p (xs ())) else filter p (xs ());

fun foldl f =
    let
      fun fold b Nil = b
        | fold b (Cons (h,t)) = fold (f (h,b)) (t ())
    in
      fold
    end;

fun concat Nil = Nil
  | concat (Cons (Nil, ss)) = concat (ss ())
  | concat (Cons (Cons (x, xs), ss)) =
    Cons (x, fn () => concat (Cons (xs (), ss)));

fun mapPartial f =
    let
      fun mp Nil = Nil
        | mp (Cons (h,t)) =
          case f h of
            NONE => mp (t ())
          | SOME h' => Cons (h', fn () => mp (t ()))
    in
      mp
    end;

fun mapsPartial f g =
    let
      fun mp s Nil = g s
        | mp s (Cons (h,t)) =
          let
            val (h,s) = f h s
          in
            case h of
              NONE => mp s (t ())
            | SOME h => Cons (h, fn () => mp s (t ()))
          end
    in
      mp
    end;

fun mapConcat f =
    let
      fun mc Nil = Nil
        | mc (Cons (h,t)) = append (f h) (fn () => mc (t ()))
    in
      mc
    end;

fun mapsConcat f g =
    let
      fun mc s Nil = g s
        | mc s (Cons (h,t)) =
          let
            val (l,s) = f h s
          in
            append l (fn () => mc s (t ()))
          end
    in
      mc
    end;

(* ------------------------------------------------------------------------- *)
(* Stream operations.                                                        *)
(* ------------------------------------------------------------------------- *)

fun memoize Nil = Nil
  | memoize (Cons (h,t)) = Cons (h, Lazy.memoize (fn () => memoize (t ())));

fun concatList [] = Nil
  | concatList (h :: t) = append h (fn () => concatList t);

local
  fun toLst res Nil = List.rev res
    | toLst res (Cons (x, xs)) = toLst (x :: res) (xs ());
in
  fun toList s = toLst [] s;
end;

fun fromList [] = Nil
  | fromList (x :: xs) = Cons (x, fn () => fromList xs);

fun listConcat s = concat (map fromList s);

fun toString s = String.implode (toList s);

fun fromString s = fromList (String.explode s);

fun toTextFile {filename = f} s =
    let
      val (h,close) =
          if f = "-" then (TextIO.stdOut, K ())
          else (TextIO.openOut f, TextIO.closeOut)

      fun toFile Nil = ()
        | toFile (Cons (x,y)) = (TextIO.output (h,x); toFile (y ()))

      val () = toFile s
    in
      close h
    end;

fun fromTextFile {filename = f} =
    let
      val (h,close) =
          if f = "-" then (TextIO.stdIn, K ())
          else (TextIO.openIn f, TextIO.closeIn)

      fun strm () =
          case TextIO.inputLine h of
            NONE => (close h; Nil)
          | SOME s => Cons (s,strm)
    in
      memoize (strm ())
    end;

end
