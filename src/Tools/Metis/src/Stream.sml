(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Stream :> Stream =
struct

val K = Useful.K;

val pair = Useful.pair;

val funpow = Useful.funpow;

(* ------------------------------------------------------------------------- *)
(* The datatype declaration encapsulates all the primitive operations        *)
(* ------------------------------------------------------------------------- *)

datatype 'a stream =
    NIL
  | CONS of 'a * (unit -> 'a stream);

(* ------------------------------------------------------------------------- *)
(* Stream constructors                                                       *)
(* ------------------------------------------------------------------------- *)

fun repeat x = let fun rep () = CONS (x,rep) in rep () end;

fun count n = CONS (n, fn () => count (n + 1));

fun funpows f x = CONS (x, fn () => funpows f (f x));

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these should all terminate   *)
(* ------------------------------------------------------------------------- *)

fun cons h t = CONS (h,t);

fun null NIL = true | null (CONS _) = false;

fun hd NIL = raise Empty
  | hd (CONS (h,_)) = h;

fun tl NIL = raise Empty
  | tl (CONS (_,t)) = t ();

fun hdTl s = (hd s, tl s);

fun singleton s = CONS (s, K NIL);

fun append NIL s = s ()
  | append (CONS (h,t)) s = CONS (h, fn () => append (t ()) s);

fun map f =
    let
      fun m NIL = NIL
        | m (CONS (h, t)) = CONS (f h, fn () => m (t ()))
    in
      m
    end;

fun maps f =
    let
      fun mm _ NIL = NIL
        | mm s (CONS (x, xs)) =
          let
            val (y, s') = f x s
          in
            CONS (y, fn () => mm s' (xs ()))
          end
    in
      mm
    end;

fun zipwith f =
    let
      fun z NIL _ = NIL
        | z _ NIL = NIL
        | z (CONS (x,xs)) (CONS (y,ys)) =
          CONS (f x y, fn () => z (xs ()) (ys ()))
    in
      z
    end;

fun zip s t = zipwith pair s t;

fun take 0 _ = NIL
  | take n NIL = raise Subscript
  | take 1 (CONS (x,_)) = CONS (x, K NIL)
  | take n (CONS (x,xs)) = CONS (x, fn () => take (n - 1) (xs ()));

fun drop n s = funpow n tl s handle Empty => raise Subscript;

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these might not terminate    *)
(* ------------------------------------------------------------------------- *)

local
  fun len n NIL = n
    | len n (CONS (_,t)) = len (n + 1) (t ());
in
  fun length s = len 0 s;
end;

fun exists pred =
    let
      fun f NIL = false
        | f (CONS (h,t)) = pred h orelse f (t ())
    in
      f
    end;

fun all pred = not o exists (not o pred);

fun filter p NIL = NIL
  | filter p (CONS (x,xs)) =
    if p x then CONS (x, fn () => filter p (xs ())) else filter p (xs ());

fun foldl f =
    let
      fun fold b NIL = b
        | fold b (CONS (h,t)) = fold (f (h,b)) (t ())
    in
      fold
    end;

fun concat NIL = NIL
  | concat (CONS (NIL, ss)) = concat (ss ())
  | concat (CONS (CONS (x, xs), ss)) =
    CONS (x, fn () => concat (CONS (xs (), ss)));

fun mapPartial f =
    let
      fun mp NIL = NIL
        | mp (CONS (h,t)) =
          case f h of
            NONE => mp (t ())
          | SOME h' => CONS (h', fn () => mp (t ()))
    in
      mp
    end;

fun mapsPartial f =
    let
      fun mm _ NIL = NIL
        | mm s (CONS (x, xs)) =
          let
            val (yo, s') = f x s
            val t = mm s' o xs
          in
            case yo of NONE => t () | SOME y => CONS (y, t)
          end
    in
      mm
    end;

(* ------------------------------------------------------------------------- *)
(* Stream operations                                                         *)
(* ------------------------------------------------------------------------- *)

fun memoize NIL = NIL
  | memoize (CONS (h,t)) = CONS (h, Lazy.memoize (fn () => memoize (t ())));

local
  fun toLst res NIL = rev res
    | toLst res (CONS (x, xs)) = toLst (x :: res) (xs ());
in
  fun toList s = toLst [] s;
end;

fun fromList [] = NIL
  | fromList (x :: xs) = CONS (x, fn () => fromList xs);

fun toString s = implode (toList s);

fun fromString s = fromList (explode s);

fun toTextFile {filename = f} s =
    let
      val (h,close) =
          if f = "-" then (TextIO.stdOut, K ())
          else (TextIO.openOut f, TextIO.closeOut)

      fun toFile NIL = ()
        | toFile (CONS (x,y)) = (TextIO.output (h,x); toFile (y ()))

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
            NONE => (close h; NIL)
          | SOME s => CONS (s,strm)
    in
      memoize (strm ())
    end;

end
