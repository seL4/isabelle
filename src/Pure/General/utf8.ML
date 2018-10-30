(*  Title:      Pure/General/utf8.ML
    Author:     Makarius

Variations on UTF-8.
*)

signature UTF8 =
sig
  type codepoint = int
  val decode_permissive: string -> codepoint list
end;

structure UTF8: UTF8 =
struct

type codepoint = int;


(* permissive UTF-8 decoding *)

(*see also https://en.wikipedia.org/wiki/UTF-8#Description
  overlong encodings enable byte-stuffing of low-ASCII*)

local

type state = codepoint list * codepoint * int;

fun flush ((buf, code, rest): state) : state =
  if code <> ~1 then
    ((if rest = 0 andalso code <= 0x10FFFF then code else 0xFFFD) :: buf, ~1, 0)
  else (buf, code, rest);

fun init x n (state: state) : state = (#1 (flush state), Word8.toInt x, n);

fun push x ((buf, code, rest): state) =
  if rest <= 0 then init x ~1 (buf, code, rest)
  else (buf, code * 64 + Word8.toInt x, rest - 1);

fun append x ((buf, code, rest): state) : state = (Word8.toInt x :: buf, code, rest);

fun decode (c, state) =
  if c < 0w128 then state |> flush |> append c
  else if Word8.andb (c, 0wxC0) = 0wx80 then state |> push (Word8.andb (c, 0wx3F))
  else if Word8.andb (c, 0wxE0) = 0wxC0 then state |> init (Word8.andb (c, 0wx1F)) 1
  else if Word8.andb (c, 0wxF0) = 0wxE0 then state |> init (Word8.andb (c, 0wx0F)) 2
  else if Word8.andb (c, 0wxF8) = 0wxF0 then state |> init (Word8.andb (c, 0wx07)) 3
  else state;

in

fun decode_permissive text =
  Word8Vector.foldl decode ([], ~1, 0) (Byte.stringToBytes text)
  |> flush |> #1 |> rev;

end;

end;
