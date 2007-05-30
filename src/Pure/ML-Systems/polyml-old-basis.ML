(*  Title:      Pure/ML-Systems/polyml-old-basis.ML
    ID:         $Id$

Fixes for the old SML basis library (before Poly/ML 4.2.0).
*)

structure String =
struct
  fun isSuffix s1 s2 =
    let val n1 = size s1 and n2 = size s2
    in if n1 = n2 then s1 = s2 else n1 <= n2 andalso String.substring (s2, n2 - n1, n1) = s1 end;
  open String;
end;

structure Substring =
struct
  open Substring;
  val full = all;
end;

structure Posix =
struct
  open Posix;
  structure IO =
  struct
    open IO;
    val mkTextReader = mkReader;
    val mkTextWriter = mkWriter;
  end;
end;

structure TextIO =
struct
  open TextIO;
  fun inputLine is =
    let val s = TextIO.inputLine is
    in if s = "" then NONE else SOME s end;
end;
