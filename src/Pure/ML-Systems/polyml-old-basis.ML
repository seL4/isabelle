(*  Title:      Pure/ML-Systems/polyml-old-basis.ML
    ID:         $Id$

Fixes for the old SML basis library (before Poly/ML 4.2.0).
*)

structure String =
struct
  open String;
  fun isSuffix s1 s2 =
    let val n1 = size s1 and n2 = size s2
    in if n1 = n2 then s1 = s2 else n1 <= n2 andalso String.substring (s2, n2 - n1, n1) = s1 end;
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
