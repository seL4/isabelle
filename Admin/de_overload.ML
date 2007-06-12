(*  Title:      Pure/ML-Systems/de_overload.ML
    ID:         $Id$
    Author:     Makarius

De-overloaded operations for int and real.
*)

(* int *)

val op + = Int.+;
val op - = Int.-;
val op * = Int.*;
val op div = Int.div;
val op mod = Int.mod;
val ~ = Int.~;
val abs = Int.abs;

infix  7  *%
infix  6  +% -%
infix  4  >% >=% <% <=%

val op *% = Int.*;
val op +% = Int.+;
val op -% = Int.-;
val op >% = Int.>;
val op >=% = Int.>=;
val op <% = Int.<;
val op <=% = Int.<=;


(* real *)

infix  7  *~ /~
infix  6  +~ -~
infix  4  >~ >=~ <~ <=~

val op *~ = Real.*;
val op /~ = Real./;
val op +~ = Real.+;
val op -~ = Real.-;
val op >~ = Real.>;
val op >=~ = Real.>=;
val op <~ = Real.<;
val op <=~ = Real.<=;
