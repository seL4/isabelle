(*  Title:      ILL.thy
    ID:         $Id$
    Author:     Sara Kalvala and Valeria de Paiva
    Copyright   1995  University of Cambridge
*)


ILL = Sequents +

consts
  Trueprop       :: "two_seqi"

"><"    ::"[o, o] => o"        (infixr 35)
"-o"    ::"[o, o] => o"        (infixr 45)
"o-o"   ::"[o, o] => o"        (infixr 45)
FShriek ::"o => o"             ("! _" [100] 1000)
"&&"    ::"[o, o] => o"        (infixr 35)
"++"    ::"[o, o] => o"        (infixr 35)
zero    ::"o"                  ("0")
top     ::"o"                  ("1")
eye     ::"o"                  ("I")
aneg    ::"o=>o"               ("~_")


  (* context manipulation *)

 Context      :: "two_seqi"

  (* promotion rule *)

  PromAux :: "three_seqi"

syntax
  "@Trueprop" :: "single_seqe" ("((_)/ |- (_))" [6,6] 5)
  "@Context"  :: "two_seqe"   ("((_)/ :=: (_))" [6,6] 5)
  "@PromAux"  :: "three_seqe" ("promaux {_||_||_}")

defs

liff_def        "P o-o Q == (P -o Q) >< (Q -o P)"

aneg_def        "~A == A -o 0"




rules

identity        "P |- P"

zerol           "$G, 0, $H |- A"

  (* RULES THAT DO NOT DIVIDE CONTEXT *)

derelict   "$F, A, $G |- C ==> $F, !A, $G |- C"
  (* unfortunately, this one removes !A  *)

contract  "$F, !A, !A, $G |- C ==> $F, !A, $G |- C"

weaken     "$F, $G |- C ==> $G, !A, $F |- C"
  (* weak form of weakening, in practice just to clean context *)
  (* weaken and contract not needed (CHECK)  *)

promote2        "promaux{ || $H || B} ==> $H |- !B"
promote1        "promaux{!A, $G || $H || B}
                 ==> promaux {$G || $H, !A || B}"
promote0        "$G |- A ==> promaux {$G || || A}"



tensl     "$H, A, B, $G |- C ==> $H, A >< B, $G |- C"

impr      "A, $F |- B ==> $F |- A -o B"

conjr           "[| $F |- A ;
                 $F |- B |]
                ==> $F |- (A && B)"

conjll          "$G, A, $H |- C ==> $G, A && B, $H |- C"

conjlr          "$G, B, $H |- C ==> $G, A && B, $H |- C"

disjrl          "$G |- A ==> $G |- A ++ B"
disjrr          "$G |- B ==> $G |- A ++ B"
disjl           "[| $G, A, $H |- C ;
                    $G, B, $H |- C |]
                ==> $G, A ++ B, $H |- C"


      (* RULES THAT DIVIDE CONTEXT *)

tensr           "[| $F, $J :=: $G;
                    $F |- A ;
                    $J |- B     |]
                    ==> $G |- A >< B"

impl            "[| $G, $F :=: $J, $H ;
                    B, $F |- C ;
                       $G |- A |]
                    ==> $J, A -o B, $H |- C"


cut " [| $J1, $H1, $J2, $H3, $J3, $H2, $J4, $H4 :=: $F ;
         $H1, $H2, $H3, $H4 |- A ;
         $J1, $J2, A, $J3, $J4 |- B |]  ==> $F |- B"


  (* CONTEXT RULES *)

context1     "$G :=: $G"
context2     "$F, $G :=: $H, !A, $G ==> $F, A, $G :=: $H, !A, $G"
context3     "$F, $G :=: $H, $J ==> $F, A, $G :=: $H, A, $J"
context4a    "$F :=: $H, $G ==> $F :=: $H, !A, $G"
context4b    "$F, $H :=: $G ==> $F, !A, $H :=: $G"
context5     "$F, $G :=: $H ==> $G, $F :=: $H"




end

ML

val parse_translation = [("@Trueprop",Sequents.single_tr "Trueprop"),
                         ("@Context",Sequents.two_seq_tr "Context"),
                         ("@PromAux", Sequents.three_seq_tr "PromAux")];

val print_translation = [("Trueprop",Sequents.single_tr' "@Trueprop"),
                         ("Context",Sequents.two_seq_tr'"@Context"),
                         ("PromAux", Sequents.three_seq_tr'"@PromAux")];


