(*  Title: 	91/Modal/S4
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1991  University of Cambridge
*)

S4 = Modal0 +
rules
(* Definition of the star operation using a set of Horn clauses *)
(* For system S4:  gamma * == {[]P | []P : gamma}               *)
(*                 delta * == {<>P | <>P : delta}               *)

  lstar0         "|L>"
  lstar1         "$G |L> $H ==> []P, $G |L> []P, $H"
  lstar2         "$G |L> $H ==>   P, $G |L>      $H"
  rstar0         "|R>"
  rstar1         "$G |R> $H ==> <>P, $G |R> <>P, $H"
  rstar2         "$G |R> $H ==>   P, $G |R>      $H"

(* Rules for [] and <> *)

  boxR
   "[| $E |L> $E';  $F |R> $F';  $G |R> $G';  
           $E'         |- $F', P, $G'|] ==> $E          |- $F, []P, $G"
  boxL     "$E,P,$F,[]P |-         $G    ==> $E, []P, $F |-          $G"

  diaR     "$E          |- $F,P,$G,<>P   ==> $E          |- $F, <>P, $G"
  diaL
   "[| $E |L> $E';  $F |L> $F';  $G |R> $G';  
           $E', P, $F' |-         $G'|] ==> $E, <>P, $F |- $G"
end
