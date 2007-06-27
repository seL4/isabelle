(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Resolution =
sig

(* ------------------------------------------------------------------------- *)
(* A type of resolution proof procedures.                                    *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {active : Active.parameters,
      waiting : Waiting.parameters}

type resolution

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new : parameters -> Thm.thm list -> resolution

val active : resolution -> Active.active

val waiting : resolution -> Waiting.waiting

val pp : resolution Parser.pp

(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype decision =
    Contradiction of Thm.thm
  | Satisfiable of Thm.thm list

datatype state =
    Decided of decision
  | Undecided of resolution

val iterate : resolution -> state

val loop : resolution -> decision

end
