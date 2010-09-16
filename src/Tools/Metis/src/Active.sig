(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* Copyright (c) 2002 Joe Hurd, distributed under the MIT license            *)
(* ========================================================================= *)

signature Active =
sig

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify =
     {subsume : bool,
      reduce : bool,
      rewrite : bool}

type parameters =
     {clause : Clause.parameters,
      prefactor : simplify,
      postfactor : simplify}

type active

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val size : active -> int

val saturation : active -> Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

val new :
    parameters -> {axioms : Thm.thm list, conjecture : Thm.thm list} ->
    active * {axioms : Clause.clause list, conjecture : Clause.clause list}

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

val add : active -> Clause.clause -> active * Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp : active Print.pp

end
