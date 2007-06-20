(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2002-2007 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Waiting =
sig

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {symbolsWeight : real,
      literalsWeight : real,
      modelsWeight : real,
      modelChecks : int,
      models : Model.parameters list}

type waiting

type distance

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new : parameters -> Clause.clause list -> waiting

val size : waiting -> int

val pp : waiting Parser.pp

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

val add : waiting -> distance * Clause.clause list -> waiting

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

val remove : waiting -> ((distance * Clause.clause) * waiting) option

end
