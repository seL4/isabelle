(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2002 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

signature Waiting =
sig

(* ------------------------------------------------------------------------- *)
(* The parameters control the order that clauses are removed from the        *)
(* waiting set: clauses are assigned a weight and removed in strict weight   *)
(* order, with smaller weights being removed before larger weights.          *)
(*                                                                           *)
(* The weight of a clause is defined to be                                   *)
(*                                                                           *)
(*   d * s^symbolsWeight * v^variablesWeight * l^literalsWeight * m          *)
(*                                                                           *)
(* where                                                                     *)
(*                                                                           *)
(*   d = the derivation distance of the clause from the axioms               *)
(*   s = the number of symbols in the clause                                 *)
(*   v = the number of distinct variables in the clause                      *)
(*   l = the number of literals in the clause                                *)
(*   m = the truth of the clause wrt the models                              *)
(* ------------------------------------------------------------------------- *)

type weight = real

type modelParameters =
     {model : Model.parameters,
      initialPerturbations : int,
      maxChecks : int option,
      perturbations : int,
      weight : weight}

type parameters =
     {symbolsWeight : weight,
      variablesWeight : weight,
      literalsWeight : weight,
      models : modelParameters list}

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type waiting

type distance

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new :
    parameters ->
    {axioms : Clause.clause list,
     conjecture : Clause.clause list} -> waiting

val size : waiting -> int

val pp : waiting Print.pp

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

val add : waiting -> distance * Clause.clause list -> waiting

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

val remove : waiting -> ((distance * Clause.clause) * waiting) option

end
