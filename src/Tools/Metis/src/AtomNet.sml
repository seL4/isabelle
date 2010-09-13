(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure AtomNet :> AtomNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun atomToTerm atom = Term.Fn atom;

fun termToAtom (Term.Var _) = raise Bug "AtomNet.termToAtom"
  | termToAtom (Term.Fn atom) = atom;

(* ------------------------------------------------------------------------- *)
(* A type of atom sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = TermNet.parameters;

type 'a atomNet = 'a TermNet.termNet;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new = TermNet.new;

val size = TermNet.size;

fun insert net (atm,a) = TermNet.insert net (atomToTerm atm, a);

fun fromList parm l = foldl (fn (atm_a,n) => insert n atm_a) (new parm) l;

val filter = TermNet.filter;

fun toString net = "AtomNet[" ^ Int.toString (size net) ^ "]";

val pp = TermNet.pp;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

fun match net atm = TermNet.match net (atomToTerm atm);

fun matched net atm = TermNet.matched net (atomToTerm atm);

fun unify net atm = TermNet.unify net (atomToTerm atm);

end
