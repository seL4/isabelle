(*  Title:      HOL/Refute.thy
    Author:     Tjark Weber
    Copyright   2003-2007

Basic setup and documentation for the 'refute' (and 'refute_params') command.
*)

header {* Refute *}

theory Refute
imports Hilbert_Choice List Sledgehammer
keywords "refute" :: diag and "refute_params" :: thy_decl
begin

ML_file "Tools/refute.ML"
setup Refute.setup

refute_params
 [itself = 1,
  minsize = 1,
  maxsize = 8,
  maxvars = 10000,
  maxtime = 60,
  satsolver = auto,
  no_assms = false]

text {*
\small
\begin{verbatim}
(* ------------------------------------------------------------------------- *)
(* REFUTE                                                                    *)
(*                                                                           *)
(* We use a SAT solver to search for a (finite) model that refutes a given   *)
(* HOL formula.                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* NOTE                                                                      *)
(*                                                                           *)
(* I strongly recommend that you install a stand-alone SAT solver if you     *)
(* want to use 'refute'.  For details see 'HOL/Tools/sat_solver.ML'.  If you *)
(* have installed (a supported version of) zChaff, simply set 'ZCHAFF_HOME'  *)
(* in 'etc/settings'.                                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* USAGE                                                                     *)
(*                                                                           *)
(* See the file 'HOL/ex/Refute_Examples.thy' for examples.  The supported    *)
(* parameters are explained below.                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* CURRENT LIMITATIONS                                                       *)
(*                                                                           *)
(* 'refute' currently accepts formulas of higher-order predicate logic (with *)
(* equality), including free/bound/schematic variables, lambda abstractions, *)
(* sets and set membership, "arbitrary", "The", "Eps", records and           *)
(* inductively defined sets.  Constants are unfolded automatically, and sort *)
(* axioms are added as well.  Other, user-asserted axioms however are        *)
(* ignored.  Inductive datatypes and recursive functions are supported, but  *)
(* may lead to spurious countermodels.                                       *)
(*                                                                           *)
(* The (space) complexity of the algorithm is non-elementary.                *)
(*                                                                           *)
(* Schematic type variables are not supported.                               *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* PARAMETERS                                                                *)
(*                                                                           *)
(* The following global parameters are currently supported (and required,    *)
(* except for "expect"):                                                     *)
(*                                                                           *)
(* Name          Type    Description                                         *)
(*                                                                           *)
(* "minsize"     int     Only search for models with size at least           *)
(*                       'minsize'.                                          *)
(* "maxsize"     int     If >0, only search for models with size at most     *)
(*                       'maxsize'.                                          *)
(* "maxvars"     int     If >0, use at most 'maxvars' boolean variables      *)
(*                       when transforming the term into a propositional     *)
(*                       formula.                                            *)
(* "maxtime"     int     If >0, terminate after at most 'maxtime' seconds.   *)
(*                       This value is ignored under some ML compilers.      *)
(* "satsolver"   string  Name of the SAT solver to be used.                  *)
(* "no_assms"    bool    If "true", assumptions in structured proofs are     *)
(*                       not considered.                                     *)
(* "expect"      string  Expected result ("genuine", "potential", "none", or *)
(*                       "unknown").                                         *)
(*                                                                           *)
(* The size of particular types can be specified in the form type=size       *)
(* (where 'type' is a string, and 'size' is an int).  Examples:              *)
(* "'a"=1                                                                    *)
(* "List.list"=2                                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* FILES                                                                     *)
(*                                                                           *)
(* HOL/Tools/prop_logic.ML     Propositional logic                           *)
(* HOL/Tools/sat_solver.ML     SAT solvers                                   *)
(* HOL/Tools/refute.ML         Translation HOL -> propositional logic and    *)
(*                             Boolean assignment -> HOL model               *)
(* HOL/Refute.thy              This file: loads the ML files, basic setup,   *)
(*                             documentation                                 *)
(* HOL/SAT.thy                 Sets default parameters                       *)
(* HOL/ex/Refute_Examples.thy  Examples                                      *)
(* ------------------------------------------------------------------------- *)
\end{verbatim}
*}

end
