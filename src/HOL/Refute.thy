(*  Title:      HOL/Refute.thy
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004

Basic setup and documentation for the 'refute' (and 'refute_params') command.
*)

header {* Refute *}

theory Refute = Map

files "Tools/prop_logic.ML"
      "Tools/sat_solver.ML"
      "Tools/refute.ML"
      "Tools/refute_isar.ML":

use "Tools/prop_logic.ML"
use "Tools/sat_solver.ML"
use "Tools/refute.ML"
use "Tools/refute_isar.ML"

setup Refute.setup

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
(* have installed ZChaff, simply set 'ZCHAFF_HOME' in 'etc/settings'.        *)
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
(* sets and set membership, "arbitrary", "The", and "Eps".  Constants for    *)
(* which a defining equation exists are unfolded automatically.  Non-        *)
(* recursive inductive datatypes are supported.                              *)
(*                                                                           *)
(* The (space) complexity of the algorithm is exponential in both the length *)
(* of the formula and the size of the model.                                 *)
(*                                                                           *)
(* NOT (YET) SUPPORTED ARE                                                   *)
(*                                                                           *)
(* - schematic type variables                                                *)
(* - axioms, sorts                                                           *)
(* - type constructors other than bool, =>, set, non-recursive IDTs          *)
(* - inductively defined sets                                                *)
(* - recursive functions                                                     *)
(* - ...                                                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* PARAMETERS                                                                *)
(*                                                                           *)
(* The following global parameters are currently supported (and required):   *)
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
(* "satsolver"   string  Name of the SAT solver to be used.                  *)
(*                                                                           *)
(* See 'HOL/Main.thy' for default values.                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* FILES                                                                     *)
(*                                                                           *)
(* HOL/Tools/prop_logic.ML    Propositional logic                            *)
(* HOL/Tools/sat_solver.ML    SAT solvers                                    *)
(* HOL/Tools/refute.ML        Translation HOL -> propositional logic and     *)
(*                            boolean assignment -> HOL model                *)
(* HOL/Tools/refute_isar.ML   Adds 'refute'/'refute_params' to Isabelle's    *)
(*                            syntax                                         *)
(* HOL/Refute.thy             This file: loads the ML files, basic setup,    *)
(*                            documentation                                  *)
(* HOL/Main.thy               Sets default parameters                        *)
(* HOL/ex/RefuteExamples.thy  Examples                                       *)
(* ------------------------------------------------------------------------- *)
\end{verbatim}
*}

end
