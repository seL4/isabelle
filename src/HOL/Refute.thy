(*  Title:      HOL/Refute.thy
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004

Basic setup and documentation for the 'refute' (and 'refute_params') command.
*)

(* ------------------------------------------------------------------------- *)
(* REFUTE                                                                    *)
(*                                                                           *)
(* We use a SAT solver to search for a (finite) model that refutes a given   *)
(* HOL formula.                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* INSTALLATION                                                              *)
(*                                                                           *)
(* 1. Install a stand-alone SAT solver.  The default parameters in           *)
(*    'HOL/Main.thy' assume that ZChaff 2003.12.04 (available for Solaris/   *)
(*    Linux/Cygwin/Windows at http://ee.princeton.edu/~chaff/zchaff.php) is  *)
(*    installed as '$HOME/bin/zchaff'.  If you want to use a different SAT   *)
(*    solver (or install ZChaff to a different location), you will need to   *)
(*    modify at least the values for 'command' and (probably) 'success'.     *)
(*                                                                           *)
(* 2. That's it. You can now use the 'refute' command in your own theories.  *)
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
(* sets and set membership.                                                  *)
(*                                                                           *)
(* NOT (YET) SUPPORTED ARE                                                   *)
(*                                                                           *)
(* - schematic type variables                                                *)
(* - type constructors other than =>, set, unit, and inductive datatypes     *)
(* - constants, including constructors of inductive datatypes and recursive  *)
(*   functions on inductive datatypes                                        *)
(*                                                                           *)
(* Unfolding of constants currently needs to be done manually, e.g. using    *)
(* 'apply (unfold xxx_def)'.                                                 *)
(*                                                                           *)
(* For formulas that contain (variables of) an inductive datatype, a         *)
(* spurious countermodel may be returned.  Currently no warning is issued in *)
(* this case.                                                                *)
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
(* "satfile"     string  Name of the file used to store the propositional    *)
(*                       formula, i.e. the input to the SAT solver.          *)
(* "satformat"   string  Format of the SAT solver's input file.  Must be     *)
(*                       either "cnf", "defcnf", or "sat".  Since "sat" is   *)
(*                       not supported by most SAT solvers, and "cnf" can    *)
(*                       cause exponential blowup of the formula, "defcnf"   *)
(*                       is recommended.                                     *)
(* "resultfile"  string  Name of the file containing the SAT solver's        *)
(*                       output.                                             *)
(* "success"     string  Part of the line in the SAT solver's output that    *)
(*                       precedes a list of integers representing the        *)
(*                       satisfying assignment.                              *)
(* "command"     string  System command used to execute the SAT solver.      *)
(*                       Note that you if you change 'satfile' or            *)
(*                       'resultfile', you will also need to change          *)
(*                       'command'.                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* FILES                                                                     *)
(*                                                                           *)
(* HOL/Tools/refute.ML        Implementation of the algorithm.               *)
(* HOL/Tools/refute_isar.ML   Adds 'refute'/'refute_params' to Isabelle's    *)
(*                            syntax.                                        *)
(* HOL/Refute.thy             This file. Loads the ML files, basic setup,    *)
(*                            documentation.                                 *)
(* HOL/Main.thy               Sets default parameters.                       *)
(* HOL/ex/RefuteExamples.thy  Examples.                                      *)
(* ------------------------------------------------------------------------- *)

header {* Refute *}

theory Refute = Map

files "Tools/refute.ML"
      "Tools/refute_isar.ML":

(* Setting up the 'refute' and 'refute\_params' commands *)

use "Tools/refute.ML"
use "Tools/refute_isar.ML"

setup Refute.setup

end
