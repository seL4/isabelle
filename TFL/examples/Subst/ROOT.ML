(*  Title:      HOL/Subst/ROOT.ML
    ID:         $Id$
    Authors:     Martin Coen, Cambridge University Computer Laboratory
                 Konrad Slind, TU Munich
    Copyright   1993  University of Cambridge,
                1996  TU Munich

Substitution and Unification in Higher-Order Logic. 

Implements Manna & Waldinger's formalization, with Paulson's simplifications,
and some new simplifications by Slind.

Z Manna & R Waldinger, Deductive Synthesis of the Unification Algorithm. 
SCP 1 (1981), 5-48

L C Paulson, Verifying the Unification Algorithm in LCF. SCP 5 (1985), 143-170

Setplus      -  minor additions to HOL's set theory
Alist        -  association lists
Uterm        -  data type of terms
Subst        -  substitutions
Unify        -  specification of unification and conditions for 
                correctness and termination

To load, type use"ROOT.ML"; into an Isabelle-HOL that has TFL 
also loaded. 
*)

HOL_build_completed;    (*Cause examples to fail if HOL did*)

writeln"Root file for Substitutions and Unification";
loadpath := "../../" :: !loadpath;
use_thy "Unify";

writeln"END: Root file for Substitutions and Unification";
