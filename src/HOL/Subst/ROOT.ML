(*  Title: 	HOL/Subst/ROOT.ML
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Substitution and Unification in Higher-Order Logic. 

Implements Manna & Waldinger's formalization, with Paulson's simplifications:

Z Manna & R Waldinger, Deductive Synthesis of the Unification Algorithm. 
SCP 1 (1981), 5-48

L C Paulson, Verifying the Unification Algorithm in LCF. SCP 5 (1985), 143-170

setplus      -  minor additions to HOL's set theory
alist        -  association lists
uterm        -  inductive data type of terms
utlemmas     -  definition of occurs and vars_of for terms
subst        -  substitutions
unifier      -  specification of unification and conditions for 
                correctness and termination

To load, go to the parent directory and type use"Subst/ROOT.ML";
*)

HOL_build_completed;    (*Cause examples to fail if HOL did*)

writeln"Root file for Substitutions and Unification";
loadpath := ["Subst"];

use_thy "Unifier";

make_chart ();   (*make HTML chart*)

writeln"END: Root file for Substitutions and Unification";
