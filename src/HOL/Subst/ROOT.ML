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

AList        -  association lists
UTerm        -  data type of terms
Subst        -  substitutions
Unifier      -  specification of unification and conditions for 
                correctness and termination
Unify        -  the unification function

*)

time_use_thy "Unify";
