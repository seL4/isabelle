(*  Title:      HOL/NumberTheory/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   2003  University of Cambridge

This directory contains formalized proofs of Wilson's Theorem (by Thomas M
Rasmussen) and of Gauss's law of quadratic reciprocity (by Avigad, Gray and
Kramer).  

The quadratic reciprocity formalization follows Eisenstein's proof, which is
the one most commonly found in introductory textbooks, and also uses a trick
used David Russinoff with the Boyer-Moore theorem prover.  See his "A
mechanical proof of quadratic reciprocity," Journal of Automated Reasoning
8:3-21, 1992.*)

no_document use_thy "Permutation";
no_document use_thy "Primes";

use_thy "Fib";
use_thy "Factorization";
use_thy "Chinese";
use_thy "WilsonRuss";
use_thy "WilsonBij";
use_thy "Quadratic_Reciprocity";
