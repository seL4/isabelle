(*  Title:      ZF/Resid/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Executes the Residuals example.
This is a proof of the Church-Rosser Theorem for the untyped lambda-calculus.

By Ole Rasmussen, following the Coq proof given in

Gérard Huet.  Residual Theory in Lambda-Calculus: A Formal Development.
J. Functional Programming 4(3) 1994, 371-394.
*)

writeln"Root file for ZF/Resid";

set proof_timing;
time_use_thy "Conversion";

writeln"END: Root file for ZF/Resid";
