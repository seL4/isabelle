(*  Title: 	ZF/Resid/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Executes the Residuals example.
This is a proof of the Church-Rosser Theorem for the untyped lambda-calculus.

By Ole Rasmussen, following the Coq proof given in

Gérard Huet.  Residual Theory in Lambda-Calculus: A Formal Development.
J. Functional Programming 4(3) 1994, 371-394.
*)

ZF_build_completed;	(*Make examples fail if ZF did*)

writeln"Root file for ZF/Resid";
proof_timing := true;

loadpath := [".", "Resid"];

time_use_thy "Confluence";

writeln"END: Root file for ZF/Resid";
