(*  Title:      HOL/SVC_Oracle
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Installing the oracle for SVC (Stanford Validity Checker)

Based upon the work of Søren T. Heilmann
*)

SVC_Oracle = NatBin + (**Real?? + **)
oracle svc_oracle = Svc.oracle
end
