(*  Title:      HOL/SVC_Oracle.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Installing the oracle for SVC (Stanford Validity Checker)

Based upon the work of Søren T. Heilmann
*)

theory SVC_Oracle = NatBin (** + Real??**)
files "Tools/svc_funcs.ML":

consts
  (*reserved for the oracle*)
  iff_keep :: "[bool, bool] => bool"
  iff_unfold :: "[bool, bool] => bool"

oracle
  svc_oracle = Svc.oracle

end
