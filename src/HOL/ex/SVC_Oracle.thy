(*  Title:      HOL/ex/SVC_Oracle.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Based upon the work of Søren T. Heilmann.
*)

header {* Installing an oracle for SVC (Stanford Validity Checker) *}

theory SVC_Oracle
imports Main
uses "svc_funcs.ML"
begin

consts
  iff_keep :: "[bool, bool] => bool"
  iff_unfold :: "[bool, bool] => bool"

hide const iff_keep iff_unfold

oracle
  svc_oracle ("term") = Svc.oracle

end
