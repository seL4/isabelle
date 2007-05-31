(*  Title:      Tools/Compute_Oracle/Compute_Oracle.thy
    ID:         $Id$
    Author:     Steven Obua, TU Munich

Steven Obua's evaluator.
*)

theory Compute_Oracle
imports CPure
uses
  "am_interpreter.ML"
  "am_compiler.ML"
  "am_util.ML"
  "compute.ML"
begin

oracle compute_oracle ("Compute.computer * (int -> string) * cterm") =
  {* Compute.oracle_fn *}

ML {*
structure Compute =
struct
  open Compute

  fun rewrite_param r n ct =
    compute_oracle (Thm.theory_of_cterm ct) (r, n, ct)

  fun rewrite r ct = rewrite_param r default_naming ct
end
*}

end
