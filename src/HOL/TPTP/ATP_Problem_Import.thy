(*  Title:      HOL/TPTP/ATP_Problem_Import.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* ATP Problem Importer *}

theory ATP_Problem_Import
imports Complex_Main TPTP_Interpret
uses ("atp_problem_import.ML")
begin

typedecl iota (* for TPTP *)

use "atp_problem_import.ML"

end
