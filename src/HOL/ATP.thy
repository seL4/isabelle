(*  Title:      HOL/ATP.thy
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory ATP
imports Plain
uses "Tools/ATP/atp_problem.ML"
     "Tools/ATP/atp_proof.ML"
     "Tools/ATP/atp_systems.ML"
begin

setup ATP_Systems.setup

end
