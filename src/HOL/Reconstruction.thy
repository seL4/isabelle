(*  Title:      HOL/Reconstruction.thy
    ID: $Id$
    Author:     Lawrence C Paulson
    Copyright   2004  University of Cambridge
*)

header{*Attributes for Reconstructing External Resolution Proofs*}

theory Reconstruction
    imports Hilbert_Choice Map Infinite_Set Extraction
    files "Tools/res_lib.ML"
	  "Tools/res_clause.ML"
	  "Tools/res_skolem_function.ML"
	  "Tools/res_axioms.ML"
	  "Tools/res_types_sorts.ML"

      "Tools/ATP/recon_prelim.ML"
 	  "Tools/ATP/recon_order_clauses.ML"
 	  "Tools/ATP/recon_translate_proof.ML"
 	  "Tools/ATP/recon_parse.ML"
 	  "Tools/ATP/recon_transfer_proof.ML"
	  "Tools/ATP/VampireCommunication.ML"
	  "Tools/ATP/SpassCommunication.ML"
	  "Tools/ATP/watcher.sig"
	  "Tools/ATP/watcher.ML"
	  "Tools/ATP/res_clasimpset.ML"
	  "Tools/res_atp.ML"

      "Tools/reconstruction.ML"

begin

text{*Every theory of HOL must be a descendant or ancestor of this one!*}

setup ResAxioms.setup
setup Reconstruction.setup

end
