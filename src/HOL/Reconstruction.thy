(*  Title:      HOL/Reconstruction.thy
    ID: $Id$
    Author:     Lawrence C Paulson
    Copyright   2004  University of Cambridge
*)

header{*Attributes for Reconstructing External Resolution Proofs*}

theory Reconstruction
    imports Hilbert_Choice Map Infinite_Set
    files "Tools/res_lib.ML"
	  "Tools/res_clause.ML"
	  "Tools/res_skolem_function.ML"
	  "Tools/res_axioms.ML"
	  "Tools/res_types_sorts.ML"

          "Tools/reconstruction.ML"

begin

text{*Every theory of HOL must be a descendant or ancestor of this one!*}

setup Reconstruction.setup

end
