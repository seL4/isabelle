(*  Title:      HOLCF/thy_syntax.ML
    ID:         $Id$
    Author:     Tobias Mayr

Additional thy file sections for HOLCF: axioms, ops.
*)

ThySyn.add_syntax
 (ThyAxioms.axioms_keywords @ ThyOps.ops_keywords)
 (ThyAxioms.axioms_sections @ ThyOps.ops_sections);
