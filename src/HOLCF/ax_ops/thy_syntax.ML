(*  Title:      HOLCF/thy_syntax.ML
    ID:         $Id$
    Author:     Tobias Mayr

Additional thy file sections for HOLCF: axioms, ops.
*)

(* use "holcflogics.ML"; 
   use "thy_axioms.ML";
   use "thy_ops.ML";      should already have been done in ROOT.ML *)

structure ThySynData : THY_SYN_DATA =
struct

open HOLCFlogic;

val user_keywords = (*####*)filter_out (fn s => s mem (ThyAxioms.axioms_keywords@
                    ThyOps.ops_keywords)) (*####*)ThySynData.user_keywords @ 
                    ThyAxioms.axioms_keywords @ 
                    ThyOps.ops_keywords;

val user_sections = (*####*)filter_out (fn (s,_) => s mem (map fst (
                    ThyAxioms.axioms_sections@ ThyOps.ops_sections))) (*####*)
                      ThySynData.user_sections @
                    ThyAxioms.axioms_sections @
                    ThyOps.ops_sections;
end;

structure ThySyn = ThySynFun(ThySynData);
set_parser ThySyn.parse;
