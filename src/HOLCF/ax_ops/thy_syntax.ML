(*  Title:      HOLCF/thy_syntax.ML
    ID:         $Id$
    Author:     Tobias Mayr

Installation of the additional theory file sections for HOLCF: axioms , ops 
There's an elaborate but german description of this extension
and a short english description of the new sections,
write to mayrt@informatik.tu-muenchen.de.

TODO:

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
init_thy_reader ();
