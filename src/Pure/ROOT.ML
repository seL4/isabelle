(*  Title:      Pure/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Root file for Pure Isabelle: all modules in proper order for loading.
Loads pure Isabelle into an empty database (see also Makefile).

TO DO:
instantiation of theorems can lead to inconsistent sorting of type vars if
'a::S is already present and 'a::T is introduced.
*)

val banner = "Pure Isabelle";
val version = "February 93";

print_depth 1;

use "library.ML";
use "term.ML";
use "symtab.ML";

structure Symtab = SymtabFun();

(*Syntax module*)
cd "Syntax";
use "ROOT.ML";
cd "..";

use "type.ML";
use "sign.ML";
use "sequence.ML";
use "envir.ML";
use "pattern.ML";
use "unify.ML";
use "net.ML";
use "logic.ML";
use "thm.ML";
use "drule.ML";
use "tctical.ML";
use "tactic.ML";
use "goals.ML";

(*Will be visible to all object-logics.*)
structure Type = TypeFun(structure Symtab=Symtab and Syntax=Syntax);
structure Sign = SignFun(structure Type=Type and Syntax=Syntax);
structure Sequence = SequenceFun();
structure Envir = EnvirFun();
structure Pattern = PatternFun(structure Sign=Sign and Envir=Envir);
structure Unify = UnifyFun(structure Sign=Sign and Envir=Envir
                           and Sequence=Sequence and Pattern=Pattern);
structure Net = NetFun();
structure Logic = LogicFun(structure Unify=Unify and Net=Net);
structure Thm = ThmFun(structure Logic=Logic and Unify=Unify and Net=Net
                             and Pattern=Pattern);
structure Drule = DruleFun(structure Logic=Logic and Thm=Thm);
structure Tactical = TacticalFun(structure Logic=Logic and Drule=Drule);
structure Tactic = TacticFun(structure Logic=Logic and Drule=Drule
                             and Tactical=Tactical and Net=Net);
structure Goals = GoalsFun(structure Logic=Logic and Drule=Drule
                           and Tactic=Tactic and Pattern=Pattern);
open BasicSyntax Thm Drule Tactical Tactic Goals;

structure Pure = struct val thy = pure_thy end;

use "install_pp.ML";



(*Theory parser
  (The new Thy/read.ML needs Thm so this has to be done AFTER Thm is
   created.) *)
cd "Thy";
use "ROOT.ML";
cd "..";

