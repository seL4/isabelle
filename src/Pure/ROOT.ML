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
val version = "Isabelle-94 revision 3: March 95";

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
use "axclass.ML";

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
structure AxClass = AxClassFun(structure Logic = Logic
  and Goals = Goals and Tactic = Tactic);
open BasicSyntax Thm Drule Tactical Tactic Goals;

structure Pure = struct val thy = pure_thy end;
structure CPure = struct val thy = cpure_thy end;

(*Theory parser and loader*)
cd "Thy";
use "ROOT.ML";
cd "..";

use "install_pp.ML";
fun init_database () = (init_thy_reader (); init_pps ());

