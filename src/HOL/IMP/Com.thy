(*  Title:        HOL/IMP/Com.thy
    ID:           $Id$
    Author:       Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Isar Version: Gerwin Klein, 2001
    Copyright     1994 TUM
*)

header "Syntax of Commands"

theory Com = Main:

typedecl loc 
  -- "an unspecified (arbitrary) type of locations 
      (adresses/names) for variables"
      
types 
  val   = nat -- "or anything else, @{text nat} used in examples"
  state = "loc \<Rightarrow> val"
  aexp  = "state \<Rightarrow> val"  
  bexp  = "state \<Rightarrow> bool"
  -- "arithmetic and boolean expressions are not modelled explicitly here,"
  -- "they are just functions on states"

datatype
  com = SKIP                    
      | Assign loc aexp         ("_ :== _ " 60)
      | Semi   com com          ("_; _"  [60, 60] 10)
      | Cond   bexp com com     ("IF _ THEN _ ELSE _"  60)
      | While  bexp com         ("WHILE _ DO _"  60)

syntax (latex)
  SKIP :: com   ("\<SKIP>")
  Cond :: "bexp \<Rightarrow> com \<Rightarrow> com \<Rightarrow> com"  ("\<IF> _ \<THEN> _ \<ELSE> _"  60)
  While :: "bexp \<Rightarrow> com \<Rightarrow> com" ("\<WHILE> _ \<DO> _"  60)

end
