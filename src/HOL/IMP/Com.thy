(*  Title:        HOL/IMP/Com.thy
    Author:       Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Author:       Gerwin Klein
*)

header "Syntax of Commands"

theory Com imports Main begin

typedecl loc 
  -- "an unspecified (arbitrary) type of locations 
      (adresses/names) for variables"
      
type_synonym val = nat -- "or anything else, @{text nat} used in examples"
type_synonym state = "loc \<Rightarrow> val"
type_synonym aexp = "state \<Rightarrow> val"
type_synonym bexp = "state \<Rightarrow> bool"
  -- "arithmetic and boolean expressions are not modelled explicitly here,"
  -- "they are just functions on states"

datatype
  com = SKIP                    
      | Assign loc aexp         ("_ :== _ " 60)
      | Semi   com com          ("_; _"  [60, 60] 10)
      | Cond   bexp com com     ("IF _ THEN _ ELSE _"  60)
      | While  bexp com         ("WHILE _ DO _"  60)

notation (latex)
  SKIP  ("\<SKIP>") and
  Cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  While  ("\<WHILE> _ \<DO> _"  60)

end
