(*  Title:      HOL/IMP/Com.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM

Semantics of arithmetic and boolean expressions
Syntax of commands
*)

Com = Arith +

types 
      val
      loc
      state = "loc => val"
      aexp  = "state => val"
      bexp  = state => bool

arities loc,val :: term

datatype
  com = SKIP
      | ":="  loc aexp         (infixl  60)
      | Semi  com com          ("_; _"  [60, 60] 10)
      | Cond  bexp com com     ("IF _ THEN _ ELSE _"  60)
      | While bexp com         ("WHILE _ DO _"  60)

end
