(*  Title:      HOL/MicroJava/J/Term.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Expressions and Statements} *}

theory Term = Value:

datatype binop = Eq | Add    -- "function codes for binary operation"

datatype expr
  = NewC cname               -- "class instance creation"
  | Cast cname expr          -- "type cast"
  | Lit val                  -- "literal value, also references"
  | BinOp binop expr expr    -- "binary operation"
  | LAcc vname               -- "local (incl. parameter) access"
  | LAss vname expr          ("_::=_" [90,90]90)      -- "local assign"
  | FAcc cname expr vname    ("{_}_.._" [10,90,99]90) -- "field access"
  | FAss cname expr vname 
                    expr     ("{_}_.._:=_" [10,90,99,90]90) -- "field ass."
  | Call cname expr mname 
    "ty list" "expr list"    ("{_}_.._'( {_}_')" [10,90,99,10,10] 90) -- "method call" 

datatype stmt
  = Skip                     -- "empty statement"
  | Expr expr                -- "expression statement"
  | Comp stmt stmt       ("_;; _"             [61,60]60)
  | Cond expr stmt stmt  ("If '(_') _ Else _" [80,79,79]70)
  | Loop expr stmt       ("While '(_') _"     [80,79]70)

end

