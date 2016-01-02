(*  Title:      HOL/MicroJava/J/Term.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

section \<open>Expressions and Statements\<close>

theory Term imports Value begin

datatype binop = Eq | Add    \<comment> "function codes for binary operation"

datatype expr
  = NewC cname               \<comment> "class instance creation"
  | Cast cname expr          \<comment> "type cast"
  | Lit val                  \<comment> "literal value, also references"
  | BinOp binop expr expr    \<comment> "binary operation"
  | LAcc vname               \<comment> "local (incl. parameter) access"
  | LAss vname expr          ("_::=_" [90,90]90)      \<comment> "local assign"
  | FAcc cname expr vname    ("{_}_.._" [10,90,99]90) \<comment> "field access"
  | FAss cname expr vname 
                    expr     ("{_}_.._:=_" [10,90,99,90]90) \<comment> "field ass."
  | Call cname expr mname 
    "ty list" "expr list"    ("{_}_.._'( {_}_')" [10,90,99,10,10] 90) \<comment> "method call"

datatype_compat expr

datatype stmt
  = Skip                     \<comment> "empty statement"
  | Expr expr                \<comment> "expression statement"
  | Comp stmt stmt       ("_;; _"             [61,60]60)
  | Cond expr stmt stmt  ("If '(_') _ Else _" [80,79,79]70)
  | Loop expr stmt       ("While '(_') _"     [80,79]70)

end

