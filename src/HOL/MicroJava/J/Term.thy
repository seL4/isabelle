(*  Title:      HOL/MicroJava/J/Term.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

section \<open>Expressions and Statements\<close>

theory Term imports Value begin

datatype binop = Eq | Add    \<comment> \<open>function codes for binary operation\<close>

datatype expr
  = NewC cname               \<comment> \<open>class instance creation\<close>
  | Cast cname expr          \<comment> \<open>type cast\<close>
  | Lit val                  \<comment> \<open>literal value, also references\<close>
  | BinOp binop expr expr    \<comment> \<open>binary operation\<close>
  | LAcc vname               \<comment> \<open>local (incl. parameter) access\<close>
  | LAss vname expr          (\<open>_::=_\<close> [90,90]90)      \<comment> \<open>local assign\<close>
  | FAcc cname expr vname    (\<open>{_}_.._\<close> [10,90,99]90) \<comment> \<open>field access\<close>
  | FAss cname expr vname 
                    expr     (\<open>{_}_.._:=_\<close> [10,90,99,90]90) \<comment> \<open>field ass.\<close>
  | Call cname expr mname 
    "ty list" "expr list"    (\<open>{_}_.._'( {_}_')\<close> [10,90,99,10,10] 90) \<comment> \<open>method call\<close>

datatype_compat expr

datatype stmt
  = Skip                     \<comment> \<open>empty statement\<close>
  | Expr expr                \<comment> \<open>expression statement\<close>
  | Comp stmt stmt       (\<open>_;; _\<close>             [61,60]60)
  | Cond expr stmt stmt  (\<open>If '(_') _ Else _\<close> [80,79,79]70)
  | Loop expr stmt       (\<open>While '(_') _\<close>     [80,79]70)

end

