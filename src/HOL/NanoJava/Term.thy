(*  Title:      HOL/NanoJava/Term.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Statements and expression emulations"

theory Term = Main:

typedecl cname  --{* class    name *}
typedecl mname  --{* method   name *}
typedecl fname  --{* field    name *}
typedecl vname  --{* variable name *}

consts 
  This :: vname --{* This pointer *}
  Par  :: vname --{* method parameter *}
  Res  :: vname --{* method result *}

text {* Inequality axioms not required here *}
(*
axioms
  This_neq_Par [simp]: "This \<noteq> Par"
  Par_neq_Res  [simp]: "Par \<noteq> Res"
  Res_neq_This [simp]: "Res \<noteq> This"
*)

datatype stmt
  = Skip                   --{* empty statement *}
  | Comp       stmt stmt   ("_;; _"             [91,90   ] 90)
  | Cond expr  stmt stmt   ("If '(_') _ Else _" [99,91,91] 91)
  | Loop vname stmt        ("While '(_') _"     [99,91   ] 91)
  | LAss vname expr        ("_ :== _"           [99,   95] 94) --{* local assignment *}
  | FAss expr  fname expr  ("_.._:==_"          [95,99,95] 94) --{* field assignment *}
  | Meth "cname \<times> mname"   --{* virtual method *}
  | Impl "cname \<times> mname"   --{* method implementation *}
and expr
  = NewC cname       ("new _"        [   99] 95) --{* object creation  *}
  | Cast cname expr                              --{* type cast        *}
  | LAcc vname                                   --{* local access     *}
  | FAcc expr  fname ("_.._"         [95,99] 95) --{* field access     *}
  | Call cname expr mname expr                   
                     ("{_}_.._'(_')" [99,95,99,95] 95) --{* method call *}

end

