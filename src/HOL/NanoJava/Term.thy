(*  Title:      HOL/NanoJava/Term.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Statements and expression emulations"

theory Term = Main:

typedecl cname  (* class name *)
typedecl vnam   (* variable or field name *)
typedecl mname  (* method name *)
arities  cname :: "term"
         vnam  :: "term"
         mname :: "term"

datatype vname  (* variable for special names *)
  = This        (* This pointer *)
  | Param       (* method parameter *)
  | Res         (* method result *)
  | VName vnam 

datatype stmt
  = Skip                   (* empty statement *)
  | Comp       stmt stmt   ("_;; _"             [91,90   ] 90)
  | Cond expr  stmt stmt   ("If '(_') _ Else _" [99,91,91] 91)
  | Loop vname stmt        ("While '(_') _"     [99,91   ] 91)
  | LAss vname expr        ("_ :== _"           [99,   95] 94) (* local ass. *)
  | FAss expr  vnam expr   ("_.._:==_"          [95,99,95] 94) (* field ass. *)
  | Meth cname mname       (* virtual method *)
  | Impl cname mname       (* method implementation *)
and expr
  = NewC cname       ("new _"        [   99] 95) (* object creation  *)
  | Cast cname expr                              (* type cast        *)
  | LAcc vname                                   (* local access     *)
  | FAcc expr  vnam  ("_.._"         [95,99] 95) (* field access     *)
  | Call cname expr mname expr                   (* method call      *)
                     ("{_}_.._'(_')" [99,95,99,95] 95)

end

