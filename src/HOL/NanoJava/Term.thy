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
  | Comp       stmt stmt   ("_;; _"             [91,90]    90)
  | Cond vname stmt stmt   ("If '(_') _ Else _" [99,91,91] 91)
  | Loop vname stmt        ("While '(_') _"     [99,91   ] 91)

  | NewC vname cname       ("_:=new _"  [99,   99] 95) (* object creation  *)
  | Cast vname cname vname ("_:='(_')_" [99,99,99] 95) (* assignment, cast *)
  | FAcc vname vname vnam  ("_:=_.._"   [99,99,99] 95) (* field access     *)
  | FAss vname vnam  vname ("_.._:=_"   [99,99,99] 95) (* field assigment  *)
  | Call vname cname vname mname vname                 (* method call      *)
                           ("_:={_}_.._'(_')" [99,99,99,99,99] 95)
  | Meth cname mname       (* virtual method *)
  | Impl cname mname       (* method implementation *)

(*###TO Product_Type_lemmas.ML*)
lemma pair_imageI [intro]: "(a, b) \<in> A ==> f a b : (%(a, b). f a b) ` A"
apply (rule_tac x = "(a,b)" in image_eqI)
apply  auto
done

end

