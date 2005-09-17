(*  Title:    HOL/IMPP/Com.thy
    ID:       $Id$
    Author:   David von Oheimb (based on a theory by Tobias Nipkow et al), TUM
    Copyright 1999 TUM
*)

header {* Semantics of arithmetic and boolean expressions, Syntax of commands *}

theory Com
imports Main
begin

types    val = nat   (* for the meta theory, this may be anything, but with
                        current Isabelle, types cannot be refined later *)
typedecl glb
typedecl loc

consts
  Arg :: loc
  Res :: loc

datatype vname  = Glb glb | Loc loc
types    globs  = "glb => val"
         locals = "loc => val"
datatype state  = st globs locals
(* for the meta theory, the following would be sufficient:
typedecl state
consts   st :: "[globs , locals] => state"
*)
types    aexp   = "state => val"
         bexp   = "state => bool"

typedecl pname

datatype com
      = SKIP
      | Ass   vname aexp        ("_:==_"                [65, 65    ] 60)
      | Local loc aexp com      ("LOCAL _:=_ IN _"      [65,  0, 61] 60)
      | Semi  com  com          ("_;; _"                [59, 60    ] 59)
      | Cond  bexp com com      ("IF _ THEN _ ELSE _"   [65, 60, 61] 60)
      | While bexp com          ("WHILE _ DO _"         [65,     61] 60)
      | BODY  pname
      | Call  vname pname aexp  ("_:=CALL _'(_')"       [65, 65,  0] 60)

consts bodies :: "(pname  *  com) list"(* finitely many procedure definitions *)
       body   :: " pname ~=> com"
defs   body_def: "body == map_of bodies"


(* Well-typedness: all procedures called must exist *)
consts WTs :: "com set"
syntax WT  :: "com => bool"
translations "WT c" == "c : WTs"

inductive WTs intros

    Skip:    "WT SKIP"

    Assign:  "WT (X :== a)"

    Local:   "WT c ==>
              WT (LOCAL Y := a IN c)"

    Semi:    "[| WT c0; WT c1 |] ==>
              WT (c0;; c1)"

    If:      "[| WT c0; WT c1 |] ==>
              WT (IF b THEN c0 ELSE c1)"

    While:   "WT c ==>
              WT (WHILE b DO c)"

    Body:    "body pn ~= None ==>
              WT (BODY pn)"

    Call:    "WT (BODY pn) ==>
              WT (X:=CALL pn(a))"

inductive_cases WTs_elim_cases:
  "WT SKIP"  "WT (X:==a)"  "WT (LOCAL Y:=a IN c)"
  "WT (c1;;c2)"  "WT (IF b THEN c1 ELSE c2)"  "WT (WHILE b DO c)"
  "WT (BODY P)"  "WT (X:=CALL P(a))"

constdefs
  WT_bodies :: bool
  "WT_bodies == !(pn,b):set bodies. WT b"

ML {* use_legacy_bindings (the_context ()) *}

end
