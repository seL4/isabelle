(*  Title:    HOL/IMPP/Com.thy
    ID:       $Id$
    Author:   David von Oheimb (based on a theory by Tobias Nipkow et al), TUM
    Copyright 1999 TUM

Semantics of arithmetic and boolean expressions, Syntax of commands
*)

Com = Main +

types	 val = nat   (* for the meta theory, this may be anything, but with
                        current Isabelle, types cannot be refined later *)
types	 glb
         loc
arities	 (*val,*)glb,loc :: type
consts   Arg, Res :: loc

datatype vname  = Glb glb | Loc loc
types	 globs  = glb => val
	 locals = loc => val
datatype state  = st globs locals
(* for the meta theory, the following would be sufficient:
types    state
arities  state::type
consts   st:: [globs , locals] => state
*)
types	 aexp   = state => val
	 bexp   = state => bool

types	pname
arities	pname  :: type

datatype com
      = SKIP
      | Ass   vname aexp	("_:==_"	        [65, 65    ] 60)
      | Local loc aexp com	("LOCAL _:=_ IN _"	[65,  0, 61] 60)
      | Semi  com  com		("_;; _"	        [59, 60    ] 59)
      | Cond  bexp com com	("IF _ THEN _ ELSE _"	[65, 60, 61] 60)
      | While bexp com		("WHILE _ DO _"		[65,     61] 60)
      | BODY  pname
      | Call  vname pname aexp	("_:=CALL _'(_')"	[65, 65,  0] 60)

consts bodies :: "(pname  *  com) list"(* finitely many procedure definitions *)
       body   :: " pname ~=> com"
defs   body_def  "body == map_of bodies"


(* Well-typedness: all procedures called must exist *)
consts WTs :: com set
syntax WT  :: com => bool
translations "WT c" == "c : WTs"

inductive WTs intrs

    Skip    "WT SKIP"

    Assign  "WT (X :== a)"

    Local   "WT c ==>
             WT (LOCAL Y := a IN c)"

    Semi    "[| WT c0; WT c1 |] ==>
             WT (c0;; c1)"

    If      "[| WT c0; WT c1 |] ==>
             WT (IF b THEN c0 ELSE c1)"

    While   "WT c ==>
             WT (WHILE b DO c)"

    Body    "body pn ~= None ==>
             WT (BODY pn)"

    Call    "WT (BODY pn) ==>
             WT (X:=CALL pn(a))"

constdefs
  WT_bodies :: bool
 "WT_bodies == !(pn,b):set bodies. WT b"

end
