(*  Title:      HOLCF/Tr.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduce infix if_then_else_fi and boolean connectives andalso, orelse
*)

Tr = Lift +

syntax
  tr	:: "type"
translations
  "tr" == (type) "bool lift" 

consts
	TT,FF           :: "tr"
        Icifte          :: "tr -> 'c -> 'c -> 'c"
        trand           :: "tr -> tr -> tr"
        tror            :: "tr -> tr -> tr"
        neg             :: "tr -> tr"
        plift           :: "('a::term => bool) => 'a lift -> tr"

syntax  "@cifte"        :: "tr=>'c=>'c=>'c" ("(3If _/ (then _/ else _) fi)" 60)
        "@andalso"      :: "tr => tr => tr" ("_ andalso _" [36,35] 35)
        "@orelse"       :: "tr => tr => tr" ("_ orelse _"  [31,30] 30)
 
translations 
	     "x andalso y" == "trand`x`y"
             "x orelse y"  == "tror`x`y"
             "If b then e1 else e2 fi" == "Icifte`b`e1`e2"
defs
  TT_def      "TT==Def True"
  FF_def      "FF==Def False"
  neg_def     "neg == flift2 Not"
  ifte_def    "Icifte == (LAM b t e.flift1(%b.if b then t else e)`b)"
  andalso_def "trand == (LAM x y.If x then y else FF fi)"
  orelse_def  "tror == (LAM x y.If x then TT else y fi)"
(* andalso, orelse are different from strict functions 
  andalso_def "trand == flift1(flift2 o (op &))"
  orelse_def  "tror == flift1(flift2 o (op |))"
*)
  plift_def   "plift p == (LAM x. flift1(%a.Def(p a))`x)"

(* FIXME remove?
syntax
  "GeqTT"        :: "tr => bool"               ("(\\<lceil>_\\<rceil>)")
  "GeqFF"        :: "tr => bool"               ("(\\<lfloor>_\\<rfloor>)")

translations
  "\\<lceil>x\\<rceil>" == "x = TT"
  "\\<lfloor>x\\<rfloor>" == "x = FF"
*)

end

