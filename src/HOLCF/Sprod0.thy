(*  Title:      HOLCF/sprod0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Strict product
*)

Sprod0 = Cfun3 +

(* new type for strict product *)

types "**" 2        (infixr 20)

arities "**" :: (pcpo,pcpo)term 

syntax (symbols)
 
  "**"		:: [type, type] => type		("(_ \\<otimes>/ _)" [21,20] 20)

consts
  Sprod         :: "('a => 'b => bool)set"
  Spair_Rep     :: "['a,'b] => ['a,'b] => bool"
  Rep_Sprod     :: "('a ** 'b) => ('a => 'b => bool)"
  Abs_Sprod     :: "('a => 'b => bool) => ('a ** 'b)"
  Ispair        :: "['a,'b] => ('a ** 'b)"
  Isfst         :: "('a ** 'b) => 'a"
  Issnd         :: "('a ** 'b) => 'b"  

defs
  Spair_Rep_def         "Spair_Rep == (%a b. %x y.
                                (~a=UU & ~b=UU --> x=a  & y=b ))"

  Sprod_def             "Sprod == {f. ? a b. f = Spair_Rep a b}"

rules
  (*faking a type definition... *)
  (* "**" is isomorphic to Sprod *)

  Rep_Sprod             "Rep_Sprod(p):Sprod"            
  Rep_Sprod_inverse     "Abs_Sprod(Rep_Sprod(p)) = p"   
  Abs_Sprod_inverse     "f:Sprod ==> Rep_Sprod(Abs_Sprod(f)) = f"

defs
   (*defining the abstract constants*)

  Ispair_def    "Ispair a b == Abs_Sprod(Spair_Rep a b)"

  Isfst_def     "Isfst(p) == @z.
                                        (p=Ispair UU UU --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b   --> z=a)"  

  Issnd_def     "Issnd(p) == @z.
                                        (p=Ispair UU UU  --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b    --> z=b)"  


end

