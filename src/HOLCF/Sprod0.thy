(*  Title:      HOLCF/Sprod0.thy
    ID:         $Id$
    Author:     Franz Regensburger

Strict product with typedef.
*)

Sprod0 = Cfun3 +

constdefs
  Spair_Rep     :: ['a,'b] => ['a,'b] => bool
 "Spair_Rep == (%a b. %x y.(~a=UU & ~b=UU --> x=a  & y=b ))"

typedef (Sprod)  ('a, 'b) "**" (infixr 20) = "{f. ? a b. f = Spair_Rep (a::'a) (b::'b)}"

syntax (xsymbols)
  "**"		:: [type, type] => type	 ("(_ \\<otimes>/ _)" [21,20] 20)
syntax (HTML output)
  "**"		:: [type, type] => type	 ("(_ \\<otimes>/ _)" [21,20] 20)

consts
  Ispair        :: "['a,'b] => ('a ** 'b)"
  Isfst         :: "('a ** 'b) => 'a"
  Issnd         :: "('a ** 'b) => 'b"  

defs
   (*defining the abstract constants*)

  Ispair_def    "Ispair a b == Abs_Sprod(Spair_Rep a b)"

  Isfst_def     "Isfst(p) == @z.        (p=Ispair UU UU --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b   --> z=a)"  

  Issnd_def     "Issnd(p) == @z.        (p=Ispair UU UU  --> z=UU)
                &(! a b. ~a=UU & ~b=UU & p=Ispair a b    --> z=b)"  


end
