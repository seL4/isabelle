(*  Title: 	ZF/Rel.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Relations in Zermelo-Fraenkel Set Theory 
*)

Rel = ZF +
consts
    refl,irrefl,equiv      :: "[i,i]=>o"
    sym,asym,antisym,trans :: "i=>o"
    trans_on               :: "[i,i]=>o"	("trans[_]'(_')")

defs
  refl_def     "refl(A,r) == (ALL x: A. <x,x> : r)"

  irrefl_def   "irrefl(A,r) == ALL x: A. <x,x> ~: r"

  sym_def      "sym(r) == ALL x y. <x,y>: r --> <y,x>: r"

  asym_def     "asym(r) == ALL x y. <x,y>:r --> ~ <y,x>:r"

  antisym_def  "antisym(r) == ALL x y.<x,y>:r --> <y,x>:r --> x=y"

  trans_def    "trans(r) == ALL x y z. <x,y>: r --> <y,z>: r --> <x,z>: r"

  trans_on_def "trans[A](r) == ALL x:A. ALL y:A. ALL z:A. 	\
\                          <x,y>: r --> <y,z>: r --> <x,z>: r"

  equiv_def    "equiv(A,r) == r <= A*A & refl(A,r) & sym(r) & trans(r)"

end
