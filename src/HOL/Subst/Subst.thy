(*  Title:      Substitutions/subst.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Substitutions on uterms
*)

Subst = AList + UTerm +

consts

  "=$="  ::  "[('a*('a uterm)) list,('a*('a uterm)) list] => bool" (infixr 52)
  "<|"   ::  "'a uterm => ('a * 'a uterm) list => 'a uterm"        (infixl 55)
  "<>"   ::  "[('a*('a uterm)) list, ('a*('a uterm)) list] 
                 => ('a*('a uterm)) list"                          (infixl 56)
  sdom   ::  "('a*('a uterm)) list => 'a set"
  srange ::  "('a*('a uterm)) list => 'a set"


primrec "op <|"   uterm
  subst_Var      "(Var v <| s) = assoc v (Var v) s"
  subst_Const  "(Const c <| s) = Const c"
  subst_Comb  "(Comb M N <| s) = Comb (M <| s) (N <| s)"


defs 

  subst_eq_def  "r =$= s == ALL t.t <| r = t <| s"

  comp_def    "al <> bl == alist_rec al bl (%x y xs g. (x,y <| bl)#g)"

  sdom_def
  "sdom(al) == alist_rec al {}  
                (%x y xs g. if Var(x)=y then g - {x} else g Un {x})"

  srange_def   
   "srange(al) == Union({y. EX x:sdom(al). y=vars_of(Var(x) <| al)})"

end
