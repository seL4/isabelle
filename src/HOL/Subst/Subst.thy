(*  Title:      Substitutions/subst.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Substitutions on uterms
*)

Subst = Setplus + AList + UTLemmas +

consts

  "=s="  ::  "[('a*('a uterm)) list,('a*('a uterm)) list] => bool" (infixr 52)

  "<|"   ::  "['a uterm,('a*('a uterm)) list] => 'a uterm"         (infixl 55)
  "<>"   ::  "[('a*('a uterm)) list, ('a*('a uterm)) list] => 
                                    ('a*('a uterm)) list"         (infixl 56)
  sdom   ::  "('a*('a uterm)) list => 'a set"
  srange ::  "('a*('a uterm)) list => 'a set"

rules 

  subst_eq_def  "r =s= s == ALL t.t <| r = t <| s"

  subst_def    
  "t <| al == uterm_rec t (%x.assoc x (Var x) al)       
                         (%x.Const(x))                  
                         (%u v q r.Comb q r)"

  comp_def    "al <> bl == alist_rec al bl (%x y xs g.(x,y <| bl)#g)"

  sdom_def
  "sdom(al) == alist_rec al {}  
                (%x y xs g.if Var(x)=y then g Int Compl({x}) else g Un {x})"
  srange_def   
  "srange(al) == Union({y. EX x:sdom(al).y=vars_of(Var(x) <| al)})"

end
