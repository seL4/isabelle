(*  Title:      Terms.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Terms = Cube+

consts
  lambda        :: i
  unmark        :: i=>i
  Apl           :: [i,i]=>i

translations
  "Apl(n,m)" == "App(0,n,m)"
  
inductive
  domains       "lambda" <= "redexes"
  intrs
    Lambda_Var  "               n \\<in> nat ==>     Var(n):lambda"
    Lambda_Fun  "            u \\<in> lambda ==>     Fun(u):lambda"
    Lambda_App  "[|u \\<in> lambda; v \\<in> lambda|]==> Apl(u,v):lambda"
  type_intrs    "redexes.intrs@bool_typechecks"

primrec
  "unmark(Var(n)) = Var(n)"
  "unmark(Fun(u)) = Fun(unmark(u))"
  "unmark(App(b,f,a)) = Apl(unmark(f), unmark(a))"

end


