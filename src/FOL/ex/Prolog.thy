(*  Title: 	FOL/ex/prolog.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

First-Order Logic: PROLOG examples

Inherits from FOL the class term, the type o, and the coercion Trueprop
*)

Prolog = FOL +
types   list 1
arities list    :: (term)term
consts  Nil     :: "'a list"
        ":"     :: "['a, 'a list]=> 'a list"            (infixr 60)
        app     :: "['a list, 'a list, 'a list] => o"
        rev     :: "['a list, 'a list] => o"
rules   appNil  "app(Nil,ys,ys)"
        appCons "app(xs,ys,zs) ==> app(x:xs, ys, x:zs)"
        revNil  "rev(Nil,Nil)"
        revCons "[| rev(xs,ys);  app(ys, x:Nil, zs) |] ==> rev(x:xs, zs)"
end
