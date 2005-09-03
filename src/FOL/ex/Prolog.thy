(*  Title:      FOL/ex/prolog.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* First-Order Logic: PROLOG examples *}

theory Prolog
imports FOL
begin

typedecl 'a list
arities list :: ("term") "term"
consts
  Nil     :: "'a list"
  Cons    :: "['a, 'a list]=> 'a list"    (infixr ":" 60)
  app     :: "['a list, 'a list, 'a list] => o"
  rev     :: "['a list, 'a list] => o"
axioms
  appNil:  "app(Nil,ys,ys)"
  appCons: "app(xs,ys,zs) ==> app(x:xs, ys, x:zs)"
  revNil:  "rev(Nil,Nil)"
  revCons: "[| rev(xs,ys);  app(ys, x:Nil, zs) |] ==> rev(x:xs, zs)"

ML {* use_legacy_bindings (the_context ()) *}

end
