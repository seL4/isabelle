(*  Title:      FOL/ex/Prolog.thy
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

lemma "app(a:b:c:Nil, d:e:Nil, ?x)"
apply (rule appNil appCons)
apply (rule appNil appCons)
apply (rule appNil appCons)
apply (rule appNil appCons)
done

lemma "app(?x, c:d:Nil, a:b:c:d:Nil)"
apply (rule appNil appCons)+
done

lemma "app(?x, ?y, a:b:c:d:Nil)"
apply (rule appNil appCons)+
back
back
back
back
done

(*app([x1,...,xn], y, ?z) requires (n+1) inferences*)
(*rev([x1,...,xn], ?y) requires (n+1)(n+2)/2 inferences*)

lemmas rules = appNil appCons revNil revCons

lemma "rev(a:b:c:d:Nil, ?x)"
apply (rule rules)+
done

lemma "rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:Nil, ?w)"
apply (rule rules)+
done

lemma "rev(?x, a:b:c:Nil)"
apply (rule rules)+  -- {* does not solve it directly! *}
back
back
done

(*backtracking version*)
ML {*
val prolog_tac = DEPTH_FIRST (has_fewer_prems 1) (resolve_tac (@{thms rules}) 1)
*}

lemma "rev(?x, a:b:c:Nil)"
apply (tactic prolog_tac)
done

lemma "rev(a:?x:c:?y:Nil, d:?z:b:?u)"
apply (tactic prolog_tac)
done

(*rev([a..p], ?w) requires 153 inferences *)
lemma "rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil, ?w)"
apply (tactic {* DEPTH_SOLVE (resolve_tac ([@{thm refl}, @{thm conjI}] @ @{thms rules}) 1) *})
done

(*?x has 16, ?y has 32;  rev(?y,?w) requires 561 (rather large) inferences
  total inferences = 2 + 1 + 17 + 561 = 581*)
lemma "a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil = ?x & app(?x,?x,?y) & rev(?y,?w)"
apply (tactic {* DEPTH_SOLVE (resolve_tac ([@{thm refl}, @{thm conjI}] @ @{thms rules}) 1) *})
done

end
