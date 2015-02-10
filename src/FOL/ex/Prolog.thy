(*  Title:      FOL/ex/Prolog.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section {* First-Order Logic: PROLOG examples *}

theory Prolog
imports FOL
begin

typedecl 'a list
instance list :: ("term") "term" ..

axiomatization
  Nil     :: "'a list" and
  Cons    :: "['a, 'a list]=> 'a list"    (infixr ":" 60) and
  app     :: "['a list, 'a list, 'a list] => o" and
  rev     :: "['a list, 'a list] => o"
where
  appNil:  "app(Nil,ys,ys)" and
  appCons: "app(xs,ys,zs) ==> app(x:xs, ys, x:zs)" and
  revNil:  "rev(Nil,Nil)" and
  revCons: "[| rev(xs,ys);  app(ys, x:Nil, zs) |] ==> rev(x:xs, zs)"

schematic_lemma "app(a:b:c:Nil, d:e:Nil, ?x)"
apply (rule appNil appCons)
apply (rule appNil appCons)
apply (rule appNil appCons)
apply (rule appNil appCons)
done

schematic_lemma "app(?x, c:d:Nil, a:b:c:d:Nil)"
apply (rule appNil appCons)+
done

schematic_lemma "app(?x, ?y, a:b:c:d:Nil)"
apply (rule appNil appCons)+
back
back
back
back
done

(*app([x1,...,xn], y, ?z) requires (n+1) inferences*)
(*rev([x1,...,xn], ?y) requires (n+1)(n+2)/2 inferences*)

lemmas rules = appNil appCons revNil revCons

schematic_lemma "rev(a:b:c:d:Nil, ?x)"
apply (rule rules)+
done

schematic_lemma "rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:Nil, ?w)"
apply (rule rules)+
done

schematic_lemma "rev(?x, a:b:c:Nil)"
apply (rule rules)+  -- {* does not solve it directly! *}
back
back
done

(*backtracking version*)
ML {*
fun prolog_tac ctxt =
  DEPTH_FIRST (has_fewer_prems 1) (resolve_tac ctxt @{thms rules} 1)
*}

schematic_lemma "rev(?x, a:b:c:Nil)"
apply (tactic \<open>prolog_tac @{context}\<close>)
done

schematic_lemma "rev(a:?x:c:?y:Nil, d:?z:b:?u)"
apply (tactic \<open>prolog_tac @{context}\<close>)
done

(*rev([a..p], ?w) requires 153 inferences *)
schematic_lemma "rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil, ?w)"
apply (tactic {*
  DEPTH_SOLVE (resolve_tac @{context} ([@{thm refl}, @{thm conjI}] @ @{thms rules}) 1) *})
done

(*?x has 16, ?y has 32;  rev(?y,?w) requires 561 (rather large) inferences
  total inferences = 2 + 1 + 17 + 561 = 581*)
schematic_lemma "a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil = ?x & app(?x,?x,?y) & rev(?y,?w)"
apply (tactic {*
  DEPTH_SOLVE (resolve_tac @{context} ([@{thm refl}, @{thm conjI}] @ @{thms rules}) 1) *})
done

end
