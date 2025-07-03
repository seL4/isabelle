(*  Title:      FOL/ex/Prolog.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section \<open>First-Order Logic: PROLOG examples\<close>

theory Prolog
imports FOL
begin

typedecl 'a list
instance list :: (\<open>term\<close>) \<open>term\<close> ..

axiomatization
  Nil     :: \<open>'a list\<close> and
  Cons    :: \<open>['a, 'a list]=> 'a list\<close>    (infixr \<open>:\<close> 60) and
  app     :: \<open>['a list, 'a list, 'a list] => o\<close> and
  rev     :: \<open>['a list, 'a list] => o\<close>
where
  appNil:  \<open>app(Nil,ys,ys)\<close> and
  appCons: \<open>app(xs,ys,zs) ==> app(x:xs, ys, x:zs)\<close> and
  revNil:  \<open>rev(Nil,Nil)\<close> and
  revCons: \<open>[| rev(xs,ys);  app(ys, x:Nil, zs) |] ==> rev(x:xs, zs)\<close>

schematic_goal \<open>app(a:b:c:Nil, d:e:Nil, ?x)\<close>
apply (rule appNil appCons)
apply (rule appNil appCons)
apply (rule appNil appCons)
apply (rule appNil appCons)
done

schematic_goal \<open>app(?x, c:d:Nil, a:b:c:d:Nil)\<close>
apply (rule appNil appCons)+
done

schematic_goal \<open>app(?x, ?y, a:b:c:d:Nil)\<close>
apply (rule appNil appCons)+
back
back
back
back
done

(*app([x1,...,xn], y, ?z) requires (n+1) inferences*)
(*rev([x1,...,xn], ?y) requires (n+1)(n+2)/2 inferences*)

lemmas rules = appNil appCons revNil revCons

schematic_goal \<open>rev(a:b:c:d:Nil, ?x)\<close>
apply (rule rules)+
done

schematic_goal \<open>rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:Nil, ?w)\<close>
apply (rule rules)+
done

schematic_goal \<open>rev(?x, a:b:c:Nil)\<close>
apply (rule rules)+  \<comment> \<open>does not solve it directly!\<close>
back
back
done

(*backtracking version*)
ML \<open>
fun prolog_tac ctxt =
  DEPTH_FIRST Thm.no_prems (resolve_tac ctxt @{thms rules} 1)
\<close>

schematic_goal \<open>rev(?x, a:b:c:Nil)\<close>
apply (tactic \<open>prolog_tac \<^context>\<close>)
done

schematic_goal \<open>rev(a:?x:c:?y:Nil, d:?z:b:?u)\<close>
apply (tactic \<open>prolog_tac \<^context>\<close>)
done

(*rev([a..p], ?w) requires 153 inferences *)
schematic_goal \<open>rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil, ?w)\<close>
apply (tactic \<open>
  DEPTH_SOLVE (resolve_tac \<^context> ([@{thm refl}, @{thm conjI}] @ @{thms rules}) 1)\<close>)
done

(*?x has 16, ?y has 32;  rev(?y,?w) requires 561 (rather large) inferences
  total inferences = 2 + 1 + 17 + 561 = 581*)
schematic_goal \<open>a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil = ?x \<and> app(?x,?x,?y) \<and> rev(?y,?w)\<close>
apply (tactic \<open>
  DEPTH_SOLVE (resolve_tac \<^context> ([@{thm refl}, @{thm conjI}] @ @{thms rules}) 1)\<close>)
done

end
