(*  Title: 	CTT/ex/elim
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Some examples taken from P. Martin-L\"of, Intuitionistic type theory
	(Bibliopolis, 1984).

by (safe_tac prems 1);
by (step_tac prems 1);
by (pc_tac prems 1);
*)

writeln"Examples with elimination rules";


writeln"This finds the functions fst and snd!"; 
val prems = goal CTT.thy "A type ==> ?a : (A*A) --> A";
by (pc_tac prems 1  THEN  fold_tac basic_defs);   (*puts in fst and snd*)
result();
writeln"first solution is fst;  backtracking gives snd";
back(); 
back() handle ERROR => writeln"And there are indeed no others";  


writeln"Double negation of the Excluded Middle";
val prems = goal CTT.thy "A type ==> ?a : ((A + (A-->F)) --> F) --> F";
by (intr_tac prems);
by (rtac ProdE 1);
by (assume_tac 1);
by (pc_tac prems 1);
result();

val prems = goal CTT.thy 
    "[| A type;  B type |] ==> ?a : (A*B) --> (B*A)";
by (pc_tac prems 1);
result();
(*The sequent version (ITT) could produce an interesting alternative
  by backtracking.  No longer.*)

writeln"Binary sums and products";
val prems = goal CTT.thy
   "[| A type;  B type;  C type |] ==> ?a : (A+B --> C) --> (A-->C) * (B-->C)";
by (pc_tac prems 1);
result();

(*A distributive law*)
val prems = goal CTT.thy 
    "[| A type;  B type;  C type |] ==> ?a : A * (B+C)  -->  (A*B + A*C)";
by (pc_tac prems 1);
result();

(*more general version, same proof*)
val prems = goal CTT.thy 
    "[| A type;  !!x. x:A ==> B(x) type;  !!x. x:A ==> C(x) type|] ==> \
\    ?a : (SUM x:A. B(x) + C(x)) --> (SUM x:A. B(x)) + (SUM x:A. C(x))";
by (pc_tac prems 1);
result();

writeln"Construction of the currying functional";
val prems = goal CTT.thy 
    "[| A type;  B type;  C type |] ==> ?a : (A*B --> C) --> (A--> (B-->C))";
by (pc_tac prems 1);
result();

(*more general goal with same proof*)
val prems = goal CTT.thy  
    "[| A type; !!x. x:A ==> B(x) type; !!z. z: (SUM x:A. B(x)) ==> C(z) type|] \
\    ==> ?a : (PROD z : (SUM x:A . B(x)) . C(z)) \
\         --> (PROD x:A . PROD y:B(x) . C(<x,y>))";
by (pc_tac prems 1);
result();

writeln"Martin-Lof (1984), page 48: axiom of sum-elimination (uncurry)";
val prems = goal CTT.thy 
    "[| A type;  B type;  C type |] ==> ?a : (A --> (B-->C)) --> (A*B --> C)";
by (pc_tac prems 1);
result();

(*more general goal with same proof*)
val prems = goal CTT.thy 
  "[| A type; !!x. x:A ==> B(x) type; !!z. z : (SUM x:A . B(x)) ==> C(z) type|] \
\  ==> ?a : (PROD x:A . PROD y:B(x) . C(<x,y>)) \
\       --> (PROD z : (SUM x:A . B(x)) . C(z))";
by (pc_tac prems 1);
result();

writeln"Function application";
val prems = goal CTT.thy  
    "[| A type;  B type |] ==> ?a : ((A --> B) * A) --> B";
by (pc_tac prems 1);
result();

writeln"Basic test of quantifier reasoning";
val prems = goal CTT.thy  
    "[| A type;  B type;  !!x y.[| x:A;  y:B |] ==> C(x,y) type |] ==> \
\    ?a :     (SUM y:B . PROD x:A . C(x,y))  \
\         --> (PROD x:A . SUM y:B . C(x,y))";
by (pc_tac prems 1);
result();

(*faulty proof attempt, stripping the quantifiers in wrong sequence
by (intr_tac[]);
by (pc_tac prems 1);        ...fails!!  *)

writeln"Martin-Lof (1984) pages 36-7: the combinator S";
val prems = goal CTT.thy  
    "[| A type;  !!x. x:A ==> B(x) type;  \
\       !!x y.[| x:A; y:B(x) |] ==> C(x,y) type |] \
\    ==> ?a :    (PROD x:A. PROD y:B(x). C(x,y)) \
\            --> (PROD f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))";
by (pc_tac prems 1);
result();

writeln"Martin-Lof (1984) page 58: the axiom of disjunction elimination";
val prems = goal CTT.thy
    "[| A type;  B type;  !!z. z: A+B ==> C(z) type|] ==> \
\    ?a : (PROD x:A. C(inl(x))) --> (PROD y:B. C(inr(y)))  \
\         --> (PROD z: A+B. C(z))";
by (pc_tac prems 1);
result();

(*towards AXIOM OF CHOICE*)
val prems = goal CTT.thy  
  "[| A type;  B type;  C type |] ==> ?a : (A --> B*C) --> (A-->B) * (A-->C)";
by (pc_tac prems 1);
by (fold_tac basic_defs);   (*puts in fst and snd*)
result();

(*Martin-Lof (1984) page 50*)
writeln"AXIOM OF CHOICE!!!  Delicate use of elimination rules";
val prems = goal CTT.thy   
    "[| A type;  !!x. x:A ==> B(x) type;  \
\       !!x y.[| x:A;  y:B(x) |] ==> C(x,y) type|]  \
\    ==> ?a :    (PROD x:A. SUM y:B(x). C(x,y))    \
\            --> (SUM f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))";
by (intr_tac prems);
by (add_mp_tac 2);
by (add_mp_tac 1);
by (etac SumE_fst 1);
by (rtac replace_type 1);
by (rtac subst_eqtyparg 1);
by (resolve_tac comp_rls 1);
by (rtac SumE_snd 4);
by (typechk_tac (SumE_fst::prems));
result();

writeln"Axiom of choice.  Proof without fst, snd.  Harder still!"; 
val prems = goal CTT.thy   
    "[| A type;  !!x.x:A ==> B(x) type;  \
\       !!x y.[| x:A;  y:B(x) |] ==> C(x,y) type|] \
\    ==> ?a :    (PROD x:A. SUM y:B(x). C(x,y)) \
\            --> (SUM f: (PROD x:A. B(x)). PROD x:A. C(x, f`x))";
by (intr_tac prems);
(*Must not use add_mp_tac as subst_prodE hides the construction.*)
by (resolve_tac [ProdE RS SumE] 1  THEN  assume_tac 1);
by (TRYALL assume_tac);
by (rtac replace_type 1);
by (rtac subst_eqtyparg 1);
by (resolve_tac comp_rls 1);
by (etac (ProdE RS SumE) 4);
by (typechk_tac prems);
by (rtac replace_type 1);
by (rtac subst_eqtyparg 1);
by (resolve_tac comp_rls 1);
by (typechk_tac prems);
by (assume_tac 1);
by (fold_tac basic_defs);  (*puts in fst and snd*)
result();

writeln"Example of sequent_style deduction"; 
(*When splitting z:A*B, the assumption C(z) is affected;  ?a becomes
    lam u. split(u,%v w.split(v,%x y.lam z. <x,<y,z>>) ` w)     *)
val prems = goal CTT.thy   
    "[| A type;  B type;  !!z. z:A*B ==> C(z) type |] ==>  \
\    ?a : (SUM z:A*B. C(z)) --> (SUM u:A. SUM v:B. C(<u,v>))";
by (resolve_tac intr_rls 1);
by (biresolve_tac safe_brls 2);
(*Now must convert assumption C(z) into antecedent C(<kd,ke>) *)
by (res_inst_tac [ ("a","y") ] ProdE 2);
by (typechk_tac prems);
by (rtac SumE 1  THEN  assume_tac 1);
by (intr_tac[]);
by (TRYALL assume_tac);
by (typechk_tac prems);
result();

writeln"Reached end of file.";
