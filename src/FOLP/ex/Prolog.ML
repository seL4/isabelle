(*  Title:      FOLP/ex/prolog.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For ex/prolog.thy.  First-Order Logic: PROLOG examples
*)

open Prolog;

goal Prolog.thy "app(a:b:c:Nil, d:e:Nil, ?x)";
by (resolve_tac [appNil,appCons] 1);
by (resolve_tac [appNil,appCons] 1);
by (resolve_tac [appNil,appCons] 1);
by (resolve_tac [appNil,appCons] 1);
prth (result());

goal Prolog.thy "app(?x, c:d:Nil, a:b:c:d:Nil)";
by (REPEAT (resolve_tac [appNil,appCons] 1));
result();


goal Prolog.thy "app(?x, ?y, a:b:c:d:Nil)";
by (REPEAT (resolve_tac [appNil,appCons] 1));
back();
back();
back();
back();
result();


(*app([x1,...,xn], y, ?z) requires (n+1) inferences*)
(*rev([x1,...,xn], ?y) requires (n+1)(n+2)/2 inferences*)

goal Prolog.thy "rev(a:b:c:d:Nil, ?x)";
val rules = [appNil,appCons,revNil,revCons];
by (REPEAT (resolve_tac rules 1));
result();

goal Prolog.thy "rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:Nil, ?w)";
by (REPEAT (resolve_tac rules 1));
result();

goal Prolog.thy "rev(?x, a:b:c:Nil)";
by (REPEAT (resolve_tac rules 1)); (*does not solve it directly!*)
back();
back();

(*backtracking version*)
val prolog_tac = DEPTH_FIRST (has_fewer_prems 1) (resolve_tac rules 1);

choplev 0;
by prolog_tac;
result();

goal Prolog.thy "rev(a:?x:c:?y:Nil, d:?z:b:?u)";
by prolog_tac;
result();

(*rev([a..p], ?w) requires 153 inferences *)
goal Prolog.thy "rev(a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil, ?w)";
by (DEPTH_SOLVE (resolve_tac ([refl,conjI]@rules) 1));
(*Poly/ML: 4 secs >> 38 lips*)
result();

(*?x has 16, ?y has 32;  rev(?y,?w) requires 561 (rather large) inferences;
  total inferences = 2 + 1 + 17 + 561 = 581*)
goal Prolog.thy
    "a:b:c:d:e:f:g:h:i:j:k:l:m:n:o:p:Nil = ?x & app(?x,?x,?y) & rev(?y,?w)";
by (DEPTH_SOLVE (resolve_tac ([refl,conjI]@rules) 1));
(*Poly/ML: 29 secs >> 20 lips*)
result();

writeln"Reached end of file.";
