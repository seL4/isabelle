(*  Title:      92/CCL/eval
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

*)



(*** Evaluation ***)

val EVal_rls = ref [trueV,falseV,pairV,lamV,caseVtrue,caseVfalse,caseVpair,caseVlam];
val eval_tac = DEPTH_SOLVE_1 (resolve_tac (!EVal_rls) 1);
fun ceval_tac rls = DEPTH_SOLVE_1 (resolve_tac (!EVal_rls@rls) 1);

val prems = goalw thy [apply_def]
   "[| f ---> lam x.b(x);  b(a) ---> c |] ==> f ` a ---> c";
by (ceval_tac prems);
qed "applyV";

EVal_rls := !EVal_rls @ [applyV];

val major::prems = goalw thy [let_def]
   "[| t ---> a;  f(a) ---> c |] ==> let x be t in f(x) ---> c";
by (rtac (major RS canonical) 1);
by (REPEAT (DEPTH_SOLVE_1 (resolve_tac ([major]@prems@(!EVal_rls)) 1 ORELSE
                           etac substitute 1)));
qed "letV";

val prems = goalw thy [fix_def]
   "f(fix(f)) ---> c ==> fix(f) ---> c";
by (rtac applyV 1);
by (rtac lamV 1);
by (resolve_tac prems 1);
qed "fixV";

val prems = goalw thy [letrec_def]
    "h(t,%y.letrec g x be h(x,g) in g(y)) ---> c ==> \
\                  letrec g x be h(x,g) in g(t) ---> c";
by (REPEAT (resolve_tac (prems @ [fixV,applyV,lamV]) 1));
qed "letrecV";

EVal_rls := !EVal_rls @ [letV,letrecV,fixV];

fun mk_V_rl s = prove_goalw thy data_defs s (fn prems => [ceval_tac prems]);

val V_rls = map mk_V_rl 
             ["true ---> true",
              "false ---> false",
              "[| b--->true;  t--->c |] ==> if b then t else u ---> c",
              "[| b--->false;  u--->c |] ==> if b then t else u ---> c",
              "<a,b> ---> <a,b>",
              "[| t ---> <a,b>;  h(a,b) ---> c |] ==> split(t,h) ---> c",
              "zero ---> zero",
              "succ(n) ---> succ(n)",
              "[| n ---> zero; t ---> c |] ==> ncase(n,t,u) ---> c",
              "[| n ---> succ(x); u(x) ---> c |] ==> ncase(n,t,u) ---> c",
              "[| n ---> zero; t ---> c |] ==> nrec(n,t,u) ---> c",
              "[| n--->succ(x); u(x,nrec(x,t,u))--->c |] ==> nrec(n,t,u)--->c",
              "[] ---> []",
              "h$t ---> h$t",
              "[| l ---> []; t ---> c |] ==> lcase(l,t,u) ---> c",
              "[| l ---> x$xs; u(x,xs) ---> c |] ==> lcase(l,t,u) ---> c",
              "[| l ---> []; t ---> c |] ==> lrec(l,t,u) ---> c",
              "[| l--->x$xs; u(x,xs,lrec(xs,t,u))--->c |] ==> lrec(l,t,u)--->c"];

EVal_rls := !EVal_rls @ V_rls;

(* Factorial *)

val prems = goal thy
    "letrec f n be ncase(n,succ(zero),%x.nrec(n,zero,%y g.nrec(f(x),g,%z h.succ(h)))) \
\              in f(succ(succ(zero))) ---> ?a";
by (ceval_tac []);

val prems = goal thy
    "letrec f n be ncase(n,succ(zero),%x.nrec(n,zero,%y g.nrec(f(x),g,%z h.succ(h)))) \
\              in f(succ(succ(succ(zero)))) ---> ?a";
by (ceval_tac []);

(* Less Than Or Equal *)

fun isle x y = prove_goal thy 
    ("letrec f p be split(p,%m n.ncase(m,true,%x.ncase(n,false,%y.f(<x,y>)))) \
\              in f(<"^x^","^y^">) ---> ?a")
    (fn prems => [ceval_tac []]);

isle "succ(zero)" "succ(zero)";
isle "succ(zero)" "succ(succ(succ(succ(zero))))";
isle "succ(succ(succ(succ(succ(zero)))))" "succ(succ(succ(succ(zero))))";


(* Reverse *)

val prems = goal thy
    "letrec id l be lcase(l,[],%x xs.x$id(xs)) \
\              in id(zero$succ(zero)$[]) ---> ?a";
by (ceval_tac []);

val prems = goal thy
    "letrec rev l be lcase(l,[],%x xs.lrec(rev(xs),x$[],%y ys g.y$g)) \
\              in rev(zero$succ(zero)$(succ((lam x.x)`succ(zero)))$([])) ---> ?a";
by (ceval_tac []);

