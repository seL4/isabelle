(*  Title: 	CCL/wfd.ML
    ID:         $Id$

For wfd.thy.

Based on
    Titles: 	ZF/wf.ML and HOL/ex/lex-prod
    Authors: 	Lawrence C Paulson and Tobias Nipkow
    Copyright   1992  University of Cambridge

*)

open Wfd;

(***********)

val [major,prem] = goalw Wfd.thy [Wfd_def]
    "[| Wfd(R);       \
\       !!x.[| ALL y. <y,x>: R --> P(y) |] ==> P(x) |]  ==>  \
\    P(a)";
by (rtac (major RS spec RS mp RS spec RS CollectD) 1);
by (fast_tac (set_cs addSIs [prem RS CollectI]) 1);
val wfd_induct = result();

val [p1,p2,p3] = goal Wfd.thy
    "[| !!x y.<x,y> : R ==> Q(x); \
\       ALL x. (ALL y. <y,x> : R --> y : P) --> x : P; \
\       !!x.Q(x) ==> x:P |] ==> a:P";
br (p2 RS  spec  RS mp) 1;
by (fast_tac (set_cs addSIs [p1 RS p3]) 1);
val wfd_strengthen_lemma = result();

fun wfd_strengthen_tac s i = res_inst_tac [("Q",s)] wfd_strengthen_lemma i THEN
                             assume_tac (i+1);

val wfd::prems = goal Wfd.thy "[| Wfd(r);  <a,x>:r;  <x,a>:r |] ==> P";
by (subgoal_tac "ALL x. <a,x>:r --> <x,a>:r --> P" 1);
by (fast_tac (FOL_cs addIs prems) 1);
br (wfd RS  wfd_induct) 1;
by (ALLGOALS (fast_tac (ccl_cs addSIs prems)));
val wf_anti_sym = result();

val prems = goal Wfd.thy "[| Wfd(r);  <a,a>: r |] ==> P";
by (rtac wf_anti_sym 1);
by (REPEAT (resolve_tac prems 1));
val wf_anti_refl = result();

(*** Irreflexive transitive closure ***)

val [prem] = goal Wfd.thy "Wfd(R) ==> Wfd(R^+)";
by (rewtac Wfd_def);
by (REPEAT (ares_tac [allI,ballI,impI] 1));
(*must retain the universal formula for later use!*)
by (rtac allE 1 THEN assume_tac 1);
by (etac mp 1);
br (prem RS wfd_induct) 1;
by (rtac (impI RS allI) 1);
by (etac tranclE 1);
by (fast_tac ccl_cs 1);
be (spec RS mp RS spec RS mp) 1;
by (REPEAT (atac 1));
val trancl_wf = result();

(*** Lexicographic Ordering ***)

goalw Wfd.thy [lex_def] 
 "p : ra**rb <-> (EX a a' b b'.p = <<a,b>,<a',b'>> & (<a,a'> : ra | a=a' & <b,b'> : rb))";
by (fast_tac ccl_cs 1);
val lexXH = result();

val prems = goal Wfd.thy
 "<a,a'> : ra ==> <<a,b>,<a',b'>> : ra**rb";
by (fast_tac (ccl_cs addSIs (prems @ [lexXH RS iffD2])) 1);
val lexI1 = result();

val prems = goal Wfd.thy
 "<b,b'> : rb ==> <<a,b>,<a,b'>> : ra**rb";
by (fast_tac (ccl_cs addSIs (prems @ [lexXH RS iffD2])) 1);
val lexI2 = result();

val major::prems = goal Wfd.thy
 "[| p : ra**rb;  \
\    !!a a' b b'.[| <a,a'> : ra; p=<<a,b>,<a',b'>> |] ==> R;  \
\    !!a b b'.[| <b,b'> : rb;  p = <<a,b>,<a,b'>> |] ==> R  |] ==> \
\ R";
br (major RS (lexXH RS iffD1) RS exE) 1;
by (REPEAT_SOME (eresolve_tac ([exE,conjE,disjE]@prems)));
by (ALLGOALS (fast_tac ccl_cs));
val lexE = result();

val [major,minor] = goal Wfd.thy
 "[| p : r**s;  !!a a' b b'. p = <<a,b>,<a',b'>> ==> P |] ==>P";
br (major RS lexE) 1;
by (ALLGOALS (fast_tac (set_cs addSEs [minor])));
val lex_pair = result();

val [wfa,wfb] = goal Wfd.thy
 "[| Wfd(R); Wfd(S) |] ==> Wfd(R**S)";
bw Wfd_def;
by (safe_tac ccl_cs);
by (wfd_strengthen_tac "%x.EX a b.x=<a,b>" 1);
by (fast_tac (term_cs addSEs [lex_pair]) 1);
by (subgoal_tac "ALL a b.<a,b>:P" 1);
by (fast_tac ccl_cs 1);
br (wfa RS wfd_induct RS allI) 1;
br (wfb RS wfd_induct RS allI) 1;back();
by (fast_tac (type_cs addSEs [lexE]) 1);
val lex_wf = result();

(*** Mapping ***)

goalw Wfd.thy [wmap_def] 
 "p : wmap(f,r) <-> (EX x y. p=<x,y>  &  <f(x),f(y)> : r)";
by (fast_tac ccl_cs 1);
val wmapXH = result();

val prems = goal Wfd.thy
 "<f(a),f(b)> : r ==> <a,b> : wmap(f,r)";
by (fast_tac (ccl_cs addSIs (prems @ [wmapXH RS iffD2])) 1);
val wmapI = result();

val major::prems = goal Wfd.thy
 "[| p : wmap(f,r);  !!a b.[| <f(a),f(b)> : r;  p=<a,b> |] ==> R |] ==> R";
br (major RS (wmapXH RS iffD1) RS exE) 1;
by (REPEAT_SOME (eresolve_tac ([exE,conjE,disjE]@prems)));
by (ALLGOALS (fast_tac ccl_cs));
val wmapE = result();

val [wf] = goal Wfd.thy
 "Wfd(r) ==> Wfd(wmap(f,r))";
bw Wfd_def;
by (safe_tac ccl_cs);
by (subgoal_tac "ALL b.ALL a.f(a)=b-->a:P" 1);
by (fast_tac ccl_cs 1);
br (wf RS wfd_induct RS allI) 1;
by (safe_tac ccl_cs);
be (spec RS mp) 1;
by (safe_tac (ccl_cs addSEs [wmapE]));
be (spec RS mp RS spec RS mp) 1;
ba 1;
br refl 1;
val wmap_wf = result();

(* Projections *)

val prems = goal Wfd.thy "<xa,ya> : r ==> <<xa,xb>,<ya,yb>> : wmap(fst,r)";
br wmapI 1;
by (simp_tac (term_ss addsimps prems) 1);
val wfstI = result();

val prems = goal Wfd.thy "<xb,yb> : r ==> <<xa,xb>,<ya,yb>> : wmap(snd,r)";
br wmapI 1;
by (simp_tac (term_ss addsimps prems) 1);
val wsndI = result();

val prems = goal Wfd.thy "<xc,yc> : r ==> <<xa,<xb,xc>>,<ya,<yb,yc>>> : wmap(thd,r)";
br wmapI 1;
by (simp_tac (term_ss addsimps prems) 1);
val wthdI = result();

(*** Ground well-founded relations ***)

val prems = goalw Wfd.thy [wf_def] 
    "[| Wfd(r);  a : r |] ==> a : wf(r)";
by (fast_tac (set_cs addSIs prems) 1);
val wfI = result();

val prems = goalw Wfd.thy [Wfd_def] "Wfd({})";
by (fast_tac (set_cs addEs [EmptyXH RS iffD1 RS FalseE]) 1);
val Empty_wf = result();

val prems = goalw Wfd.thy [wf_def] "Wfd(wf(R))";
by (res_inst_tac [("Q","Wfd(R)")] (excluded_middle RS disjE) 1);
by (ALLGOALS (asm_simp_tac CCL_ss));
br Empty_wf 1;
val wf_wf = result();

goalw Wfd.thy [NatPR_def]  "p : NatPR <-> (EX x:Nat.p=<x,succ(x)>)";
by (fast_tac set_cs 1);
val NatPRXH = result();

goalw Wfd.thy [ListPR_def]  "p : ListPR(A) <-> (EX h:A.EX t:List(A).p=<t,h$t>)";
by (fast_tac set_cs 1);
val ListPRXH = result();

val NatPRI = refl RS (bexI RS (NatPRXH RS iffD2));
val ListPRI = refl RS (bexI RS (bexI RS (ListPRXH RS iffD2)));

goalw Wfd.thy [Wfd_def]  "Wfd(NatPR)";
by (safe_tac set_cs);
by (wfd_strengthen_tac "%x.x:Nat" 1);
by (fast_tac (type_cs addSEs [XH_to_E NatPRXH]) 1);
be Nat_ind 1;
by (ALLGOALS (fast_tac (type_cs addEs [XH_to_E NatPRXH])));
val NatPR_wf = result();

goalw Wfd.thy [Wfd_def]  "Wfd(ListPR(A))";
by (safe_tac set_cs);
by (wfd_strengthen_tac "%x.x:List(A)" 1);
by (fast_tac (type_cs addSEs [XH_to_E ListPRXH]) 1);
be List_ind 1;
by (ALLGOALS (fast_tac (type_cs addEs [XH_to_E ListPRXH])));
val ListPR_wf = result();

