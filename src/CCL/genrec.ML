(*  Title: 	92/CCL/genrec
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

(*** General Recursive Functions ***)

val major::prems = goal Wfd.thy 
    "[| a : A;  \
\       !!p g.[| p:A; ALL x:{x: A. <x,p>:wf(R)}. g(x) : D(x) |] ==>\
\               h(p,g) : D(p) |] ==> \
\    letrec g x be h(x,g) in g(a) : D(a)";
by (rtac (major RS rev_mp) 1);
by (rtac (wf_wf RS wfd_induct) 1);
by (rtac (letrecB RS ssubst) 1);
by (rtac impI 1);
by (eresolve_tac prems 1);
by (rtac ballI 1);
by (etac (spec RS mp RS mp) 1);
by (REPEAT (eresolve_tac [SubtypeD1,SubtypeD2] 1));
val letrecT = result();

goalw Wfd.thy [SPLIT_def] "SPLIT(<a,b>,B) = B(a,b)";
by (rtac set_ext 1);
by (fast_tac ccl_cs 1);
val SPLITB = result();

val prems = goalw Wfd.thy [letrec2_def]
    "[| a : A;  b : B;  \
\     !!p q g.[| p:A; q:B; \
\             ALL x:A.ALL y:{y: B. <<x,y>,<p,q>>:wf(R)}. g(x,y) : D(x,y) |] ==>\
\               h(p,q,g) : D(p,q) |] ==> \
\    letrec g x y be h(x,y,g) in g(a,b) : D(a,b)";
by (rtac (SPLITB RS subst) 1);
by (REPEAT (ares_tac ([letrecT,pairT,splitT]@prems) 1));
by (rtac (SPLITB RS ssubst) 1);
by (REPEAT (ares_tac ([ballI,SubtypeI]@prems) 1));
by (rtac (SPLITB RS subst) 1);
by (REPEAT (ares_tac ([letrecT,SubtypeI,pairT,splitT]@prems) 1 ORELSE 
            eresolve_tac [bspec,SubtypeE,sym RS subst] 1));
val letrec2T = result();

goal Wfd.thy "SPLIT(<a,<b,c>>,%x xs.SPLIT(xs,%y z.B(x,y,z))) = B(a,b,c)";
by (simp_tac (ccl_ss addsimps [SPLITB]) 1);
val lemma = result();

val prems = goalw Wfd.thy [letrec3_def]
    "[| a : A;  b : B;  c : C;  \
\    !!p q r g.[| p:A; q:B; r:C; \
\      ALL x:A.ALL y:B.ALL z:{z:C. <<x,<y,z>>,<p,<q,r>>> : wf(R)}. \
\                                                       g(x,y,z) : D(x,y,z) |] ==>\
\               h(p,q,r,g) : D(p,q,r) |] ==> \
\    letrec g x y z be h(x,y,z,g) in g(a,b,c) : D(a,b,c)";
by (rtac (lemma RS subst) 1);
by (REPEAT (ares_tac ([letrecT,pairT,splitT]@prems) 1));
by (simp_tac (ccl_ss addsimps [SPLITB]) 1);
by (REPEAT (ares_tac ([ballI,SubtypeI]@prems) 1));
by (rtac (lemma RS subst) 1);
by (REPEAT (ares_tac ([letrecT,SubtypeI,pairT,splitT]@prems) 1 ORELSE 
            eresolve_tac [bspec,SubtypeE,sym RS subst] 1));
val letrec3T = result();

val letrecTs = [letrecT,letrec2T,letrec3T];


(*** Type Checking for Recursive Calls ***)

val major::prems = goal Wfd.thy
    "[| ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x); \
\       g(a) : D(a) ==> g(a) : E;  a:A;  <a,p>:wf(R) |] ==> \
\   g(a) : E";
by (REPEAT (ares_tac ([SubtypeI,major RS bspec,major]@prems) 1));
val rcallT = result();

val major::prems = goal Wfd.thy
    "[| ALL x:A.ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y); \
\       g(a,b) : D(a,b) ==> g(a,b) : E;  a:A;  b:B;  <<a,b>,<p,q>>:wf(R) |] ==> \
\   g(a,b) : E";
by (REPEAT (ares_tac ([SubtypeI,major RS bspec RS bspec,major]@prems) 1));
val rcall2T = result();

val major::prems = goal Wfd.thy
    "[| ALL x:A.ALL y:B.ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}. g(x,y,z):D(x,y,z); \
\       g(a,b,c) : D(a,b,c) ==> g(a,b,c) : E;  \
\       a:A;  b:B;  c:C;  <<a,<b,c>>,<p,<q,r>>> : wf(R) |] ==> \
\   g(a,b,c) : E";
by (REPEAT (ares_tac ([SubtypeI,major RS bspec RS bspec RS bspec,major]@prems) 1));
val rcall3T = result();

val rcallTs = [rcallT,rcall2T,rcall3T];

(*** Instantiating an induction hypothesis with an equality assumption ***)

val prems = goal Wfd.thy
    "[| g(a) = b; ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x);  \
\       [| ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x);  b=g(a);  g(a) : D(a) |] ==> P; \
\       ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) ==> a:A;  \
\       ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) ==> <a,p>:wf(R) |] ==> \
\   P";
by (resolve_tac (prems RL prems) 1);
by (resolve_tac (prems RL [sym]) 1);
by (rtac rcallT 1);
by (REPEAT (ares_tac prems 1));
val hyprcallT = result();

val prems = goal Wfd.thy
    "[| g(a) = b; ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x);\
\       [| b=g(a);  g(a) : D(a) |] ==> P; a:A;  <a,p>:wf(R) |] ==> \
\   P";
by (resolve_tac (prems) 1);
by (resolve_tac (prems RL [sym]) 1);
by (rtac rcallT 1);
by (REPEAT (ares_tac prems 1));
val hyprcallT = result();

val prems = goal Wfd.thy
    "[| g(a,b) = c; ALL x:A.ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y); \
\       [| c=g(a,b);  g(a,b) : D(a,b) |] ==> P; \
\       a:A;  b:B;  <<a,b>,<p,q>>:wf(R) |] ==> \
\   P";
by (resolve_tac (prems) 1);
by (resolve_tac (prems RL [sym]) 1);
by (rtac rcall2T 1);
by (REPEAT (ares_tac prems 1));
val hyprcall2T = result();

val prems = goal Wfd.thy
  "[| g(a,b,c) = d; \
\     ALL x:A.ALL y:B.ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}.g(x,y,z):D(x,y,z); \
\   [| d=g(a,b,c);  g(a,b,c) : D(a,b,c) |] ==> P; \
\   a:A;  b:B;  c:C;  <<a,<b,c>>,<p,<q,r>>> : wf(R) |] ==> \
\   P";
by (resolve_tac (prems) 1);
by (resolve_tac (prems RL [sym]) 1);
by (rtac rcall3T 1);
by (REPEAT (ares_tac prems 1));
val hyprcall3T = result();

val hyprcallTs = [hyprcallT,hyprcall2T,hyprcall3T];

(*** Rules to Remove Induction Hypotheses after Type Checking ***)

val prems = goal Wfd.thy
    "[| ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x); P |] ==> \
\    P";
by (REPEAT (ares_tac prems 1));
val rmIH1  = result();

val prems = goal Wfd.thy
    "[| ALL x:A.ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y); P |] ==> \
\    P";
by (REPEAT (ares_tac prems 1));
val rmIH2  = result();

val prems = goal Wfd.thy
 "[| ALL x:A.ALL y:B.ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}.g(x,y,z):D(x,y,z); \
\    P |] ==> \
\    P";
by (REPEAT (ares_tac prems 1));
val rmIH3  = result();

val rmIHs = [rmIH1,rmIH2,rmIH3];

