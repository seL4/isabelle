(*  Title: 	HOL/ex/rel
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Domain, range of a relation or function -- NOT YET WORKING
*)

structure Rel =
struct
val thy = extend_theory Univ.thy "Rel"
([], [], [], [],
 [ 
  (["domain"],	"('a * 'b)set => 'a set"),
  (["range2"],	"('a * 'b)set => 'b set"),
  (["field"],	"('a * 'a)set => 'a set")
 ],
 None)
 [
  ("domain_def",     "domain(r) == {a. ? b. <a,b> : r}" ),
  ("range2_def",     "range2(r) == {b. ? a. <a,b> : r}" ),
  ("field_def",      "field(r)  == domain(r) Un range2(r)" )
 ];
end;

local val ax = get_axiom Rel.thy
in
val domain_def = ax"domain_def";
val range2_def = ax"range2_def";
val field_def = ax"field_def";
end;


(*** domain ***)

val [prem] = goalw Rel.thy [domain_def,Pair_def] "<a,b>: r ==> a : domain(r)";
by (fast_tac (set_cs addIs [prem]) 1);
qed "domainI";

val major::prems = goalw Rel.thy [domain_def]
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P";
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
qed "domainE";


(*** range2 ***)

val [prem] = goalw Rel.thy [range2_def,Pair_def] "<a,b>: r ==> b : range2(r)";
by (fast_tac (set_cs addIs [prem]) 1);
qed "range2I";

val major::prems = goalw Rel.thy [range2_def]
    "[| b : range2(r);  !!x. <x,b>: r ==> P |] ==> P";
by (rtac (major RS CollectE) 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
qed "range2E";


(*** field ***)

val [prem] = goalw Rel.thy [field_def] "<a,b>: r ==> a : field(r)";
by (rtac (prem RS domainI RS UnI1) 1);
qed "fieldI1";

val [prem] = goalw Rel.thy [field_def] "<a,b>: r ==> b : field(r)";
by (rtac (prem RS range2I RS UnI2) 1);
qed "fieldI2";

val [prem] = goalw Rel.thy [field_def]
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)";
by (rtac (prem RS domainI RS UnCI) 1);
by (swap_res_tac [range2I] 1);
by (etac notnotD 1);
qed "fieldCI";

val major::prems = goalw Rel.thy [field_def]
     "[| a : field(r);  \
\        !!x. <a,x>: r ==> P;  \
\        !!x. <x,a>: r ==> P        |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (eresolve_tac (prems@[domainE,range2E]) 1));
qed "fieldE";

goalw Rel.thy [field_def] "domain(r) <= field(r)";
by (rtac Un_upper1 1);
qed "domain_in_field";

goalw Rel.thy [field_def] "range2(r) <= field(r)";
by (rtac Un_upper2 1);
qed "range2_in_field";


????????????????????????????????????????????????????????????????;

(*If r allows well-founded induction then wf(r)*)
val [prem1,prem2] = goalw Rel.thy [wf_def] 
    "[| field(r)<=A;  \
\       !!P u. ! x:A. (! y. <y,x>: r --> P(y)) --> P(x) ==> P(u) |]  \
\    ==>  wf(r)";
by (rtac (prem1 RS wfI) 1);
by (res_inst_tac [ ("B", "A-Z") ] (prem2 RS subsetCE) 1);
by (fast_tac ZF_cs 3);
by (fast_tac ZF_cs 2);
by (fast_tac ZF_cs 1);
qed "wfI2";

