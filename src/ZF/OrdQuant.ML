(*  Title:      ZF/AC/OrdQuant.thy
    ID:         $Id$
    Authors:    Krzysztof Grabczewski and L C Paulson

Quantifiers and union operator for ordinals. 
*)

open OrdQuant;

(*** universal quantifier for ordinals ***)

qed_goalw "oallI" thy [oall_def]
    "[| !!x. x<A ==> P(x) |] ==> ALL x<A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [allI,impI]) 1)) ]);

qed_goalw "ospec" thy [oall_def]
    "[| ALL x<A. P(x);  x<A |] ==> P(x)"
 (fn major::prems=>
  [ (rtac (major RS spec RS mp) 1),
    (resolve_tac prems 1) ]);

qed_goalw "oallE" thy [oall_def]
    "[| ALL x<A. P(x);  P(x) ==> Q;  ~x<A ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS allE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl,impCE]) 1)) ]);

qed_goal "rev_oallE" thy
    "[| ALL x<A. P(x);  ~x<A ==> Q;  P(x) ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS oallE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*Trival rewrite rule;   (ALL x<a.P)<->P holds only if a is not 0!*)
qed_goal "oall_simp" thy "(ALL x<a. True) <-> True"
 (fn _=> [ (REPEAT (ares_tac [TrueI,oallI,iffI] 1)) ]);

(*Congruence rule for rewriting*)
qed_goalw "oall_cong" thy [oall_def]
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |] ==> oall(a,P) <-> oall(a',P')"
 (fn prems=> [ (simp_tac (!simpset addsimps prems) 1) ]);


(*** existential quantifier for ordinals ***)

qed_goalw "oexI" thy [oex_def]
    "[| P(x);  x<A |] ==> EX x<A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [exI,conjI]) 1)) ]);

(*Not of the general form for such rules; ~EX has become ALL~ *)
qed_goal "oexCI" thy 
   "[| ALL x<A. ~P(x) ==> P(a);  a<A |] ==> EX x<A. P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[oexI,oallI,notI,notE]) 1)) ]);

qed_goalw "oexE" thy [oex_def]
    "[| EX x<A. P(x);  !!x. [| x<A; P(x) |] ==> Q \
\    |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS exE) 1),
    (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1)) ]);

qed_goalw "oex_cong" thy [oex_def]
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) \
\    |] ==> oex(a,P) <-> oex(a',P')"
 (fn prems=> [ (simp_tac (!simpset addsimps prems addcongs [conj_cong]) 1) ]);


(*** Rules for Ordinal-Indexed Unions ***)

qed_goalw "OUN_I" thy [OUnion_def]
        "!!i. [| a<i;  b: B(a) |] ==> b: (UN z<i. B(z))"
 (fn _=> [ fast_tac (!claset addSEs [ltE]) 1 ]);

qed_goalw "OUN_E" thy [OUnion_def]
    "[| b : (UN z<i. B(z));  !!a.[| b: B(a);  a<i |] ==> R |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS CollectE) 1),
    (rtac UN_E 1),
    (REPEAT (ares_tac (ltI::prems) 1)) ]);

qed_goalw "OUN_iff" thy [oex_def]
    "b : (UN x<i. B(x)) <-> (EX x<i. b : B(x))"
 (fn _=> [ (fast_tac (!claset addIs [OUN_I] addSEs [OUN_E]) 1) ]);

qed_goal "OUN_cong" thy
    "[| i=j;  !!x. x<j ==> C(x)=D(x) |] ==> (UN x<i. C(x)) = (UN x<j. D(x))"
 (fn prems=>
      [ rtac equality_iffI 1,
        simp_tac (!simpset addcongs [oex_cong] addsimps (OUN_iff::prems)) 1 ]);

AddSIs [oallI];
AddIs  [oexI, OUN_I];
AddSEs [oexE, OUN_E];
AddEs  [rev_oallE];

val Ord_atomize = atomize (("oall", [ospec])::ZF_conn_pairs, 
                           ZF_mem_pairs);

simpset := !simpset setmksimps (map mk_meta_eq o Ord_atomize o gen_all)
                        addsimps [oall_simp, ltD RS beta]
                        addcongs [oall_cong, oex_cong, OUN_cong];

val major::prems = goalw thy [lt_def, oall_def]
    "[| i<k;  !!x.[| x<k;  ALL y<x. P(y) |] ==> P(x) \
\    |]  ==>  P(i)";
by (rtac (major RS conjE) 1);
by (etac Ord_induct 1 THEN assume_tac 1);
by (fast_tac (!claset addIs prems) 1);
qed "lt_induct";

