(*  Title:      ZF/AC/OrdQuant.thy
    ID:         $Id$
    Authors:    Krzysztof Grabczewski and L C Paulson

Quantifiers and union operator for ordinals. 
*)

(*** universal quantifier for ordinals ***)

val prems = Goalw [oall_def] 
    "[| !!x. x<A ==> P(x) |] ==> ALL x<A. P(x)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1)) ;
qed "oallI";

Goalw [oall_def] "[| ALL x<A. P(x);  x<A |] ==> P(x)";
by (etac (spec RS mp) 1);
by (assume_tac 1) ;
qed "ospec";

val major::prems = Goalw [oall_def] 
    "[| ALL x<A. P(x);  P(x) ==> Q;  ~x<A ==> Q |] ==> Q";
by (rtac (major RS allE) 1);
by (REPEAT (eresolve_tac (prems@[asm_rl,impCE]) 1)) ;
qed "oallE";

val major::prems = Goal
    "[| ALL x<A. P(x);  ~x<A ==> Q;  P(x) ==> Q |] ==> Q";
by (rtac (major RS oallE) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "rev_oallE";

(*Trival rewrite rule;   (ALL x<a.P)<->P holds only if a is not 0!*)
Goal "(ALL x<a. True) <-> True";
by (REPEAT (ares_tac [TrueI,oallI,iffI] 1)) ;
qed "oall_simp";

(*Congruence rule for rewriting*)
val prems = Goalw [oall_def] 
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |] ==> oall(a,P) <-> oall(a',P')";
by (simp_tac (simpset() addsimps prems) 1) ;
qed "oall_cong";


(*** existential quantifier for ordinals ***)

val prems = Goalw [oex_def] 
    "[| P(x);  x<A |] ==> EX x<A. P(x)";
by (REPEAT (ares_tac (prems @ [exI,conjI]) 1)) ;
qed "oexI";

(*Not of the general form for such rules; ~EX has become ALL~ *)
val prems = Goal
   "[| ALL x<A. ~P(x) ==> P(a);  a<A |] ==> EX x<A. P(x)";
by (rtac classical 1);
by (REPEAT (ares_tac (prems@[oexI,oallI,notI,notE]) 1)) ;
qed "oexCI";

val major::prems = Goalw [oex_def] 
    "[| EX x<A. P(x);  !!x. [| x<A; P(x) |] ==> Q \
\    |] ==> Q";
by (rtac (major RS exE) 1);
by (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1)) ;
qed "oexE";

val prems = Goalw [oex_def] 
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) \
\    |] ==> oex(a,P) <-> oex(a',P')";
by (simp_tac (simpset() addsimps prems addcongs [conj_cong]) 1) ;
qed "oex_cong";


(*** Rules for Ordinal-Indexed Unions ***)

Goalw [OUnion_def] "[| a<i;  b: B(a) |] ==> b: (UN z<i. B(z))";
by (blast_tac (claset() addSEs [ltE]) 1);
qed "OUN_I";

val major::prems = Goalw [OUnion_def] 
    "[| b : (UN z<i. B(z));  !!a.[| b: B(a);  a<i |] ==> R |] ==> R";
by (rtac (major RS CollectE) 1);
by (rtac UN_E 1);
by (REPEAT (ares_tac (ltI::prems) 1)) ;
qed "OUN_E";

Goalw [oex_def] "b : (UN x<i. B(x)) <-> (EX x<i. b : B(x))";
by (fast_tac (claset() addIs [OUN_I] addSEs [OUN_E]) 1) ;
qed "OUN_iff";

val prems = Goal
    "[| i=j;  !!x. x<j ==> C(x)=D(x) |] ==> (UN x<i. C(x)) = (UN x<j. D(x))";
by (rtac equality_iffI 1);
by (simp_tac (simpset() addcongs [oex_cong] addsimps OUN_iff::prems) 1) ;
qed "OUN_cong";

AddSIs [oallI];
AddIs  [oexI, OUN_I];
AddSEs [oexE, OUN_E];
AddEs  [rev_oallE];

val Ord_atomize = atomize (("OrdQuant.oall", [ospec])::ZF_conn_pairs, 
                           ZF_mem_pairs);

simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o gen_all)
                        addsimps [oall_simp, ltD RS beta]
                        addcongs [oall_cong, oex_cong, OUN_cong];

val major::prems = Goalw [lt_def, oall_def]
    "[| i<k;  !!x.[| x<k;  ALL y<x. P(y) |] ==> P(x) \
\    |]  ==>  P(i)";
by (rtac (major RS conjE) 1);
by (etac Ord_induct 1 THEN assume_tac 1);
by (fast_tac (claset() addIs prems) 1);
qed "lt_induct";

