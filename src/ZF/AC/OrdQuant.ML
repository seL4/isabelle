(*
  file OrdQuant.ML

  Proofs concerning special instances of quantifiers and union operator.
  Very useful when proving theorems about ordinals. 
*)

open OrdQuant;

(*** universal quantifier for ordinals ***)

qed_goalw "oallI" OrdQuant.thy [Oall_def]
    "[| !!x. x<A ==> P(x) |] ==> ALL x<A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [allI,impI]) 1)) ]);

qed_goalw "ospec" OrdQuant.thy [Oall_def]
    "[| ALL x<A. P(x);  x<A |] ==> P(x)"
 (fn major::prems=>
  [ (rtac (major RS spec RS mp) 1),
    (resolve_tac prems 1) ]);

qed_goalw "oallE" OrdQuant.thy [Oall_def]
    "[| ALL x<A. P(x);  P(x) ==> Q;  ~x<A ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS allE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl,impCE]) 1)) ]);

qed_goal "rev_oallE" OrdQuant.thy
    "[| ALL x<A. P(x);  ~x<A ==> Q;  P(x) ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS oallE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*Trival rewrite rule;   (ALL x<a.P)<->P holds only if a is not 0!*)
qed_goal "oall_simp" OrdQuant.thy "(ALL x<a. True) <-> True"
 (fn _=> [ (REPEAT (ares_tac [TrueI,oallI,iffI] 1)) ]);

(*Congruence rule for rewriting*)
qed_goalw "oall_cong" OrdQuant.thy [Oall_def]
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) |] ==> Oall(a,P) <-> Oall(a',P')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems) 1) ]);


(*** existential quantifier for ordinals ***)

qed_goalw "oexI" OrdQuant.thy [Oex_def]
    "[| P(x);  x<A |] ==> EX x<A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [exI,conjI]) 1)) ]);

(*Not of the general form for such rules; ~EX has become ALL~ *)
qed_goal "oexCI" OrdQuant.thy 
   "[| ALL x<A. ~P(x) ==> P(a);  a<A |] ==> EX x<A.P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[oexI,oallI,notI,notE]) 1)) ]);

qed_goalw "oexE" OrdQuant.thy [Oex_def]
    "[| EX x<A. P(x);  !!x. [| x<A; P(x) |] ==> Q \
\    |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS exE) 1),
    (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1)) ]);

qed_goalw "oex_cong" OrdQuant.thy [Oex_def]
    "[| a=a';  !!x. x<a' ==> P(x) <-> P'(x) \
\    |] ==> Oex(a,P) <-> Oex(a',P')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems addcongs [conj_cong]) 1) ]);


(*** Rules for Unions ***)

(*The order of the premises presupposes that a is rigid; A may be flexible*)
qed_goal "OUnionI" OrdQuant.thy "[| b<a;  A: B(b) |] ==> A: OUnion(a, %z. B(z))"
 (fn prems=>
  [ (resolve_tac [OUnion_iff RS iffD2] 1),
    (REPEAT (resolve_tac (prems @ [oexI]) 1)) ]);

qed_goal "OUnionE" OrdQuant.thy
    "[| A : OUnion(a, %z. B(z));  !!b.[| A: B(b);  b<a |] ==> R |] ==> R"
 (fn prems=>
  [ (resolve_tac [OUnion_iff RS iffD1 RS oexE] 1),
    (REPEAT (ares_tac prems 1)) ]);




(*** Rules for Unions of families ***)
(* UN x<a. B(x) abbreviates OUnion(a, %x. B(x)) *)

qed_goalw "OUN_iff" OrdQuant.thy [Oex_def]
    "b : (UN x<a. B(x)) <-> (EX x<a. b : B(x))"
 (fn _=> [ (fast_tac (FOL_cs addIs [OUnionI] 
                             addSEs [OUnionE]) 1) ]);

(*The order of the premises presupposes that a is rigid; b may be flexible*)
qed_goal "OUN_I" OrdQuant.thy "[| c<a;  b: B(c) |] ==> b: (UN x<a. B(x))"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems@[OUnionI]) 1)) ]);

qed_goal "OUN_E" OrdQuant.thy
    "[| b : (UN x<a. B(x));  !!x.[| x<a;  b: B(x) |] ==> R |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS OUnionE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl, RepFunE, subst]) 1)) ]);

val prems = goal thy "[| a=b;  !!x. x<b ==> f(x)=g(x) |] ==> OUnion(a,f) = OUnion(b,g)";
by (resolve_tac [OUnion_iff RS iff_sym RSN (2, OUnion_iff RS iff_trans RS iff_trans) RS equality_iffI] 1);
by (resolve_tac [oex_cong] 1);
by (resolve_tac prems 1);
by (dresolve_tac prems 1);
by (fast_tac (ZF_cs addSEs [equalityE]) 1);
qed "OUnion_cong";

val OrdQuant_cs = ZF_cs
  addSIs [oallI]
  addIs [oexI, OUnionI]
  addSEs [oexE, OUnionE]
  addEs [rev_oallE];

val OrdQuant_ss = ZF_ss addsimps [oall_simp, ltD RS beta]
                        addcongs [oall_cong, OUnion_cong];



