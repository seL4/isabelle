(*  Title: 	HOL/prod
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For prod.thy.  Ordered Pairs, the Cartesian product type, the unit type
*)

open Prod;

(*This counts as a non-emptiness result for admitting 'a * 'b as a type*)
goalw Prod.thy [Prod_def] "Pair_Rep a b : Prod";
by (EVERY1 [rtac CollectI, rtac exI, rtac exI, rtac refl]);
qed "ProdI";

val [major] = goalw Prod.thy [Pair_Rep_def]
    "Pair_Rep a b = Pair_Rep a' b' ==> a=a' & b=b'";
by (EVERY1 [rtac (major RS fun_cong RS fun_cong RS subst), 
	    rtac conjI, rtac refl, rtac refl]);
qed "Pair_Rep_inject";

goal Prod.thy "inj_onto Abs_Prod Prod";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Prod_inverse 1);
qed "inj_onto_Abs_Prod";

val prems = goalw Prod.thy [Pair_def]
    "[| <a, b> = <a',b'>;  [| a=a';  b=b' |] ==> R |] ==> R";
by (rtac (inj_onto_Abs_Prod RS inj_ontoD RS Pair_Rep_inject RS conjE) 1);
by (REPEAT (ares_tac (prems@[ProdI]) 1));
qed "Pair_inject";

goal Prod.thy "(<a,b> = <a',b'>) = (a=a' & b=b')";
by (fast_tac (set_cs addIs [Pair_inject]) 1);
qed "Pair_eq";

goalw Prod.thy [fst_def] "fst(<a,b>) = a";
by (fast_tac (set_cs addIs [select_equality] addSEs [Pair_inject]) 1);
qed "fst_conv";

goalw Prod.thy [snd_def] "snd(<a,b>) = b";
by (fast_tac (set_cs addIs [select_equality] addSEs [Pair_inject]) 1);
qed "snd_conv";

goalw Prod.thy [Pair_def] "? x y. p = <x,y>";
by (rtac (rewrite_rule [Prod_def] Rep_Prod RS CollectE) 1);
by (EVERY1[etac exE, etac exE, rtac exI, rtac exI,
	   rtac (Rep_Prod_inverse RS sym RS trans),  etac arg_cong]);
qed "PairE_lemma";

val [prem] = goal Prod.thy "[| !!x y. p = <x,y> ==> Q |] ==> Q";
by (rtac (PairE_lemma RS exE) 1);
by (REPEAT (eresolve_tac [prem,exE] 1));
qed "PairE";

goalw Prod.thy [split_def] "split c <a,b> = c a b";
by (sstac [fst_conv, snd_conv] 1);
by (rtac refl 1);
qed "split";

val prod_ss = set_ss addsimps [fst_conv, snd_conv, split, Pair_eq];

goal Prod.thy "(s=t) = (fst(s)=fst(t) & snd(s)=snd(t))";
by (res_inst_tac[("p","s")] PairE 1);
by (res_inst_tac[("p","t")] PairE 1);
by (asm_simp_tac prod_ss 1);
qed "Pair_fst_snd_eq";

(*Prevents simplification of c: much faster*)
qed_goal "split_weak_cong" Prod.thy
  "p=q ==> split c p = split c q"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

(* Do not add as rewrite rule: invalidates some proofs in IMP *)
goal Prod.thy "p = <fst(p),snd(p)>";
by (res_inst_tac [("p","p")] PairE 1);
by (asm_simp_tac prod_ss 1);
qed "surjective_pairing";

goal Prod.thy "p = split (%x y.<x,y>) p";
by (res_inst_tac [("p","p")] PairE 1);
by (asm_simp_tac prod_ss 1);
qed "surjective_pairing2";

(*For use with split_tac and the simplifier*)
goal Prod.thy "R(split c p) = (! x y. p = <x,y> --> R(c x y))";
by (stac surjective_pairing 1);
by (stac split 1);
by (fast_tac (HOL_cs addSEs [Pair_inject]) 1);
qed "expand_split";

(** split used as a logical connective or set former **)

(*These rules are for use with fast_tac.
  Could instead call simp_tac/asm_full_simp_tac using split as rewrite.*)

goal Prod.thy "!!a b c. c a b ==> split c <a,b>";
by (asm_simp_tac prod_ss 1);
qed "splitI";

val prems = goalw Prod.thy [split_def]
    "[| split c p;  !!x y. [| p = <x,y>;  c x y |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "splitE";

goal Prod.thy "!!R a b. split R <a,b> ==> R a b";
by (etac (split RS iffD1) 1);
qed "splitD";

goal Prod.thy "!!a b c. z: c a b ==> z: split c <a,b>";
by (asm_simp_tac prod_ss 1);
qed "mem_splitI";

val prems = goalw Prod.thy [split_def]
    "[| z: split c p;  !!x y. [| p = <x,y>;  z: c x y |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "mem_splitE";

(*** prod_fun -- action of the product functor upon functions ***)

goalw Prod.thy [prod_fun_def] "prod_fun f g <a,b> = <f(a),g(b)>";
by (rtac split 1);
qed "prod_fun";

goal Prod.thy 
    "prod_fun (f1 o f2) (g1 o g2) = ((prod_fun f1 g1) o (prod_fun f2 g2))";
by (rtac ext 1);
by (res_inst_tac [("p","x")] PairE 1);
by (asm_simp_tac (prod_ss addsimps [prod_fun,o_def]) 1);
qed "prod_fun_compose";

goal Prod.thy "prod_fun (%x.x) (%y.y) = (%z.z)";
by (rtac ext 1);
by (res_inst_tac [("p","z")] PairE 1);
by (asm_simp_tac (prod_ss addsimps [prod_fun]) 1);
qed "prod_fun_ident";

val prems = goal Prod.thy "<a,b>:r ==> <f(a),g(b)> : (prod_fun f g)``r";
by (rtac image_eqI 1);
by (rtac (prod_fun RS sym) 1);
by (resolve_tac prems 1);
qed "prod_fun_imageI";

val major::prems = goal Prod.thy
    "[| c: (prod_fun f g)``r;  !!x y. [| c=<f(x),g(y)>;  <x,y>:r |] ==> P  \
\    |] ==> P";
by (rtac (major RS imageE) 1);
by (res_inst_tac [("p","x")] PairE 1);
by (resolve_tac prems 1);
by (fast_tac HOL_cs 2);
by (fast_tac (HOL_cs addIs [prod_fun]) 1);
qed "prod_fun_imageE";

(*** Disjoint union of a family of sets - Sigma ***)

qed_goalw "SigmaI" Prod.thy [Sigma_def]
    "[| a:A;  b:B(a) |] ==> <a,b> : Sigma A B"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[singletonI,UN_I]) 1)) ]);

(*The general elimination rule*)
qed_goalw "SigmaE" Prod.thy [Sigma_def]
    "[| c: Sigma A B;  \
\       !!x y.[| x:A;  y:B(x);  c=<x,y> |] ==> P \
\    |] ==> P"
 (fn major::prems=>
  [ (cut_facts_tac [major] 1),
    (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ]);

(** Elimination of <a,b>:A*B -- introduces no eigenvariables **)
qed_goal "SigmaD1" Prod.thy "<a,b> : Sigma A B ==> a : A"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

qed_goal "SigmaD2" Prod.thy "<a,b> : Sigma A B ==> b : B(a)"
 (fn [major]=>
  [ (rtac (major RS SigmaE) 1),
    (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ]);

qed_goal "SigmaE2" Prod.thy
    "[| <a,b> : Sigma A B;    \
\       [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P"
 (fn [major,minor]=>
  [ (rtac minor 1),
    (rtac (major RS SigmaD1) 1),
    (rtac (major RS SigmaD2) 1) ]);

(*** Domain of a relation ***)

val prems = goalw Prod.thy [image_def] "<a,b> : r ==> a : fst``r";
by (rtac CollectI 1);
by (rtac bexI 1);
by (rtac (fst_conv RS sym) 1);
by (resolve_tac prems 1);
qed "fst_imageI";

val major::prems = goal Prod.thy
    "[| a : fst``r;  !!y.[| <a,y> : r |] ==> P |] ==> P"; 
by (rtac (major RS imageE) 1);
by (resolve_tac prems 1);
by (etac ssubst 1);
by (rtac (surjective_pairing RS subst) 1);
by (assume_tac 1);
qed "fst_imageE";

(*** Range of a relation ***)

val prems = goalw Prod.thy [image_def] "<a,b> : r ==> b : snd``r";
by (rtac CollectI 1);
by (rtac bexI 1);
by (rtac (snd_conv RS sym) 1);
by (resolve_tac prems 1);
qed "snd_imageI";

val major::prems = goal Prod.thy
    "[| a : snd``r;  !!y.[| <y,a> : r |] ==> P |] ==> P"; 
by (rtac (major RS imageE) 1);
by (resolve_tac prems 1);
by (etac ssubst 1);
by (rtac (surjective_pairing RS subst) 1);
by (assume_tac 1);
qed "snd_imageE";

(** Exhaustion rule for unit -- a degenerate form of induction **)

goalw Prod.thy [Unity_def]
    "u = Unity";
by (stac (rewrite_rule [Unit_def] Rep_Unit RS CollectD RS sym) 1);
by (rtac (Rep_Unit_inverse RS sym) 1);
qed "unit_eq";

val prod_cs = set_cs addSIs [SigmaI, mem_splitI] 
                     addIs  [fst_imageI, snd_imageI, prod_fun_imageI]
                     addSEs [SigmaE2, SigmaE, mem_splitE, 
			     fst_imageE, snd_imageE, prod_fun_imageE,
			     Pair_inject];
