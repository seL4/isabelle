(*  Title: 	ZF/ex/fin.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Finite powerset operator

could define cardinality?

prove X:Fin(A) ==> EX n:nat. EX f. f:bij(X,n)
	card(0)=0
	[| ~ a:b; b: Fin(A) |] ==> card(cons(a,b)) = succ(card(b))

b: Fin(A) ==> inj(b,b)<=surj(b,b)

Limit(i) ==> Fin(Vfrom(A,i)) <= Un j:i. Fin(Vfrom(A,j))
Fin(univ(A)) <= univ(A)
*)

structure Fin = Inductive_Fun
 (val thy = Arith.thy addconsts [(["Fin"],"i=>i")];
  val rec_doms = [("Fin","Pow(A)")];
  val sintrs = 
	  ["0 : Fin(A)",
	   "[| a: A;  b: Fin(A) |] ==> cons(a,b) : Fin(A)"];
  val monos = [];
  val con_defs = [];
  val type_intrs = [Pow_bottom, cons_subsetI, PowI]
  val type_elims = [make_elim PowD]);

val [Fin_0I, Fin_consI] = Fin.intrs;


goalw Fin.thy Fin.defs "!!A B. A<=B ==> Fin(A) <= Fin(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Fin.bnd_mono 1));
by (REPEAT (ares_tac (Pow_mono::basic_monos) 1));
val Fin_mono = result();

(* A : Fin(B) ==> A <= B *)
val FinD = Fin.dom_subset RS subsetD RS PowD;

(** Induction on finite sets **)

(*Discharging ~ x:y entails extra work*)
val major::prems = goal Fin.thy 
    "[| b: Fin(A);  \
\       P(0);        \
\       !!x y. [| x: A;  y: Fin(A);  ~ x:y;  P(y) |] ==> P(cons(x,y)) \
\    |] ==> P(b)";
by (rtac (major RS Fin.induct) 1);
by (res_inst_tac [("Q","a:b")] (excluded_middle RS disjE) 2);
by (etac (cons_absorb RS ssubst) 3 THEN assume_tac 3);	    (*backtracking!*)
by (REPEAT (ares_tac prems 1));
val Fin_induct = result();

(** Simplification for Fin **)
val Fin_ss = arith_ss addcongs mk_congs Fin.thy ["Fin"] addrews Fin.intrs;

(*The union of two finite sets is fin*)
val major::prems = goal Fin.thy
    "[| b: Fin(A);  c: Fin(A) |] ==> b Un c : Fin(A)";
by (rtac (major RS Fin_induct) 1);
by (ALLGOALS (ASM_SIMP_TAC (Fin_ss addrews (prems@[Un_0, Un_cons]))));
val Fin_UnI = result();

(*The union of a set of finite sets is fin*)
val [major] = goal Fin.thy "C : Fin(Fin(A)) ==> Union(C) : Fin(A)";
by (rtac (major RS Fin_induct) 1);
by (ALLGOALS (ASM_SIMP_TAC (Fin_ss addrews [Union_0, Union_cons, Fin_UnI])));
val Fin_UnionI = result();

(*Every subset of a finite set is fin*)
val [subs,fin] = goal Fin.thy "[| c<=b;  b: Fin(A) |] ==> c: Fin(A)";
by (EVERY1 [subgoal_tac "(ALL z. z<=b --> z: Fin(A))",
	    etac (spec RS mp),
	    rtac subs]);
by (rtac (fin RS Fin_induct) 1);
by (SIMP_TAC (Fin_ss addrews [subset_empty_iff]) 1);
by (safe_tac (ZF_cs addSDs [subset_cons_iff RS iffD1]));
by (eres_inst_tac [("b","z")] (cons_Diff RS subst) 2);
by (ALLGOALS (ASM_SIMP_TAC Fin_ss));
val Fin_subset = result();

val major::prems = goal Fin.thy 
    "[| c: Fin(A);  b: Fin(A);  				\
\       P(b);       						\
\       !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> c<=b --> P(b-c)";
by (rtac (major RS Fin_induct) 1);
by (rtac (Diff_cons RS ssubst) 2);
by (ALLGOALS (ASM_SIMP_TAC (Fin_ss addrews (prems@[Diff_0, cons_subset_iff, 
				Diff_subset RS Fin_subset]))));
val Fin_0_induct_lemma = result();

val prems = goal Fin.thy 
    "[| b: Fin(A);  						\
\       P(b);        						\
\       !!x y. [| x: A;  y: Fin(A);  x:y;  P(y) |] ==> P(y-{x}) \
\    |] ==> P(0)";
by (rtac (Diff_cancel RS subst) 1);
by (rtac (Fin_0_induct_lemma RS mp) 1);
by (REPEAT (ares_tac (subset_refl::prems) 1));
val Fin_0_induct = result();
