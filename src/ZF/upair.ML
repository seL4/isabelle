(*  Title: 	ZF/upair
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

UNORDERED pairs in Zermelo-Fraenkel Set Theory 

Observe the order of dependence:
    Upair is defined in terms of Replace
    Un is defined in terms of Upair and Union (similarly for Int)
    cons is defined in terms of Upair and Un
    Ordered pairs and descriptions are defined using cons ("set notation")
*)

(*** Lemmas about power sets  ***)

val Pow_bottom = empty_subsetI RS PowI;		(* 0 : Pow(B) *)
val Pow_top = subset_refl RS PowI;		(* A : Pow(A) *)
val Pow_neq_0 = Pow_top RSN (2,equals0D);	(* Pow(a)=0 ==> P *) 


(*** Unordered pairs - Upair ***)

val pairing = prove_goalw ZF.thy [Upair_def]
    "c : Upair(a,b) <-> (c=a | c=b)"
 (fn _ => [ (fast_tac (lemmas_cs addEs [Pow_neq_0, sym RS Pow_neq_0]) 1) ]);

val UpairI1 = prove_goal ZF.thy "a : Upair(a,b)"
 (fn _ => [ (rtac (refl RS disjI1 RS (pairing RS iffD2)) 1) ]);

val UpairI2 = prove_goal ZF.thy "b : Upair(a,b)"
 (fn _ => [ (rtac (refl RS disjI2 RS (pairing RS iffD2)) 1) ]);

val UpairE = prove_goal ZF.thy
    "[| a : Upair(b,c);  a=b ==> P;  a=c ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS (pairing RS iffD1 RS disjE)) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*** Rules for binary union -- Un -- defined via Upair ***)

val UnI1 = prove_goalw ZF.thy [Un_def] "c : A ==> c : A Un B"
 (fn [prem]=> [ (rtac (prem RS (UpairI1 RS UnionI)) 1) ]);

val UnI2 = prove_goalw ZF.thy [Un_def] "c : B ==> c : A Un B"
 (fn [prem]=> [ (rtac (prem RS (UpairI2 RS UnionI)) 1) ]);

val UnE = prove_goalw ZF.thy [Un_def] 
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnionE) 1),
    (etac UpairE 1),
    (REPEAT (EVERY1 [resolve_tac prems, etac subst, assume_tac])) ]);

(*Stronger version of the rule above*)
val UnE' = prove_goal ZF.thy
    "[| c : A Un B;  c:A ==> P;  [| c:B;  c~:A |] ==> P |] ==> P"
 (fn major::prems =>
  [(rtac (major RS UnE) 1),
   (eresolve_tac prems 1),
   (rtac classical 1),
   (eresolve_tac prems 1),
   (swap_res_tac prems 1),
   (etac notnotD 1)]);

val Un_iff = prove_goal ZF.thy "c : A Un B <-> (c:A | c:B)"
 (fn _ => [ (fast_tac (lemmas_cs addIs [UnI1,UnI2] addSEs [UnE]) 1) ]);

(*Classical introduction rule: no commitment to A vs B*)
val UnCI = prove_goal ZF.thy "(c ~: B ==> c : A) ==> c : A Un B"
 (fn [prem]=>
  [ (rtac (disjCI RS (Un_iff RS iffD2)) 1),
    (etac prem 1) ]);


(*** Rules for small intersection -- Int -- defined via Upair ***)

val IntI = prove_goalw ZF.thy [Int_def]
    "[| c : A;  c : B |] ==> c : A Int B"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems @ [UpairI1,InterI]) 1
     ORELSE eresolve_tac [UpairE, ssubst] 1)) ]);

val IntD1 = prove_goalw ZF.thy [Int_def] "c : A Int B ==> c : A"
 (fn [major]=>
  [ (rtac (UpairI1 RS (major RS InterD)) 1) ]);

val IntD2 = prove_goalw ZF.thy [Int_def] "c : A Int B ==> c : B"
 (fn [major]=>
  [ (rtac (UpairI2 RS (major RS InterD)) 1) ]);

val IntE = prove_goal ZF.thy
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (resolve_tac (prems RL [IntD1,IntD2]) 1)) ]);

val Int_iff = prove_goal ZF.thy "c : A Int B <-> (c:A & c:B)"
 (fn _ => [ (fast_tac (lemmas_cs addSIs [IntI] addSEs [IntE]) 1) ]);


(*** Rules for set difference -- defined via Upair ***)

val DiffI = prove_goalw ZF.thy [Diff_def]
    "[| c : A;  c ~: B |] ==> c : A - B"
 (fn prems=> [ (REPEAT (resolve_tac (prems @ [CollectI]) 1)) ]);

val DiffD1 = prove_goalw ZF.thy [Diff_def]
    "c : A - B ==> c : A"
 (fn [major]=> [ (rtac (major RS CollectD1) 1) ]);

val DiffD2 = prove_goalw ZF.thy [Diff_def]
    "c : A - B ==> c ~: B"
 (fn [major]=> [ (rtac (major RS CollectD2) 1) ]);

val DiffE = prove_goal ZF.thy
    "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (ares_tac (prems RL [DiffD1, DiffD2]) 1)) ]);

val Diff_iff = prove_goal ZF.thy "c : A-B <-> (c:A & c~:B)"
 (fn _ => [ (fast_tac (lemmas_cs addSIs [DiffI] addSEs [DiffE]) 1) ]);

(*** Rules for cons -- defined via Un and Upair ***)

val consI1 = prove_goalw ZF.thy [cons_def] "a : cons(a,B)"
 (fn _ => [ (rtac (UpairI1 RS UnI1) 1) ]);

val consI2 = prove_goalw ZF.thy [cons_def] "a : B ==> a : cons(b,B)"
 (fn [prem]=> [ (rtac (prem RS UnI2) 1) ]);

val consE = prove_goalw ZF.thy [cons_def]
    "[| a : cons(b,A);  a=b ==> P;  a:A ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems @ [UpairE]) 1)) ]);

(*Stronger version of the rule above*)
val consE' = prove_goal ZF.thy
    "[| a : cons(b,A);  a=b ==> P;  [| a:A;  a~=b |] ==> P |] ==> P"
 (fn major::prems =>
  [(rtac (major RS consE) 1),
   (eresolve_tac prems 1),
   (rtac classical 1),
   (eresolve_tac prems 1),
   (swap_res_tac prems 1),
   (etac notnotD 1)]);

val cons_iff = prove_goal ZF.thy "a : cons(b,A) <-> (a=b | a:A)"
 (fn _ => [ (fast_tac (lemmas_cs addIs [consI1,consI2] addSEs [consE]) 1) ]);

(*Classical introduction rule*)
val consCI = prove_goal ZF.thy "(a~:B ==> a=b) ==> a: cons(b,B)"
 (fn [prem]=>
  [ (rtac (disjCI RS (cons_iff RS iffD2)) 1),
    (etac prem 1) ]);

(*** Singletons - using cons ***)

val singletonI = prove_goal ZF.thy "a : {a}"
 (fn _=> [ (rtac consI1 1) ]);

val singletonE = prove_goal ZF.thy "[| a: {b};  a=b ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS consE) 1),
    (REPEAT (eresolve_tac (prems @ [emptyE]) 1)) ]);


(*** Rules for Descriptions ***)

val the_equality = prove_goalw ZF.thy [the_def]
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a"
 (fn prems=>
  [ (fast_tac (lemmas_cs addIs ([equalityI,singletonI]@prems) 
	                 addEs (prems RL [subst])) 1) ]);

(* Only use this if you already know EX!x. P(x) *)
val the_equality2 = prove_goal ZF.thy
    "!!P. [| EX! x. P(x);  P(a) |] ==> (THE x. P(x)) = a"
 (fn _ =>
  [ (deepen_tac (lemmas_cs addSIs [the_equality]) 1 1) ]);

val theI = prove_goal ZF.thy "EX! x. P(x) ==> P(THE x. P(x))"
 (fn [major]=>
  [ (rtac (major RS ex1E) 1),
    (resolve_tac [major RS the_equality2 RS ssubst] 1),
    (REPEAT (assume_tac 1)) ]);

(*the_cong is no longer necessary: if (ALL y.P(y)<->Q(y)) then 
  (THE x.P(x))  rewrites to  (THE x. Q(x))  *)

(*If it's "undefined", it's zero!*)
val the_0 = prove_goalw ZF.thy [the_def]
    "!!P. ~ (EX! x. P(x)) ==> (THE x. P(x))=0"
 (fn _ =>
  [ (fast_tac (lemmas_cs addIs [equalityI] addSEs [ReplaceE]) 1) ]);


(*** if -- a conditional expression for formulae ***)

goalw ZF.thy [if_def] "if(True,a,b) = a";
by (fast_tac (lemmas_cs addIs [the_equality]) 1);
val if_true = result();

goalw ZF.thy [if_def] "if(False,a,b) = b";
by (fast_tac (lemmas_cs addIs [the_equality]) 1);
val if_false = result();

(*Never use with case splitting, or if P is known to be true or false*)
val prems = goalw ZF.thy [if_def]
    "[| P<->Q;  Q ==> a=c;  ~Q ==> b=d |] ==> if(P,a,b) = if(Q,c,d)";
by (simp_tac (FOL_ss addsimps prems addcongs [conj_cong]) 1);
val if_cong = result();

(*Not needed for rewriting, since P would rewrite to True anyway*)
goalw ZF.thy [if_def] "!!P. P ==> if(P,a,b) = a";
by (fast_tac (lemmas_cs addSIs [the_equality]) 1);
val if_P = result();

(*Not needed for rewriting, since P would rewrite to False anyway*)
goalw ZF.thy [if_def] "!!P. ~P ==> if(P,a,b) = b";
by (fast_tac (lemmas_cs addSIs [the_equality]) 1);
val if_not_P = result();

val if_ss = FOL_ss addsimps  [if_true,if_false];

val expand_if = prove_goal ZF.thy
    "P(if(Q,x,y)) <-> ((Q --> P(x)) & (~Q --> P(y)))"
 (fn _=> [ (excluded_middle_tac "Q" 1),
	   (asm_simp_tac if_ss 1),
	   (asm_simp_tac if_ss 1) ]);

val prems = goal ZF.thy
    "[| P ==> a: A;  ~P ==> b: A |] ==> if(P,a,b): A";
by (excluded_middle_tac "P" 1);
by (ALLGOALS (asm_simp_tac (if_ss addsimps prems)));
val if_type = result();


(*** Foundation lemmas ***)

(*was called mem_anti_sym*)
val mem_asym = prove_goal ZF.thy "!!P. [| a:b;  b:a |] ==> P"
 (fn _=>
  [ (res_inst_tac [("A1","{a,b}")] (foundation RS disjE) 1),
    (etac equals0D 1),
    (rtac consI1 1),
    (fast_tac (lemmas_cs addIs [consI1,consI2]
		         addSEs [consE,equalityE]) 1) ]);

(*was called mem_anti_refl*)
val mem_irrefl = prove_goal ZF.thy "a:a ==> P"
 (fn [major]=> [ (rtac (major RS (major RS mem_asym)) 1) ]);

val mem_not_refl = prove_goal ZF.thy "a ~: a"
 (K [ (rtac notI 1), (etac mem_irrefl 1) ]);

(*Good for proving inequalities by rewriting*)
val mem_imp_not_eq = prove_goal ZF.thy "!!a A. a:A ==> a ~= A"
 (fn _=> [ fast_tac (lemmas_cs addSEs [mem_irrefl]) 1 ]);

(*** Rules for succ ***)

val succI1 = prove_goalw ZF.thy [succ_def] "i : succ(i)"
 (fn _=> [ (rtac consI1 1) ]);

val succI2 = prove_goalw ZF.thy [succ_def]
    "i : j ==> i : succ(j)"
 (fn [prem]=> [ (rtac (prem RS consI2) 1) ]);

val succE = prove_goalw ZF.thy [succ_def]
    "[| i : succ(j);  i=j ==> P;  i:j ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS consE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

val succ_iff = prove_goal ZF.thy "i : succ(j) <-> i=j | i:j"
 (fn _ => [ (fast_tac (lemmas_cs addIs [succI1,succI2] addSEs [succE]) 1) ]);

(*Classical introduction rule*)
val succCI = prove_goal ZF.thy "(i~:j ==> i=j) ==> i: succ(j)"
 (fn [prem]=>
  [ (rtac (disjCI RS (succ_iff RS iffD2)) 1),
    (etac prem 1) ]);

val succ_neq_0 = prove_goal ZF.thy "succ(n)=0 ==> P"
 (fn [major]=>
  [ (rtac (major RS equalityD1 RS subsetD RS emptyE) 1),
    (rtac succI1 1) ]);

(*Useful for rewriting*)
val succ_not_0 = prove_goal ZF.thy "succ(n) ~= 0"
 (fn _=> [ (rtac notI 1), (etac succ_neq_0 1) ]);

(* succ(c) <= B ==> c : B *)
val succ_subsetD = succI1 RSN (2,subsetD);

val succ_inject = prove_goal ZF.thy "!!m n. succ(m) = succ(n) ==> m=n"
 (fn _ =>
  [ (fast_tac (lemmas_cs addSEs [succE, equalityE, make_elim succ_subsetD] 
                         addEs [mem_asym]) 1) ]);

val succ_inject_iff = prove_goal ZF.thy "succ(m) = succ(n) <-> m=n"
 (fn _=> [ (fast_tac (FOL_cs addSEs [succ_inject]) 1) ]);

(*UpairI1/2 should become UpairCI;  mem_irrefl as a hazE? *)
val upair_cs = lemmas_cs
  addSIs [singletonI, DiffI, IntI, UnCI, consCI, succCI, UpairI1,UpairI2]
  addSEs [singletonE, DiffE, IntE, UnE, consE, succE, UpairE];

