(*  Title: 	ZF/zf.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1994  University of Cambridge

Basic introduction and elimination rules for Zermelo-Fraenkel Set Theory 
*)

open ZF;

signature ZF_LEMMAS = 
  sig
  val ballE		: thm
  val ballI		: thm
  val ball_cong		: thm
  val ball_simp		: thm
  val ball_tac		: int -> tactic
  val bexCI		: thm
  val bexE		: thm
  val bexI		: thm
  val bex_cong		: thm
  val bspec		: thm
  val CollectD1		: thm
  val CollectD2		: thm
  val CollectE		: thm
  val CollectI		: thm
  val Collect_cong	: thm
  val emptyE		: thm
  val empty_subsetI	: thm
  val equalityCE	: thm
  val equalityD1	: thm
  val equalityD2	: thm
  val equalityE		: thm
  val equalityI		: thm
  val equality_iffI	: thm
  val equals0D		: thm
  val equals0I		: thm
  val InterD		: thm
  val InterE		: thm
  val InterI		: thm
  val Inter_iff 	: thm
  val INT_E		: thm
  val INT_I		: thm
  val INT_cong		: thm
  val INT_iff		: thm
  val lemmas_cs		: claset
  val PowD		: thm
  val PowI		: thm
  val RepFunE		: thm
  val RepFunI		: thm
  val RepFun_eqI	: thm
  val RepFun_cong	: thm
  val RepFun_iff	: thm
  val ReplaceE		: thm
  val ReplaceE2		: thm
  val ReplaceI		: thm
  val Replace_iff	: thm
  val Replace_cong	: thm
  val rev_ballE		: thm
  val rev_bspec		: thm
  val rev_subsetD	: thm
  val separation	: thm
  val setup_induction	: thm
  val set_mp_tac	: int -> tactic
  val subset0_cs	: claset
  val subsetCE		: thm
  val subsetD		: thm
  val subsetI		: thm
  val subset_iff	: thm
  val subset_refl	: thm
  val subset_trans	: thm
  val UnionE		: thm
  val UnionI		: thm
  val Union_in_Pow	: thm
  val UN_E		: thm
  val UN_I		: thm
  val UN_cong		: thm
  val UN_iff		: thm
  end;


structure ZF_Lemmas : ZF_LEMMAS = 
struct

(*** Bounded universal quantifier ***)

val ballI = prove_goalw ZF.thy [Ball_def]
    "[| !!x. x:A ==> P(x) |] ==> ALL x:A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [allI,impI]) 1)) ]);

val bspec = prove_goalw ZF.thy [Ball_def]
    "[| ALL x:A. P(x);  x: A |] ==> P(x)"
 (fn major::prems=>
  [ (rtac (major RS spec RS mp) 1),
    (resolve_tac prems 1) ]);

val ballE = prove_goalw ZF.thy [Ball_def]
    "[| ALL x:A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS allE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl,impCE]) 1)) ]);

(*Used in the datatype package*)
val rev_bspec = prove_goal ZF.thy
    "!!x A P. [| x: A;  ALL x:A. P(x) |] ==> P(x)"
 (fn _ =>
  [ REPEAT (ares_tac [bspec] 1) ]);

(*Instantiates x first: better for automatic theorem proving?*)
val rev_ballE = prove_goal ZF.thy
    "[| ALL x:A. P(x);  x~:A ==> Q;  P(x) ==> Q |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS ballE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*Takes assumptions ALL x:A.P(x) and a:A; creates assumption P(a)*)
val ball_tac = dtac bspec THEN' assume_tac;

(*Trival rewrite rule;   (ALL x:A.P)<->P holds only if A is nonempty!*)
val ball_simp = prove_goal ZF.thy "(ALL x:A. True) <-> True"
 (fn _=> [ (REPEAT (ares_tac [TrueI,ballI,iffI] 1)) ]);

(*Congruence rule for rewriting*)
val ball_cong = prove_goalw ZF.thy [Ball_def]
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==> Ball(A,P) <-> Ball(A',P')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems) 1) ]);

(*** Bounded existential quantifier ***)

val bexI = prove_goalw ZF.thy [Bex_def]
    "[| P(x);  x: A |] ==> EX x:A. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [exI,conjI]) 1)) ]);

(*Not of the general form for such rules; ~EX has become ALL~ *)
val bexCI = prove_goal ZF.thy 
   "[| ALL x:A. ~P(x) ==> P(a);  a: A |] ==> EX x:A.P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1)) ]);

val bexE = prove_goalw ZF.thy [Bex_def]
    "[| EX x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q \
\    |] ==> Q"
 (fn major::prems=>
  [ (rtac (major RS exE) 1),
    (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1)) ]);

(*We do not even have (EX x:A. True) <-> True unless A is nonempty!!*)

val bex_cong = prove_goalw ZF.thy [Bex_def]
    "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) \
\    |] ==> Bex(A,P) <-> Bex(A',P')"
 (fn prems=> [ (simp_tac (FOL_ss addsimps prems addcongs [conj_cong]) 1) ]);

(*** Rules for subsets ***)

val subsetI = prove_goalw ZF.thy [subset_def]
    "(!!x.x:A ==> x:B) ==> A <= B"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [ballI]) 1)) ]);

(*Rule in Modus Ponens style [was called subsetE] *)
val subsetD = prove_goalw ZF.thy [subset_def] "[| A <= B;  c:A |] ==> c:B"
 (fn major::prems=>
  [ (rtac (major RS bspec) 1),
    (resolve_tac prems 1) ]);

(*Classical elimination rule*)
val subsetCE = prove_goalw ZF.thy [subset_def]
    "[| A <= B;  c~:A ==> P;  c:B ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS ballE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
val set_mp_tac = dtac subsetD THEN' assume_tac;

(*Sometimes useful with premises in this order*)
val rev_subsetD = prove_goal ZF.thy "!!A B c. [| c:A; A<=B |] ==> c:B"
 (fn _=> [REPEAT (ares_tac [subsetD] 1)]);

val subset_refl = prove_goal ZF.thy "A <= A"
 (fn _=> [ (rtac subsetI 1), atac 1 ]);

val subset_trans = prove_goal ZF.thy "[| A<=B;  B<=C |] ==> A<=C"
 (fn prems=> [ (REPEAT (ares_tac ([subsetI]@(prems RL [subsetD])) 1)) ]);

(*Useful for proving A<=B by rewriting in some cases*)
val subset_iff = prove_goalw ZF.thy [subset_def,Ball_def]
     "A<=B <-> (ALL x. x:A --> x:B)"
 (fn _=> [ (rtac iff_refl 1) ]);


(*** Rules for equality ***)

(*Anti-symmetry of the subset relation*)
val equalityI = prove_goal ZF.thy "[| A <= B;  B <= A |] ==> A = B"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[conjI, extension RS iffD2]) 1)) ]);

val equality_iffI = prove_goal ZF.thy "(!!x. x:A <-> x:B) ==> A = B"
 (fn [prem] =>
  [ (rtac equalityI 1),
    (REPEAT (ares_tac [subsetI, prem RS iffD1, prem RS iffD2] 1)) ]);

val equalityD1 = prove_goal ZF.thy "A = B ==> A<=B"
 (fn prems=>
  [ (rtac (extension RS iffD1 RS conjunct1) 1),
    (resolve_tac prems 1) ]);

val equalityD2 = prove_goal ZF.thy "A = B ==> B<=A"
 (fn prems=>
  [ (rtac (extension RS iffD1 RS conjunct2) 1),
    (resolve_tac prems 1) ]);

val equalityE = prove_goal ZF.thy
    "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P"
 (fn prems=>
  [ (DEPTH_SOLVE (resolve_tac (prems@[equalityD1,equalityD2]) 1)) ]);

val equalityCE = prove_goal ZF.thy
    "[| A = B;  [| c:A; c:B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P"
 (fn major::prems=>
  [ (rtac (major RS equalityE) 1),
    (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1)) ]);

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. 
  Would it be better to do subgoal_tac "ALL z. p = f(z) --> R(z)" ??*)
val setup_induction = prove_goal ZF.thy
    "[| p: A;  !!z. z: A ==> p=z --> R |] ==> R"
 (fn prems=>
  [ (rtac mp 1),
    (REPEAT (resolve_tac (refl::prems) 1)) ]);


(*** Rules for Replace -- the derived form of replacement ***)

val Replace_iff = prove_goalw ZF.thy [Replace_def]
    "b : {y. x:A, P(x,y)}  <->  (EX x:A. P(x,b) & (ALL y. P(x,y) --> y=b))"
 (fn _=>
  [ (rtac (replacement RS iff_trans) 1),
    (REPEAT (ares_tac [refl,bex_cong,iffI,ballI,allI,conjI,impI,ex1I] 1
        ORELSE eresolve_tac [conjE, spec RS mp, ex1_functional] 1)) ]);

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
val ReplaceI = prove_goal ZF.thy
    "[| P(x,b);  x: A;  !!y. P(x,y) ==> y=b |] ==> \
\    b : {y. x:A, P(x,y)}"
 (fn prems=>
  [ (rtac (Replace_iff RS iffD2) 1),
    (REPEAT (ares_tac (prems@[bexI,conjI,allI,impI]) 1)) ]);

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
val ReplaceE = prove_goal ZF.thy 
    "[| b : {y. x:A, P(x,y)};  \
\       !!x. [| x: A;  P(x,b);  ALL y. P(x,y)-->y=b |] ==> R \
\    |] ==> R"
 (fn prems=>
  [ (rtac (Replace_iff RS iffD1 RS bexE) 1),
    (etac conjE 2),
    (REPEAT (ares_tac prems 1)) ]);

(*As above but without the (generally useless) 3rd assumption*)
val ReplaceE2 = prove_goal ZF.thy 
    "[| b : {y. x:A, P(x,y)};  \
\       !!x. [| x: A;  P(x,b) |] ==> R \
\    |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (ares_tac prems 1)) ]);

val Replace_cong = prove_goal ZF.thy
    "[| A=B;  !!x y. x:B ==> P(x,y) <-> Q(x,y) |] ==> \
\    Replace(A,P) = Replace(B,Q)"
 (fn prems=>
   let val substprems = prems RL [subst, ssubst]
       and iffprems = prems RL [iffD1,iffD2]
   in [ (rtac equalityI 1),
	(REPEAT (eresolve_tac (substprems@[asm_rl, ReplaceE, spec RS mp]) 1
	 ORELSE resolve_tac [subsetI, ReplaceI] 1
	 ORELSE (resolve_tac iffprems 1 THEN assume_tac 2))) ]
   end);

(*** Rules for RepFun ***)

val RepFunI = prove_goalw ZF.thy [RepFun_def]
    "!!a A. a : A ==> f(a) : {f(x). x:A}"
 (fn _ => [ (REPEAT (ares_tac [ReplaceI,refl] 1)) ]);

(*Useful for coinduction proofs*)
val RepFun_eqI = prove_goal ZF.thy
    "!!b a f. [| b=f(a);  a : A |] ==> b : {f(x). x:A}"
 (fn _ => [ etac ssubst 1, etac RepFunI 1 ]);

val RepFunE = prove_goalw ZF.thy [RepFun_def]
    "[| b : {f(x). x:A};  \
\       !!x.[| x:A;  b=f(x) |] ==> P |] ==> \
\    P"
 (fn major::prems=>
  [ (rtac (major RS ReplaceE) 1),
    (REPEAT (ares_tac prems 1)) ]);

val RepFun_cong = prove_goalw ZF.thy [RepFun_def]
    "[| A=B;  !!x. x:B ==> f(x)=g(x) |] ==> RepFun(A,f) = RepFun(B,g)"
 (fn prems=> [ (simp_tac (FOL_ss addcongs [Replace_cong] addsimps prems) 1) ]);

val RepFun_iff = prove_goalw ZF.thy [Bex_def]
    "b : {f(x). x:A} <-> (EX x:A. b=f(x))"
 (fn _ => [ (fast_tac (FOL_cs addIs [RepFunI] addSEs [RepFunE]) 1) ]);


(*** Rules for Collect -- forming a subset by separation ***)

(*Separation is derivable from Replacement*)
val separation = prove_goalw ZF.thy [Collect_def]
    "a : {x:A. P(x)} <-> a:A & P(a)"
 (fn _=> [ (fast_tac (FOL_cs addIs  [bexI,ReplaceI] 
		             addSEs [bexE,ReplaceE]) 1) ]);

val CollectI = prove_goal ZF.thy
    "[| a:A;  P(a) |] ==> a : {x:A. P(x)}"
 (fn prems=>
  [ (rtac (separation RS iffD2) 1),
    (REPEAT (resolve_tac (prems@[conjI]) 1)) ]);

val CollectE = prove_goal ZF.thy
    "[| a : {x:A. P(x)};  [| a:A; P(a) |] ==> R |] ==> R"
 (fn prems=>
  [ (rtac (separation RS iffD1 RS conjE) 1),
    (REPEAT (ares_tac prems 1)) ]);

val CollectD1 = prove_goal ZF.thy "a : {x:A. P(x)} ==> a:A"
 (fn [major]=>
  [ (rtac (major RS CollectE) 1),
    (assume_tac 1) ]);

val CollectD2 = prove_goal ZF.thy "a : {x:A. P(x)} ==> P(a)"
 (fn [major]=>
  [ (rtac (major RS CollectE) 1),
    (assume_tac 1) ]);

val Collect_cong = prove_goalw ZF.thy [Collect_def] 
    "[| A=B;  !!x. x:B ==> P(x) <-> Q(x) |] ==> Collect(A,P) = Collect(B,Q)"
 (fn prems=> [ (simp_tac (FOL_ss addcongs [Replace_cong] addsimps prems) 1) ]);

(*** Rules for Unions ***)

(*The order of the premises presupposes that C is rigid; A may be flexible*)
val UnionI = prove_goal ZF.thy "[| B: C;  A: B |] ==> A: Union(C)"
 (fn prems=>
  [ (resolve_tac [Union_iff RS iffD2] 1),
    (REPEAT (resolve_tac (prems @ [bexI]) 1)) ]);

val UnionE = prove_goal ZF.thy
    "[| A : Union(C);  !!B.[| A: B;  B: C |] ==> R |] ==> R"
 (fn prems=>
  [ (resolve_tac [Union_iff RS iffD1 RS bexE] 1),
    (REPEAT (ares_tac prems 1)) ]);

(*** Rules for Inter ***)

(*Not obviously useful towards proving InterI, InterD, InterE*)
val Inter_iff = prove_goalw ZF.thy [Inter_def,Ball_def]
    "A : Inter(C) <-> (ALL x:C. A: x) & (EX x. x:C)"
 (fn _=> [ (rtac (separation RS iff_trans) 1),
	   (fast_tac (FOL_cs addIs [UnionI] addSEs [UnionE]) 1) ]);

(* Intersection is well-behaved only if the family is non-empty! *)
val InterI = prove_goalw ZF.thy [Inter_def]
    "[| !!x. x: C ==> A: x;  c:C |] ==> A : Inter(C)"
 (fn prems=>
  [ (DEPTH_SOLVE (ares_tac ([CollectI,UnionI,ballI] @ prems) 1)) ]);

(*A "destruct" rule -- every B in C contains A as an element, but
  A:B can hold when B:C does not!  This rule is analogous to "spec". *)
val InterD = prove_goalw ZF.thy [Inter_def]
    "[| A : Inter(C);  B : C |] ==> A : B"
 (fn [major,minor]=>
  [ (rtac (major RS CollectD2 RS bspec) 1),
    (rtac minor 1) ]);

(*"Classical" elimination rule -- does not require exhibiting B:C *)
val InterE = prove_goalw ZF.thy [Inter_def]
    "[| A : Inter(C);  A:B ==> R;  B~:C ==> R |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS CollectD2 RS ballE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*** Rules for Unions of families ***)
(* UN x:A. B(x) abbreviates Union({B(x). x:A}) *)

val UN_iff = prove_goalw ZF.thy [Bex_def]
    "b : (UN x:A. B(x)) <-> (EX x:A. b : B(x))"
 (fn _=> [ (fast_tac (FOL_cs addIs [UnionI, RepFunI] 
                             addSEs [UnionE, RepFunE]) 1) ]);

(*The order of the premises presupposes that A is rigid; b may be flexible*)
val UN_I = prove_goal ZF.thy "[| a: A;  b: B(a) |] ==> b: (UN x:A. B(x))"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems@[UnionI,RepFunI]) 1)) ]);

val UN_E = prove_goal ZF.thy
    "[| b : (UN x:A. B(x));  !!x.[| x: A;  b: B(x) |] ==> R |] ==> R"
 (fn major::prems=>
  [ (rtac (major RS UnionE) 1),
    (REPEAT (eresolve_tac (prems@[asm_rl, RepFunE, subst]) 1)) ]);

val UN_cong = prove_goal ZF.thy
    "[| A=B;  !!x. x:B ==> C(x)=D(x) |] ==> (UN x:A.C(x)) = (UN x:B.D(x))"
 (fn prems=> [ (simp_tac (FOL_ss addcongs [RepFun_cong] addsimps prems) 1) ]);


(*** Rules for Intersections of families ***)
(* INT x:A. B(x) abbreviates Inter({B(x). x:A}) *)

val INT_iff = prove_goal ZF.thy
    "b : (INT x:A. B(x)) <-> (ALL x:A. b : B(x)) & (EX x. x:A)"
 (fn _=> [ (simp_tac (FOL_ss addsimps [Inter_def, Ball_def, Bex_def, 
				       separation, Union_iff, RepFun_iff]) 1),
	   (fast_tac FOL_cs 1) ]);

val INT_I = prove_goal ZF.thy
    "[| !!x. x: A ==> b: B(x);  a: A |] ==> b: (INT x:A. B(x))"
 (fn prems=>
  [ (REPEAT (ares_tac (prems@[InterI,RepFunI]) 1
     ORELSE eresolve_tac [RepFunE,ssubst] 1)) ]);

val INT_E = prove_goal ZF.thy
    "[| b : (INT x:A. B(x));  a: A |] ==> b : B(a)"
 (fn [major,minor]=>
  [ (rtac (major RS InterD) 1),
    (rtac (minor RS RepFunI) 1) ]);

val INT_cong = prove_goal ZF.thy
    "[| A=B;  !!x. x:B ==> C(x)=D(x) |] ==> (INT x:A.C(x)) = (INT x:B.D(x))"
 (fn prems=> [ (simp_tac (FOL_ss addcongs [RepFun_cong] addsimps prems) 1) ]);


(*** Rules for Powersets ***)

val PowI = prove_goal ZF.thy "A <= B ==> A : Pow(B)"
 (fn [prem]=> [ (rtac (prem RS (Pow_iff RS iffD2)) 1) ]);

val PowD = prove_goal ZF.thy "A : Pow(B)  ==>  A<=B"
 (fn [major]=> [ (rtac (major RS (Pow_iff RS iffD1)) 1) ]);


(*** Rules for the empty set ***)

(*The set {x:0.False} is empty; by foundation it equals 0 
  See Suppes, page 21.*)
val emptyE = prove_goal ZF.thy "a:0 ==> P"
 (fn [major]=>
  [ (rtac (foundation RS disjE) 1),
    (etac (equalityD2 RS subsetD RS CollectD2 RS FalseE) 1),
    (rtac major 1),
    (etac bexE 1),
    (etac (CollectD2 RS FalseE) 1) ]);

val empty_subsetI = prove_goal ZF.thy "0 <= A"
 (fn _ => [ (REPEAT (ares_tac [equalityI,subsetI,emptyE] 1)) ]);

val equals0I = prove_goal ZF.thy "[| !!y. y:A ==> False |] ==> A=0"
 (fn prems=>
  [ (REPEAT (ares_tac (prems@[empty_subsetI,subsetI,equalityI]) 1 
      ORELSE eresolve_tac (prems RL [FalseE]) 1)) ]);

val equals0D = prove_goal ZF.thy "[| A=0;  a:A |] ==> P"
 (fn [major,minor]=>
  [ (rtac (minor RS (major RS equalityD1 RS subsetD RS emptyE)) 1) ]);

(*A claset that leaves <= formulae unchanged!*)
val subset0_cs = FOL_cs
  addSIs [ballI, InterI, CollectI, PowI, empty_subsetI]
  addIs [bexI, UnionI, ReplaceI, RepFunI]
  addSEs [bexE, make_elim PowD, UnionE, ReplaceE2, RepFunE,
	  CollectE, emptyE]
  addEs [rev_ballE, InterD, make_elim InterD, subsetD];

(*Standard claset*)
val lemmas_cs = subset0_cs addSIs [subsetI] addEs [subsetCE];

(*Lemma for the inductive definition in Zorn.thy*)
val Union_in_Pow = prove_goal ZF.thy
    "!!Y. Y : Pow(Pow(A)) ==> Union(Y) : Pow(A)"
 (fn _ => [fast_tac lemmas_cs 1]);

end;

open ZF_Lemmas;
