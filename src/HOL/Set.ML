(*  Title:      HOL/set
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Set theory for higher-order logic.  A set is simply a predicate.
*)

open Set;

section "Relating predicates and sets";

Addsimps [Collect_mem_eq];
AddIffs  [mem_Collect_eq];

goal Set.thy "!!a. P(a) ==> a : {x. P(x)}";
by (Asm_simp_tac 1);
qed "CollectI";

val prems = goal Set.thy "!!a. a : {x. P(x)} ==> P(a)";
by (Asm_full_simp_tac 1);
qed "CollectD";

val [prem] = goal Set.thy "[| !!x. (x:A) = (x:B) |] ==> A = B";
by (rtac (prem RS ext RS arg_cong RS box_equals) 1);
by (rtac Collect_mem_eq 1);
by (rtac Collect_mem_eq 1);
qed "set_ext";

val [prem] = goal Set.thy "[| !!x. P(x)=Q(x) |] ==> {x. P(x)} = {x. Q(x)}";
by (rtac (prem RS ext RS arg_cong) 1);
qed "Collect_cong";

val CollectE = make_elim CollectD;

AddSIs [CollectI];
AddSEs [CollectE];


section "Bounded quantifiers";

val prems = goalw Set.thy [Ball_def]
    "[| !!x. x:A ==> P(x) |] ==> ! x:A. P(x)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "ballI";

val [major,minor] = goalw Set.thy [Ball_def]
    "[| ! x:A. P(x);  x:A |] ==> P(x)";
by (rtac (minor RS (major RS spec RS mp)) 1);
qed "bspec";

val major::prems = goalw Set.thy [Ball_def]
    "[| ! x:A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q";
by (rtac (major RS spec RS impCE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "ballE";

(*Takes assumptions ! x:A.P(x) and a:A; creates assumption P(a)*)
fun ball_tac i = etac ballE i THEN contr_tac (i+1);

AddSIs [ballI];
AddEs  [ballE];

val prems = goalw Set.thy [Bex_def]
    "[| P(x);  x:A |] ==> ? x:A. P(x)";
by (REPEAT (ares_tac (prems @ [exI,conjI]) 1));
qed "bexI";

qed_goal "bexCI" Set.thy 
   "[| ! x:A. ~P(x) ==> P(a);  a:A |] ==> ? x:A. P(x)"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1))  ]);

val major::prems = goalw Set.thy [Bex_def]
    "[| ? x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q  |] ==> Q";
by (rtac (major RS exE) 1);
by (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1));
qed "bexE";

AddIs  [bexI];
AddSEs [bexE];

(*Trival rewrite rule*)
goal Set.thy "(! x:A. P) = ((? x. x:A) --> P)";
by (simp_tac (simpset() addsimps [Ball_def]) 1);
qed "ball_triv";

(*Dual form for existentials*)
goal Set.thy "(? x:A. P) = ((? x. x:A) & P)";
by (simp_tac (simpset() addsimps [Bex_def]) 1);
qed "bex_triv";

Addsimps [ball_triv, bex_triv];

(** Congruence rules **)

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> P(x) = Q(x) |] ==> \
\    (! x:A. P(x)) = (! x:B. Q(x))";
by (resolve_tac (prems RL [ssubst]) 1);
by (REPEAT (ares_tac [ballI,iffI] 1
     ORELSE eresolve_tac ([make_elim bspec, mp] @ (prems RL [iffE])) 1));
qed "ball_cong";

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> P(x) = Q(x) |] ==> \
\    (? x:A. P(x)) = (? x:B. Q(x))";
by (resolve_tac (prems RL [ssubst]) 1);
by (REPEAT (etac bexE 1
     ORELSE ares_tac ([bexI,iffI] @ (prems RL [iffD1,iffD2])) 1));
qed "bex_cong";

section "Subsets";

val prems = goalw Set.thy [subset_def] "(!!x. x:A ==> x:B) ==> A <= B";
by (REPEAT (ares_tac (prems @ [ballI]) 1));
qed "subsetI";

Blast.overload ("op <=", domain_type); (*The <= relation is overloaded*)

(*While (:) is not, its type must be kept
  for overloading of = to work.*)
Blast.overload ("op :", domain_type);
seq (fn a => Blast.overload (a, HOLogic.dest_setT o domain_type))
    ["Ball", "Bex"];
(*need UNION, INTER also?*)


(*Rule in Modus Ponens style*)
val major::prems = goalw Set.thy [subset_def] "[| A <= B;  c:A |] ==> c:B";
by (rtac (major RS bspec) 1);
by (resolve_tac prems 1);
qed "subsetD";

(*The same, with reversed premises for use with etac -- cf rev_mp*)
qed_goal "rev_subsetD" Set.thy "[| c:A;  A <= B |] ==> c:B"
 (fn prems=>  [ (REPEAT (resolve_tac (prems@[subsetD]) 1)) ]);

(*Converts A<=B to x:A ==> x:B*)
fun impOfSubs th = th RSN (2, rev_subsetD);

qed_goal "contra_subsetD" Set.thy "!!c. [| A <= B; c ~: B |] ==> c ~: A"
 (fn prems=>  [ (REPEAT (eresolve_tac [asm_rl, contrapos, subsetD] 1)) ]);

qed_goal "rev_contra_subsetD" Set.thy "!!c. [| c ~: B;  A <= B |] ==> c ~: A"
 (fn prems=>  [ (REPEAT (eresolve_tac [asm_rl, contrapos, subsetD] 1)) ]);

(*Classical elimination rule*)
val major::prems = goalw Set.thy [subset_def] 
    "[| A <= B;  c~:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "subsetCE";

(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
fun set_mp_tac i = etac subsetCE i  THEN  mp_tac i;

AddSIs [subsetI];
AddEs  [subsetD, subsetCE];

qed_goal "subset_refl" Set.thy "A <= (A::'a set)"
 (fn _=> [Fast_tac 1]);		(*Blast_tac would try order_refl and fail*)

val prems = goal Set.thy "!!B. [| A<=B;  B<=C |] ==> A<=(C::'a set)";
by (Blast_tac 1);
qed "subset_trans";


section "Equality";

(*Anti-symmetry of the subset relation*)
val prems = goal Set.thy "[| A <= B;  B <= A |] ==> A = (B::'a set)";
by (rtac (iffI RS set_ext) 1);
by (REPEAT (ares_tac (prems RL [subsetD]) 1));
qed "subset_antisym";
val equalityI = subset_antisym;

AddSIs [equalityI];

(* Equality rules from ZF set theory -- are they appropriate here? *)
val prems = goal Set.thy "A = B ==> A<=(B::'a set)";
by (resolve_tac (prems RL [subst]) 1);
by (rtac subset_refl 1);
qed "equalityD1";

val prems = goal Set.thy "A = B ==> B<=(A::'a set)";
by (resolve_tac (prems RL [subst]) 1);
by (rtac subset_refl 1);
qed "equalityD2";

val prems = goal Set.thy
    "[| A = B;  [| A<=B; B<=(A::'a set) |] ==> P |]  ==>  P";
by (resolve_tac prems 1);
by (REPEAT (resolve_tac (prems RL [equalityD1,equalityD2]) 1));
qed "equalityE";

val major::prems = goal Set.thy
    "[| A = B;  [| c:A; c:B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P";
by (rtac (major RS equalityE) 1);
by (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1));
qed "equalityCE";

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. *)
val prems = goal Set.thy 
    "[| p:A;  !!z. z:A ==> p=z --> R |] ==> R";
by (rtac mp 1);
by (REPEAT (resolve_tac (refl::prems) 1));
qed "setup_induction";


section "The empty set -- {}";

qed_goalw "empty_iff" Set.thy [empty_def] "(c : {}) = False"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [empty_iff];

qed_goal "emptyE" Set.thy "!!a. a:{} ==> P"
 (fn _ => [Full_simp_tac 1]);

AddSEs [emptyE];

qed_goal "empty_subsetI" Set.thy "{} <= A"
 (fn _ => [ (Blast_tac 1) ]);

qed_goal "equals0I" Set.thy "[| !!y. y:A ==> False |] ==> A={}"
 (fn [prem]=>
  [ (blast_tac (claset() addIs [prem RS FalseE]) 1) ]);

qed_goal "equals0D" Set.thy "!!a. [| A={};  a:A |] ==> P"
 (fn _ => [ (Blast_tac 1) ]);


section "The Powerset operator -- Pow";

qed_goalw "Pow_iff" Set.thy [Pow_def] "(A : Pow(B)) = (A <= B)"
 (fn _ => [ (Asm_simp_tac 1) ]);

AddIffs [Pow_iff]; 

qed_goalw "PowI" Set.thy [Pow_def] "!!A B. A <= B ==> A : Pow(B)"
 (fn _ => [ (etac CollectI 1) ]);

qed_goalw "PowD" Set.thy [Pow_def] "!!A B. A : Pow(B)  ==>  A<=B"
 (fn _=> [ (etac CollectD 1) ]);

val Pow_bottom = empty_subsetI RS PowI;        (* {}: Pow(B) *)
val Pow_top = subset_refl RS PowI;             (* A : Pow(A) *)


section "Set complement -- Compl";

qed_goalw "Compl_iff" Set.thy [Compl_def] "(c : Compl(A)) = (c~:A)"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [Compl_iff];

val prems = goalw Set.thy [Compl_def]
    "[| c:A ==> False |] ==> c : Compl(A)";
by (REPEAT (ares_tac (prems @ [CollectI,notI]) 1));
qed "ComplI";

(*This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the notional
  turnstile...*)
val major::prems = goalw Set.thy [Compl_def]
    "c : Compl(A) ==> c~:A";
by (rtac (major RS CollectD) 1);
qed "ComplD";

val ComplE = make_elim ComplD;

AddSIs [ComplI];
AddSEs [ComplE];


section "Binary union -- Un";

qed_goalw "Un_iff" Set.thy [Un_def] "(c : A Un B) = (c:A | c:B)"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [Un_iff];

goal Set.thy "!!c. c:A ==> c : A Un B";
by (Asm_simp_tac 1);
qed "UnI1";

goal Set.thy "!!c. c:B ==> c : A Un B";
by (Asm_simp_tac 1);
qed "UnI2";

(*Classical introduction rule: no commitment to A vs B*)
qed_goal "UnCI" Set.thy "(c~:B ==> c:A) ==> c : A Un B"
 (fn prems=>
  [ (Simp_tac 1),
    (REPEAT (ares_tac (prems@[disjCI]) 1)) ]);

val major::prems = goalw Set.thy [Un_def]
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS CollectD RS disjE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "UnE";

AddSIs [UnCI];
AddSEs [UnE];


section "Binary intersection -- Int";

qed_goalw "Int_iff" Set.thy [Int_def] "(c : A Int B) = (c:A & c:B)"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [Int_iff];

goal Set.thy "!!c. [| c:A;  c:B |] ==> c : A Int B";
by (Asm_simp_tac 1);
qed "IntI";

goal Set.thy "!!c. c : A Int B ==> c:A";
by (Asm_full_simp_tac 1);
qed "IntD1";

goal Set.thy "!!c. c : A Int B ==> c:B";
by (Asm_full_simp_tac 1);
qed "IntD2";

val [major,minor] = goal Set.thy
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P";
by (rtac minor 1);
by (rtac (major RS IntD1) 1);
by (rtac (major RS IntD2) 1);
qed "IntE";

AddSIs [IntI];
AddSEs [IntE];

section "Set difference";

qed_goalw "Diff_iff" Set.thy [set_diff_def] "(c : A-B) = (c:A & c~:B)"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [Diff_iff];

qed_goal "DiffI" Set.thy "!!c. [| c : A;  c ~: B |] ==> c : A - B"
 (fn _=> [ Asm_simp_tac 1 ]);

qed_goal "DiffD1" Set.thy "!!c. c : A - B ==> c : A"
 (fn _=> [ (Asm_full_simp_tac 1) ]);

qed_goal "DiffD2" Set.thy "!!c. [| c : A - B;  c : B |] ==> P"
 (fn _=> [ (Asm_full_simp_tac 1) ]);

qed_goal "DiffE" Set.thy "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (ares_tac (prems RL [DiffD1, DiffD2 RS notI]) 1)) ]);

AddSIs [DiffI];
AddSEs [DiffE];


section "Augmenting a set -- insert";

qed_goalw "insert_iff" Set.thy [insert_def] "a : insert b A = (a=b | a:A)"
 (fn _ => [Blast_tac 1]);

Addsimps [insert_iff];

qed_goal "insertI1" Set.thy "a : insert a B"
 (fn _ => [Simp_tac 1]);

qed_goal "insertI2" Set.thy "!!a. a : B ==> a : insert b B"
 (fn _=> [Asm_simp_tac 1]);

qed_goalw "insertE" Set.thy [insert_def]
    "[| a : insert b A;  a=b ==> P;  a:A ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems @ [CollectE]) 1)) ]);

(*Classical introduction rule*)
qed_goal "insertCI" Set.thy "(a~:B ==> a=b) ==> a: insert b B"
 (fn prems=>
  [ (Simp_tac 1),
    (REPEAT (ares_tac (prems@[disjCI]) 1)) ]);

AddSIs [insertCI]; 
AddSEs [insertE];

section "Singletons, using insert";

qed_goal "singletonI" Set.thy "a : {a}"
 (fn _=> [ (rtac insertI1 1) ]);

goal Set.thy "!!a. b : {a} ==> b=a";
by (Blast_tac 1);
qed "singletonD";

bind_thm ("singletonE", make_elim singletonD);

qed_goal "singleton_iff" thy "(b : {a}) = (b=a)" 
(fn _ => [Blast_tac 1]);

goal Set.thy "!!a b. {a}={b} ==> a=b";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "singleton_inject";

(*Redundant? But unlike insertCI, it proves the subgoal immediately!*)
AddSIs [singletonI];   
AddSDs [singleton_inject];
AddSEs [singletonE];

goal Set.thy "{x. x=a} = {a}";
by(Blast_tac 1);
qed "singleton_conv";
Addsimps [singleton_conv];

section "The universal set -- UNIV";

qed_goal "UNIV_I" Set.thy "x : UNIV"
  (fn _ => [rtac ComplI 1, etac emptyE 1]);

qed_goal "subset_UNIV" Set.thy "A <= UNIV"
  (fn _ => [rtac subsetI 1, rtac UNIV_I 1]);


section "Unions of families -- UNION x:A. B(x) is Union(B``A)";

goalw Set.thy [UNION_def] "(b: (UN x:A. B(x))) = (EX x:A. b: B(x))";
by (Blast_tac 1);
qed "UN_iff";

Addsimps [UN_iff];

(*The order of the premises presupposes that A is rigid; b may be flexible*)
goal Set.thy "!!b. [| a:A;  b: B(a) |] ==> b: (UN x:A. B(x))";
by (Auto_tac());
qed "UN_I";

val major::prems = goalw Set.thy [UNION_def]
    "[| b : (UN x:A. B(x));  !!x.[| x:A;  b: B(x) |] ==> R |] ==> R";
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
qed "UN_E";

AddIs  [UN_I];
AddSEs [UN_E];

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (UN x:A. C(x)) = (UN x:B. D(x))";
by (REPEAT (etac UN_E 1
     ORELSE ares_tac ([UN_I,equalityI,subsetI] @ 
                      (prems RL [equalityD1,equalityD2] RL [subsetD])) 1));
qed "UN_cong";


section "Intersections of families -- INTER x:A. B(x) is Inter(B``A)";

goalw Set.thy [INTER_def] "(b: (INT x:A. B(x))) = (ALL x:A. b: B(x))";
by (Auto_tac());
qed "INT_iff";

Addsimps [INT_iff];

val prems = goalw Set.thy [INTER_def]
    "(!!x. x:A ==> b: B(x)) ==> b : (INT x:A. B(x))";
by (REPEAT (ares_tac ([CollectI,ballI] @ prems) 1));
qed "INT_I";

goal Set.thy "!!b. [| b : (INT x:A. B(x));  a:A |] ==> b: B(a)";
by (Auto_tac());
qed "INT_D";

(*"Classical" elimination -- by the Excluded Middle on a:A *)
val major::prems = goalw Set.thy [INTER_def]
    "[| b : (INT x:A. B(x));  b: B(a) ==> R;  a~:A ==> R |] ==> R";
by (rtac (major RS CollectD RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "INT_E";

AddSIs [INT_I];
AddEs  [INT_D, INT_E];

val prems = goal Set.thy
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (INT x:A. C(x)) = (INT x:B. D(x))";
by (REPEAT_FIRST (resolve_tac [INT_I,equalityI,subsetI]));
by (REPEAT (dtac INT_D 1
     ORELSE ares_tac (prems RL [equalityD1,equalityD2] RL [subsetD]) 1));
qed "INT_cong";


section "Unions over a type; UNION1(B) = Union(range(B))";

goalw Set.thy [UNION1_def] "(b: (UN x. B(x))) = (EX x. b: B(x))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "UN1_iff";

Addsimps [UN1_iff];

(*The order of the premises presupposes that A is rigid; b may be flexible*)
goal Set.thy "!!b. b: B(x) ==> b: (UN x. B(x))";
by (Auto_tac());
qed "UN1_I";

val major::prems = goalw Set.thy [UNION1_def]
    "[| b : (UN x. B(x));  !!x. b: B(x) ==> R |] ==> R";
by (rtac (major RS UN_E) 1);
by (REPEAT (ares_tac prems 1));
qed "UN1_E";

AddIs  [UN1_I];
AddSEs [UN1_E];


section "Intersections over a type; INTER1(B) = Inter(range(B))";

goalw Set.thy [INTER1_def] "(b: (INT x. B(x))) = (ALL x. b: B(x))";
by (Simp_tac 1);
by (Blast_tac 1);
qed "INT1_iff";

Addsimps [INT1_iff];

val prems = goalw Set.thy [INTER1_def]
    "(!!x. b: B(x)) ==> b : (INT x. B(x))";
by (REPEAT (ares_tac (INT_I::prems) 1));
qed "INT1_I";

goal Set.thy "!!b. b : (INT x. B(x)) ==> b: B(a)";
by (Asm_full_simp_tac 1);
qed "INT1_D";

AddSIs [INT1_I]; 
AddDs  [INT1_D];


section "Union";

goalw Set.thy [Union_def] "(A : Union(C)) = (EX X:C. A:X)";
by (Blast_tac 1);
qed "Union_iff";

Addsimps [Union_iff];

(*The order of the premises presupposes that C is rigid; A may be flexible*)
goal Set.thy "!!X. [| X:C;  A:X |] ==> A : Union(C)";
by (Auto_tac());
qed "UnionI";

val major::prems = goalw Set.thy [Union_def]
    "[| A : Union(C);  !!X.[| A:X;  X:C |] ==> R |] ==> R";
by (rtac (major RS UN_E) 1);
by (REPEAT (ares_tac prems 1));
qed "UnionE";

AddIs  [UnionI];
AddSEs [UnionE];


section "Inter";

goalw Set.thy [Inter_def] "(A : Inter(C)) = (ALL X:C. A:X)";
by (Blast_tac 1);
qed "Inter_iff";

Addsimps [Inter_iff];

val prems = goalw Set.thy [Inter_def]
    "[| !!X. X:C ==> A:X |] ==> A : Inter(C)";
by (REPEAT (ares_tac ([INT_I] @ prems) 1));
qed "InterI";

(*A "destruct" rule -- every X in C contains A as an element, but
  A:X can hold when X:C does not!  This rule is analogous to "spec". *)
goal Set.thy "!!X. [| A : Inter(C);  X:C |] ==> A:X";
by (Auto_tac());
qed "InterD";

(*"Classical" elimination rule -- does not require proving X:C *)
val major::prems = goalw Set.thy [Inter_def]
    "[| A : Inter(C);  X~:C ==> R;  A:X ==> R |] ==> R";
by (rtac (major RS INT_E) 1);
by (REPEAT (eresolve_tac prems 1));
qed "InterE";

AddSIs [InterI];
AddEs  [InterD, InterE];


(*** Image of a set under a function ***)

(*Frequently b does not have the syntactic form of f(x).*)
val prems = goalw thy [image_def] "[| b=f(x);  x:A |] ==> b : f``A";
by (REPEAT (resolve_tac (prems @ [CollectI,bexI,prem]) 1));
qed "image_eqI";
Addsimps [image_eqI];

bind_thm ("imageI", refl RS image_eqI);

(*The eta-expansion gives variable-name preservation.*)
val major::prems = goalw thy [image_def]
    "[| b : (%x. f(x))``A;  !!x.[| b=f(x);  x:A |] ==> P |] ==> P"; 
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
qed "imageE";

AddIs  [image_eqI];
AddSEs [imageE]; 

goalw thy [o_def] "(f o g)``r = f``(g``r)";
by (Blast_tac 1);
qed "image_compose";

goal thy "f``(A Un B) = f``A Un f``B";
by (Blast_tac 1);
qed "image_Un";

goal Set.thy "(z : f``A) = (EX x:A. z = f x)";
by (Blast_tac 1);
qed "image_iff";


(*** Range of a function -- just a translation for image! ***)

goal thy "!!b. b=f(x) ==> b : range(f)";
by (EVERY1 [etac image_eqI, rtac UNIV_I]);
bind_thm ("range_eqI", UNIV_I RSN (2,image_eqI));

bind_thm ("rangeI", UNIV_I RS imageI);

val [major,minor] = goal thy 
    "[| b : range(%x. f(x));  !!x. b=f(x) ==> P |] ==> P"; 
by (rtac (major RS imageE) 1);
by (etac minor 1);
qed "rangeE";


(*** Set reasoning tools ***)


(** Rewrite rules for boolean case-splitting: faster than 
	addsplits[expand_if]
**)

bind_thm ("expand_if_eq1", read_instantiate [("P", "%x. x = ?b")] expand_if);
bind_thm ("expand_if_eq2", read_instantiate [("P", "%x. ?a = x")] expand_if);

bind_thm ("expand_if_mem1", 
    read_instantiate_sg (sign_of Set.thy) [("P", "%x. x : ?b")] expand_if);
bind_thm ("expand_if_mem2", 
    read_instantiate_sg (sign_of Set.thy) [("P", "%x. ?a : x")] expand_if);

val expand_ifs = [if_bool_eq, expand_if_eq1, expand_if_eq2,
		  expand_if_mem1, expand_if_mem2];


(*Each of these has ALREADY been added to simpset() above.*)
val mem_simps = [insert_iff, empty_iff, Un_iff, Int_iff, Compl_iff, Diff_iff, 
                 mem_Collect_eq, 
		 UN_iff, UN1_iff, Union_iff, 
		 INT_iff, INT1_iff, Inter_iff];

(*Not for Addsimps -- it can cause goals to blow up!*)
goal Set.thy "(a : (if Q then x else y)) = ((Q --> a:x) & (~Q --> a : y))";
by (simp_tac (simpset() addsplits [expand_if]) 1);
qed "mem_if";

val mksimps_pairs = ("Ball",[bspec]) :: mksimps_pairs;

simpset_ref() := simpset() addcongs [ball_cong,bex_cong]
                    setmksimps (mksimps mksimps_pairs);

Addsimps[subset_UNIV, empty_subsetI, subset_refl];


(*** < ***)

goalw Set.thy [psubset_def] "!!A::'a set. [| A <= B; A ~= B |] ==> A<B";
by (Blast_tac 1);
qed "psubsetI";

goalw Set.thy [psubset_def]
    "!!x. A < insert x B ==> (x ~: A) & A<=B | x:A & A-{x}<B";
by (Auto_tac());
qed "psubset_insertD";

bind_thm ("psubset_eq", psubset_def RS meta_eq_to_obj_eq);
