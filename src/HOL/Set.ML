(*  Title:      HOL/set
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Set theory for higher-order logic.  A set is simply a predicate.
*)

section "Relating predicates and sets";

Addsimps [Collect_mem_eq];
AddIffs  [mem_Collect_eq];

Goal "P(a) ==> a : {x. P(x)}";
by (Asm_simp_tac 1);
qed "CollectI";

Goal "a : {x. P(x)} ==> P(a)";
by (Asm_full_simp_tac 1);
qed "CollectD";

val [prem] = Goal "[| !!x. (x:A) = (x:B) |] ==> A = B";
by (rtac (prem RS ext RS arg_cong RS box_equals) 1);
by (rtac Collect_mem_eq 1);
by (rtac Collect_mem_eq 1);
qed "set_ext";

val [prem] = Goal "[| !!x. P(x)=Q(x) |] ==> {x. P(x)} = {x. Q(x)}";
by (rtac (prem RS ext RS arg_cong) 1);
qed "Collect_cong";

val CollectE = make_elim CollectD;

AddSIs [CollectI];
AddSEs [CollectE];


section "Bounded quantifiers";

val prems = Goalw [Ball_def]
    "[| !!x. x:A ==> P(x) |] ==> ! x:A. P(x)";
by (REPEAT (ares_tac (prems @ [allI,impI]) 1));
qed "ballI";

Goalw [Ball_def] "[| ! x:A. P(x);  x:A |] ==> P(x)";
by (Blast_tac 1);
qed "bspec";

val major::prems = Goalw [Ball_def]
    "[| ! x:A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q";
by (rtac (major RS spec RS impCE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "ballE";

(*Takes assumptions ! x:A.P(x) and a:A; creates assumption P(a)*)
fun ball_tac i = etac ballE i THEN contr_tac (i+1);

AddSIs [ballI];
AddEs  [ballE];
AddXDs [bspec];
(* gives better instantiation for bound: *)
claset_ref() := claset() addWrapper ("bspec", fn tac2 =>
			 (dtac bspec THEN' atac) APPEND' tac2);

(*Normally the best argument order: P(x) constrains the choice of x:A*)
Goalw [Bex_def] "[| P(x);  x:A |] ==> ? x:A. P(x)";
by (Blast_tac 1);
qed "bexI";

(*The best argument order when there is only one x:A*)
Goalw [Bex_def] "[| x:A;  P(x) |] ==> ? x:A. P(x)";
by (Blast_tac 1);
qed "rev_bexI";

val prems = Goal 
   "[| ! x:A. ~P(x) ==> P(a);  a:A |] ==> ? x:A. P(x)";
by (rtac classical 1);
by (REPEAT (ares_tac (prems@[bexI,ballI,notI,notE]) 1))  ;
qed "bexCI";

val major::prems = Goalw [Bex_def]
    "[| ? x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q  |] ==> Q";
by (rtac (major RS exE) 1);
by (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1));
qed "bexE";

AddIs  [bexI];
AddSEs [bexE];

(*Trival rewrite rule*)
Goal "(! x:A. P) = ((? x. x:A) --> P)";
by (simp_tac (simpset() addsimps [Ball_def]) 1);
qed "ball_triv";

(*Dual form for existentials*)
Goal "(? x:A. P) = ((? x. x:A) & P)";
by (simp_tac (simpset() addsimps [Bex_def]) 1);
qed "bex_triv";

Addsimps [ball_triv, bex_triv];

(** Congruence rules **)

val prems = Goalw [Ball_def]
    "[| A=B;  !!x. x:B ==> P(x) = Q(x) |] ==> \
\    (! x:A. P(x)) = (! x:B. Q(x))";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "ball_cong";

val prems = Goalw [Bex_def]
    "[| A=B;  !!x. x:B ==> P(x) = Q(x) |] ==> \
\    (? x:A. P(x)) = (? x:B. Q(x))";
by (asm_simp_tac (simpset() addcongs [conj_cong] addsimps prems) 1);
qed "bex_cong";

Addcongs [ball_cong,bex_cong];

section "Subsets";

val prems = Goalw [subset_def] "(!!x. x:A ==> x:B) ==> A <= B";
by (REPEAT (ares_tac (prems @ [ballI]) 1));
qed "subsetI";

(*Map the type ('a set => anything) to just 'a.
  For overloading constants whose first argument has type "'a set" *)
fun overload_1st_set s = Blast.overloaded (s, HOLogic.dest_setT o domain_type);

(*While (:) is not, its type must be kept
  for overloading of = to work.*)
Blast.overloaded ("op :", domain_type);

overload_1st_set "Ball";		(*need UNION, INTER also?*)
overload_1st_set "Bex";

(*Image: retain the type of the set being expressed*)
Blast.overloaded ("op ``", domain_type);

(*Rule in Modus Ponens style*)
Goalw [subset_def] "[| A <= B;  c:A |] ==> c:B";
by (Blast_tac 1);
qed "subsetD";

(*The same, with reversed premises for use with etac -- cf rev_mp*)
Goal "[| c:A;  A <= B |] ==> c:B";
by (REPEAT (ares_tac [subsetD] 1)) ;
qed "rev_subsetD";

(*Converts A<=B to x:A ==> x:B*)
fun impOfSubs th = th RSN (2, rev_subsetD);

Goal "[| A <= B; c ~: B |] ==> c ~: A";
by (REPEAT (eresolve_tac [asm_rl, contrapos, subsetD] 1)) ;
qed "contra_subsetD";

Goal "[| c ~: B;  A <= B |] ==> c ~: A";
by (REPEAT (eresolve_tac [asm_rl, contrapos, subsetD] 1)) ;
qed "rev_contra_subsetD";

(*Classical elimination rule*)
val major::prems = Goalw [subset_def] 
    "[| A <= B;  c~:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "subsetCE";

(*Takes assumptions A<=B; c:A and creates the assumption c:B *)
fun set_mp_tac i = etac subsetCE i  THEN  mp_tac i;

AddSIs [subsetI];
AddEs  [subsetD, subsetCE];

Goal "A <= (A::'a set)";
by (Fast_tac 1);
qed "subset_refl";		(*Blast_tac would try order_refl and fail*)

Goal "[| A<=B;  B<=C |] ==> A<=(C::'a set)";
by (Blast_tac 1);
qed "subset_trans";


section "Equality";

(*Anti-symmetry of the subset relation*)
Goal "[| A <= B;  B <= A |] ==> A = (B::'a set)";
by (rtac set_ext 1);
by (blast_tac (claset() addIs [subsetD]) 1);
qed "subset_antisym";
val equalityI = subset_antisym;

AddSIs [equalityI];

(* Equality rules from ZF set theory -- are they appropriate here? *)
Goal "A = B ==> A<=(B::'a set)";
by (etac ssubst 1);
by (rtac subset_refl 1);
qed "equalityD1";

Goal "A = B ==> B<=(A::'a set)";
by (etac ssubst 1);
by (rtac subset_refl 1);
qed "equalityD2";

val prems = Goal
    "[| A = B;  [| A<=B; B<=(A::'a set) |] ==> P |]  ==>  P";
by (resolve_tac prems 1);
by (REPEAT (resolve_tac (prems RL [equalityD1,equalityD2]) 1));
qed "equalityE";

val major::prems = Goal
    "[| A = B;  [| c:A; c:B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P";
by (rtac (major RS equalityE) 1);
by (REPEAT (contr_tac 1 ORELSE eresolve_tac ([asm_rl,subsetCE]@prems) 1));
qed "equalityCE";

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. *)
val prems = Goal 
    "[| p:A;  !!z. z:A ==> p=z --> R |] ==> R";
by (rtac mp 1);
by (REPEAT (resolve_tac (refl::prems) 1));
qed "setup_induction";


section "The universal set -- UNIV";

Goalw [UNIV_def] "x : UNIV";
by (rtac CollectI 1);
by (rtac TrueI 1);
qed "UNIV_I";

Addsimps [UNIV_I];
AddIs    [UNIV_I];  (*unsafe makes it less likely to cause problems*)

Goal "A <= UNIV";
by (rtac subsetI 1);
by (rtac UNIV_I 1);
qed "subset_UNIV";

(** Eta-contracting these two rules (to remove P) causes them to be ignored
    because of their interaction with congruence rules. **)

Goalw [Ball_def] "Ball UNIV P = All P";
by (Simp_tac 1);
qed "ball_UNIV";

Goalw [Bex_def] "Bex UNIV P = Ex P";
by (Simp_tac 1);
qed "bex_UNIV";
Addsimps [ball_UNIV, bex_UNIV];


section "The empty set -- {}";

Goalw [empty_def] "(c : {}) = False";
by (Blast_tac 1) ;
qed "empty_iff";

Addsimps [empty_iff];

Goal "a:{} ==> P";
by (Full_simp_tac 1);
qed "emptyE";

AddSEs [emptyE];

Goal "{} <= A";
by (Blast_tac 1) ;
qed "empty_subsetI";

(*One effect is to delete the ASSUMPTION {} <= A*)
AddIffs [empty_subsetI];

val [prem]= Goal "[| !!y. y:A ==> False |] ==> A={}";
by (blast_tac (claset() addIs [prem RS FalseE]) 1) ;
qed "equals0I";

(*Use for reasoning about disjointness: A Int B = {} *)
Goal "A={} ==> a ~: A";
by (Blast_tac 1) ;
qed "equals0D";

AddDs [equals0D, sym RS equals0D];

Goalw [Ball_def] "Ball {} P = True";
by (Simp_tac 1);
qed "ball_empty";

Goalw [Bex_def] "Bex {} P = False";
by (Simp_tac 1);
qed "bex_empty";
Addsimps [ball_empty, bex_empty];

Goal "UNIV ~= {}";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "UNIV_not_empty";
AddIffs [UNIV_not_empty];



section "The Powerset operator -- Pow";

Goalw [Pow_def] "(A : Pow(B)) = (A <= B)";
by (Asm_simp_tac 1);
qed "Pow_iff";

AddIffs [Pow_iff]; 

Goalw [Pow_def] "A <= B ==> A : Pow(B)";
by (etac CollectI 1);
qed "PowI";

Goalw [Pow_def] "A : Pow(B)  ==>  A<=B";
by (etac CollectD 1);
qed "PowD";


val Pow_bottom = empty_subsetI RS PowI;        (* {}: Pow(B) *)
val Pow_top = subset_refl RS PowI;             (* A : Pow(A) *)


section "Set complement";

Goalw [Compl_def] "(c : -A) = (c~:A)";
by (Blast_tac 1);
qed "Compl_iff";

Addsimps [Compl_iff];

val prems = Goalw [Compl_def] "[| c:A ==> False |] ==> c : -A";
by (REPEAT (ares_tac (prems @ [CollectI,notI]) 1));
qed "ComplI";

(*This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the notional
  turnstile...*)
Goalw [Compl_def] "c : -A ==> c~:A";
by (etac CollectD 1);
qed "ComplD";

val ComplE = make_elim ComplD;

AddSIs [ComplI];
AddSEs [ComplE];


section "Binary union -- Un";

Goalw [Un_def] "(c : A Un B) = (c:A | c:B)";
by (Blast_tac 1);
qed "Un_iff";
Addsimps [Un_iff];

Goal "c:A ==> c : A Un B";
by (Asm_simp_tac 1);
qed "UnI1";

Goal "c:B ==> c : A Un B";
by (Asm_simp_tac 1);
qed "UnI2";

(*Classical introduction rule: no commitment to A vs B*)

val prems = Goal "(c~:B ==> c:A) ==> c : A Un B";
by (Simp_tac 1);
by (REPEAT (ares_tac (prems@[disjCI]) 1)) ;
qed "UnCI";

val major::prems = Goalw [Un_def]
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS CollectD RS disjE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "UnE";

AddSIs [UnCI];
AddSEs [UnE];


section "Binary intersection -- Int";

Goalw [Int_def] "(c : A Int B) = (c:A & c:B)";
by (Blast_tac 1);
qed "Int_iff";
Addsimps [Int_iff];

Goal "[| c:A;  c:B |] ==> c : A Int B";
by (Asm_simp_tac 1);
qed "IntI";

Goal "c : A Int B ==> c:A";
by (Asm_full_simp_tac 1);
qed "IntD1";

Goal "c : A Int B ==> c:B";
by (Asm_full_simp_tac 1);
qed "IntD2";

val [major,minor] = Goal
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P";
by (rtac minor 1);
by (rtac (major RS IntD1) 1);
by (rtac (major RS IntD2) 1);
qed "IntE";

AddSIs [IntI];
AddSEs [IntE];

section "Set difference";

Goalw [set_diff_def] "(c : A-B) = (c:A & c~:B)";
by (Blast_tac 1);
qed "Diff_iff";
Addsimps [Diff_iff];

Goal "[| c : A;  c ~: B |] ==> c : A - B";
by (Asm_simp_tac 1) ;
qed "DiffI";

Goal "c : A - B ==> c : A";
by (Asm_full_simp_tac 1) ;
qed "DiffD1";

Goal "[| c : A - B;  c : B |] ==> P";
by (Asm_full_simp_tac 1) ;
qed "DiffD2";

val prems = Goal "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P";
by (resolve_tac prems 1);
by (REPEAT (ares_tac (prems RL [DiffD1, DiffD2 RS notI]) 1)) ;
qed "DiffE";

AddSIs [DiffI];
AddSEs [DiffE];


section "Augmenting a set -- insert";

Goalw [insert_def] "a : insert b A = (a=b | a:A)";
by (Blast_tac 1);
qed "insert_iff";
Addsimps [insert_iff];

Goal "a : insert a B";
by (Simp_tac 1);
qed "insertI1";

Goal "!!a. a : B ==> a : insert b B";
by (Asm_simp_tac 1);
qed "insertI2";

val major::prems = Goalw [insert_def]
    "[| a : insert b A;  a=b ==> P;  a:A ==> P |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (eresolve_tac (prems @ [CollectE]) 1));
qed "insertE";

(*Classical introduction rule*)
val prems = Goal "(a~:B ==> a=b) ==> a: insert b B";
by (Simp_tac 1);
by (REPEAT (ares_tac (prems@[disjCI]) 1)) ;
qed "insertCI";

AddSIs [insertCI]; 
AddSEs [insertE];

Goal "A <= insert x B ==> A <= B & x ~: A | (? B'. A = insert x B' & B' <= B)";
by (case_tac "x:A" 1);
by  (Fast_tac 2);
br  disjI2 1;
by (res_inst_tac [("x","A-{x}")] exI 1);
by (Fast_tac 1);
qed "subset_insertD";

section "Singletons, using insert";

Goal "a : {a}";
by (rtac insertI1 1) ;
qed "singletonI";

Goal "b : {a} ==> b=a";
by (Blast_tac 1);
qed "singletonD";

bind_thm ("singletonE", make_elim singletonD);

Goal "(b : {a}) = (b=a)";
by (Blast_tac 1);
qed "singleton_iff";

Goal "{a}={b} ==> a=b";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "singleton_inject";

(*Redundant? But unlike insertCI, it proves the subgoal immediately!*)
AddSIs [singletonI];   
AddSDs [singleton_inject];
AddSEs [singletonE];

Goal "{b} = insert a A = (a = b & A <= {a})";
by (safe_tac (claset() addSEs [equalityE]));
by   (ALLGOALS Blast_tac);
qed "singleton_insert_inj_eq";

Goal "A <= {x} ==> A={} | A = {x}";
by (Fast_tac 1);
qed "subset_singletonD";

Goal "{x. x=a} = {a}";
by (Blast_tac 1);
qed "singleton_conv";
Addsimps [singleton_conv];

Goal "{x. a=x} = {a}";
by (Blast_tac 1);
qed "singleton_conv2";
Addsimps [singleton_conv2];


section "Unions of families -- UNION x:A. B(x) is Union(B``A)";

Goalw [UNION_def] "(b: (UN x:A. B(x))) = (EX x:A. b: B(x))";
by (Blast_tac 1);
qed "UN_iff";

Addsimps [UN_iff];

(*The order of the premises presupposes that A is rigid; b may be flexible*)
Goal "[| a:A;  b: B(a) |] ==> b: (UN x:A. B(x))";
by Auto_tac;
qed "UN_I";

val major::prems = Goalw [UNION_def]
    "[| b : (UN x:A. B(x));  !!x.[| x:A;  b: B(x) |] ==> R |] ==> R";
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
qed "UN_E";

AddIs  [UN_I];
AddSEs [UN_E];

val prems = Goalw [UNION_def]
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (UN x:A. C(x)) = (UN x:B. D(x))";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "UN_cong";


section "Intersections of families -- INTER x:A. B(x) is Inter(B``A)";

Goalw [INTER_def] "(b: (INT x:A. B(x))) = (ALL x:A. b: B(x))";
by Auto_tac;
qed "INT_iff";

Addsimps [INT_iff];

val prems = Goalw [INTER_def]
    "(!!x. x:A ==> b: B(x)) ==> b : (INT x:A. B(x))";
by (REPEAT (ares_tac ([CollectI,ballI] @ prems) 1));
qed "INT_I";

Goal "[| b : (INT x:A. B(x));  a:A |] ==> b: B(a)";
by Auto_tac;
qed "INT_D";

(*"Classical" elimination -- by the Excluded Middle on a:A *)
val major::prems = Goalw [INTER_def]
    "[| b : (INT x:A. B(x));  b: B(a) ==> R;  a~:A ==> R |] ==> R";
by (rtac (major RS CollectD RS ballE) 1);
by (REPEAT (eresolve_tac prems 1));
qed "INT_E";

AddSIs [INT_I];
AddEs  [INT_D, INT_E];

val prems = Goalw [INTER_def]
    "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==> \
\    (INT x:A. C(x)) = (INT x:B. D(x))";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "INT_cong";


section "Union";

Goalw [Union_def] "(A : Union(C)) = (EX X:C. A:X)";
by (Blast_tac 1);
qed "Union_iff";

Addsimps [Union_iff];

(*The order of the premises presupposes that C is rigid; A may be flexible*)
Goal "[| X:C;  A:X |] ==> A : Union(C)";
by Auto_tac;
qed "UnionI";

val major::prems = Goalw [Union_def]
    "[| A : Union(C);  !!X.[| A:X;  X:C |] ==> R |] ==> R";
by (rtac (major RS UN_E) 1);
by (REPEAT (ares_tac prems 1));
qed "UnionE";

AddIs  [UnionI];
AddSEs [UnionE];


section "Inter";

Goalw [Inter_def] "(A : Inter(C)) = (ALL X:C. A:X)";
by (Blast_tac 1);
qed "Inter_iff";

Addsimps [Inter_iff];

val prems = Goalw [Inter_def]
    "[| !!X. X:C ==> A:X |] ==> A : Inter(C)";
by (REPEAT (ares_tac ([INT_I] @ prems) 1));
qed "InterI";

(*A "destruct" rule -- every X in C contains A as an element, but
  A:X can hold when X:C does not!  This rule is analogous to "spec". *)
Goal "[| A : Inter(C);  X:C |] ==> A:X";
by Auto_tac;
qed "InterD";

(*"Classical" elimination rule -- does not require proving X:C *)
val major::prems = Goalw [Inter_def]
    "[| A : Inter(C);  X~:C ==> R;  A:X ==> R |] ==> R";
by (rtac (major RS INT_E) 1);
by (REPEAT (eresolve_tac prems 1));
qed "InterE";

AddSIs [InterI];
AddEs  [InterD, InterE];


(*** Image of a set under a function ***)

(*Frequently b does not have the syntactic form of f(x).*)
Goalw [image_def] "[| b=f(x);  x:A |] ==> b : f``A";
by (Blast_tac 1);
qed "image_eqI";
Addsimps [image_eqI];

bind_thm ("imageI", refl RS image_eqI);

(*The eta-expansion gives variable-name preservation.*)
val major::prems = Goalw [image_def]
    "[| b : (%x. f(x))``A;  !!x.[| b=f(x);  x:A |] ==> P |] ==> P"; 
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
qed "imageE";

AddIs  [image_eqI];
AddSEs [imageE]; 

Goal "f``(A Un B) = f``A Un f``B";
by (Blast_tac 1);
qed "image_Un";

Goal "(z : f``A) = (EX x:A. z = f x)";
by (Blast_tac 1);
qed "image_iff";

(*This rewrite rule would confuse users if made default.*)
Goal "(f``A <= B) = (ALL x:A. f(x): B)";
by (Blast_tac 1);
qed "image_subset_iff";

(*Replaces the three steps subsetI, imageE, hyp_subst_tac, but breaks too
  many existing proofs.*)
val prems = Goal "(!!x. x:A ==> f(x) : B) ==> f``A <= B";
by (blast_tac (claset() addIs prems) 1);
qed "image_subsetI";


(*** Range of a function -- just a translation for image! ***)

Goal "b=f(x) ==> b : range(f)";
by (EVERY1 [etac image_eqI, rtac UNIV_I]);
bind_thm ("range_eqI", UNIV_I RSN (2,image_eqI));

bind_thm ("rangeI", UNIV_I RS imageI);

val [major,minor] = Goal 
    "[| b : range(%x. f(x));  !!x. b=f(x) ==> P |] ==> P"; 
by (rtac (major RS imageE) 1);
by (etac minor 1);
qed "rangeE";


(*** Set reasoning tools ***)


(** Rewrite rules for boolean case-splitting: faster than 
	addsplits[split_if]
**)

bind_thm ("split_if_eq1", read_instantiate [("P", "%x. x = ?b")] split_if);
bind_thm ("split_if_eq2", read_instantiate [("P", "%x. ?a = x")] split_if);

(*Split ifs on either side of the membership relation.
	Not for Addsimps -- can cause goals to blow up!*)
bind_thm ("split_if_mem1", 
    read_instantiate_sg (Theory.sign_of Set.thy) [("P", "%x. x : ?b")] split_if);
bind_thm ("split_if_mem2", 
    read_instantiate_sg (Theory.sign_of Set.thy) [("P", "%x. ?a : x")] split_if);

val split_ifs = [if_bool_eq_conj, split_if_eq1, split_if_eq2,
		  split_if_mem1, split_if_mem2];


(*Each of these has ALREADY been added to simpset() above.*)
val mem_simps = [insert_iff, empty_iff, Un_iff, Int_iff, Compl_iff, Diff_iff, 
                 mem_Collect_eq, UN_iff, Union_iff, INT_iff, Inter_iff];

val mksimps_pairs = ("Ball",[bspec]) :: mksimps_pairs;

simpset_ref() := simpset() setmksimps (mksimps mksimps_pairs);

Addsimps[subset_UNIV, subset_refl];


(*** < ***)

Goalw [psubset_def] "!!A::'a set. [| A <= B; A ~= B |] ==> A<B";
by (Blast_tac 1);
qed "psubsetI";

Goalw [psubset_def] "A < insert x B ==> (x ~: A) & A<=B | x:A & A-{x}<B";
by Auto_tac;
qed "psubset_insertD";

bind_thm ("psubset_eq", psubset_def RS meta_eq_to_obj_eq);

bind_thm ("psubset_imp_subset", psubset_eq RS iffD1 RS conjunct1);

Goal"[| (A::'a set) < B; B <= C |] ==> A < C";
by (auto_tac (claset(), simpset() addsimps [psubset_eq]));
qed "psubset_subset_trans";

Goal"[| (A::'a set) <= B; B < C|] ==> A < C";
by (auto_tac (claset(), simpset() addsimps [psubset_eq]));
qed "subset_psubset_trans";
