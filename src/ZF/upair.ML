(*  Title:      ZF/upair
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

UNORDERED pairs in Zermelo-Fraenkel Set Theory 

Observe the order of dependence:
    Upair is defined in terms of Replace
    Un is defined in terms of Upair and Union (similarly for Int)
    cons is defined in terms of Upair and Un
    Ordered pairs and descriptions are defined using cons ("set notation")
*)

(*** Lemmas about power sets  ***)

val Pow_bottom = empty_subsetI RS PowI;         (* 0 : Pow(B) *)
val Pow_top = subset_refl RS PowI;              (* A : Pow(A) *)


(*** Unordered pairs - Upair ***)

qed_goalw "Upair_iff" thy [Upair_def]
    "c : Upair(a,b) <-> (c=a | c=b)"
 (fn _ => [ (Blast_tac 1) ]);

Addsimps [Upair_iff];

qed_goal "UpairI1" thy "a : Upair(a,b)"
 (fn _ => [ Simp_tac 1 ]);

qed_goal "UpairI2" thy "b : Upair(a,b)"
 (fn _ => [ Simp_tac 1 ]);

qed_goal "UpairE" thy
    "[| a : Upair(b,c);  a=b ==> P;  a=c ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS (Upair_iff RS iffD1 RS disjE)) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

AddSIs [UpairI1,UpairI2];
AddSEs [UpairE];

(*** Rules for binary union -- Un -- defined via Upair ***)

qed_goalw "Un_iff" thy [Un_def] "c : A Un B <-> (c:A | c:B)"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [Un_iff];

qed_goal "UnI1" thy "!!c. c : A ==> c : A Un B"
 (fn _ => [ Asm_simp_tac 1 ]);

qed_goal "UnI2" thy "!!c. c : B ==> c : A Un B"
 (fn _ => [ Asm_simp_tac 1 ]);

qed_goal "UnE" thy 
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS (Un_iff RS iffD1 RS disjE)) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*Stronger version of the rule above*)
qed_goal "UnE'" thy
    "[| c : A Un B;  c:A ==> P;  [| c:B;  c~:A |] ==> P |] ==> P"
 (fn major::prems =>
  [(rtac (major RS UnE) 1),
   (eresolve_tac prems 1),
   (rtac classical 1),
   (eresolve_tac prems 1),
   (swap_res_tac prems 1),
   (etac notnotD 1)]);

(*Classical introduction rule: no commitment to A vs B*)
qed_goal "UnCI" thy "(c ~: B ==> c : A) ==> c : A Un B"
 (fn prems=>
  [ Simp_tac 1, blast_tac (claset() addSIs prems) 1 ]);

AddSIs [UnCI];
AddSEs [UnE];


(*** Rules for small intersection -- Int -- defined via Upair ***)

qed_goalw "Int_iff" thy [Int_def] "c : A Int B <-> (c:A & c:B)"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [Int_iff];

qed_goal "IntI" thy "!!c. [| c : A;  c : B |] ==> c : A Int B"
 (fn _ => [ Asm_simp_tac 1 ]);

qed_goal "IntD1" thy "!!c. c : A Int B ==> c : A"
 (fn _ => [ Asm_full_simp_tac 1 ]);

qed_goal "IntD2" thy "!!c. c : A Int B ==> c : B"
 (fn _ => [ Asm_full_simp_tac 1 ]);

qed_goal "IntE" thy
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (resolve_tac (prems RL [IntD1,IntD2]) 1)) ]);

AddSIs [IntI];
AddSEs [IntE];

(*** Rules for set difference -- defined via Upair ***)

qed_goalw "Diff_iff" thy [Diff_def] "c : A-B <-> (c:A & c~:B)"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [Diff_iff];

qed_goal "DiffI" thy "!!c. [| c : A;  c ~: B |] ==> c : A - B"
 (fn _ => [ Asm_simp_tac 1 ]);

qed_goal "DiffD1" thy "!!c. c : A - B ==> c : A"
 (fn _ => [ Asm_full_simp_tac 1 ]);

qed_goal "DiffD2" thy "!!c. c : A - B ==> c ~: B"
 (fn _ => [ Asm_full_simp_tac 1 ]);

qed_goal "DiffE" thy
    "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (ares_tac (prems RL [DiffD1, DiffD2]) 1)) ]);

AddSIs [DiffI];
AddSEs [DiffE];

(*** Rules for cons -- defined via Un and Upair ***)

qed_goalw "cons_iff" thy [cons_def] "a : cons(b,A) <-> (a=b | a:A)"
 (fn _ => [ Blast_tac 1 ]);

Addsimps [cons_iff];

qed_goal "consI1" thy "a : cons(a,B)"
 (fn _ => [ Simp_tac 1 ]);

Addsimps [consI1];
AddTCs   [consI1];   (*risky as a typechecking rule, but solves otherwise
		       unconstrained goals of the form  x : ?A*)

qed_goal "consI2" thy "!!B. a : B ==> a : cons(b,B)"
 (fn _ => [ Asm_simp_tac 1 ]);

qed_goal "consE" thy
    "[| a : cons(b,A);  a=b ==> P;  a:A ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS (cons_iff RS iffD1 RS disjE)) 1),
    (REPEAT (eresolve_tac (prems @ [UpairE]) 1)) ]);

(*Stronger version of the rule above*)
qed_goal "consE'" thy
    "[| a : cons(b,A);  a=b ==> P;  [| a:A;  a~=b |] ==> P |] ==> P"
 (fn major::prems =>
  [(rtac (major RS consE) 1),
   (eresolve_tac prems 1),
   (rtac classical 1),
   (eresolve_tac prems 1),
   (swap_res_tac prems 1),
   (etac notnotD 1)]);

(*Classical introduction rule*)
qed_goal "consCI" thy "(a~:B ==> a=b) ==> a: cons(b,B)"
 (fn prems=>
  [ Simp_tac 1, blast_tac (claset() addSIs prems) 1 ]);

AddSIs [consCI];
AddSEs [consE];

qed_goal "cons_not_0" thy "cons(a,B) ~= 0"
 (fn _ => [ (blast_tac (claset() addEs [equalityE]) 1) ]);

bind_thm ("cons_neq_0", cons_not_0 RS notE);

Addsimps [cons_not_0, cons_not_0 RS not_sym];


(*** Singletons - using cons ***)

qed_goal "singleton_iff" thy "a : {b} <-> a=b"
 (fn _ => [ Simp_tac 1 ]);

qed_goal "singletonI" thy "a : {a}"
 (fn _=> [ (rtac consI1 1) ]);

bind_thm ("singletonE", make_elim (singleton_iff RS iffD1));

AddSIs [singletonI];
AddSEs [singletonE];

(*** Rules for Descriptions ***)

qed_goalw "the_equality" thy [the_def]
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a"
 (fn [pa,eq] =>
  [ (fast_tac (claset() addSIs [pa] addEs [eq RS subst]) 1) ]);

AddIs [the_equality];

(* Only use this if you already know EX!x. P(x) *)
qed_goal "the_equality2" thy
    "!!P. [| EX! x. P(x);  P(a) |] ==> (THE x. P(x)) = a"
 (fn _ => [ (Blast_tac 1) ]);

qed_goal "theI" thy "EX! x. P(x) ==> P(THE x. P(x))"
 (fn [major]=>
  [ (rtac (major RS ex1E) 1),
    (resolve_tac [major RS the_equality2 RS ssubst] 1),
    (REPEAT (assume_tac 1)) ]);

(*the_cong is no longer necessary: if (ALL y.P(y)<->Q(y)) then 
  (THE x.P(x))  rewrites to  (THE x. Q(x))  *)

(*If it's "undefined", it's zero!*)
qed_goalw "the_0" thy [the_def]
    "!!P. ~ (EX! x. P(x)) ==> (THE x. P(x))=0"
 (fn _ => [ (blast_tac (claset() addSEs [ReplaceE]) 1) ]);


(*Easier to apply than theI: conclusion has only one occurrence of P*)
val prems = 
Goal "[| ~ Q(0) ==> EX! x. P(x);  !!x. P(x) ==> Q(x) |] ==> Q(THE x. P(x))";
by (rtac classical 1);
by (resolve_tac prems 1);
by (rtac theI 1);
by (rtac classical 1);
by (resolve_tac prems 1);
be (the_0 RS subst) 1;
ba 1;
qed "theI2";

(*** if -- a conditional expression for formulae ***)

Goalw [if_def] "(if True then a else b) = a";
by (Blast_tac 1);
qed "if_true";

Goalw [if_def] "(if False then a else b) = b";
by (Blast_tac 1);
qed "if_false";

(*Never use with case splitting, or if P is known to be true or false*)
val prems = Goalw [if_def]
    "[| P<->Q;  Q ==> a=c;  ~Q ==> b=d |] \
\    ==> (if P then a else b) = (if Q then c else d)";
by (simp_tac (simpset() addsimps prems addcongs [conj_cong]) 1);
qed "if_cong";

(*Not needed for rewriting, since P would rewrite to True anyway*)
Goalw [if_def] "P ==> (if P then a else b) = a";
by (Blast_tac 1);
qed "if_P";

(*Not needed for rewriting, since P would rewrite to False anyway*)
Goalw [if_def] "~P ==> (if P then a else b) = b";
by (Blast_tac 1);
qed "if_not_P";

Addsimps [if_true, if_false];

qed_goal "split_if" thy
    "P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))"
 (fn _=> [ (case_tac "Q" 1),
           (Asm_simp_tac 1),
           (Asm_simp_tac 1) ]);

(** Rewrite rules for boolean case-splitting: faster than 
	addsplits[split_if]
**)

bind_thm ("split_if_eq1", read_instantiate [("P", "%x. x = ?b")] split_if);
bind_thm ("split_if_eq2", read_instantiate [("P", "%x. ?a = x")] split_if);

bind_thm ("split_if_mem1", read_instantiate [("P", "%x. x : ?b")] split_if);
bind_thm ("split_if_mem2", read_instantiate [("P", "%x. ?a : x")] split_if);

val split_ifs = [split_if_eq1, split_if_eq2,
		 split_if_mem1, split_if_mem2];

(*Logically equivalent to split_if_mem2*)
qed_goal "if_iff" thy "a: (if P then x else y) <-> P & a:x | ~P & a:y"
 (fn _=> [ (simp_tac (simpset() addsplits [split_if]) 1) ]);

qed_goal "if_type" thy
    "[| P ==> a: A;  ~P ==> b: A |] ==> (if P then a else b): A"
 (fn prems=> [ (simp_tac 
                (simpset() addsimps prems addsplits [split_if]) 1) ]);
AddTCs [if_type];

(*** Foundation lemmas ***)

(*was called mem_anti_sym*)
qed_goal "mem_asym" thy "[| a:b;  ~P ==> b:a |] ==> P"
 (fn prems=>
  [ (rtac classical 1),
    (res_inst_tac [("A1","{a,b}")] (foundation RS disjE) 1),
    REPEAT (blast_tac (claset() addIs prems addSEs [equalityE]) 1) ]);

(*was called mem_anti_refl*)
qed_goal "mem_irrefl" thy "a:a ==> P"
 (fn [major]=> [ (rtac ([major,major] MRS mem_asym) 1) ]);

(*mem_irrefl should NOT be added to default databases:
      it would be tried on most goals, making proofs slower!*)

qed_goal "mem_not_refl" thy "a ~: a"
 (K [ (rtac notI 1), (etac mem_irrefl 1) ]);

(*Good for proving inequalities by rewriting*)
qed_goal "mem_imp_not_eq" thy "!!a A. a:A ==> a ~= A"
 (fn _=> [ blast_tac (claset() addSEs [mem_irrefl]) 1 ]);

(*** Rules for succ ***)

qed_goalw "succ_iff" thy [succ_def] "i : succ(j) <-> i=j | i:j"
 (fn _ => [ Blast_tac 1 ]);

qed_goalw "succI1" thy [succ_def] "i : succ(i)"
 (fn _=> [ (rtac consI1 1) ]);

Addsimps [succI1];

qed_goalw "succI2" thy [succ_def]
    "i : j ==> i : succ(j)"
 (fn [prem]=> [ (rtac (prem RS consI2) 1) ]);

qed_goalw "succE" thy [succ_def]
    "[| i : succ(j);  i=j ==> P;  i:j ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS consE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*Classical introduction rule*)
qed_goal "succCI" thy "(i~:j ==> i=j) ==> i: succ(j)"
 (fn [prem]=>
  [ (rtac (disjCI RS (succ_iff RS iffD2)) 1),
    (etac prem 1) ]);

AddSIs [succCI];
AddSEs [succE];

qed_goal "succ_not_0" thy "succ(n) ~= 0"
 (fn _=> [ (blast_tac (claset() addSEs [equalityE]) 1) ]);

bind_thm ("succ_neq_0", succ_not_0 RS notE);

Addsimps [succ_not_0, succ_not_0 RS not_sym];
AddSEs [succ_neq_0, sym RS succ_neq_0];


(* succ(c) <= B ==> c : B *)
val succ_subsetD = succI1 RSN (2,subsetD);

(* succ(b) ~= b *)
bind_thm ("succ_neq_self", succI1 RS mem_imp_not_eq RS not_sym);


qed_goal "succ_inject_iff" thy "succ(m) = succ(n) <-> m=n"
 (fn _=> [ (blast_tac (claset() addEs [mem_asym] addSEs [equalityE]) 1) ]);

bind_thm ("succ_inject", succ_inject_iff RS iffD1);

Addsimps [succ_inject_iff];
AddSDs [succ_inject];

(*Not needed now that cons is available.  Deletion reduces the search space.*)
Delrules [UpairI1,UpairI2,UpairE];

use"simpdata.ML";
