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

bind_thm ("Pow_bottom", empty_subsetI RS PowI);         (* 0 : Pow(B) *)
bind_thm ("Pow_top", subset_refl RS PowI);              (* A : Pow(A) *)


(*** Unordered pairs - Upair ***)

Goalw [Upair_def] "c : Upair(a,b) <-> (c=a | c=b)";
by (Blast_tac 1) ;
qed "Upair_iff";

Addsimps [Upair_iff];

Goal "a : Upair(a,b)";
by (Simp_tac 1);
qed "UpairI1";

Goal "b : Upair(a,b)";
by (Simp_tac 1);
qed "UpairI2";

val major::prems= Goal
    "[| a : Upair(b,c);  a=b ==> P;  a=c ==> P |] ==> P";
by (rtac (major RS (Upair_iff RS iffD1 RS disjE)) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "UpairE";

AddSIs [UpairI1,UpairI2];
AddSEs [UpairE];

(*** Rules for binary union -- Un -- defined via Upair ***)

Goalw [Un_def]  "c : A Un B <-> (c:A | c:B)";
by (Blast_tac 1);
qed "Un_iff";

Addsimps [Un_iff];

Goal "c : A ==> c : A Un B";
by (Asm_simp_tac 1);
qed "UnI1";

Goal "c : B ==> c : A Un B";
by (Asm_simp_tac 1);
qed "UnI2";

val major::prems= Goal 
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P";
by (rtac (major RS (Un_iff RS iffD1 RS disjE)) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "UnE";

(*Stronger version of the rule above*)
val major::prems = Goal
    "[| c : A Un B;  c:A ==> P;  [| c:B;  c~:A |] ==> P |] ==> P";
by (rtac (major RS UnE) 1);
by (eresolve_tac prems 1);
by (rtac classical 1);
by (eresolve_tac prems 1);
by (swap_res_tac prems 1);
by (etac notnotD 1);
qed "UnE'";

(*Classical introduction rule: no commitment to A vs B*)
val prems = Goal "(c ~: B ==> c : A) ==> c : A Un B";
by (Simp_tac 1);
by (blast_tac (claset() addSIs prems) 1);
qed "UnCI";

AddSIs [UnCI];
AddSEs [UnE];


(*** Rules for small intersection -- Int -- defined via Upair ***)

Goalw [Int_def]  "c : A Int B <-> (c:A & c:B)";
by (Blast_tac 1);
qed "Int_iff";

Addsimps [Int_iff];

Goal "[| c : A;  c : B |] ==> c : A Int B";
by (Asm_simp_tac 1);
qed "IntI";

Goal "c : A Int B ==> c : A";
by (Asm_full_simp_tac 1);
qed "IntD1";

Goal "c : A Int B ==> c : B";
by (Asm_full_simp_tac 1);
qed "IntD2";

val prems = Goal "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P";
by (resolve_tac prems 1);
by (REPEAT (resolve_tac (prems RL [IntD1,IntD2]) 1)) ;
qed "IntE";

AddSIs [IntI];
AddSEs [IntE];

(*** Rules for set difference -- defined via Upair ***)

Goalw [Diff_def]  "c : A-B <-> (c:A & c~:B)";
by (Blast_tac 1);
qed "Diff_iff";

Addsimps [Diff_iff];

Goal "[| c : A;  c ~: B |] ==> c : A - B";
by (Asm_simp_tac 1);
qed "DiffI";

Goal "c : A - B ==> c : A";
by (Asm_full_simp_tac 1);
qed "DiffD1";

Goal "c : A - B ==> c ~: B";
by (Asm_full_simp_tac 1);
qed "DiffD2";

val prems = Goal "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P";
by (resolve_tac prems 1);
by (REPEAT (ares_tac (prems RL [DiffD1, DiffD2]) 1)) ;
qed "DiffE";

AddSIs [DiffI];
AddSEs [DiffE];

(*** Rules for cons -- defined via Un and Upair ***)

Goalw [cons_def]  "a : cons(b,A) <-> (a=b | a:A)";
by (Blast_tac 1);
qed "cons_iff";

Addsimps [cons_iff];

Goal "a : cons(a,B)";
by (Simp_tac 1);
qed "consI1";

Addsimps [consI1];
AddTCs   [consI1];   (*risky as a typechecking rule, but solves otherwise
		       unconstrained goals of the form  x : ?A*)

Goal "a : B ==> a : cons(b,B)";
by (Asm_simp_tac 1);
qed "consI2";

val major::prems= Goal
    "[| a : cons(b,A);  a=b ==> P;  a:A ==> P |] ==> P";
by (rtac (major RS (cons_iff RS iffD1 RS disjE)) 1);
by (REPEAT (eresolve_tac (prems @ [UpairE]) 1)) ;
qed "consE";

(*Stronger version of the rule above*)
val major::prems = Goal
    "[| a : cons(b,A);  a=b ==> P;  [| a:A;  a~=b |] ==> P |] ==> P";
by (rtac (major RS consE) 1);
by (eresolve_tac prems 1);
by (rtac classical 1);
by (eresolve_tac prems 1);
by (swap_res_tac prems 1);
by (etac notnotD 1);
qed "consE'";

(*Classical introduction rule*)
val prems = Goal "(a~:B ==> a=b) ==> a: cons(b,B)";
by (Simp_tac 1);
by (blast_tac (claset() addSIs prems) 1);
qed "consCI";

AddSIs [consCI];
AddSEs [consE];

Goal "cons(a,B) ~= 0";
by (blast_tac (claset() addEs [equalityE]) 1) ;
qed "cons_not_0";

bind_thm ("cons_neq_0", cons_not_0 RS notE);

Addsimps [cons_not_0, cons_not_0 RS not_sym];


(*** Singletons - using cons ***)

Goal "a : {b} <-> a=b";
by (Simp_tac 1);
qed "singleton_iff";

Goal "a : {a}";
by (rtac consI1 1) ;
qed "singletonI";

bind_thm ("singletonE", make_elim (singleton_iff RS iffD1));

AddSIs [singletonI];
AddSEs [singletonE];

(*** Rules for Descriptions ***)

val [pa,eq] = Goalw [the_def] 
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a";
by (fast_tac (claset() addSIs [pa] addEs [eq RS subst]) 1) ;
qed "the_equality";

AddIs [the_equality];

(* Only use this if you already know EX!x. P(x) *)
Goal "[| EX! x. P(x);  P(a) |] ==> (THE x. P(x)) = a";
by (Blast_tac 1);
qed "the_equality2";

Goal "EX! x. P(x) ==> P(THE x. P(x))";
by (etac ex1E 1);
by (stac the_equality 1);
by (REPEAT (Blast_tac 1));
qed "theI";

(*the_cong is no longer necessary: if (ALL y.P(y)<->Q(y)) then 
  (THE x.P(x))  rewrites to  (THE x. Q(x))  *)

(*If it's "undefined", it's zero!*)
Goalw  [the_def] "~ (EX! x. P(x)) ==> (THE x. P(x))=0";
by (blast_tac (claset() addSEs [ReplaceE]) 1);
qed "the_0";

(*Easier to apply than theI: conclusion has only one occurrence of P*)
val prems = 
Goal "[| ~ Q(0) ==> EX! x. P(x);  !!x. P(x) ==> Q(x) |] ==> Q(THE x. P(x))";
by (rtac classical 1);
by (resolve_tac prems 1);
by (rtac theI 1);
by (rtac classical 1);
by (resolve_tac prems 1);
by (etac (the_0 RS subst) 1);
by (assume_tac 1);
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

(*Prevents simplification of x and y: faster and allows the execution
  of functional programs. NOW THE DEFAULT.*)
Goal "P<->Q ==> (if P then x else y) = (if Q then x else y)";
by (Asm_simp_tac 1);
qed "if_weak_cong";

(*Not needed for rewriting, since P would rewrite to True anyway*)
Goalw [if_def] "P ==> (if P then a else b) = a";
by (Blast_tac 1);
qed "if_P";

(*Not needed for rewriting, since P would rewrite to False anyway*)
Goalw [if_def] "~P ==> (if P then a else b) = b";
by (Blast_tac 1);
qed "if_not_P";

Addsimps [if_true, if_false];

Goal "P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))";
by (case_tac "Q" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1) ;
qed "split_if";

(** Rewrite rules for boolean case-splitting: faster than 
	addsplits[split_if]
**)

bind_thm ("split_if_eq1", inst "P" "%x. x = ?b" split_if);
bind_thm ("split_if_eq2", inst "P" "%x. ?a = x" split_if);

bind_thm ("split_if_mem1", inst "P" "%x. x : ?b" split_if);
bind_thm ("split_if_mem2", inst "P" "%x. ?a : x" split_if);

bind_thms ("split_ifs", [split_if_eq1, split_if_eq2, split_if_mem1, split_if_mem2]);

(*Logically equivalent to split_if_mem2*)
Goal "a: (if P then x else y) <-> P & a:x | ~P & a:y";
by (simp_tac (simpset() addsplits [split_if]) 1) ;
qed "if_iff";

val prems = Goal
    "[| P ==> a: A;  ~P ==> b: A |] ==> (if P then a else b): A";
by (simp_tac (simpset() addsimps prems addsplits [split_if]) 1) ;
qed "if_type";

AddTCs [if_type];

(*** Foundation lemmas ***)

(*was called mem_anti_sym*)
val prems = Goal "[| a:b;  ~P ==> b:a |] ==> P";
by (rtac classical 1);
by (res_inst_tac [("A1","{a,b}")] (foundation RS disjE) 1);
by (REPEAT (blast_tac (claset() addIs prems addSEs [equalityE]) 1));
qed "mem_asym";

(*was called mem_anti_refl*)
Goal "a:a ==> P";
by (blast_tac (claset() addIs [mem_asym]) 1);
qed "mem_irrefl";

(*mem_irrefl should NOT be added to default databases:
      it would be tried on most goals, making proofs slower!*)

Goal "a ~: a";
by (rtac notI 1);
by (etac mem_irrefl 1);
qed "mem_not_refl";

(*Good for proving inequalities by rewriting*)
Goal "a:A ==> a ~= A";
by (blast_tac (claset() addSEs [mem_irrefl]) 1);
qed "mem_imp_not_eq";

(*** Rules for succ ***)

Goalw [succ_def]  "i : succ(j) <-> i=j | i:j";
by (Blast_tac 1);
qed "succ_iff";

Goalw [succ_def]  "i : succ(i)";
by (rtac consI1 1) ;
qed "succI1";

Addsimps [succI1];

Goalw [succ_def] "i : j ==> i : succ(j)";
by (etac consI2 1) ;
qed "succI2";

val major::prems= Goalw [succ_def] 
    "[| i : succ(j);  i=j ==> P;  i:j ==> P |] ==> P";
by (rtac (major RS consE) 1);
by (REPEAT (eresolve_tac prems 1)) ;
qed "succE";

(*Classical introduction rule*)
val [prem]= Goal "(i~:j ==> i=j) ==> i: succ(j)";
by (rtac (disjCI RS (succ_iff RS iffD2)) 1);
by (etac prem 1) ;
qed "succCI";

AddSIs [succCI];
AddSEs [succE];

Goal "succ(n) ~= 0";
by (blast_tac (claset() addSEs [equalityE]) 1) ;
qed "succ_not_0";

bind_thm ("succ_neq_0", succ_not_0 RS notE);

Addsimps [succ_not_0, succ_not_0 RS not_sym];
AddSEs [succ_neq_0, sym RS succ_neq_0];


(* succ(c) <= B ==> c : B *)
bind_thm ("succ_subsetD", succI1 RSN (2,subsetD));

(* succ(b) ~= b *)
bind_thm ("succ_neq_self", succI1 RS mem_imp_not_eq RS not_sym);

Goal "succ(m) = succ(n) <-> m=n";
by (blast_tac (claset() addEs [mem_asym] addSEs [equalityE]) 1) ;
qed "succ_inject_iff";

bind_thm ("succ_inject", succ_inject_iff RS iffD1);

Addsimps [succ_inject_iff];
AddSDs [succ_inject];

(*Not needed now that cons is available.  Deletion reduces the search space.*)
Delrules [UpairI1,UpairI2,UpairE];
