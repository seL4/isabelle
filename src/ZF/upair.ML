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
val Pow_neq_0 = Pow_top RSN (2,equals0D);       (* Pow(a)=0 ==> P *) 


(*** Unordered pairs - Upair ***)

qed_goalw "pairing" ZF.thy [Upair_def]
    "c : Upair(a,b) <-> (c=a | c=b)"
 (fn _ => [ (fast_tac (lemmas_cs addEs [Pow_neq_0, sym RS Pow_neq_0]) 1) ]);

qed_goal "UpairI1" ZF.thy "a : Upair(a,b)"
 (fn _ => [ (rtac (refl RS disjI1 RS (pairing RS iffD2)) 1) ]);

qed_goal "UpairI2" ZF.thy "b : Upair(a,b)"
 (fn _ => [ (rtac (refl RS disjI2 RS (pairing RS iffD2)) 1) ]);

qed_goal "UpairE" ZF.thy
    "[| a : Upair(b,c);  a=b ==> P;  a=c ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS (pairing RS iffD1 RS disjE)) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

(*** Rules for binary union -- Un -- defined via Upair ***)

qed_goalw "UnI1" ZF.thy [Un_def] "c : A ==> c : A Un B"
 (fn [prem]=> [ (rtac (prem RS (UpairI1 RS UnionI)) 1) ]);

qed_goalw "UnI2" ZF.thy [Un_def] "c : B ==> c : A Un B"
 (fn [prem]=> [ (rtac (prem RS (UpairI2 RS UnionI)) 1) ]);

qed_goalw "UnE" ZF.thy [Un_def] 
    "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnionE) 1),
    (etac UpairE 1),
    (REPEAT (EVERY1 [resolve_tac prems, etac subst, assume_tac])) ]);

(*Stronger version of the rule above*)
qed_goal "UnE'" ZF.thy
    "[| c : A Un B;  c:A ==> P;  [| c:B;  c~:A |] ==> P |] ==> P"
 (fn major::prems =>
  [(rtac (major RS UnE) 1),
   (eresolve_tac prems 1),
   (rtac classical 1),
   (eresolve_tac prems 1),
   (swap_res_tac prems 1),
   (etac notnotD 1)]);

qed_goal "Un_iff" ZF.thy "c : A Un B <-> (c:A | c:B)"
 (fn _ => [ (fast_tac (lemmas_cs addIs [UnI1,UnI2] addSEs [UnE]) 1) ]);

(*Classical introduction rule: no commitment to A vs B*)
qed_goal "UnCI" ZF.thy "(c ~: B ==> c : A) ==> c : A Un B"
 (fn [prem]=>
  [ (rtac (disjCI RS (Un_iff RS iffD2)) 1),
    (etac prem 1) ]);


(*** Rules for small intersection -- Int -- defined via Upair ***)

qed_goalw "IntI" ZF.thy [Int_def]
    "[| c : A;  c : B |] ==> c : A Int B"
 (fn prems=>
  [ (REPEAT (resolve_tac (prems @ [UpairI1,InterI]) 1
     ORELSE eresolve_tac [UpairE, ssubst] 1)) ]);

qed_goalw "IntD1" ZF.thy [Int_def] "c : A Int B ==> c : A"
 (fn [major]=>
  [ (rtac (UpairI1 RS (major RS InterD)) 1) ]);

qed_goalw "IntD2" ZF.thy [Int_def] "c : A Int B ==> c : B"
 (fn [major]=>
  [ (rtac (UpairI2 RS (major RS InterD)) 1) ]);

qed_goal "IntE" ZF.thy
    "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (resolve_tac (prems RL [IntD1,IntD2]) 1)) ]);

qed_goal "Int_iff" ZF.thy "c : A Int B <-> (c:A & c:B)"
 (fn _ => [ (fast_tac (lemmas_cs addSIs [IntI] addSEs [IntE]) 1) ]);


(*** Rules for set difference -- defined via Upair ***)

qed_goalw "DiffI" ZF.thy [Diff_def]
    "[| c : A;  c ~: B |] ==> c : A - B"
 (fn prems=> [ (REPEAT (resolve_tac (prems @ [CollectI]) 1)) ]);

qed_goalw "DiffD1" ZF.thy [Diff_def]
    "c : A - B ==> c : A"
 (fn [major]=> [ (rtac (major RS CollectD1) 1) ]);

qed_goalw "DiffD2" ZF.thy [Diff_def]
    "c : A - B ==> c ~: B"
 (fn [major]=> [ (rtac (major RS CollectD2) 1) ]);

qed_goal "DiffE" ZF.thy
    "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P"
 (fn prems=>
  [ (resolve_tac prems 1),
    (REPEAT (ares_tac (prems RL [DiffD1, DiffD2]) 1)) ]);

qed_goal "Diff_iff" ZF.thy "c : A-B <-> (c:A & c~:B)"
 (fn _ => [ (fast_tac (lemmas_cs addSIs [DiffI] addSEs [DiffE]) 1) ]);

(*** Rules for cons -- defined via Un and Upair ***)

qed_goalw "consI1" ZF.thy [cons_def] "a : cons(a,B)"
 (fn _ => [ (rtac (UpairI1 RS UnI1) 1) ]);

qed_goalw "consI2" ZF.thy [cons_def] "a : B ==> a : cons(b,B)"
 (fn [prem]=> [ (rtac (prem RS UnI2) 1) ]);

qed_goalw "consE" ZF.thy [cons_def]
    "[| a : cons(b,A);  a=b ==> P;  a:A ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS UnE) 1),
    (REPEAT (eresolve_tac (prems @ [UpairE]) 1)) ]);

(*Stronger version of the rule above*)
qed_goal "consE'" ZF.thy
    "[| a : cons(b,A);  a=b ==> P;  [| a:A;  a~=b |] ==> P |] ==> P"
 (fn major::prems =>
  [(rtac (major RS consE) 1),
   (eresolve_tac prems 1),
   (rtac classical 1),
   (eresolve_tac prems 1),
   (swap_res_tac prems 1),
   (etac notnotD 1)]);

qed_goal "cons_iff" ZF.thy "a : cons(b,A) <-> (a=b | a:A)"
 (fn _ => [ (fast_tac (lemmas_cs addIs [consI1,consI2] addSEs [consE]) 1) ]);

(*Classical introduction rule*)
qed_goal "consCI" ZF.thy "(a~:B ==> a=b) ==> a: cons(b,B)"
 (fn [prem]=>
  [ (rtac (disjCI RS (cons_iff RS iffD2)) 1),
    (etac prem 1) ]);

qed_goal "cons_neq_0" ZF.thy "cons(a,B)=0 ==> P"
 (fn [major]=>
  [ (rtac (major RS equalityD1 RS subsetD RS emptyE) 1),
    (rtac consI1 1) ]);

(*Useful for rewriting*)
qed_goal "cons_not_0" ZF.thy "cons(a,B) ~= 0"
 (fn _=> [ (rtac notI 1), (etac cons_neq_0 1) ]);

(*** Singletons - using cons ***)

qed_goal "singletonI" ZF.thy "a : {a}"
 (fn _=> [ (rtac consI1 1) ]);

qed_goal "singletonE" ZF.thy "[| a: {b};  a=b ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS consE) 1),
    (REPEAT (eresolve_tac (prems @ [emptyE]) 1)) ]);

qed_goal "singleton_iff" ZF.thy "a : {b} <-> a=b"
 (fn _ => [ (fast_tac (lemmas_cs addIs [consI1] addSEs [consE]) 1) ]);


(*** Rules for Descriptions ***)

qed_goalw "the_equality" ZF.thy [the_def]
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a"
 (fn [pa,eq] =>
  [ (fast_tac (lemmas_cs addSIs [singletonI,pa] addIs [equalityI]
                         addEs [eq RS subst]) 1) ]);

(* Only use this if you already know EX!x. P(x) *)
qed_goal "the_equality2" ZF.thy
    "!!P. [| EX! x. P(x);  P(a) |] ==> (THE x. P(x)) = a"
 (fn _ =>
  [ (deepen_tac (lemmas_cs addSIs [the_equality]) 1 1) ]);

qed_goal "theI" ZF.thy "EX! x. P(x) ==> P(THE x. P(x))"
 (fn [major]=>
  [ (rtac (major RS ex1E) 1),
    (resolve_tac [major RS the_equality2 RS ssubst] 1),
    (REPEAT (assume_tac 1)) ]);

(*Easier to apply than theI: conclusion has only one occurrence of P*)
qed_goal "theI2" ZF.thy
    "[| EX! x. P(x);  !!x. P(x) ==> Q(x) |] ==> Q(THE x.P(x))"
 (fn prems => [ resolve_tac prems 1, 
                rtac theI 1, 
                resolve_tac prems 1 ]);

(*the_cong is no longer necessary: if (ALL y.P(y)<->Q(y)) then 
  (THE x.P(x))  rewrites to  (THE x. Q(x))  *)

(*If it's "undefined", it's zero!*)
qed_goalw "the_0" ZF.thy [the_def]
    "!!P. ~ (EX! x. P(x)) ==> (THE x. P(x))=0"
 (fn _ =>
  [ (fast_tac (lemmas_cs addIs [equalityI] addSEs [ReplaceE]) 1) ]);


(*** if -- a conditional expression for formulae ***)

goalw ZF.thy [if_def] "if(True,a,b) = a";
by (fast_tac (lemmas_cs addIs [the_equality]) 1);
qed "if_true";

goalw ZF.thy [if_def] "if(False,a,b) = b";
by (fast_tac (lemmas_cs addIs [the_equality]) 1);
qed "if_false";

(*Never use with case splitting, or if P is known to be true or false*)
val prems = goalw ZF.thy [if_def]
    "[| P<->Q;  Q ==> a=c;  ~Q ==> b=d |] ==> if(P,a,b) = if(Q,c,d)";
by (simp_tac (FOL_ss addsimps prems addcongs [conj_cong]) 1);
qed "if_cong";

(*Not needed for rewriting, since P would rewrite to True anyway*)
goalw ZF.thy [if_def] "!!P. P ==> if(P,a,b) = a";
by (fast_tac (lemmas_cs addSIs [the_equality]) 1);
qed "if_P";

(*Not needed for rewriting, since P would rewrite to False anyway*)
goalw ZF.thy [if_def] "!!P. ~P ==> if(P,a,b) = b";
by (fast_tac (lemmas_cs addSIs [the_equality]) 1);
qed "if_not_P";

val if_ss = FOL_ss addsimps  [if_true,if_false];

qed_goal "expand_if" ZF.thy
    "P(if(Q,x,y)) <-> ((Q --> P(x)) & (~Q --> P(y)))"
 (fn _=> [ (excluded_middle_tac "Q" 1),
           (asm_simp_tac if_ss 1),
           (asm_simp_tac if_ss 1) ]);

qed_goal "if_iff" ZF.thy "a: if(P,x,y) <-> P & a:x | ~P & a:y"
 (fn _=> [ (simp_tac (if_ss setloop split_tac [expand_if]) 1) ]);

qed_goal "if_type" ZF.thy
    "[| P ==> a: A;  ~P ==> b: A |] ==> if(P,a,b): A"
 (fn prems=> [ (simp_tac 
                (if_ss addsimps prems setloop split_tac [expand_if]) 1) ]);


(*** Foundation lemmas ***)

(*was called mem_anti_sym*)
qed_goal "mem_asym" ZF.thy "!!P. [| a:b;  b:a |] ==> P"
 (fn _=>
  [ (res_inst_tac [("A1","{a,b}")] (foundation RS disjE) 1),
    (etac equals0D 1),
    (rtac consI1 1),
    (fast_tac (lemmas_cs addIs [consI1,consI2]
                         addSEs [consE,equalityE]) 1) ]);

(*was called mem_anti_refl*)
qed_goal "mem_irrefl" ZF.thy "a:a ==> P"
 (fn [major]=> [ (rtac (major RS (major RS mem_asym)) 1) ]);

qed_goal "mem_not_refl" ZF.thy "a ~: a"
 (K [ (rtac notI 1), (etac mem_irrefl 1) ]);

(*Good for proving inequalities by rewriting*)
qed_goal "mem_imp_not_eq" ZF.thy "!!a A. a:A ==> a ~= A"
 (fn _=> [ fast_tac (lemmas_cs addSEs [mem_irrefl]) 1 ]);

(*** Rules for succ ***)

qed_goalw "succI1" ZF.thy [succ_def] "i : succ(i)"
 (fn _=> [ (rtac consI1 1) ]);

qed_goalw "succI2" ZF.thy [succ_def]
    "i : j ==> i : succ(j)"
 (fn [prem]=> [ (rtac (prem RS consI2) 1) ]);

qed_goalw "succE" ZF.thy [succ_def]
    "[| i : succ(j);  i=j ==> P;  i:j ==> P |] ==> P"
 (fn major::prems=>
  [ (rtac (major RS consE) 1),
    (REPEAT (eresolve_tac prems 1)) ]);

qed_goal "succ_iff" ZF.thy "i : succ(j) <-> i=j | i:j"
 (fn _ => [ (fast_tac (lemmas_cs addIs [succI1,succI2] addSEs [succE]) 1) ]);

(*Classical introduction rule*)
qed_goal "succCI" ZF.thy "(i~:j ==> i=j) ==> i: succ(j)"
 (fn [prem]=>
  [ (rtac (disjCI RS (succ_iff RS iffD2)) 1),
    (etac prem 1) ]);

qed_goal "succ_neq_0" ZF.thy "succ(n)=0 ==> P"
 (fn [major]=>
  [ (rtac (major RS equalityD1 RS subsetD RS emptyE) 1),
    (rtac succI1 1) ]);

(*Useful for rewriting*)
qed_goal "succ_not_0" ZF.thy "succ(n) ~= 0"
 (fn _=> [ (rtac notI 1), (etac succ_neq_0 1) ]);

(* succ(c) <= B ==> c : B *)
val succ_subsetD = succI1 RSN (2,subsetD);

(* succ(b) ~= b *)
bind_thm ("succ_neq_self", succI1 RS mem_imp_not_eq RS not_sym);


qed_goal "succ_inject" ZF.thy "!!m n. succ(m) = succ(n) ==> m=n"
 (fn _ =>
  [ (fast_tac (lemmas_cs addSEs [succE, equalityE, make_elim succ_subsetD] 
                         addEs [mem_asym]) 1) ]);

qed_goal "succ_inject_iff" ZF.thy "succ(m) = succ(n) <-> m=n"
 (fn _=> [ (fast_tac (FOL_cs addSEs [succ_inject]) 1) ]);

(*UpairI1/2 should become UpairCI? 
  mem_irrefl should NOT be added as an elim-rule here; 
      it would be tried on most goals, making proof slower!*)
val upair_cs = lemmas_cs
  addSIs [singletonI, DiffI, IntI, UnCI, consCI, succCI, UpairI1,UpairI2]
  addSEs [singletonE, DiffE, IntE, UnE, consE, succE, UpairE];

