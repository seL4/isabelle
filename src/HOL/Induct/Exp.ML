(*  Title:      HOL/Induct/Exp
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Example of Mutual Induction via Iteratived Inductive Definitions: Expressions
*)

AddSIs [eval.N, eval.X];
AddIs  [eval.Op, eval.valOf];

val eval_elim_cases = 
    map eval.mk_cases 
       ["(N(n),sigma) -|-> (n',s')", 
	"(X(x),sigma) -|-> (n,s')",
	"(Op f a1 a2,sigma)  -|-> (n,s')",
	"(VALOF c RESULTIS e, s) -|-> (n, s1)"];

AddSEs eval_elim_cases;


Goal "(X x, s(x:=n)) -|-> (n, s(x:=n))";
by (rtac (fun_upd_same RS subst) 1 THEN resolve_tac eval.intrs 1);
qed "var_assign_eval";

AddSIs [var_assign_eval];


(** Make the induction rule look nicer -- though eta_contract makes the new
    version look worse than it is...**)

Goal "{((e,s),(n,s')). P e s n s'} = \
\         Collect (split (%v. split (split P v)))";
by (rtac Collect_cong 1);
by (split_all_tac 1);
by (Simp_tac 1);
val split_lemma = result();

(*New induction rule.  Note the form of the VALOF induction hypothesis*)
val major::prems = goal thy
  "[| (e,s) -|-> (n,s');                                         \
\     !!n s. P (N n) s n s;                                      \
\     !!s x. P (X x) s (s x) s;                                  \
\     !!e0 e1 f n0 n1 s s0 s1.                                   \
\        [| (e0,s) -|-> (n0,s0); P e0 s n0 s0;                   \
\           (e1,s0) -|-> (n1,s1); P e1 s0 n1 s1                  \
\        |] ==> P (Op f e0 e1) s (f n0 n1) s1;                   \
\     !!c e n s s0 s1.                                           \
\        [| (c,s) -[eval Int {((e,s),(n,s')). P e s n s'}]-> s0; \
\           (c,s) -[eval]-> s0;                                  \
\           (e,s0) -|-> (n,s1); P e s0 n s1 |]                   \
\        ==> P (VALOF c RESULTIS e) s n s1                       \
\  |] ==> P e s n s'";
by (rtac (major RS eval.induct) 1);
by (blast_tac (claset() addIs prems) 1);
by (blast_tac (claset() addIs prems) 1);
by (blast_tac (claset() addIs prems) 1);
by (forward_tac [impOfSubs (Int_lower1 RS exec_mono)] 1);
by (auto_tac (claset() addIs prems,simpset() addsimps [split_lemma]));
qed "eval_induct";


(*Lemma for Function_eval.  The major premise is that (c,s) executes to s1
  using eval restricted to its functional part.  Note that the execution
  (c,s) -[eval]-> s2 can use unrestricted eval!  The reason is that 
  the execution (c,s) -[eval Int {...}]-> s1 assures us that execution is
  functional on the argument (c,s).
*)
Goal "(c,s) -[eval Int {((e,s),(n,t)). ALL nt'. (e,s) -|-> nt' --> (n,t)=nt'}]-> s1 \
\     ==> (ALL s2. (c,s) -[eval]-> s2 --> s2=s1)";
by (etac exec.induct 1);
by (ALLGOALS Full_simp_tac);
      by (Blast_tac 1);
     by (Force_tac 1);
    by (Blast_tac 1);
   by (Blast_tac 1);
  by (Blast_tac 1);
 by (blast_tac (claset() addEs [exec_WHILE_case]) 1);
by (thin_tac "(?c,s2) -[?ev]-> s3" 1);
by (Clarify_tac 1);
by (etac exec_WHILE_case 1);
 by (ALLGOALS Blast_tac);
qed "com_Unique";


(*Expression evaluation is functional, or deterministic*)
Goalw [univalent_def] "univalent eval";
by (EVERY1[rtac allI, rtac allI, rtac impI]);
by (split_all_tac 1);
by (etac eval_induct 1);
by (dtac com_Unique 4);
by (ALLGOALS Full_simp_tac);
by (ALLGOALS Blast_tac);
qed "univalent_eval";


Goal "(e,s) -|-> (v,s') ==> (e = N n) --> (v=n & s'=s)";
by (etac eval_induct 1);
by (ALLGOALS Asm_simp_tac);
val lemma = result();
bind_thm ("eval_N_E", refl RSN (2, lemma RS mp));

AddSEs [eval_N_E];


(*This theorem says that "WHILE TRUE DO c" cannot terminate*)
Goal "(c', s) -[eval]-> t ==> (c' = WHILE (N 0) DO c) --> False";
by (etac exec.induct 1);
by Auto_tac;
bind_thm ("while_true_E", refl RSN (2, result() RS mp));


(** Equivalence of IF e THEN c;;(WHILE e DO c) ELSE SKIP  and  WHILE e DO c **)

Goal "(c',s) -[eval]-> t ==> \
\              (c' = WHILE e DO c) --> \
\              (IF e THEN c;;c' ELSE SKIP, s) -[eval]-> t";
by (etac exec.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac); 
bind_thm ("while_if1", refl RSN (2, result() RS mp));


Goal "(c',s) -[eval]-> t ==> \
\              (c' = IF e THEN c;;(WHILE e DO c) ELSE SKIP) --> \
\              (WHILE e DO c, s) -[eval]-> t";
by (etac exec.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac); 
bind_thm ("while_if2", refl RSN (2, result() RS mp));


Goal "((IF e THEN c;;(WHILE e DO c) ELSE SKIP, s) -[eval]-> t)  =  \
\         ((WHILE e DO c, s) -[eval]-> t)";
by (blast_tac (claset() addIs [while_if1, while_if2]) 1);
qed "while_if";



(** Equivalence of  (IF e THEN c1 ELSE c2);;c
               and  IF e THEN (c1;;c) ELSE (c2;;c)   **)

Goal "(c',s) -[eval]-> t ==> \
\              (c' = (IF e THEN c1 ELSE c2);;c) --> \
\              (IF e THEN (c1;;c) ELSE (c2;;c), s) -[eval]-> t";
by (etac exec.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1); 
bind_thm ("if_semi1", refl RSN (2, result() RS mp));


Goal "(c',s) -[eval]-> t ==> \
\              (c' = IF e THEN (c1;;c) ELSE (c2;;c)) --> \
\              ((IF e THEN c1 ELSE c2);;c, s) -[eval]-> t";
by (etac exec.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Blast_tac); 
bind_thm ("if_semi2", refl RSN (2, result() RS mp));


Goal "(((IF e THEN c1 ELSE c2);;c, s) -[eval]-> t)  =  \
\         ((IF e THEN (c1;;c) ELSE (c2;;c), s) -[eval]-> t)";
by (blast_tac (claset() addIs [if_semi1, if_semi2]) 1);
qed "if_semi";



(** Equivalence of  VALOF c1 RESULTIS (VALOF c2 RESULTIS e)
               and  VALOF c1;;c2 RESULTIS e
 **)

Goal "(e',s) -|-> (v,s') ==> \
\              (e' = VALOF c1 RESULTIS (VALOF c2 RESULTIS e)) --> \
\              (VALOF c1;;c2 RESULTIS e, s) -|-> (v,s')";
by (etac eval_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1); 
bind_thm ("valof_valof1", refl RSN (2, result() RS mp));


Goal "(e',s) -|-> (v,s') ==> \
\              (e' = VALOF c1;;c2 RESULTIS e) --> \
\              (VALOF c1 RESULTIS (VALOF c2 RESULTIS e), s) -|-> (v,s')";
by (etac eval_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1); 
bind_thm ("valof_valof2", refl RSN (2, result() RS mp));


Goal "((VALOF c1 RESULTIS (VALOF c2 RESULTIS e), s) -|-> (v,s'))  =  \
\         ((VALOF c1;;c2 RESULTIS e, s) -|-> (v,s'))";
by (blast_tac (claset() addIs [valof_valof1, valof_valof2]) 1);
qed "valof_valof";


(** Equivalence of  VALOF SKIP RESULTIS e  and  e **)

Goal "(e',s) -|-> (v,s') ==> \
\              (e' = VALOF SKIP RESULTIS e) --> \
\              (e, s) -|-> (v,s')";
by (etac eval_induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1); 
bind_thm ("valof_skip1", refl RSN (2, result() RS mp));

Goal "(e,s) -|-> (v,s') ==> (VALOF SKIP RESULTIS e, s) -|-> (v,s')";
by (Blast_tac 1);
qed "valof_skip2";

Goal "((VALOF SKIP RESULTIS e, s) -|-> (v,s'))  =  ((e, s) -|-> (v,s'))";
by (blast_tac (claset() addIs [valof_skip1, valof_skip2]) 1);
qed "valof_skip";


(** Equivalence of  VALOF x:=e RESULTIS x  and  e **)

Delsimps [fun_upd_apply];
Goal "(e',s) -|-> (v,s'') ==> \
\              (e' = VALOF x:=e RESULTIS X x) --> \
\              (EX s'. (e, s) -|-> (v,s') & (s'' = s'(x:=v)))";
by (etac eval_induct 1);
   by (ALLGOALS Asm_simp_tac);
by (thin_tac "?PP-->?QQ" 1);
by (Clarify_tac 1);
by (Simp_tac 1);
by (Blast_tac 1); 
bind_thm ("valof_assign1", refl RSN (2, result() RS mp));


Goal "(e,s) -|-> (v,s') ==> \
\              (VALOF x:=e RESULTIS X x, s) -|-> (v,s'(x:=v))";
by (Blast_tac 1);
qed "valof_assign2";
