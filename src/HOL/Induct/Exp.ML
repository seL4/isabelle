(*  Title:      HOL/Induct/Exp
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Example of Mutual Induction via Iteratived Inductive Definitions: Expressions
*)

open Exp;

val eval_elim_cases = map (eval.mk_cases exp.simps)
   ["(N(n),sigma) -|-> (n',s')", "(X(x),sigma) -|-> (n,s')",
    "(Op f a1 a2,sigma)  -|-> (n,s')",
    "(VALOF c RESULTIS e, s) -|-> (n, s1)"
   ];

AddSEs eval_elim_cases;


(** Make the induction rule look nicer -- though eta_contract makes the new
    version look worse than it is...**)

goal thy "{((e,s),(n,s')). P e s n s'} = \
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
\           (e,s0) -|-> (n,s1); P e s0 n s1 |]                   \
\        ==> P (VALOF c RESULTIS e) s n s1                       \
\  |] ==> P e s n s'";
by (rtac (major RS eval.induct) 1);
by (blast_tac (!claset addIs prems) 1);
by (blast_tac (!claset addIs prems) 1);
by (blast_tac (!claset addIs prems) 1);
by (fast_tac (!claset addIs prems addss (!simpset addsimps [split_lemma])) 1);
qed "eval_induct";


(*Lemma for Function_eval.  The major premise is that (c,s) executes to s1
  using eval restricted to its functional part.  Note that the execution
  (c,s) -[eval]-> s2 can use unrestricted eval!  The reason is that 
  the execution (c,s) -[eval Int {...}]-> s1 assures us that execution is
  functional on the argument (c,s).
*)
goal thy
    "!!x. (c,s) -[eval Int {((e,s),(n,s')). Unique (e,s) (n,s') eval}]-> s1 \
\         ==> (ALL s2. (c,s) -[eval]-> s2 --> s2=s1)";
by (etac exec.induct 1);
by (ALLGOALS Full_simp_tac);
by (Blast_tac 3);
by (Blast_tac 1);
by (rewtac Unique_def);
by (Blast_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
by (blast_tac (!claset addEs [exec_WHILE_case]) 1);
by (thin_tac "(?c,s2) -[?ev]-> s3" 1);
by (Step_tac 1);
by (etac exec_WHILE_case 1);
by (ALLGOALS Fast_tac);         (*Blast_tac: proof fails*)
qed "com_Unique";


(*Expression evaluation is functional, or deterministic*)
goal thy "Function eval";
by (simp_tac (!simpset addsimps [Function_def]) 1);
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (etac eval_induct 1);
by (dtac com_Unique 4);
by (ALLGOALS (full_simp_tac (!simpset addsimps [Unique_def])));
by (ALLGOALS Blast_tac);
qed "Function_eval";
