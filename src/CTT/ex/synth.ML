(*  Title:      CTT/ex/synth
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

writeln"Synthesis examples, using a crude form of narrowing";


writeln"discovery of predecessor function";
goal CTT.thy 
 "?a : SUM pred:?A . Eq(N, pred`0, 0)   \
\                 *  (PROD n:N. Eq(N, pred ` succ(n), n))";
by (intr_tac[]);
by eqintr_tac;
by (resolve_tac reduction_rls 3);
by (resolve_tac comp_rls 5);
by (rew_tac[]);
result();

writeln"the function fst as an element of a function type";
val prems = goal CTT.thy 
    "A type ==> ?a: SUM f:?B . PROD i:A. PROD j:A. Eq(A, f ` <i,j>, i)";
by (intr_tac prems);
by eqintr_tac;
by (resolve_tac reduction_rls 2);
by (resolve_tac comp_rls 4);
by (typechk_tac prems);
writeln"now put in A everywhere";
by (REPEAT (resolve_tac prems 1));
by (fold_tac basic_defs);
result();

writeln"An interesting use of the eliminator, when";
(*The early implementation of unification caused non-rigid path in occur check
  See following example.*)
goal CTT.thy 
    "?a : PROD i:N. Eq(?A, ?b(inl(i)), <0    ,   i>)  \
\                 * Eq(?A, ?b(inr(i)), <succ(0), i>)";
by (intr_tac[]);
by eqintr_tac;
by (resolve_tac comp_rls 1);
by (rew_tac[]);
uresult();

(*Here we allow the type to depend on i.  
 This prevents the cycle in the first unification (no longer needed).  
 Requires flex-flex to preserve the dependence.
 Simpler still: make ?A into a constant type N*N.*)
goal CTT.thy 
    "?a : PROD i:N. Eq(?A(i), ?b(inl(i)), <0   ,   i>)   \
\                *  Eq(?A(i), ?b(inr(i)), <succ(0),i>)";

writeln"A tricky combination of when and split";
(*Now handled easily, but caused great problems once*)
goal CTT.thy 
    "?a : PROD i:N. PROD j:N. Eq(?A, ?b(inl(<i,j>)), i)   \
\                          *  Eq(?A, ?b(inr(<i,j>)), j)";
by (intr_tac[]); 
by eqintr_tac;
by (resolve_tac [ PlusC_inl RS trans_elem ] 1);
by (resolve_tac comp_rls 4); 
by (resolve_tac reduction_rls 7);
by (resolve_tac comp_rls 10);
by (typechk_tac[]); (*2 secs*)
by (fold_tac basic_defs);
uresult();

(*similar but allows the type to depend on i and j*)
goal CTT.thy 
    "?a : PROD i:N. PROD j:N. Eq(?A(i,j), ?b(inl(<i,j>)), i) \
\                         *   Eq(?A(i,j), ?b(inr(<i,j>)), j)";

(*similar but specifying the type N simplifies the unification problems*)
goal CTT.thy
    "?a : PROD i:N. PROD j:N. Eq(N, ?b(inl(<i,j>)), i)  \
\                         *   Eq(N, ?b(inr(<i,j>)), j)";


writeln"Deriving the addition operator";
goal Arith.thy 
   "?c : PROD n:N. Eq(N, ?f(0,n), n)  \
\               *  (PROD m:N. Eq(N, ?f(succ(m), n), succ(?f(m,n))))";
by (intr_tac[]);
by eqintr_tac;
by (resolve_tac comp_rls 1);
by (rew_tac[]);
by (fold_tac arith_defs);
result();

writeln"The addition function -- using explicit lambdas";
goal Arith.thy 
  "?c : SUM plus : ?A .  \
\        PROD x:N. Eq(N, plus`0`x, x)  \
\               *  (PROD y:N. Eq(N, plus`succ(y)`x, succ(plus`y`x)))";
by (intr_tac[]);
by eqintr_tac;
by (resolve_tac [TSimp.split_eqn] 3);
by (SELECT_GOAL (rew_tac[]) 4);
by (resolve_tac [TSimp.split_eqn] 3);
by (SELECT_GOAL (rew_tac[]) 4);
by (res_inst_tac [("p","y")] NC_succ 3);
  (**  by (resolve_tac comp_rls 3);  caused excessive branching  **)
by (rew_tac[]); 
by (fold_tac arith_defs);
result();

writeln"Reached end of file.";
