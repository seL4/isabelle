(*  Title:      HOL/Induct/Com
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Example of Mutual Induction via Iteratived Inductive Definitions: Commands
*)

AddIs exec.intrs;

val exec_elim_cases = 
    map exec.mk_cases
       ["(SKIP,s) -[eval]-> t",
	"(x:=a,s) -[eval]-> t", 
	"(c1;;c2, s) -[eval]-> t",
	"(IF e THEN c1 ELSE c2, s) -[eval]-> t"];

val exec_WHILE_case = exec.mk_cases "(WHILE b DO c,s) -[eval]-> t";

AddSEs exec_elim_cases;

(*This theorem justifies using "exec" in the inductive definition of "eval"*)
Goalw exec.defs "A<=B ==> exec(A) <= exec(B)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "exec_mono";


Unify.trace_bound := 30;
Unify.search_bound := 60;

(*Command execution is functional (deterministic) provided evaluation is*)
Goal "single_valued ev ==> single_valued(exec ev)";
by (simp_tac (simpset() addsimps [single_valued_def]) 1);
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (etac exec.induct 1);
by (Blast_tac 3);
by (Blast_tac 1);
by (rewrite_goals_tac [single_valued_def]);
by (REPEAT (blast_tac (claset() addEs [exec_WHILE_case]) 1));
qed "single_valued_exec";

Addsimps [fun_upd_same, fun_upd_other];
