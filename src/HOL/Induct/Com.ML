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
Goal "Function ev ==> Function(exec ev)";
by (simp_tac (simpset() addsimps [Function_def, Unique_def]) 1);
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (etac exec.induct 1);
by (Blast_tac 3);
by (Blast_tac 1);
by (rewrite_goals_tac [Function_def, Unique_def]);
by (thin_tac "(?c,s1) -[ev]-> s2" 5);
by (rotate_tac 1 5);   (*PATCH to avoid very slow proof*)
(*SLOW (23s) due to proof reconstruction; needs 60s if thin_tac is omitted*)
by (REPEAT (blast_tac (claset() addEs [exec_WHILE_case]) 1));
qed "Function_exec";


Goalw [assign_def] "(s[v/x])x = v";
by (Simp_tac 1);
qed "assign_same";

Goalw [assign_def] "y~=x ==> (s[v/x])y = s y";
by (Asm_simp_tac 1);
qed "assign_different";

Goalw [assign_def] "s[s x/x] = s";
by (rtac ext 1);
by (Simp_tac 1);
qed "assign_triv";

Addsimps [assign_same, assign_different, assign_triv];
