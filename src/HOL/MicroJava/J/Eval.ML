(*  Title:      HOL/MicroJava/J/Eval.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goal "[|new_Addr (heap s) = (a,x); \
\      s' = c_hupd (heap s(a\\<mapsto>(C,init_vars (fields (G,C))))) (x,s)|] ==> \
\      G\\<turnstile>Norm s -NewC C\\<succ>Addr a-> s'";
by (Asm_simp_tac 1);
br eval_evals_exec.NewC 1;
by Auto_tac;
qed "NewCI";

Goal "!!s s'. (G\\<turnstile>(x,s) -e \\<succ>  v -> (x',s') --> x'=None --> x=None) \\<and> \
\             (G\\<turnstile>(x,s) -es[\\<succ>]vs-> (x',s') --> x'=None --> x=None) \\<and> \
\             (G\\<turnstile>(x,s) -c       -> (x',s') --> x'=None --> x=None)";
by(split_all_tac 1);
by(rtac eval_evals_exec.induct 1);
by(rewtac c_hupd_def);
by(ALLGOALS Asm_full_simp_tac);
qed "eval_evals_exec_no_xcpt";

Goal "G\\<turnstile>(x,s) -e\\<succ>v-> (None,s') ==> x=None";
by (dtac (eval_evals_exec_no_xcpt RS conjunct1 RS mp) 1);
by (Fast_tac 1);
qed "eval_no_xcpt";

Goal "G\\<turnstile>(x,s) -e[\\<succ>]v-> (None,s') ==> x=None";
by (dtac (eval_evals_exec_no_xcpt RS conjunct2 RS conjunct1 RS mp) 1);
by (Fast_tac 1);
qed "evals_no_xcpt";

Goal 
"!!s s'. (G\\<turnstile>(x,s) -e \\<succ>  v -> (x',s') --> x=Some xc --> x'=Some xc \\<and> s'=s) \\<and> \
\        (G\\<turnstile>(x,s) -es[\\<succ>]vs-> (x',s') --> x=Some xc --> x'=Some xc \\<and> s'=s) \\<and> \
\        (G\\<turnstile>(x,s) -c       -> (x',s') --> x=Some xc --> x'=Some xc \\<and> s'=s)";
by (split_all_tac 1);
by (rtac eval_evals_exec.induct 1);
by (rewtac c_hupd_def);
by (ALLGOALS Asm_full_simp_tac);
qed "eval_evals_exec_xcpt";

Goal "G\\<turnstile>(Some xc,s) -e\\<succ>v-> (x',s') ==> x'=Some xc \\<and>  s'=s";
by (dtac (eval_evals_exec_xcpt RS conjunct1 RS mp) 1);
by (Fast_tac 1);
qed "eval_xcpt";  

Goal "G\\<turnstile>(Some xc,s) -s0-> (x',s') ==> x'=Some xc \\<and>  s'=s";
by (dtac (eval_evals_exec_xcpt RS conjunct2 RS conjunct2 RS mp) 1);
by (Fast_tac 1);
qed "exec_xcpt";