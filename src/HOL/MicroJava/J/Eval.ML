(*  Title:      HOL/MicroJava/J/Eval.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goal "\\<And>s s'. (G\\<turnstile>(x,s) -e \\<succ>  v \\<rightarrow> (x',s') \\<longrightarrow> x'=None \\<longrightarrow> x=None) \\<and> \
\             (G\\<turnstile>(x,s) -es[\\<succ>]vs\\<rightarrow> (x',s') \\<longrightarrow> x'=None \\<longrightarrow> x=None) \\<and> \
\             (G\\<turnstile>(x,s) -c       \\<rightarrow> (x',s') \\<longrightarrow> x'=None \\<longrightarrow> x=None)";
by(split_all_tac 1);
by(rtac eval_evals_exec.induct 1);
by(rewtac c_hupd_def);
by(ALLGOALS Asm_full_simp_tac);
qed "eval_evals_exec_no_xcpt";

val eval_no_xcpt = prove_goal thy "\\<And>X. G\\<turnstile>(x,s) -e\\<succ>v\\<rightarrow> (None,s') \\<Longrightarrow> x=None" (K [
	dtac (eval_evals_exec_no_xcpt RS conjunct1 RS mp) 1,
	Fast_tac 1]);
val evals_no_xcpt = prove_goal thy "\\<And>X. G\\<turnstile>(x,s) -e[\\<succ>]v\\<rightarrow> (None,s') \\<Longrightarrow> x=None" (K [
	dtac (eval_evals_exec_no_xcpt RS conjunct2 RS conjunct1 RS mp) 1,
	Fast_tac 1]);

val eval_evals_exec_xcpt = prove_goal thy 
"\\<And>s s'. (G\\<turnstile>(x,s) -e \\<succ>  v \\<rightarrow> (x',s') \\<longrightarrow> x=Some xc \\<longrightarrow> x'=Some xc \\<and> s'=s) \\<and> \
\        (G\\<turnstile>(x,s) -es[\\<succ>]vs\\<rightarrow> (x',s') \\<longrightarrow> x=Some xc \\<longrightarrow> x'=Some xc \\<and> s'=s) \\<and> \
\        (G\\<turnstile>(x,s) -c       \\<rightarrow> (x',s') \\<longrightarrow> x=Some xc \\<longrightarrow> x'=Some xc \\<and> s'=s)"
 (K [
	split_all_tac 1,
	rtac eval_evals_exec.induct 1,
	rewtac c_hupd_def,
	ALLGOALS Asm_full_simp_tac]);
val eval_xcpt = prove_goal thy 
"\\<And>X. G\\<turnstile>(Some xc,s) -e\\<succ>v\\<rightarrow> (x',s') \\<Longrightarrow> x'=Some xc \\<and>  s'=s" (K [
	dtac (eval_evals_exec_xcpt RS conjunct1 RS mp) 1,
	Fast_tac 1]);
val exec_xcpt = prove_goal thy 
"\\<And>X. G\\<turnstile>(Some xc,s) -s0\\<rightarrow> (x',s') \\<Longrightarrow> x'=Some xc \\<and>  s'=s" (K [
	dtac (eval_evals_exec_xcpt RS conjunct2 RS conjunct2 RS mp) 1,
	Fast_tac 1]);
