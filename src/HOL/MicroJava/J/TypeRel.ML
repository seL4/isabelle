(*  Title:      HOL/MicroJava/J/TypeRel.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

val subcls1D = prove_goalw thy [subcls1_def] "\\<And>G. G\\<turnstile>C\\<prec>C1D \\<Longrightarrow> \
\ \\<exists>fs ms. class G C = Some (Some D,fs,ms)" (K [Auto_tac]);

val subcls1I = prove_goalw  thy [subcls1_def] 
"\\<And>G. \\<lbrakk> class G C = Some (Some D,rest) \\<rbrakk> \\<Longrightarrow> G\\<turnstile>C\\<prec>C1D" (K [Auto_tac]);

val subcls1_def2 = prove_goalw thy [subcls1_def,is_class_def]  "subcls1 G = \
\ (SIGMA C:{C. is_class G C} . {D. fst (the (class G C)) = Some D})"
 (K [Auto_tac]);

Goal "finite (subcls1 G)";
by(stac subcls1_def2 1);
by( rtac finite_SigmaI 1);
by(  rtac finite_is_class 1);
by( rtac finite_subset 1);
by(  rtac some_subset_the 1);
by( Simp_tac 1);
qed "finite_subcls1";

fun prove_typerel_lemma drules indrule s = prove_goal thy s (fn prems => [
	rtac (hd prems RS indrule) 1,
	auto_tac (claset() addDs drules, simpset())]);

fun prove_typerel s lemmata = prove_goal thy s (fn prems => [
	cut_facts_tac prems 1,
	auto_tac (claset() addDs lemmata, simpset())]);


Goalw [is_class_def] "(C,D) \\<in> (subcls1 G)^+ \\<Longrightarrow> is_class G C";
by(etac trancl_trans_induct 1);
by (auto_tac (HOL_cs addSDs [subcls1D],simpset()));
qed "subcls_is_class";

(* A particular thm about wf;
   looks like it is an odd instance of something more general
*)
Goalw [wf_def] "wf{((A,x),(B,y)) . A=B \\<and> wf(R(A)) \\<and> (x,y)\\<in>R(A)}";
by(full_simp_tac (simpset() delcongs [imp_cong] addsimps [split_paired_All]) 1);
by(strip_tac 1);
by(rename_tac "A x" 1);
by(case_tac "wf(R A)" 1);
by (eres_inst_tac [("a","x")] wf_induct 1);
by (EVERY1[etac allE, etac allE, etac mp, rtac allI, rtac allI]);
by (Fast_tac 1);
by(rewrite_goals_tac [wf_def]);
by(Blast_tac 1);
qed "wf_rel_lemma";


(* Proving the termination conditions *)

goalw thy [subcls1_rel_def] "wf subcls1_rel";
by(rtac (wf_rel_lemma RS wf_subset) 1);
by(Force_tac 1);
qed "wf_subcls1_rel";

val method_TC = prove_goalw_cterm [subcls1_rel_def]
 (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd (tl (method.tcs)))))
 (K [auto_tac (claset() addIs [subcls1I], simpset())]);

val fields_TC = prove_goalw_cterm [subcls1_rel_def]
 (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd (tl (fields.tcs)))))
 (K [auto_tac (claset() addIs [subcls1I], simpset())]);


AddSIs   [widen.refl];
Addsimps [widen.refl];

val prove_widen_lemma = prove_typerel_lemma [] widen.elim;

Goal "(G\\<turnstile>PrimT pT\\<preceq>RefT rT) = False";
br iffI 1;
be widen.elim 1;
by(Auto_tac);
qed "widen_PrimT_RefT";
AddIffs [widen_PrimT_RefT];

val widen_RefT = prove_typerel "G\\<turnstile>RefT R\\<preceq>T \\<Longrightarrow> \\<exists>t. T=RefT t" 
	[prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S=RefT R \\<longrightarrow> (\\<exists>t. T=RefT t)"];

val widen_RefT2 = prove_typerel "G\\<turnstile>S\\<preceq>RefT R \\<Longrightarrow> \\<exists>t. S=RefT t" 
	[prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> T=RefT R \\<longrightarrow> (\\<exists>t. S=RefT t)"];

val widen_Class = prove_typerel "G\\<turnstile>Class C\\<preceq>T \\<Longrightarrow> \\<exists>D. T=Class D"
 [ prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S = Class C \\<longrightarrow> (\\<exists>D. T=Class D)"];

Goal "(G\\<turnstile>Class C\\<preceq>RefT NullT) = False"; 
br iffI 1;
be widen.elim 1;
by(Auto_tac);
qed "widen_Class_NullT";
AddIffs [widen_Class_NullT];

Goal "(G\\<turnstile>Class C\\<preceq> Class D) = (G\\<turnstile>C\\<preceq>C D)";
br iffI 1;
be widen.elim 1;
by(Auto_tac);
bes widen.intrs 1;
qed "widen_Class_Class";
AddIffs [widen_Class_Class];

Goal "G\\<turnstile>S\\<preceq>U \\<Longrightarrow> \\<forall>T. G\\<turnstile>U\\<preceq>T \\<longrightarrow> G\\<turnstile>S\\<preceq>T";
by( etac widen.induct 1);
by   Safe_tac;
by(  ALLGOALS (forward_tac [widen_Class, widen_RefT]));
by  Safe_tac;
by(  rtac widen.null 2);
by(eatac rtrancl_trans 1 1);
qed_spec_mp "widen_trans";


val prove_cast_lemma = prove_typerel_lemma [] cast.elim;

val cast_RefT = prove_typerel "G\\<turnstile>RefT R\\<preceq>? T \\<Longrightarrow> \\<exists>t. T=RefT t" 
	[prove_typerel_lemma [widen_RefT] cast.elim 
	"G\\<turnstile>S\\<preceq>? T \\<Longrightarrow> S=RefT R \\<longrightarrow> (\\<exists>t. T=RefT t)"];

val cast_RefT2 = prove_typerel "G\\<turnstile>S\\<preceq>? RefT R \\<Longrightarrow> \\<exists>t. S=RefT t" 
	[prove_typerel_lemma [widen_RefT2] cast.elim 
	"G\\<turnstile>S\\<preceq>? T \\<Longrightarrow> T=RefT R \\<longrightarrow> (\\<exists>t. S=RefT t)"];

val cast_PrimT2 = prove_typerel "G\\<turnstile>S\\<preceq>? PrimT pt \\<Longrightarrow> G\\<turnstile>S\\<preceq>PrimT pt" 
 [prove_cast_lemma "G\\<turnstile>S\\<preceq>? T \\<Longrightarrow> T=PrimT pt \\<longrightarrow> G\\<turnstile>S\\<preceq>PrimT pt"];

