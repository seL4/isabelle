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

context Option.thy;
Goal "{y. x = Some y} \\<subseteq> {the x}";
by Auto_tac;
val some_subset_the = result();
context thy;

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


(*#### patch for Isabelle98-1*)
val major::prems = goal Trancl.thy
 "\\<lbrakk> (x,y) \\<in> r^+; \
\    \\<And>x y. (x,y) \\<in> r \\<Longrightarrow> P x y; \
\    \\<And>x y z. \\<lbrakk> (x,y) \\<in> r^+; P x y; (y,z) \\<in> r^+; P y z \\<rbrakk> \\<Longrightarrow> P x z \
\ \\<rbrakk> \\<Longrightarrow> P x y";
by(blast_tac (claset() addIs ([r_into_trancl,major RS trancl_induct]@prems))1);
qed "trancl_trans_induct";

Goalw [is_class_def] "G\\<turnstile>C\\<prec>C D \\<Longrightarrow> is_class G C";
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
val wf_rel_lemma = result();


(* Proving the termination conditions *)

goalw thy [subcls1_rel_def] "wf subcls1_rel";
by(rtac (wf_rel_lemma RS wf_subset) 1);
by(Force_tac 1);
val wf_subcls1_rel = result();

val cmethd_TC = prove_goalw_cterm [subcls1_rel_def]
 (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd (tl (cmethd.tcs)))))
 (K [auto_tac (claset() addIs [subcls1I], simpset())]);

val fields_TC = prove_goalw_cterm [subcls1_rel_def]
 (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd (tl (fields.tcs)))))
 (K [auto_tac (claset() addIs [subcls1I], simpset())]);


AddSIs   [widen.refl];
Addsimps [widen.refl];

val prove_widen_lemma = prove_typerel_lemma [] widen.elim;

val widen_PrimT_RefT = prove_typerel "G\\<turnstile>PrimT x\\<preceq>RefT tname \\<Longrightarrow> R"
 [ prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S = PrimT x \\<longrightarrow> T = RefT tname \\<longrightarrow> R"];


val widen_RefT = prove_typerel "G\\<turnstile>RefT R\\<preceq>T \\<Longrightarrow> \\<exists>t. T=RefT t" 
	[prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S=RefT R \\<longrightarrow> (\\<exists>t. T=RefT t)"];

val widen_RefT2 = prove_typerel "G\\<turnstile>S\\<preceq>RefT R \\<Longrightarrow> \\<exists>t. S=RefT t" 
	[prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> T=RefT R \\<longrightarrow> (\\<exists>t. S=RefT t)"];

val widen_Class = prove_typerel "G\\<turnstile>Class C\\<preceq>T \\<Longrightarrow> \\<exists>D. T=Class D"
 [ prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S = Class C \\<longrightarrow> (\\<exists>D. T=Class D)"];

val widen_Class_RefT = prove_typerel 
	"G\\<turnstile>Class C\\<preceq>RefT t \\<Longrightarrow> (\\<exists>tname. t=ClassT tname)" 
 [prove_widen_lemma 
 "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S=Class C \\<longrightarrow> T=RefT t \\<longrightarrow> (\\<exists>tname. t=ClassT tname)"];

val widen_Class_NullT = prove_typerel "G\\<turnstile>Class C\\<preceq>RefT NullT \\<Longrightarrow> R" 
 [prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S=Class C \\<longrightarrow> T=RefT NullT \\<longrightarrow> R"];

val widen_Class_Class = prove_typerel "G\\<turnstile>Class C\\<preceq>Class cm \\<Longrightarrow> C=cm |  G\\<turnstile>C\\<prec>C cm"
[ prove_widen_lemma "G\\<turnstile>S\\<preceq>T \\<Longrightarrow> S = Class C \\<longrightarrow> T = Class cm \\<longrightarrow> C=cm |  G\\<turnstile>C\\<prec>C cm"];

Goal "\\<lbrakk>G\\<turnstile>S\\<preceq>U; \\<forall>C. is_class G C \\<longrightarrow> G\\<turnstile>Class C\\<preceq>Class Object;\
\\\<forall>C. G\\<turnstile>Object\\<prec>C C \\<longrightarrow> False \\<rbrakk> \\<Longrightarrow> \\<forall>T. G\\<turnstile>U\\<preceq>T \\<longrightarrow> G\\<turnstile>S\\<preceq>T";
by( etac widen.induct 1);
by   Safe_tac;
by(  ALLGOALS (forward_tac [widen_Class, widen_RefT]));
by  Safe_tac;
by(  rtac widen.null 2);
by( forward_tac [widen_Class_Class] 1);
by Safe_tac;
by(  ALLGOALS(EVERY'[etac thin_rl,etac thin_rl,
	fast_tac (claset() addIs [widen.subcls,trancl_trans])]));
qed_spec_mp "widen_trans_lemma";


val prove_cast_lemma = prove_typerel_lemma [] cast.elim;

val cast_RefT = prove_typerel "G\\<turnstile>RefT R\\<Rightarrow>? T \\<Longrightarrow> \\<exists>t. T=RefT t" 
	[prove_typerel_lemma [widen_RefT] cast.elim 
	"G\\<turnstile>S\\<Rightarrow>? T \\<Longrightarrow> S=RefT R \\<longrightarrow> (\\<exists>t. T=RefT t)"];

val cast_RefT2 = prove_typerel "G\\<turnstile>S\\<Rightarrow>? RefT R \\<Longrightarrow> \\<exists>t. S=RefT t" 
	[prove_typerel_lemma [widen_RefT2] cast.elim 
	"G\\<turnstile>S\\<Rightarrow>? T \\<Longrightarrow> T=RefT R \\<longrightarrow> (\\<exists>t. S=RefT t)"];

val cast_PrimT2 = prove_typerel "G\\<turnstile>S\\<Rightarrow>? PrimT pt \\<Longrightarrow> G\\<turnstile>S\\<preceq>PrimT pt" 
 [prove_cast_lemma "G\\<turnstile>S\\<Rightarrow>? T \\<Longrightarrow> T=PrimT pt \\<longrightarrow> G\\<turnstile>S\\<preceq>PrimT pt"];

