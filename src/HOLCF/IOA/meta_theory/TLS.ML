(*  Title:      HOLCF/IOA/meta_theory/TLS.ML
    ID:         $Id$
    Author:     Olaf Müller

Temporal Logic of Steps -- tailored for I/O automata.
*)    

(* global changes to simpset() and claset(), repeated from Traces.ML *)
Delsimps (ex_simps @ all_simps);
Delsimps [split_paired_Ex];
Addsimps [Let_def];
claset_ref() := claset() delSWrapper "split_all_tac";


(* ---------------------------------------------------------------- *)
(*                                 ex2seqC                          *)
(* ---------------------------------------------------------------- *)

Goal "ex2seqC  = (LAM ex. (%s. case ex of \
\      nil =>  (s,None,s)>>nil   \
\    | x##xs => (flift1 (%pr. \
\                (s,Some (fst pr), snd pr)>> (ex2seqC$xs) (snd pr))  \
\                $x)  \
\      ))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac ex2seqC_def 1);
by (rtac beta_cfun 1);
by (simp_tac (simpset() addsimps [flift1_def]) 1);
qed"ex2seqC_unfold";

Goal "(ex2seqC $UU) s=UU";
by (stac ex2seqC_unfold 1);
by (Simp_tac 1);
qed"ex2seqC_UU";

Goal "(ex2seqC $nil) s = (s,None,s)>>nil";
by (stac ex2seqC_unfold 1);
by (Simp_tac 1);
qed"ex2seqC_nil";

Goal "(ex2seqC $((a,t)>>xs)) s = \
\          (s,Some a,t)>> ((ex2seqC$xs) t)";
by (rtac trans 1);
by (stac ex2seqC_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,flift1_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,flift1_def]) 1);
qed"ex2seqC_cons";

Addsimps [ex2seqC_UU,ex2seqC_nil,ex2seqC_cons];



Addsimps [mkfin_UU,mkfin_nil,mkfin_cons];

Goal "ex2seq (s, UU) = (s,None,s)>>nil";
by (simp_tac (simpset() addsimps [ex2seq_def]) 1);
qed"ex2seq_UU";

Goal "ex2seq (s, nil) = (s,None,s)>>nil";
by (simp_tac (simpset() addsimps [ex2seq_def]) 1);
qed"ex2seq_nil";

Goal "ex2seq (s, (a,t)>>ex) = (s,Some a,t) >> ex2seq (t, ex)";
by (simp_tac (simpset() addsimps [ex2seq_def]) 1);
qed"ex2seq_cons";

Delsimps [ex2seqC_UU,ex2seqC_nil,ex2seqC_cons]; 
Addsimps [ex2seq_UU,ex2seq_nil, ex2seq_cons];  


Goal "ex2seq exec ~= UU & ex2seq exec ~= nil";
by (pair_tac "exec" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
qed"ex2seq_nUUnnil";


(* ----------------------------------------------------------- *)
(*           Interface TL -- TLS                               *)
(* ---------------------------------------------------------- *)


(* uses the fact that in executions states overlap, which is lost in 
   after the translation via ex2seq !! *)

Goalw [Init_def,Next_def,temp_sat_def,satisfies_def,IMPLIES_def,AND_def]
 "[| ! s a t. (P s) & s-a--A-> t --> (Q t) |]\
\  ==> ex |== (Init (%(s,a,t). P s) .& Init (%(s,a,t). s -a--A-> t) \
\             .--> (Next (Init (%(s,a,t).Q s))))";

by (clarify_tac set_cs 1);
by (asm_full_simp_tac (simpset() addsplits [split_if]) 1);
(* TL = UU *)
by (rtac conjI 1);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
(* TL = nil *)
by (rtac conjI 1);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (asm_full_simp_tac (simpset() addsimps [unlift_def])1);
by (Fast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [unlift_def])1);
by (Fast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [unlift_def])1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
(* TL =cons *)
by (asm_full_simp_tac (simpset() addsimps [unlift_def])1);

by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
 by (Fast_tac 1);
 by (Fast_tac 1);
by (pair_tac "a" 1);
 by (Fast_tac 1);
qed"TL_TLS";
