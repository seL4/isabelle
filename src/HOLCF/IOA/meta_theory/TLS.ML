(*  Title:      HOLCF/IOA/meta_theory/TLS.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Temporal Logic of Steps -- tailored for I/O automata
*)   

(* global changes to simpset() and claset(), repeated from Traces.ML *)
Delsimps (ex_simps @ all_simps);
Delsimps [split_paired_Ex];
Addsimps [Let_def];
claset_ref() := claset() delSWrapper "split_all_tac";


(* ---------------------------------------------------------------- *)
(*                                 ex2seqC                          *)
(* ---------------------------------------------------------------- *)

goal thy "ex2seqC  = (LAM ex. (%s. case ex of \
\      nil =>  (s,None,s)>>nil   \
\    | x##xs => (flift1 (%pr. \
\                (s,Some (fst pr), snd pr)>> (ex2seqC`xs) (snd pr))  \
\                `x)  \
\      ))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac ex2seqC_def 1);
by (rtac beta_cfun 1);
by (simp_tac (simpset() addsimps [flift1_def]) 1);
qed"ex2seqC_unfold";

goal thy "(ex2seqC `UU) s=UU";
by (stac ex2seqC_unfold 1);
by (Simp_tac 1);
qed"ex2seqC_UU";

goal thy "(ex2seqC `nil) s = (s,None,s)>>nil";
by (stac ex2seqC_unfold 1);
by (Simp_tac 1);
qed"ex2seqC_nil";

goal thy "(ex2seqC `((a,t)>>xs)) s = \
\          (s,Some a,t)>> ((ex2seqC`xs) t)";
by (rtac trans 1);
by (stac ex2seqC_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_def,flift1_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_def,flift1_def]) 1);
qed"ex2seqC_cons";

Addsimps [ex2seqC_UU,ex2seqC_nil,ex2seqC_cons];


goal thy "ex2seq (s, UU) = UU";
by (simp_tac (simpset() addsimps [ex2seq_def]) 1);
qed"ex2seq_UU";

goal thy "ex2seq (s, nil) = (s,None,s)>>nil";
by (simp_tac (simpset() addsimps [ex2seq_def]) 1);
qed"ex2seq_nil";

goal thy "ex2seq (s, (a,t)>>ex) = (s,Some a,t) >> ex2seq (t, ex)";
by (simp_tac (simpset() addsimps [ex2seq_def]) 1);
qed"ex2seq_cons";

Delsimps [ex2seqC_UU,ex2seqC_nil,ex2seqC_cons]; 
Addsimps [ex2seq_UUAlt,ex2seq_nil, ex2seq_cons];  



(* FIX: Not true for UU, as ex2seq is defined continously !!!!! *)
goal thy "ex2seq exec ~= UU & ex2seq exec ~= nil";


goal thy "ex |== [] P .--> P";


(* ----------------------------------------------------------- *)
(*           Interface TL -- TLS                               *)
(* ---------------------------------------------------------- *)

goalw thy [Init_def,Next_def,temp_sat_def,satisfies_def,IMPLIES_def,AND_def]
 "!! s. (P s) & s-a--A-> t --> (Q t) \
\  ==> ex |== (Init (%(s,a,t). P s) .& Init (%(s,a,t). s -a--A-> t) \
\             .--> (Next (Init (%(s,a,t).Q s))))";

by (asm_full_simp_tac (simpset() setloop split_tac [expand_if]) 1);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);




