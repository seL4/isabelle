(*  Title: 	HOLCF/FOCUS/Buffer_adm.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

infixr 0 y;
fun _ y t = by t;
val b=9999;

Addsimps [thm "Fin_0"];

val BufAC_Asm_d2 = prove_forw "a\\<leadsto>s:BufAC_Asm ==> ? d. a=Md d" BufAC_Asm_unfold;
val BufAC_Asm_d3 = prove_forw 
    "a\\<leadsto>b\\<leadsto>s:BufAC_Asm ==> ? d. a=Md d & b=\\<bullet> & s:BufAC_Asm" BufAC_Asm_unfold;

val BufAC_Asm_F_def3 = prove_goalw thy [BufAC_Asm_F_def] 
 "(s:BufAC_Asm_F A) = (s=<> | \
\ (? d. ft\\<cdot>s=Def(Md d)) & (rt\\<cdot>s=<> | ft\\<cdot>(rt\\<cdot>s)=Def \\<bullet> & rt\\<cdot>(rt\\<cdot>s):A))" (K [
	Auto_tac]);

Goal "down_cont BufAC_Asm_F";
by (auto_tac (claset(),simpset() addsimps [down_cont_def,BufAC_Asm_F_def3]));
qed "cont_BufAC_Asm_F";

val BufAC_Cmt_F_def3 = prove_goalw thy [BufAC_Cmt_F_def] 
 "((s,t):BufAC_Cmt_F C) = (!d x.\
\   (s = <>       --> t = <>                   ) & \
\   (s = Md d\\<leadsto><>  --> t = <>                   ) & \
\   (s = Md d\\<leadsto>\\<bullet>\\<leadsto>x --> ft\\<cdot>t = Def d & (x,rt\\<cdot>t):C))" (fn _=> [
	subgoal_tac "!d x. (s = Md d\\<leadsto>\\<bullet>\\<leadsto>x --> (? y. t = d\\<leadsto>y & (x,y):C)) = \
		   \ (s = Md d\\<leadsto>\\<bullet>\\<leadsto>x --> ft\\<cdot>t = Def d & (x,rt\\<cdot>t):C)"  1,
	Asm_simp_tac 1,
	auto_tac (claset() addIs [surjectiv_scons RS sym], simpset())]);

val cont_BufAC_Cmt_F = prove_goal thy "down_cont BufAC_Cmt_F" (K [
	auto_tac (claset(),simpset() addsimps [down_cont_def,BufAC_Cmt_F_def3])]);


(**** adm_BufAC_Asm ***********************************************************)

Goalw [BufAC_Asm_F_def, stream_monoP_def] "stream_monoP BufAC_Asm_F";
by (res_inst_tac [("x","{x. (? d. x = Md d\\<leadsto>\\<bullet>\\<leadsto><>)}")] exI 1);
by (res_inst_tac [("x","2")] exI 1);
by (Clarsimp_tac 1);
qed "BufAC_Asm_F_stream_monoP";

val adm_BufAC_Asm = prove_goalw thy [BufAC_Asm_def] "adm (%x. x:BufAC_Asm)" (K [
rtac (cont_BufAC_Asm_F RS (BufAC_Asm_F_stream_monoP RS fstream_gfp_admI))1]);


(**** adm_non_BufAC_Asm *******************************************************)

Goalw [stream_antiP_def, BufAC_Asm_F_def] "stream_antiP BufAC_Asm_F";
b y strip_tac 1;
b y res_inst_tac [("x","{x. (? d. x = Md d\\<leadsto>\\<bullet>\\<leadsto><>)}")] exI 1;
b y res_inst_tac [("x","2")] exI 1;
b y rtac conjI 1;
b y  strip_tac 2;
b y  dtac slen_mono 2;
b y  datac (thm "ile_trans") 1 2;
b y ALLGOALS Force_tac;
qed "BufAC_Asm_F_stream_antiP";

Goalw [BufAC_Asm_def] "adm (%u. u~:BufAC_Asm)";
by (rtac (cont_BufAC_Asm_F RS (BufAC_Asm_F_stream_antiP RS fstream_non_gfp_admI)) 1);
qed "adm_non_BufAC_Asm";

(**** adm_BufAC ***************************************************************)

(*adm_non_BufAC_Asm*)
Goal "!f ff. f:BufEq --> ff:BufEq --> s:BufAC_Asm --> f\\<cdot>s = ff\\<cdot>s";
by (rtac fstream_ind2 1);
by (simp_tac (simpset() addsimps [adm_non_BufAC_Asm]) 1);
by   (force_tac (claset() addDs [Buf_f_empty], simpset()) 1);
by  (force_tac (claset() addSDs [BufAC_Asm_d2] 
		addDs [Buf_f_d] addEs [ssubst], simpset()) 1);
by (safe_tac (claset() addSDs [BufAC_Asm_d3]));
by (REPEAT(dtac Buf_f_d_req 1));
by (fast_tac (claset() addEs [ssubst]) 1);
qed_spec_mp "BufAC_Asm_cong";

(*adm_non_BufAC_Asm,BufAC_Asm_cong*)
val BufAC_Cmt_d_req = prove_goal thy 
"!!X. [|f:BufEq; s:BufAC_Asm; (s, f\\<cdot>s):BufAC_Cmt|] ==> (a\\<leadsto>b\\<leadsto>s, f\\<cdot>(a\\<leadsto>b\\<leadsto>s)):BufAC_Cmt"
 (K [
	rtac (BufAC_Cmt_unfold RS iffD2) 1,
	strip_tac 1,
	forward_tac [Buf_f_d_req] 1,
	auto_tac (claset() addEs [BufAC_Asm_cong RS subst],simpset())]);

(*adm_BufAC_Asm*)
Goal "antitonP BufAC_Asm";
b y rtac antitonPI 1;
b y rtac allI 1;
b y rtac fstream_ind2 1;
b y   REPEAT(resolve_tac adm_lemmas 1);
b y    rtac cont_id 1;
b y    rtac adm_BufAC_Asm 1;
b y   safe_tac HOL_cs;
b y   rtac BufAC_Asm_empty 1;
b y  force_tac (claset() addSDs [fstream_prefix]
		addDs [BufAC_Asm_d2] addIs [BufAC_Asm_d],simpset()) 1;
b y  force_tac (claset() addSDs [fstream_prefix]
		addDs [] addIs []
		addDs [BufAC_Asm_d3] addSIs [BufAC_Asm_d_req],simpset()) 1;
qed "BufAC_Asm_antiton";

(*adm_BufAC_Asm,BufAC_Asm_antiton,adm_non_BufAC_Asm,BufAC_Asm_cong*)
Goal "f:BufEq ==> ? l. !i x s. s:BufAC_Asm --> x << s --> Fin (l i) < #x --> \
		\    (x,f\\<cdot>x):down_iterate BufAC_Cmt_F i --> \
		\    (s,f\\<cdot>s):down_iterate BufAC_Cmt_F i";
by (res_inst_tac [("x","%i. #2*i")] exI 1);
by (rtac allI 1);
by (nat_ind_tac "i" 1);
by ( Simp_tac 1);
by (simp_tac (simpset() addsimps [add_commute]) 1);
by (strip_tac 1);
by (stac BufAC_Cmt_F_def3 1);
by (dres_inst_tac [("P","%x. x")] (BufAC_Cmt_F_def3 RS subst) 1);
by (Safe_tac);
by (   etac Buf_f_empty 1);
by (  etac Buf_f_d 1);
by ( dtac Buf_f_d_req 1);
by ( EVERY[safe_tac HOL_cs, etac ssubst 1, Simp_tac 1]);
by (safe_tac (claset() addSDs [slen_fscons_eq RS iffD1] addSss simpset()));
(*
 1. \\<And>i d xa ya t.
       \\<lbrakk>f \\<in> BufEq;
          \\<forall>x s. s \\<in> BufAC_Asm \\<longrightarrow>
                x \\<sqsubseteq> s \\<longrightarrow>
                Fin (#2 * i) < #x \\<longrightarrow>
                (x, f\\<cdot>x) \\<in> down_iterate BufAC_Cmt_F i \\<longrightarrow>
                (s, f\\<cdot>s) \\<in> down_iterate BufAC_Cmt_F i;
          Md d\\<leadsto>\\<bullet>\\<leadsto>xa \\<in> BufAC_Asm; Fin (#2 * i) < #ya; f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>ya) = d\\<leadsto>t;
          (ya, t) \\<in> down_iterate BufAC_Cmt_F i; ya \\<sqsubseteq> xa\\<rbrakk>
       \\<Longrightarrow> (xa, rt\\<cdot>(f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>xa))) \\<in> down_iterate BufAC_Cmt_F i
*)
by (rotate_tac 2 1);
by (dtac BufAC_Asm_prefix2 1);
by (EVERY[ftac Buf_f_d_req 1, etac exE 1, etac conjE 1, rotate_tac ~1 1,etac ssubst 1]); 
by (EVERY[ftac Buf_f_d_req 1, etac exE 1, etac conjE 1]);
by (		subgoal_tac "f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>ya) = d\\<leadsto>ffa\\<cdot>ya" 1);
by ( atac 2);
by (		rotate_tac ~1 1);
by (		Asm_full_simp_tac 1);
by (hyp_subst_tac 1);
(*
 1. \\<And>i d xa ya t ff ffa.
       \\<lbrakk>f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>ya) = d\\<leadsto>ffa\\<cdot>ya; Fin (#2 * i) < #ya;
          (ya, ffa\\<cdot>ya) \\<in> down_iterate BufAC_Cmt_F i; ya \\<sqsubseteq> xa; f \\<in> BufEq;
          \\<forall>x s. s \\<in> BufAC_Asm \\<longrightarrow>
                x \\<sqsubseteq> s \\<longrightarrow>
                Fin (#2 * i) < #x \\<longrightarrow>
                (x, f\\<cdot>x) \\<in> down_iterate BufAC_Cmt_F i \\<longrightarrow>
                (s, f\\<cdot>s) \\<in> down_iterate BufAC_Cmt_F i;
          xa \\<in> BufAC_Asm; ff \\<in> BufEq; ffa \\<in> BufEq\\<rbrakk>
       \\<Longrightarrow> (xa, ff\\<cdot>xa) \\<in> down_iterate BufAC_Cmt_F i
*)
by (smp_tac 2 1);
by (mp_tac 1);
by (mp_tac 1);
by (etac impE 1);
by ( EVERY[stac BufAC_Asm_cong 1, atac 1, atac 3, atac 1]);
by ( eatac (BufAC_Asm_antiton RS antitonPD) 1 1);
by (EVERY[stac BufAC_Asm_cong 1, atac 1, atac 3, atac 1, atac 1]);
qed "BufAC_Cmt_2stream_monoP";

Goalw [BufAC_Cmt_def] "(x\\<in>BufAC_Cmt) = (\\<forall>n. x\\<in>down_iterate BufAC_Cmt_F n)";
by (stac (cont_BufAC_Cmt_F RS INTER_down_iterate_is_gfp) 1);
by (Fast_tac 1);
qed "BufAC_Cmt_iterate_all";

(*adm_BufAC_Asm,BufAC_Asm_antiton,adm_non_BufAC_Asm,BufAC_Asm_cong,
  BufAC_Cmt_2stream_monoP*)
Goal "f:BufEq ==> adm (%s. s:BufAC_Asm --> (s, f\\<cdot>s):BufAC_Cmt)";
by (rtac flatstream_admI 1);
by (stac BufAC_Cmt_iterate_all 1);
by (dtac BufAC_Cmt_2stream_monoP 1);
by Safe_tac;
by (EVERY'[dtac spec, etac exE] 1);
by (EVERY'[dtac spec, etac impE] 1);
by  (etac (BufAC_Asm_antiton RS antitonPD) 1);
by  (etac is_ub_thelub 1);
by (smp_tac 3 1);
by (dtac is_ub_thelub 1);
by (mp_tac 1);
by (mp_tac 1);
by (etac mp 1);
by (dtac (BufAC_Cmt_iterate_all RS iffD1) 1);
by (etac spec 1);
qed "adm_BufAC";



(**** Buf_Eq_imp_AC by induction **********************************************)

(*adm_BufAC_Asm,BufAC_Asm_antiton,adm_non_BufAC_Asm,BufAC_Asm_cong,
  BufAC_Cmt_2stream_monoP,adm_BufAC,BufAC_Cmt_d_req*)
Goalw [BufAC_def] "BufEq <= BufAC";
by (rtac subsetI 1);
by (Simp_tac 1);
by (rtac allI 1);
by (rtac fstream_ind2 1);
back();
by (   etac adm_BufAC 1);
by (  Safe_tac);
by (   etac BufAC_Cmt_empty 1);
by (  etac BufAC_Cmt_d 1);
by ( dtac BufAC_Asm_prefix2 1);
by ( contr_tac 1);
by (fast_tac (claset() addIs [BufAC_Cmt_d_req, BufAC_Asm_prefix2]) 1);
qed "Buf_Eq_imp_AC";

(**** new approach for admissibility, reduces itself to absurdity *************)

Goal "adm (\\<lambda>x. x\\<in>BufAC_Asm)";
by(rtac def_gfp_admI 1);
by(rtac BufAC_Asm_def 1);
b y Safe_tac;
b y rewtac BufAC_Asm_F_def;
b y Safe_tac;
b y etac swap 1;
b y dtac (fstream_exhaust_eq RS iffD1) 1;
b y Clarsimp_tac 1;
b y datac fstream_lub_lemma 1 1;
b y Clarify_tac 1;
b y eres_inst_tac [("x","j")] all_dupE 1;
b y Asm_full_simp_tac 1;
b y dtac (BufAC_Asm_d2) 1;
b y Clarify_tac 1;
b y Simp_tac 1;
b y rtac disjCI 1;
b y etac swap 1;
b y dtac (fstream_exhaust_eq RS iffD1) 1;
b y Clarsimp_tac 1;
b y datac fstream_lub_lemma 1 1;
b y Clarsimp_tac 1;
b y simp_tac (HOL_basic_ss addsimps (ex_simps@all_simps RL[sym])) 1;
b y res_inst_tac [("x","Xa")] exI 1;
br allI 1;
b y rotate_tac ~1 1;
b y eres_inst_tac [("x","i")] allE 1;
b y Clarsimp_tac 1;
b y eres_inst_tac [("x","jb")] allE 1;
b y Clarsimp_tac 1;
b y eres_inst_tac [("x","jc")] allE 1;
by (clarsimp_tac (claset() addSDs [BufAC_Asm_d3], simpset()) 1);
qed "adm_BufAC_Asm";

Goal "adm (\\<lambda>u. u \\<notin> BufAC_Asm)"; (* uses antitonP *)
by (rtac def_gfp_adm_nonP 1);
by (rtac BufAC_Asm_def 1);
b y rewtac BufAC_Asm_F_def;
b y Safe_tac;
b y etac swap 1;
b y dtac (fstream_exhaust_eq RS iffD1) 1;
b y Clarsimp_tac 1;
b y ftac fstream_prefix 1;
b y Clarsimp_tac 1;
b y ftac BufAC_Asm_d2 1;
b y Clarsimp_tac 1;
b y rotate_tac ~1 1;
b y etac contrapos_pp 1;
b y dtac (fstream_exhaust_eq RS iffD1) 1;
b y Clarsimp_tac 1;
b y ftac fstream_prefix 1;
b y Clarsimp_tac 1;
b y ftac BufAC_Asm_d3 1;
b y Force_tac 1;
qed "adm_non_BufAC_Asm";

Goal "f \\<in> BufEq \\<Longrightarrow> adm (\\<lambda>u. u \\<in> BufAC_Asm \\<longrightarrow> (u, f\\<cdot>u) \\<in> BufAC_Cmt)";
by(rtac triv_admI 1);
by(Clarify_tac 1);
by(eatac Buf_Eq_imp_AC_lemma 1 1); 
      (* this is what we originally aimed to show, using admissibilty :-( *)
qed "adm_BufAC";
