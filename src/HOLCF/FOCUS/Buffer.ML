(*  Title: 	HOLCF/FOCUS/Buffer.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

val set_cong = prove_goal Set.thy "!!X. A = B ==> (x:A) = (x:B)" (K [
	etac subst 1, rtac refl 1]);

fun B_prover s tac eqs = prove_goal thy s (fn prems => [cut_facts_tac prems 1, 
	tac 1, auto_tac (claset(), simpset() addsimps eqs)]);

fun prove_forw  s thm     = B_prover s (dtac (thm RS iffD1)) [];
fun prove_backw s thm eqs = B_prover s (rtac (thm RS iffD2)) eqs;


(**** BufEq *******************************************************************)

val mono_BufEq_F = prove_goalw thy [mono_def, BufEq_F_def] 
		"mono BufEq_F" (K [Fast_tac 1]);

val BufEq_fix = mono_BufEq_F RS (BufEq_def RS def_gfp_unfold);

val BufEq_unfold = prove_goal thy "(f:BufEq) = (!d. f\\<cdot>(Md d\\<leadsto><>) = <> & \
		\(!x. ? ff:BufEq. f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x) = d\\<leadsto>(ff\\<cdot>x)))" (K [
	stac (BufEq_fix RS set_cong) 1,
	rewtac BufEq_F_def,
	Asm_full_simp_tac 1]);

val Buf_f_empty = prove_forw "f:BufEq \\<Longrightarrow> f\\<cdot><> = <>" BufEq_unfold;
val Buf_f_d     = prove_forw "f:BufEq \\<Longrightarrow> f\\<cdot>(Md d\\<leadsto><>) = <>" BufEq_unfold;
val Buf_f_d_req = prove_forw 
	"f:BufEq \\<Longrightarrow> \\<exists>ff. ff:BufEq \\<and> f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x) = d\\<leadsto>ff\\<cdot>x" BufEq_unfold;


(**** BufAC_Asm ***************************************************************)

val mono_BufAC_Asm_F = prove_goalw thy [mono_def, BufAC_Asm_F_def]
		"mono BufAC_Asm_F" (K [Fast_tac 1]);

val BufAC_Asm_fix = mono_BufAC_Asm_F RS (BufAC_Asm_def RS def_gfp_unfold);

val BufAC_Asm_unfold = prove_goal thy "(s:BufAC_Asm) = (s = <> | (? d x. \
\       s = Md d\\<leadsto>x & (x = <> | (ft\\<cdot>x = Def \\<bullet> & (rt\\<cdot>x):BufAC_Asm))))" (K [
				stac (BufAC_Asm_fix RS set_cong) 1,
				rewtac BufAC_Asm_F_def,
				Asm_full_simp_tac 1]);

val BufAC_Asm_empty = prove_backw "<>     :BufAC_Asm" BufAC_Asm_unfold [];
val BufAC_Asm_d     = prove_backw "Md d\\<leadsto><>:BufAC_Asm" BufAC_Asm_unfold [];
val BufAC_Asm_d_req = prove_backw "x:BufAC_Asm ==> Md d\\<leadsto>\\<bullet>\\<leadsto>x:BufAC_Asm"
							   BufAC_Asm_unfold [];
val BufAC_Asm_prefix2 = prove_forw "a\\<leadsto>b\\<leadsto>s:BufAC_Asm ==> s:BufAC_Asm"
							 BufAC_Asm_unfold;


(**** BBufAC_Cmt **************************************************************)

val mono_BufAC_Cmt_F = prove_goalw thy [mono_def, BufAC_Cmt_F_def] 
		"mono BufAC_Cmt_F" (K [Fast_tac 1]);

val BufAC_Cmt_fix = mono_BufAC_Cmt_F RS (BufAC_Cmt_def RS def_gfp_unfold);

val BufAC_Cmt_unfold = prove_goal thy "((s,t):BufAC_Cmt) = (!d x. \
    \(s = <>       -->      t = <>) & \
    \(s = Md d\\<leadsto><>  -->      t = <>) & \
    \(s = Md d\\<leadsto>\\<bullet>\\<leadsto>x --> ft\\<cdot>t = Def d & (x, rt\\<cdot>t):BufAC_Cmt))" (K [
	stac (BufAC_Cmt_fix RS set_cong) 1,
	rewtac BufAC_Cmt_F_def,
	Asm_full_simp_tac 1]);

val BufAC_Cmt_empty = prove_backw "f:BufEq ==> (<>, f\\<cdot><>):BufAC_Cmt"
				BufAC_Cmt_unfold [Buf_f_empty];

val BufAC_Cmt_d = prove_backw "f:BufEq ==> (a\\<leadsto>\\<bottom>, f\\<cdot>(a\\<leadsto>\\<bottom>)):BufAC_Cmt" 
				BufAC_Cmt_unfold [Buf_f_d];

val BufAC_Cmt_d2 = prove_forw 
 "(Md d\\<leadsto>\\<bottom>, f\\<cdot>(Md d\\<leadsto>\\<bottom>)):BufAC_Cmt ==> f\\<cdot>(Md d\\<leadsto>\\<bottom>) = \\<bottom>" BufAC_Cmt_unfold;
val BufAC_Cmt_d3 = prove_forw 
"(Md d\\<leadsto>\\<bullet>\\<leadsto>x, f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x)):BufAC_Cmt ==> (x, rt\\<cdot>(f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x))):BufAC_Cmt"
							BufAC_Cmt_unfold;

val BufAC_Cmt_d32 = prove_forw 
"(Md d\\<leadsto>\\<bullet>\\<leadsto>x, f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x)):BufAC_Cmt ==> ft\\<cdot>(f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x)) = Def d"
							BufAC_Cmt_unfold;

(**** BufAC *******************************************************************)

Goalw [BufAC_def] "f \\<in> BufAC \\<Longrightarrow> f\\<cdot>(Md d\\<leadsto>\\<bottom>) = \\<bottom>";
by (fast_tac (claset() addIs [BufAC_Cmt_d2, BufAC_Asm_d]) 1);
qed "BufAC_f_d";

Goal "(? ff:B. (!x. f\\<cdot>(a\\<leadsto>b\\<leadsto>x) = d\\<leadsto>ff\\<cdot>x)) = \
   \((!x. ft\\<cdot>(f\\<cdot>(a\\<leadsto>b\\<leadsto>x)) = Def d) & (LAM x. rt\\<cdot>(f\\<cdot>(a\\<leadsto>b\\<leadsto>x))):B)";
(*  this is an instance (though unification cannot handle this) of
Goal "(? ff:B. (!x. f\\<cdot>x = d\\<leadsto>ff\\<cdot>x)) = \
   \((!x. ft\\<cdot>(f\\<cdot>x) = Def d) & (LAM x. rt\\<cdot>(f\\<cdot>x)):B)";*)
by Safe_tac;
by (  res_inst_tac [("P","(%x. x:B)")] ssubst 2);
by (   atac 3);
by (  rtac ext_cfun 2);
by (  dtac spec 2);
by (  dres_inst_tac [("f","rt")] cfun_arg_cong 2);
by (  Asm_full_simp_tac 2);
by ( Full_simp_tac 2);
by (rtac bexI 2);
by Auto_tac;
by (dtac spec 1);
by (etac exE 1);;
by (etac ssubst 1);
by (Simp_tac 1);
qed "ex_elim_lemma";

Goalw [BufAC_def] "f\\<in>BufAC \\<Longrightarrow> \\<exists>ff\\<in>BufAC. \\<forall>x. f\\<cdot>(Md d\\<leadsto>\\<bullet>\\<leadsto>x) = d\\<leadsto>ff\\<cdot>x";
by (rtac (ex_elim_lemma RS iffD2) 1);
by Safe_tac;
by  (fast_tac (claset() addIs [BufAC_Cmt_d32 RS Def_maximal, 
             monofun_cfun_arg,	BufAC_Asm_empty RS BufAC_Asm_d_req]) 1);
by (auto_tac (claset() addIs [BufAC_Cmt_d3, BufAC_Asm_d_req],simpset()));
qed "BufAC_f_d_req";


(**** BufSt *******************************************************************)

val mono_BufSt_F = prove_goalw thy [mono_def, BufSt_F_def] 
		"mono BufSt_F" (K [Fast_tac 1]);

val BufSt_P_fix = mono_BufSt_F RS (BufSt_P_def RS def_gfp_unfold);

val BufSt_P_unfold = prove_goal thy "(h:BufSt_P) = (!s. h s\\<cdot><> = <> & \
	 \ (!d x. h \\<currency>     \\<cdot>(Md d\\<leadsto>x)   =    h (Sd d)\\<cdot>x & \
  \   (? hh:BufSt_P. h (Sd d)\\<cdot>(\\<bullet>\\<leadsto>x)   = d\\<leadsto>(hh \\<currency>    \\<cdot>x))))" (K [
	stac (BufSt_P_fix RS set_cong) 1,
	rewtac BufSt_F_def,
	Asm_full_simp_tac 1]);

val BufSt_P_empty = prove_forw "h:BufSt_P ==> h s     \\<cdot> <>       = <>" 
			BufSt_P_unfold;
val BufSt_P_d     = prove_forw "h:BufSt_P ==> h  \\<currency>    \\<cdot>(Md d\\<leadsto>x) = h (Sd d)\\<cdot>x"
			BufSt_P_unfold;
val BufSt_P_d_req = prove_forw "h:BufSt_P ==> \\<exists>hh\\<in>BufSt_P. \
				         \ h (Sd d)\\<cdot>(\\<bullet>   \\<leadsto>x) = d\\<leadsto>(hh \\<currency>    \\<cdot>x)"
			BufSt_P_unfold;


(**** Buf_AC_imp_Eq ***********************************************************)

Goalw [BufEq_def] "BufAC \\<subseteq> BufEq";
by (rtac gfp_upperbound 1);
by (rewtac BufEq_F_def);
by Safe_tac;
by  (etac BufAC_f_d 1);
by (dtac BufAC_f_d_req 1);
by (Fast_tac 1);
qed "Buf_AC_imp_Eq";


(**** Buf_Eq_imp_AC by coinduction ********************************************)

Goal "\\<forall>s f ff. f\\<in>BufEq \\<longrightarrow> ff\\<in>BufEq \\<longrightarrow> \
\ s\\<in>BufAC_Asm \\<longrightarrow> stream_take n\\<cdot>(f\\<cdot>s) = stream_take n\\<cdot>(ff\\<cdot>s)";
by (induct_tac "n" 1);
by  (Simp_tac 1);
by (strip_tac 1);
by (dtac (BufAC_Asm_unfold RS iffD1) 1);
by Safe_tac;
by   (asm_simp_tac (simpset() addsimps [Buf_f_empty]) 1);
by  (asm_simp_tac (simpset() addsimps [Buf_f_d]) 1);
by (dtac (ft_eq RS iffD1) 1);
by (Clarsimp_tac 1);
by (REPEAT(dtac Buf_f_d_req 1));
by Safe_tac;
by (REPEAT(etac ssubst 1));
by (Simp_tac 1);
by (Fast_tac 1);
qed_spec_mp "BufAC_Asm_cong_lemma";
Goal "\\<lbrakk>f \\<in> BufEq; ff \\<in> BufEq; s \\<in> BufAC_Asm\\<rbrakk> \\<Longrightarrow> f\\<cdot>s = ff\\<cdot>s";
by (resolve_tac stream.take_lemmas 1);
by (eatac BufAC_Asm_cong_lemma 2 1);
qed "BufAC_Asm_cong";

Goalw [BufAC_Cmt_def] "\\<lbrakk>f \\<in> BufEq; x \\<in> BufAC_Asm\\<rbrakk> \\<Longrightarrow> (x, f\\<cdot>x) \\<in> BufAC_Cmt";
by (rotate_tac ~1 1);
by (etac weak_coinduct_image 1);
by (rewtac BufAC_Cmt_F_def);
by Safe_tac;
by    (etac Buf_f_empty 1);
by   (etac Buf_f_d 1);
by  (dtac Buf_f_d_req 1);
by  (Clarsimp_tac 1);
by  (etac exI 1);
by (dtac BufAC_Asm_prefix2 1);
by (ftac Buf_f_d_req 1);
by (Clarsimp_tac 1);
by (etac ssubst 1);
by (Simp_tac 1);
by (datac BufAC_Asm_cong 2 1);
by (etac subst 1);
by (etac imageI 1);
qed "Buf_Eq_imp_AC_lemma";
Goalw [BufAC_def] "BufEq \\<subseteq> BufAC";
by (Clarify_tac 1);
by (eatac Buf_Eq_imp_AC_lemma 1 1);
qed "Buf_Eq_imp_AC";

(**** Buf_Eq_eq_AC ************************************************************)

val Buf_Eq_eq_AC = Buf_AC_imp_Eq RS (Buf_Eq_imp_AC RS subset_antisym);


(**** alternative (not strictly) stronger version of Buf_Eq *******************)

val Buf_Eq_alt_imp_Eq = prove_goalw thy [BufEq_def,BufEq_alt_def] 
	"BufEq_alt \\<subseteq> BufEq" (K [
	rtac gfp_mono 1,
	rewtac BufEq_F_def,
	Fast_tac 1]);

(* direct proof of "BufEq \\<subseteq> BufEq_alt" seems impossible *)


Goalw [BufEq_alt_def] "BufAC <= BufEq_alt";
by (rtac gfp_upperbound 1);
by (fast_tac (claset() addEs [BufAC_f_d, BufAC_f_d_req]) 1);
qed "Buf_AC_imp_Eq_alt";

bind_thm ("Buf_Eq_imp_Eq_alt", 
  subset_trans OF [Buf_Eq_imp_AC, Buf_AC_imp_Eq_alt]);

bind_thm ("Buf_Eq_alt_eq", 
 subset_antisym OF [Buf_Eq_alt_imp_Eq, Buf_Eq_imp_Eq_alt]);


(**** Buf_Eq_eq_St ************************************************************)

Goalw [BufSt_def, BufEq_def] "BufSt <= BufEq";
by (rtac gfp_upperbound 1);
by (rewtac BufEq_F_def);
by Safe_tac;
by ( asm_simp_tac (simpset() addsimps [BufSt_P_d, BufSt_P_empty]) 1);
by (asm_simp_tac (simpset() addsimps [BufSt_P_d]) 1);
by (dtac BufSt_P_d_req 1);
by (Force_tac 1);
qed "Buf_St_imp_Eq";

Goalw [BufSt_def, BufSt_P_def] "BufEq <= BufSt";
by Safe_tac;
by (EVERY'[rename_tac "f", res_inst_tac 
        [("x","\\<lambda>s. case s of Sd d => \\<Lambda> x. f\\<cdot>(Md d\\<leadsto>x)| \\<currency> => f")] bexI] 1);
by ( Simp_tac 1);
by (etac weak_coinduct_image 1);
by (rewtac BufSt_F_def); 
by (Simp_tac 1);
by Safe_tac;
by (  EVERY'[rename_tac "s", induct_tac "s"] 1);
by (   asm_simp_tac (simpset() addsimps [Buf_f_d]) 1);
by (  asm_simp_tac (simpset() addsimps [Buf_f_empty]) 1);
by ( Simp_tac 1);
by (Simp_tac 1);
by (EVERY'[rename_tac"f d x",dres_inst_tac[("d","d"),("x","x")] Buf_f_d_req] 1);
by Auto_tac;
qed "Buf_Eq_imp_St";

bind_thm ("Buf_Eq_eq_St", Buf_St_imp_Eq RS (Buf_Eq_imp_St RS subset_antisym));



