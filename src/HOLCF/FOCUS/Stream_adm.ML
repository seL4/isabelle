(*  Title: 	HOLCF/ex/Stream_adm.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(* ----------------------------------------------------------------------- *)

val down_cont_def = thm "down_cont_def";
val INTER_down_iterate_is_gfp = thm "INTER_down_iterate_is_gfp";

section "admissibility";

Goal "[| chain Y; !i. P (Y i);\
\(!!Y. [| chain Y; !i. P (Y i); !k. ? j. Fin k < #((Y j)::'a::flat stream)|]\
\ ==> P(lub (range Y))) |] ==> P(lub (range Y))";
by (cut_facts_tac (premises()) 1);
by (eatac increasing_chain_adm_lemma 1 1);
by (etac thin_rl 1);
by (EVERY'[eresolve_tac (premises()), atac, etac thin_rl] 1);
by (rtac allI 1);
by (case_tac "!j. stream_finite (Y j)" 1);
by ( rtac (thm "chain_incr") 1);
by ( rtac allI 1);
by ( dtac spec 1);
by ( Safe_tac);
by ( rtac exI 1);
by ( rtac slen_strict_mono 1);
by (   etac spec 1);
by (  atac 1);
by ( atac 1);
by (dtac (not_ex RS iffD1) 1);
by (stac slen_infinite 1);
by (etac thin_rl 1);
by (dtac spec 1);
by (fold_goals_tac [thm "ile_def"]);
by (etac (thm "ile_iless_trans" RS (thm "Infty_eq" RS iffD1)) 1);
by (Simp_tac 1);
qed "flatstream_adm_lemma";


(* should be without reference to stream length? *)
Goalw [adm_def] "[|(!!Y. [| chain Y; !i. P (Y i); \
\!k. ? j. Fin k < #((Y j)::'a::flat stream)|] ==> P(lub (range Y)))|]==> adm P";
by (strip_tac 1);
by (eatac flatstream_adm_lemma 1 1);
by (EVERY'[eresolve_tac (premises()), atac, atac] 1);
qed "flatstream_admI";


(* context (theory "Nat_InFinity");*)
Goal "Fin (i + j) <= x ==> Fin i <= x";
by (rtac (thm "ile_trans") 1);
by  (atac 2);
by (Simp_tac 1);
qed "ile_lemma";

Goalw [stream_monoP_def]
"!!X. stream_monoP F ==> !i. ? l. !x y. \
\ Fin l <= #x --> (x::'a::flat stream) << y --> x:down_iterate F i --> y:down_iterate F i";
by (safe_tac HOL_cs);
by (res_inst_tac [("x","i*ia")] exI 1);
by (induct_tac "ia" 1);
by ( Simp_tac 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac allE 1 THEN etac all_dupE 1 THEN dtac mp 1 THEN etac ile_lemma 1);
by (dres_inst_tac [("P","%x. x")] subst 1 THEN atac 1);
by (etac allE 1 THEN dtac mp 1 THEN rtac ile_lemma 1);
by ( etac (thm "ile_trans") 1);
by ( etac slen_mono 1);
by (etac ssubst 1);
by (safe_tac HOL_cs);
by ( eatac (ile_lemma RS slen_take_lemma3 RS subst) 2 1);
by (etac allE 1);
by (etac allE 1);
by (dtac mp 1);
by ( etac slen_rt_mult 1);
by (dtac mp 1);
by (etac monofun_rt_mult 1);
by (mp_tac 1); 
by (atac 1);
qed "stream_monoP2I";

Goal "[| !i. ? l. !x y. \
\Fin l <= #x --> (x::'a::flat stream) << y --> x:down_iterate F i --> y:down_iterate F i;\
\   down_cont F |] ==> adm (%x. x:gfp F)";
byev[	etac (INTER_down_iterate_is_gfp RS ssubst) 1, (* cont *)
	Simp_tac 1,
	resolve_tac adm_lemmas 1,
	rtac flatstream_admI 1,
	etac allE 1,
	etac exE 1,
	etac allE 1 THEN etac exE 1,
	etac allE 1 THEN etac allE 1 THEN dtac mp 1, (* stream_monoP *)
	 dtac (thm "ileI1") 1,
	 dtac (thm "ile_trans") 1,
	  rtac (thm "ile_iSuc") 1,
	 dtac (thm "iSuc_ile_mono" RS iffD1) 1,
	 atac 1,
	dtac mp 1,
	 etac is_ub_thelub 1,
	Fast_tac 1];
qed "stream_monoP2_gfp_admI";

bind_thm("fstream_gfp_admI",stream_monoP2I RS stream_monoP2_gfp_admI);

qed_goalw "stream_antiP2I" thy [stream_antiP_def]
"!!X. [|stream_antiP (F::(('a::flat stream)set => ('a stream set)))|]\
\ ==> !i x y. x << y --> y:down_iterate F i --> x:down_iterate F i" (K [
	rtac allI 1,
	induct_tac "i" 1,
	 Simp_tac 1,
	Simp_tac 1,
	strip_tac 1,
	etac allE 1 THEN etac all_dupE 1 THEN etac exE 1 THEN etac exE 1,
	etac conjE 1,
	case_tac "#x < Fin i" 1,
	 fast_tac HOL_cs 1,
	fold_goals_tac [thm "ile_def"],
	mp_tac 1,
	etac all_dupE 1 THEN dtac mp 1 THEN rtac refl_less 1,
	etac ssubst 1,
        etac allE 1 THEN mp_tac 1,
	dres_inst_tac [("P","%x. x")] subst 1 THEN atac 1,
	etac conjE 1 THEN rtac conjI 1,
	 etac (slen_take_lemma3 RS ssubst) 1 THEN atac 1,
	 atac 1,
	etac allE 1 THEN etac allE 1 THEN dtac mp 1 THEN etac monofun_rt_mult 1,
	mp_tac 1,
	atac 1]);

qed_goalw "stream_antiP2_non_gfp_admI" thy [adm_def]
"!!X. [|!i x y. x << y --> y:down_iterate F i --> x:down_iterate F i; down_cont F |] \
\ ==> adm (%u. ~ u:gfp F)" (K [
	asm_simp_tac (simpset() addsimps [INTER_down_iterate_is_gfp]) 1,
	fast_tac (claset() addSDs [is_ub_thelub]) 1]);

bind_thm ("fstream_non_gfp_admI", stream_antiP2I RS 
				stream_antiP2_non_gfp_admI);



(**new approach for adm********************************************************)

section "antitonP";

Goalw [antitonP_def] "[| antitonP P; y:P; x<<y |] ==> x:P";
by Auto_tac;
qed "antitonPD";

Goalw [antitonP_def]"!x y. y:P --> x<<y --> x:P ==> antitonP P";
by (Fast_tac 1);
qed "antitonPI";

Goalw [adm_def] "antitonP P ==> adm (%u. u~:P)";
by (auto_tac (claset() addDs [antitonPD] addEs [is_ub_thelub],simpset()));
qed "antitonP_adm_non_P";

Goal "P \\<equiv> gfp F \\<Longrightarrow> {y. \\<exists>x::'a::pcpo. y \\<sqsubseteq> x \\<and> x \\<in> P} \\<subseteq> F {y. \\<exists>x. y \\<sqsubseteq> x \\<and> x \\<in> P} \\<Longrightarrow> \
\ adm (\\<lambda>u. u\\<notin>P)";
by (Asm_full_simp_tac 1);
by (rtac antitonP_adm_non_P 1);
by (rtac antitonPI 1);
by (dtac gfp_upperbound 1);
by (Fast_tac 1);
qed "def_gfp_adm_nonP";

Goalw [adm_def] 
"{lub (range Y) |Y. chain Y & (\\<forall>i. Y i \\<in> P)} \\<subseteq> P \\<Longrightarrow> adm (\\<lambda>x. x\\<in>P)";
by (Fast_tac 1);
qed "adm_set";

Goal "P \\<equiv> gfp F \\<Longrightarrow> {lub (range Y) |Y. chain Y \\<and> (\\<forall>i. Y i \\<in> P)} \\<subseteq> \
\ F {lub (range Y) |Y. chain Y \\<and> (\\<forall>i. Y i \\<in> P)} \\<Longrightarrow> adm (\\<lambda>x. x\\<in>P)";
by (Asm_full_simp_tac 1);
by (rtac adm_set 1);
by (etac gfp_upperbound 1);
qed "def_gfp_admI";
