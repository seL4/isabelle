(*  Title: 	HOLCF/FOCUS/Fstream.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
*)

Goal "a = Def d \\<Longrightarrow> a\\<sqsubseteq>b \\<Longrightarrow> b = Def d";
by (rtac (flat_eq RS iffD1 RS sym) 1);
by (rtac Def_not_UU 1);
by (dtac antisym_less_inverse 1);
by (eatac (conjunct2 RS trans_less) 1 1);
qed "Def_maximal";


section "fscons";

Goalw [fscons_def] "a~>s = Def a && s";
by (Simp_tac 1);
qed "fscons_def2";

qed_goal "fstream_exhaust" thy "x = UU |  (? a y. x = a~> y)" (fn _ => [
	simp_tac (simpset() addsimps [fscons_def2]) 1,
	cut_facts_tac [stream.exhaust] 1,
	fast_tac (claset() addDs [not_Undef_is_Def RS iffD1]) 1]);

qed_goal "fstream_cases" thy "[| x = UU ==> P; !!a y. x = a~> y ==> P |] ==> P" 
 (fn prems => [
	cut_facts_tac [fstream_exhaust] 1,
	etac disjE 1,
	 eresolve_tac prems 1,
	REPEAT(etac exE 1),
	eresolve_tac prems 1]);

fun fstream_case_tac s i = res_inst_tac [("x",s)] fstream_cases i
			  THEN hyp_subst_tac i THEN hyp_subst_tac (i+1);

qed_goal "fstream_exhaust_eq" thy "(x ~= UU) = (? a y. x = a~> y)" (fn _ => [
	simp_tac(simpset() addsimps [fscons_def2,stream_exhaust_eq]) 1,
	fast_tac (claset() addDs [not_Undef_is_Def RS iffD1] addEs [DefE]) 1]);


qed_goal "fscons_not_empty" thy "a~> s ~= <>" (fn _ => [
	stac fscons_def2 1,
        Simp_tac 1]);
Addsimps[fscons_not_empty];


qed_goal "fscons_inject" thy "(a~> s = b~> t) = (a = b &  s = t)" (fn _ => [
	simp_tac (HOL_ss addsimps [fscons_def2]) 1,
	stac (hd lift.inject RS sym) 1, (*2*back();*)
        Simp_tac 1]);
Addsimps[fscons_inject];

qed_goal "fstream_prefix" thy "a~> s << t ==> ? tt. t = a~> tt &  s << tt" (fn prems =>[
	cut_facts_tac prems 1,
	stream_case_tac "t" 1,
	 cut_facts_tac [fscons_not_empty] 1,
	 fast_tac (HOL_cs addDs [eq_UU_iff RS iffD2]) 1,
	asm_full_simp_tac (HOL_ss addsimps [fscons_def2]) 1,
	dtac stream_flat_prefix 1,
	rtac Def_not_UU 1,
	fast_tac HOL_cs 1]);

qed_goal "fstream_prefix'" thy
	"x << a~> z = (x = <> |  (? y. x = a~> y &  y << z))" (fn _ => [
	simp_tac(HOL_ss addsimps [fscons_def2, Def_not_UU RS stream_prefix'])1,
	Step_tac 1,
	 ALLGOALS(etac swap),
	 fast_tac (HOL_cs addIs [refl_less] addEs [DefE]) 2,
	rtac Lift_cases 1,
	 contr_tac 1,
	Step_tac 1,
	dtac (Def_inject_less_eq RS iffD1) 1,
	Fast_tac 1]);
Addsimps[fstream_prefix'];

(* ------------------------------------------------------------------------- *)

section "ft & rt";

bind_thm("ft_empty",hd stream.sel_rews);
qed_goalw "ft_fscons" thy [fscons_def] "ft\\<cdot>(m~> s) = Def m" (fn _ => [
	(Simp_tac 1)]);
Addsimps[ft_fscons];

bind_thm("rt_empty",hd (tl stream.sel_rews));
qed_goalw "rt_fscons" thy [fscons_def] "rt\\<cdot>(m~> s) = s" (fn _ => [
	(Simp_tac 1)]);
Addsimps[rt_fscons];

qed_goalw "ft_eq" thy [fscons_def] "(ft\\<cdot>s = Def a) = (? t. s = a~> t)" (K [
	Simp_tac 1,
	Safe_tac,
	 etac subst 1,
	 rtac exI 1,
	 rtac (surjectiv_scons RS sym) 1,
	Simp_tac 1]);
Addsimps[ft_eq];

Goal "(d\\<leadsto>y = x) = (ft\\<cdot>x = Def d & rt\\<cdot>x = y)";
by Auto_tac;
qed "surjective_fscons_lemma";
Goal "ft\\<cdot>x = Def d \\<Longrightarrow> d\\<leadsto>rt\\<cdot>x = x";
by (asm_simp_tac (simpset() addsimps [surjective_fscons_lemma]) 1);
qed "surjective_fscons";


(* ------------------------------------------------------------------------- *)

section "take";

qed_goalw "fstream_take_Suc" thy [fscons_def]
	"stream_take (Suc n)\\<cdot>(a~> s) = a~> stream_take n\\<cdot>s" (K [
	Simp_tac 1]);
Addsimps[fstream_take_Suc];


(* ------------------------------------------------------------------------- *)

section "slen";
	
(*bind_thm("slen_empty", slen_empty);*)

qed_goalw "slen_fscons" thy [fscons_def] "#(m~> s) = iSuc (#s)" (fn _ => [
	(Simp_tac 1)]);

qed_goal "slen_fscons_eq" thy 
	"(Fin (Suc n) < #x) = (? a y. x = a~> y & Fin n < #y)" (fn _ => [
	simp_tac (HOL_ss addsimps [fscons_def2, slen_scons_eq]) 1,
	fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1] addEs [DefE]) 1]);

qed_goal "slen_fscons_eq_rev" thy 
	"(#x < Fin (Suc (Suc n))) = (!a y. x ~= a~> y | #y < Fin (Suc n))" (K [
	simp_tac (HOL_ss addsimps [fscons_def2, slen_scons_eq_rev]) 1,
	step_tac (HOL_cs addSEs [DefE]) 1,
	step_tac (HOL_cs addSEs [DefE]) 1,
	step_tac (HOL_cs addSEs [DefE]) 1,
	step_tac (HOL_cs addSEs [DefE]) 1,
	step_tac (HOL_cs addSEs [DefE]) 1,
	step_tac (HOL_cs addSEs [DefE]) 1,
	etac swap 1,
	fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1] addEs [DefE]) 1]);

qed_goal "slen_fscons_less_eq" thy 
	"(#(a~> y) < Fin (Suc (Suc n))) = (#y < Fin (Suc n))" (fn _ => [
	stac slen_fscons_eq_rev 1,
	fast_tac (HOL_cs addSDs [fscons_inject RS iffD1]) 1]);


(* ------------------------------------------------------------------------- *)

section "induction";

qed_goal "fstream_ind" thy 
	"[| adm P; P <>; !!a s. P s ==> P (a~> s) |] ==> P x" (fn prems => [
	cut_facts_tac prems 1,
	etac stream.ind 1,
	 atac 1,
	fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1] 
			 addEs (tl (tl prems) RL [fscons_def2 RS subst])) 1]);

qed_goal "fstream_ind2" thy 
  "[| adm P; P UU; !!a. P (a~> UU); !!a b s. P s ==> P (a~> b~> s) |] ==> P x" (fn prems => [
	cut_facts_tac prems 1,
	etac stream_ind2 1,
	  atac 1,
	fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1] 
			 addIs ([hd(tl(tl prems))]RL[fscons_def2 RS subst]))1,
	fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1] 
			 addEs [hd(tl(tl(tl prems))RL[fscons_def2 RS subst]
						 RL[fscons_def2 RS subst])])1]);


(* ------------------------------------------------------------------------- *)

section "fsfilter";

qed_goalw "fsfilter_empty" thy [fsfilter_def] "A(C)UU = UU" (fn _ => [
	rtac sfilter_empty 1]);

qed_goalw "fsfilter_fscons" thy [fsfilter_def] 
	"A(C)x~> xs = (if x:A then x~> (A(C)xs) else A(C)xs)" (fn _ => [
	simp_tac (simpset() addsimps [fscons_def2,sfilter_scons,If_and_if]) 1]);

qed_goal "fsfilter_emptys" thy "{}(C)x = UU" (fn _ => [
	res_inst_tac [("x","x")] fstream_ind 1,
	  resolve_tac adm_lemmas 1,
	   cont_tacR 1,
	 rtac fsfilter_empty 1,
	asm_simp_tac (simpset()addsimps [fsfilter_fscons]) 1]);

qed_goal "fsfilter_insert" thy "(insert a A)(C)a~> x = a~> ((insert a A)(C)x)" (fn _=> [
	simp_tac (simpset() addsimps [fsfilter_fscons]) 1]);

qed_goal "fsfilter_single_in" thy "{a}(C)a~> x = a~> ({a}(C)x)" (fn _=> [
	rtac fsfilter_insert 1]);

qed_goal "fsfilter_single_out" thy "b ~= a ==> {a}(C)b~> x = ({a}(C)x)" (fn prems => [
	cut_facts_tac prems 1,
	asm_simp_tac (simpset() addsimps[fsfilter_fscons]) 1]);

Goal "\\<lbrakk>chain Y; lub (range Y) = a\\<leadsto>s\\<rbrakk> \\<Longrightarrow> \\<exists>j t. Y j = a\\<leadsto>t";
by (case_tac "max_in_chain i Y" 1);
by  (datac (lub_finch1 RS thelubI RS sym) 1 1);
by  (Force_tac 1);
by (rewtac max_in_chain_def);
by Auto_tac;
by (fatac chain_mono3 1 1);
by (res_inst_tac [("x","Y j")] fstream_cases 1);
by  (Force_tac 1);
by (dres_inst_tac [("x","j")] is_ub_thelub 1);
by (Force_tac 1);
qed "fstream_lub_lemma1";

Goal "\\<lbrakk>chain Y; lub (range Y) = a\\<leadsto>s\\<rbrakk> \\<Longrightarrow> (\\<exists>j t. Y j = a\\<leadsto>t) & (\\<exists>X. chain X & (!i. ? j. Y j = a\\<leadsto>X i) & lub (range X) = s)";
by (fatac fstream_lub_lemma1 1 1);
by (Clarsimp_tac 1);
by (res_inst_tac [("x","%i. rt\\<cdot>(Y(i+j))")] exI 1);
by (rtac conjI 1);
by  (etac (chain_shift RS chain_monofun) 1);
by Safe_tac;
by  (dres_inst_tac [("x","j"),("y","i+j")] chain_mono3 1);
by   (Simp_tac 1);
by  (Asm_full_simp_tac 1);
by  (res_inst_tac [("x","i+j")] exI 1);
by  (dtac fstream_prefix 1);
by  (Clarsimp_tac 1);
by  (stac (contlub_cfun RS sym) 1);
by   (rtac chainI 1);
by   (Fast_tac 1);
by  (etac chain_shift 1);
by (stac (lub_const RS thelubI) 1);
by (stac lub_range_shift 1);
by  (atac 1);
by (Asm_simp_tac 1);
qed "fstream_lub_lemma";


