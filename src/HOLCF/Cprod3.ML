(*  Title:      HOLCF/Cprod3
    ID:         $Id$
    Author:     Franz Regensburger

Class instance of * for class pcpo and cpo.
*)

(* for compatibility with old HOLCF-Version *)
Goal "UU = (UU,UU)";
by (simp_tac (HOL_ss addsimps [UU_def,UU_cprod_def]) 1);
qed "inst_cprod_pcpo";

(* ------------------------------------------------------------------------ *)
(* continuity of (_,_) , fst, snd                                           *)
(* ------------------------------------------------------------------------ *)

Goal 
"chain(Y::(nat=>'a::cpo)) ==>\
\ (lub(range(Y)),(x::'b::cpo)) =\
\ (lub(range(%i. fst(Y i,x))),lub(range(%i. snd(Y i,x))))";
by (res_inst_tac [("f1","Pair")] (arg_cong RS cong) 1);
by (rtac lub_equal 1);
by (atac 1);
by (rtac (monofun_fst RS ch2ch_monofun) 1);
by (rtac ch2ch_fun 1);
by (rtac (monofun_pair1 RS ch2ch_monofun) 1);
by (atac 1);
by (rtac allI 1);
by (Simp_tac 1);
by (rtac sym 1);
by (Simp_tac 1);
by (rtac (lub_const RS thelubI) 1);
qed "Cprod3_lemma1";

Goal "contlub(Pair)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (stac (lub_fun RS thelubI) 1);
by (etac (monofun_pair1 RS ch2ch_monofun) 1);
by (rtac trans 1);
by (rtac (thelub_cprod RS sym) 2);
by (rtac ch2ch_fun 2);
by (etac (monofun_pair1 RS ch2ch_monofun) 2);
by (etac Cprod3_lemma1 1);
qed "contlub_pair1";

Goal 
"chain(Y::(nat=>'a::cpo)) ==>\
\ ((x::'b::cpo),lub(range Y)) =\
\ (lub(range(%i. fst(x,Y i))),lub(range(%i. snd(x, Y i))))";
by (res_inst_tac [("f1","Pair")] (arg_cong RS cong) 1);
by (rtac sym 1);
by (Simp_tac 1);
by (rtac (lub_const RS thelubI) 1);
by (rtac lub_equal 1);
by (atac 1);
by (rtac (monofun_snd RS ch2ch_monofun) 1);
by (rtac (monofun_pair2 RS ch2ch_monofun) 1);
by (atac 1);
by (rtac allI 1);
by (Simp_tac 1);
qed "Cprod3_lemma2";

Goal "contlub(Pair(x))";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac trans 1);
by (rtac (thelub_cprod RS sym) 2);
by (etac (monofun_pair2 RS ch2ch_monofun) 2);
by (etac Cprod3_lemma2 1);
qed "contlub_pair2";

Goal "cont(Pair)";
by (rtac monocontlub2cont 1);
by (rtac monofun_pair1 1);
by (rtac contlub_pair1 1);
qed "cont_pair1";

Goal "cont(Pair(x))";
by (rtac monocontlub2cont 1);
by (rtac monofun_pair2 1);
by (rtac contlub_pair2 1);
qed "cont_pair2";

Goal "contlub(fst)";
by (rtac contlubI 1);
by (strip_tac 1);
by (stac (lub_cprod RS thelubI) 1);
by (atac 1);
by (Simp_tac 1);
qed "contlub_fst";

Goal "contlub(snd)";
by (rtac contlubI 1);
by (strip_tac 1);
by (stac (lub_cprod RS thelubI) 1);
by (atac 1);
by (Simp_tac 1);
qed "contlub_snd";

Goal "cont(fst)";
by (rtac monocontlub2cont 1);
by (rtac monofun_fst 1);
by (rtac contlub_fst 1);
qed "cont_fst";

Goal "cont(snd)";
by (rtac monocontlub2cont 1);
by (rtac monofun_snd 1);
by (rtac contlub_snd 1);
qed "cont_snd";

(* 
 -------------------------------------------------------------------------- 
 more lemmas for Cprod3.thy 
 
 -------------------------------------------------------------------------- 
*)

(* ------------------------------------------------------------------------ *)
(* convert all lemmas to the continuous versions                            *)
(* ------------------------------------------------------------------------ *)

Goalw [cpair_def]
        "(LAM x y.(x,y))$a$b = (a,b)";
by (stac beta_cfun 1);
by (simp_tac (simpset() addsimps [cont_pair1,cont_pair2,cont2cont_CF1L]) 1);
by (stac beta_cfun 1);
by (rtac cont_pair2 1);
by (rtac refl 1);
qed "beta_cfun_cprod";

Goalw [cpair_def]
        " <a,b>=<aa,ba>  ==> a=aa & b=ba";
by (dtac (beta_cfun_cprod RS subst) 1);
by (dtac (beta_cfun_cprod RS subst) 1);
by (etac Pair_inject 1);
by (fast_tac HOL_cs 1);
qed "inject_cpair";

Goalw [cpair_def] "UU = <UU,UU>";
by (rtac sym 1);
by (rtac trans 1);
by (rtac beta_cfun_cprod 1);
by (rtac sym 1);
by (rtac inst_cprod_pcpo 1);
qed "inst_cprod_pcpo2";

Goal
 "<a,b> = UU ==> a = UU & b = UU";
by (dtac (inst_cprod_pcpo2 RS subst) 1);
by (etac inject_cpair 1);
qed "defined_cpair_rev";

Goalw [cpair_def]
        "? a b. z=<a,b>";
by (rtac PairE 1);
by (rtac exI 1);
by (rtac exI 1);
by (etac (beta_cfun_cprod RS ssubst) 1);
qed "Exh_Cprod2";

val prems = Goalw [cpair_def] "[|!!x y. [|p=<x,y> |] ==> Q|] ==> Q";
by (rtac PairE 1);
by (resolve_tac prems 1);
by (etac (beta_cfun_cprod RS ssubst) 1);
qed "cprodE";

Goalw [cfst_def,cpair_def] 
        "cfst$<x,y>=x";
by (stac beta_cfun_cprod 1);
by (stac beta_cfun 1);
by (rtac cont_fst 1);
by (Simp_tac  1);
qed "cfst2";

Goalw [csnd_def,cpair_def] 
        "csnd$<x,y>=y";
by (stac beta_cfun_cprod 1);
by (stac beta_cfun 1);
by (rtac cont_snd 1);
by (Simp_tac  1);
qed "csnd2";

Goal "cfst$UU = UU";
by (simp_tac (HOL_ss addsimps [inst_cprod_pcpo2,cfst2]) 1);
qed "cfst_strict";

Goal "csnd$UU = UU";
by (simp_tac (HOL_ss addsimps [inst_cprod_pcpo2,csnd2]) 1);
qed "csnd_strict";

Goalw [cfst_def,csnd_def,cpair_def] "<cfst$p , csnd$p> = p";
by (stac beta_cfun_cprod 1);
by (stac beta_cfun 1);
by (rtac cont_snd 1);
by (stac beta_cfun 1);
by (rtac cont_fst 1);
by (rtac (surjective_pairing RS sym) 1);
qed "surjective_pairing_Cprod2";

Goalw [cfst_def,csnd_def,cpair_def]
 "<xa,ya> << <x,y> ==> xa<<x & ya << y";
by (rtac less_cprod4c 1);
by (dtac (beta_cfun_cprod RS subst) 1);
by (dtac (beta_cfun_cprod RS subst) 1);
by (atac 1);
qed "less_cprod5c";

Goalw [cfst_def,csnd_def,cpair_def]
"[|chain(S)|] ==> range(S) <<| \
\ <(lub(range(%i. cfst$(S i)))) , lub(range(%i. csnd$(S i)))>";
by (stac beta_cfun_cprod 1);
by (stac (beta_cfun RS ext) 1);
by (rtac cont_snd 1);
by (stac (beta_cfun RS ext) 1);
by (rtac cont_fst 1);
by (rtac lub_cprod 1);
by (atac 1);
qed "lub_cprod2";

bind_thm ("thelub_cprod2", lub_cprod2 RS thelubI);
(*
chain ?S1 ==>
 lub (range ?S1) =
 <lub (range (%i. cfst$(?S1 i))), lub (range (%i. csnd$(?S1 i)))>" 
*)
Goalw [csplit_def]
        "csplit$f$<x,y> = f$x$y";
by (stac beta_cfun 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [cfst2,csnd2]) 1);
qed "csplit2";

Goalw [csplit_def]
  "csplit$cpair$z=z";
by (stac beta_cfun 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [surjective_pairing_Cprod2]) 1);
qed "csplit3";

(* ------------------------------------------------------------------------ *)
(* install simplifier for Cprod                                             *)
(* ------------------------------------------------------------------------ *)

Addsimps [cfst2,csnd2,csplit2];

val Cprod_rews = [cfst2,csnd2,csplit2];
