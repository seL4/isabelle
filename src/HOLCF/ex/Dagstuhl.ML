(*
    ID:         $Id$
*)


open Dagstuhl;

val YS_def2  = fix_prover Dagstuhl.thy  YS_def  "YS  = scons[y][YS]";
val YYS_def2 = fix_prover Dagstuhl.thy YYS_def "YYS = scons[y][scons[y][YYS]]";


val prems = goal Dagstuhl.thy "YYS << scons[y][YYS]";
by (rtac (YYS_def RS ssubst) 1);
by (rtac fix_ind 1);
by (resolve_tac adm_thms 1);
by (contX_tacR 1);
by (rtac minimal 1);
by (rtac (beta_cfun RS ssubst) 1);
by (contX_tacR 1);
by (rtac monofun_cfun_arg 1);
by (rtac monofun_cfun_arg 1);
by (atac 1);
qed "lemma3";

val prems = goal Dagstuhl.thy "scons[y][YYS] << YYS";
by (rtac (YYS_def2 RS ssubst) 1);
back();
by (rtac monofun_cfun_arg 1);
by (rtac lemma3 1);
qed "lemma4";

(* val  lemma5 = lemma3 RS (lemma4 RS antisym_less) *)

val prems = goal Dagstuhl.thy "scons[y][YYS] = YYS";
by (rtac antisym_less 1);
by (rtac lemma4 1);
by (rtac lemma3 1);
qed "lemma5";

val prems = goal Dagstuhl.thy "YS = YYS";
by (rtac stream_take_lemma 1);
by (nat_ind_tac "n" 1);
by (simp_tac (HOLCF_ss addsimps stream_rews) 1);
by (res_inst_tac [("y1","y")] (YS_def2 RS ssubst) 1);
by (res_inst_tac [("y1","y")] (YYS_def2 RS ssubst) 1);
by (asm_simp_tac (HOLCF_ss addsimps stream_rews) 1);
by (rtac (lemma5 RS sym RS subst) 1);
by (rtac refl 1);
qed "wir_moel";

(* ------------------------------------------------------------------------ *)
(* Zweite L"osung: Bernhard M"oller                                         *)
(* statt Beweis von  wir_moel "uber take_lemma beidseitige Inclusion        *)
(* verwendet lemma5                                                         *)
(* ------------------------------------------------------------------------ *)

val prems = goal Dagstuhl.thy "YYS << YS";
by (rtac (YYS_def RS ssubst) 1);
by (rtac fix_least 1);
by (rtac (beta_cfun RS ssubst) 1);
by (contX_tacR 1);
by (simp_tac (HOLCF_ss addsimps [YS_def2 RS sym]) 1);
qed "lemma6";

val prems = goal Dagstuhl.thy "YS << YYS";
by (rtac (YS_def RS ssubst) 1);
by (rtac fix_ind 1);
by (resolve_tac adm_thms 1);
by (contX_tacR 1);
by (rtac minimal 1);
by (rtac (beta_cfun RS ssubst) 1);
by (contX_tacR 1);
by (res_inst_tac [("y2","y10")] (lemma5 RS sym RS ssubst) 1);
by (etac monofun_cfun_arg 1);
qed "lemma7";

val  wir_moel = lemma6 RS (lemma7 RS antisym_less);


(* ------------------------------------------------------------------------ *)
(* L"osung aus Dagstuhl (F.R.)                                              *)
(* Wie oben, jedoch ohne Konstantendefinition f"ur YS, YYS                  *)
(* ------------------------------------------------------------------------ *)

val prems = goal Stream2.thy
    "(fix[LAM x. scons[y][x]]) = scons[y][fix[LAM x. scons[y][x]]]";
by (rtac (fix_eq RS ssubst) 1);
back();
back();
by (rtac (beta_cfun RS ssubst) 1);
by (contX_tacR 1);
by (rtac refl 1);
qed "lemma1";

val prems = goal Stream2.thy
    "(fix[ LAM z. scons[y][scons[y][z]]]) = \
\     scons[y][scons[y][(fix[ LAM z. scons[y][scons[y][z]]])]]";
by (rtac (fix_eq RS ssubst) 1);
back();
back();
by (rtac (beta_cfun RS ssubst) 1);
by (contX_tacR 1);
by (rtac refl 1);
qed "lemma2";

val prems = goal Stream2.thy
"fix[LAM z. scons[y][scons[y][z]]] << \
\ scons[y][fix[LAM z. scons[y][scons[y][z]]]]";
by (rtac fix_ind 1);
by (resolve_tac adm_thms 1);
by (contX_tacR 1);
by (rtac minimal 1);
by (asm_simp_tac (HOLCF_ss addsimps stream_rews) 1);
by (rtac monofun_cfun_arg 1);
by (rtac monofun_cfun_arg 1);
by (atac 1);
qed "lemma3";

val prems = goal Stream2.thy
" scons[y][fix[LAM z. scons[y][scons[y][z]]]] <<\
\ fix[LAM z. scons[y][scons[y][z]]]";
by (rtac (lemma2 RS ssubst) 1);
back();
by (rtac monofun_cfun_arg 1);
by (rtac lemma3 1);
qed "lemma4";

val prems = goal Stream2.thy
" scons[y][fix[LAM z. scons[y][scons[y][z]]]] =\
\ fix[LAM z. scons[y][scons[y][z]]]";
by (rtac antisym_less 1);
by (rtac lemma4 1);
by (rtac lemma3 1);
qed "lemma5";

val prems = goal Stream2.thy
    "(fix[LAM x. scons[y][x]]) = (fix[ LAM z. scons[y][scons[y][z]]])";
by (rtac stream_take_lemma 1);
by (nat_ind_tac "n" 1);
by (simp_tac (HOLCF_ss addsimps stream_rews) 1);
by (rtac (lemma1 RS ssubst) 1);
by (rtac (lemma2 RS ssubst) 1);
by (asm_simp_tac (HOLCF_ss addsimps stream_rews) 1);
by (rtac (lemma5 RS sym RS subst) 1);
by (rtac refl 1);
qed "wir_moel";



