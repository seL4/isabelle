(* $Id$ *)

open Dagstuhl;

val YS_def2  = fix_prover2 Dagstuhl.thy  YS_def  "YS = y && YS";
val YYS_def2 = fix_prover2 Dagstuhl.thy YYS_def "YYS = y && y && YYS";


val prems = goal Dagstuhl.thy "YYS << y && YYS";
by (rtac (YYS_def RS def_fix_ind) 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac monofun_cfun_arg 1);
by (rtac monofun_cfun_arg 1);
by (atac 1);
val lemma3 = result();

val prems = goal Dagstuhl.thy "y && YYS << YYS";
by (stac YYS_def2 1);
back();
by (rtac monofun_cfun_arg 1);
by (rtac lemma3 1);
val lemma4=result();

(* val  lemma5 = lemma3 RS (lemma4 RS antisym_less) *)

val prems = goal Dagstuhl.thy "y && YYS = YYS";
by (rtac antisym_less 1);
by (rtac lemma4 1);
by (rtac lemma3 1);
val lemma5=result();

val prems = goal Dagstuhl.thy "YS = YYS";
by (resolve_tac stream.take_lemmas 1);
by (nat_ind_tac "n" 1);
by (simp_tac (!simpset addsimps stream.rews) 1);
by (stac YS_def2 1);
by (stac YYS_def2 1);
by (asm_simp_tac (!simpset addsimps stream.rews) 1);
by (rtac (lemma5 RS sym RS subst) 1);
by (rtac refl 1);
val wir_moel=result();

(* ------------------------------------------------------------------------ *)
(* Zweite L"osung: Bernhard M"oller                                         *)
(* statt Beweis von  wir_moel "uber take_lemma beidseitige Inclusion        *)
(* verwendet lemma5                                                         *)
(* ------------------------------------------------------------------------ *)

val prems = goal Dagstuhl.thy "YYS << YS";
by (rewtac YYS_def);
by (rtac fix_least 1);
by (stac beta_cfun 1);
by (cont_tacR 1);
by (simp_tac (!simpset addsimps [YS_def2 RS sym]) 1);
val lemma6=result();

val prems = goal Dagstuhl.thy "YS << YYS";
by (rtac (YS_def RS def_fix_ind) 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (stac (lemma5 RS sym) 1);
by (etac monofun_cfun_arg 1);
val lemma7 = result();

val  wir_moel = lemma6 RS (lemma7 RS antisym_less);

