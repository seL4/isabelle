(*  Title:      92/CCL/coinduction
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Lemmas and tactics for using the rule coinduct3 on [= and =.
*)

val [mono,prem] = goal Lfp.thy "[| mono(f);  a : f(lfp(f)) |] ==> a : lfp(f)";
by (stac (mono RS lfp_Tarski) 1);
by (rtac prem 1);
qed "lfpI";

val prems = goal CCL.thy "[| a=a';  a' : A |] ==> a : A";
by (simp_tac (term_ss addsimps prems) 1);
qed "ssubst_single";

val prems = goal CCL.thy "[| a=a';  b=b';  <a',b'> : A |] ==> <a,b> : A";
by (simp_tac (term_ss addsimps prems) 1);
qed "ssubst_pair";

(***)

local 
fun mk_thm s = prove_goal Term.thy s (fn mono::prems => 
       [fast_tac (term_cs addIs ((mono RS coinduct3_mono_lemma RS lfpI)::prems)) 1]);
in
val ci3_RI    = mk_thm "[|  mono(Agen);  a : R |] ==> a : lfp(%x. Agen(x) Un R Un A)";
val ci3_AgenI = mk_thm "[|  mono(Agen);  a : Agen(lfp(%x. Agen(x) Un R Un A)) |] ==> \
\                       a : lfp(%x. Agen(x) Un R Un A)";
val ci3_AI    = mk_thm "[|  mono(Agen);  a : A |] ==> a : lfp(%x. Agen(x) Un R Un A)";
end;

fun mk_genIs thy defs genXH gen_mono s = prove_goalw thy defs s 
      (fn prems => [rtac (genXH RS iffD2) 1,
                    (simp_tac term_ss 1),
                    TRY (fast_tac (term_cs addIs 
                            ([genXH RS iffD2,gen_mono RS coinduct3_mono_lemma RS lfpI]
                             @ prems)) 1)]);

(** POgen **)

goal Term.thy "<a,a> : PO";
by (rtac (po_refl RS (XH_to_D PO_iff)) 1);
qed "PO_refl";

val POgenIs = map (mk_genIs Term.thy data_defs POgenXH POgen_mono)
      ["<true,true> : POgen(R)",
       "<false,false> : POgen(R)",
       "[| <a,a'> : R;  <b,b'> : R |] ==> <<a,b>,<a',b'>> : POgen(R)",
       "[|!!x. <b(x),b'(x)> : R |] ==><lam x.b(x),lam x.b'(x)> : POgen(R)",
       "<one,one> : POgen(R)",
       "<a,a'> : lfp(%x. POgen(x) Un R Un PO) ==> \
\                         <inl(a),inl(a')> : POgen(lfp(%x. POgen(x) Un R Un PO))",
       "<b,b'> : lfp(%x. POgen(x) Un R Un PO) ==> \
\                         <inr(b),inr(b')> : POgen(lfp(%x. POgen(x) Un R Un PO))",
       "<zero,zero> : POgen(lfp(%x. POgen(x) Un R Un PO))",
       "<n,n'> : lfp(%x. POgen(x) Un R Un PO) ==> \
\                         <succ(n),succ(n')> : POgen(lfp(%x. POgen(x) Un R Un PO))",
       "<[],[]> : POgen(lfp(%x. POgen(x) Un R Un PO))",
       "[| <h,h'> : lfp(%x. POgen(x) Un R Un PO); \
\          <t,t'> : lfp(%x. POgen(x) Un R Un PO) |] ==> \
\       <h$t,h'$t'> : POgen(lfp(%x. POgen(x) Un R Un PO))"];

fun POgen_tac (rla,rlb) i =
       SELECT_GOAL (safe_tac ccl_cs) i THEN
       rtac (rlb RS (rla RS ssubst_pair)) i THEN
       (REPEAT (resolve_tac (POgenIs @ [PO_refl RS (POgen_mono RS ci3_AI)] @ 
                   (POgenIs RL [POgen_mono RS ci3_AgenI]) @ [POgen_mono RS ci3_RI]) i));

(** EQgen **)

goal Term.thy "<a,a> : EQ";
by (rtac (refl RS (EQ_iff RS iffD1)) 1);
qed "EQ_refl";

val EQgenIs = map (mk_genIs Term.thy data_defs EQgenXH EQgen_mono)
["<true,true> : EQgen(R)",
 "<false,false> : EQgen(R)",
 "[| <a,a'> : R;  <b,b'> : R |] ==> <<a,b>,<a',b'>> : EQgen(R)",
 "[|!!x. <b(x),b'(x)> : R |] ==> <lam x.b(x),lam x.b'(x)> : EQgen(R)",
 "<one,one> : EQgen(R)",
 "<a,a'> : lfp(%x. EQgen(x) Un R Un EQ) ==> \
\                   <inl(a),inl(a')> : EQgen(lfp(%x. EQgen(x) Un R Un EQ))",
 "<b,b'> : lfp(%x. EQgen(x) Un R Un EQ) ==> \
\                   <inr(b),inr(b')> : EQgen(lfp(%x. EQgen(x) Un R Un EQ))",
 "<zero,zero> : EQgen(lfp(%x. EQgen(x) Un R Un EQ))",
 "<n,n'> : lfp(%x. EQgen(x) Un R Un EQ) ==> \
\                   <succ(n),succ(n')> : EQgen(lfp(%x. EQgen(x) Un R Un EQ))",
 "<[],[]> : EQgen(lfp(%x. EQgen(x) Un R Un EQ))",
 "[| <h,h'> : lfp(%x. EQgen(x) Un R Un EQ); \
\          <t,t'> : lfp(%x. EQgen(x) Un R Un EQ) |] ==> \
\       <h$t,h'$t'> : EQgen(lfp(%x. EQgen(x) Un R Un EQ))"];

fun EQgen_raw_tac i =
       (REPEAT (resolve_tac (EQgenIs @ [EQ_refl RS (EQgen_mono RS ci3_AI)] @ 
                   (EQgenIs RL [EQgen_mono RS ci3_AgenI]) @ [EQgen_mono RS ci3_RI]) i));

(* Goals of the form R <= EQgen(R) - rewrite elements <a,b> : EQgen(R) using rews and *)
(* then reduce this to a goal <a',b'> : R (hopefully?)                                *)
(*      rews are rewrite rules that would cause looping in the simpifier              *)

fun EQgen_tac simp_set rews i = 
 SELECT_GOAL 
   (TRY (safe_tac ccl_cs) THEN
    resolve_tac ((rews@[refl]) RL ((rews@[refl]) RL [ssubst_pair])) i THEN
    ALLGOALS (simp_tac simp_set) THEN
    ALLGOALS EQgen_raw_tac) i;
