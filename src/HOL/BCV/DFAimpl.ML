(*  Title:      HOL/BCV/DFAimpl.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

(** merges **)

Goal "!sos. size(merges t ps sos) = size sos";
by (induct_tac "ps" 1);
by (Auto_tac);
qed_spec_mp "length_merges";
Addsimps [length_merges];

Goal
 "!xs. xs : listsn n (option A) --> x : A --> (!p : set ps. p<n) --> \
\      semilat A --> merges x ps xs : listsn n (option A)";
by (induct_tac "ps" 1);
by (Auto_tac);
qed_spec_mp "merges_preserves_type";
Addsimps [merges_preserves_type];
(*AddSIs [merges_preserves_type];*)

Goal "semilat A ==> !xs. xs : listsn n (option A) --> x:A --> (!p:set ps. p<n) \
\ --> xs <= merges x ps xs";
by (induct_tac "ps" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (rtac order_trans 1);
 by (etac list_update_incr 1);
   by (Blast_tac 2);
  by (assume_tac 2);
 by (etac (Some_in_option RS iffD2) 1);
by (blast_tac (claset() addSIs [listsnE_set]
          addIs [semilat_plus,listsnE_length RS nth_in]) 1);
qed_spec_mp "merges_incr";

(* is redundant but useful *)
Goal "[| xs!i = Some x; xs : listsn n (option A); i < n |] ==> x:A";
by (dtac listsnE_nth_in 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
qed "listsn_optionE_in";
(*Addsimps [listsn_optionE_in];*)

Goal
 "[| semilat L |] ==> \
\ (!xs. xs : listsn n (option L) --> x:L --> (!p:set ps. p<n) --> \
\      (merges x ps xs = xs) = (!p:set ps. Some x <= xs!p))";
by (induct_tac "ps" 1);
 by (Asm_simp_tac 1);
by (Clarsimp_tac 1);
by (rename_tac "p ps xs" 1);
by (rtac iffI 1);
 by (rtac context_conjI 1);
  by (subgoal_tac "xs[p := Some x + xs!p] <= xs" 1);
   by (EVERY[etac subst 2, rtac merges_incr 2]);
      by (assume_tac 2);
     by (Force_tac 2);
    by (assume_tac 2);
   by (assume_tac 2);
  by (exhaust_tac "xs!p" 1);
   by (asm_full_simp_tac (simpset() addsimps [list_update_le_conv]) 1);
  by (asm_full_simp_tac (simpset() addsimps
      [list_update_le_conv,listsn_optionE_in]) 1);
 by (Clarify_tac 1);
 by (rotate_tac ~3 1);
 by (asm_full_simp_tac (simpset() addsimps
      [le_iff_plus_unchanged RS iffD1,listsn_optionE_in,
       list_update_same_conv RS iffD2]) 1);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsimps
      [le_iff_plus_unchanged RS iffD1,listsn_optionE_in,
       list_update_same_conv RS iffD2]) 1);
qed_spec_mp "merges_same_conv";


Goalw [le_list,plus_option]
 "xs <= ys --> xs : listsn n (option L) --> ys : listsn n (option L) --> \
\ p < n --> ys!p = Some y --> x <= y --> x : L --> semilat L --> \
\ xs[p := Some x + xs!p] <= ys";
by (simp_tac (simpset()  addsimps [nth_list_update]
                        addsplits [option.split]) 1);
by (Clarify_tac 1);
by (rotate_tac 3 1);
by (force_tac (claset() addEs [listsn_optionE_in] addIs [semilat_lub],
              simpset()) 1);
qed_spec_mp "list_update_le_listI";

Goal
 "[| semilat(L); t:L; tos : listsn n (option L); \
\    !p. p:set ps --> Some t <= tos!p; \
\    !p. p:set ps --> p<n |] ==> \
\ set qs <= set ps  --> \
\ (!sos. sos : listsn n (option L) & sos <= tos --> merges t qs sos <= tos)";
by (induct_tac "qs" 1);
 by (Asm_simp_tac 1);
by (force_tac (claset(),simpset() addsimps [list_update_le_listI]) 1);
val lemma = result();

Goal
 "[| semilat(L); t:L; \
\    !p. p:set ps --> Some t <= tos!p; \
\    !p. p:set ps --> p<n; \
\    sos <= tos; sos : listsn n (option L); tos : listsn n (option L) |] \
\ ==> merges t ps sos <= tos";
by (blast_tac (claset() addDs [lemma]) 1);
qed "merges_pres_le_ub";


(** next **)

Goalw [is_next_def]
 "[| is_next next; next step succs sos = None; succs_bounded succs n; \
\    sos : listsn n S |] ==> \
\ ? p<n. ? s. sos!p = Some s & step p s = None";
by (subgoal_tac "n=size sos" 1);
by (Blast_tac 1);
by (Asm_simp_tac 1);
qed "next_None";

Goalw [is_next_def]
 "[| is_next next; succs_bounded succs n; sos : listsn n S |] ==> \
\ next step succs sos = Some sos --> \
\ (!p<n. !s. sos!p = Some s --> (? t. \
\         step p s = Some(t) & merges t (succs p) sos = sos))";
by (subgoal_tac "n=size sos" 1);
by (Blast_tac 1);
by (Asm_simp_tac 1);
qed "next_Some1";

Goalw [is_next_def]
 "[| is_next next; next step succs sos = Some sos'; sos' ~= sos; \
\    succs_bounded succs n; sos : listsn n S |] ==> \
\ ? p<n. ? s. sos!p = Some s & (? t. \
\     step p s = Some(t) & merges t (succs p) sos = sos')";
by (subgoal_tac "n=size sos" 1);
by (Blast_tac 1);
by (Asm_simp_tac 1);
qed "next_Some2";

Goal
 "[| is_next next; succs_bounded succs n; sos : listsn n S |] ==> \
\ (next step succs sos = Some sos) = \
\ (!p<n. !s. sos!p = Some s --> (? t. \
\         step p s = Some(t) & merges t (succs p) sos = sos))";
by (rtac iffI 1);
 by (asm_simp_tac (simpset() addsimps [next_Some1]) 1);
by (exhaust_tac "next step succs sos" 1);
 by (best_tac (claset() addSDs [next_None] addss simpset()) 1);
by (rename_tac "sos'" 1);
by (case_tac "sos' = sos" 1);
 by (Blast_tac 1);
by (best_tac (claset() addSDs [next_Some2] addss simpset()) 1);
qed "next_Some1_eq";

Addsimps [next_Some1_eq];

Goalw [step_pres_type_def]
 "[| step_pres_type step n L; s:L; p<n; step p s = Some(t) |] ==> t:L";
by (Blast_tac 1);
qed "step_pres_typeD";

Goalw [succs_bounded_def]
 "[| succs_bounded succs n; p < n; q : set(succs p) |] ==> q < n";
by (Blast_tac 1);
qed "succs_boundedD";

Goal
 "[| is_next next; semilat A; \
\    step_pres_type step n A; succs_bounded succs n;\
\    sos : listsn n (option A) |] ==> \
\ next step succs sos : option (listsn n (option A))";
by (exhaust_tac "next step succs sos" 1);
 by (ALLGOALS Asm_simp_tac);
by (rename_tac "sos'" 1);
by (case_tac "sos' = sos" 1);
 by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [step_pres_typeD,succs_boundedD,listsn_optionE_in] addSIs [merges_preserves_type] addDs [next_Some2]) 1);
qed_spec_mp "next_preserves_type";

Goal
 "[| is_next next; semilat A; \
\    step_pres_type step n A; succs_bounded succs n; \
\    next step succs xs = Some ys; xs : listsn n (option A) |] ==> xs <= ys";
by (case_tac "ys = xs" 1);
 by (Asm_full_simp_tac 1);
by (blast_tac (claset() addSIs [merges_incr] addIs [listsn_optionE_in]
       addDs [step_pres_typeD,succs_boundedD,next_Some2]) 1);
qed_spec_mp "next_incr";

val lemma = (Unify.trace_bound, Unify.search_bound);
Unify.trace_bound := 50;
Unify.search_bound := 50;

Goalw [is_next_def]
 "is_next (%step succs sos. itnext (size sos) step succs sos)";
by (Clarify_tac 1);
by (etac thin_rl 1);
by (res_inst_tac [("n","length sos")] nat_induct 1);
 by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [less_Suc_eq,Let_def]
                                addsplits [option.split])1);
by (Blast_tac 1);
qed "is_next_itnext";

Unify.trace_bound := !(fst lemma);
Unify.search_bound := !(snd lemma);

(** fix step **)

Goalw [step_mono_None_def]
 "[| step_mono_None step n L; s : L; p < n; s <= t; step p s = None |] ==> \
\ step p t = None";
by (Blast_tac 1);
qed "step_mono_NoneD";

Goalw [step_mono_def]
 "[| step_mono step n L; s : L; p < n; s <= t; step p s = Some(u) |] ==> \
\ !v. step p t = Some(v) --> u <= v";
by (Blast_tac 1);
qed "step_monoD";

Goalw [stable_def]
"[| is_next next; semilat L; sos : listsn n (option L); \
\   step_pres_type step n L; succs_bounded succs n |] \
\ ==> (next step succs sos = Some sos) = (!p<n. stable step succs p sos)";
by (Asm_simp_tac 1);
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (etac allE 1 THEN mp_tac 1);
 by (etac allE 1 THEN mp_tac 1);
 by (Clarify_tac 1);
 bd(merges_same_conv RS iffD1)1;
     by (assume_tac 4);
    by (assume_tac 1);
   by (blast_tac (claset() addIs [step_pres_typeD,listsn_optionE_in]) 1);
  by (blast_tac (claset() addIs [succs_boundedD,listsn_optionE_in]) 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (etac allE 1 THEN mp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addSIs [merges_same_conv RS iffD2]
     addIs [step_pres_typeD,succs_boundedD,listsn_optionE_in]) 1);
qed "fixpoint_next_iff_stable";

Goal
 "[| semilat L; is_next next; succs_bounded succs n; \
\    step_pres_type step n L; step_mono_None step n L; step_mono step n L; \
\    tos:listsn n (option L); next step succs tos = Some tos; \
\    sos:listsn n (option L); sos <= tos |] \
\ ==> ? sos'. next step succs sos = Some sos' & sos' <= tos";
by (subgoal_tac
   "!p<n. !s. sos!p = Some s --> (? u. \
\             step p s = Some(u) & (!q:set(succs p). Some u<=tos!q))" 1);
 by (exhaust_tac "next step succs sos" 1);
  by (dtac next_None 1);
     by (assume_tac 1);
    by (assume_tac 1);
   by (assume_tac 1);
  by (Force_tac 1);
 by (rename_tac "sos'" 1);
 by (case_tac "sos' = sos" 1);
  by (Blast_tac 1);
 by (dtac next_Some2 1);
    by (EVERY1[atac, atac, atac, atac]);
 by (Clarify_tac 1);
 by (etac allE 1 THEN mp_tac 1);
 by (etac allE 1 THEN mp_tac 1);
 by (Clarify_tac 1);
 by (EVERY1[rtac exI, rtac conjI, atac]);
 by (rtac merges_pres_le_ub 1);
       by (assume_tac 1);
      by (blast_tac (claset() addIs [step_pres_typeD,listsn_optionE_in]) 1);
     by (Asm_full_simp_tac 1);
    by (blast_tac (claset() addIs [succs_boundedD,listsn_optionE_in]) 1);
   by (REPEAT(atac 1));
by (Clarify_tac 1);
by (exhaust_tac "tos!p" 1);
 by (force_tac (claset() addDs [le_listD],simpset()) 1);
by (rename_tac "t" 1);
by (subgoal_tac "s <= t" 1);
 by (force_tac (claset() addDs [le_listD],simpset()) 2);
by (exhaust_tac "step p s" 1);
 by (dtac step_mono_NoneD 1);
     by (assume_tac 4);
    by (blast_tac (claset() addIs [listsn_optionE_in]) 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (Force_tac 1);
by (dtac step_monoD 1);
    by (assume_tac 4);
   by (blast_tac (claset() addIs [listsn_optionE_in]) 1);
  by (assume_tac 1);
 by (assume_tac 1);
by (Asm_full_simp_tac 1);
by (etac allE 1 THEN mp_tac 1);
by (etac allE 1 THEN mp_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (forward_tac[merges_same_conv RS iffD1]1);
    by (assume_tac 4);
   by (assume_tac 1);
  by (blast_tac (claset() addIs [step_pres_typeD,listsn_optionE_in]) 1);
 by (blast_tac (claset() addIs [succs_boundedD,listsn_optionE_in]) 1);
by (blast_tac (claset() addIs [order_trans]) 1);
val lemma = result();

Goalw [is_dfa_def]
 "[| semilat L; acc L; is_next next; \
\    step_pres_type step n L; succs_bounded succs n; \
\    step_mono_None step n L; step_mono step n L |] ==> \
\ is_dfa (%sos. fix(next step succs, sos)) step succs n L";
by (Clarify_tac 1);
by (stac fix_iff_has_fixpoint 1);
     by (etac (acc_option RS acc_listsn) 1);
    by (blast_tac (claset() addIs [lemma]) 1);
   by (blast_tac (claset() addIs [next_preserves_type]) 1);
  by (blast_tac (claset() addIs [next_incr]) 1);
 by (assume_tac 1);
by (asm_simp_tac (simpset() delsimps [next_Some1_eq] addsimps [fixpoint_next_iff_stable]) 1);
qed "is_dfa_fix_next";

Goal
 "[| semilat L; acc L; is_next next; \
\    step_pres_type step n L; succs_bounded succs n; \
\    step_mono_None step n L; step_mono step n L; \
\    wti_is_fix_step step wti succs n L; \
\    sos : listsn n (option L) |] ==> \
\ fix(next step succs, sos) = \
\ (? tos:listsn n (option L). sos<=tos & welltyping wti tos)";
by (blast_tac (claset() addSDs [dfa_iff_welltyping] addSIs [is_dfa_fix_next]) 1);
qed "fix_next_iff_welltyping";
