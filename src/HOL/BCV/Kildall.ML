(*  Title:      HOL/BCV/Kildall.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Addsimps [Let_def];
Addsimps [le_iff_plus_unchanged RS sym];

Goalw [pres_type_def]
 "[| pres_type step n A; s:A; p<n |] ==> step p s : A";
by (Blast_tac 1);
qed "pres_typeD";

Goalw [bounded_def]
 "[| bounded succs n; p < n; q : set(succs p) |] ==> q < n";
by (Blast_tac 1);
qed "boundedD";

Goalw [mono_def]
 "[| mono r step n A; p < n; s:A; s <=_r t |] ==> step p s <=_r step p t";
by (Blast_tac 1);
qed "monoD";

(** merges **)

Goal "!ss. size(merges f t ps ss) = size ss";
by (induct_tac "ps" 1);
by (Auto_tac);
qed_spec_mp "length_merges";
Addsimps [length_merges];

Goalw [closed_def]
 "[| semilat(A,r,f) |] ==> \
\ !xs. xs : list n A --> x : A --> (!p : set ps. p<n) \
\      --> merges f x ps xs : list n A";
by (ftac semilatDclosedI 1);
by (rewtac closed_def);
by (induct_tac "ps" 1);
by (Auto_tac);
qed_spec_mp "merges_preserves_type";
Addsimps [merges_preserves_type];

Goal
 "[| semilat(A,r,f) |] ==> \
\ !xs. xs : list n A --> x : A --> (!p:set ps. p<size xs) --> xs <=[r] merges f x ps xs";
by (induct_tac "ps" 1);
 by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (rtac order_trans 1);
  by (Asm_simp_tac 1);
 by (etac list_update_incr 1);
   by (assume_tac 1);
  by (Asm_simp_tac 1);
 by (Asm_simp_tac 1);
by (blast_tac (claset() addSIs [listE_set]
          addIs [closedD,listE_length RS nth_in]) 1);
qed_spec_mp "merges_incr";

Goal
 "[| semilat(A,r,f) |] ==> \
\ (!xs. xs : list n A --> x:A --> (!p:set ps. p<size xs) --> \
\       (merges f x ps xs = xs) = (!p:set ps. x <=_r xs!p))";
by (induct_tac "ps" 1);
 by (Asm_simp_tac 1);
by (Clarsimp_tac 1);
by (rename_tac "p ps xs" 1);
by (rtac iffI 1);
 by (rtac context_conjI 1);
  by (subgoal_tac "xs[p := x +_f xs!p] <=[r] xs" 1);
   by (EVERY[etac subst 2, rtac merges_incr 2]);
      by (force_tac (claset() addSDs [le_listD],
                    simpset() addsimps [nth_list_update]) 1);
     by (assume_tac 1);
    by (blast_tac (claset() addSIs [listE_set]
                   addIs [closedD,listE_length RS nth_in]) 1);
   by (assume_tac 1);
  by (Asm_simp_tac 1);
 by (Clarify_tac 1);
 by (rotate_tac ~2 1);
 by (asm_full_simp_tac (simpset() addsimps
      [le_iff_plus_unchanged RS iffD1,
       list_update_same_conv RS iffD2]) 1);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsimps
      [le_iff_plus_unchanged RS iffD1,
       list_update_same_conv RS iffD2]) 1);
qed_spec_mp "merges_same_conv";


Goalw [Listn.le_def,lesub_def,semilat_def]
 "set xs <= A --> set ys <= A --> xs <=[r] ys --> p < size xs -->  \
\ x <=_r ys!p --> semilat(A,r,f) --> x:A --> \
\ xs[p := x +_f xs!p] <=[r] ys";
by (simp_tac (simpset()  addsimps [list_all2_conv_all_nth,nth_list_update]) 1);
qed_spec_mp "list_update_le_listI";

Goalw [closed_def]
 "[| semilat(A,r,f); set ts <= A; t:A; \
\    !p. p:set ps --> t <=_r ts!p; \
\    !p. p:set ps --> p<size ts |] ==> \
\ set qs <= set ps  --> \
\ (!ss. set ss <= A --> ss <=[r] ts --> merges f t qs ss <=[r] ts)";
by (induct_tac "qs" 1);
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1);
by (EVERY[etac allE 1, etac impE 1, etac mp 2]);
 by (asm_simp_tac (simpset() addsimps [closedD]) 1);
by (asm_full_simp_tac (simpset() addsimps [list_update_le_listI]) 1);
val lemma = result();

Goal
 "[| semilat(A,r,f); t:A; set ts <= A; set ss <= A; \
\    !p. p:set ps --> t <=_r ts!p; \
\    !p. p:set ps --> p<size ts; \
\    ss <=[r] ts |] \
\ ==> merges f t ps ss <=[r] ts";
by (blast_tac (claset() addDs [lemma]) 1);
qed "merges_pres_le_ub";

Goal "[| semilat (A, r, f); t:A; p < n |] ==> !ss. ss : list n A --> \
\     (!p:set ps. p<n) --> \
\     (merges f t ps ss)!p = (if p : set ps then t +_f ss!p else ss!p)";
by (induct_tac "ps" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [nth_list_update,closedD,listE_nth_in]) 1);
qed_spec_mp "nth_merges";


(** propa **)

Goal "!ss w. (!q:set qs. q < size ss) --> \
\ propa f qs t ss w = \
\ (merges f t qs ss, {q. q:set qs & t +_f ss!q ~= ss!q} Un w)";
by (induct_tac "qs" 1);
 by (Simp_tac 1);
by (Simp_tac 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (asm_simp_tac (simpset() addsimps [nth_list_update]) 1);
 by (Blast_tac 1);
by (asm_simp_tac (simpset() addsimps [nth_list_update]) 1);
by (Blast_tac 1);
qed_spec_mp "decomp_propa";

(** iter **)

val [iter_wf,iter_tc] = iter.tcs;

goalw_cterm [] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop iter_wf));
by (REPEAT(rtac wf_same_fstI 1));
by (split_all_tac 1);
by (asm_full_simp_tac (simpset() addsimps [lesssub_def]) 1);
by (REPEAT(rtac wf_same_fstI 1));
by (rtac wf_lex_prod 1);
 by (rtac wf_finite_psubset 2); (* FIXME *)
by (Clarify_tac 1);
by (dtac (semilatDorderI RS acc_le_listI) 1);
 by (assume_tac 1);
by (rewrite_goals_tac [acc_def,lesssub_def]);
by (assume_tac 1);
qed "iter_wf";

Goalw [lesssub_def]
 "[| semilat(A,r,f); ss : list n A; t:A; ! q:set qs. q < n; p:w |] ==> \
\ ss <[r] merges f t qs ss | \
\ merges f t qs ss = ss & {q. q:set qs & t +_f ss!q ~= ss!q} Un (w-{p}) < w";
by (asm_simp_tac (simpset() addsimps [merges_incr]) 1);
by (rtac impI 1);
by (dtac (sym RS (rotate_prems 4 (merges_same_conv RS iffD1))) 1);
    by (assume_tac 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addcongs [conj_cong]
                            addsimps [le_iff_plus_unchanged RS sym]) 1);
by (blast_tac (claset() addSIs [psubsetI] addEs [equalityE]) 1);
qed "inter_tc_lemma";

goalw_cterm [] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop iter_tc));
by (asm_simp_tac (simpset() addsimps [same_fst_def,pres_type_def]) 1);
by (clarify_tac (claset() delrules [disjCI]) 1);
by (subgoal_tac "(@p. p:w) : w" 1);
 by (fast_tac (claset() addIs [someI]) 2);
by (subgoal_tac "ss : list (size ss) A" 1);
 by (blast_tac (claset() addSIs [listI]) 2);
by (subgoal_tac "!q:set(succs (@ p. p : w)). q < size ss" 1);
 by (blast_tac (claset() addDs [boundedD]) 2);
by (rotate_tac 1 1);
by (asm_full_simp_tac (simpset() delsimps [listE_length]
      addsimps [decomp_propa,finite_psubset_def,inter_tc_lemma,
                bounded_nat_set_is_finite]) 1);
qed "iter_tc";

val prems = goal thy
 "(!!A r f step succs ss w. \
\    (!p. p = (@ p. p : w) & w ~= {} & semilat(A,r,f) & acc r & \
\       (!p:w. p < length ss) & bounded succs (length ss) & \
\       set ss <= A & pres_type step (length ss) A \
\     --> P A r f step succs (merges f (step p (ss!p)) (succs p) ss) \
\           ({q. q:set(succs p) & step p (ss!p) +_f ss!q ~= ss!q} Un (w-{p})))\
\    ==> P A r f step succs ss w) ==> P A r f step succs ss w";
by (res_inst_tac [("P","P")] (iter_tc RS (iter_wf RS iter.induct)) 1);
by (rename_tac "w" 1);
by (resolve_tac prems 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset()) 1);
by (subgoal_tac "!q:set(succs (@ p. p : w)). q < size ss" 1);
 by (rotate_tac ~1 1);
 by (asm_full_simp_tac (simpset() addsimps [decomp_propa]) 1);
by (subgoal_tac "(@p. p:w) : w" 1);
 by (fast_tac (claset() addIs [someI]) 2);
by (blast_tac (claset() addDs [boundedD]) 1);
qed "iter_induct";

Goal
 "[| semilat(A,r,f); acc r; set ss <= A; pres_type step (length ss) A; \
\    bounded succs (size ss); !p:w. p<size ss |] ==> \
\ iter(((A,r,f),step,succs),ss,w) = \
\ (if w={} then ss \
\  else let p = SOME p. p : w \
\       in iter(((A,r,f),step,succs),merges f (step p (ss!p)) (succs p) ss, \
\        {q. q:set(succs p) & step p (ss!p) +_f ss!q ~= ss!q} Un (w-{p})))";
by (rtac ((iter_tc RS (iter_wf RS (hd iter.simps))) RS trans) 1);
by (Asm_simp_tac 1);
by (rtac impI 1);
by (stac decomp_propa 1);
 by (subgoal_tac "(@p. p:w) : w" 1);
  by (fast_tac (claset() addIs [someI]) 2);
 by (blast_tac (claset() addDs [boundedD]) 1);
by (Simp_tac 1);
qed "iter_unfold";

Goalw [stable_def]
 "[| semilat (A,r,f); pres_type step n A; bounded succs n; \
\    ss : list n A; p : w; ! q:w. q < n; \
\    ! q. q < n --> q ~: w --> stable r step succs ss q; q < n; \
\    q : set (succs p) --> step p (ss ! p) +_f ss ! q = ss ! q; \
\    q ~: w | q = p  |] ==> \
\      stable r step succs (merges f (step p (ss!p)) (succs p) ss) q";
by (subgoal_tac "step p (ss!p) : A" 1);
 by (blast_tac (claset() addIs [listE_nth_in,pres_typeD]) 2);
by (Simp_tac 1);
by (Clarify_tac 1);
by (stac nth_merges 1);
     by (assume_tac 1);
    by (assume_tac 1);
   by (assume_tac 2);
  by (blast_tac (claset() addDs [boundedD]) 1);
 by (blast_tac (claset() addDs [boundedD]) 1);
by (stac nth_merges 1);
     by (assume_tac 1);
    by (assume_tac 1);
   by (assume_tac 2);
  by (blast_tac (claset() addDs [boundedD]) 1);
 by (blast_tac (claset() addDs [boundedD]) 1);
by (Simp_tac 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
 by (asm_simp_tac (simpset() delsimps [listE_length]) 1);
 by (blast_tac (claset() addSIs [semilat_ub1,semilat_ub2,listE_nth_in] addIs [order_trans]addDs [boundedD]) 1);
by (blast_tac (claset() addSIs [semilat_ub1,semilat_ub2,listE_nth_in] addIs [order_trans]addDs [boundedD]) 1);
qed "stable_pres_lemma";

Goalw [stable_def]
 "[| semilat (A,r,f); mono r step n A; bounded succs n; \
\    step p (ss!p) : A; ss : list n A; ts : list n A; p < n; \
\    ss <=[r] ts; ! p. p < n --> stable r step succs ts p |] \
\ ==> merges f (step p (ss!p)) (succs p) ss <=[r] ts";
by (blast_tac (claset()
    addSIs [listE_set,monoD,listE_nth_in,le_listD,less_lengthI]
    addIs [merges_pres_le_ub,order_trans]
    addDs [pres_typeD,boundedD]) 1);
qed_spec_mp "merges_bounded_lemma";

Unify.trace_bound := 80;
Unify.search_bound := 90;
Goalw [stables_def]
 "semilat(A,r,f) & acc r & pres_type step n A & mono r step n A & \
\ bounded succs n & (! p:w. p < n) & ss:list n A & \
\ (!p<n. p~:w --> stable r step succs ss p) \
\ --> iter(((A,r,f),step,succs),ss,w) : list n A & \
\     stables r step succs (iter(((A,r,f),step,succs),ss,w)) & \
\     ss <=[r] iter(((A,r,f),step,succs),ss,w) & \
\     (! ts:list n A. \
\          ss <=[r] ts & stables r step succs ts --> \
\          iter(((A,r,f),step,succs),ss,w) <=[r] ts)";
by (res_inst_tac [("A","A"),("r","r"),("f","f"),("step","step"),("ss","ss"),("w","w")]iter_induct 1);
by (Clarify_tac 1);
by (ftac listE_length 1);
by (hyp_subst_tac 1);
by (stac iter_unfold 1);
      by (assume_tac 1);
     by (assume_tac 1);
    by (Asm_simp_tac 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (assume_tac 1);
by (asm_simp_tac (simpset() delsimps [listE_length]) 1);
by (rtac impI 1);
by (etac allE 1);
by (etac impE 1);
 by (asm_simp_tac (simpset() delsimps [listE_length]) 1);
by (subgoal_tac "(@p. p:w) : w" 1);
 by (fast_tac (claset() addIs [someI]) 2);
by (subgoal_tac "step (@ p. p : w) (ss ! (@ p. p : w)) : A" 1);
 by (blast_tac (claset() addIs [pres_typeD,listE_nth_in]) 2);
by (etac impE 1);
 by (asm_simp_tac (simpset() delsimps [listE_length,le_iff_plus_unchanged RS sym]) 1);
 by (rtac conjI 1);
  by (blast_tac (claset() addDs [boundedD]) 1);
 by (rtac conjI 1);
  by (blast_tac (claset() addIs[merges_preserves_type]addDs[boundedD]) 1);
 by (blast_tac (claset() addSIs [stable_pres_lemma]) 1);
by (asm_simp_tac (simpset() delsimps [listE_length]) 1);
by (subgoal_tac "!q:set(succs (@ p. p : w)). q < size ss" 1);
 by (blast_tac (claset() addDs [boundedD]) 2);
by (subgoal_tac "step (@ p. p : w) (ss ! (@ p. p : w)) : A" 1);
 by (blast_tac (claset() addIs [pres_typeD]) 2);
by (rtac conjI 1);
 by (blast_tac (claset() addSIs [merges_incr] addIs [le_list_trans]) 1);
by (Clarify_tac 1);
by (EVERY1[dtac bspec, atac, etac mp]);
by (asm_full_simp_tac (simpset() delsimps [listE_length]) 1);
by (blast_tac (claset() addIs [merges_bounded_lemma]) 1);
qed_spec_mp "iter_properties";


Goalw [is_dfa_def,kildall_def]
 "[| semilat(A,r,f); acc r; pres_type step n A; \
\    mono r step n A; bounded succs n|] ==> \
\ is_dfa r (kildall (A,r,f) step succs) step succs n A";
by (Clarify_tac 1);
by (Simp_tac 1);
by (rtac iter_properties 1);
by (asm_simp_tac (simpset() addsimps [unstables_def,stable_def]) 1);
by (blast_tac (claset() addSIs [le_iff_plus_unchanged RS iffD2,listE_nth_in]
              addDs [boundedD,pres_typeD]) 1);
qed "is_dfa_kildall";

Goal
 "[| semilat(A,r,f); acc r; top r T; \
\    pres_type step n A; bounded succs n; \
\    mono r step n A; wti_is_stable_topless r T step wti succs n A |] \
\ ==> is_bcv r T wti n A (kildall (A,r,f) step succs)";
by (REPEAT(ares_tac [is_bcv_dfa,is_dfa_kildall,semilatDorderI] 1));
qed "is_bcv_kildall";
