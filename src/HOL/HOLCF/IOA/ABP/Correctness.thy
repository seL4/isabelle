(*  Title:      HOL/HOLCF/IOA/ABP/Correctness.thy
    Author:     Olaf Müller
*)

section \<open>The main correctness proof: System_fin implements System\<close>

theory Correctness
imports IOA.IOA Env Impl Impl_finite
begin

ML_file "Check.ML"

primrec reduce :: "'a list => 'a list"
where
  reduce_Nil:  "reduce [] = []"
| reduce_Cons: "reduce(x#xs) =
                 (case xs of
                     [] => [x]
               |   y#ys => (if (x=y)
                              then reduce xs
                              else (x#(reduce xs))))"

definition
  abs where
    "abs  =
      (%p.(fst(p),(fst(snd(p)),(fst(snd(snd(p))),
       (reduce(fst(snd(snd(snd(p))))),reduce(snd(snd(snd(snd(p))))))))))"

definition
  system_ioa :: "('m action, bool * 'm impl_state)ioa" where
  "system_ioa = (env_ioa \<parallel> impl_ioa)"

definition
  system_fin_ioa :: "('m action, bool * 'm impl_state)ioa" where
  "system_fin_ioa = (env_ioa \<parallel> impl_fin_ioa)"


axiomatization where
  sys_IOA: "IOA system_ioa" and
  sys_fin_IOA: "IOA system_fin_ioa"



declare split_paired_All [simp del] Collect_empty_eq [simp del]

lemmas [simp] =
  srch_asig_def rsch_asig_def rsch_ioa_def srch_ioa_def ch_ioa_def
  ch_asig_def srch_actions_def rsch_actions_def rename_def rename_set_def asig_of_def
  actions_def exis_elim srch_trans_def rsch_trans_def ch_trans_def
  trans_of_def asig_projections set_lemmas

lemmas abschannel_fin [simp] =
  srch_fin_asig_def rsch_fin_asig_def
  rsch_fin_ioa_def srch_fin_ioa_def
  ch_fin_ioa_def ch_fin_trans_def ch_fin_asig_def

lemmas impl_ioas = sender_ioa_def receiver_ioa_def
  and impl_trans = sender_trans_def receiver_trans_def
  and impl_asigs = sender_asig_def receiver_asig_def

declare let_weak_cong [cong]
declare ioa_triple_proj [simp] starts_of_par [simp]

lemmas env_ioas = env_ioa_def env_asig_def env_trans_def
lemmas hom_ioas =
  env_ioas [simp] impl_ioas [simp] impl_trans [simp] impl_asigs [simp]
  asig_projections set_lemmas


subsection \<open>lemmas about reduce\<close>

lemma l_iff_red_nil: "(reduce l = []) = (l = [])"
  by (induct l) (auto split: list.split)

lemma hd_is_reduce_hd: "s ~= [] --> hd s = hd (reduce s)"
  by (induct s) (auto split: list.split)

text \<open>to be used in the following Lemma\<close>
lemma rev_red_not_nil [rule_format]:
    "l ~= [] --> reverse (reduce l) ~= []"
  by (induct l) (auto split: list.split)

text \<open>shows applicability of the induction hypothesis of the following Lemma 1\<close>
lemma last_ind_on_first:
    "l ~= [] ==> hd (reverse (reduce (a # l))) = hd (reverse (reduce l))"
  apply simp
  apply (tactic \<open>auto_tac (put_simpset HOL_ss @{context}
    addsimps (@{thms reverse.simps} @ [@{thm hd_append}, @{thm rev_red_not_nil}])
    |> Splitter.add_split @{thm list.split})\<close>)
  done

text \<open>Main Lemma 1 for \<open>S_pkt\<close> in showing that reduce is refinement.\<close>
lemma reduce_hd:
   "if x=hd(reverse(reduce(l))) & reduce(l)~=[] then
       reduce(l@[x])=reduce(l) else
       reduce(l@[x])=reduce(l)@[x]"
apply (simplesubst if_split)
apply (rule conjI)
txt \<open>\<open>-->\<close>\<close>
apply (induct_tac "l")
apply (simp (no_asm))
apply (case_tac "list=[]")
 apply simp
 apply (rule impI)
apply (simp (no_asm))
apply (cut_tac l = "list" in cons_not_nil)
 apply (simp del: reduce_Cons)
 apply (erule exE)+
 apply hypsubst
apply (simp del: reduce_Cons add: last_ind_on_first l_iff_red_nil)
txt \<open>\<open><--\<close>\<close>
apply (simp (no_asm) add: and_de_morgan_and_absorbe l_iff_red_nil)
apply (induct_tac "l")
apply (simp (no_asm))
apply (case_tac "list=[]")
apply (cut_tac [2] l = "list" in cons_not_nil)
apply simp
apply (auto simp del: reduce_Cons simp add: last_ind_on_first l_iff_red_nil split: if_split)
apply simp
done


text \<open>Main Lemma 2 for R_pkt in showing that reduce is refinement.\<close>
lemma reduce_tl: "s~=[] ==>
     if hd(s)=hd(tl(s)) & tl(s)~=[] then
       reduce(tl(s))=reduce(s) else
       reduce(tl(s))=tl(reduce(s))"
apply (cut_tac l = "s" in cons_not_nil)
apply simp
apply (erule exE)+
apply (auto split: list.split)
done


subsection \<open>Channel Abstraction\<close>

declare if_split [split del]

lemma channel_abstraction: "is_weak_ref_map reduce ch_ioa ch_fin_ioa"
apply (simp (no_asm) add: is_weak_ref_map_def)
txt \<open>main-part\<close>
apply (rule allI)+
apply (rule imp_conj_lemma)
apply (induct_tac "a")
txt \<open>2 cases\<close>
apply (simp_all (no_asm) cong del: if_weak_cong add: externals_def)
txt \<open>fst case\<close>
 apply (rule impI)
 apply (rule disjI2)
apply (rule reduce_hd)
txt \<open>snd case\<close>
 apply (rule impI)
 apply (erule conjE)+
 apply (erule disjE)
apply (simp add: l_iff_red_nil)
apply (erule hd_is_reduce_hd [THEN mp])
apply (simp add: l_iff_red_nil)
apply (rule conjI)
apply (erule hd_is_reduce_hd [THEN mp])
apply (rule bool_if_impl_or [THEN mp])
apply (erule reduce_tl)
done

declare if_split [split]

lemma sender_abstraction: "is_weak_ref_map reduce srch_ioa srch_fin_ioa"
apply (tactic \<open>
  simp_tac (put_simpset HOL_ss @{context}
    addsimps [@{thm srch_fin_ioa_def}, @{thm rsch_fin_ioa_def},
      @{thm srch_ioa_def}, @{thm rsch_ioa_def}, @{thm rename_through_pmap},
      @{thm channel_abstraction}]) 1\<close>)
done

lemma receiver_abstraction: "is_weak_ref_map reduce rsch_ioa rsch_fin_ioa"
apply (tactic \<open>
  simp_tac (put_simpset HOL_ss @{context}
    addsimps [@{thm srch_fin_ioa_def}, @{thm rsch_fin_ioa_def},
      @{thm srch_ioa_def}, @{thm rsch_ioa_def}, @{thm rename_through_pmap},
      @{thm channel_abstraction}]) 1\<close>)
done


text \<open>3 thms that do not hold generally! The lucky restriction here is
   the absence of internal actions.\<close>
lemma sender_unchanged: "is_weak_ref_map (%id. id) sender_ioa sender_ioa"
apply (simp (no_asm) add: is_weak_ref_map_def)
txt \<open>main-part\<close>
apply (rule allI)+
apply (induct_tac a)
txt \<open>7 cases\<close>
apply (simp_all (no_asm) add: externals_def)
done

text \<open>2 copies of before\<close>
lemma receiver_unchanged: "is_weak_ref_map (%id. id) receiver_ioa receiver_ioa"
apply (simp (no_asm) add: is_weak_ref_map_def)
txt \<open>main-part\<close>
apply (rule allI)+
apply (induct_tac a)
txt \<open>7 cases\<close>
apply (simp_all (no_asm) add: externals_def)
done

lemma env_unchanged: "is_weak_ref_map (%id. id) env_ioa env_ioa"
apply (simp (no_asm) add: is_weak_ref_map_def)
txt \<open>main-part\<close>
apply (rule allI)+
apply (induct_tac a)
txt \<open>7 cases\<close>
apply (simp_all (no_asm) add: externals_def)
done


lemma compat_single_ch: "compatible srch_ioa rsch_ioa"
apply (simp add: compatible_def Int_def)
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

text \<open>totally the same as before\<close>
lemma compat_single_fin_ch: "compatible srch_fin_ioa rsch_fin_ioa"
apply (simp add: compatible_def Int_def)
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

lemmas del_simps = trans_of_def srch_asig_def rsch_asig_def
  asig_of_def actions_def srch_trans_def rsch_trans_def srch_ioa_def
  srch_fin_ioa_def rsch_fin_ioa_def rsch_ioa_def sender_trans_def
  receiver_trans_def set_lemmas

lemma compat_rec: "compatible receiver_ioa (srch_ioa \<parallel> rsch_ioa)"
apply (simp del: del_simps
  add: compatible_def asig_of_par asig_comp_def actions_def Int_def)
apply simp
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

text \<open>5 proofs totally the same as before\<close>
lemma compat_rec_fin: "compatible receiver_ioa (srch_fin_ioa \<parallel> rsch_fin_ioa)"
apply (simp del: del_simps
  add: compatible_def asig_of_par asig_comp_def actions_def Int_def)
apply simp
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

lemma compat_sen: "compatible sender_ioa
       (receiver_ioa \<parallel> srch_ioa \<parallel> rsch_ioa)"
apply (simp del: del_simps
  add: compatible_def asig_of_par asig_comp_def actions_def Int_def)
apply simp
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

lemma compat_sen_fin: "compatible sender_ioa
       (receiver_ioa \<parallel> srch_fin_ioa \<parallel> rsch_fin_ioa)"
apply (simp del: del_simps
  add: compatible_def asig_of_par asig_comp_def actions_def Int_def)
apply simp
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

lemma compat_env: "compatible env_ioa
       (sender_ioa \<parallel> receiver_ioa \<parallel> srch_ioa \<parallel> rsch_ioa)"
apply (simp del: del_simps
  add: compatible_def asig_of_par asig_comp_def actions_def Int_def)
apply simp
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done

lemma compat_env_fin: "compatible env_ioa
       (sender_ioa \<parallel> receiver_ioa \<parallel> srch_fin_ioa \<parallel> rsch_fin_ioa)"
apply (simp del: del_simps
  add: compatible_def asig_of_par asig_comp_def actions_def Int_def)
apply simp
apply (rule set_eqI)
apply (induct_tac x)
apply simp_all
done


text \<open>lemmata about externals of channels\<close>
lemma ext_single_ch: "externals(asig_of(srch_fin_ioa)) = externals(asig_of(srch_ioa)) &
    externals(asig_of(rsch_fin_ioa)) = externals(asig_of(rsch_ioa))"
  by (simp add: externals_def)


subsection \<open>Soundness of Abstraction\<close>

lemmas ext_simps = externals_of_par ext_single_ch
  and compat_simps = compat_single_ch compat_single_fin_ch compat_rec
    compat_rec_fin compat_sen compat_sen_fin compat_env compat_env_fin
  and abstractions = env_unchanged sender_unchanged
    receiver_unchanged sender_abstraction receiver_abstraction


(* FIX: this proof should be done with compositionality on trace level, not on
        weak_ref_map level, as done here with fxg_is_weak_ref_map_of_product_IOA

Goal "is_weak_ref_map  abs  system_ioa  system_fin_ioa"

by (simp_tac (impl_ss delsimps ([srch_ioa_def, rsch_ioa_def, srch_fin_ioa_def,
                                 rsch_fin_ioa_def] @ env_ioas @ impl_ioas)
                      addsimps [system_def, system_fin_def, abs_def,
                                impl_ioa_def, impl_fin_ioa_def, sys_IOA,
                                sys_fin_IOA]) 1);

by (REPEAT (EVERY[rtac fxg_is_weak_ref_map_of_product_IOA 1,
                  simp_tac (ss addsimps abstractions) 1,
                  rtac conjI 1]));

by (ALLGOALS (simp_tac (ss addsimps ext_ss @ compat_ss)));

qed "system_refinement";
*)

end
