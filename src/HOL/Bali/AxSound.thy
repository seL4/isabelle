(*  Title:      HOL/Bali/AxSound.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)
header {* Soundness proof for Axiomatic semantics of Java expressions and 
          statements
       *}



theory AxSound = AxSem:

section "validity"

consts

 triple_valid2:: "prog \<Rightarrow> nat \<Rightarrow>        'a triple  \<Rightarrow> bool"
                                                (   "_\<Turnstile>_\<Colon>_"[61,0, 58] 57)
    ax_valids2:: "prog \<Rightarrow> 'a triples \<Rightarrow> 'a triples \<Rightarrow> bool"
                                                ("_,_|\<Turnstile>\<Colon>_" [61,58,58] 57)

defs  triple_valid2_def: "G\<Turnstile>n\<Colon>t \<equiv> case t of {P} t\<succ> {Q} \<Rightarrow>
 \<forall>Y s Z. P Y s Z \<longrightarrow> (\<forall>L. s\<Colon>\<preceq>(G,L) 
 \<longrightarrow> (\<forall>T C. (normal s \<longrightarrow> \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) \<longrightarrow>
 (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s') \<longrightarrow> Q Y' s' Z \<and> s'\<Colon>\<preceq>(G,L))))"

defs  ax_valids2_def:    "G,A|\<Turnstile>\<Colon>ts \<equiv>  \<forall>n. (\<forall>t\<in>A. G\<Turnstile>n\<Colon>t) \<longrightarrow> (\<forall>t\<in>ts. G\<Turnstile>n\<Colon>t)"

lemma triple_valid2_def2: "G\<Turnstile>n\<Colon>{P} t\<succ> {Q} =  
 (\<forall>Y s Z. P Y s Z \<longrightarrow> (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s')\<longrightarrow>  
  (\<forall>L. s\<Colon>\<preceq>(G,L) \<longrightarrow> (\<forall>T C. (normal s \<longrightarrow> \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) \<longrightarrow>  
  Q Y' s' Z \<and> s'\<Colon>\<preceq>(G,L)))))"
apply (unfold triple_valid2_def)
apply (simp (no_asm) add: split_paired_All)
apply blast
done

lemma triple_valid2_eq [rule_format (no_asm)]: 
  "wf_prog G ==> triple_valid2 G = triple_valid G"
apply (rule ext)
apply (rule ext)
apply (rule triple.induct)
apply (simp (no_asm) add: triple_valid_def2 triple_valid2_def2)
apply (rule iffI)
apply  fast
apply clarify
apply (tactic "smp_tac 3 1")
apply (case_tac "normal s")
apply  clarsimp
apply  (blast dest: evaln_eval eval_type_sound [THEN conjunct1])
apply clarsimp
done

lemma ax_valids2_eq: "wf_prog G \<Longrightarrow> G,A|\<Turnstile>\<Colon>ts = G,A|\<Turnstile>ts"
apply (unfold ax_valids_def ax_valids2_def)
apply (force simp add: triple_valid2_eq)
done

lemma triple_valid2_Suc [rule_format (no_asm)]: "G\<Turnstile>Suc n\<Colon>t \<longrightarrow> G\<Turnstile>n\<Colon>t"
apply (induct_tac "t")
apply (subst triple_valid2_def2)
apply (subst triple_valid2_def2)
apply (fast intro: evaln_nonstrict_Suc)
done

lemma Methd_triple_valid2_0: "G\<Turnstile>0\<Colon>{Normal P} Methd C sig-\<succ> {Q}"
apply (clarsimp elim!: evaln_elim_cases simp add: triple_valid2_def2)
done

lemma Methd_triple_valid2_SucI: 
"\<lbrakk>G\<Turnstile>n\<Colon>{Normal P} body G C sig-\<succ>{Q}\<rbrakk> 
  \<Longrightarrow> G\<Turnstile>Suc n\<Colon>{Normal P} Methd C sig-\<succ> {Q}"
apply (simp (no_asm_use) add: triple_valid2_def2)
apply (intro strip, tactic "smp_tac 3 1", clarify)
apply (erule wt_elim_cases, erule evaln_elim_cases)
apply (unfold body_def Let_def)
apply clarsimp
apply blast
done

lemma triples_valid2_Suc: 
 "Ball ts (triple_valid2 G (Suc n)) \<Longrightarrow> Ball ts (triple_valid2 G n)"
apply (fast intro: triple_valid2_Suc)
done

lemma "G|\<Turnstile>n:insert t A = (G\<Turnstile>n:t \<and> G|\<Turnstile>n:A)";
oops


section "soundness"

lemma Methd_sound: 
"\<lbrakk>G,A\<union>  {{P} Methd-\<succ> {Q} | ms}|\<Turnstile>\<Colon>{{P} body G-\<succ> {Q} | ms}\<rbrakk> \<Longrightarrow> 
  G,A|\<Turnstile>\<Colon>{{P} Methd-\<succ> {Q} | ms}"
apply (unfold ax_valids2_def mtriples_def)
apply (rule allI)
apply (induct_tac "n")
apply  (clarify, tactic {* pair_tac "x" 1 *}, simp (no_asm))
apply  (fast intro: Methd_triple_valid2_0)
apply (clarify, tactic {* pair_tac "xa" 1 *}, simp (no_asm))
apply (drule triples_valid2_Suc)
apply (erule (1) notE impE)
apply (drule_tac x = na in spec)
apply (tactic {* auto_tac (claset() addSIs [thm "Methd_triple_valid2_SucI"],
   simpset() addsimps [ball_Un] addloop ("split_all_tac", split_all_tac)) *})
done


lemma valids2_inductI: "\<forall>s t n Y' s'. G\<turnstile>s\<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s') \<longrightarrow> t = c \<longrightarrow>    
  Ball A (triple_valid2 G n) \<longrightarrow> (\<forall>Y Z. P Y s Z \<longrightarrow>  
  (\<forall>L. s\<Colon>\<preceq>(G,L) \<longrightarrow> (\<forall>T C. (normal s \<longrightarrow> \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) \<longrightarrow>  
  Q Y' s' Z \<and> s'\<Colon>\<preceq>(G, L)))) \<Longrightarrow>  
  G,A|\<Turnstile>\<Colon>{ {P} c\<succ> {Q}}"
apply (simp (no_asm) add: ax_valids2_def triple_valid2_def2)
apply clarsimp
done

ML_setup {*
Delsimprocs [evaln_expr_proc,evaln_var_proc,evaln_exprs_proc,evaln_stmt_proc]
*}

lemma Loop_sound: "\<lbrakk>G,A|\<Turnstile>\<Colon>{ {P} e-\<succ> {P'}};  
       G,A|\<Turnstile>\<Colon>{ {Normal (P'\<leftarrow>=True)} .c. {abupd (absorb (Cont l)) .; P}}\<rbrakk> \<Longrightarrow>  
       G,A|\<Turnstile>\<Colon>{ {P} .l\<bullet> While(e) c. {(P'\<leftarrow>=False)\<down>=\<diamondsuit>}}"
apply (rule valids2_inductI)
apply ((rule allI)+, rule impI, tactic {* pair_tac "s" 1*}, tactic {* pair_tac "s'" 1*})
apply (erule evaln.induct)
apply  simp_all (* takes half a minute *)
apply  clarify
apply  (erule_tac V = "G,A|\<Turnstile>\<Colon>{ {?P'} .c. {?P}}" in thin_rl)
apply  (simp_all (no_asm_use) add: ax_valids2_def triple_valid2_def2)
apply  (tactic "smp_tac 1 1", tactic "smp_tac 3 1", force)
apply clarify
apply (rule wt_elim_cases, assumption)
apply (tactic "smp_tac 1 1", tactic "smp_tac 1 1", tactic "smp_tac 3 1", 
       tactic "smp_tac 2 1", tactic "smp_tac 1 1")
apply (erule impE,simp (no_asm),blast)
apply (simp add: imp_conjL split_tupled_all split_paired_All)
apply (case_tac "the_Bool b")
apply  clarsimp
apply  (case_tac "a")
apply (simp_all)
apply clarsimp
apply  (erule_tac V = "c = l\<bullet> While(e) c \<longrightarrow> ?P" in thin_rl)
apply (blast intro: conforms_absorb)
apply blast+
done

declare subst_Bool_def2 [simp del]
lemma all_empty: "(!x. P) = P"
by simp
lemma sound_valid2_lemma: 
"\<lbrakk>\<forall>v n. Ball A (triple_valid2 G n) \<longrightarrow> P v n; Ball A (triple_valid2 G n)\<rbrakk>
 \<Longrightarrow>P v n"
by blast
ML {*
val fullsimptac = full_simp_tac(simpset() delsimps [thm "all_empty"]);
val sound_prepare_tac = EVERY'[REPEAT o thin_tac "?x \<in> ax_derivs G",
 full_simp_tac (simpset()addsimps[thm "ax_valids2_def",thm "triple_valid2_def2",
                                  thm "imp_conjL"] delsimps[thm "all_empty"]),
 Clarify_tac];
val sound_elim_tac = EVERY'[eresolve_tac (thms "evaln_elim_cases"), 
        TRY o eresolve_tac (thms "wt_elim_cases"), fullsimptac, Clarify_tac];
val sound_valid2_tac = REPEAT o FIRST'[smp_tac 1, 
                  datac (thm "sound_valid2_lemma") 1];
val sound_forw_hyp_tac = 
 EVERY'[smp_tac 3 
          ORELSE' EVERY'[dtac spec,dtac spec, dtac spec,etac impE, Fast_tac] 
          ORELSE' EVERY'[dtac spec,dtac spec,etac impE, Fast_tac],
        fullsimptac, 
        smp_tac 2,TRY o smp_tac 1,
        TRY o EVERY'[etac impE, TRY o rtac impI, 
        atac ORELSE' (EVERY' [REPEAT o rtac exI,Blast_tac]),
        fullsimptac, Clarify_tac, TRY o smp_tac 1]]
*}
(* ### rtac conjI,rtac HOL.refl *)
lemma Call_sound: 
"\<lbrakk>wf_prog G; G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> {Q}}; \<forall>a. G,A|\<Turnstile>\<Colon>{ {Q\<leftarrow>Val a} ps\<doteq>\<succ> {R a}};
  \<forall>a vs invC declC l. G,A|\<Turnstile>\<Colon>{ {(R a\<leftarrow>Vals vs \<and>.  
   (\<lambda>s. declC = invocation_declclass 
                    G mode (store s) a statT \<lparr>name=mn,parTs=pTs\<rparr> \<and>
         invC = invocation_class mode (store s) a statT \<and>
            l = locals (store s)) ;.  
   init_lvars G declC \<lparr>name=mn,parTs=pTs\<rparr> mode a vs) \<and>.  
   (\<lambda>s. normal s \<longrightarrow> G\<turnstile>mode\<rightarrow>invC\<preceq>statT)}  
   Methd declC \<lparr>name=mn,parTs=pTs\<rparr>-\<succ> {set_lvars l .; S}}\<rbrakk> \<Longrightarrow>  
  G,A|\<Turnstile>\<Colon>{ {Normal P} {statT,mode}e\<cdot>mn({pTs}ps)-\<succ> {S}}"
apply (tactic "EVERY'[sound_prepare_tac, sound_elim_tac, sound_valid2_tac] 1")
apply (rename_tac x1 s1 x2 s2 ab bb v vs m pTsa statDeclC)
apply (tactic "smp_tac 6 1")
apply (tactic "sound_forw_hyp_tac 1")
apply (tactic "sound_forw_hyp_tac 1")
apply (drule max_spec2mheads)
apply (drule evaln_eval, drule (3) eval_ts)
apply (drule evaln_eval, frule (3) evals_ts)
apply (drule spec,erule impE,rule exI, blast)
(* apply (drule spec,drule spec,drule spec,erule impE,rule exI,blast) *)
apply (case_tac "if static m then x2 else (np a') x2")
defer 1
apply  (rename_tac x, subgoal_tac "(Some x, s2)\<Colon>\<preceq>(G, L)" (* used two times *))
prefer 2 
apply   (force split add: split_if_asm)
apply  (simp del: if_raise_if_None)
apply  (tactic "smp_tac 2 1")
apply (simp only: init_lvars_def2 invmode_Static_eq)
apply (clarsimp simp del: resTy_mthd)
apply  (drule spec,erule swap,erule conforms_set_locals [OF _ lconf_empty])
apply clarsimp
apply (drule Null_staticD)
apply (drule eval_gext', drule (1) conf_gext, frule (3) DynT_propI)
apply (erule impE) apply blast
apply (subgoal_tac 
 "G\<turnstile>invmode (mhd (statDeclC,m)) e
     \<rightarrow>invocation_class (invmode m e) s2 a' statT\<preceq>statT")
defer   apply simp
apply (drule (3) DynT_mheadsD,simp,simp)
apply (clarify, drule wf_mdeclD1, clarify)
apply (frule ty_expr_is_type) apply simp
apply (subgoal_tac "invmode (mhd (statDeclC,m)) e = IntVir \<longrightarrow> a' \<noteq> Null")
defer   apply simp
apply (frule (2) wt_MethdI)
apply clarify
apply (drule (2) conforms_init_lvars)
apply   (simp) 
apply   (assumption)+
apply   simp
apply   (assumption)+
apply   (rule impI) apply simp
apply   simp
apply   simp
apply   (rule Ball_weaken)
apply     assumption
apply     (force simp add: is_acc_type_def)
apply (tactic "smp_tac 2 1")
apply simp
apply (tactic "smp_tac 1 1")
apply (erule_tac V = "?P \<longrightarrow> ?Q" in thin_rl) 
apply (erule impE)
apply   (rule exI)+ 
apply   (subgoal_tac "is_static dm = (static m)") 
prefer 2  apply (simp add: member_is_static_simp)
apply   (simp only: )
apply   (simp only: sig.simps)
apply (force dest!: evaln_eval eval_gext' elim: conforms_return 
             del: impCE simp add: init_lvars_def2)
done

lemma Init_sound: "\<lbrakk>wf_prog G; the (class G C) = c;  
      G,A|\<Turnstile>\<Colon>{ {Normal ((P \<and>. Not \<circ> initd C) ;. supd (init_class_obj G C))}  
             .(if C = Object then Skip else Init (super c)). {Q}};  
  \<forall>l. G,A|\<Turnstile>\<Colon>{ {Q \<and>. (\<lambda>s. l = locals (store s)) ;. set_lvars empty}  
            .init c. {set_lvars l .; R}}\<rbrakk> \<Longrightarrow>  
      G,A|\<Turnstile>\<Colon>{ {Normal (P \<and>. Not \<circ> initd C)} .Init C. {R}}"
apply (tactic "EVERY'[sound_prepare_tac, sound_elim_tac,sound_valid2_tac] 1")
apply (tactic {* instantiate_tac [("l24","\<lambda> n Y Z sa Y' s' L y a b aa ba ab bb. locals b")]*})
apply (clarsimp simp add: split_paired_Ex)
apply (drule spec, drule spec, drule spec, erule impE)
apply  (erule_tac V = "All ?P" in thin_rl, fast)
apply clarsimp
apply (tactic "smp_tac 2 1", drule spec, erule impE, 
       erule (3) conforms_init_class_obj)
apply (drule (1) wf_prog_cdecl)
apply (erule impE, rule exI,erule_tac V = "All ?P" in thin_rl,
       force dest: wf_cdecl_supD split add: split_if simp add: is_acc_class_def)
apply clarify
apply (drule spec)
apply (drule spec)
apply (drule spec)
apply  (erule impE)
apply ( fast)
apply (simp (no_asm_use) del: empty_def2)
apply (tactic "smp_tac 2 1")
apply (drule spec, erule impE, erule conforms_set_locals, rule lconf_empty)
apply (erule impE,rule impI,rule exI, erule wf_cdecl_wt_init)
apply clarsimp
apply (erule (1) conforms_return, force dest: evaln_eval eval_gext')
done

lemma all_conjunct2: "\<forall>l. P' l \<and> P l \<Longrightarrow> \<forall>l. P l"
by fast

lemma all4_conjunct2: 
  "\<forall>a vs D l. (P' a vs D l \<and> P a vs D l) \<Longrightarrow> \<forall>a vs D l. P a vs D l"
by fast

lemmas sound_lemmas = Init_sound Loop_sound Methd_sound

lemma ax_sound2: "wf_prog G \<Longrightarrow> G,A|\<turnstile>ts \<Longrightarrow> G,A|\<Turnstile>\<Colon>ts"
apply (erule ax_derivs.induct)
prefer 20 (* Call *)
apply (erule (1) Call_sound) apply simp apply force apply force 

apply (tactic {* TRYALL (eresolve_tac (thms "sound_lemmas") THEN_ALL_NEW 
    eresolve_tac [asm_rl, thm "all_conjunct2", thm "all4_conjunct2"]) *})

apply(tactic "COND (has_fewer_prems(30+3)) (ALLGOALS sound_prepare_tac) no_tac")

               (*empty*)
apply        fast (* insert *)
apply       fast (* asm *)
(*apply    fast *) (* cut *)
apply     fast (* weaken *)
apply    (tactic "smp_tac 3 1", clarify, tactic "smp_tac 1 1", frule evaln_eval,
(* conseq *)case_tac"fst s",clarsimp simp add: eval_type_sound [THEN conjunct1],
clarsimp)
apply   (simp (no_asm_use) add: type_ok_def, drule evaln_eval,fast) (* hazard *)
apply  force (* Abrupt *)

(* 25 subgoals *)
apply (tactic {* ALLGOALS sound_elim_tac *})(* LVar, Lit, Super, Nil, Skip,Do *)
apply (tactic {* ALLGOALS (asm_simp_tac (noAll_simpset() 
                          delsimps [thm "all_empty"])) *})    (* Done *)
(* for FVar *)
apply (frule wf_ws_prog) 
apply (frule ty_expr_is_type [THEN type_is_class, 
                              THEN accfield_declC_is_class])
apply (simp,simp,simp) 
apply (frule_tac [4] wt_init_comp_ty) (* for NewA*)
apply (tactic "ALLGOALS sound_valid2_tac")
apply (tactic "TRYALL sound_forw_hyp_tac") (* Cast, Inst, Acc, Expr *)
apply (tactic {* TRYALL (EVERY'[dtac spec, TRY o EVERY'[rotate_tac ~1, 
  dtac spec], dtac conjunct2, smp_tac 1, 
  TRY o dres_inst_tac [("P","P'")] (thm "subst_Bool_the_BoolI")]) *})
apply (frule_tac [14] x = x1 in conforms_NormI)  (* for Fin *)


(* 15 subgoals *)
(* FVar *)
apply (tactic "sound_forw_hyp_tac 1")
apply (clarsimp simp add: fvar_def2 Let_def split add: split_if_asm)

(* AVar *)
(*
apply (drule spec, drule spec, erule impE, fast)
apply (simp)
apply (tactic "smp_tac 2 1")
apply (tactic "smp_tac 1 1")
apply (erule impE)
apply (rule impI)
apply (rule exI)+
apply blast
apply (clarsimp simp add: avar_def2)
*)
apply (tactic "sound_forw_hyp_tac 1")
apply (clarsimp simp add: avar_def2)

(* NewC *)
apply (clarsimp simp add: is_acc_class_def)
apply (erule (1) halloc_conforms, simp, simp)

(* NewA *)
apply (tactic "sound_forw_hyp_tac 1")
apply (rule conjI,blast)
apply (erule (1) halloc_conforms, simp, simp, simp add: is_acc_type_def)

(* Ass *)
apply (tactic "sound_forw_hyp_tac 1")
apply (case_tac "aa")
prefer 2
apply  clarsimp
apply (drule evaln_eval)+
apply (frule (3) eval_ts)
apply clarsimp
apply (frule (3) evar_ts [THEN conjunct2])
apply (frule wf_ws_prog)
apply (drule (2) conf_widen)
apply (drule_tac "s1.0" = b in eval_gext')
apply (clarsimp simp add: assign_conforms_def)

(* Cond *)

apply (tactic "smp_tac 3 1") apply (tactic "smp_tac 2 1") 
apply (tactic "smp_tac 1 1") apply (erule impE) 
apply (rule impI,rule exI) 
apply (rule_tac x = "if the_Bool b then T1 else T2" in exI)
apply (force split add: split_if)
apply assumption

(* Body *)
apply (tactic "sound_forw_hyp_tac 1")
apply (rule conforms_absorb,assumption)

(* Lab *)
apply (tactic "sound_forw_hyp_tac 1")
apply (rule conforms_absorb,assumption)

(* If *)
apply (tactic "sound_forw_hyp_tac 1")
apply (tactic "sound_forw_hyp_tac 1")
apply (force split add: split_if)

(* Throw *)
apply (drule evaln_eval, drule (3) eval_ts)
apply clarsimp
apply (drule (3) Throw_lemma)
apply clarsimp

(* Try *)
apply (frule (1) sxalloc_type_sound)
apply (erule sxalloc_elim_cases2)
apply  (tactic "smp_tac 3 1")
apply  (clarsimp split add: option.split_asm)
apply (clarsimp split add: option.split_asm)
apply (tactic "smp_tac 1 1")
apply (simp only: split add: split_if_asm)
prefer 2
apply  (tactic "smp_tac 3 1", erule_tac V = "All ?P" in thin_rl, clarsimp)
apply (drule spec, erule_tac V = "All ?P" in thin_rl, drule spec, drule spec, 
       erule impE, force)
apply (frule (2) Try_lemma)
apply clarsimp
apply (fast elim!: conforms_deallocL)

(* Fin *)
apply (tactic "sound_forw_hyp_tac 1")
apply (case_tac "x1", force)
apply clarsimp
apply (drule evaln_eval, drule (4) Fin_lemma)
done



declare subst_Bool_def2 [simp]

theorem ax_sound: 
 "wf_prog G \<Longrightarrow> G,(A::'a triple set)|\<turnstile>(ts::'a triple set) \<Longrightarrow> G,A|\<Turnstile>ts"
apply (subst ax_valids2_eq [symmetric])
apply  assumption
apply (erule (1) ax_sound2)
done


end
