(*  Title:      isabelle/Bali/AxCompl.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {*
Completeness proof for Axiomatic semantics of Java expressions and statements
*}

theory AxCompl = AxSem:

text {*
design issues:
\begin{itemize}
\item proof structured by Most General Formulas (-> Thomas Kleymann)
\end{itemize}
*}
section "set of not yet initialzed classes"

constdefs

  nyinitcls :: "prog \<Rightarrow> state \<Rightarrow> qtname set"
 "nyinitcls G s \<equiv> {C. is_class G C \<and> \<not> initd C s}"

lemma nyinitcls_subset_class: "nyinitcls G s \<subseteq> {C. is_class G C}"
apply (unfold nyinitcls_def)
apply fast
done

lemmas finite_nyinitcls [simp] =
   finite_is_class [THEN nyinitcls_subset_class [THEN finite_subset], standard]

lemma card_nyinitcls_bound: "card (nyinitcls G s) \<le> card {C. is_class G C}"
apply (rule nyinitcls_subset_class [THEN finite_is_class [THEN card_mono]])
done

lemma nyinitcls_set_locals_cong [simp]: 
  "nyinitcls G (x,set_locals l s) = nyinitcls G (x,s)"
apply (unfold nyinitcls_def)
apply (simp (no_asm))
done

lemma nyinitcls_abrupt_cong [simp]: "nyinitcls G (f x, y) = nyinitcls G (x, y)"
apply (unfold nyinitcls_def)
apply (simp (no_asm))
done

lemma nyinitcls_abupd_cong [simp]:"!!s. nyinitcls G (abupd f s) = nyinitcls G s"
apply (unfold nyinitcls_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done

lemma card_nyinitcls_abrupt_congE [elim!]: 
        "card (nyinitcls G (x, s)) \<le> n \<Longrightarrow> card (nyinitcls G (y, s)) \<le> n"
apply (unfold nyinitcls_def)
apply auto
done

lemma nyinitcls_new_xcpt_var [simp]: 
"nyinitcls G (new_xcpt_var vn s) = nyinitcls G s"
apply (unfold nyinitcls_def)
apply (induct_tac "s")
apply (simp (no_asm))
done

lemma nyinitcls_init_lvars [simp]: 
  "nyinitcls G ((init_lvars G C sig mode a' pvs) s) = nyinitcls G s"
apply (induct_tac "s")
apply (simp (no_asm) add: init_lvars_def2 split add: split_if)
done

lemma nyinitcls_emptyD: "\<lbrakk>nyinitcls G s = {}; is_class G C\<rbrakk> \<Longrightarrow> initd C s"
apply (unfold nyinitcls_def)
apply fast
done

lemma card_Suc_lemma: "\<lbrakk>card (insert a A) \<le> Suc n; a\<notin>A; finite A\<rbrakk> \<Longrightarrow> card A \<le> n"
apply (rotate_tac 1)
apply clarsimp
done

lemma nyinitcls_le_SucD: 
"\<lbrakk>card (nyinitcls G (x,s)) \<le> Suc n; \<not>inited C (globs s); class G C=Some y\<rbrakk> \<Longrightarrow> 
  card (nyinitcls G (x,init_class_obj G C s)) \<le> n"
apply (subgoal_tac 
        "nyinitcls G (x,s) = insert C (nyinitcls G (x,init_class_obj G C s))")
apply  clarsimp
apply  (erule thin_rl)
apply  (rule card_Suc_lemma [OF _ _ finite_nyinitcls])
apply   (auto dest!: not_initedD elim!: 
              simp add: nyinitcls_def inited_def split add: split_if_asm)
done

ML {* bind_thm("inited_gext'",permute_prems 0 1 (thm "inited_gext")) *}

lemma nyinitcls_gext: "snd s\<le>|snd s' \<Longrightarrow> nyinitcls G s' \<subseteq> nyinitcls G s"
apply (unfold nyinitcls_def)
apply (force dest!: inited_gext')
done

lemma card_nyinitcls_gext: 
  "\<lbrakk>snd s\<le>|snd s'; card (nyinitcls G s) \<le> n\<rbrakk>\<Longrightarrow> card (nyinitcls G s') \<le> n"
apply (rule le_trans)
apply  (rule card_mono)
apply   (rule finite_nyinitcls)
apply  (erule nyinitcls_gext)
apply assumption
done


section "init-le"

constdefs
  init_le :: "prog \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"            ("_\<turnstile>init\<le>_"  [51,51] 50)
 "G\<turnstile>init\<le>n \<equiv> \<lambda>s. card (nyinitcls G s) \<le> n"
  
lemma init_le_def2 [simp]: "(G\<turnstile>init\<le>n) s = (card (nyinitcls G s)\<le>n)"
apply (unfold init_le_def)
apply auto
done

lemma All_init_leD: "\<forall>n::nat. G,A\<turnstile>{P \<and>. G\<turnstile>init\<le>n} t\<succ> {Q} \<Longrightarrow> G,A\<turnstile>{P} t\<succ> {Q}"
apply (drule spec)
apply (erule conseq1)
apply clarsimp
apply (rule card_nyinitcls_bound)
done

section "Most General Triples and Formulas"

constdefs

  remember_init_state :: "state assn"                ("\<doteq>")
  "\<doteq> \<equiv> \<lambda>Y s Z. s = Z"

lemma remember_init_state_def2 [simp]: "\<doteq> Y = op ="
apply (unfold remember_init_state_def)
apply (simp (no_asm))
done

consts
  
  MGF ::"[state assn, term, prog] \<Rightarrow> state triple"   ("{_} _\<succ> {_\<rightarrow>}"[3,65,3]62)
  MGFn::"[nat       , term, prog] \<Rightarrow> state triple" ("{=:_} _\<succ> {_\<rightarrow>}"[3,65,3]62)

defs
  

  MGF_def:
  "{P} t\<succ> {G\<rightarrow>} \<equiv> {P} t\<succ> {\<lambda>Y s' s. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y,s')}"

  MGFn_def:
  "{=:n} t\<succ> {G\<rightarrow>} \<equiv> {\<doteq> \<and>. G\<turnstile>init\<le>n} t\<succ> {G\<rightarrow>}"

(* unused *)
lemma MGF_valid: "G,{}\<Turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (unfold MGF_def)
apply (force dest!: evaln_eval simp add: ax_valids_def triple_valid_def2)
done

lemma MGF_res_eq_lemma [simp]: 
  "(\<forall>Y' Y s. Y = Y' \<and> P s \<longrightarrow> Q s) = (\<forall>s. P s \<longrightarrow> Q s)"
apply auto
done

lemma MGFn_def2: 
"G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>} = G,A\<turnstile>{\<doteq> \<and>. G\<turnstile>init\<le>n} 
                    t\<succ> {\<lambda>Y s' s. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y,s')}"
apply (unfold MGFn_def MGF_def)
apply fast
done

lemma MGF_MGFn_iff: "G,A\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>} = (\<forall>n. G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>})"
apply (simp (no_asm_use) add: MGFn_def2 MGF_def)
apply safe
apply  (erule_tac [2] All_init_leD)
apply (erule conseq1)
apply clarsimp
done

lemma MGFnD: 
"G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>} \<Longrightarrow>  
 G,A\<turnstile>{(\<lambda>Y' s' s. s' = s           \<and> P s) \<and>. G\<turnstile>init\<le>n}  
 t\<succ>  {(\<lambda>Y' s' s. G\<turnstile>s\<midarrow>t\<succ>\<rightarrow>(Y',s') \<and> P s) \<and>. G\<turnstile>init\<le>n}"
apply (unfold init_le_def)
apply (simp (no_asm_use) add: MGFn_def2)
apply (erule conseq12)
apply clarsimp
apply (erule (1) eval_gext [THEN card_nyinitcls_gext])
done
lemmas MGFnD' = MGFnD [of _ _ _ _ "\<lambda>x. True"] 

lemma MGFNormalI: "G,A\<turnstile>{Normal \<doteq>} t\<succ> {G\<rightarrow>} \<Longrightarrow>  
  G,(A::state triple set)\<turnstile>{\<doteq>::state assn} t\<succ> {G\<rightarrow>}"
apply (unfold MGF_def)
apply (rule ax_Normal_cases)
apply  (erule conseq1)
apply  clarsimp
apply (rule ax_derivs.Abrupt [THEN conseq1])
apply (clarsimp simp add: Let_def)
done

lemma MGFNormalD: "G,A\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>} \<Longrightarrow> G,A\<turnstile>{Normal \<doteq>} t\<succ> {G\<rightarrow>}"
apply (unfold MGF_def)
apply (erule conseq1)
apply clarsimp
done

lemma MGFn_NormalI: 
"G,(A::state triple set)\<turnstile>{Normal((\<lambda>Y' s' s. s'=s \<and> normal s) \<and>. G\<turnstile>init\<le>n)}t\<succ> 
 {\<lambda>Y s' s. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y,s')} \<Longrightarrow> G,A\<turnstile>{=:n}t\<succ>{G\<rightarrow>}"
apply (simp (no_asm_use) add: MGFn_def2)
apply (rule ax_Normal_cases)
apply  (erule conseq1)
apply  clarsimp
apply (rule ax_derivs.Abrupt [THEN conseq1])
apply (clarsimp simp add: Let_def)
done

lemma MGFn_free_wt: 
  "(\<exists>T L C. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) 
    \<longrightarrow> G,(A::state triple set)\<turnstile>{=:n} t\<succ> {G\<rightarrow>} 
   \<Longrightarrow> G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>}"
apply (rule MGFn_NormalI)
apply (rule ax_free_wt)
apply (auto elim: conseq12 simp add: MGFn_def MGF_def)
done


section "main lemmas"

declare fun_upd_apply [simp del]
declare splitI2 [rule del] (*prevents ugly renaming of state variables*)

ML_setup {* 
Delsimprocs [eval_expr_proc, eval_var_proc, eval_exprs_proc, eval_stmt_proc]
*} (*prevents modifying rhs of MGF*)
ML {*
val eval_css = (claset() delrules [thm "eval.Abrupt"] addSIs (thms "eval.intros") 
                delrules[thm "eval.Expr", thm "eval.Init", thm "eval.Try"] 
                addIs   [thm "eval.Expr", thm "eval.Init"]
                addSEs[thm "eval.Try"] delrules[equalityCE],
                simpset() addsimps [split_paired_all,Let_def]
 addsimprocs [eval_expr_proc,eval_var_proc,eval_exprs_proc,eval_stmt_proc]);
val eval_Force_tac = force_tac eval_css;

val wt_prepare_tac = EVERY'[
    rtac (thm "MGFn_free_wt"),
    clarsimp_tac (claset() addSEs (thms "wt_elim_cases"), simpset())]
val compl_prepare_tac = EVERY'[rtac (thm "MGFn_NormalI"), Simp_tac]
val forw_hyp_tac = EVERY'[etac (thm "MGFnD'" RS thm "conseq12"), Clarsimp_tac]
val forw_hyp_eval_Force_tac = 
         EVERY'[TRY o rtac allI, forw_hyp_tac, eval_Force_tac]
*}

lemma MGFn_Init: "\<forall>m. Suc m\<le>n \<longrightarrow> (\<forall>t. G,A\<turnstile>{=:m} t\<succ> {G\<rightarrow>}) \<Longrightarrow>  
  G,(A::state triple set)\<turnstile>{=:n} In1r (Init C)\<succ> {G\<rightarrow>}"
apply (tactic "wt_prepare_tac 1")
(* requires is_class G C two times for nyinitcls *)
apply (tactic "compl_prepare_tac 1")
apply (rule_tac C = "initd C" in ax_cases)
apply  (rule ax_derivs.Done [THEN conseq1])
apply  (clarsimp intro!: init_done)
apply (rule_tac y = n in nat.exhaust, clarsimp)
apply  (rule ax_impossible [THEN conseq1])
apply  (force dest!: nyinitcls_emptyD)
apply clarsimp
apply (drule_tac x = "nat" in spec)
apply clarsimp
apply (rule_tac Q = " (\<lambda>Y s' (x,s) . G\<turnstile> (x,init_class_obj G C s) \<midarrow> (if C=Object then Skip else Init (super (the (class G C))))\<rightarrow> s' \<and> x=None \<and> \<not>inited C (globs s)) \<and>. G\<turnstile>init\<le>nat" in ax_derivs.Init)
apply   simp
apply  (rule_tac P' = "Normal ((\<lambda>Y s' s. s' = supd (init_class_obj G C) s \<and> normal s \<and> \<not> initd C s) \<and>. G\<turnstile>init\<le>nat) " in conseq1)
prefer 2
apply   (force elim!: nyinitcls_le_SucD)
apply  (simp split add: split_if, rule conjI, clarify)
apply   (rule ax_derivs.Skip [THEN conseq1], tactic "eval_Force_tac 1")
apply  clarify
apply  (drule spec)
apply  (erule MGFnD' [THEN conseq12])
apply  (tactic "force_tac (claset(), simpset() addsimprocs[eval_stmt_proc]) 1")
apply (rule allI)
apply (drule spec)
apply (erule MGFnD' [THEN conseq12])
apply clarsimp
apply (tactic {* pair_tac "sa" 1 *})
apply (tactic"clarsimp_tac (claset(), simpset() addsimprocs[eval_stmt_proc]) 1")
apply (rule eval_Init, force+)
done
lemmas MGFn_InitD = MGFn_Init [THEN MGFnD, THEN ax_NormalD]

lemma MGFn_Call: 
"\<lbrakk>\<forall>C sig. G,(A::state triple set)\<turnstile>{=:n} In1l (Methd C sig)\<succ> {G\<rightarrow>};  
  G,A\<turnstile>{=:n} In1l e\<succ> {G\<rightarrow>}; G,A\<turnstile>{=:n} In3 ps\<succ> {G\<rightarrow>}\<rbrakk> \<Longrightarrow>  
  G,A\<turnstile>{=:n} In1l ({statT,mode}e\<cdot>mn({pTs'}ps))\<succ> {G\<rightarrow>}"
apply (tactic "wt_prepare_tac 1") (* required for equating mode = invmode m e *)
apply (tactic "compl_prepare_tac 1")
apply (rule_tac R = "\<lambda>a'. (\<lambda>Y (x2,s2) (x,s) . x = None \<and> (\<exists>s1 pvs. G\<turnstile>Norm s \<midarrow>e-\<succ>a'\<rightarrow> s1 \<and> Y = In3 pvs \<and> G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>pvs\<rightarrow> (x2,s2))) \<and>. G\<turnstile>init\<le>n" in ax_derivs.Call)
apply  (erule MGFnD [THEN ax_NormalD])
apply safe
apply  (erule_tac V = "All ?P" in thin_rl, tactic "forw_hyp_eval_Force_tac 1")
apply (drule spec, drule spec)
apply (erule MGFnD' [THEN conseq12])
apply (tactic "clarsimp_tac eval_css 1")
apply (erule (1) eval_Call)
apply   (rule HOL.refl)
apply  (simp (no_asm_simp))+
done

lemma MGF_altern: "G,A\<turnstile>{Normal (\<doteq> \<and>. p)} t\<succ> {G\<rightarrow>} =  
 G,A\<turnstile>{Normal ((\<lambda>Y s Z. \<forall>w s'. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w,s') \<longrightarrow> (w,s') = Z) \<and>. p)} 
  t\<succ> {\<lambda>Y s Z. (Y,s) = Z}"
apply (unfold MGF_def)
apply (auto del: conjI elim!: conseq12)
apply (case_tac "\<exists>w s. G\<turnstile>Norm sa \<midarrow>t\<succ>\<rightarrow> (w,s) ")
apply  (fast dest: unique_eval)
apply clarsimp
apply (erule thin_rl)
apply (erule thin_rl)
apply (drule split_paired_All [THEN subst])
apply (clarsimp elim!: state_not_single)
done


lemma MGFn_Loop: 
"\<lbrakk>G,(A::state triple set)\<turnstile>{=:n} In1l expr\<succ> {G\<rightarrow>};G,A\<turnstile>{=:n} In1r stmnt\<succ> {G\<rightarrow>} \<rbrakk> 
\<Longrightarrow> 
  G,A\<turnstile>{=:n} In1r (l\<bullet> While(expr) stmnt)\<succ> {G\<rightarrow>}"
apply (rule MGFn_NormalI, simp)
apply (rule_tac p2 = "\<lambda>s. card (nyinitcls G s) \<le> n" in 
          MGF_altern [unfolded MGF_def, THEN iffD2, THEN conseq1])
prefer 2
apply  clarsimp
apply (rule_tac P' = 
"((\<lambda>Y s Z. \<forall>w s'. G\<turnstile>s \<midarrow>In1r (l\<bullet>  While(expr) stmnt) \<succ>\<rightarrow> (w,s') \<longrightarrow> (w,s') = Z) 
  \<and>. (\<lambda>s. card (nyinitcls G s) \<le> n))" in conseq12)
prefer 2
apply  clarsimp
apply  (tactic "smp_tac 1 1", erule_tac V = "All ?P" in thin_rl)
apply  (rule_tac [2] P' = " (\<lambda>b s (Y',s') . (\<exists>s0. G\<turnstile>s0 \<midarrow>In1l expr\<succ>\<rightarrow> (b,s)) \<and> (if normal s \<and> the_Bool (the_In1 b) then (\<forall>s'' w s0. G\<turnstile>s \<midarrow>stmnt\<rightarrow> s'' \<and> G\<turnstile>(abupd (absorb (Cont l)) s'') \<midarrow>In1r (l\<bullet> While(expr) stmnt) \<succ>\<rightarrow> (w,s0) \<longrightarrow> (w,s0) = (Y',s')) else (\<diamondsuit>,s) = (Y',s'))) \<and>. G\<turnstile>init\<le>n" in polymorphic_Loop)
apply   (force dest!: eval.Loop split add: split_if_asm)
prefer 2
apply  (erule MGFnD' [THEN conseq12])
apply  clarsimp
apply  (erule_tac V = "card (nyinitcls G s') \<le> n" in thin_rl)
apply  (tactic "eval_Force_tac 1")
apply (erule MGFnD' [THEN conseq12] , clarsimp)
apply (rule conjI, erule exI)
apply (tactic "clarsimp_tac eval_css 1")
apply (case_tac "a")
prefer 2
apply  (clarsimp)
apply (clarsimp split add: split_if)
apply (rule conjI, (tactic {* force_tac (claset() addSDs [thm "eval.Loop"],
  simpset() addsimps [split_paired_all] addsimprocs [eval_stmt_proc]) 1*})+)
done

lemma MGFn_lemma [rule_format (no_asm)]: 
 "\<forall>n C sig. G,(A::state triple set)\<turnstile>{=:n} In1l (Methd C sig)\<succ> {G\<rightarrow>} \<Longrightarrow>  
  \<forall>t. G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>}"
apply (rule full_nat_induct)
apply (rule allI)
apply (drule_tac x = n in spec)
apply (drule_tac psi = "All ?P" in asm_rl)
apply (subgoal_tac "\<forall>v e c es. G,A\<turnstile>{=:n} In2 v\<succ> {G\<rightarrow>} \<and> G,A\<turnstile>{=:n} In1l e\<succ> {G\<rightarrow>} \<and> G,A\<turnstile>{=:n} In1r c\<succ> {G\<rightarrow>} \<and> G,A\<turnstile>{=:n} In3 es\<succ> {G\<rightarrow>}")
apply  (tactic "Clarify_tac 2")
apply  (induct_tac "t")
apply    (induct_tac "a")
apply     fast+
apply (rule var_expr_stmt.induct)
(* 28 subgoals *)
prefer 14 apply fast (* Methd *)
prefer 13 apply (erule (2) MGFn_Call)
apply (erule_tac [!] V = "All ?P" in thin_rl) (* assumptions on Methd *)
apply (erule_tac [24] MGFn_Init)
prefer 19 apply (erule (1) MGFn_Loop)
apply (tactic "ALLGOALS compl_prepare_tac")

apply (rule ax_derivs.LVar [THEN conseq1], tactic "eval_Force_tac 1")

apply (rule ax_derivs.FVar)
apply  (erule MGFn_InitD)
apply (tactic "forw_hyp_eval_Force_tac 1")

apply (rule ax_derivs.AVar)
apply  (erule MGFnD [THEN ax_NormalD])
apply (tactic "forw_hyp_eval_Force_tac 1")

apply (rule ax_derivs.NewC)
apply (erule MGFn_InitD [THEN conseq2])
apply (tactic "eval_Force_tac 1")

apply (rule_tac Q = "(\<lambda>Y' s' s. normal s \<and> G\<turnstile>s \<midarrow>In1r (init_comp_ty ty) \<succ>\<rightarrow> (Y',s')) \<and>. G\<turnstile>init\<le>n" in ax_derivs.NewA)
apply  (simp add: init_comp_ty_def split add: split_if)
apply   (rule conjI, clarsimp)
apply   (erule MGFn_InitD [THEN conseq2])
apply   (tactic "clarsimp_tac eval_css 1")
apply  clarsimp
apply  (rule ax_derivs.Skip [THEN conseq1], tactic "eval_Force_tac 1")
apply (tactic "forw_hyp_eval_Force_tac 1")

apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Cast],tactic"eval_Force_tac 1")

apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Inst],tactic"eval_Force_tac 1")
apply (rule ax_derivs.Lit [THEN conseq1], tactic "eval_Force_tac 1")
apply (rule ax_derivs.Super [THEN conseq1], tactic "eval_Force_tac 1")
apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Acc],tactic"eval_Force_tac 1")

apply (rule ax_derivs.Ass)
apply  (erule MGFnD [THEN ax_NormalD])
apply (tactic "forw_hyp_eval_Force_tac 1")

apply (rule ax_derivs.Cond)
apply  (erule MGFnD [THEN ax_NormalD])
apply (rule allI)
apply (rule ax_Normal_cases)
prefer 2
apply  (rule ax_derivs.Abrupt [THEN conseq1], clarsimp simp add: Let_def)
apply  (tactic "eval_Force_tac 1")
apply (case_tac "b")
apply  (simp, tactic "forw_hyp_eval_Force_tac 1")
apply (simp, tactic "forw_hyp_eval_Force_tac 1")

apply (rule_tac Q = " (\<lambda>Y' s' s. normal s \<and> G\<turnstile>s \<midarrow>Init pid_field_type\<rightarrow> s') \<and>. G\<turnstile>init\<le>n" in ax_derivs.Body)
 apply (erule MGFn_InitD [THEN conseq2])
 apply (tactic "eval_Force_tac 1")
apply (tactic "forw_hyp_tac 1")
apply (tactic {* clarsimp_tac (eval_css delsimps2 [split_paired_all]) 1 *})
apply (erule (1) eval.Body)

apply (rule ax_derivs.Skip [THEN conseq1], tactic "eval_Force_tac 1")

apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Expr],tactic"eval_Force_tac 1")

apply (erule MGFnD' [THEN conseq12, THEN ax_derivs.Lab])
apply (tactic "clarsimp_tac eval_css 1")

apply (rule ax_derivs.Comp)
apply  (erule MGFnD [THEN ax_NormalD])
apply (tactic "forw_hyp_eval_Force_tac 1")

apply (rule ax_derivs.If)
apply  (erule MGFnD [THEN ax_NormalD])
apply (rule allI)
apply (rule ax_Normal_cases)
prefer 2
apply  (rule ax_derivs.Abrupt [THEN conseq1], clarsimp simp add: Let_def)
apply  (tactic "eval_Force_tac 1")
apply (case_tac "b")
apply  (simp, tactic "forw_hyp_eval_Force_tac 1")
apply (simp, tactic "forw_hyp_eval_Force_tac 1")

apply (rule ax_derivs.Do [THEN conseq1])
apply (tactic {* force_tac (eval_css addsimps2 [thm "abupd_def2"]) 1 *})

apply (erule MGFnD' [THEN conseq12, THEN ax_derivs.Throw])
apply (tactic "clarsimp_tac eval_css 1")

apply (rule_tac Q = " (\<lambda>Y' s' s. normal s \<and> (\<exists>s''. G\<turnstile>s \<midarrow>In1r stmt1\<succ>\<rightarrow> (Y',s'') \<and> G\<turnstile>s'' \<midarrow>sxalloc\<rightarrow> s')) \<and>. G\<turnstile>init\<le>n" in ax_derivs.Try)
apply   (tactic "eval_Force_tac 3")
apply  (tactic "forw_hyp_eval_Force_tac 2")
apply (erule MGFnD [THEN ax_NormalD, THEN conseq2])
apply (tactic "clarsimp_tac eval_css 1")
apply (force elim: sxalloc_gext [THEN card_nyinitcls_gext])

apply (rule_tac Q = " (\<lambda>Y' s' s. normal s \<and> G\<turnstile>s \<midarrow>stmt1\<rightarrow> s') \<and>. G\<turnstile>init\<le>n" in ax_derivs.Fin)
apply  (tactic "forw_hyp_eval_Force_tac 1")
apply (rule allI)
apply (tactic "forw_hyp_tac 1")
apply (tactic {* pair_tac "sb" 1 *})
apply (tactic"clarsimp_tac (claset(),simpset() addsimprocs [eval_stmt_proc]) 1")
apply (drule (1) eval.Fin)
apply clarsimp

apply (rule ax_derivs.Nil [THEN conseq1], tactic "eval_Force_tac 1")

apply (rule ax_derivs.Cons)
apply  (erule MGFnD [THEN ax_NormalD])
apply (tactic "forw_hyp_eval_Force_tac 1")
done

lemma MGF_asm: "\<forall>C sig. is_methd G C sig \<longrightarrow> G,A\<turnstile>{\<doteq>} In1l (Methd C sig)\<succ> {G\<rightarrow>} \<Longrightarrow>
  G,(A::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (simp (no_asm_use) add: MGF_MGFn_iff)
apply (rule allI)
apply (rule MGFn_lemma)
apply (intro strip)
apply (rule MGFn_free_wt)
apply (force dest: wt_Methd_is_methd)
done

declare splitI2 [intro!]
ML_setup {*
Addsimprocs [ eval_expr_proc, eval_var_proc, eval_exprs_proc, eval_stmt_proc]
*}


section "nested version"

lemma nesting_lemma' [rule_format (no_asm)]: "[| !!A ts. ts <= A ==> P A ts; 
  !!A pn. !b:bdy pn. P (insert (mgf_call pn) A) {mgf b} ==> P A {mgf_call pn}; 
  !!A t. !pn:U. P A {mgf_call pn} ==> P A {mgf t};  
          finite U; uA = mgf_call`U |] ==>  
  !A. A <= uA --> n <= card uA --> card A = card uA - n --> (!t. P A {mgf t})"
proof -
  assume ax_derivs_asm:    "!!A ts. ts <= A ==> P A ts"
  assume MGF_nested_Methd: "!!A pn. !b:bdy pn. P (insert (mgf_call pn) A) 
                                                  {mgf b} ==> P A {mgf_call pn}"
  assume MGF_asm:          "!!A t. !pn:U. P A {mgf_call pn} ==> P A {mgf t}"
  assume "finite U" "uA = mgf_call`U"
  then show ?thesis
    apply -
    apply (induct_tac "n")
    apply  (tactic "ALLGOALS Clarsimp_tac")
    apply  (tactic "dtac (permute_prems 0 1 card_seteq) 1")
    apply    simp
    apply   (erule finite_imageI)
    apply  (simp add: MGF_asm ax_derivs_asm)
    apply (rule MGF_asm)
    apply (rule ballI)
    apply (case_tac "mgf_call pn : A")
    apply  (fast intro: ax_derivs_asm)
    apply (rule MGF_nested_Methd)
    apply (rule ballI)
    apply (drule spec, erule impE, erule_tac [2] impE, erule_tac [3] impE, 
           erule_tac [4] spec)
    apply   fast
    apply  (erule Suc_leD)
    apply (drule finite_subset)
    apply (erule finite_imageI)
    apply auto
    apply arith
  done
qed

lemma nesting_lemma [rule_format (no_asm)]: "[| !!A ts. ts <= A ==> P A ts; 
  !!A pn. !b:bdy pn. P (insert (mgf (f pn)) A) {mgf b} ==> P A {mgf (f pn)}; 
          !!A t. !pn:U. P A {mgf (f pn)} ==> P A {mgf t}; 
          finite U |] ==> P {} {mgf t}"
proof -
  assume 2: "!!A pn. !b:bdy pn. P (insert (mgf (f pn)) A) {mgf b} ==> P A {mgf (f pn)}"
  assume 3: "!!A t. !pn:U. P A {mgf (f pn)} ==> P A {mgf t}"
  assume "!!A ts. ts <= A ==> P A ts" "finite U"
  then show ?thesis
    apply -
    apply (rule_tac mgf = "mgf" in nesting_lemma')
    apply (erule_tac [2] 2)
    apply (rule_tac [2] 3)
    apply (rule_tac [6] le_refl)
    apply auto
  done
qed

lemma MGF_nested_Methd: "\<lbrakk>  
  G,insert ({Normal \<doteq>} In1l (Methd  C sig) \<succ>{G\<rightarrow>}) A\<turnstile>  
            {Normal \<doteq>} In1l (body G C sig) \<succ>{G\<rightarrow>}  
 \<rbrakk> \<Longrightarrow>  G,A\<turnstile>{Normal \<doteq>} In1l (Methd  C sig) \<succ>{G\<rightarrow>}"
apply (unfold MGF_def)
apply (rule ax_MethdN)
apply (erule conseq2)
apply clarsimp
apply (erule MethdI)
done

lemma MGF_deriv: "ws_prog G \<Longrightarrow> G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (rule MGFNormalI)
apply (rule_tac mgf = "\<lambda>t. {Normal \<doteq>} t\<succ> {G\<rightarrow>}" and 
                bdy = "\<lambda> (C,sig) .{In1l (body G C sig) }" and 
                f = "\<lambda> (C,sig) . In1l (Methd C sig) " in nesting_lemma)
apply    (erule ax_derivs.asm)
apply   (clarsimp simp add: split_tupled_all)
apply   (erule MGF_nested_Methd)
apply  (erule_tac [2] finite_is_methd)
apply (rule MGF_asm [THEN MGFNormalD])
apply clarify
apply (rule MGFNormalI)
apply force
done


section "simultaneous version"

lemma MGF_simult_Methd_lemma: "finite ms \<Longrightarrow>  
  G,A\<union> (\<lambda>(C,sig). {Normal \<doteq>} In1l (Methd  C sig)\<succ> {G\<rightarrow>}) ` ms  
     |\<turnstile>(\<lambda>(C,sig). {Normal \<doteq>} In1l (body G C sig)\<succ> {G\<rightarrow>}) ` ms \<Longrightarrow>  
  G,A|\<turnstile>(\<lambda>(C,sig). {Normal \<doteq>} In1l (Methd  C sig)\<succ> {G\<rightarrow>}) ` ms"
apply (unfold MGF_def)
apply (rule ax_derivs.Methd [unfolded mtriples_def])
apply (erule ax_finite_pointwise)
prefer 2
apply  (rule ax_derivs.asm)
apply  fast
apply clarsimp
apply (rule conseq2)
apply  (erule (1) ax_methods_spec)
apply clarsimp
apply (erule eval_Methd)
done

lemma MGF_simult_Methd: "ws_prog G \<Longrightarrow> 
   G,({}::state triple set)|\<turnstile>(\<lambda>(C,sig). {Normal \<doteq>} In1l (Methd C sig)\<succ> {G\<rightarrow>}) 
   ` Collect (split (is_methd G)) "
apply (frule finite_is_methd)
apply (rule MGF_simult_Methd_lemma)
apply  assumption
apply (erule ax_finite_pointwise)
prefer 2
apply  (rule ax_derivs.asm)
apply  blast
apply clarsimp
apply (rule MGF_asm [THEN MGFNormalD])
apply clarify
apply (rule MGFNormalI)
apply force
done

lemma MGF_deriv: "ws_prog G \<Longrightarrow> G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (rule MGF_asm)
apply (intro strip)
apply (rule MGFNormalI)
apply (rule ax_derivs.weaken)
apply  (erule MGF_simult_Methd)
apply force
done


section "corollaries"

lemma MGF_complete: "G,{}\<Turnstile>{P} t\<succ> {Q} \<Longrightarrow> G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>} \<Longrightarrow>
  G,({}::state triple set)\<turnstile>{P::state assn} t\<succ> {Q}"
apply (rule ax_no_hazard)
apply (unfold MGF_def)
apply (erule conseq12)
apply (simp (no_asm_use) add: ax_valids_def triple_valid_def)
apply (fast dest!: eval_evaln)
done

theorem ax_complete: "ws_prog G \<Longrightarrow>  
  G,{}\<Turnstile>{P::state assn} t\<succ> {Q} \<Longrightarrow> G,({}::state triple set)\<turnstile>{P} t\<succ> {Q}"
apply (erule MGF_complete)
apply (erule MGF_deriv)
done

end
