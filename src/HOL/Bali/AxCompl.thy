(*  Title:      HOL/Bali/AxCompl.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
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

lemma card_Suc_lemma: 
  "\<lbrakk>card (insert a A) \<le> Suc n; a\<notin>A; finite A\<rbrakk> \<Longrightarrow> card A \<le> n"
apply clarsimp
done

lemma nyinitcls_le_SucD: 
"\<lbrakk>card (nyinitcls G (x,s)) \<le> Suc n; \<not>inited C (globs s); class G C=Some y\<rbrakk> \<Longrightarrow> 
  card (nyinitcls G (x,init_class_obj G C s)) \<le> n"
apply (subgoal_tac 
        "nyinitcls G (x,s) = insert C (nyinitcls G (x,init_class_obj G C s))")
apply  clarsimp
apply  (erule_tac V="nyinitcls G (x, s) = ?rhs" in thin_rl)
apply  (rule card_Suc_lemma [OF _ _ finite_nyinitcls])
apply   (auto dest!: not_initedD elim!: 
              simp add: nyinitcls_def inited_def split add: split_if_asm)
done

lemma inited_gext': "\<lbrakk>s\<le>|s';inited C (globs s)\<rbrakk> \<Longrightarrow> inited C (globs s')"
by (rule inited_gext)

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

lemma All_init_leD: 
 "\<forall>n::nat. G,(A::'a triple set)\<turnstile>{P \<and>. G\<turnstile>init\<le>n} t\<succ> {Q::'a assn} 
  \<Longrightarrow> G,A\<turnstile>{P} t\<succ> {Q}"
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
lemma MGF_valid: "wf_prog G \<Longrightarrow> G,{}\<Turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (unfold MGF_def)
apply (simp add:  ax_valids_def triple_valid_def2)
apply (auto elim: evaln_eval)
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

lemma MGF_MGFn_iff: 
"G,(A::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>} = (\<forall>n. G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>})"
apply (simp (no_asm_use) add: MGFn_def2 MGF_def)
apply safe
apply  (erule_tac [2] All_init_leD)
apply (erule conseq1)
apply clarsimp
done

lemma MGFnD: 
"G,(A::state triple set)\<turnstile>{=:n} t\<succ> {G\<rightarrow>} \<Longrightarrow>  
 G,A\<turnstile>{(\<lambda>Y' s' s. s' = s           \<and> P s) \<and>. G\<turnstile>init\<le>n}  
 t\<succ>  {(\<lambda>Y' s' s. G\<turnstile>s\<midarrow>t\<succ>\<rightarrow>(Y',s') \<and> P s) \<and>. G\<turnstile>init\<le>n}"
apply (unfold init_le_def)
apply (simp (no_asm_use) add: MGFn_def2)
apply (erule conseq12)
apply clarsimp
apply (erule (1) eval_gext [THEN card_nyinitcls_gext])
done
lemmas MGFnD' = MGFnD [of _ _ _ _ "\<lambda>x. True"] 

text {* To derive the most general formula, we can always assume a normal
state in the precondition, since abrupt cases can be handled uniformally by
the abrupt rule.
*}
lemma MGFNormalI: "G,A\<turnstile>{Normal \<doteq>} t\<succ> {G\<rightarrow>} \<Longrightarrow>  
  G,(A::state triple set)\<turnstile>{\<doteq>::state assn} t\<succ> {G\<rightarrow>}"
apply (unfold MGF_def)
apply (rule ax_Normal_cases)
apply  (erule conseq1)
apply  clarsimp
apply (rule ax_derivs.Abrupt [THEN conseq1])
apply (clarsimp simp add: Let_def)
done

lemma MGFNormalD: 
"G,(A::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>} \<Longrightarrow> G,A\<turnstile>{Normal \<doteq>} t\<succ> {G\<rightarrow>}"
apply (unfold MGF_def)
apply (erule conseq1)
apply clarsimp
done

text {* Additionally to @{text MGFNormalI}, we also expand the definition of 
the most general formula here *} 
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

text {* To derive the most general formula, we can restrict ourselves to 
welltyped terms, since all others can be uniformally handled by the hazard
rule. *} 
lemma MGFn_free_wt: 
  "(\<exists>T L C. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) 
    \<longrightarrow> G,(A::state triple set)\<turnstile>{=:n} t\<succ> {G\<rightarrow>} 
   \<Longrightarrow> G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>}"
apply (rule MGFn_NormalI)
apply (rule ax_free_wt)
apply (auto elim: conseq12 simp add: MGFn_def MGF_def)
done

text {* To derive the most general formula, we can restrict ourselves to 
welltyped terms and assume that the state in the precondition conforms to the
environment. All type violations can be uniformally handled by the hazard
rule. *} 
lemma MGFn_free_wt_NormalConformI: 
"(\<forall> T L C . \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T 
  \<longrightarrow> G,(A::state triple set)
      \<turnstile>{Normal((\<lambda>Y' s' s. s'=s \<and> normal s) \<and>. G\<turnstile>init\<le>n) \<and>. (\<lambda> s. s\<Colon>\<preceq>(G, L))}
      t\<succ> 
      {\<lambda>Y s' s. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y,s')}) 
 \<Longrightarrow> G,A\<turnstile>{=:n}t\<succ>{G\<rightarrow>}"
apply (rule MGFn_NormalI)
apply (rule ax_no_hazard)
apply (rule ax_escape)
apply (intro strip)
apply (simp only: type_ok_def peek_and_def)
apply (erule conjE)+
apply (erule exE,erule exE, erule exE, erule exE,erule conjE,drule (1) mp,
       erule conjE)
apply (drule spec,drule spec, drule spec, drule (1) mp)
apply (erule conseq12)
apply blast
done

text {* To derive the most general formula, we can restrict ourselves to 
welltyped terms and assume that the state in the precondition conforms to the
environment and that the term is definetly assigned with respect to this state.
All type violations can be uniformally handled by the hazard rule. *} 
lemma MGFn_free_wt_da_NormalConformI: 
"(\<forall> T L C B. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T
  \<longrightarrow> G,(A::state triple set)
      \<turnstile>{Normal((\<lambda>Y' s' s. s'=s \<and> normal s) \<and>. G\<turnstile>init\<le>n) \<and>. (\<lambda> s. s\<Colon>\<preceq>(G, L))
        \<and>. (\<lambda> s. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>B)}
      t\<succ> 
      {\<lambda>Y s' s. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y,s')}) 
 \<Longrightarrow> G,A\<turnstile>{=:n}t\<succ>{G\<rightarrow>}"
apply (rule MGFn_NormalI)
apply (rule ax_no_hazard)
apply (rule ax_escape)
apply (intro strip)
apply (simp only: type_ok_def peek_and_def)
apply (erule conjE)+
apply (erule exE,erule exE, erule exE, erule exE,erule conjE,drule (1) mp,
       erule conjE)
apply (drule spec,drule spec, drule spec,drule spec, drule (1) mp)
apply (erule conseq12)
apply blast
done

section "main lemmas"

lemma MGFn_Init: 
 assumes mgf_hyp: "\<forall>m. Suc m\<le>n \<longrightarrow> (\<forall>t. G,A\<turnstile>{=:m} t\<succ> {G\<rightarrow>})"
 shows "G,(A::state triple set)\<turnstile>{=:n} \<langle>Init C\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
proof (rule MGFn_free_wt [rule_format],elim exE,rule MGFn_NormalI)
  fix T L accC
  assume "\<lparr>prg=G, cls=accC, lcl= L\<rparr>\<turnstile>\<langle>Init C\<rangle>\<^sub>s\<Colon>T"
  hence is_cls: "is_class G C"
    by cases simp
  show "G,A\<turnstile>{Normal ((\<lambda>Y' s' s. s' = s \<and> normal s) \<and>. G\<turnstile>init\<le>n)} 
            .Init C.
            {\<lambda>Y s' s. G\<turnstile>s \<midarrow>\<langle>Init C\<rangle>\<^sub>s\<succ>\<rightarrow> (Y, s')}"
       (is "G,A\<turnstile>{Normal ?P} .Init C. {?R}")
  proof (rule ax_cases [where ?C="initd C"])
    show "G,A\<turnstile>{Normal ?P  \<and>. initd C} .Init C. {?R}"
      by (rule ax_derivs.Done [THEN conseq1]) (fastsimp intro: init_done)
  next
    have "G,A\<turnstile>{Normal (?P  \<and>. Not \<circ> initd C)} .Init C. {?R}" 
    proof (cases n)
      case 0
      with is_cls
      show ?thesis
	by - (rule ax_impossible [THEN conseq1],fastsimp dest: nyinitcls_emptyD)
    next
      case (Suc m)
      with mgf_hyp have mgf_hyp': "\<And> t. G,A\<turnstile>{=:m} t\<succ> {G\<rightarrow>}"
	by simp
      from is_cls obtain c where c: "the (class G C) = c"
	by auto
      let ?Q= "(\<lambda>Y s' (x,s) . 
          G\<turnstile> (x,init_class_obj G C s) 
             \<midarrow> (if C=Object then Skip else Init (super (the (class G C))))\<rightarrow> s'
          \<and> x=None \<and> \<not>inited C (globs s)) \<and>. G\<turnstile>init\<le>m"
      from c
      show ?thesis
      proof (rule ax_derivs.Init [where ?Q="?Q"])
	let ?P' = "Normal ((\<lambda>Y s' s. s' = supd (init_class_obj G C) s 
                           \<and> normal s \<and> \<not> initd C s) \<and>. G\<turnstile>init\<le>m)" 
	show "G,A\<turnstile>{Normal (?P \<and>. Not \<circ> initd C ;. supd (init_class_obj G C))}
                  .(if C = Object then Skip else Init (super c)). 
                  {?Q}"
	proof (rule conseq1 [where ?P'="?P'"])
	  show "G,A\<turnstile>{?P'} .(if C = Object then Skip else Init (super c)). {?Q}"
	  proof (cases "C=Object")
	    case True
	    have "G,A\<turnstile>{?P'} .Skip. {?Q}"
	      by (rule ax_derivs.Skip [THEN conseq1])
	         (auto simp add: True intro: eval.Skip)
            with True show ?thesis 
	      by simp
	  next
	    case False
	    from mgf_hyp'
	    have "G,A\<turnstile>{?P'} .Init (super c). {?Q}"
	      by (rule MGFnD' [THEN conseq12]) (fastsimp simp add: False c)
	    with False show ?thesis
	      by simp
	  qed
	next
	  from Suc is_cls
	  show "Normal (?P \<and>. Not \<circ> initd C ;. supd (init_class_obj G C))
                \<Rightarrow> ?P'"
	    by (fastsimp elim: nyinitcls_le_SucD)
	qed
      next
	from mgf_hyp'
	show "\<forall>l. G,A\<turnstile>{?Q \<and>. (\<lambda>s. l = locals (snd s)) ;. set_lvars empty} 
                      .init c.
                      {set_lvars l .; ?R}"
	  apply (rule MGFnD' [THEN conseq12, THEN allI])
	  apply (clarsimp simp add: split_paired_all)
	  apply (rule eval.Init [OF c])
	  apply (insert c)
	  apply auto
	  done
      qed
    qed
    thus "G,A\<turnstile>{Normal ?P  \<and>. Not \<circ> initd C} .Init C. {?R}"
      by clarsimp
  qed
qed
lemmas MGFn_InitD = MGFn_Init [THEN MGFnD, THEN ax_NormalD]

lemma MGFn_Call: 
  assumes mgf_methds: 
           "\<forall>C sig. G,(A::state triple set)\<turnstile>{=:n} \<langle>(Methd C sig)\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
  and mgf_e: "G,A\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
  and mgf_ps: "G,A\<turnstile>{=:n} \<langle>ps\<rangle>\<^sub>l\<succ> {G\<rightarrow>}"
  and wf: "wf_prog G"
  shows "G,A\<turnstile>{=:n} \<langle>{accC,statT,mode}e\<cdot>mn({pTs'}ps)\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
proof (rule MGFn_free_wt_da_NormalConformI [rule_format],clarsimp) 
  note inj_term_simps [simp]
  fix T L accC' E
  assume wt: "\<lparr>prg=G,cls=accC',lcl = L\<rparr>\<turnstile>\<langle>({accC,statT,mode}e\<cdot>mn( {pTs'}ps))\<rangle>\<^sub>e\<Colon>T"
  then obtain pTs statDeclT statM where
                 wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT" and
              wt_args: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>ps\<Colon>\<doteq>pTs" and
                statM: "max_spec G accC statT \<lparr>name=mn,parTs=pTs\<rparr> 
                         = {((statDeclT,statM),pTs')}" and
                 mode: "mode = invmode statM e" and
                    T: "T =Inl (resTy statM)" and
        eq_accC_accC': "accC=accC'"
	by cases fastsimp+
  let ?Q="(\<lambda>Y s1 (x,s) . x = None \<and> 
              (\<exists>a. G\<turnstile>Norm s \<midarrow>e-\<succ>a\<rightarrow> s1 \<and> 
                   (normal s1 \<longrightarrow> G, store s1\<turnstile>a\<Colon>\<preceq>RefT statT)
                   \<and> Y = In1 a) \<and> 
              (\<exists> P. normal s1
                  \<longrightarrow> \<lparr>prg=G,cls=accC',lcl=L\<rparr>\<turnstile>dom (locals (store s1))\<guillemotright>\<langle>ps\<rangle>\<^sub>l\<guillemotright>P)) 
          \<and>. G\<turnstile>init\<le>n \<and>. (\<lambda> s. s\<Colon>\<preceq>(G, L))::state assn"
  let ?R="\<lambda>a. ((\<lambda>Y (x2,s2) (x,s) . x = None \<and> 
                (\<exists>s1 pvs. G\<turnstile>Norm s \<midarrow>e-\<succ>a\<rightarrow> s1 \<and> 
                          (normal s1 \<longrightarrow> G, store s1\<turnstile>a\<Colon>\<preceq>RefT statT)\<and> 
                          Y = \<lfloor>pvs\<rfloor>\<^sub>l \<and> G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>pvs\<rightarrow> (x2,s2))) 
               \<and>. G\<turnstile>init\<le>n \<and>. (\<lambda> s. s\<Colon>\<preceq>(G, L)))::state assn"

  show "G,A\<turnstile>{Normal ((\<lambda>Y' s' s. s' = s \<and> abrupt s = None) \<and>. G\<turnstile>init\<le>n \<and>.
                     (\<lambda>s. s\<Colon>\<preceq>(G, L)) \<and>.
                     (\<lambda>s. \<lparr>prg=G, cls=accC',lcl=L\<rparr> \<turnstile> dom (locals (store s)) 
                           \<guillemotright> \<langle>{accC,statT,mode}e\<cdot>mn( {pTs'}ps)\<rangle>\<^sub>e\<guillemotright> E))}
             {accC,statT,mode}e\<cdot>mn( {pTs'}ps)-\<succ>
             {\<lambda>Y s' s. \<exists>v. Y = \<lfloor>v\<rfloor>\<^sub>e \<and> 
                           G\<turnstile>s \<midarrow>{accC,statT,mode}e\<cdot>mn( {pTs'}ps)-\<succ>v\<rightarrow> s'}"
    (is "G,A\<turnstile>{Normal ?P} {accC,statT,mode}e\<cdot>mn( {pTs'}ps)-\<succ> {?S}")
  proof (rule ax_derivs.Call [where ?Q="?Q" and ?R="?R"])
    from mgf_e
    show "G,A\<turnstile>{Normal ?P} e-\<succ> {?Q}"
    proof (rule MGFnD' [THEN conseq12],clarsimp)
      fix s0 s1 a
      assume conf_s0: "Norm s0\<Colon>\<preceq>(G, L)"
      assume da: "\<lparr>prg=G,cls=accC',lcl=L\<rparr>\<turnstile> 
                     dom (locals s0) \<guillemotright>\<langle>{accC,statT,mode}e\<cdot>mn( {pTs'}ps)\<rangle>\<^sub>e\<guillemotright> E"
      assume eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1"
      show "(abrupt s1 = None \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>RefT statT) \<and>
            (abrupt s1 = None \<longrightarrow>
              (\<exists>P. \<lparr>prg=G,cls=accC',lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>ps\<rangle>\<^sub>l\<guillemotright> P))
            \<and> s1\<Colon>\<preceq>(G, L)"
      proof -
	from da obtain C where
	  da_e:  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>
                    dom (locals (store ((Norm s0)::state)))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> C" and
	  da_ps: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm C \<guillemotright>\<langle>ps\<rangle>\<^sub>l\<guillemotright> E" 
	  by cases (simp add: eq_accC_accC')
	from eval_e conf_s0 wt_e da_e wf
	obtain "(abrupt s1 = None \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>RefT statT)"
	  and  "s1\<Colon>\<preceq>(G, L)"
	  by (rule eval_type_soundE) simp
	moreover
	{
	  assume normal_s1: "normal s1"
	  have "\<exists>P. \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>ps\<rangle>\<^sub>l\<guillemotright> P"
	  proof -
	    from eval_e wt_e da_e wf normal_s1
	    have "nrm C \<subseteq>  dom (locals (store s1))"
	      by (cases rule: da_good_approxE') rules
	    with da_ps show ?thesis
	      by (rule da_weakenE) rules
	  qed
	}
	ultimately show ?thesis
	  using eq_accC_accC' by simp
      qed
    qed
  next
    show "\<forall>a. G,A\<turnstile>{?Q\<leftarrow>In1 a} ps\<doteq>\<succ> {?R a}" (is "\<forall> a. ?PS a")
    proof 
      fix a  
      show "?PS a"
      proof (rule MGFnD' [OF mgf_ps, THEN conseq12],
             clarsimp simp add: eq_accC_accC' [symmetric])
	fix s0 s1 s2 vs
	assume conf_s1: "s1\<Colon>\<preceq>(G, L)"
	assume eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1"
	assume conf_a: "abrupt s1 = None \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>RefT statT"
	assume eval_ps: "G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>vs\<rightarrow> s2"
	assume da_ps: "abrupt s1 = None \<longrightarrow> 
                       (\<exists>P. \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
                               dom (locals (store s1)) \<guillemotright>\<langle>ps\<rangle>\<^sub>l\<guillemotright> P)"
	show "(\<exists>s1. G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1 \<and>
                (abrupt s1 = None \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>RefT statT) \<and>
                G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>vs\<rightarrow> s2) \<and>
              s2\<Colon>\<preceq>(G, L)"
	proof (cases "normal s1")
	  case True
	  with da_ps obtain P where
	   "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>ps\<rangle>\<^sub>l\<guillemotright> P"
	    by auto
	  from eval_ps conf_s1 wt_args this wf
	  have "s2\<Colon>\<preceq>(G, L)"
	    by (rule eval_type_soundE)
	  with eval_e conf_a eval_ps 
	  show ?thesis 
	    by auto
	next
	  case False
	  with eval_ps have "s2=s1" by auto
	  with eval_e conf_a eval_ps conf_s1 
	  show ?thesis 
	    by auto
	qed
      qed
    qed
  next
    show "\<forall>a vs invC declC l.
      G,A\<turnstile>{?R a\<leftarrow>\<lfloor>vs\<rfloor>\<^sub>l \<and>.
             (\<lambda>s. declC =
                  invocation_declclass G mode (store s) a statT
                      \<lparr>name=mn, parTs=pTs'\<rparr> \<and>
                  invC = invocation_class mode (store s) a statT \<and>
                  l = locals (store s)) ;.
             init_lvars G declC \<lparr>name=mn, parTs=pTs'\<rparr> mode a vs \<and>.
             (\<lambda>s. normal s \<longrightarrow> G\<turnstile>mode\<rightarrow>invC\<preceq>statT)}
          Methd declC \<lparr>name=mn,parTs=pTs'\<rparr>-\<succ> 
          {set_lvars l .; ?S}" 
      (is "\<forall> a vs invC declC l. ?METHD a vs invC declC l")
    proof (intro allI)
      fix a vs invC declC l
      from mgf_methds [rule_format]
      show "?METHD a vs invC declC l"
      proof (rule MGFnD' [THEN conseq12],clarsimp)
	fix s4 s2 s1::state
	fix s0 v
	let ?D= "invocation_declclass G mode (store s2) a statT 
                    \<lparr>name=mn,parTs=pTs'\<rparr>"
	let ?s3= "init_lvars G ?D \<lparr>name=mn, parTs=pTs'\<rparr> mode a vs s2"
	assume inv_prop: "abrupt ?s3=None 
             \<longrightarrow> G\<turnstile>mode\<rightarrow>invocation_class mode (store s2) a statT\<preceq>statT"
	assume conf_s2: "s2\<Colon>\<preceq>(G, L)"
	assume conf_a: "abrupt s1 = None \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>RefT statT"
	assume eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1"
	assume eval_ps: "G\<turnstile>s1 \<midarrow>ps\<doteq>\<succ>vs\<rightarrow> s2"
	assume eval_mthd: "G\<turnstile>?s3 \<midarrow>Methd ?D \<lparr>name=mn,parTs=pTs'\<rparr>-\<succ>v\<rightarrow> s4"
	show "G\<turnstile>Norm s0 \<midarrow>{accC,statT,mode}e\<cdot>mn( {pTs'}ps)-\<succ>v
                        \<rightarrow> (set_lvars (locals (store s2))) s4"
	proof -
	  obtain D where D: "D=?D" by simp
	  obtain s3 where s3: "s3=?s3" by simp
	  obtain s3' where 
	    s3': "s3' = check_method_access G accC statT mode 
                           \<lparr>name=mn,parTs=pTs'\<rparr> a s3"
	    by simp
	  have eq_s3'_s3: "s3'=s3"
	  proof -
	    from inv_prop s3 mode
	    have "normal s3 \<Longrightarrow> 
             G\<turnstile>invmode statM e\<rightarrow>invocation_class mode (store s2) a statT\<preceq>statT"
	      by auto
	    with eval_ps wt_e statM conf_s2 conf_a [rule_format] 
	    have "check_method_access G accC statT (invmode statM e)
                      \<lparr>name=mn,parTs=pTs'\<rparr> a s3 = s3"
	      by (rule error_free_call_access) (auto simp add: s3 mode wf)
	    thus ?thesis 
	      by (simp add: s3' mode)
	  qed
	  with eval_mthd D s3
	  have "G\<turnstile>s3' \<midarrow>Methd D \<lparr>name=mn,parTs=pTs'\<rparr>-\<succ>v\<rightarrow> s4"
	    by simp
	  with eval_e eval_ps D _ s3' 
	  show ?thesis
	    by (rule eval_Call) (auto simp add: s3 mode D)
	qed
      qed
    qed
  qed
qed
	  	  
lemma eval_expression_no_jump':
  assumes eval: "G\<turnstile>s0 \<midarrow>e-\<succ>v\<rightarrow> s1"
  and   no_jmp: "abrupt s0 \<noteq> Some (Jump j)"
  and      wt: "\<lparr>prg=G, cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-T" 
  and      wf: "wf_prog G"
shows "abrupt s1 \<noteq> Some (Jump j)"
using eval no_jmp wt wf
by - (rule eval_expression_no_jump 
            [where ?Env="\<lparr>prg=G, cls=C,lcl=L\<rparr>",simplified],auto)


text {* To derive the most general formula for the loop statement, we need to
come up with a proper loop invariant, which intuitively states that we are 
currently inside the evaluation of the loop. To define such an invariant, we
unroll the loop in iterated evaluations of the expression and evaluations of
the loop body. *}

constdefs
 unroll:: "prog \<Rightarrow> label \<Rightarrow> expr \<Rightarrow> stmt \<Rightarrow> (state \<times>  state) set"

 "unroll G l e c \<equiv> {(s,t). \<exists> v s1 s2.
                             G\<turnstile>s \<midarrow>e-\<succ>v\<rightarrow> s1 \<and> the_Bool v \<and> normal s1 \<and>
                             G\<turnstile>s1 \<midarrow>c\<rightarrow> s2 \<and> t=(abupd (absorb (Cont l)) s2)}"


lemma unroll_while:
  assumes unroll: "(s, t) \<in> (unroll G l e c)\<^sup>*"
  and     eval_e: "G\<turnstile>t \<midarrow>e-\<succ>v\<rightarrow> s'" 
  and     normal_termination: "normal s'  \<longrightarrow> \<not> the_Bool v"
  and     wt: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-T"
  and     wf: "wf_prog G" 
  shows "G\<turnstile>s \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
using unroll (* normal_s *)
proof (induct rule: converse_rtrancl_induct) 
  show "G\<turnstile>t \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
  proof (cases "normal t")
    case False
    with eval_e have "s'=t" by auto
    with False show ?thesis by auto
  next
    case True
    note normal_t = this
    show ?thesis
    proof (cases "normal s'")
      case True
      with normal_t eval_e normal_termination
      show ?thesis
	by (auto intro: eval.Loop)
    next
      case False
      note abrupt_s' = this
      from eval_e _ wt wf
      have no_cont: "abrupt s' \<noteq> Some (Jump (Cont l))"
	by (rule eval_expression_no_jump') (insert normal_t,simp)
      have
	"if the_Bool v 
             then (G\<turnstile>s' \<midarrow>c\<rightarrow> s' \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s') \<midarrow>l\<bullet> While(e) c\<rightarrow> s')
	     else s' = s'"
      proof (cases "the_Bool v")
	case False thus ?thesis by simp
      next
	case True
	with abrupt_s' have "G\<turnstile>s' \<midarrow>c\<rightarrow> s'" by auto
	moreover from abrupt_s' no_cont 
	have no_absorb: "(abupd (absorb (Cont l)) s')=s'"
	  by (cases s') (simp add: absorb_def split: split_if)
	moreover
	from no_absorb abrupt_s'
	have "G\<turnstile>(abupd (absorb (Cont l)) s') \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
	  by auto
	ultimately show ?thesis
	  using True by simp
      qed
      with eval_e 
      show ?thesis
	using normal_t by (auto intro: eval.Loop)
    qed
  qed
next
  fix s s3
  assume unroll: "(s,s3) \<in> unroll G l e c"
  assume while: "G\<turnstile>s3 \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
  show "G\<turnstile>s \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
  proof -
    from unroll obtain v s1 s2 where
      normal_s1: "normal s1" and
      eval_e: "G\<turnstile>s \<midarrow>e-\<succ>v\<rightarrow> s1" and
      continue: "the_Bool v" and
      eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" and
      s3: "s3=(abupd (absorb (Cont l)) s2)"
      by  (unfold unroll_def) fast 
    from eval_e normal_s1 have
      "normal s"
      by (rule eval_no_abrupt_lemma [rule_format])
    with while eval_e continue eval_c s3 show ?thesis
      by (auto intro!: eval.Loop)
  qed
qed


ML"Addsimprocs [eval_expr_proc, eval_var_proc, eval_exprs_proc, eval_stmt_proc]"
  
lemma MGFn_Loop:
  assumes mfg_e: "G,(A::state triple set)\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
  and     mfg_c: "G,A\<turnstile>{=:n} \<langle>c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
  and     wf: "wf_prog G" 
shows "G,A\<turnstile>{=:n} \<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
proof (rule MGFn_free_wt [rule_format],elim exE)
  fix T L C
  assume wt: "\<lparr>prg = G, cls = C, lcl = L\<rparr>\<turnstile>\<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<Colon>T"
  then obtain eT where
    wt_e: "\<lparr>prg = G, cls = C, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" 
    by cases simp
  show ?thesis
  proof (rule MGFn_NormalI)
    show "G,A\<turnstile>{Normal ((\<lambda>Y' s' s. s' = s \<and> normal s) \<and>. G\<turnstile>init\<le>n)} 
              .l\<bullet> While(e) c.
              {\<lambda>Y s' s. G\<turnstile>s \<midarrow>In1r (l\<bullet> While(e) c)\<succ>\<rightarrow> (Y, s')}"
    proof (rule conseq12 
           [where ?P'="(\<lambda> Y s' s. (s,s') \<in> (unroll G l e c)\<^sup>* ) \<and>. G\<turnstile>init\<le>n"
             and  ?Q'="((\<lambda> Y s' s. (\<exists> t b. (s,t) \<in> (unroll G l e c)\<^sup>* \<and> 
                          Y=\<lfloor>b\<rfloor>\<^sub>e \<and> G\<turnstile>t \<midarrow>e-\<succ>b\<rightarrow> s')) 
                        \<and>. G\<turnstile>init\<le>n)\<leftarrow>=False\<down>=\<diamondsuit>"])
      show  "G,A\<turnstile>{(\<lambda>Y s' s. (s, s') \<in> (unroll G l e c)\<^sup>*) \<and>. G\<turnstile>init\<le>n} 
                  .l\<bullet> While(e) c.
                 {((\<lambda>Y s' s. (\<exists>t b. (s, t) \<in> (unroll G l e c)\<^sup>* \<and> 
                                  Y = In1 b \<and> G\<turnstile>t \<midarrow>e-\<succ>b\<rightarrow> s')) 
                              \<and>. G\<turnstile>init\<le>n)\<leftarrow>=False\<down>=\<diamondsuit>}"
      proof (rule ax_derivs.Loop)
	from mfg_e
	show "G,A\<turnstile>{(\<lambda>Y s' s. (s, s') \<in> (unroll G l e c)\<^sup>*) \<and>. G\<turnstile>init\<le>n} 
                   e-\<succ>
                  {(\<lambda>Y s' s. (\<exists>t b. (s, t) \<in> (unroll G l e c)\<^sup>* \<and> 
                                     Y = In1 b \<and> G\<turnstile>t \<midarrow>e-\<succ>b\<rightarrow> s')) 
                   \<and>. G\<turnstile>init\<le>n}"
	proof (rule MGFnD' [THEN conseq12],clarsimp)
	  fix s Z s' v
	  assume "(Z, s) \<in> (unroll G l e c)\<^sup>*"
	  moreover
	  assume "G\<turnstile>s \<midarrow>e-\<succ>v\<rightarrow> s'"
	  ultimately
	  show "\<exists>t. (Z, t) \<in> (unroll G l e c)\<^sup>* \<and> G\<turnstile>t \<midarrow>e-\<succ>v\<rightarrow> s'"
	    by blast
	qed
      next
	from mfg_c
	show "G,A\<turnstile>{Normal (((\<lambda>Y s' s. \<exists>t b. (s, t) \<in> (unroll G l e c)\<^sup>* \<and>
                                       Y = \<lfloor>b\<rfloor>\<^sub>e \<and> G\<turnstile>t \<midarrow>e-\<succ>b\<rightarrow> s') 
                          \<and>. G\<turnstile>init\<le>n)\<leftarrow>=True)}
                  .c.
                  {abupd (absorb (Cont l)) .;
                   ((\<lambda>Y s' s. (s, s') \<in> (unroll G l e c)\<^sup>*) \<and>. G\<turnstile>init\<le>n)}"
	proof (rule MGFnD' [THEN conseq12],clarsimp)
	  fix Z s' s v t
	  assume unroll: "(Z, t) \<in> (unroll G l e c)\<^sup>*"
	  assume eval_e: "G\<turnstile>t \<midarrow>e-\<succ>v\<rightarrow> Norm s" 
	  assume true: "the_Bool v"
	  assume eval_c: "G\<turnstile>Norm s \<midarrow>c\<rightarrow> s'"
	  show "(Z, abupd (absorb (Cont l)) s') \<in> (unroll G l e c)\<^sup>*"
	  proof -
	    note unroll
	    also
	    from eval_e true eval_c
	    have "(t,abupd (absorb (Cont l)) s') \<in> unroll G l e c" 
	      by (unfold unroll_def) force
	    ultimately show ?thesis ..
	  qed
	qed
      qed
    next
      show 
	"\<forall>Y s Z.
         (Normal ((\<lambda>Y' s' s. s' = s \<and> normal s) \<and>. G\<turnstile>init\<le>n)) Y s Z 
         \<longrightarrow> (\<forall>Y' s'.
               (\<forall>Y Z'. 
                 ((\<lambda>Y s' s. (s, s') \<in> (unroll G l e c)\<^sup>*) \<and>. G\<turnstile>init\<le>n) Y s Z' 
                 \<longrightarrow> (((\<lambda>Y s' s. \<exists>t b. (s,t) \<in> (unroll G l e c)\<^sup>* 
                                       \<and> Y=\<lfloor>b\<rfloor>\<^sub>e \<and> G\<turnstile>t \<midarrow>e-\<succ>b\<rightarrow> s') 
                     \<and>. G\<turnstile>init\<le>n)\<leftarrow>=False\<down>=\<diamondsuit>) Y' s' Z') 
               \<longrightarrow> G\<turnstile>Z \<midarrow>\<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<succ>\<rightarrow> (Y', s'))"
      proof (clarsimp)
	fix Y' s' s
	assume asm:
	  "\<forall>Z'. (Z', Norm s) \<in> (unroll G l e c)\<^sup>* 
                 \<longrightarrow> card (nyinitcls G s') \<le> n \<and>
                     (\<exists>v. (\<exists>t. (Z', t) \<in> (unroll G l e c)\<^sup>* \<and> G\<turnstile>t \<midarrow>e-\<succ>v\<rightarrow> s') \<and>
                     (fst s' = None \<longrightarrow> \<not> the_Bool v)) \<and> Y' = \<diamondsuit>"
	show "Y' = \<diamondsuit> \<and> G\<turnstile>Norm s \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
	proof -
	  from asm obtain v t where 
	    -- {* @{term "Z'"} gets instantiated with @{term "Norm s"} *}  
	    unroll: "(Norm s, t) \<in> (unroll G l e c)\<^sup>*" and
            eval_e: "G\<turnstile>t \<midarrow>e-\<succ>v\<rightarrow> s'" and
            normal_termination: "normal s' \<longrightarrow> \<not> the_Bool v" and
	     Y': "Y' = \<diamondsuit>"
	    by auto
	  from unroll eval_e normal_termination wt_e wf
	  have "G\<turnstile>Norm s \<midarrow>l\<bullet> While(e) c\<rightarrow> s'"
	    by (rule unroll_while)
	  with Y' 
	  show ?thesis
	    by simp
	qed
      qed
    qed
  qed
qed

lemma MGFn_FVar:
  fixes A :: "state triple set"
 assumes mgf_init: "G,A\<turnstile>{=:n} \<langle>Init statDeclC\<rangle>\<^sub>s\<succ> {G\<rightarrow>}" 
  and    mgf_e: "G,A\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
  and    wf: "wf_prog G"
  shows "G,A\<turnstile>{=:n} \<langle>{accC,statDeclC,stat}e..fn\<rangle>\<^sub>v\<succ> {G\<rightarrow>}"
proof (rule MGFn_free_wt_da_NormalConformI [rule_format],clarsimp) 
  note inj_term_simps [simp]
  fix T L accC' V
  assume wt: "\<lparr>prg = G, cls = accC', lcl = L\<rparr>\<turnstile>\<langle>{accC,statDeclC,stat}e..fn\<rangle>\<^sub>v\<Colon>T"
  then obtain statC f where
    wt_e: "\<lparr>prg=G, cls=accC', lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
    accfield: "accfield G accC' statC fn = Some (statDeclC,f )" and
    eq_accC: "accC=accC'" and
    stat: "stat=is_static  f"
    by (cases) (auto simp add: member_is_static_simp)
  let ?Q="(\<lambda>Y s1 (x,s) . x = None \<and> 
                (G\<turnstile>Norm s \<midarrow>Init statDeclC\<rightarrow> s1) \<and>
                (\<exists> E. \<lparr>prg=G,cls=accC',lcl=L\<rparr>\<turnstile>dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E))
                \<and>. G\<turnstile>init\<le>n \<and>. (\<lambda> s. s\<Colon>\<preceq>(G, L))"
  show "G,A\<turnstile>{Normal
             ((\<lambda>Y' s' s. s' = s \<and> abrupt s = None) \<and>. G\<turnstile>init\<le>n \<and>.
              (\<lambda>s. s\<Colon>\<preceq>(G, L)) \<and>.
              (\<lambda>s. \<lparr>prg=G,cls=accC',lcl=L\<rparr>
                 \<turnstile> dom (locals (store s)) \<guillemotright> \<langle>{accC,statDeclC,stat}e..fn\<rangle>\<^sub>v\<guillemotright> V))
             } {accC,statDeclC,stat}e..fn=\<succ>
             {\<lambda>Y s' s. \<exists>vf. Y = \<lfloor>vf\<rfloor>\<^sub>v \<and> 
                        G\<turnstile>s \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>vf\<rightarrow> s'}"
    (is "G,A\<turnstile>{Normal ?P} {accC,statDeclC,stat}e..fn=\<succ> {?R}")
  proof (rule ax_derivs.FVar [where ?Q="?Q" ])
    from mgf_init
    show "G,A\<turnstile>{Normal ?P} .Init statDeclC. {?Q}"
    proof (rule MGFnD' [THEN conseq12],clarsimp)
      fix s s'
      assume conf_s: "Norm s\<Colon>\<preceq>(G, L)"
      assume da: "\<lparr>prg=G,cls=accC',lcl=L\<rparr>
                    \<turnstile> dom (locals s) \<guillemotright>\<langle>{accC,statDeclC,stat}e..fn\<rangle>\<^sub>v\<guillemotright> V"
      assume eval_init: "G\<turnstile>Norm s \<midarrow>Init statDeclC\<rightarrow> s'"
      show "(\<exists>E. \<lparr>prg=G, cls=accC', lcl=L\<rparr>\<turnstile> dom (locals (store s')) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E) \<and>
            s'\<Colon>\<preceq>(G, L)"
      proof -
	from da 
	obtain E where
	  "\<lparr>prg=G, cls=accC', lcl=L\<rparr>\<turnstile> dom (locals s) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	  by cases simp
	moreover
	from eval_init
	have "dom (locals s) \<subseteq> dom (locals (store s'))"
	  by (rule dom_locals_eval_mono [elim_format]) simp
	ultimately obtain E' where
	  "\<lparr>prg=G, cls=accC', lcl=L\<rparr>\<turnstile> dom (locals (store s')) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E'"
	  by (rule da_weakenE)
	moreover
	have "s'\<Colon>\<preceq>(G, L)"
	proof -
	  have wt_init: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(Init statDeclC)\<Colon>\<surd>"
	  proof -
	    from wf wt_e 
	    have iscls_statC: "is_class G statC"
	      by (auto dest: ty_expr_is_type type_is_class)
	    with wf accfield 
	    have iscls_statDeclC: "is_class G statDeclC"
	      by (auto dest!: accfield_fields dest: fields_declC)
	    thus ?thesis by simp
	  qed
	  obtain I where 
	    da_init: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
               \<turnstile> dom (locals (store ((Norm s)::state))) \<guillemotright>\<langle>Init statDeclC\<rangle>\<^sub>s\<guillemotright> I"
	    by (auto intro: da_Init [simplified] assigned.select_convs)
	  from eval_init conf_s wt_init da_init  wf
	  show ?thesis
	    by (rule eval_type_soundE)
	qed
	ultimately show ?thesis by rules
      qed
    qed
  next
    from mgf_e
    show "G,A\<turnstile>{?Q} e-\<succ> {\<lambda>Val:a:. fvar statDeclC stat fn a ..; ?R}"
    proof (rule MGFnD' [THEN conseq12],clarsimp)
      fix s0 s1 s2 E a
      let ?fvar = "fvar statDeclC stat fn a s2"
      assume eval_init: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<rightarrow> s1"
      assume eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2"
      assume conf_s1: "s1\<Colon>\<preceq>(G, L)"
      assume da_e: "\<lparr>prg=G,cls=accC',lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
      show "G\<turnstile>Norm s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>fst ?fvar\<rightarrow> snd ?fvar"
      proof -
	obtain v s2' where
	  v: "v=fst ?fvar" and s2': "s2'=snd ?fvar"
	  by simp
	obtain s3 where
	  s3: "s3= check_field_access G accC' statDeclC fn stat a s2'"
	  by simp
	have eq_s3_s2': "s3=s2'"
	proof -
	  from eval_e conf_s1 wt_e da_e wf obtain
	    conf_s2: "s2\<Colon>\<preceq>(G, L)"  and
	    conf_a: "normal s2 \<Longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC"
	    by (rule eval_type_soundE) simp
	  from accfield wt_e eval_init eval_e conf_s2 conf_a _ wf
	  show ?thesis
	    by (rule  error_free_field_access 
                      [where ?v=v and ?s2'=s2',elim_format])
	       (simp add: s3 v s2' stat)+
        qed
	from eval_init eval_e 
	show ?thesis
	  apply (rule eval.FVar [where ?s2'=s2'])
	  apply  (simp add: s2')
	  apply  (simp add: s3 [symmetric]   eq_s3_s2' eq_accC s2' [symmetric])
	  done
      qed
    qed
  qed
qed


lemma MGFn_Fin:
  assumes wf: "wf_prog G" 
  and     mgf_c1: "G,A\<turnstile>{=:n} \<langle>c1\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
  and     mgf_c2: "G,A\<turnstile>{=:n} \<langle>c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
  shows "G,(A\<Colon>state triple set)\<turnstile>{=:n} \<langle>c1 Finally c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
proof (rule MGFn_free_wt_da_NormalConformI [rule_format],clarsimp)
  fix T L accC C 
  assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>In1r (c1 Finally c2)\<Colon>T"
  then obtain
    wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
    wt_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c2\<Colon>\<surd>"
    by cases simp
  let  ?Q = "(\<lambda>Y' s' s. normal s \<and> G\<turnstile>s \<midarrow>c1\<rightarrow> s' \<and> 
               (\<exists> C1. \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s)) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1)
               \<and> s\<Colon>\<preceq>(G, L)) 
             \<and>. G\<turnstile>init\<le>n"
  show "G,A\<turnstile>{Normal
              ((\<lambda>Y' s' s. s' = s \<and> abrupt s = None) \<and>. G\<turnstile>init\<le>n \<and>.
              (\<lambda>s. s\<Colon>\<preceq>(G, L)) \<and>.
              (\<lambda>s. \<lparr>prg=G,cls=accC,lcl =L\<rparr>  
                     \<turnstile>dom (locals (store s)) \<guillemotright>\<langle>c1 Finally c2\<rangle>\<^sub>s\<guillemotright> C))}
             .c1 Finally c2. 
             {\<lambda>Y s' s. Y = \<diamondsuit> \<and> G\<turnstile>s \<midarrow>c1 Finally c2\<rightarrow> s'}"
    (is "G,A\<turnstile>{Normal ?P} .c1 Finally c2. {?R}")
  proof (rule ax_derivs.Fin [where ?Q="?Q"])
    from mgf_c1
    show "G,A\<turnstile>{Normal ?P} .c1. {?Q}"
    proof (rule MGFnD' [THEN conseq12],clarsimp)
      fix s0
      assume "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals s0) \<guillemotright>\<langle>c1 Finally c2\<rangle>\<^sub>s\<guillemotright> C"
      thus "\<exists>C1. \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals s0) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1"
	by cases (auto simp add: inj_term_simps)
    qed
  next
    from mgf_c2
    show "\<forall>abr. G,A\<turnstile>{?Q \<and>. (\<lambda>s. abr = abrupt s) ;. abupd (\<lambda>abr. None)} .c2.
          {abupd (abrupt_if (abr \<noteq> None) abr) .; ?R}"
    proof (rule MGFnD' [THEN conseq12, THEN allI],clarsimp)
      fix s0 s1 s2 C1
      assume da_c1:"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals s0) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1"
      assume conf_s0: "Norm s0\<Colon>\<preceq>(G, L)"
      assume eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1"
      assume eval_c2: "G\<turnstile>abupd (\<lambda>abr. None) s1 \<midarrow>c2\<rightarrow> s2"
      show "G\<turnstile>Norm s0 \<midarrow>c1 Finally c2
               \<rightarrow> abupd (abrupt_if (\<exists>y. abrupt s1 = Some y) (abrupt s1)) s2"
      proof -
	obtain abr1 str1 where s1: "s1=(abr1,str1)"
	  by (cases s1) simp
	with eval_c1 eval_c2 obtain
	  eval_c1': "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (abr1,str1)" and
	  eval_c2': "G\<turnstile>Norm str1 \<midarrow>c2\<rightarrow> s2"
	  by simp
	obtain s3 where 
	  s3: "s3 = (if \<exists>err. abr1 = Some (Error err) 
	                then (abr1, str1)
                        else abupd (abrupt_if (abr1 \<noteq> None) abr1) s2)"
	  by simp
	from eval_c1' conf_s0 wt_c1 _ wf 
	have "error_free (abr1,str1)"
	  by (rule eval_type_soundE) (insert da_c1,auto)
	with s3 have eq_s3: "s3=abupd (abrupt_if (abr1 \<noteq> None) abr1) s2"
	  by (simp add: error_free_def)
	from eval_c1' eval_c2' s3
	show ?thesis
	  by (rule eval.Fin [elim_format]) (simp add: s1 eq_s3)
      qed
    qed 
  qed
qed
      
lemma Body_no_break:
 assumes eval_init: "G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1" 
   and      eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" 
   and       jmpOk: "jumpNestingOkS {Ret} c"
   and        wt_c: "\<lparr>prg=G, cls=C, lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>"
   and        clsD: "class G D=Some d"
   and          wf: "wf_prog G" 
  shows "\<forall> l. abrupt s2 \<noteq> Some (Jump (Break l)) \<and> 
              abrupt s2 \<noteq> Some (Jump (Cont l))"
proof
  fix l show "abrupt s2 \<noteq> Some (Jump (Break l)) \<and>  
              abrupt s2 \<noteq> Some (Jump (Cont l))"
  proof -
    from clsD have wt_init: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(Init D)\<Colon>\<surd>"
      by auto
    from eval_init wf
    have s1_no_jmp: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
      by - (rule eval_statement_no_jump [OF _ _ _ wt_init],auto)
    from eval_c _ wt_c wf
    show ?thesis
      apply (rule jumpNestingOk_eval [THEN conjE, elim_format])
      using jmpOk s1_no_jmp
      apply auto
      done
  qed
qed

lemma MGFn_Body:
  assumes wf: "wf_prog G"
  and     mgf_init: "G,A\<turnstile>{=:n} \<langle>Init D\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
  and     mgf_c: "G,A\<turnstile>{=:n} \<langle>c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
  shows  "G,(A\<Colon>state triple set)\<turnstile>{=:n} \<langle>Body D c\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
proof (rule MGFn_free_wt_da_NormalConformI [rule_format],clarsimp)
  fix T L accC E
  assume wt: "\<lparr>prg=G, cls=accC,lcl=L\<rparr>\<turnstile>\<langle>Body D c\<rangle>\<^sub>e\<Colon>T"
  let ?Q="(\<lambda>Y' s' s. normal s \<and> G\<turnstile>s \<midarrow>Init D\<rightarrow> s' \<and> jumpNestingOkS {Ret} c) 
          \<and>. G\<turnstile>init\<le>n" 
  show "G,A\<turnstile>{Normal
               ((\<lambda>Y' s' s. s' = s \<and> fst s = None) \<and>. G\<turnstile>init\<le>n \<and>.
                (\<lambda>s. s\<Colon>\<preceq>(G, L)) \<and>.
                (\<lambda>s. \<lparr>prg=G,cls=accC,lcl=L\<rparr>
                       \<turnstile> dom (locals (store s)) \<guillemotright>\<langle>Body D c\<rangle>\<^sub>e\<guillemotright> E))}
             Body D c-\<succ> 
             {\<lambda>Y s' s. \<exists>v. Y = In1 v \<and> G\<turnstile>s \<midarrow>Body D c-\<succ>v\<rightarrow> s'}"
    (is "G,A\<turnstile>{Normal ?P} Body D c-\<succ> {?R}")
  proof (rule ax_derivs.Body [where ?Q="?Q"])
    from mgf_init
    show "G,A\<turnstile>{Normal ?P} .Init D. {?Q}"
    proof (rule MGFnD' [THEN conseq12],clarsimp)
      fix s0
      assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals s0) \<guillemotright>\<langle>Body D c\<rangle>\<^sub>e\<guillemotright> E"
      thus "jumpNestingOkS {Ret} c"
	by cases simp
    qed
  next
    from mgf_c
    show "G,A\<turnstile>{?Q}.c.{\<lambda>s.. abupd (absorb Ret) .; ?R\<leftarrow>\<lfloor>the (locals s Result)\<rfloor>\<^sub>e}"
    proof (rule MGFnD' [THEN conseq12],clarsimp)
      fix s0 s1 s2
      assume eval_init: "G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1"
      assume eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2"
      assume nestingOk: "jumpNestingOkS {Ret} c"
      show "G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)
              \<rightarrow> abupd (absorb Ret) s2"
      proof -
	from wt obtain d where 
          d: "class G D=Some d" and
          wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
	  by cases auto
	obtain s3 where 
	  s3: "s3= (if \<exists>l. fst s2 = Some (Jump (Break l)) \<or>
                           fst s2 = Some (Jump (Cont l))
                       then abupd (\<lambda>x. Some (Error CrossMethodJump)) s2 
                       else s2)"
	  by simp
	from eval_init eval_c nestingOk wt_c d wf
	have eq_s3_s2: "s3=s2"
	  by (rule Body_no_break [elim_format]) (simp add: s3)
	from eval_init eval_c s3
	show ?thesis
	  by (rule eval.Body [elim_format]) (simp add: eq_s3_s2)
      qed
    qed
  qed
qed

lemma MGFn_lemma:
  assumes mgf_methds: 
           "\<And> n. \<forall> C sig. G,(A::state triple set)\<turnstile>{=:n} \<langle>Methd C sig\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
  and wf: "wf_prog G"
  shows "\<And> t. G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>}"
proof (induct rule: full_nat_induct)
  fix n t
  assume hyp: "\<forall> m. Suc m \<le> n \<longrightarrow> (\<forall> t. G,A\<turnstile>{=:m} t\<succ> {G\<rightarrow>})"
  show "G,A\<turnstile>{=:n} t\<succ> {G\<rightarrow>}"
  proof -
  { 
    fix v e c es
    have "G,A\<turnstile>{=:n} \<langle>v\<rangle>\<^sub>v\<succ> {G\<rightarrow>}" and 
      "G,A\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}" and
      "G,A\<turnstile>{=:n} \<langle>c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}" and  
      "G,A\<turnstile>{=:n} \<langle>es\<rangle>\<^sub>l\<succ> {G\<rightarrow>}"
    proof (induct rule: var_expr_stmt.induct)
      case (LVar v)
      show "G,A\<turnstile>{=:n} \<langle>LVar v\<rangle>\<^sub>v\<succ> {G\<rightarrow>}"
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.LVar [THEN conseq1])
	apply (clarsimp)
	apply (rule eval.LVar)
	done
    next
      case (FVar accC statDeclC stat e fn)
      have "G,A\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}".
      from MGFn_Init [OF hyp] this wf 
      show ?case
	by (rule MGFn_FVar)
    next
      case (AVar e1 e2)
      have mgf_e1: "G,A\<turnstile>{=:n} \<langle>e1\<rangle>\<^sub>e\<succ> {G\<rightarrow>}".
      have mgf_e2: "G,A\<turnstile>{=:n} \<langle>e2\<rangle>\<^sub>e\<succ> {G\<rightarrow>}".
      show "G,A\<turnstile>{=:n} \<langle>e1.[e2]\<rangle>\<^sub>v\<succ> {G\<rightarrow>}"
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.AVar)
	apply  (rule MGFnD [OF mgf_e1, THEN ax_NormalD])
	apply (rule allI)
	apply (rule MGFnD' [OF mgf_e2, THEN conseq12])
	apply (fastsimp intro: eval.AVar)
	done
    next
      case (InsInitV c v)
      show ?case
	by (rule MGFn_NormalI) (rule ax_derivs.InsInitV)
    next
      case (NewC C)
      show ?case
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.NewC)
	apply (rule MGFn_InitD [OF hyp, THEN conseq2])
	apply (fastsimp intro: eval.NewC)
	done
    next
      case (NewA T e)
      thus ?case
	apply -
	apply (rule MGFn_NormalI) 
	apply (rule ax_derivs.NewA 
               [where ?Q = "(\<lambda>Y' s' s. normal s \<and> G\<turnstile>s \<midarrow>In1r (init_comp_ty T) 
                              \<succ>\<rightarrow> (Y',s')) \<and>. G\<turnstile>init\<le>n"])
	apply  (simp add: init_comp_ty_def split add: split_if)
	apply  (rule conjI, clarsimp)
	apply   (rule MGFn_InitD [OF hyp, THEN conseq2])
	apply   (clarsimp intro: eval.Init)
	apply  clarsimp
	apply  (rule ax_derivs.Skip [THEN conseq1])
	apply  (clarsimp intro: eval.Skip)
	apply (erule MGFnD' [THEN conseq12])
	apply (fastsimp intro: eval.NewA)
	done
    next
      case (Cast C e)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Cast])
	apply (fastsimp intro: eval.Cast)
	done
    next
      case (Inst e C)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Inst])
	apply (fastsimp intro: eval.Inst)
	done
    next
      case (Lit v)
      show ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Lit [THEN conseq1])
	apply (fastsimp intro: eval.Lit)
	done
    next
      case (UnOp unop e)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.UnOp)
	apply (erule MGFnD' [THEN conseq12])
	apply (fastsimp intro: eval.UnOp)
	done
    next
      case (BinOp binop e1 e2)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.BinOp)
	apply  (erule MGFnD [THEN ax_NormalD])
	apply (rule allI)
	apply (case_tac "need_second_arg binop__ v1")
	apply  simp
	apply  (erule MGFnD' [THEN conseq12])
	apply  (fastsimp intro: eval.BinOp)
	apply simp
	apply (rule ax_Normal_cases)
	apply  (rule ax_derivs.Skip [THEN conseq1])
	apply  clarsimp
	apply  (rule eval_BinOp_arg2_indepI)
	apply   simp
	apply  simp
	apply (rule ax_derivs.Abrupt [THEN conseq1], clarsimp simp add: Let_def)
	apply (fastsimp intro: eval.BinOp)
	done
    next
      case Super
      show ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Super [THEN conseq1])
	apply (fastsimp intro: eval.Super)
	done
    next
      case (Acc v)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Acc])
	apply (fastsimp intro: eval.Acc simp add: split_paired_all)
	done
    next
      case (Ass v e)
      thus "G,A\<turnstile>{=:n} \<langle>v:=e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Ass)
	apply  (erule MGFnD [THEN ax_NormalD])
	apply (rule allI)
	apply (erule MGFnD'[THEN conseq12])
	apply (fastsimp intro: eval.Ass simp add: split_paired_all)
	done
    next
      case (Cond e1 e2 e3)
      thus "G,A\<turnstile>{=:n} \<langle>e1 ? e2 : e3\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Cond)
	apply  (erule MGFnD [THEN ax_NormalD])
	apply (rule allI)
	apply (rule ax_Normal_cases)
	prefer 2
	apply  (rule ax_derivs.Abrupt [THEN conseq1],clarsimp simp add: Let_def)
	apply  (fastsimp intro: eval.Cond)
	apply (case_tac "b")
	apply  simp
	apply  (erule MGFnD'[THEN conseq12])
	apply  (fastsimp intro: eval.Cond)
	apply simp
	apply (erule MGFnD'[THEN conseq12])
	apply (fastsimp intro: eval.Cond)
	done
    next
      case (Call accC statT mode e mn pTs' ps)
      have mgf_e:  "G,A\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}".
      have mgf_ps: "G,A\<turnstile>{=:n} \<langle>ps\<rangle>\<^sub>l\<succ> {G\<rightarrow>}".
      from mgf_methds mgf_e mgf_ps wf
      show "G,A\<turnstile>{=:n} \<langle>{accC,statT,mode}e\<cdot>mn({pTs'}ps)\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
	by (rule MGFn_Call)
    next
      case (Methd D mn)
      from mgf_methds
      show "G,A\<turnstile>{=:n} \<langle>Methd D mn\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
	by simp
    next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
      case (Body D c)
      have mgf_c: "G,A\<turnstile>{=:n} \<langle>c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}" .
      from wf MGFn_Init [OF hyp] mgf_c
      show "G,A\<turnstile>{=:n} \<langle>Body D c\<rangle>\<^sub>e\<succ> {G\<rightarrow>}"
	by (rule MGFn_Body)
    next
      case (InsInitE c e)
      show ?case
	by (rule MGFn_NormalI) (rule ax_derivs.InsInitE)
    next
      case (Callee l e)
      show ?case
	by (rule MGFn_NormalI) (rule ax_derivs.Callee)
    next
      case Skip
      show ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Skip [THEN conseq1])
	apply (fastsimp intro: eval.Skip)
	done
    next
      case (Expr e)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (erule MGFnD'[THEN conseq12,THEN ax_derivs.Expr])
	apply (fastsimp intro: eval.Expr)
	done
    next
      case (Lab l c)
      thus "G,A\<turnstile>{=:n} \<langle>l\<bullet> c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (erule MGFnD' [THEN conseq12, THEN ax_derivs.Lab])
	apply (fastsimp intro: eval.Lab)
	done
    next
      case (Comp c1 c2)
      thus "G,A\<turnstile>{=:n} \<langle>c1;; c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Comp)
	apply  (erule MGFnD [THEN ax_NormalD])
	apply (erule MGFnD' [THEN conseq12])
	apply (fastsimp intro: eval.Comp) 
	done
    next
      case (If_ e c1 c2)
      thus "G,A\<turnstile>{=:n} \<langle>If(e) c1 Else c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.If)
	apply  (erule MGFnD [THEN ax_NormalD])
	apply (rule allI)
	apply (rule ax_Normal_cases)
	prefer 2
	apply  (rule ax_derivs.Abrupt [THEN conseq1],clarsimp simp add: Let_def)
	apply  (fastsimp intro: eval.If)
	apply (case_tac "b")
	apply  simp
	apply  (erule MGFnD' [THEN conseq12])
	apply  (fastsimp intro: eval.If)
	apply simp
	apply (erule MGFnD' [THEN conseq12])
	apply (fastsimp intro: eval.If)
	done
    next
      case (Loop l e c)
      have mgf_e: "G,A\<turnstile>{=:n} \<langle>e\<rangle>\<^sub>e\<succ> {G\<rightarrow>}".
      have mgf_c: "G,A\<turnstile>{=:n} \<langle>c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}".
      from mgf_e mgf_c wf
      show "G,A\<turnstile>{=:n} \<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	by (rule MGFn_Loop)
    next
      case (Jmp j)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Jmp [THEN conseq1])
	apply (auto intro: eval.Jmp simp add: abupd_def2)
	done
    next
      case (Throw e)
      thus ?case
	apply -
	apply (rule MGFn_NormalI)
	apply (erule MGFnD' [THEN conseq12, THEN ax_derivs.Throw])
	apply (fastsimp intro: eval.Throw)
	done
    next
      case (TryC c1 C vn c2)
      thus "G,A\<turnstile>{=:n} \<langle>Try c1 Catch(C vn) c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Try [where 
          ?Q = " (\<lambda>Y' s' s. normal s \<and> (\<exists>s''. G\<turnstile>s \<midarrow>\<langle>c1\<rangle>\<^sub>s\<succ>\<rightarrow> (Y',s'') \<and> 
                            G\<turnstile>s'' \<midarrow>sxalloc\<rightarrow> s')) \<and>. G\<turnstile>init\<le>n"])
	apply   (erule MGFnD [THEN ax_NormalD, THEN conseq2])
	apply   (fastsimp elim: sxalloc_gext [THEN card_nyinitcls_gext])
	apply  (erule MGFnD'[THEN conseq12])
	apply  (fastsimp intro: eval.Try)
	apply (fastsimp intro: eval.Try)
	done
    next
      case (Fin c1 c2)
      have mgf_c1: "G,A\<turnstile>{=:n} \<langle>c1\<rangle>\<^sub>s\<succ> {G\<rightarrow>}".
      have mgf_c2: "G,A\<turnstile>{=:n} \<langle>c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}".
      from wf mgf_c1 mgf_c2
      show "G,A\<turnstile>{=:n} \<langle>c1 Finally c2\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	by (rule MGFn_Fin)
    next
      case (FinA abr c)
      show ?case
	by (rule MGFn_NormalI) (rule ax_derivs.FinA)
    next
      case (Init C)
      from hyp
      show "G,A\<turnstile>{=:n} \<langle>Init C\<rangle>\<^sub>s\<succ> {G\<rightarrow>}"
	by (rule MGFn_Init)
    next
      case Nil_expr
      show "G,A\<turnstile>{=:n} \<langle>[]\<rangle>\<^sub>l\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Nil [THEN conseq1])
	apply (fastsimp intro: eval.Nil)
	done
    next
      case (Cons_expr e es)
      thus "G,A\<turnstile>{=:n} \<langle>e# es\<rangle>\<^sub>l\<succ> {G\<rightarrow>}"
	apply -
	apply (rule MGFn_NormalI)
	apply (rule ax_derivs.Cons)
	apply  (erule MGFnD [THEN ax_NormalD])
	apply (rule allI)
	apply (erule MGFnD'[THEN conseq12])
	apply (fastsimp intro: eval.Cons)
	done
    qed
  }
  thus ?thesis
    by (cases rule: term_cases) auto
  qed
qed

lemma MGF_asm: 
"\<lbrakk>\<forall>C sig. is_methd G C sig \<longrightarrow> G,A\<turnstile>{\<doteq>} In1l (Methd C sig)\<succ> {G\<rightarrow>}; wf_prog G\<rbrakk>
 \<Longrightarrow> G,(A::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (simp (no_asm_use) add: MGF_MGFn_iff)
apply (rule allI)
apply (rule MGFn_lemma)
apply (intro strip)
apply (rule MGFn_free_wt)
apply (force dest: wt_Methd_is_methd)
apply assumption (* wf_prog G *)
done

section "nested version"

lemma nesting_lemma' [rule_format (no_asm)]: 
  assumes ax_derivs_asm: "\<And>A ts. ts \<subseteq> A \<Longrightarrow> P A ts" 
  and MGF_nested_Methd: "\<And>A pn. \<forall>b\<in>bdy pn. P (insert (mgf_call pn) A) {mgf b}
                                  \<Longrightarrow> P A {mgf_call pn}"
  and MGF_asm: "\<And>A t. \<forall>pn\<in>U. P A {mgf_call pn} \<Longrightarrow> P A {mgf t}"
  and finU: "finite U"
  and uA: "uA = mgf_call`U"
  shows "\<forall>A. A \<subseteq> uA \<longrightarrow> n \<le> card uA \<longrightarrow> card A = card uA - n 
             \<longrightarrow> (\<forall>t. P A {mgf t})"
using finU uA
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
apply (drule spec, erule impE, erule_tac [2] impE, erule_tac [3] spec)
apply   fast
apply (drule finite_subset)
apply (erule finite_imageI)
apply auto
apply arith
done


lemma nesting_lemma [rule_format (no_asm)]:
  assumes ax_derivs_asm: "\<And>A ts. ts \<subseteq> A \<Longrightarrow> P A ts"
  and MGF_nested_Methd: "\<And>A pn. \<forall>b\<in>bdy pn. P (insert (mgf (f pn)) A) {mgf b}
                                  \<Longrightarrow> P A {mgf (f pn)}"
  and MGF_asm: "\<And>A t. \<forall>pn\<in>U. P A {mgf (f pn)} \<Longrightarrow> P A {mgf t}"
  and finU: "finite U"
shows "P {} {mgf t}"
using ax_derivs_asm MGF_nested_Methd MGF_asm finU
by (rule nesting_lemma') (auto intro!: le_refl)


lemma MGF_nested_Methd: "\<lbrakk>  
 G,insert ({Normal \<doteq>} \<langle>Methd  C sig\<rangle>\<^sub>e \<succ>{G\<rightarrow>}) A
    \<turnstile>{Normal \<doteq>} \<langle>body G C sig\<rangle>\<^sub>e \<succ>{G\<rightarrow>}  
 \<rbrakk> \<Longrightarrow>  G,A\<turnstile>{Normal \<doteq>}  \<langle>Methd  C sig\<rangle>\<^sub>e \<succ>{G\<rightarrow>}"
apply (unfold MGF_def)
apply (rule ax_MethdN)
apply (erule conseq2)
apply clarsimp
apply (erule MethdI)
done

lemma MGF_deriv: "wf_prog G \<Longrightarrow> G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
apply (rule MGFNormalI)
apply (rule_tac mgf = "\<lambda>t. {Normal \<doteq>} t\<succ> {G\<rightarrow>}" and 
                bdy = "\<lambda> (C,sig) .{\<langle>body G C sig\<rangle>\<^sub>e }" and 
                f = "\<lambda> (C,sig) . \<langle>Methd C sig\<rangle>\<^sub>e " in nesting_lemma)
apply    (erule ax_derivs.asm)
apply   (clarsimp simp add: split_tupled_all)
apply   (erule MGF_nested_Methd)
apply  (erule_tac [2] finite_is_methd [OF wf_ws_prog])
apply (rule MGF_asm [THEN MGFNormalD])
apply (auto intro: MGFNormalI)
done


section "simultaneous version"

lemma MGF_simult_Methd_lemma: "finite ms \<Longrightarrow>  
  G,A \<union> (\<lambda>(C,sig). {Normal \<doteq>} \<langle>Methd  C sig\<rangle>\<^sub>e\<succ> {G\<rightarrow>}) ` ms  
      |\<turnstile>(\<lambda>(C,sig). {Normal \<doteq>} \<langle>body G C sig\<rangle>\<^sub>e\<succ> {G\<rightarrow>}) ` ms \<Longrightarrow>  
  G,A|\<turnstile>(\<lambda>(C,sig). {Normal \<doteq>} \<langle>Methd  C sig\<rangle>\<^sub>e\<succ> {G\<rightarrow>}) ` ms"
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

lemma MGF_simult_Methd: "wf_prog G \<Longrightarrow> 
   G,({}::state triple set)|\<turnstile>(\<lambda>(C,sig). {Normal \<doteq>} \<langle>Methd C sig\<rangle>\<^sub>e\<succ> {G\<rightarrow>}) 
   ` Collect (split (is_methd G)) "
apply (frule finite_is_methd [OF wf_ws_prog])
apply (rule MGF_simult_Methd_lemma)
apply  assumption
apply (erule ax_finite_pointwise)
prefer 2
apply  (rule ax_derivs.asm)
apply  blast
apply clarsimp
apply (rule MGF_asm [THEN MGFNormalD])
apply   (auto intro: MGFNormalI)
done


section "corollaries"

lemma eval_to_evaln: "\<lbrakk>G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y', s');type_ok G t s; wf_prog G\<rbrakk>
 \<Longrightarrow>   \<exists>n. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y', s')"
apply (cases "normal s")
apply   (force simp add: type_ok_def intro: eval_evaln)
apply   (force intro: evaln.Abrupt)
done

lemma MGF_complete:
  assumes valid: "G,{}\<Turnstile>{P} t\<succ> {Q}"
  and     mgf: "G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
  and      wf: "wf_prog G"
  shows "G,({}::state triple set)\<turnstile>{P::state assn} t\<succ> {Q}"
proof (rule ax_no_hazard)
  from mgf
  have "G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {\<lambda>Y s' s. G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y, s')}"  
    by  (unfold MGF_def) 
  thus "G,({}::state triple set)\<turnstile>{P \<and>. type_ok G t} t\<succ> {Q}"
  proof (rule conseq12,clarsimp)
    fix Y s Z Y' s'
    assume P: "P Y s Z"
    assume type_ok: "type_ok G t s"
    assume eval_t: "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (Y', s')"
    show "Q Y' s' Z"
    proof -
      from eval_t type_ok wf 
      obtain n where evaln: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y', s')"
	by (rule eval_to_evaln [elim_format]) rules
      from valid have 
	valid_expanded:
	"\<forall>n Y s Z. P Y s Z \<longrightarrow> type_ok G t s 
                   \<longrightarrow> (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y', s') \<longrightarrow> Q Y' s' Z)"
	by (simp add: ax_valids_def triple_valid_def)
      from P type_ok evaln
      show "Q Y' s' Z"
	by (rule valid_expanded [rule_format])
    qed
  qed 
qed
   
theorem ax_complete: 
  assumes wf: "wf_prog G" 
  and valid: "G,{}\<Turnstile>{P::state assn} t\<succ> {Q}"
  shows "G,({}::state triple set)\<turnstile>{P} t\<succ> {Q}"
proof -
  from wf have "G,({}::state triple set)\<turnstile>{\<doteq>} t\<succ> {G\<rightarrow>}"
    by (rule MGF_deriv)
  from valid this wf
  show ?thesis
    by (rule MGF_complete)
qed
 
end
