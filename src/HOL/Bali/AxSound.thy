(*  Title:      HOL/Bali/AxSound.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
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
 \<longrightarrow> (\<forall>T C A. (normal s \<longrightarrow> (\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T \<and> 
                            \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>A)) \<longrightarrow>
 (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s') \<longrightarrow> Q Y' s' Z \<and> s'\<Colon>\<preceq>(G,L))))"

text {* This definition differs from the ordinary  @{text triple_valid_def} 
manly in the conclusion: We also ensures conformance of the result state. So
we don't have to apply the type soundness lemma all the time during
induction. This definition is only introduced for the soundness
proof of the axiomatic semantics, in the end we will conclude to 
the ordinary definition.
*}
 
defs  ax_valids2_def:    "G,A|\<Turnstile>\<Colon>ts \<equiv>  \<forall>n. (\<forall>t\<in>A. G\<Turnstile>n\<Colon>t) \<longrightarrow> (\<forall>t\<in>ts. G\<Turnstile>n\<Colon>t)"

lemma triple_valid2_def2: "G\<Turnstile>n\<Colon>{P} t\<succ> {Q} =  
 (\<forall>Y s Z. P Y s Z \<longrightarrow> (\<forall>Y' s'. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s')\<longrightarrow>  
  (\<forall>L. s\<Colon>\<preceq>(G,L) \<longrightarrow> (\<forall>T C A. (normal s \<longrightarrow> (\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T \<and> 
                            \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>A)) \<longrightarrow>
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
apply  (elim conjE impE)
apply    blast

apply    (tactic "smp_tac 2 1")
apply    (drule evaln_eval)
apply    (drule (1) eval_type_sound [THEN conjunct1],simp, assumption+)
apply    simp

apply    clarsimp
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
apply (erule wt_elim_cases, erule da_elim_cases, erule evaln_elim_cases)
apply (unfold body_def Let_def)
apply (clarsimp simp add: inj_term_simps)
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
  assumes recursive: "G,A\<union>  {{P} Methd-\<succ> {Q} | ms}|\<Turnstile>\<Colon>{{P} body G-\<succ> {Q} | ms}"
  shows "G,A|\<Turnstile>\<Colon>{{P} Methd-\<succ> {Q} | ms}"
proof -
  {
    fix n
    assume recursive: "\<And> n. \<forall>t\<in>(A \<union> {{P} Methd-\<succ> {Q} | ms}). G\<Turnstile>n\<Colon>t
                              \<Longrightarrow>  \<forall>t\<in>{{P} body G-\<succ> {Q} | ms}.  G\<Turnstile>n\<Colon>t"
    have "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t \<Longrightarrow> \<forall>t\<in>{{P} Methd-\<succ> {Q} | ms}.  G\<Turnstile>n\<Colon>t"
    proof (induct n)
      case 0
      show "\<forall>t\<in>{{P} Methd-\<succ> {Q} | ms}.  G\<Turnstile>0\<Colon>t"
      proof -
	{
	  fix C sig
	  assume "(C,sig) \<in> ms" 
	  have "G\<Turnstile>0\<Colon>{Normal (P C sig)} Methd C sig-\<succ> {Q C sig}"
	    by (rule Methd_triple_valid2_0)
	}
	thus ?thesis
	  by (simp add: mtriples_def split_def)
      qed
    next
      case (Suc m)
      have hyp: "\<forall>t\<in>A. G\<Turnstile>m\<Colon>t \<Longrightarrow> \<forall>t\<in>{{P} Methd-\<succ> {Q} | ms}.  G\<Turnstile>m\<Colon>t".
      have prem: "\<forall>t\<in>A. G\<Turnstile>Suc m\<Colon>t" .
      show "\<forall>t\<in>{{P} Methd-\<succ> {Q} | ms}.  G\<Turnstile>Suc m\<Colon>t"
      proof -
	{
	  fix C sig
	  assume m: "(C,sig) \<in> ms" 
	  have "G\<Turnstile>Suc m\<Colon>{Normal (P C sig)} Methd C sig-\<succ> {Q C sig}"
	  proof -
	    from prem have prem_m: "\<forall>t\<in>A. G\<Turnstile>m\<Colon>t"
	      by (rule triples_valid2_Suc)
	    hence "\<forall>t\<in>{{P} Methd-\<succ> {Q} | ms}.  G\<Turnstile>m\<Colon>t"
	      by (rule hyp)
	    with prem_m
	    have "\<forall>t\<in>(A \<union> {{P} Methd-\<succ> {Q} | ms}). G\<Turnstile>m\<Colon>t"
	      by (simp add: ball_Un)
	    hence "\<forall>t\<in>{{P} body G-\<succ> {Q} | ms}.  G\<Turnstile>m\<Colon>t"
	      by (rule recursive)
	    with m have "G\<Turnstile>m\<Colon>{Normal (P C sig)} body G C sig-\<succ> {Q C sig}"
	      by (auto simp add: mtriples_def split_def)
	    thus ?thesis
	      by (rule Methd_triple_valid2_SucI)
	  qed
	}
	thus ?thesis
	  by (simp add: mtriples_def split_def)
      qed
    qed
  }
  with recursive show ?thesis
    by (unfold ax_valids2_def) blast
qed


lemma valids2_inductI: "\<forall>s t n Y' s'. G\<turnstile>s\<midarrow>t\<succ>\<midarrow>n\<rightarrow> (Y',s') \<longrightarrow> t = c \<longrightarrow>    
  Ball A (triple_valid2 G n) \<longrightarrow> (\<forall>Y Z. P Y s Z \<longrightarrow>  
  (\<forall>L. s\<Colon>\<preceq>(G,L) \<longrightarrow> 
    (\<forall>T C A. (normal s \<longrightarrow> (\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T) \<and> 
                            \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>A) \<longrightarrow>
    Q Y' s' Z \<and> s'\<Colon>\<preceq>(G, L)))) \<Longrightarrow>  
  G,A|\<Turnstile>\<Colon>{ {P} c\<succ> {Q}}"
apply (simp (no_asm) add: ax_valids2_def triple_valid2_def2)
apply clarsimp
done

lemma da_good_approx_evalnE [consumes 4]:
  assumes evaln: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v, s1)"
     and     wt: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T"
     and     da: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>t\<guillemotright> A"
     and     wf: "wf_prog G"
     and   elim: "\<lbrakk>normal s1 \<Longrightarrow> nrm A \<subseteq> dom (locals (store s1));
                  \<And> l. \<lbrakk>abrupt s1 = Some (Jump (Break l)); normal s0\<rbrakk>
                        \<Longrightarrow> brk A l \<subseteq> dom (locals (store s1));
                   \<lbrakk>abrupt s1 = Some (Jump Ret);normal s0\<rbrakk>
                   \<Longrightarrow>Result \<in> dom (locals (store s1))
                  \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from evaln have "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v, s1)"
    by (rule evaln_eval)
  from this wt da wf elim show P
    by (rule da_good_approxE') rules+
qed

lemma validI: 
   assumes I: "\<And> n s0 L accC T C v s1 Y Z.
               \<lbrakk>\<forall>t\<in>A. G\<Turnstile>n\<Colon>t; s0\<Colon>\<preceq>(G,L); 
               normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T;
               normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>C;
               G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1); P Y s0 Z\<rbrakk> \<Longrightarrow> Q v s1 Z \<and> s1\<Colon>\<preceq>(G,L)" 
  shows "G,A|\<Turnstile>\<Colon>{ {P} t\<succ> {Q} }"
apply (simp add: ax_valids2_def triple_valid2_def2)
apply (intro allI impI)
apply (case_tac "normal s")
apply   clarsimp 
apply   (rule I,(assumption|simp)+)

apply   (rule I,auto)
done
  



ML "Addsimprocs [wt_expr_proc,wt_var_proc,wt_exprs_proc,wt_stmt_proc]"

lemma valid_stmtI: 
   assumes I: "\<And> n s0 L accC C s1 Y Z.
             \<lbrakk>\<forall>t\<in>A. G\<Turnstile>n\<Colon>t; s0\<Colon>\<preceq>(G,L); 
              normal s0\<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>;
              normal s0\<Longrightarrow>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright>C;
              G\<turnstile>s0 \<midarrow>c\<midarrow>n\<rightarrow> s1; P Y s0 Z\<rbrakk> \<Longrightarrow> Q \<diamondsuit> s1 Z \<and> s1\<Colon>\<preceq>(G,L)" 
  shows "G,A|\<Turnstile>\<Colon>{ {P} \<langle>c\<rangle>\<^sub>s\<succ> {Q} }"
apply (simp add: ax_valids2_def triple_valid2_def2)
apply (intro allI impI)
apply (case_tac "normal s")
apply   clarsimp 
apply   (rule I,(assumption|simp)+)

apply   (rule I,auto)
done

lemma valid_stmt_NormalI: 
   assumes I: "\<And> n s0 L accC C s1 Y Z.
               \<lbrakk>\<forall>t\<in>A. G\<Turnstile>n\<Colon>t; s0\<Colon>\<preceq>(G,L); normal s0; \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>;
               \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright>C;
               G\<turnstile>s0 \<midarrow>c\<midarrow>n\<rightarrow> s1; (Normal P) Y s0 Z\<rbrakk> \<Longrightarrow> Q \<diamondsuit> s1 Z \<and> s1\<Colon>\<preceq>(G,L)" 
  shows "G,A|\<Turnstile>\<Colon>{ {Normal P} \<langle>c\<rangle>\<^sub>s\<succ> {Q} }"
apply (simp add: ax_valids2_def triple_valid2_def2)
apply (intro allI impI)
apply (elim exE conjE)
apply (rule I)
by auto

lemma valid_var_NormalI: 
   assumes I: "\<And> n s0 L accC T C vf s1 Y Z.
               \<lbrakk>\<forall>t\<in>A. G\<Turnstile>n\<Colon>t; s0\<Colon>\<preceq>(G,L); normal s0; 
                \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>=T;
                \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>t\<rangle>\<^sub>v\<guillemotright>C;
                G\<turnstile>s0 \<midarrow>t=\<succ>vf\<midarrow>n\<rightarrow> s1; (Normal P) Y s0 Z\<rbrakk> 
               \<Longrightarrow> Q (In2 vf) s1 Z \<and> s1\<Colon>\<preceq>(G,L)"
   shows "G,A|\<Turnstile>\<Colon>{ {Normal P} \<langle>t\<rangle>\<^sub>v\<succ> {Q} }"
apply (simp add: ax_valids2_def triple_valid2_def2)
apply (intro allI impI)
apply (elim exE conjE)
apply simp
apply (rule I)
by auto

lemma valid_expr_NormalI: 
   assumes I: "\<And> n s0 L accC T C v s1 Y Z.
               \<lbrakk>\<forall>t\<in>A. G\<Turnstile>n\<Colon>t; s0\<Colon>\<preceq>(G,L); normal s0; 
                \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>-T;
                \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>t\<rangle>\<^sub>e\<guillemotright>C;
                G\<turnstile>s0 \<midarrow>t-\<succ>v\<midarrow>n\<rightarrow> s1; (Normal P) Y s0 Z\<rbrakk> 
               \<Longrightarrow> Q (In1 v) s1 Z \<and> s1\<Colon>\<preceq>(G,L)"
   shows "G,A|\<Turnstile>\<Colon>{ {Normal P} \<langle>t\<rangle>\<^sub>e\<succ> {Q} }"
apply (simp add: ax_valids2_def triple_valid2_def2)
apply (intro allI impI)
apply (elim exE conjE)
apply simp
apply (rule I)
by auto

lemma valid_expr_list_NormalI: 
   assumes I: "\<And> n s0 L accC T C vs s1 Y Z.
               \<lbrakk>\<forall>t\<in>A. G\<Turnstile>n\<Colon>t; s0\<Colon>\<preceq>(G,L); normal s0; 
                \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>\<doteq>T;
                \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>t\<rangle>\<^sub>l\<guillemotright>C;
                G\<turnstile>s0 \<midarrow>t\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s1; (Normal P) Y s0 Z\<rbrakk> 
                \<Longrightarrow> Q (In3 vs) s1 Z \<and> s1\<Colon>\<preceq>(G,L)"
   shows "G,A|\<Turnstile>\<Colon>{ {Normal P} \<langle>t\<rangle>\<^sub>l\<succ> {Q} }"
apply (simp add: ax_valids2_def triple_valid2_def2)
apply (intro allI impI)
apply (elim exE conjE)
apply simp
apply (rule I)
by auto

lemma validE [consumes 5]: 
  assumes valid: "G,A|\<Turnstile>\<Colon>{ {P} t\<succ> {Q} }"
   and    P: "P Y s0 Z"
   and    valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
   and    conf: "s0\<Colon>\<preceq>(G,L)"
   and    eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)"
   and    wt: "normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T"
   and    da: "normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>C"
   and    elim: "\<lbrakk>Q v s1 Z; s1\<Colon>\<preceq>(G,L)\<rbrakk> \<Longrightarrow> concl" 
  shows "concl"
using prems
by (simp add: ax_valids2_def triple_valid2_def2) fast
(* why consumes 5?. If I want to apply this lemma in a context wgere
   \<not> normal s0 holds,
   I can chain "\<not> normal s0" as fact number 6 and apply the rule with
   cases. Auto will then solve premise 6 and 7.
*)

lemma all_empty: "(!x. P) = P"
by simp

corollary evaln_type_sound:
  assumes evaln: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)" and
             wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T" and
             da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>t\<guillemotright> A" and
        conf_s0: "s0\<Colon>\<preceq>(G,L)" and
             wf: "wf_prog G"                         
  shows "s1\<Colon>\<preceq>(G,L) \<and>  (normal s1 \<longrightarrow> G,L,store s1\<turnstile>t\<succ>v\<Colon>\<preceq>T) \<and> 
         (error_free s0 = error_free s1)"
proof -
  from evaln have "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)"
    by (rule evaln_eval)
  from this wt da wf conf_s0 show ?thesis
    by (rule eval_type_sound)
qed

corollary dom_locals_evaln_mono_elim [consumes 1]: 
  assumes   
  evaln: "G\<turnstile> s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)" and
    hyps: "\<lbrakk>dom (locals (store s0)) \<subseteq> dom (locals (store s1));
           \<And> vv s val. \<lbrakk>v=In2 vv; normal s1\<rbrakk> 
                        \<Longrightarrow> dom (locals (store s)) 
                             \<subseteq> dom (locals (store ((snd vv) val s)))\<rbrakk> \<Longrightarrow> P"
 shows "P"
proof -
  from evaln have "G\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" by (rule evaln_eval)
  from this hyps show ?thesis
    by (rule dom_locals_eval_mono_elim) rules+
qed



lemma evaln_no_abrupt: 
   "\<And>s s'. \<lbrakk>G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (w,s'); normal s'\<rbrakk> \<Longrightarrow> normal s"
by (erule evaln_cases,auto)

declare inj_term_simps [simp]
lemma ax_sound2: 
  assumes    wf: "wf_prog G" 
    and   deriv: "G,A|\<turnstile>ts"
  shows "G,A|\<Turnstile>\<Colon>ts"
using deriv
proof (induct)
  case (empty A)
  show ?case
    by (simp add: ax_valids2_def triple_valid2_def2)
next
  case (insert A t ts)
  have valid_t: "G,A|\<Turnstile>\<Colon>{t}" . 
  moreover have valid_ts: "G,A|\<Turnstile>\<Colon>ts" .
  {
    fix n assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    have "G\<Turnstile>n\<Colon>t" and "\<forall>t\<in>ts. G\<Turnstile>n\<Colon>t"
    proof -
      from valid_A valid_t show "G\<Turnstile>n\<Colon>t"
	by (simp add: ax_valids2_def)
    next
      from valid_A valid_ts show "\<forall>t\<in>ts. G\<Turnstile>n\<Colon>t"
	by (unfold ax_valids2_def) blast
    qed
    hence "\<forall>t'\<in>insert t ts. G\<Turnstile>n\<Colon>t'"
      by simp
  }
  thus ?case
    by (unfold ax_valids2_def) blast
next
  case (asm A ts)
  have "ts \<subseteq> A" .
  then show "G,A|\<Turnstile>\<Colon>ts"
    by (auto simp add: ax_valids2_def triple_valid2_def)
next
  case (weaken A ts ts')
  have "G,A|\<Turnstile>\<Colon>ts'" .
  moreover have "ts \<subseteq> ts'" .
  ultimately show "G,A|\<Turnstile>\<Colon>ts"
    by (unfold ax_valids2_def triple_valid2_def) blast
next
  case (conseq A P Q t)
  have con: "\<forall>Y s Z. P Y s Z \<longrightarrow> 
              (\<exists>P' Q'.
                  (G,A\<turnstile>{P'} t\<succ> {Q'} \<and> G,A|\<Turnstile>\<Colon>{ {P'} t\<succ> {Q'} }) \<and>
                  (\<forall>Y' s'. (\<forall>Y Z'. P' Y s Z' \<longrightarrow> Q' Y' s' Z') \<longrightarrow> Q Y' s' Z))".
  show "G,A|\<Turnstile>\<Colon>{ {P} t\<succ> {Q} }"
  proof (rule validI)
    fix n s0 L accC T C v s1 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t" 
    assume conf: "s0\<Colon>\<preceq>(G,L)"
    assume wt: "normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T"
    assume da: "normal s0 
                 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>t\<guillemotright> C"
    assume eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v, s1)"
    assume P: "P Y s0 Z"
    show "Q v s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from valid_A conf wt da eval P con
      have "Q v s1 Z"
	apply (simp add: ax_valids2_def triple_valid2_def2)
	apply (tactic "smp_tac 3 1")
	apply clarify
	apply (tactic "smp_tac 1 1")
	apply (erule allE,erule allE, erule mp)
	apply (intro strip)
	apply (tactic "smp_tac 3 1")
	apply (tactic "smp_tac 2 1")
	apply (tactic "smp_tac 1 1")
	by blast
      moreover have "s1\<Colon>\<preceq>(G, L)"
      proof (cases "normal s0")
	case True
	from eval wt [OF True] da [OF True] conf wf 
	show ?thesis
	  by (rule evaln_type_sound [elim_format]) simp
      next
	case False
	with eval have "s1=s0"
	  by auto
	with conf show ?thesis by simp
      qed
      ultimately show ?thesis ..
    qed
  qed
next
  case (hazard A P Q t)
  show "G,A|\<Turnstile>\<Colon>{ {P \<and>. Not \<circ> type_ok G t} t\<succ> {Q} }"
    by (simp add: ax_valids2_def triple_valid2_def2 type_ok_def) fast
next
  case (Abrupt A P t)
  show "G,A|\<Turnstile>\<Colon>{ {P\<leftarrow>arbitrary3 t \<and>. Not \<circ> normal} t\<succ> {P} }"
  proof (rule validI)
    fix n s0 L accC T C v s1 Y Z 
    assume conf_s0: "s0\<Colon>\<preceq>(G, L)"
    assume eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v, s1)"
    assume "(P\<leftarrow>arbitrary3 t \<and>. Not \<circ> normal) Y s0 Z"
    then obtain P: "P (arbitrary3 t) s0 Z" and abrupt_s0: "\<not> normal s0"
      by simp
    from eval abrupt_s0 obtain "s1=s0" and "v=arbitrary3 t"
      by auto
    with P conf_s0
    show "P v s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
      by simp
  qed
next
  case (LVar A P vn)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (\<lambda>s.. P\<leftarrow>In2 (lvar vn s))} LVar vn=\<succ> {P} }"
  proof (rule valid_var_NormalI)
    fix n s0 L accC T C vf s1 Y Z
    assume conf_s0: "s0\<Colon>\<preceq>(G, L)"
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>LVar vn\<Colon>=T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>LVar vn\<rangle>\<^sub>v\<guillemotright> C"
    assume eval: "G\<turnstile>s0 \<midarrow>LVar vn=\<succ>vf\<midarrow>n\<rightarrow> s1" 
    assume P: "(Normal (\<lambda>s.. P\<leftarrow>In2 (lvar vn s))) Y s0 Z"
    show "P (In2 vf) s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof 
      from eval normal_s0 obtain "s1=s0" "vf=lvar vn (store s0)"
	by (fastsimp elim: evaln_elim_cases)
      with P show "P (In2 vf) s1 Z"
	by simp
    next
      from eval wt da conf_s0 wf
      show "s1\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
    qed
  qed
next
  case (FVar A statDeclC P Q R accC e fn stat)
  have valid_init: "G,A|\<Turnstile>\<Colon>{ {Normal P} .Init statDeclC. {Q} }" .
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Q} e-\<succ> {\<lambda>Val:a:. fvar statDeclC stat fn a ..; R} }" .
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} {accC,statDeclC,stat}e..fn=\<succ> {R} }"
  proof (rule valid_var_NormalI)
    fix n s0 L accC' T V vf s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC',lcl=L\<rparr>\<turnstile>{accC,statDeclC,stat}e..fn\<Colon>=T"
    assume da: "\<lparr>prg=G,cls=accC',lcl=L\<rparr>
                  \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>{accC,statDeclC,stat}e..fn\<rangle>\<^sub>v\<guillemotright> V"
    assume eval: "G\<turnstile>s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>vf\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>vf\<rfloor>\<^sub>v s3 Z \<and> s3\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain statC f where
        wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
        accfield: "accfield G accC statC fn = Some (statDeclC,f)" and
	eq_accC: "accC=accC'" and
        stat: "stat=is_static f" and
	T: "T=(type f)"
	by (cases) (auto simp add: member_is_static_simp)
      from da eq_accC
      have da_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> V"
	by cases simp
      from eval obtain a s1 s2 s2' where
	eval_init: "G\<turnstile>s0 \<midarrow>Init statDeclC\<midarrow>n\<rightarrow> s1" and 
        eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s2" and 
	fvar: "(vf,s2')=fvar statDeclC stat fn a s2" and
	s3: "s3 = check_field_access G accC statDeclC fn stat a s2'"
	using normal_s0 by (fastsimp elim: evaln_elim_cases) 
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
                    \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>Init statDeclC\<rangle>\<^sub>s\<guillemotright> I"
	by (auto intro: da_Init [simplified] assigned.select_convs)
      from valid_init P valid_A conf_s0 eval_init wt_init da_init
      obtain Q: "Q \<diamondsuit> s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G, L)"
	by (rule validE)
      obtain 
	R: "R \<lfloor>vf\<rfloor>\<^sub>v s2' Z" and 
        conf_s2: "s2\<Colon>\<preceq>(G, L)" and
	conf_a: "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC"
      proof (cases "normal s1")
	case True
	obtain V' where 
	  da_e':
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile>dom (locals (store s1))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> V'"
	proof -
	  from eval_init 
	  have "(dom (locals (store s0))) \<subseteq> (dom (locals (store s1)))"
	    by (rule dom_locals_evaln_mono_elim)
	  with da_e show ?thesis
	    by (rule da_weakenE)
	qed
	with valid_e Q valid_A conf_s1 eval_e wt_e
	obtain "R \<lfloor>vf\<rfloor>\<^sub>v s2' Z" and "s2\<Colon>\<preceq>(G, L)"
	  by (rule validE) (simp add: fvar [symmetric])
	moreover
	from eval_e wt_e da_e' conf_s1 wf
	have "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC"
	  by (rule evaln_type_sound [elim_format]) simp
	ultimately show ?thesis ..
      next
	case False
	with valid_e Q valid_A conf_s1 eval_e
	obtain  "R \<lfloor>vf\<rfloor>\<^sub>v s2' Z" and "s2\<Colon>\<preceq>(G, L)"
	  by (cases rule: validE) (simp add: fvar [symmetric])+
	moreover from False eval_e have "\<not> normal s2"
	  by auto
	hence "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC"
	  by auto
	ultimately show ?thesis ..
      qed
      from accfield wt_e eval_init eval_e conf_s2 conf_a fvar stat s3 wf
      have eq_s3_s2': "s3=s2'"  
	using normal_s0 by (auto dest!: error_free_field_access evaln_eval)
      moreover
      from eval wt da conf_s0 wf
      have "s3\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis using Q by simp
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)   
  case (AVar A P Q R e1 e2)
  have valid_e1: "G,A|\<Turnstile>\<Colon>{ {Normal P} e1-\<succ> {Q} }" .
  have valid_e2: "\<And> a. G,A|\<Turnstile>\<Colon>{ {Q\<leftarrow>In1 a} e2-\<succ> {\<lambda>Val:i:. avar G i a ..; R} }"
    using AVar.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} e1.[e2]=\<succ> {R} }"
  proof (rule valid_var_NormalI)
    fix n s0 L accC T V vf s2' Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e1.[e2]\<Colon>=T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e1.[e2]\<rangle>\<^sub>v\<guillemotright> V"
    assume eval: "G\<turnstile>s0 \<midarrow>e1.[e2]=\<succ>vf\<midarrow>n\<rightarrow> s2'"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>vf\<rfloor>\<^sub>v s2' Z \<and> s2'\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain 
	wt_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e1\<Colon>-T.[]" and
        wt_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e2\<Colon>-PrimT Integer" 
	by (rule wt_elim_cases) simp
      from da obtain E1 where
	da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile>dom (locals (store s0))\<guillemotright>\<langle>e1\<rangle>\<^sub>e\<guillemotright> E1" and
	da_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm E1 \<guillemotright>\<langle>e2\<rangle>\<^sub>e\<guillemotright> V"
	by (rule da_elim_cases) simp
      from eval obtain s1 a i s2 where
	eval_e1: "G\<turnstile>s0 \<midarrow>e1-\<succ>a\<midarrow>n\<rightarrow> s1" and
	eval_e2: "G\<turnstile>s1 \<midarrow>e2-\<succ>i\<midarrow>n\<rightarrow> s2" and
	avar: "avar G i a s2 =(vf, s2')"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e1 P valid_A conf_s0 eval_e1 wt_e1 da_e1
      obtain Q: "Q \<lfloor>a\<rfloor>\<^sub>e s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G, L)"
	by (rule validE)
      from Q have Q': "\<And> v. (Q\<leftarrow>In1 a) v s1 Z"
	by simp
      have "R \<lfloor>vf\<rfloor>\<^sub>v s2' Z"
      proof (cases "normal s1")
	case True
	obtain V' where 
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile>dom (locals (store s1))\<guillemotright>\<langle>e2\<rangle>\<^sub>e\<guillemotright> V'"
	proof -
	  from eval_e1  wt_e1 da_e1 wf True
	  have "nrm E1 \<subseteq> dom (locals (store s1))"
	    by (cases rule: da_good_approx_evalnE) rules
	  with da_e2 show ?thesis
	    by (rule da_weakenE)
	qed
	with valid_e2 Q' valid_A conf_s1 eval_e2 wt_e2 
	show ?thesis
	  by (rule validE) (simp add: avar)
      next
	case False
	with valid_e2 Q' valid_A conf_s1 eval_e2
	show ?thesis
	  by (cases rule: validE) (simp add: avar)+
      qed
      moreover
      from eval wt da conf_s0 wf
      have "s2'\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (NewC A C P Q)
  have valid_init: "G,A|\<Turnstile>\<Colon>{ {Normal P} .Init C. {Alloc G (CInst C) Q} }".
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} NewC C-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>NewC C\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>NewC C\<rangle>\<^sub>e\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>NewC C-\<succ>v\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<lfloor>v\<rfloor>\<^sub>e s2 Z \<and> s2\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain is_cls_C: "is_class G C" 
	by (rule wt_elim_cases) (auto dest: is_acc_classD)
      hence wt_init: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>Init C\<Colon>\<surd>" 
	by auto
      obtain I where 
	da_init: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>Init C\<rangle>\<^sub>s\<guillemotright> I"
	by (auto intro: da_Init [simplified] assigned.select_convs)
      from eval obtain s1 a where
	eval_init: "G\<turnstile>s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s1" and 
        alloc: "G\<turnstile>s1 \<midarrow>halloc CInst C\<succ>a\<rightarrow> s2" and
	v: "v=Addr a"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_init P valid_A conf_s0 eval_init wt_init da_init
      obtain "(Alloc G (CInst C) Q) \<diamondsuit> s1 Z" 
	by (rule validE)
      with alloc v have "Q \<lfloor>v\<rfloor>\<^sub>e s2 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (NewA A P Q R T e)
  have valid_init: "G,A|\<Turnstile>\<Colon>{ {Normal P} .init_comp_ty T. {Q} }" .
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Q} e-\<succ> {\<lambda>Val:i:. abupd (check_neg i) .; 
                                            Alloc G (Arr T (the_Intg i)) R}}" .
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} New T[e]-\<succ> {R} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC arrT E v s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>New T[e]\<Colon>-arrT"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>New T[e]\<rangle>\<^sub>e\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>New T[e]-\<succ>v\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>v\<rfloor>\<^sub>e s3 Z \<and> s3\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain
	wt_init: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>init_comp_ty T\<Colon>\<surd>" and 
	wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Integer" 
	by (rule wt_elim_cases) (auto intro: wt_init_comp_ty )
      from da obtain
	da_e:"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	by cases simp
      from eval obtain s1 i s2 a where
	eval_init: "G\<turnstile>s0 \<midarrow>init_comp_ty T\<midarrow>n\<rightarrow> s1" and 
        eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>i\<midarrow>n\<rightarrow> s2" and
        alloc: "G\<turnstile>abupd (check_neg i) s2 \<midarrow>halloc Arr T (the_Intg i)\<succ>a\<rightarrow> s3" and
        v: "v=Addr a"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      obtain I where
	da_init:
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>init_comp_ty T\<rangle>\<^sub>s\<guillemotright> I"
      proof (cases "\<exists>C. T = Class C")
	case True
	thus ?thesis
	  by - (rule that, (auto intro: da_Init [simplified] 
                                        assigned.select_convs
                              simp add: init_comp_ty_def))
	 (* simplified: to rewrite \<langle>Init C\<rangle> to In1r (Init C) *)
      next
	case False
	thus ?thesis
	  by - (rule that, (auto intro: da_Skip [simplified] 
                                      assigned.select_convs
                           simp add: init_comp_ty_def))
         (* simplified: to rewrite \<langle>Skip\<rangle> to In1r (Skip) *)
      qed
      with valid_init P valid_A conf_s0 eval_init wt_init 
      obtain Q: "Q \<diamondsuit> s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G, L)"
	by (rule validE)
      obtain E' where
       "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E'"
      proof -
	from eval_init 
	have "dom (locals (store s0)) \<subseteq> dom (locals (store s1))"
	  by (rule dom_locals_evaln_mono_elim)
	with da_e show ?thesis
	  by (rule da_weakenE)
      qed
      with valid_e Q valid_A conf_s1 eval_e wt_e
      have "(\<lambda>Val:i:. abupd (check_neg i) .; 
                      Alloc G (Arr T (the_Intg i)) R) \<lfloor>i\<rfloor>\<^sub>e s2 Z"
	by (rule validE)
      with alloc v have "R \<lfloor>v\<rfloor>\<^sub>e s3 Z"
	by simp
      moreover 
      from eval wt da conf_s0 wf
      have "s3\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Cast A P Q T e)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> 
                 {\<lambda>Val:v:. \<lambda>s.. abupd (raise_if (\<not> G,s\<turnstile>v fits T) ClassCast) .;
                  Q\<leftarrow>In1 v} }" .
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} Cast T e-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC castT E v s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Cast T e\<Colon>-castT"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>Cast T e\<rangle>\<^sub>e\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>Cast T e-\<succ>v\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<lfloor>v\<rfloor>\<^sub>e s2 Z \<and> s2\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain eT where 
	wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" 
	by cases simp
      from da obtain
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	by cases simp
      from eval obtain s1 where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1" and
        s2: "s2 = abupd (raise_if (\<not> G,snd s1\<turnstile>v fits T) ClassCast) s1"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e P valid_A conf_s0 eval_e wt_e da_e
      have "(\<lambda>Val:v:. \<lambda>s.. abupd (raise_if (\<not> G,s\<turnstile>v fits T) ClassCast) .;
                  Q\<leftarrow>In1 v) \<lfloor>v\<rfloor>\<^sub>e s1 Z"
	by (rule validE)
      with s2 have "Q \<lfloor>v\<rfloor>\<^sub>e s2 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Inst A P Q T e)
  assume valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ>
               {\<lambda>Val:v:. \<lambda>s.. Q\<leftarrow>In1 (Bool (v \<noteq> Null \<and> G,s\<turnstile>v fits RefT T))} }"
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} e InstOf T-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC instT E v s1 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e InstOf T\<Colon>-instT"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>e InstOf T\<rangle>\<^sub>e\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>e InstOf T-\<succ>v\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain eT where 
	wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" 
	by cases simp
      from da obtain
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	by cases simp
      from eval obtain a where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s1" and
        v: "v = Bool (a \<noteq> Null \<and> G,store s1\<turnstile>a fits RefT T)"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e P valid_A conf_s0 eval_e wt_e da_e
      have "(\<lambda>Val:v:. \<lambda>s.. Q\<leftarrow>In1 (Bool (v \<noteq> Null \<and> G,s\<turnstile>v fits RefT T))) 
              \<lfloor>a\<rfloor>\<^sub>e s1 Z"
	by (rule validE)
      with v have "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s1\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Lit A P v)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (P\<leftarrow>In1 v)} Lit v-\<succ> {P} }"
  proof (rule valid_expr_NormalI)
    fix n L s0 s1 v'  Y Z
    assume conf_s0: "s0\<Colon>\<preceq>(G, L)"
    assume normal_s0: " normal s0"
    assume eval: "G\<turnstile>s0 \<midarrow>Lit v-\<succ>v'\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal (P\<leftarrow>In1 v)) Y s0 Z"
    show "P \<lfloor>v'\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from eval have "s1=s0" and  "v'=v"
	using normal_s0 by (auto elim: evaln_elim_cases)
      with P conf_s0 show ?thesis by simp
    qed
  qed
next
  case (UnOp A P Q e unop)
  assume valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P}e-\<succ>{\<lambda>Val:v:. Q\<leftarrow>In1 (eval_unop unop v)} }"
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} UnOp unop e-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s1 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>UnOp unop e\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>UnOp unop e\<rangle>\<^sub>e\<guillemotright>E"
    assume eval: "G\<turnstile>s0 \<midarrow>UnOp unop e-\<succ>v\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain eT where 
	wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" 
	by cases simp
      from da obtain
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	by cases simp
      from eval obtain ve where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>ve\<midarrow>n\<rightarrow> s1" and
        v: "v = eval_unop unop ve"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e P valid_A conf_s0 eval_e wt_e da_e
      have "(\<lambda>Val:v:. Q\<leftarrow>In1 (eval_unop unop v)) \<lfloor>ve\<rfloor>\<^sub>e s1 Z"
	by (rule validE)
      with v have "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s1\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
  case (BinOp A P Q R binop e1 e2)
  assume valid_e1: "G,A|\<Turnstile>\<Colon>{ {Normal P} e1-\<succ> {Q} }" 
  have valid_e2: "\<And> v1.  G,A|\<Turnstile>\<Colon>{ {Q\<leftarrow>In1 v1}
              (if need_second_arg binop v1 then In1l e2 else In1r Skip)\<succ>
              {\<lambda>Val:v2:. R\<leftarrow>In1 (eval_binop binop v1 v2)} }"
    using BinOp.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} BinOp binop e1 e2-\<succ> {R} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>BinOp binop e1 e2\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>BinOp binop e1 e2\<rangle>\<^sub>e\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>BinOp binop e1 e2-\<succ>v\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>v\<rfloor>\<^sub>e s2 Z \<and> s2\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain e1T e2T where
        wt_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e1\<Colon>-e1T" and
        wt_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e2\<Colon>-e2T" and
	wt_binop: "wt_binop G binop e1T e2T" 
	by cases simp
      have wt_Skip: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>Skip\<Colon>\<surd>"
	by simp
      (*
      obtain S where
	daSkip: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> dom (locals (store s1)) \<guillemotright>In1r Skip\<guillemotright> S"
	by (auto intro: da_Skip [simplified] assigned.select_convs) *)
      from da obtain E1 where
	da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e1\<rangle>\<^sub>e\<guillemotright> E1"
	by cases simp+
      from eval obtain v1 s1 v2 where
	eval_e1: "G\<turnstile>s0 \<midarrow>e1-\<succ>v1\<midarrow>n\<rightarrow> s1" and
	eval_e2: "G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then \<langle>e2\<rangle>\<^sub>e else \<langle>Skip\<rangle>\<^sub>s)
                        \<succ>\<midarrow>n\<rightarrow> (\<lfloor>v2\<rfloor>\<^sub>e, s2)" and
        v: "v=eval_binop binop v1 v2"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e1 P valid_A conf_s0 eval_e1 wt_e1 da_e1
      obtain Q: "Q \<lfloor>v1\<rfloor>\<^sub>e s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      from Q have Q': "\<And> v. (Q\<leftarrow>In1 v1) v s1 Z"
	by simp
      have "(\<lambda>Val:v2:. R\<leftarrow>In1 (eval_binop binop v1 v2)) \<lfloor>v2\<rfloor>\<^sub>e s2 Z"
      proof (cases "normal s1")
	case True
	from eval_e1 wt_e1 da_e1 conf_s0 wf
	have conf_v1: "G,store s1\<turnstile>v1\<Colon>\<preceq>e1T" 
	  by (rule evaln_type_sound [elim_format]) (insert True,simp)
	from eval_e1 
	have "G\<turnstile>s0 \<midarrow>e1-\<succ>v1\<rightarrow> s1"
	  by (rule evaln_eval)
	from da wt_e1 wt_e2 wt_binop conf_s0 True this conf_v1 wf
	obtain E2 where
	  da_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) 
                   \<guillemotright>(if need_second_arg binop v1 then \<langle>e2\<rangle>\<^sub>e else \<langle>Skip\<rangle>\<^sub>s)\<guillemotright> E2"
	  by (rule da_e2_BinOp [elim_format]) rules
	from wt_e2 wt_Skip obtain T2 
	  where "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile>(if need_second_arg binop v1 then \<langle>e2\<rangle>\<^sub>e else \<langle>Skip\<rangle>\<^sub>s)\<Colon>T2"
	  by (cases "need_second_arg binop v1") auto
	note ve=validE [OF valid_e2,OF  Q' valid_A conf_s1 eval_e2 this da_e2]
	(* chaining Q', without extra OF causes unification error *)
	thus ?thesis
	  by (rule ve)
      next
	case False
	note ve=validE [OF valid_e2,OF Q' valid_A conf_s1 eval_e2]
	with False show ?thesis
	  by rules
      qed
      with v have "R \<lfloor>v\<rfloor>\<^sub>e s2 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Super A P)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (\<lambda>s.. P\<leftarrow>In1 (val_this s))} Super-\<succ> {P} }"
  proof (rule valid_expr_NormalI)
    fix n L s0 s1 v  Y Z
    assume conf_s0: "s0\<Colon>\<preceq>(G, L)"
    assume normal_s0: " normal s0"
    assume eval: "G\<turnstile>s0 \<midarrow>Super-\<succ>v\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal (\<lambda>s.. P\<leftarrow>In1 (val_this s))) Y s0 Z"
    show "P \<lfloor>v\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from eval have "s1=s0" and  "v=val_this (store s0)"
	using normal_s0 by (auto elim: evaln_elim_cases)
      with P conf_s0 show ?thesis by simp
    qed
  qed
next
  case (Acc A P Q var)
  have valid_var: "G,A|\<Turnstile>\<Colon>{ {Normal P} var=\<succ> {\<lambda>Var:(v, f):. Q\<leftarrow>In1 v} }" .
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} Acc var-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s1 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Acc var\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>Acc var\<rangle>\<^sub>e\<guillemotright>E"
    assume eval: "G\<turnstile>s0 \<midarrow>Acc var-\<succ>v\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain 
	wt_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>var\<Colon>=T" 
	by cases simp
      from da obtain V where 
	da_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>var\<rangle>\<^sub>v\<guillemotright> V"
	by (cases "\<exists> n. var=LVar n") (insert da.LVar,auto elim!: da_elim_cases)
      from eval obtain w upd where
	eval_var: "G\<turnstile>s0 \<midarrow>var=\<succ>(v, upd)\<midarrow>n\<rightarrow> s1"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_var P valid_A conf_s0 eval_var wt_var da_var
      have "(\<lambda>Var:(v, f):. Q\<leftarrow>In1 v) \<lfloor>(v, upd)\<rfloor>\<^sub>v s1 Z"
	by (rule validE)
      then have "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s1\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Ass A P Q R e var)
  have valid_var: "G,A|\<Turnstile>\<Colon>{ {Normal P} var=\<succ> {Q} }" .
  have valid_e: "\<And> vf. 
                  G,A|\<Turnstile>\<Colon>{ {Q\<leftarrow>In2 vf} e-\<succ> {\<lambda>Val:v:. assign (snd vf) v .; R} }"
    using Ass.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} var:=e-\<succ> {R} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>var:=e\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>var:=e\<rangle>\<^sub>e\<guillemotright>E"
    assume eval: "G\<turnstile>s0 \<midarrow>var:=e-\<succ>v\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>v\<rfloor>\<^sub>e s3 Z \<and> s3\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain varT  where
	wt_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>var\<Colon>=varT" and
	wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-T" 
	by cases simp
      from eval obtain w upd s1 s2 where
	eval_var: "G\<turnstile>s0 \<midarrow>var=\<succ>(w, upd)\<midarrow>n\<rightarrow> s1" and
        eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s2" and
	s3: "s3=assign upd v s2"
	using normal_s0 by (auto elim: evaln_elim_cases)
      have "R \<lfloor>v\<rfloor>\<^sub>e s3 Z"
      proof (cases "\<exists> vn. var = LVar vn")
	case False
	with da obtain V where
	  da_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                      \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>var\<rangle>\<^sub>v\<guillemotright> V" and
	  da_e:   "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> nrm V \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	  by cases simp+
	from valid_var P valid_A conf_s0 eval_var wt_var da_var
	obtain Q: "Q \<lfloor>(w,upd)\<rfloor>\<^sub>v s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"  
	  by (rule validE) 
	hence Q': "\<And> v. (Q\<leftarrow>In2 (w,upd)) v s1 Z"
	  by simp
	have "(\<lambda>Val:v:. assign (snd (w,upd)) v .; R) \<lfloor>v\<rfloor>\<^sub>e s2 Z"
	proof (cases "normal s1")
	  case True
	  obtain E' where 
	    da_e': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E'"
	  proof -
	    from eval_var wt_var da_var wf True
	    have "nrm V \<subseteq>  dom (locals (store s1))"
	      by (cases rule: da_good_approx_evalnE) rules
	    with da_e show ?thesis
	      by (rule da_weakenE) 
	  qed
	  note ve=validE [OF valid_e,OF Q' valid_A conf_s1 eval_e wt_e da_e']
	  show ?thesis
	    by (rule ve)
	next
	  case False
	  note ve=validE [OF valid_e,OF Q' valid_A conf_s1 eval_e]
	  with False show ?thesis
	    by rules
	qed
	with s3 show "R \<lfloor>v\<rfloor>\<^sub>e s3 Z"
	  by simp
      next
	case True
	then obtain vn where 
	  vn: "var = LVar vn" 
	  by auto
	with da obtain E where
	    da_e:   "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	  by cases simp+
	from da.LVar vn obtain  V where
	  da_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                      \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>var\<rangle>\<^sub>v\<guillemotright> V"
	  by auto
	from valid_var P valid_A conf_s0 eval_var wt_var da_var
	obtain Q: "Q \<lfloor>(w,upd)\<rfloor>\<^sub>v s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"  
	  by (rule validE) 
	hence Q': "\<And> v. (Q\<leftarrow>In2 (w,upd)) v s1 Z"
	  by simp
	have "(\<lambda>Val:v:. assign (snd (w,upd)) v .; R) \<lfloor>v\<rfloor>\<^sub>e s2 Z"
	proof (cases "normal s1")
	  case True
	  obtain E' where
	    da_e': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                       \<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E'"
	  proof -
	    from eval_var
	    have "dom (locals (store s0)) \<subseteq> dom (locals (store (s1)))"
	      by (rule dom_locals_evaln_mono_elim)
	    with da_e show ?thesis
	      by (rule da_weakenE)
	  qed
	  note ve=validE [OF valid_e,OF Q' valid_A conf_s1 eval_e wt_e da_e']
	  show ?thesis
	    by (rule ve)
	next
	  case False
	  note ve=validE [OF valid_e,OF Q' valid_A conf_s1 eval_e]
	  with False show ?thesis
	    by rules
	qed
	with s3 show "R \<lfloor>v\<rfloor>\<^sub>e s3 Z"
	  by simp
      qed
      moreover
      from eval wt da conf_s0 wf
      have "s3\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Cond A P P' Q e0 e1 e2)
  have valid_e0: "G,A|\<Turnstile>\<Colon>{ {Normal P} e0-\<succ> {P'} }" .
  have valid_then_else:"\<And> b.  G,A|\<Turnstile>\<Colon>{ {P'\<leftarrow>=b} (if b then e1 else e2)-\<succ> {Q} }"
    using Cond.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} e0 ? e1 : e2-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e0 ? e1 : e2\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>e0 ? e1:e2\<rangle>\<^sub>e\<guillemotright>E"
    assume eval: "G\<turnstile>s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<lfloor>v\<rfloor>\<^sub>e s2 Z \<and> s2\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain T1 T2 where
	wt_e0: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e0\<Colon>-PrimT Boolean" and
	wt_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e1\<Colon>-T1" and
	wt_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e2\<Colon>-T2" 
	by cases simp
      from da obtain E0 E1 E2 where
        da_e0: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e0\<rangle>\<^sub>e\<guillemotright> E0" and
        da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                 \<turnstile>(dom (locals (store s0)) \<union> assigns_if True e0)\<guillemotright>\<langle>e1\<rangle>\<^sub>e\<guillemotright> E1" and
        da_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                 \<turnstile>(dom (locals (store s0)) \<union> assigns_if False e0)\<guillemotright>\<langle>e2\<rangle>\<^sub>e\<guillemotright> E2"
	by cases simp+
      from eval obtain b s1 where
	eval_e0: "G\<turnstile>s0 \<midarrow>e0-\<succ>b\<midarrow>n\<rightarrow> s1" and
        eval_then_else: "G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n\<rightarrow> s2"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e0 P valid_A conf_s0 eval_e0 wt_e0 da_e0
      obtain "P' \<lfloor>b\<rfloor>\<^sub>e s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"  
	by (rule validE)
      hence P': "\<And> v. (P'\<leftarrow>=(the_Bool b)) v s1 Z"
	by (cases "normal s1") auto
      have "Q \<lfloor>v\<rfloor>\<^sub>e s2 Z"
      proof (cases "normal s1")
	case True
	note normal_s1=this
	from wt_e1 wt_e2 obtain T' where
	  wt_then_else: 
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>(if the_Bool b then e1 else e2)\<Colon>-T'"
	  by (cases "the_Bool b") simp+
	have s0_s1: "dom (locals (store s0)) 
                      \<union> assigns_if (the_Bool b) e0 \<subseteq> dom (locals (store s1))"
	proof -
	  from eval_e0 
	  have eval_e0': "G\<turnstile>s0 \<midarrow>e0-\<succ>b\<rightarrow> s1"
	    by (rule evaln_eval)
	  hence
	    "dom (locals (store s0)) \<subseteq> dom (locals (store s1))"
	    by (rule dom_locals_eval_mono_elim)
          moreover
	  from eval_e0' True wt_e0 
	  have "assigns_if (the_Bool b) e0 \<subseteq> dom (locals (store s1))"
	    by (rule assigns_if_good_approx') 
	  ultimately show ?thesis by (rule Un_least)
	qed
	obtain E' where
	  da_then_else:
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
              \<turnstile>dom (locals (store s1))\<guillemotright>\<langle>if the_Bool b then e1 else e2\<rangle>\<^sub>e\<guillemotright> E'"
	proof (cases "the_Bool b")
	  case True
	  with that da_e1 s0_s1 show ?thesis
	    by simp (erule da_weakenE,auto)
	next
	  case False
	  with that da_e2 s0_s1 show ?thesis
	    by simp (erule da_weakenE,auto)
	qed
	with valid_then_else P' valid_A conf_s1 eval_then_else wt_then_else
	show ?thesis
	  by (rule validE)
      next
	case False
	with valid_then_else P' valid_A conf_s1 eval_then_else
	show ?thesis
	  by (cases rule: validE) rules+
      qed
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
  case (Call A P Q R S accC' args e mn mode pTs' statT)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> {Q} }" .
  have valid_args: "\<And> a. G,A|\<Turnstile>\<Colon>{ {Q\<leftarrow>In1 a} args\<doteq>\<succ> {R a} }"
    using Call.hyps by simp
  have valid_methd: "\<And> a vs invC declC l.
        G,A|\<Turnstile>\<Colon>{ {R a\<leftarrow>In3 vs \<and>.
                 (\<lambda>s. declC =
                    invocation_declclass G mode (store s) a statT
                     \<lparr>name = mn, parTs = pTs'\<rparr> \<and>
                    invC = invocation_class mode (store s) a statT \<and>
                    l = locals (store s)) ;.
                 init_lvars G declC \<lparr>name = mn, parTs = pTs'\<rparr> mode a vs \<and>.
                 (\<lambda>s. normal s \<longrightarrow> G\<turnstile>mode\<rightarrow>invC\<preceq>statT)}
            Methd declC \<lparr>name=mn,parTs=pTs'\<rparr>-\<succ> {set_lvars l .; S} }"
    using Call.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} {accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ> {S} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s5 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>{accC',statT,mode}e\<cdot>mn( {pTs'}args)\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))
                   \<guillemotright>\<langle>{accC',statT,mode}e\<cdot>mn( {pTs'}args)\<rangle>\<^sub>e\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ>v\<midarrow>n\<rightarrow> s5"
    assume P: "(Normal P) Y s0 Z"
    show "S \<lfloor>v\<rfloor>\<^sub>e s5 Z \<and> s5\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain pTs statDeclT statM where
                 wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT" and
              wt_args: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>args\<Colon>\<doteq>pTs" and
                statM: "max_spec G accC statT \<lparr>name=mn,parTs=pTs\<rparr> 
                         = {((statDeclT,statM),pTs')}" and
                 mode: "mode = invmode statM e" and
                    T: "T =(resTy statM)" and
        eq_accC_accC': "accC=accC'"
	by cases fastsimp+
      from da obtain C where
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s0)))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> C" and
	da_args: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm C \<guillemotright>\<langle>args\<rangle>\<^sub>l\<guillemotright> E" 
	by cases simp
      from eval eq_accC_accC' obtain a s1 vs s2 s3 s3' s4 invDeclC where
	evaln_e: "G\<turnstile>s0 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s1" and
        evaln_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2" and
	invDeclC: "invDeclC = invocation_declclass 
                G mode (store s2) a statT \<lparr>name=mn,parTs=pTs'\<rparr>" and
        s3: "s3 = init_lvars G invDeclC \<lparr>name=mn,parTs=pTs'\<rparr> mode a vs s2" and
        check: "s3' = check_method_access G 
                           accC' statT mode \<lparr>name = mn, parTs = pTs'\<rparr> a s3" and
	evaln_methd:
           "G\<turnstile>s3' \<midarrow>Methd invDeclC  \<lparr>name=mn,parTs=pTs'\<rparr>-\<succ>v\<midarrow>n\<rightarrow> s4" and
        s5: "s5=(set_lvars (locals (store s2))) s4"
	using normal_s0 by (auto elim: evaln_elim_cases)

      from evaln_e
      have eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>a\<rightarrow> s1"
	by (rule evaln_eval)
      
      from eval_e _ wt_e wf
      have s1_no_return: "abrupt s1 \<noteq> Some (Jump Ret)"
	by (rule eval_expression_no_jump 
                 [where ?Env="\<lparr>prg=G,cls=accC,lcl=L\<rparr>",simplified])
	   (insert normal_s0,auto)

      from valid_e P valid_A conf_s0 evaln_e wt_e da_e
      obtain "Q \<lfloor>a\<rfloor>\<^sub>e s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      hence Q: "\<And> v. (Q\<leftarrow>In1 a) v s1 Z"
	by simp
      obtain 
	R: "(R a) \<lfloor>vs\<rfloor>\<^sub>l s2 Z" and 
	conf_s2: "s2\<Colon>\<preceq>(G,L)" and 
	s2_no_return: "abrupt s2 \<noteq> Some (Jump Ret)"
      proof (cases "normal s1")
	case True
	obtain E' where 
	  da_args':
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>args\<rangle>\<^sub>l\<guillemotright> E'"
	proof -
	  from evaln_e wt_e da_e wf True
	  have "nrm C \<subseteq>  dom (locals (store s1))"
	    by (cases rule: da_good_approx_evalnE) rules
	  with da_args show ?thesis
	    by (rule da_weakenE) 
	qed
	with valid_args Q valid_A conf_s1 evaln_args wt_args 
	obtain "(R a) \<lfloor>vs\<rfloor>\<^sub>l s2 Z" "s2\<Colon>\<preceq>(G,L)" 
	  by (rule validE)
	moreover
	from evaln_args
	have e: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2"
	  by (rule evaln_eval)
	from this s1_no_return wt_args wf
	have "abrupt s2 \<noteq> Some (Jump Ret)"
	  by (rule eval_expression_list_no_jump 
                 [where ?Env="\<lparr>prg=G,cls=accC,lcl=L\<rparr>",simplified])
	ultimately show ?thesis ..
      next
	case False
	with valid_args Q valid_A conf_s1 evaln_args
	obtain "(R a) \<lfloor>vs\<rfloor>\<^sub>l s2 Z" "s2\<Colon>\<preceq>(G,L)" 
	  by (cases rule: validE) rules+
	moreover
	from False evaln_args have "s2=s1"
	  by auto
	with s1_no_return have "abrupt s2 \<noteq> Some (Jump Ret)"
	  by simp
	ultimately show ?thesis ..
      qed

      obtain invC where
	invC: "invC = invocation_class mode (store s2) a statT"
	by simp
      with s3
      have invC': "invC = (invocation_class mode (store s3) a statT)"
	by (cases s2,cases mode) (auto simp add: init_lvars_def2 )
      obtain l where
	l: "l = locals (store s2)"
	by simp

      from eval wt da conf_s0 wf
      have conf_s5: "s5\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      let "PROP ?R" = "\<And> v.
             (R a\<leftarrow>In3 vs \<and>.
                 (\<lambda>s. invDeclC = invocation_declclass G mode (store s) a statT
                                  \<lparr>name = mn, parTs = pTs'\<rparr> \<and>
                       invC = invocation_class mode (store s) a statT \<and>
                          l = locals (store s)) ;.
                  init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> mode a vs \<and>.
                  (\<lambda>s. normal s \<longrightarrow> G\<turnstile>mode\<rightarrow>invC\<preceq>statT)
               ) v s3' Z"
      {
	assume abrupt_s3: "\<not> normal s3"
	have "S \<lfloor>v\<rfloor>\<^sub>e s5 Z"
	proof -
	  from abrupt_s3 check have eq_s3'_s3: "s3'=s3"
	    by (auto simp add: check_method_access_def Let_def)
	  with R s3 invDeclC invC l abrupt_s3
	  have R': "PROP ?R"
	    by auto
	  have conf_s3': "s3'\<Colon>\<preceq>(G, empty)"
	   (* we need an arbirary environment (here empty) that s2' conforms to
              to apply validE *)
	  proof -
	    from s2_no_return s3
	    have "abrupt s3 \<noteq> Some (Jump Ret)"
	      by (cases s2) (auto simp add: init_lvars_def2 split: split_if_asm)
	    moreover
	    obtain abr2 str2 where s2: "s2=(abr2,str2)"
	      by (cases s2) simp
	    from s3 s2 conf_s2 have "(abrupt s3,str2)\<Colon>\<preceq>(G, L)"
	      by (auto simp add: init_lvars_def2 split: split_if_asm)
	    ultimately show ?thesis
	      using s3 s2 eq_s3'_s3
	      apply (simp add: init_lvars_def2)
	      apply (rule conforms_set_locals [OF _ wlconf_empty])
	      by auto
	  qed
	  from valid_methd R' valid_A conf_s3' evaln_methd abrupt_s3 eq_s3'_s3
	  have "(set_lvars l .; S) \<lfloor>v\<rfloor>\<^sub>e s4 Z"
	    by (cases rule: validE) simp+
	  with s5 l show ?thesis
	    by simp
	qed
      } note abrupt_s3_lemma = this

      have "S \<lfloor>v\<rfloor>\<^sub>e s5 Z"
      proof (cases "normal s2")
	case False
	with s3 have abrupt_s3: "\<not> normal s3"
	  by (cases s2) (simp add: init_lvars_def2)
	thus ?thesis
	  by (rule abrupt_s3_lemma)
      next
	case True
	note normal_s2 = this
	with evaln_args 
	have normal_s1: "normal s1"
	  by (rule evaln_no_abrupt)
	obtain E' where 
	  da_args':
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>args\<rangle>\<^sub>l\<guillemotright> E'"
	proof -
	  from evaln_e wt_e da_e wf normal_s1
	  have "nrm C \<subseteq>  dom (locals (store s1))"
	    by (cases rule: da_good_approx_evalnE) rules
	  with da_args show ?thesis
	    by (rule da_weakenE) 
	qed
	from evaln_args
	have eval_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2"
	  by (rule evaln_eval)
	from evaln_e wt_e da_e conf_s0 wf
	have conf_a: "G, store s1\<turnstile>a\<Colon>\<preceq>RefT statT"
	  by (rule evaln_type_sound [elim_format]) (insert normal_s1,simp)
	with normal_s1 normal_s2 eval_args 
	have conf_a_s2: "G, store s2\<turnstile>a\<Colon>\<preceq>RefT statT"
	  by (auto dest: eval_gext intro: conf_gext)
	from evaln_args wt_args da_args' conf_s1 wf
	have conf_args: "list_all2 (conf G (store s2)) vs pTs"
	  by (rule evaln_type_sound [elim_format]) (insert normal_s2,simp)
	from statM 
	obtain
	  statM': "(statDeclT,statM)\<in>mheads G accC statT \<lparr>name=mn,parTs=pTs'\<rparr>" 
	  and
	  pTs_widen: "G\<turnstile>pTs[\<preceq>]pTs'"
	  by (blast dest: max_spec2mheads)
	show ?thesis
	proof (cases "normal s3")
	  case False
	  thus ?thesis
	    by (rule abrupt_s3_lemma)
	next
	  case True
	  note normal_s3 = this
	  with s3 have notNull: "mode = IntVir \<longrightarrow> a \<noteq> Null"
	    by (cases s2) (auto simp add: init_lvars_def2)
	  from conf_s2 conf_a_s2 wf notNull invC
	  have dynT_prop: "G\<turnstile>mode\<rightarrow>invC\<preceq>statT"
	    by (cases s2) (auto intro: DynT_propI)

	  with wt_e statM' invC mode wf 
	  obtain dynM where 
            dynM: "dynlookup G statT invC  \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
            acc_dynM: "G \<turnstile>Methd  \<lparr>name=mn,parTs=pTs'\<rparr> dynM 
                            in invC dyn_accessible_from accC"
	    by (force dest!: call_access_ok)
	  with invC' check eq_accC_accC'
	  have eq_s3'_s3: "s3'=s3"
	    by (auto simp add: check_method_access_def Let_def)
	  
	  with dynT_prop R s3 invDeclC invC l 
	  have R': "PROP ?R"
	    by auto

	  from dynT_prop wf wt_e statM' mode invC invDeclC dynM
	  obtain 
            dynM: "dynlookup G statT invC  \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
	    wf_dynM: "wf_mdecl G invDeclC (\<lparr>name=mn,parTs=pTs'\<rparr>,mthd dynM)" and
	      dynM': "methd G invDeclC \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
            iscls_invDeclC: "is_class G invDeclC" and
	         invDeclC': "invDeclC = declclass dynM" and
	      invC_widen: "G\<turnstile>invC\<preceq>\<^sub>C invDeclC" and
	     resTy_widen: "G\<turnstile>resTy dynM\<preceq>resTy statM" and
	    is_static_eq: "is_static dynM = is_static statM" and
	    involved_classes_prop:
             "(if invmode statM e = IntVir
               then \<forall>statC. statT = ClassT statC \<longrightarrow> G\<turnstile>invC\<preceq>\<^sub>C statC
               else ((\<exists>statC. statT = ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C invDeclC) \<or>
                     (\<forall>statC. statT \<noteq> ClassT statC \<and> invDeclC = Object)) \<and>
                      statDeclT = ClassT invDeclC)"
	    by (cases rule: DynT_mheadsE) simp
	  obtain L' where 
	    L':"L'=(\<lambda> k. 
                    (case k of
                       EName e
                       \<Rightarrow> (case e of 
                             VNam v 
                             \<Rightarrow>(table_of (lcls (mbody (mthd dynM)))
                                (pars (mthd dynM)[\<mapsto>]pTs')) v
                           | Res \<Rightarrow> Some (resTy dynM))
                     | This \<Rightarrow> if is_static statM 
                               then None else Some (Class invDeclC)))"
	    by simp
	  from wf_dynM [THEN wf_mdeclD1, THEN conjunct1] normal_s2 conf_s2 wt_e
            wf eval_args conf_a mode notNull wf_dynM involved_classes_prop
	  have conf_s3: "s3\<Colon>\<preceq>(G,L')"
	    apply - 
               (* FIXME confomrs_init_lvars should be 
                  adjusted to be more directy applicable *)
	    apply (drule conforms_init_lvars [of G invDeclC 
                    "\<lparr>name=mn,parTs=pTs'\<rparr>" dynM "store s2" vs pTs "abrupt s2" 
                    L statT invC a "(statDeclT,statM)" e])
	    apply (rule wf)
	    apply (rule conf_args)
	    apply (simp add: pTs_widen)
	    apply (cases s2,simp)
	    apply (rule dynM')
	    apply (force dest: ty_expr_is_type)
	    apply (rule invC_widen)
	    apply (force intro: conf_gext dest: eval_gext)
	    apply simp
	    apply simp
	    apply (simp add: invC)
	    apply (simp add: invDeclC)
	    apply (simp add: normal_s2)
	    apply (cases s2, simp add: L' init_lvars_def2 s3
	                     cong add: lname.case_cong ename.case_cong)
	    done
	  with eq_s3'_s3 have conf_s3': "s3'\<Colon>\<preceq>(G,L')" by simp
	  from is_static_eq wf_dynM L'
	  obtain mthdT where
	    "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
               \<turnstile>Body invDeclC (stmt (mbody (mthd dynM)))\<Colon>-mthdT" and
	    mthdT_widen: "G\<turnstile>mthdT\<preceq>resTy dynM"
	    by - (drule wf_mdecl_bodyD,
                  auto simp add: callee_lcl_def  
                       cong add: lname.case_cong ename.case_cong)
	  with dynM' iscls_invDeclC invDeclC'
	  have
	    wt_methd:
	    "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
               \<turnstile>(Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)\<Colon>-mthdT"
	    by (auto intro: wt.Methd)
	  obtain M where 
	    da_methd:
	    "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr> 
	       \<turnstile> dom (locals (store s3')) 
                   \<guillemotright>\<langle>Methd invDeclC \<lparr>name=mn,parTs=pTs'\<rparr>\<rangle>\<^sub>e\<guillemotright> M"
	  proof -
	    from wf_dynM
	    obtain M' where
	      da_body: 
	      "\<lparr>prg=G, cls=invDeclC
               ,lcl=callee_lcl invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> (mthd dynM)
               \<rparr> \<turnstile> parameters (mthd dynM) \<guillemotright>\<langle>stmt (mbody (mthd dynM))\<rangle>\<guillemotright> M'" and
              res: "Result \<in> nrm M'"
	      by (rule wf_mdeclE) rules
	    from da_body is_static_eq L' have
	      "\<lparr>prg=G, cls=invDeclC,lcl=L'\<rparr> 
                 \<turnstile> parameters (mthd dynM) \<guillemotright>\<langle>stmt (mbody (mthd dynM))\<rangle>\<guillemotright> M'"
	      by (simp add: callee_lcl_def  
                  cong add: lname.case_cong ename.case_cong)
	    moreover have "parameters (mthd dynM) \<subseteq>  dom (locals (store s3'))"
	    proof -
	      from is_static_eq 
	      have "(invmode (mthd dynM) e) = (invmode statM e)"
		by (simp add: invmode_def)
	      with s3 dynM' is_static_eq normal_s2 mode 
	      have "parameters (mthd dynM) = dom (locals (store s3))"
		using dom_locals_init_lvars 
                  [of "mthd dynM" G invDeclC "\<lparr>name=mn,parTs=pTs'\<rparr>" e a vs s2]
		by simp
	      thus ?thesis using eq_s3'_s3 by simp
	    qed
	    ultimately obtain M2 where
	      da:
	      "\<lparr>prg=G, cls=invDeclC,lcl=L'\<rparr> 
                \<turnstile> dom (locals (store s3')) \<guillemotright>\<langle>stmt (mbody (mthd dynM))\<rangle>\<guillemotright> M2" and
              M2: "nrm M' \<subseteq> nrm M2"
	      by (rule da_weakenE)
	    from res M2 have "Result \<in> nrm M2"
	      by blast
	    moreover from wf_dynM
	    have "jumpNestingOkS {Ret} (stmt (mbody (mthd dynM)))"
	      by (rule wf_mdeclE)
	    ultimately
	    obtain M3 where
	      "\<lparr>prg=G, cls=invDeclC,lcl=L'\<rparr> \<turnstile> dom (locals (store s3')) 
                     \<guillemotright>\<langle>Body (declclass dynM) (stmt (mbody (mthd dynM)))\<rangle>\<guillemotright> M3"
	      using da
	      by (rules intro: da.Body assigned.select_convs)
	    from _ this [simplified]
	    show ?thesis
	      by (rule da.Methd [simplified,elim_format])
	         (auto intro: dynM')
	  qed
	  from valid_methd R' valid_A conf_s3' evaln_methd wt_methd da_methd
	  have "(set_lvars l .; S) \<lfloor>v\<rfloor>\<^sub>e s4 Z"
	    by (cases rule: validE) rules+
	  with s5 l show ?thesis
	    by simp
	qed
      qed
      with conf_s5 show ?thesis by rules
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
  case (Methd A P Q ms)
  have valid_body: "G,A \<union> {{P} Methd-\<succ> {Q} | ms}|\<Turnstile>\<Colon>{{P} body G-\<succ> {Q} | ms}".
  show "G,A|\<Turnstile>\<Colon>{{P} Methd-\<succ> {Q} | ms}"
    by (rule Methd_sound)
next
  case (Body A D P Q R c)
  have valid_init: "G,A|\<Turnstile>\<Colon>{ {Normal P} .Init D. {Q} }".
  have valid_c: "G,A|\<Turnstile>\<Colon>{ {Q} .c. 
              {\<lambda>s.. abupd (absorb Ret) .; R\<leftarrow>In1 (the (locals s Result))} }".
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} Body D c-\<succ> {R} }"
  proof (rule valid_expr_NormalI)
    fix n s0 L accC T E v s4 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Body D c\<Colon>-T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>Body D c\<rangle>\<^sub>e\<guillemotright>E"
    assume eval: "G\<turnstile>s0 \<midarrow>Body D c-\<succ>v\<midarrow>n\<rightarrow> s4"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>v\<rfloor>\<^sub>e s4 Z \<and> s4\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain 
	iscls_D: "is_class G D" and
        wt_init: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Init D\<Colon>\<surd>" and
        wt_c: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>" 
	by cases auto
      obtain I where 
	da_init:"\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>Init D\<rangle>\<^sub>s\<guillemotright> I"
	by (auto intro: da_Init [simplified] assigned.select_convs)
      from da obtain C where
	da_c: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s0)))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright> C" and
	jmpOk: "jumpNestingOkS {Ret} c" 
	by cases simp
      from eval obtain s1 s2 s3 where
	eval_init: "G\<turnstile>s0 \<midarrow>Init D\<midarrow>n\<rightarrow> s1" and
        eval_c: "G\<turnstile>s1 \<midarrow>c\<midarrow>n\<rightarrow> s2" and
	v: "v = the (locals (store s2) Result)" and
        s3: "s3 =(if \<exists>l. abrupt s2 = Some (Jump (Break l)) \<or> 
                         abrupt s2 = Some (Jump (Cont l))
                  then abupd (\<lambda>x. Some (Error CrossMethodJump)) s2 else s2)"and
        s4: "s4 = abupd (absorb Ret) s3"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      obtain C' where 
	da_c': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s1)))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright> C'"
      proof -
	from eval_init 
	have "(dom (locals (store s0))) \<subseteq> (dom (locals (store s1)))"
	  by (rule dom_locals_evaln_mono_elim)
	with da_c show ?thesis by (rule da_weakenE)
      qed
      from valid_init P valid_A conf_s0 eval_init wt_init da_init
      obtain Q: "Q \<diamondsuit> s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      from valid_c Q valid_A conf_s1 eval_c wt_c da_c' 
      have R: "(\<lambda>s.. abupd (absorb Ret) .; R\<leftarrow>In1 (the (locals s Result))) 
                \<diamondsuit> s2 Z"
	by (rule validE)
      have "s3=s2"
      proof -
	from eval_init [THEN evaln_eval] wf
	have s1_no_jmp: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	  by - (rule eval_statement_no_jump [OF _ _ _ wt_init],
                insert normal_s0,auto)
	from eval_c [THEN evaln_eval] _ wt_c wf
	have "\<And> j. abrupt s2 = Some (Jump j) \<Longrightarrow> j=Ret"
	  by (rule jumpNestingOk_evalE) (auto intro: jmpOk simp add: s1_no_jmp)
	moreover note s3
	ultimately show ?thesis 
	  by (force split: split_if)
      qed
      with R v s4 
      have "R \<lfloor>v\<rfloor>\<^sub>e s4 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s4\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Nil A P)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (P\<leftarrow>\<lfloor>[]\<rfloor>\<^sub>l)} []\<doteq>\<succ> {P} }"
  proof (rule valid_expr_list_NormalI)
    fix s0 s1 vs n L Y Z
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume eval: "G\<turnstile>s0 \<midarrow>[]\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal (P\<leftarrow>\<lfloor>[]\<rfloor>\<^sub>l)) Y s0 Z"
    show "P \<lfloor>vs\<rfloor>\<^sub>l s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from eval obtain "vs=[]" "s1=s0"
	using normal_s0 by (auto elim: evaln_elim_cases)
      with P conf_s0 show ?thesis
	by simp
    qed
  qed
next
  case (Cons A P Q R e es)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> {Q} }".
  have valid_es: "\<And> v. G,A|\<Turnstile>\<Colon>{ {Q\<leftarrow>\<lfloor>v\<rfloor>\<^sub>e} es\<doteq>\<succ> {\<lambda>Vals:vs:. R\<leftarrow>\<lfloor>(v # vs)\<rfloor>\<^sub>l} }"
    using Cons.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} e # es\<doteq>\<succ> {R} }"
  proof (rule valid_expr_list_NormalI)
    fix n s0 L accC T E v s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e # es\<Colon>\<doteq>T"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>e # es\<rangle>\<^sub>l\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>e # es\<doteq>\<succ>v\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "R \<lfloor>v\<rfloor>\<^sub>l s2 Z \<and> s2\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain eT esT where
	wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-eT" and
	wt_es: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>es\<Colon>\<doteq>esT"
	by cases simp
      from da obtain E1 where
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s0)))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E1" and
	da_es: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm E1 \<guillemotright>\<langle>es\<rangle>\<^sub>l\<guillemotright> E" 
	by cases simp
      from eval obtain s1 ve vs where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>ve\<midarrow>n\<rightarrow> s1" and
	eval_es: "G\<turnstile>s1 \<midarrow>es\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2" and
	v: "v=ve#vs"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e P valid_A conf_s0 eval_e wt_e da_e 
      obtain Q: "Q \<lfloor>ve\<rfloor>\<^sub>e s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      from Q have Q': "\<And> v. (Q\<leftarrow>\<lfloor>ve\<rfloor>\<^sub>e) v s1 Z"
	by simp
      have "(\<lambda>Vals:vs:. R\<leftarrow>\<lfloor>(ve # vs)\<rfloor>\<^sub>l) \<lfloor>vs\<rfloor>\<^sub>l s2 Z"
      proof (cases "normal s1")
	case True
	obtain E' where 
	  da_es': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>es\<rangle>\<^sub>l\<guillemotright> E'"
	proof -
	  from eval_e wt_e da_e wf True
	  have "nrm E1 \<subseteq> dom (locals (store s1))"
	    by (cases rule: da_good_approx_evalnE) rules
	  with da_es show ?thesis
	    by (rule da_weakenE)
	qed
	from valid_es Q' valid_A conf_s1 eval_es wt_es da_es'
	show ?thesis
	  by (rule validE)
      next
	case False
	with valid_es Q' valid_A conf_s1 eval_es 
	show ?thesis
	  by (cases rule: validE) rules+
      qed
      with v have "R \<lfloor>v\<rfloor>\<^sub>l s2 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Skip A P)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (P\<leftarrow>\<diamondsuit>)} .Skip. {P} }"
  proof (rule valid_stmt_NormalI)
    fix s0 s1 n L Y Z
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume eval: "G\<turnstile>s0 \<midarrow>Skip\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal (P\<leftarrow>\<diamondsuit>)) Y s0 Z"
    show "P \<diamondsuit> s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from eval obtain "s1=s0"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      with P conf_s0 show ?thesis
	by simp
    qed
  qed
next
  case (Expr A P Q e)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> {Q\<leftarrow>\<diamondsuit>} }".
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .Expr e. {Q} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC C s1 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Expr e\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>Expr e\<rangle>\<^sub>s\<guillemotright> C"
    assume eval: "G\<turnstile>s0 \<midarrow>Expr e\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<diamondsuit> s1 Z \<and> s1\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain eT where 
	wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT"
	by cases simp
      from da obtain E where
	da_e: "\<lparr>prg=G,cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright>E"
	by cases simp
      from eval obtain v where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_e P valid_A conf_s0 eval_e wt_e da_e
      obtain Q: "(Q\<leftarrow>\<diamondsuit>) \<lfloor>v\<rfloor>\<^sub>e s1 Z" and "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      thus ?thesis by simp
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
  case (Lab A P Q c l)
  have valid_c: "G,A|\<Turnstile>\<Colon>{ {Normal P} .c. {abupd (absorb l) .; Q} }".
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .l\<bullet> c. {Q} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC C s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>l\<bullet> c\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>l\<bullet> c\<rangle>\<^sub>s\<guillemotright> C"
    assume eval: "G\<turnstile>s0 \<midarrow>l\<bullet> c\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<diamondsuit> s2 Z \<and> s2\<Colon>\<preceq>(G, L)"
    proof -
      from wt obtain 
	wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
	by cases simp
      from da obtain E where
	da_c: "\<lparr>prg=G,cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright>E"
	by cases simp
      from eval obtain s1 where
	eval_c: "G\<turnstile>s0 \<midarrow>c\<midarrow>n\<rightarrow> s1" and
	s2: "s2 = abupd (absorb l) s1"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from valid_c P valid_A conf_s0 eval_c wt_c da_c
      obtain Q: "(abupd (absorb l) .; Q) \<diamondsuit> s1 Z" 
	by (rule validE)
      with s2 have "Q \<diamondsuit> s2 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Comp A P Q R c1 c2)
  have valid_c1: "G,A|\<Turnstile>\<Colon>{ {Normal P} .c1. {Q} }" .
  have valid_c2: "G,A|\<Turnstile>\<Colon>{ {Q} .c2. {R} }" .
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .c1;; c2. {R} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC C s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>(c1;; c2)\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>\<langle>c1;;c2\<rangle>\<^sub>s\<guillemotright>C"
    assume eval: "G\<turnstile>s0 \<midarrow>c1;; c2\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "R \<diamondsuit> s2 Z \<and> s2\<Colon>\<preceq>(G,L)"
    proof -
      from eval  obtain s1 where
	eval_c1: "G\<turnstile>s0 \<midarrow>c1 \<midarrow>n\<rightarrow> s1" and
	eval_c2: "G\<turnstile>s1 \<midarrow>c2 \<midarrow>n\<rightarrow> s2"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from wt obtain 
	wt_c1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
        wt_c2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c2\<Colon>\<surd>"
	by cases simp
      from da obtain C1 C2 where 
	da_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1" and 
	da_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>nrm C1 \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2" 
	by cases simp
      from valid_c1 P valid_A conf_s0 eval_c1 wt_c1 da_c1  
      obtain Q: "Q \<diamondsuit> s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"  
	by (rule validE) 
      have "R \<diamondsuit> s2 Z"
      proof (cases "normal s1")
	case True
	obtain C2' where 
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2'"
	proof -
	  from eval_c1 wt_c1 da_c1 wf True
	  have "nrm C1 \<subseteq> dom (locals (store s1))"
	    by (cases rule: da_good_approx_evalnE) rules
	  with da_c2 show ?thesis
	    by (rule da_weakenE)
	qed
	with valid_c2 Q valid_A conf_s1 eval_c2 wt_c2 
	show ?thesis
	  by (rule validE)
      next
	case False
	from valid_c2 Q valid_A conf_s1 eval_c2 False
	show ?thesis
	  by (cases rule: validE) rules+
      qed
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (If A P P' Q c1 c2 e)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> {P'} }" .
  have valid_then_else: "\<And> b. G,A|\<Turnstile>\<Colon>{ {P'\<leftarrow>=b} .(if b then c1 else c2). {Q} }" 
    using If.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .If(e) c1 Else c2. {Q} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC C s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>If(e) c1 Else c2\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0))\<guillemotright>\<langle>If(e) c1 Else c2\<rangle>\<^sub>s\<guillemotright>C"
    assume eval: "G\<turnstile>s0 \<midarrow>If(e) c1 Else c2\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<diamondsuit> s2 Z \<and> s2\<Colon>\<preceq>(G,L)"
    proof -
      from eval obtain b s1 where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1" and
	eval_then_else: "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<midarrow>n\<rightarrow> s2"
	using normal_s0 by (auto elim: evaln_elim_cases)
      from wt obtain  
	wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
	wt_then_else: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
	by cases (simp split: split_if)
      from da obtain E S where
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E" and
	da_then_else: 
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
             (dom (locals (store s0)) \<union> assigns_if (the_Bool b) e)
               \<guillemotright>\<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s\<guillemotright> S"
	by cases (cases "the_Bool b",auto)
      from valid_e P valid_A conf_s0 eval_e wt_e da_e
      obtain "P' \<lfloor>b\<rfloor>\<^sub>e s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      hence P': "\<And>v. (P'\<leftarrow>=the_Bool b) v s1 Z"
	by (cases "normal s1") auto
      have "Q \<diamondsuit> s2 Z"
      proof (cases "normal s1")
	case True
	have s0_s1: "dom (locals (store s0)) 
                      \<union> assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
	proof -
	  from eval_e 
	  have eval_e': "G\<turnstile>s0 \<midarrow>e-\<succ>b\<rightarrow> s1"
	    by (rule evaln_eval)
	  hence
	    "dom (locals (store s0)) \<subseteq> dom (locals (store s1))"
	    by (rule dom_locals_eval_mono_elim)
          moreover
	  from eval_e' True wt_e
	  have "assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
	    by (rule assigns_if_good_approx') 
	  ultimately show ?thesis by (rule Un_least)
	qed
	with da_then_else
	obtain S' where
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
              \<turnstile>dom (locals (store s1))\<guillemotright>\<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s\<guillemotright> S'"
	  by (rule da_weakenE)
	with valid_then_else P' valid_A conf_s1 eval_then_else wt_then_else
	show ?thesis
	  by (rule validE)
      next
	case False
	with valid_then_else P' valid_A conf_s1 eval_then_else
	show ?thesis
	  by (cases rule: validE) rules+
      qed
      moreover
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G, L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Loop A P P' c e l)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {P} e-\<succ> {P'} }".
  have valid_c: "G,A|\<Turnstile>\<Colon>{ {Normal (P'\<leftarrow>=True)} 
                         .c. 
                         {abupd (absorb (Cont l)) .; P} }" .
  show "G,A|\<Turnstile>\<Colon>{ {P} .l\<bullet> While(e) c. {P'\<leftarrow>=False\<down>=\<diamondsuit>} }"
  proof (rule valid_stmtI)
    fix n s0 L accC C s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume wt: "normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>l\<bullet> While(e) c\<Colon>\<surd>"
    assume da: "normal s0 \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<guillemotright> C"
    assume eval: "G\<turnstile>s0 \<midarrow>l\<bullet> While(e) c\<midarrow>n\<rightarrow> s3"
    assume P: "P Y s0 Z"
    show "(P'\<leftarrow>=False\<down>=\<diamondsuit>) \<diamondsuit> s3 Z \<and> s3\<Colon>\<preceq>(G,L)"
    proof -
        --{* From the given hypothesises @{text valid_e} and @{text valid_c} 
           we can only reach the state after unfolding the loop once, i.e. 
	   @{term "P \<diamondsuit> s2 Z"}, where @{term s2} is the state after executing
           @{term c}. To gain validity of the further execution of while, to
           finally get @{term "(P'\<leftarrow>=False\<down>=\<diamondsuit>) \<diamondsuit> s3 Z"} we have to get 
           a hypothesis about the subsequent unfoldings (the whole loop again),
           too. We can achieve this, by performing induction on the 
           evaluation relation, with all
           the necessary preconditions to apply @{text valid_e} and 
           @{text valid_c} in the goal.
        *}
      {
	fix t s s' v 
	assume "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v, s')"
	hence "\<And> Y' T E. 
                \<lbrakk>t =  \<langle>l\<bullet> While(e) c\<rangle>\<^sub>s; \<forall>t\<in>A. G\<Turnstile>n\<Colon>t; P Y' s Z; s\<Colon>\<preceq>(G, L);
                 normal s \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T; 
                 normal s \<Longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>t\<guillemotright>E
                \<rbrakk>\<Longrightarrow> (P'\<leftarrow>=False\<down>=\<diamondsuit>) v s' Z"
	  (is "PROP ?Hyp n t s v s'")
	proof (induct)
	  case (Loop b c' e' l' n' s0' s1' s2' s3' Y' T E)
	  have while: "(\<langle>l'\<bullet> While(e') c'\<rangle>\<^sub>s::term) = \<langle>l\<bullet> While(e) c\<rangle>\<^sub>s" .
          hence eqs: "l'=l" "e'=e" "c'=c" by simp_all
	  have valid_A: "\<forall>t\<in>A. G\<Turnstile>n'\<Colon>t". 
	  have P: "P Y' (Norm s0') Z".
	  have conf_s0': "Norm s0'\<Colon>\<preceq>(G, L)" .
          have wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>\<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<Colon>T"
	    using Loop.prems eqs by simp
	  have da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>
                    dom (locals (store ((Norm s0')::state)))\<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<guillemotright>E"
	    using Loop.prems eqs by simp
	  have evaln_e: "G\<turnstile>Norm s0' \<midarrow>e-\<succ>b\<midarrow>n'\<rightarrow> s1'" 
	    using Loop.hyps eqs by simp
	  show "(P'\<leftarrow>=False\<down>=\<diamondsuit>) \<diamondsuit> s3' Z"
	  proof -
	    from wt  obtain 
	      wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
              wt_c: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>"
	      by cases (simp add: eqs)
	    from da obtain E S where
	      da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                     \<turnstile> dom (locals (store ((Norm s0')::state))) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E" and
	      da_c: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                     \<turnstile> (dom (locals (store ((Norm s0')::state))) 
                            \<union> assigns_if True e) \<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright> S"
	      by cases (simp add: eqs)
	    from evaln_e 
	    have eval_e: "G\<turnstile>Norm s0' \<midarrow>e-\<succ>b\<rightarrow> s1'"
	      by (rule evaln_eval)
	    from valid_e P valid_A conf_s0' evaln_e wt_e da_e
	    obtain P': "P' \<lfloor>b\<rfloor>\<^sub>e s1' Z" and conf_s1': "s1'\<Colon>\<preceq>(G,L)"
	      by (rule validE)
	    show "(P'\<leftarrow>=False\<down>=\<diamondsuit>) \<diamondsuit> s3' Z"
	    proof (cases "normal s1'")
	      case True
	      note normal_s1'=this
	      show ?thesis
	      proof (cases "the_Bool b")
		case True
		with P' normal_s1' have P'': "(Normal (P'\<leftarrow>=True)) \<lfloor>b\<rfloor>\<^sub>e s1' Z"
		  by auto
		from True Loop.hyps obtain
		  eval_c: "G\<turnstile>s1' \<midarrow>c\<midarrow>n'\<rightarrow> s2'" and 
		  eval_while:  
		     "G\<turnstile>abupd (absorb (Cont l)) s2' \<midarrow>l\<bullet> While(e) c\<midarrow>n'\<rightarrow> s3'"
		  by (simp add: eqs)
		from True Loop.hyps have
		  hyp: "PROP ?Hyp n' \<langle>l\<bullet> While(e) c\<rangle>\<^sub>s 
                          (abupd (absorb (Cont l')) s2') \<diamondsuit> s3'"
		  apply (simp only: True if_True eqs)
		  apply (elim conjE)
		  apply (tactic "smp_tac 3 1")
		  apply fast
		  done
		from eval_e
		have s0'_s1': "dom (locals (store ((Norm s0')::state))) 
                                  \<subseteq> dom (locals (store s1'))"
		  by (rule dom_locals_eval_mono_elim)
		obtain S' where
		  da_c':
		   "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>(dom (locals (store s1')))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright> S'" 
		proof -
		  note s0'_s1'
		  moreover
		  from eval_e normal_s1' wt_e 
		  have "assigns_if True e \<subseteq> dom (locals (store s1'))"
		    by (rule assigns_if_good_approx' [elim_format]) 
                       (simp add: True)
		  ultimately 
		  have "dom (locals (store ((Norm s0')::state)))
                           \<union> assigns_if True e \<subseteq> dom (locals (store s1'))"
		    by (rule Un_least)
		  with da_c show ?thesis
		    by (rule da_weakenE)
		qed
		with valid_c P'' valid_A conf_s1' eval_c wt_c
		obtain "(abupd (absorb (Cont l)) .; P) \<diamondsuit> s2' Z" and 
                  conf_s2': "s2'\<Colon>\<preceq>(G,L)"
		  by (rule validE)
		hence P_s2': "P \<diamondsuit> (abupd (absorb (Cont l)) s2') Z"
		  by simp
		from conf_s2'
		have conf_absorb: "abupd (absorb (Cont l)) s2' \<Colon>\<preceq>(G, L)"
		  by (cases s2') (auto intro: conforms_absorb)
		moreover
		obtain E' where 
		  da_while':
		   "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
		     dom (locals(store (abupd (absorb (Cont l)) s2')))
                      \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<^sub>s\<guillemotright> E'"
		proof -
		  note s0'_s1'
		  also 
		  from eval_c 
		  have "G\<turnstile>s1' \<midarrow>c\<rightarrow> s2'"
		    by (rule evaln_eval)
		  hence "dom (locals (store s1')) \<subseteq> dom (locals (store s2'))"
		    by (rule dom_locals_eval_mono_elim)
		  also 
		  have "\<dots>\<subseteq>dom (locals (store (abupd (absorb (Cont l)) s2')))"
		    by simp
		  finally
		  have "dom (locals (store ((Norm s0')::state))) \<subseteq> \<dots>" .
		  with da show ?thesis
		    by (rule da_weakenE)
		qed
		from valid_A P_s2' conf_absorb wt da_while'
		show "(P'\<leftarrow>=False\<down>=\<diamondsuit>) \<diamondsuit> s3' Z" 
		  using hyp by (simp add: eqs)
	      next
		case False
		with Loop.hyps obtain "s3'=s1'"
		  by simp
		with P' False show ?thesis
		  by auto
	      qed 
	    next
	      case False
	      note abnormal_s1'=this
	      have "s3'=s1'"
	      proof -
		from False obtain abr where abr: "abrupt s1' = Some abr"
		  by (cases s1') auto
		from eval_e _ wt_e wf
		have no_jmp: "\<And> j. abrupt s1' \<noteq> Some (Jump j)"
		  by (rule eval_expression_no_jump 
                       [where ?Env="\<lparr>prg=G,cls=accC,lcl=L\<rparr>",simplified])
		     simp
		show ?thesis
		proof (cases "the_Bool b")
		  case True  
		  with Loop.hyps obtain
		    eval_c: "G\<turnstile>s1' \<midarrow>c\<midarrow>n'\<rightarrow> s2'" and 
		    eval_while:  
		     "G\<turnstile>abupd (absorb (Cont l)) s2' \<midarrow>l\<bullet> While(e) c\<midarrow>n'\<rightarrow> s3'"
		    by (simp add: eqs)
		  from eval_c abr have "s2'=s1'" by auto
		  moreover from calculation no_jmp 
		  have "abupd (absorb (Cont l)) s2'=s2'"
		    by (cases s1') (simp add: absorb_def)
		  ultimately show ?thesis
		    using eval_while abr
		    by auto
		next
		  case False
		  with Loop.hyps show ?thesis by simp
		qed
	      qed
	      with P' False show ?thesis
		by auto
	    qed
	  qed
	next
	  case (Abrupt n' s t' abr Y' T E)
	  have t': "t' = \<langle>l\<bullet> While(e) c\<rangle>\<^sub>s".
	  have conf: "(Some abr, s)\<Colon>\<preceq>(G, L)".
	  have P: "P Y' (Some abr, s) Z".
	  have valid_A: "\<forall>t\<in>A. G\<Turnstile>n'\<Colon>t". 
	  show "(P'\<leftarrow>=False\<down>=\<diamondsuit>) (arbitrary3 t') (Some abr, s) Z"
	  proof -
	    have eval_e: 
	      "G\<turnstile>(Some abr,s) \<midarrow>\<langle>e\<rangle>\<^sub>e\<succ>\<midarrow>n'\<rightarrow> (arbitrary3 \<langle>e\<rangle>\<^sub>e,(Some abr,s))"
	      by auto
	    from valid_e P valid_A conf eval_e 
	    have "P' (arbitrary3 \<langle>e\<rangle>\<^sub>e) (Some abr,s) Z"
	      by (cases rule: validE [where ?P="P"]) simp+
	    with t' show ?thesis
	      by auto
	  qed
	qed (simp_all)
      } note generalized=this
      from eval _ valid_A P conf_s0 wt da
      have "(P'\<leftarrow>=False\<down>=\<diamondsuit>) \<diamondsuit> s3 Z"
	by (rule generalized)  simp_all
      moreover
      have "s3\<Colon>\<preceq>(G, L)"
      proof (cases "normal s0")
	case True
	from eval wt [OF True] da [OF True] conf_s0 wf
	show ?thesis
	  by (rule evaln_type_sound [elim_format]) simp
      next
	case False
	with eval have "s3=s0"
	  by auto
	with conf_s0 show ?thesis 
	  by simp
      qed
      ultimately show ?thesis ..
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
  case (Jmp A P j)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (abupd (\<lambda>a. Some (Jump j)) .; P\<leftarrow>\<diamondsuit>)} .Jmp j. {P} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC C s1 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Jmp j\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0))\<guillemotright>\<langle>Jmp j\<rangle>\<^sub>s\<guillemotright>C"
    assume eval: "G\<turnstile>s0 \<midarrow>Jmp j\<midarrow>n\<rightarrow> s1"
    assume P: "(Normal (abupd (\<lambda>a. Some (Jump j)) .; P\<leftarrow>\<diamondsuit>)) Y s0 Z"
    show "P \<diamondsuit> s1 Z \<and> s1\<Colon>\<preceq>(G,L)"
    proof -
      from eval obtain s where  
	s: "s0=Norm s" "s1=(Some (Jump j), s)" 
	using normal_s0 by (auto elim: evaln_elim_cases)
      with P have "P \<diamondsuit> s1 Z"
	by simp
      moreover 
      from eval wt da conf_s0 wf
      have "s1\<Colon>\<preceq>(G,L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Throw A P Q e)
  have valid_e: "G,A|\<Turnstile>\<Colon>{ {Normal P} e-\<succ> {\<lambda>Val:a:. abupd (throw a) .; Q\<leftarrow>\<diamondsuit>} }".
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .Throw e. {Q} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC C s2 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Throw e\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0))\<guillemotright>\<langle>Throw e\<rangle>\<^sub>s\<guillemotright>C"
    assume eval: "G\<turnstile>s0 \<midarrow>Throw e\<midarrow>n\<rightarrow> s2"
    assume P: "(Normal P) Y s0 Z"
    show "Q \<diamondsuit> s2 Z \<and> s2\<Colon>\<preceq>(G,L)"
    proof -
      from eval obtain s1 a where
	eval_e: "G\<turnstile>s0 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s1" and
	s2: "s2 = abupd (throw a) s1"
	using normal_s0 by (auto elim: evaln_elim_cases)
      from wt obtain T where
	wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-T"
	by cases simp
      from da obtain E where
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E"
	by cases simp
      from valid_e P valid_A conf_s0 eval_e wt_e da_e 
      obtain "(\<lambda>Val:a:. abupd (throw a) .; Q\<leftarrow>\<diamondsuit>) \<lfloor>a\<rfloor>\<^sub>e s1 Z"
	by (rule validE)
      with s2 have "Q \<diamondsuit> s2 Z"
	by simp
      moreover 
      from eval wt da conf_s0 wf
      have "s2\<Colon>\<preceq>(G,L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Try A C P Q R c1 c2 vn)
  have valid_c1: "G,A|\<Turnstile>\<Colon>{ {Normal P} .c1. {SXAlloc G Q} }".
  have valid_c2: "G,A|\<Turnstile>\<Colon>{ {Q \<and>. (\<lambda>s. G,s\<turnstile>catch C) ;. new_xcpt_var vn} 
                           .c2. 
                          {R} }".
  have Q_R: "(Q \<and>. (\<lambda>s. \<not> G,s\<turnstile>catch C)) \<Rightarrow> R" .
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .Try c1 Catch(C vn) c2. {R} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC E s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Try c1 Catch(C vn) c2\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>Try c1 Catch(C vn) c2\<rangle>\<^sub>s\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>Try c1 Catch(C vn) c2\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal P) Y s0 Z"
    show "R \<diamondsuit> s3 Z \<and> s3\<Colon>\<preceq>(G,L)"
    proof -
      from eval obtain s1 s2 where
	eval_c1: "G\<turnstile>s0 \<midarrow>c1\<midarrow>n\<rightarrow> s1" and
        sxalloc: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" and
        s3: "if G,s2\<turnstile>catch C 
                then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>n\<rightarrow> s3 
                else s3 = s2"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from wt obtain
	wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
	wt_c2: "\<lparr>prg=G,cls=accC,lcl=L(VName vn\<mapsto>Class C)\<rparr>\<turnstile>c2\<Colon>\<surd>"
	by cases simp
      from da obtain C1 C2 where
	da_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1" and
	da_c2: "\<lparr>prg=G,cls=accC,lcl=L(VName vn\<mapsto>Class C)\<rparr>
                   \<turnstile> (dom (locals (store s0)) \<union> {VName vn}) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2"
	by cases simp
      from valid_c1 P valid_A conf_s0 eval_c1 wt_c1 da_c1
      obtain sxQ: "(SXAlloc G Q) \<diamondsuit> s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      from sxalloc sxQ
      have Q: "Q \<diamondsuit> s2 Z"
	by auto
      have "R \<diamondsuit> s3 Z"
      proof (cases "\<exists> x. abrupt s1 = Some (Xcpt x)")
	case False
	from sxalloc wf
	have "s2=s1"
	  by (rule sxalloc_type_sound [elim_format])
	     (insert False, auto split: option.splits abrupt.splits )
	with False 
	have no_catch: "\<not>  G,s2\<turnstile>catch C"
	  by (simp add: catch_def)
	moreover
	from no_catch s3
	have "s3=s2"
	  by simp
	ultimately show ?thesis
	  using Q Q_R by simp
      next
	case True
	note exception_s1 = this
	show ?thesis
	proof (cases "G,s2\<turnstile>catch C") 
	  case False
	  with s3
	  have "s3=s2"
	    by simp
	  with False Q Q_R show ?thesis
	    by simp
	next
	  case True
	  with s3 have eval_c2: "G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>n\<rightarrow> s3"
	    by simp
	  from conf_s1 sxalloc wf 
	  have conf_s2: "s2\<Colon>\<preceq>(G, L)" 
	    by (auto dest: sxalloc_type_sound 
                    split: option.splits abrupt.splits)
	  from exception_s1 sxalloc wf
	  obtain a 
	    where xcpt_s2: "abrupt s2 = Some (Xcpt (Loc a))"
	    by (auto dest!: sxalloc_type_sound 
                            split: option.splits abrupt.splits)
	  with True
	  have "G\<turnstile>obj_ty (the (globs (store s2) (Heap a)))\<preceq>Class C"
	    by (cases s2) simp
	  with xcpt_s2 conf_s2 wf
	  have conf_new_xcpt: "new_xcpt_var vn s2 \<Colon>\<preceq>(G, L(VName vn\<mapsto>Class C))"
	    by (auto dest: Try_lemma)
	  obtain C2' where
	    da_c2':
	    "\<lparr>prg=G,cls=accC,lcl=L(VName vn\<mapsto>Class C)\<rparr>
              \<turnstile> (dom (locals (store (new_xcpt_var vn s2)))) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2'"
	  proof -
	    have "(dom (locals (store s0)) \<union> {VName vn}) 
                    \<subseteq> dom (locals (store (new_xcpt_var vn s2)))"
            proof -
	      from eval_c1 
              have "dom (locals (store s0)) 
                      \<subseteq> dom (locals (store s1))"
		by (rule dom_locals_evaln_mono_elim)
              also
              from sxalloc
              have "\<dots> \<subseteq> dom (locals (store s2))"
		by (rule dom_locals_sxalloc_mono)
              also 
              have "\<dots> \<subseteq> dom (locals (store (new_xcpt_var vn s2)))" 
		by (cases s2) (simp add: new_xcpt_var_def, blast) 
              also
              have "{VName vn} \<subseteq> \<dots>"
		by (cases s2) simp
              ultimately show ?thesis
		by (rule Un_least)
            qed
	    with da_c2 show ?thesis
	      by (rule da_weakenE)
	  qed
	  from Q eval_c2 True 
	  have "(Q \<and>. (\<lambda>s. G,s\<turnstile>catch C) ;. new_xcpt_var vn) 
                   \<diamondsuit> (new_xcpt_var vn s2) Z"
	    by auto
	  from valid_c2 this valid_A conf_new_xcpt eval_c2 wt_c2 da_c2'
	  show "R \<diamondsuit> s3 Z"
	    by (rule validE)
	qed
      qed
      moreover 
      from eval wt da conf_s0 wf
      have "s3\<Colon>\<preceq>(G,L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (Fin A P Q R c1 c2)
  have valid_c1: "G,A|\<Turnstile>\<Colon>{ {Normal P} .c1. {Q} }".
  have valid_c2: "\<And> abr. G,A|\<Turnstile>\<Colon>{ {Q \<and>. (\<lambda>s. abr = fst s) ;. abupd (\<lambda>x. None)} 
                                  .c2.
                                  {abupd (abrupt_if (abr \<noteq> None) abr) .; R} }"
    using Fin.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .c1 Finally c2. {R} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC E s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1 Finally c2\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>c1 Finally c2\<rangle>\<^sub>s\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>c1 Finally c2\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal P) Y s0 Z"
    show "R \<diamondsuit> s3 Z \<and> s3\<Colon>\<preceq>(G,L)"
    proof -
      from eval obtain s1 abr1 s2 where
	eval_c1: "G\<turnstile>s0 \<midarrow>c1\<midarrow>n\<rightarrow> (abr1, s1)" and
        eval_c2: "G\<turnstile>Norm s1 \<midarrow>c2\<midarrow>n\<rightarrow> s2" and
        s3: "s3 = (if \<exists>err. abr1 = Some (Error err) 
                      then (abr1, s1)
                      else abupd (abrupt_if (abr1 \<noteq> None) abr1) s2)"
	using normal_s0 by (fastsimp elim: evaln_elim_cases)
      from wt obtain
	wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
	wt_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c2\<Colon>\<surd>"
	by cases simp
      from da obtain C1 C2 where
	da_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1" and
	da_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2"
	by cases simp
      from valid_c1 P valid_A conf_s0 eval_c1 wt_c1 da_c1
      obtain Q: "Q \<diamondsuit> (abr1,s1) Z" and conf_s1: "(abr1,s1)\<Colon>\<preceq>(G,L)" 
	by (rule validE)
      from Q 
      have Q': "(Q \<and>. (\<lambda>s. abr1 = fst s) ;. abupd (\<lambda>x. None)) \<diamondsuit> (Norm s1) Z"
	by auto
      from eval_c1 wt_c1 da_c1 conf_s0 wf
      have  "error_free (abr1,s1)"
	by (rule evaln_type_sound  [elim_format]) (insert normal_s0,simp)
      with s3 have s3': "s3 = abupd (abrupt_if (abr1 \<noteq> None) abr1) s2"
	by (simp add: error_free_def)
      from conf_s1 
      have conf_Norm_s1: "Norm s1\<Colon>\<preceq>(G,L)"
	by (rule conforms_NormI)
      obtain C2' where 
	da_c2': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> dom (locals (store ((Norm s1)::state))) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2'"
      proof -
	from eval_c1 
	have "dom (locals (store s0)) \<subseteq> dom (locals (store (abr1,s1)))"
          by (rule dom_locals_evaln_mono_elim)
	hence "dom (locals (store s0)) 
                 \<subseteq> dom (locals (store ((Norm s1)::state)))"
	  by simp
	with da_c2 show ?thesis
	  by (rule da_weakenE)
      qed
      from valid_c2 Q' valid_A conf_Norm_s1 eval_c2 wt_c2 da_c2'
      have "(abupd (abrupt_if (abr1 \<noteq> None) abr1) .; R) \<diamondsuit> s2 Z"
	by (rule validE)
      with s3' have "R \<diamondsuit> s3 Z"
	by simp
      moreover
      from eval wt da conf_s0 wf
      have "s3\<Colon>\<preceq>(G,L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
  case (Done A C P)
  show "G,A|\<Turnstile>\<Colon>{ {Normal (P\<leftarrow>\<diamondsuit> \<and>. initd C)} .Init C. {P} }" 
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC E s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Init C\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>Init C\<rangle>\<^sub>s\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal (P\<leftarrow>\<diamondsuit> \<and>. initd C)) Y s0 Z"
    show "P \<diamondsuit> s3 Z \<and> s3\<Colon>\<preceq>(G,L)"
    proof -
      from P have inited: "inited C (globs (store s0))"
	by simp
      with eval have "s3=s0"
	using normal_s0 by (auto elim: evaln_elim_cases)
      with P conf_s0 show ?thesis
	by simp
    qed
  qed
next
  case (Init A C P Q R c)
  have c: "the (class G C) = c".
  have valid_super: 
        "G,A|\<Turnstile>\<Colon>{ {Normal (P \<and>. Not \<circ> initd C ;. supd (init_class_obj G C))}
                 .(if C = Object then Skip else Init (super c)). 
                 {Q} }".
  have valid_init: 
        "\<And> l.  G,A|\<Turnstile>\<Colon>{ {Q \<and>. (\<lambda>s. l = locals (snd s)) ;. set_lvars empty} 
                        .init c.
                        {set_lvars l .; R} }"
    using Init.hyps by simp
  show "G,A|\<Turnstile>\<Colon>{ {Normal (P \<and>. Not \<circ> initd C)} .Init C. {R} }"
  proof (rule valid_stmt_NormalI)
    fix n s0 L accC E s3 Y Z
    assume valid_A: "\<forall>t\<in>A. G\<Turnstile>n\<Colon>t"
    assume conf_s0:  "s0\<Colon>\<preceq>(G,L)"  
    assume normal_s0: "normal s0"
    assume wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>Init C\<Colon>\<surd>"
    assume da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                    \<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>Init C\<rangle>\<^sub>s\<guillemotright> E"
    assume eval: "G\<turnstile>s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s3"
    assume P: "(Normal (P \<and>. Not \<circ> initd C)) Y s0 Z"
    show "R \<diamondsuit> s3 Z \<and> s3\<Colon>\<preceq>(G,L)"
    proof -
      from P have not_inited: "\<not> inited C (globs (store s0))" by simp
      with eval c obtain s1 s2 where
	eval_super: 
	"G\<turnstile>Norm ((init_class_obj G C) (store s0)) 
           \<midarrow>(if C = Object then Skip else Init (super c))\<midarrow>n\<rightarrow> s1" and
	eval_init: "G\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<midarrow>n\<rightarrow> s2" and
        s3: "s3 = (set_lvars (locals (store s1))) s2"
	using normal_s0 by (auto elim!: evaln_elim_cases)
      from wt c have
	cls_C: "class G C = Some c"
	by cases auto
      from wf cls_C have
	wt_super: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                         \<turnstile>(if C = Object then Skip else Init (super c))\<Colon>\<surd>"
	by (cases "C=Object")
           (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD)
      obtain S where
	da_super:
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>
          \<turnstile> dom (locals (store ((Norm 
                            ((init_class_obj G C) (store s0)))::state))) 
               \<guillemotright>\<langle>if C = Object then Skip else Init (super c)\<rangle>\<^sub>s\<guillemotright> S"
      proof (cases "C=Object")
	case True 
	with da_Skip show ?thesis
	  using that by (auto intro: assigned.select_convs)
      next
	case False 
	with da_Init show ?thesis
	  by - (rule that, auto intro: assigned.select_convs)
      qed
      from normal_s0 conf_s0 wf cls_C not_inited
      have conf_init_cls: "(Norm ((init_class_obj G C) (store s0)))\<Colon>\<preceq>(G, L)"
	by (auto intro: conforms_init_class_obj)	
      from P 
      have P': "(Normal (P \<and>. Not \<circ> initd C ;. supd (init_class_obj G C)))
                   Y (Norm ((init_class_obj G C) (store s0))) Z"
	by auto

      from valid_super P' valid_A conf_init_cls eval_super wt_super da_super
      obtain Q: "Q \<diamondsuit> s1 Z" and conf_s1: "s1\<Colon>\<preceq>(G,L)"
	by (rule validE)
      
      from cls_C wf have wt_init: "\<lparr>prg=G, cls=C,lcl=empty\<rparr>\<turnstile>(init c)\<Colon>\<surd>"
	by (rule wf_prog_cdecl [THEN wf_cdecl_wt_init])
      from cls_C wf obtain I where 
	"\<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile> {} \<guillemotright>\<langle>init c\<rangle>\<^sub>s\<guillemotright> I"
	by (rule wf_prog_cdecl [THEN wf_cdeclE,simplified]) blast
       (*  simplified: to rewrite \<langle>init c\<rangle> to In1r (init c) *) 
      then obtain I' where
	da_init:
	"\<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile>dom (locals (store ((set_lvars empty) s1))) 
            \<guillemotright>\<langle>init c\<rangle>\<^sub>s\<guillemotright> I'"
	by (rule da_weakenE) simp
      have conf_s1_empty: "(set_lvars empty) s1\<Colon>\<preceq>(G, empty)"
      proof -
	from eval_super have
	  "G\<turnstile>Norm ((init_class_obj G C) (store s0)) 
             \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1"
	  by (rule evaln_eval)
	from this wt_super wf
	have s1_no_ret: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	  by - (rule eval_statement_no_jump 
                 [where ?Env="\<lparr>prg=G,cls=accC,lcl=L\<rparr>"], auto split: split_if)
        with conf_s1
	show ?thesis
	  by (cases s1) (auto intro: conforms_set_locals)
      qed
      
      obtain l where l: "l = locals (store s1)"
	by simp
      with Q 
      have Q': "(Q \<and>. (\<lambda>s. l = locals (snd s)) ;. set_lvars empty)
                  \<diamondsuit> ((set_lvars empty) s1) Z"
	by auto
      from valid_init Q' valid_A conf_s1_empty eval_init wt_init da_init
      have "(set_lvars l .; R) \<diamondsuit> s2 Z"
	by (rule validE)
      with s3 l have "R \<diamondsuit> s3 Z"
	by simp
      moreover 
      from eval wt da conf_s0 wf
      have "s3\<Colon>\<preceq>(G,L)"
	by (rule evaln_type_sound [elim_format]) simp
      ultimately show ?thesis ..
    qed
  qed
next
  case (InsInitV A P Q c v)
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} InsInitV c v=\<succ> {Q} }"
  proof (rule valid_var_NormalI)
    fix s0 vf n s1 L Z
    assume "normal s0"
    moreover
    assume "G\<turnstile>s0 \<midarrow>InsInitV c v=\<succ>vf\<midarrow>n\<rightarrow> s1"
    ultimately have "False" 
      by (cases s0) (simp add: evaln_InsInitV) 
    thus "Q \<lfloor>vf\<rfloor>\<^sub>v s1 Z \<and> s1\<Colon>\<preceq>(G, L)"..
  qed
next
  case (InsInitE A P Q c e)
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} InsInitE c e-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix s0 v n s1 L Z
    assume "normal s0"
    moreover
    assume "G\<turnstile>s0 \<midarrow>InsInitE c e-\<succ>v\<midarrow>n\<rightarrow> s1"
    ultimately have "False" 
      by (cases s0) (simp add: evaln_InsInitE) 
    thus "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"..
  qed
next
  case (Callee A P Q e l)
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} Callee l e-\<succ> {Q} }"
  proof (rule valid_expr_NormalI)
    fix s0 v n s1 L Z
    assume "normal s0"
    moreover
    assume "G\<turnstile>s0 \<midarrow>Callee l e-\<succ>v\<midarrow>n\<rightarrow> s1"
    ultimately have "False" 
      by (cases s0) (simp add: evaln_Callee) 
    thus "Q \<lfloor>v\<rfloor>\<^sub>e s1 Z \<and> s1\<Colon>\<preceq>(G, L)"..
  qed
next
  case (FinA A P Q a c)
  show "G,A|\<Turnstile>\<Colon>{ {Normal P} .FinA a c. {Q} }"
  proof (rule valid_stmt_NormalI)
    fix s0 v n s1 L Z
    assume "normal s0"
    moreover
    assume "G\<turnstile>s0 \<midarrow>FinA a c\<midarrow>n\<rightarrow> s1"
    ultimately have "False" 
      by (cases s0) (simp add: evaln_FinA) 
    thus "Q \<diamondsuit> s1 Z \<and> s1\<Colon>\<preceq>(G, L)"..
  qed
qed
declare inj_term_simps [simp del]
    
theorem ax_sound: 
 "wf_prog G \<Longrightarrow> G,(A::'a triple set)|\<turnstile>(ts::'a triple set) \<Longrightarrow> G,A|\<Turnstile>ts"
apply (subst ax_valids2_eq [symmetric])
apply  assumption
apply (erule (1) ax_sound2)
done

lemma sound_valid2_lemma: 
"\<lbrakk>\<forall>v n. Ball A (triple_valid2 G n) \<longrightarrow> P v n; Ball A (triple_valid2 G n)\<rbrakk>
 \<Longrightarrow>P v n"
by blast

end
