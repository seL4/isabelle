(*  Title:      HOL/Bali/AxExample.thy
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Example of a proof based on the Bali axiomatic semantics *}

theory AxExample = AxSem + Example:

constdefs
  arr_inv :: "st \<Rightarrow> bool"
 "arr_inv \<equiv> \<lambda>s. \<exists>obj a T el. globs s (Stat Base) = Some obj \<and>
                              values obj (Inl (arr, Base)) = Some (Addr a) \<and>
                              heap s a = Some \<lparr>tag=Arr T 2,values=el\<rparr>"

lemma arr_inv_new_obj: 
"\<And>a. \<lbrakk>arr_inv s; new_Addr (heap s)=Some a\<rbrakk> \<Longrightarrow> arr_inv (gupd(Inl a\<mapsto>x) s)"
apply (unfold arr_inv_def)
apply (force dest!: new_AddrD2)
done

lemma arr_inv_set_locals [simp]: "arr_inv (set_locals l s) = arr_inv s"
apply (unfold arr_inv_def)
apply (simp (no_asm))
done

lemma arr_inv_gupd_Stat [simp]: 
  "Base \<noteq> C \<Longrightarrow> arr_inv (gupd(Stat C\<mapsto>obj) s) = arr_inv s"
apply (unfold arr_inv_def)
apply (simp (no_asm_simp))
done

lemma ax_inv_lupd [simp]: "arr_inv (lupd(x\<mapsto>y) s) = arr_inv s"
apply (unfold arr_inv_def)
apply (simp (no_asm))
done


declare split_if_asm [split del]
declare lvar_def [simp]

ML {*
fun inst1_tac s t = instantiate_tac [(s,t)];
val ax_tac = REPEAT o rtac allI THEN'
             resolve_tac(thm "ax_Skip"::thm "ax_StatRef"::thm "ax_MethdN"::
                         thm "ax_Alloc"::thm "ax_Alloc_Arr"::
                         thm "ax_SXAlloc_Normal"::
                         funpow 7 tl (thms "ax_derivs.intros"))
*}


theorem ax_test: "tprg,({}::'a triple set)\<turnstile> 
  {Normal (\<lambda>Y s Z::'a. heap_free four s \<and> \<not>initd Base s \<and> \<not> initd Ext s)} 
  .test [Class Base]. {\<lambda>Y s Z. abrupt s = Some (Xcpt (Std IndOutBound))}"
apply (unfold test_def arr_viewed_from_def)
apply (tactic "ax_tac 1" (*;;*))
defer
apply  (tactic "ax_tac 1" (* Try *))
defer
apply    (tactic {* inst1_tac "Q1" 
                 "\<lambda>Y s Z. arr_inv (snd s) \<and> tprg,s\<turnstile>catch SXcpt NullPointer" *})
prefer 2
apply    simp
apply   (rule_tac P' = "Normal (\<lambda>Y s Z. arr_inv (snd s))" in conseq1)
prefer 2
apply    clarsimp
apply   (rule_tac Q' = "(\<lambda>Y s Z. ?Q Y s Z)\<leftarrow>=False\<down>=\<diamondsuit>" in conseq2)
prefer 2
apply    simp
apply   (tactic "ax_tac 1" (* While *))
prefer 2
apply    (rule ax_impossible [THEN conseq1], clarsimp)
apply   (rule_tac P' = "Normal ?P" in conseq1)
prefer 2
apply    clarsimp
apply   (tactic "ax_tac 1")
apply   (tactic "ax_tac 1" (* AVar *))
prefer 2
apply    (rule ax_subst_Val_allI)
apply    (tactic {* inst1_tac "P'21" "\<lambda>u a. Normal (?PP a\<leftarrow>?x) u" *})
apply    (simp del: avar_def2 peek_and_def2)
apply    (tactic "ax_tac 1")
apply   (tactic "ax_tac 1")
      (* just for clarification: *)
apply   (rule_tac Q' = "Normal (\<lambda>Var:(v, f) u ua. fst (snd (avar tprg (Intg 2) v u)) = Some (Xcpt (Std IndOutBound)))" in conseq2)
prefer 2
apply    (clarsimp simp add: split_beta)
apply   (tactic "ax_tac 1" (* FVar *))
apply    (tactic "ax_tac 2" (* StatRef *))
apply   (rule ax_derivs.Done [THEN conseq1])
apply   (clarsimp simp add: arr_inv_def inited_def in_bounds_def)
defer
apply  (rule ax_SXAlloc_catch_SXcpt)
apply  (rule_tac Q' = "(\<lambda>Y (x, s) Z. x = Some (Xcpt (Std NullPointer)) \<and> arr_inv s) \<and>. heap_free two" in conseq2)
prefer 2
apply   (simp add: arr_inv_new_obj)
apply  (tactic "ax_tac 1") 
apply  (rule_tac C = "Ext" in ax_Call_known_DynT)
apply     (unfold DynT_prop_def)
apply     (simp (no_asm))
apply    (intro strip)
apply    (rule_tac P' = "Normal ?P" in conseq1)
apply     (tactic "ax_tac 1" (* Methd *))
apply     (rule ax_thin [OF _ empty_subsetI])
apply     (simp (no_asm) add: body_def2)
apply     (tactic "ax_tac 1" (* Body *))
(* apply       (rule_tac [2] ax_derivs.Abrupt) *)
defer
apply      (simp (no_asm))
apply      (tactic "ax_tac 1")
apply      (tactic "ax_tac 1") (* Ass *)
prefer 2
apply       (rule ax_subst_Var_allI)
apply       (tactic {* inst1_tac "P'27" "\<lambda>a vs l vf. ?PP a vs l vf\<leftarrow>?x \<and>. ?p" *})
apply       (rule allI)
apply       (tactic {* simp_tac (simpset() delloop "split_all_tac" delsimps [thm "peek_and_def2"]) 1 *})
apply       (rule ax_derivs.Abrupt)
apply      (simp (no_asm))
apply      (tactic "ax_tac 1" (* FVar *))
apply       (tactic "ax_tac 2", tactic "ax_tac 2", tactic "ax_tac 2")
apply      (tactic "ax_tac 1")
apply     clarsimp
apply     (tactic {* inst1_tac "R14" "\<lambda>a'. Normal ((\<lambda>Vals:vs (x, s) Z. arr_inv s \<and> inited Ext (globs s) \<and> a' \<noteq> Null \<and> hd vs = Null) \<and>. heap_free two)" *})
prefer 5
apply     (rule ax_derivs.Done [THEN conseq1], force)
apply    force
apply   (rule ax_subst_Val_allI)
apply   (tactic {* inst1_tac "P'33" "\<lambda>u a. Normal (?PP a\<leftarrow>?x) u" *})
apply   (simp (no_asm) del: peek_and_def2)
apply   (tactic "ax_tac 1")
prefer 2
apply   (rule ax_subst_Val_allI)
apply    (tactic {* inst1_tac "P'4" "\<lambda>aa v. Normal (?QQ aa v\<leftarrow>?y)" *})
apply    (simp del: peek_and_def2)
apply    (tactic "ax_tac 1")
apply   (tactic "ax_tac 1")
apply  (tactic "ax_tac 1")
apply  (tactic "ax_tac 1")
(* end method call *)
apply (simp (no_asm))
    (* just for clarification: *)
apply (rule_tac Q' = "Normal ((\<lambda>Y (x, s) Z. arr_inv s \<and> (\<exists>a. the (locals s (VName e)) = Addr a \<and> obj_class (the (globs s (Inl a))) = Ext \<and> 
 invocation_declclass tprg IntVir s (the (locals s (VName e))) (ClassT Base)  
     \<lparr>name = foo, parTs = [Class Base]\<rparr> = Ext)) \<and>. initd Ext \<and>. heap_free two)"
  in conseq2)
prefer 2
apply  clarsimp
apply (tactic "ax_tac 1")
apply (tactic "ax_tac 1")
defer
apply  (rule ax_subst_Var_allI)
apply  (tactic {* inst1_tac "P'14" "\<lambda>u vf. Normal (?PP vf \<and>. ?p) u" *})
apply  (simp (no_asm) del: split_paired_All peek_and_def2)
apply  (tactic "ax_tac 1" (* NewC *))
apply  (tactic "ax_tac 1" (* ax_Alloc *))
     (* just for clarification: *)
apply  (rule_tac Q' = "Normal ((\<lambda>Y s Z. arr_inv (store s) \<and> vf=lvar (VName e) (store s)) \<and>. heap_free tree \<and>. initd Ext)" in conseq2)
prefer 2
apply   (simp add: invocation_declclass_def dynmethd_def)
apply   (unfold dynlookup_def)
apply   (simp add: dynmethd_Ext_foo)
apply   (force elim!: arr_inv_new_obj atleast_free_SucD atleast_free_weaken)
     (* begin init *)
apply  (rule ax_InitS)
apply     force
apply    (simp (no_asm))
apply   (tactic {* simp_tac (simpset() delloop "split_all_tac") 1 *})
apply   (rule ax_Init_Skip_lemma)
apply  (tactic {* simp_tac (simpset() delloop "split_all_tac") 1 *})
apply  (rule ax_InitS [THEN conseq1] (* init Base *))
apply      force
apply     (simp (no_asm))
apply    (unfold arr_viewed_from_def)
apply    (rule allI)
apply    (rule_tac P' = "Normal ?P" in conseq1)
apply     (tactic {* simp_tac (simpset() delloop "split_all_tac") 1 *})
apply     (tactic "ax_tac 1")
apply     (tactic "ax_tac 1")
apply     (rule_tac [2] ax_subst_Var_allI)
apply      (tactic {* inst1_tac "P'29" "\<lambda>vf l vfa. Normal (?P vf l vfa)" *})
apply     (tactic {* simp_tac (simpset() delloop "split_all_tac" delsimps [split_paired_All, thm "peek_and_def2"]) 2 *})
apply      (tactic "ax_tac 2" (* NewA *))
apply       (tactic "ax_tac 3" (* ax_Alloc_Arr *))
apply       (tactic "ax_tac 3")
apply      (tactic {* inst1_tac "P" "\<lambda>vf l vfa. Normal (?P vf l vfa\<leftarrow>\<diamondsuit>)" *})
apply      (tactic {* simp_tac (simpset() delloop "split_all_tac") 2 *})
apply      (tactic "ax_tac 2")
apply     (tactic "ax_tac 1" (* FVar *))
apply      (tactic "ax_tac 2" (* StatRef *))
apply     (rule ax_derivs.Done [THEN conseq1])
apply     (tactic {* inst1_tac "Q22" "\<lambda>vf. Normal ((\<lambda>Y s Z. vf=lvar (VName e) (snd s)) \<and>. heap_free four \<and>. initd Base \<and>. initd Ext)" *})
apply     (clarsimp split del: split_if)
apply     (frule atleast_free_weaken [THEN atleast_free_weaken])
apply     (drule initedD)
apply     (clarsimp elim!: atleast_free_SucD simp add: arr_inv_def)
apply    force
apply   (tactic {* simp_tac (simpset() delloop "split_all_tac") 1 *})
apply   (rule ax_triv_Init_Object [THEN peek_and_forget2, THEN conseq1])
apply     (rule wf_tprg)
apply    clarsimp
apply   (tactic {* inst1_tac "P22" "\<lambda>vf. Normal ((\<lambda>Y s Z. vf = lvar (VName e) (snd s)) \<and>. heap_free four \<and>. initd Ext)" *})
apply   clarsimp
apply  (tactic {* inst1_tac "PP" "\<lambda>vf. Normal ((\<lambda>Y s Z. vf = lvar (VName e) (snd s)) \<and>. heap_free four \<and>. Not \<circ> initd Base)" *})
apply  clarsimp
     (* end init *)
apply (rule conseq1)
apply (tactic "ax_tac 1")
apply clarsimp
done

(*
while (true) {
  if (i) {throw xcpt;}
  else i=j
}
*)
lemma Loop_Xcpt_benchmark: 
 "Q = (\<lambda>Y (x,s) Z. x \<noteq> None \<longrightarrow> the_Bool (the (locals s i))) \<Longrightarrow>  
  G,({}::'a triple set)\<turnstile>{Normal (\<lambda>Y s Z::'a. True)}  
  .lab1\<bullet> While(Lit (Bool True)) (If(Acc (LVar i)) (Throw (Acc (LVar xcpt))) Else
        (Expr (Ass (LVar i) (Acc (LVar j))))). {Q}"
apply (rule_tac P' = "Q" and Q' = "Q\<leftarrow>=False\<down>=\<diamondsuit>" in conseq12)
apply  safe
apply  (tactic "ax_tac 1" (* Loop *))
apply   (rule ax_Normal_cases)
prefer 2
apply    (rule ax_derivs.Abrupt [THEN conseq1], clarsimp simp add: Let_def)
apply   (rule conseq1)
apply    (tactic "ax_tac 1")
apply   clarsimp
prefer 2
apply  clarsimp
apply (tactic "ax_tac 1" (* If *))
apply  (tactic 
  {* inst1_tac "P'21" "Normal (\<lambda>s.. (\<lambda>Y s Z. True)\<down>=Val (the (locals s i)))" *})
apply  (tactic "ax_tac 1")
apply  (rule conseq1)
apply   (tactic "ax_tac 1")
apply  clarsimp
apply (rule allI)
apply (rule ax_escape)
apply auto
apply  (rule conseq1)
apply   (tactic "ax_tac 1" (* Throw *))
apply   (tactic "ax_tac 1")
apply   (tactic "ax_tac 1")
apply  clarsimp
apply (rule_tac Q' = "Normal (\<lambda>Y s Z. True)" in conseq2)
prefer 2
apply  clarsimp
apply (rule conseq1)
apply  (tactic "ax_tac 1")
apply  (tactic "ax_tac 1")
prefer 2
apply   (rule ax_subst_Var_allI)
apply   (tactic {* inst1_tac "P'29" "\<lambda>b Y ba Z vf. \<lambda>Y (x,s) Z. x=None \<and> snd vf = snd (lvar i s)" *})
apply   (rule allI)
apply   (rule_tac P' = "Normal ?P" in conseq1)
prefer 2
apply    clarsimp
apply   (tactic "ax_tac 1")
apply   (rule conseq1)
apply    (tactic "ax_tac 1")
apply   clarsimp
apply  (tactic "ax_tac 1")
apply clarsimp
done

end

