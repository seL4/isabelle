
(*  Title:      HOL/MicroJava/BV/Correct.thy
    ID:         $Id$
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

The invariant for the type safety proof.
*)

header {* \isaheader{BV Type Safety Invariant} *}

theory Correct = BVSpec + JVMExec:

constdefs
  approx_val :: "[jvm_prog,aheap,val,ty err] \<Rightarrow> bool"
  "approx_val G h v any == case any of Err \<Rightarrow> True | OK T \<Rightarrow> G,h\<turnstile>v::\<preceq>T"

  approx_loc :: "[jvm_prog,aheap,val list,locvars_type] \<Rightarrow> bool"
  "approx_loc G hp loc LT == list_all2 (approx_val G hp) loc LT"

  approx_stk :: "[jvm_prog,aheap,opstack,opstack_type] \<Rightarrow> bool"
  "approx_stk G hp stk ST == approx_loc G hp stk (map OK ST)"

  correct_frame  :: "[jvm_prog,aheap,state_type,nat,bytecode] \<Rightarrow> frame \<Rightarrow> bool"
  "correct_frame G hp == \<lambda>(ST,LT) maxl ins (stk,loc,C,sig,pc).
                         approx_stk G hp stk ST  \<and> approx_loc G hp loc LT \<and> 
                         pc < length ins \<and> length loc=length(snd sig)+maxl+1"


consts
 correct_frames  :: "[jvm_prog,aheap,prog_type,ty,sig,frame list] \<Rightarrow> bool"
primrec
"correct_frames G hp phi rT0 sig0 [] = True"

"correct_frames G hp phi rT0 sig0 (f#frs) =
  (let (stk,loc,C,sig,pc) = f in
  (\<exists>ST LT rT maxs maxl ins et.
    phi C sig ! pc = Some (ST,LT) \<and> is_class G C \<and> 
    method (G,C) sig = Some(C,rT,(maxs,maxl,ins,et)) \<and>
  (\<exists>C' mn pTs. ins!pc = (Invoke C' mn pTs) \<and> 
         (mn,pTs) = sig0 \<and> 
         (\<exists>apTs D ST' LT'.
         (phi C sig)!pc = Some ((rev apTs) @ (Class D) # ST', LT') \<and>
         length apTs = length pTs \<and>
         (\<exists>D' rT' maxs' maxl' ins' et'.
           method (G,D) sig0 = Some(D',rT',(maxs',maxl',ins',et')) \<and>
           G \<turnstile> rT0 \<preceq> rT') \<and>
   correct_frame G hp (ST, LT) maxl ins f \<and> 
   correct_frames G hp phi rT sig frs))))"


constdefs
 correct_state :: "[jvm_prog,prog_type,jvm_state] \<Rightarrow> bool"
                  ("_,_ |-JVM _ [ok]"  [51,51] 50)
"correct_state G phi == \<lambda>(xp,hp,frs).
   case xp of
     None \<Rightarrow> (case frs of
             [] \<Rightarrow> True
             | (f#fs) \<Rightarrow> G\<turnstile>h hp\<surd> \<and> preallocated hp \<and> 
      (let (stk,loc,C,sig,pc) = f
             in
                         \<exists>rT maxs maxl ins et s.
                         is_class G C \<and>
                         method (G,C) sig = Some(C,rT,(maxs,maxl,ins,et)) \<and>
                         phi C sig ! pc = Some s \<and>
       correct_frame G hp s maxl ins f \<and> 
             correct_frames G hp phi rT sig fs))
   | Some x \<Rightarrow> frs = []" 


syntax (xsymbols)
 correct_state :: "[jvm_prog,prog_type,jvm_state] \<Rightarrow> bool"
                  ("_,_ \<turnstile>JVM _ \<surd>"  [51,51] 50)


lemma sup_ty_opt_OK:
  "(G \<turnstile> X <=o (OK T')) = (\<exists>T. X = OK T \<and> G \<turnstile> T \<preceq> T')"
  apply (cases X)
  apply auto
  done


section {* approx-val *}

lemma approx_val_Err [simp,intro!]:
  "approx_val G hp x Err"
  by (simp add: approx_val_def)

lemma approx_val_OK [iff]: 
  "approx_val G hp x (OK T) = (G,hp \<turnstile> x ::\<preceq> T)"
  by (simp add: approx_val_def)

lemma approx_val_Null [simp,intro!]:
  "approx_val G hp Null (OK (RefT x))"
  by (auto simp add: approx_val_def)

lemma approx_val_sup_heap:
  "\<lbrakk> approx_val G hp v T; hp \<le>| hp' \<rbrakk> \<Longrightarrow> approx_val G hp' v T"
  by (cases T) (blast intro: conf_hext)+

lemma approx_val_heap_update:
  "\<lbrakk> hp a = Some obj'; G,hp\<turnstile> v::\<preceq>T; obj_ty obj = obj_ty obj'\<rbrakk> 
  \<Longrightarrow> G,hp(a\<mapsto>obj)\<turnstile> v::\<preceq>T"
  by (cases v, auto simp add: obj_ty_def conf_def)

lemma approx_val_widen:
  "\<lbrakk> approx_val G hp v T; G \<turnstile> T <=o T'; wf_prog wt G \<rbrakk>
  \<Longrightarrow> approx_val G hp v T'"
  by (cases T', auto simp add: sup_ty_opt_OK intro: conf_widen)

section {* approx-loc *}

lemma approx_loc_Nil [simp,intro!]:
  "approx_loc G hp [] []"
  by (simp add: approx_loc_def)

lemma approx_loc_Cons [iff]:
  "approx_loc G hp (l#ls) (L#LT) = 
  (approx_val G hp l L \<and> approx_loc G hp ls LT)"
by (simp add: approx_loc_def)

lemma approx_loc_nth:
  "\<lbrakk> approx_loc G hp loc LT; n < length LT \<rbrakk>
  \<Longrightarrow> approx_val G hp (loc!n) (LT!n)"
  by (simp add: approx_loc_def list_all2_conv_all_nth)

lemma approx_loc_imp_approx_val_sup:
  "\<lbrakk>approx_loc G hp loc LT; n < length LT; LT ! n = OK T; G \<turnstile> T \<preceq> T'; wf_prog wt G\<rbrakk> 
  \<Longrightarrow> G,hp \<turnstile> (loc!n) ::\<preceq> T'"
  apply (drule approx_loc_nth, assumption) 
  apply simp
  apply (erule conf_widen, assumption+)
  done

lemma approx_loc_conv_all_nth:
  "approx_loc G hp loc LT = 
  (length loc = length LT \<and> (\<forall>n < length loc. approx_val G hp (loc!n) (LT!n)))"
  by (simp add: approx_loc_def list_all2_conv_all_nth)

lemma approx_loc_sup_heap:
  "\<lbrakk> approx_loc G hp loc LT; hp \<le>| hp' \<rbrakk>
  \<Longrightarrow> approx_loc G hp' loc LT"
  apply (clarsimp simp add: approx_loc_conv_all_nth)
  apply (blast intro: approx_val_sup_heap)
  done

lemma approx_loc_widen:
  "\<lbrakk> approx_loc G hp loc LT; G \<turnstile> LT <=l LT'; wf_prog wt G \<rbrakk>
  \<Longrightarrow> approx_loc G hp loc LT'"
apply (unfold Listn.le_def lesub_def sup_loc_def)
apply (simp (no_asm_use) only: list_all2_conv_all_nth approx_loc_conv_all_nth)
apply (simp (no_asm_simp))
apply clarify
apply (erule allE, erule impE) 
 apply simp
apply (erule approx_val_widen)
 apply simp
apply assumption
done

lemma loc_widen_Err [dest]:
  "\<And>XT. G \<turnstile> replicate n Err <=l XT \<Longrightarrow> XT = replicate n Err"
  by (induct n) auto
  
lemma approx_loc_Err [iff]:
  "approx_loc G hp (replicate n v) (replicate n Err)"
  by (induct n) auto

lemma approx_loc_subst:
  "\<lbrakk> approx_loc G hp loc LT; approx_val G hp x X \<rbrakk>
  \<Longrightarrow> approx_loc G hp (loc[idx:=x]) (LT[idx:=X])"
apply (unfold approx_loc_def list_all2_def)
apply (auto dest: subsetD [OF set_update_subset_insert] simp add: zip_update)
done

lemma approx_loc_append:
  "length l1=length L1 \<Longrightarrow>
  approx_loc G hp (l1@l2) (L1@L2) = 
  (approx_loc G hp l1 L1 \<and> approx_loc G hp l2 L2)"
  apply (unfold approx_loc_def list_all2_def)
  apply (simp cong: conj_cong)
  apply blast
  done

section {* approx-stk *}

lemma approx_stk_rev_lem:
  "approx_stk G hp (rev s) (rev t) = approx_stk G hp s t"
  apply (unfold approx_stk_def approx_loc_def)
  apply (simp add: rev_map [THEN sym])
  done

lemma approx_stk_rev:
  "approx_stk G hp (rev s) t = approx_stk G hp s (rev t)"
  by (auto intro: subst [OF approx_stk_rev_lem])

lemma approx_stk_sup_heap:
  "\<lbrakk> approx_stk G hp stk ST; hp \<le>| hp' \<rbrakk> \<Longrightarrow> approx_stk G hp' stk ST"
  by (auto intro: approx_loc_sup_heap simp add: approx_stk_def)

lemma approx_stk_widen:
  "\<lbrakk> approx_stk G hp stk ST; G \<turnstile> map OK ST <=l map OK ST'; wf_prog wt G \<rbrakk>
  \<Longrightarrow> approx_stk G hp stk ST'" 
  by (auto elim: approx_loc_widen simp add: approx_stk_def)

lemma approx_stk_Nil [iff]:
  "approx_stk G hp [] []"
  by (simp add: approx_stk_def)

lemma approx_stk_Cons [iff]:
  "approx_stk G hp (x#stk) (S#ST) = 
  (approx_val G hp x (OK S) \<and> approx_stk G hp stk ST)"
  by (simp add: approx_stk_def)

lemma approx_stk_Cons_lemma [iff]:
  "approx_stk G hp stk (S#ST') = 
  (\<exists>s stk'. stk = s#stk' \<and> approx_val G hp s (OK S) \<and> approx_stk G hp stk' ST')"
  by (simp add: list_all2_Cons2 approx_stk_def approx_loc_def)

lemma approx_stk_append:
  "approx_stk G hp stk (S@S') \<Longrightarrow>
  (\<exists>s stk'. stk = s@stk' \<and> length s = length S \<and> length stk' = length S' \<and> 
            approx_stk G hp s S \<and> approx_stk G hp stk' S')"
  by (simp add: list_all2_append2 approx_stk_def approx_loc_def)

lemma approx_stk_all_widen:
  "\<lbrakk> approx_stk G hp stk ST; \<forall>x \<in> set (zip ST ST'). x \<in> widen G; length ST = length ST'; wf_prog wt G \<rbrakk> 
  \<Longrightarrow> approx_stk G hp stk ST'"
apply (unfold approx_stk_def)
apply (clarsimp simp add: approx_loc_conv_all_nth all_set_conv_all_nth)
apply (erule allE, erule impE, assumption)
apply (erule allE, erule impE, assumption)
apply (erule conf_widen, assumption+)
done

section {* oconf *}

lemma oconf_field_update:
  "\<lbrakk>map_of (fields (G, oT)) FD = Some T; G,hp\<turnstile>v::\<preceq>T; G,hp\<turnstile>(oT,fs)\<surd> \<rbrakk>
  \<Longrightarrow> G,hp\<turnstile>(oT, fs(FD\<mapsto>v))\<surd>"
  by (simp add: oconf_def lconf_def)

lemma oconf_newref:
  "\<lbrakk>hp oref = None; G,hp \<turnstile> obj \<surd>; G,hp \<turnstile> obj' \<surd>\<rbrakk> \<Longrightarrow> G,hp(oref\<mapsto>obj') \<turnstile> obj \<surd>"
  apply (unfold oconf_def lconf_def)
  apply simp
  apply (blast intro: conf_hext hext_new)
  done

lemma oconf_heap_update:
  "\<lbrakk> hp a = Some obj'; obj_ty obj' = obj_ty obj''; G,hp\<turnstile>obj\<surd> \<rbrakk>
  \<Longrightarrow> G,hp(a\<mapsto>obj'')\<turnstile>obj\<surd>"
  apply (unfold oconf_def lconf_def)
  apply (fastsimp intro: approx_val_heap_update)
  done

section {* hconf *}

lemma hconf_newref:
  "\<lbrakk> hp oref = None; G\<turnstile>h hp\<surd>; G,hp\<turnstile>obj\<surd> \<rbrakk> \<Longrightarrow> G\<turnstile>h hp(oref\<mapsto>obj)\<surd>"
  apply (simp add: hconf_def)
  apply (fast intro: oconf_newref)
  done

lemma hconf_field_update:
  "\<lbrakk> map_of (fields (G, oT)) X = Some T; hp a = Some(oT,fs); 
     G,hp\<turnstile>v::\<preceq>T; G\<turnstile>h hp\<surd> \<rbrakk> 
  \<Longrightarrow> G\<turnstile>h hp(a \<mapsto> (oT, fs(X\<mapsto>v)))\<surd>"
  apply (simp add: hconf_def)
  apply (fastsimp intro: oconf_heap_update oconf_field_update 
                  simp add: obj_ty_def)
  done

section {* preallocated *}

lemma preallocated_field_update:
  "\<lbrakk> map_of (fields (G, oT)) X = Some T; hp a = Some(oT,fs); 
     G\<turnstile>h hp\<surd>; preallocated hp \<rbrakk> 
  \<Longrightarrow> preallocated (hp(a \<mapsto> (oT, fs(X\<mapsto>v))))"
  apply (unfold preallocated_def)
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply simp
  apply (rule ccontr)  
  apply (unfold hconf_def)
  apply (erule allE, erule allE, erule impE, assumption)
  apply (unfold oconf_def lconf_def)
  apply (simp del: split_paired_All)
  done  


lemma 
  assumes none: "hp oref = None" and alloc: "preallocated hp"
  shows preallocated_newref: "preallocated (hp(oref\<mapsto>obj))"
proof (cases oref)
  case (XcptRef x) 
  with none alloc have "False" by (auto elim: preallocatedE [of _ x])
  thus ?thesis ..
next
  case (Loc l)
  with alloc show ?thesis by (simp add: preallocated_def)
qed
  
section {* correct-frames *}

lemmas [simp del] = fun_upd_apply

lemma correct_frames_field_update [rule_format]:
  "\<forall>rT C sig. 
  correct_frames G hp phi rT sig frs \<longrightarrow> 
  hp a = Some (C,fs) \<longrightarrow> 
  map_of (fields (G, C)) fl = Some fd \<longrightarrow> 
  G,hp\<turnstile>v::\<preceq>fd 
  \<longrightarrow> correct_frames G (hp(a \<mapsto> (C, fs(fl\<mapsto>v)))) phi rT sig frs";
apply (induct frs)
 apply simp
apply clarify
apply (simp (no_asm_use))
apply clarify
apply (unfold correct_frame_def)
apply (simp (no_asm_use))
apply clarify
apply (intro exI conjI)
    apply assumption+
   apply (erule approx_stk_sup_heap)
   apply (erule hext_upd_obj)
  apply (erule approx_loc_sup_heap)
  apply (erule hext_upd_obj)
 apply assumption+
apply blast
done

lemma correct_frames_newref [rule_format]:
  "\<forall>rT C sig. 
  hp x = None \<longrightarrow> 
  correct_frames G hp phi rT sig frs \<longrightarrow>
  correct_frames G (hp(x \<mapsto> obj)) phi rT sig frs"
apply (induct frs)
 apply simp
apply clarify
apply (simp (no_asm_use))
apply clarify
apply (unfold correct_frame_def)
apply (simp (no_asm_use))
apply clarify
apply (intro exI conjI)
    apply assumption+
   apply (erule approx_stk_sup_heap)
   apply (erule hext_new)
  apply (erule approx_loc_sup_heap)
  apply (erule hext_new)
 apply assumption+
apply blast
done

end
