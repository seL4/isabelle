(*  Title:      HOL/MicroJava/BV/Correct.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

The invariant for the type safety proof.
*)

header "BV Type Safety Invariant"

theory Correct = BVSpec:

constdefs
  approx_val :: "[jvm_prog,aheap,val,ty err] => bool"
  "approx_val G h v any == case any of Err => True | OK T => G,h\<turnstile>v::\<preceq>T"

  approx_loc :: "[jvm_prog,aheap,val list,locvars_type] => bool"
  "approx_loc G hp loc LT == list_all2 (approx_val G hp) loc LT"

  approx_stk :: "[jvm_prog,aheap,opstack,opstack_type] => bool"
  "approx_stk G hp stk ST == approx_loc G hp stk (map OK ST)"

  correct_frame  :: "[jvm_prog,aheap,state_type,nat,bytecode] => frame => bool"
  "correct_frame G hp == \<lambda>(ST,LT) maxl ins (stk,loc,C,sig,pc).
                         approx_stk G hp stk ST  \<and> approx_loc G hp loc LT \<and> 
                         pc < length ins \<and> length loc=length(snd sig)+maxl+1"

  correct_frame_opt :: "[jvm_prog,aheap,state_type option,nat,bytecode] 
                        => frame => bool"
  "correct_frame_opt G hp s == 
    case s of None => \<lambda>maxl ins f. False | Some t => correct_frame G hp t"


consts
 correct_frames  :: "[jvm_prog,aheap,prog_type,ty,sig,frame list] => bool"
primrec
"correct_frames G hp phi rT0 sig0 [] = True"

"correct_frames G hp phi rT0 sig0 (f#frs) =
	(let (stk,loc,C,sig,pc) = f in
  (\<exists>ST LT rT maxs maxl ins.
    phi C sig ! pc = Some (ST,LT) \<and> is_class G C \<and> 
    method (G,C) sig = Some(C,rT,(maxs,maxl,ins)) \<and>
	(\<exists>C' mn pTs k. pc = k+1 \<and> ins!k = (Invoke C' mn pTs) \<and> 
         (mn,pTs) = sig0 \<and> 
         (\<exists>apTs D ST' LT'.
         (phi C sig)!k = Some ((rev apTs) @ (Class D) # ST', LT') \<and>
         length apTs = length pTs \<and>
         (\<exists>D' rT' maxs' maxl' ins'.
           method (G,D) sig0 = Some(D',rT',(maxs',maxl',ins')) \<and>
           G \<turnstile> rT0 \<preceq> rT') \<and>
	 correct_frame G hp (tl ST, LT) maxl ins f \<and> 
	 correct_frames G hp phi rT sig frs))))"


constdefs
 correct_state :: "[jvm_prog,prog_type,jvm_state] => bool"
                  ("_,_ \<turnstile>JVM _ \<surd>"  [51,51] 50)
"correct_state G phi == \<lambda>(xp,hp,frs).
   case xp of
     None => (case frs of
	           [] => True
             | (f#fs) => G\<turnstile>h hp\<surd> \<and>
			(let (stk,loc,C,sig,pc) = f
		         in
                         \<exists>rT maxs maxl ins s.
                         is_class G C \<and>
                         method (G,C) sig = Some(C,rT,(maxs,maxl,ins)) \<and>
                         phi C sig ! pc = Some s \<and>
			 correct_frame G hp s maxl ins f \<and> 
		         correct_frames G hp phi rT sig fs))
   | Some x => True" 


syntax (HTML)
 correct_state :: "[jvm_prog,prog_type,jvm_state] => bool"
                  ("_,_ |-JVM _ [ok]"  [51,51] 50)

section {* approx-val *}

lemma approx_val_Err:
  "approx_val G hp x Err"
by (simp add: approx_val_def)

lemma approx_val_Null:
  "approx_val G hp Null (OK (RefT x))"
by (auto intro: null simp add: approx_val_def)

lemma approx_val_imp_approx_val_assConvertible [rule_format]: 
  "wf_prog wt G ==> approx_val G hp v (OK T) --> G\<turnstile> T\<preceq>T' 
  --> approx_val G hp v (OK T')"
by (cases T) (auto intro: conf_widen simp add: approx_val_def)

lemma approx_val_imp_approx_val_sup_heap [rule_format]:
  "approx_val G hp v at --> hp \<le>| hp' --> approx_val G hp' v at"
apply (simp add: approx_val_def split: err.split)
apply (blast intro: conf_hext)
done

lemma approx_val_imp_approx_val_heap_update:
  "[|hp a = Some obj'; G,hp\<turnstile> v::\<preceq>T; obj_ty obj = obj_ty obj'|] 
  ==> G,hp(a\<mapsto>obj)\<turnstile> v::\<preceq>T"
by (cases v, auto simp add: obj_ty_def conf_def)

lemma approx_val_imp_approx_val_sup [rule_format]:
  "wf_prog wt G ==> (approx_val G h v us) --> (G \<turnstile> us <=o us') 
  --> (approx_val G h v us')"
apply (simp add: sup_PTS_eq approx_val_def split: err.split)
apply (blast intro: conf_widen)
done

lemma approx_loc_imp_approx_val_sup:
  "[| wf_prog wt G; approx_loc G hp loc LT; idx < length LT; 
      v = loc!idx; G \<turnstile> LT!idx <=o at |]
  ==> approx_val G hp v at"
apply (unfold approx_loc_def)
apply (unfold list_all2_def)
apply (auto intro: approx_val_imp_approx_val_sup 
            simp add: split_def all_set_conv_all_nth)
done


section {* approx-loc *}

lemma approx_loc_Cons [iff]:
  "approx_loc G hp (s#xs) (l#ls) = 
  (approx_val G hp s l \<and> approx_loc G hp xs ls)"
by (simp add: approx_loc_def)

lemma assConv_approx_stk_imp_approx_loc [rule_format]:
  "wf_prog wt G ==> (\<forall>tt'\<in>set (zip tys_n ts). tt' \<in> widen G) 
  --> length tys_n = length ts --> approx_stk G hp s tys_n --> 
  approx_loc G hp s (map OK ts)"
apply (unfold approx_stk_def approx_loc_def list_all2_def)
apply (clarsimp simp add: all_set_conv_all_nth)
apply (rule approx_val_imp_approx_val_assConvertible)
apply auto
done


lemma approx_loc_imp_approx_loc_sup_heap [rule_format]:
  "\<forall>lvars. approx_loc G hp lvars lt --> hp \<le>| hp' 
  --> approx_loc G hp' lvars lt"
apply (unfold approx_loc_def list_all2_def)
apply (cases lt)
 apply simp
apply clarsimp
apply (rule approx_val_imp_approx_val_sup_heap)
apply auto
done

lemma approx_loc_imp_approx_loc_sup [rule_format]:
  "wf_prog wt G ==> approx_loc G hp lvars lt --> G \<turnstile> lt <=l lt' 
  --> approx_loc G hp lvars lt'"
apply (unfold Listn.le_def lesub_def sup_loc_def approx_loc_def list_all2_def)
apply (auto simp add: all_set_conv_all_nth)
apply (auto elim: approx_val_imp_approx_val_sup)
done


lemma approx_loc_imp_approx_loc_subst [rule_format]:
  "\<forall>loc idx x X. (approx_loc G hp loc LT) --> (approx_val G hp x X) 
  --> (approx_loc G hp (loc[idx:=x]) (LT[idx:=X]))"
apply (unfold approx_loc_def list_all2_def)
apply (auto dest: subsetD [OF set_update_subset_insert] simp add: zip_update)
done


lemmas [cong] = conj_cong 

lemma approx_loc_append [rule_format]:
  "\<forall>L1 l2 L2. length l1=length L1 --> 
  approx_loc G hp (l1@l2) (L1@L2) = 
  (approx_loc G hp l1 L1 \<and> approx_loc G hp l2 L2)"
apply (unfold approx_loc_def list_all2_def)
apply simp
apply blast
done

lemmas [cong del] = conj_cong


section {* approx-stk *}

lemma approx_stk_rev_lem:
  "approx_stk G hp (rev s) (rev t) = approx_stk G hp s t"
apply (unfold approx_stk_def approx_loc_def list_all2_def)
apply (auto simp add: zip_rev sym [OF rev_map])
done

lemma approx_stk_rev:
  "approx_stk G hp (rev s) t = approx_stk G hp s (rev t)"
by (auto intro: subst [OF approx_stk_rev_lem])


lemma approx_stk_imp_approx_stk_sup_heap [rule_format]:
  "\<forall>lvars. approx_stk G hp lvars lt --> hp \<le>| hp' 
  --> approx_stk G hp' lvars lt"
by (auto intro: approx_loc_imp_approx_loc_sup_heap simp add: approx_stk_def)

lemma approx_stk_imp_approx_stk_sup [rule_format]:
  "wf_prog wt G ==> approx_stk G hp lvars st --> (G \<turnstile> map OK st <=l (map OK st')) 
  --> approx_stk G hp lvars st'" 
by (auto intro: approx_loc_imp_approx_loc_sup simp add: approx_stk_def)

lemma approx_stk_Nil [iff]:
  "approx_stk G hp [] []"
by (simp add: approx_stk_def approx_loc_def)

lemma approx_stk_Cons [iff]:
  "approx_stk G hp (x # stk) (S#ST) = 
   (approx_val G hp x (OK S) \<and> approx_stk G hp stk ST)"
by (simp add: approx_stk_def approx_loc_def)

lemma approx_stk_Cons_lemma [iff]:
  "approx_stk G hp stk (S#ST') = 
  (\<exists>s stk'. stk = s#stk' \<and> approx_val G hp s (OK S) \<and> approx_stk G hp stk' ST')"
by (simp add: list_all2_Cons2 approx_stk_def approx_loc_def)

lemma approx_stk_append_lemma:
  "approx_stk G hp stk (S@ST') ==>
   (\<exists>s stk'. stk = s@stk' \<and> length s = length S \<and> length stk' = length ST' \<and> 
             approx_stk G hp s S \<and> approx_stk G hp stk' ST')"
by (simp add: list_all2_append2 approx_stk_def approx_loc_def)


section {* oconf *}

lemma correct_init_obj:
  "[|is_class G C; wf_prog wt G|] ==> 
  G,h \<turnstile> (C, map_of (map (\<lambda>(f,fT).(f,default_val fT)) (fields(G,C)))) \<surd>"
apply (unfold oconf_def lconf_def)
apply (simp add: map_of_map)
apply (force intro: defval_conf dest: map_of_SomeD fields_is_type)
done


lemma oconf_imp_oconf_field_update [rule_format]:
  "[|map_of (fields (G, oT)) FD = Some T; G,hp\<turnstile>v::\<preceq>T; G,hp\<turnstile>(oT,fs)\<surd> |]
  ==> G,hp\<turnstile>(oT, fs(FD\<mapsto>v))\<surd>"
by (simp add: oconf_def lconf_def)

lemma oconf_imp_oconf_heap_newref [rule_format]:
"hp oref = None --> G,hp\<turnstile>obj\<surd> --> G,hp\<turnstile>obj'\<surd> --> G,(hp(oref\<mapsto>obj'))\<turnstile>obj\<surd>"
apply (unfold oconf_def lconf_def)
apply simp
apply (fast intro: conf_hext hext_new)
done

lemma oconf_imp_oconf_heap_update [rule_format]:
  "hp a = Some obj' --> obj_ty obj' = obj_ty obj'' --> G,hp\<turnstile>obj\<surd> 
  --> G,hp(a\<mapsto>obj'')\<turnstile>obj\<surd>"
apply (unfold oconf_def lconf_def)
apply simp
apply (force intro: approx_val_imp_approx_val_heap_update)
done


section {* hconf *}

lemma hconf_imp_hconf_newref [rule_format]:
  "hp oref = None --> G\<turnstile>h hp\<surd> --> G,hp\<turnstile>obj\<surd> --> G\<turnstile>h hp(oref\<mapsto>obj)\<surd>"
apply (simp add: hconf_def)
apply (fast intro: oconf_imp_oconf_heap_newref)
done

lemma hconf_imp_hconf_field_update [rule_format]:
  "map_of (fields (G, oT)) (F, D) = Some T \<and> hp oloc = Some(oT,fs) \<and> 
  G,hp\<turnstile>v::\<preceq>T \<and> G\<turnstile>h hp\<surd> --> G\<turnstile>h hp(oloc \<mapsto> (oT, fs((F,D)\<mapsto>v)))\<surd>"
apply (simp add: hconf_def)
apply (force intro: oconf_imp_oconf_heap_update oconf_imp_oconf_field_update 
             simp add: obj_ty_def)
done

section {* correct-frames *}

lemmas [simp del] = fun_upd_apply

lemma correct_frames_imp_correct_frames_field_update [rule_format]:
  "\<forall>rT C sig. correct_frames G hp phi rT sig frs --> 
  hp a = Some (C,od) --> map_of (fields (G, C)) fl = Some fd --> 
  G,hp\<turnstile>v::\<preceq>fd 
  --> correct_frames G (hp(a \<mapsto> (C, od(fl\<mapsto>v)))) phi rT sig frs";
apply (induct frs)
 apply simp
apply clarify
apply simp
apply clarify
apply (unfold correct_frame_def)
apply (simp (no_asm_use))
apply clarsimp
apply (intro exI conjI)
     apply simp
    apply simp
   apply force
  apply simp
 apply (rule approx_stk_imp_approx_stk_sup_heap)
  apply simp
 apply (rule hext_upd_obj)
 apply simp
apply (rule approx_loc_imp_approx_loc_sup_heap)
 apply simp
apply (rule hext_upd_obj)
apply simp
done

lemma correct_frames_imp_correct_frames_newref [rule_format]:
  "\<forall>rT C sig. hp x = None --> correct_frames G hp phi rT sig frs \<and> oconf G hp obj 
  --> correct_frames G (hp(x \<mapsto> obj)) phi rT sig frs"
apply (induct frs)
 apply simp
apply (clarsimp simp add: correct_frame_def)
apply (intro exI conjI)
     apply simp
    apply simp
   apply force
  apply simp
 apply (rule approx_stk_imp_approx_stk_sup_heap)
  apply simp
 apply (rule hext_new)
 apply simp
apply (rule approx_loc_imp_approx_loc_sup_heap)
 apply simp
apply (rule hext_new)
apply simp
done

end

