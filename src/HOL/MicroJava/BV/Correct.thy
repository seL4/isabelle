(*  Title:      HOL/MicroJava/BV/Correct.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

The invariant for the type safety proof.
*)

header "Type Safety Invariant"

theory Correct = BVSpec:

constdefs
 approx_val :: "[jvm_prog,aheap,val,ty err] \<Rightarrow> bool"
"approx_val G h v any \<equiv> case any of Err \<Rightarrow> True | Ok T \<Rightarrow> G,h\<turnstile>v\<Colon>\<preceq>T"

 approx_loc :: "[jvm_prog,aheap,val list,locvars_type] \<Rightarrow> bool"
"approx_loc G hp loc LT \<equiv> list_all2 (approx_val G hp) loc LT"

 approx_stk :: "[jvm_prog,aheap,opstack,opstack_type] \<Rightarrow> bool"
"approx_stk G hp stk ST \<equiv> approx_loc G hp stk (map Ok ST)"

 correct_frame  :: "[jvm_prog,aheap,state_type,nat,bytecode] \<Rightarrow> frame \<Rightarrow> bool"
"correct_frame G hp \<equiv> \<lambda>(ST,LT) maxl ins (stk,loc,C,sig,pc).
   approx_stk G hp stk ST  \<and> approx_loc G hp loc LT \<and> 
   pc < length ins \<and> length loc=length(snd sig)+maxl+1"

 correct_frame_opt :: "[jvm_prog,aheap,state_type option,nat,bytecode] \<Rightarrow> frame \<Rightarrow> bool"
"correct_frame_opt G hp s \<equiv> case s of None \<Rightarrow> \<lambda>maxl ins f. False | Some t \<Rightarrow> correct_frame G hp t"


consts
 correct_frames  :: "[jvm_prog,aheap,prog_type,ty,sig,frame list] \<Rightarrow> bool"
primrec
"correct_frames G hp phi rT0 sig0 [] = True"

"correct_frames G hp phi rT0 sig0 (f#frs) =
	(let (stk,loc,C,sig,pc) = f in
  (\<exists>ST LT rT maxl ins.
    phi C sig ! pc = Some (ST,LT) \<and> 
    method (G,C) sig = Some(C,rT,(maxl,ins)) \<and>
	(\<exists>C' mn pTs k. pc = k+1 \<and> ins!k = (Invoke C' mn pTs) \<and>
         (mn,pTs) = sig0 \<and> 
         (\<exists>apTs D ST' LT'.
         (phi C sig)!k = Some ((rev apTs) @ (Class D) # ST', LT') \<and>
         length apTs = length pTs \<and>
         (\<exists>D' rT' maxl' ins'.
           method (G,D) sig0 = Some(D',rT',(maxl',ins')) \<and>
           G \<turnstile> rT0 \<preceq> rT') \<and>
	 correct_frame G hp (tl ST, LT) maxl ins f \<and> 
	 correct_frames G hp phi rT sig frs))))"


constdefs
 correct_state :: "[jvm_prog,prog_type,jvm_state] \<Rightarrow> bool"
                  ("_,_\<turnstile>JVM _\<surd>"  [51,51] 50)
"correct_state G phi \<equiv> \<lambda>(xp,hp,frs).
   case xp of
     None \<Rightarrow> (case frs of
	           [] \<Rightarrow> True
             | (f#fs) \<Rightarrow> G\<turnstile>h hp\<surd> \<and>
			(let (stk,loc,C,sig,pc) = f
		         in
                         \<exists>rT maxl ins s.
                         method (G,C) sig = Some(C,rT,(maxl,ins)) \<and>
                         phi C sig ! pc = Some s \<and>
			 correct_frame G hp s maxl ins f \<and> 
		         correct_frames G hp phi rT sig fs))
   | Some x \<Rightarrow> True" 


lemma sup_heap_newref:
  "hp x = None \<Longrightarrow> hp \<le>| hp(newref hp \<mapsto> obj)"
apply (unfold hext_def)
apply clarsimp
apply (drule newref_None 1) back
apply simp
.

lemma sup_heap_update_value:
  "hp a = Some (C,od') \<Longrightarrow> hp \<le>| hp (a \<mapsto> (C,od))"
by (simp add: hext_def)


(** approx_val **)

lemma approx_val_Err:
  "approx_val G hp x Err"
by (simp add: approx_val_def)

lemma approx_val_Null:
  "approx_val G hp Null (Ok (RefT x))"
by (auto intro: null simp add: approx_val_def)

lemma approx_val_imp_approx_val_assConvertible [rulified]: 
  "wf_prog wt G \<Longrightarrow> approx_val G hp v (Ok T) \<longrightarrow> G\<turnstile> T\<preceq>T' \<longrightarrow> approx_val G hp v (Ok T')"
by (cases T) (auto intro: conf_widen simp add: approx_val_def)

lemma approx_val_imp_approx_val_sup_heap [rulified]:
  "approx_val G hp v at \<longrightarrow> hp \<le>| hp' \<longrightarrow> approx_val G hp' v at"
apply (simp add: approx_val_def split: err.split)
apply (blast intro: conf_hext)
.

lemma approx_val_imp_approx_val_heap_update:
  "\<lbrakk>hp a = Some obj'; G,hp\<turnstile> v\<Colon>\<preceq>T; obj_ty obj = obj_ty obj'\<rbrakk> 
  \<Longrightarrow> G,hp(a\<mapsto>obj)\<turnstile> v\<Colon>\<preceq>T"
by (cases v, auto simp add: obj_ty_def conf_def)

lemma approx_val_imp_approx_val_sup [rulified]:
  "wf_prog wt G \<Longrightarrow> (approx_val G h v us) \<longrightarrow> (G \<turnstile> us <=o us') \<longrightarrow> (approx_val G h v us')"
apply (simp add: sup_PTS_eq approx_val_def split: err.split)
apply (blast intro: conf_widen)
.

lemma approx_loc_imp_approx_val_sup:
  "\<lbrakk>wf_prog wt G; approx_loc G hp loc LT; idx < length LT; v = loc!idx; G \<turnstile> LT!idx <=o at\<rbrakk>
  \<Longrightarrow> approx_val G hp v at"
apply (unfold approx_loc_def)
apply (unfold list_all2_def)
apply (auto intro: approx_val_imp_approx_val_sup simp add: split_def all_set_conv_all_nth)
.


(** approx_loc **)

lemma approx_loc_Cons [iff]:
  "approx_loc G hp (s#xs) (l#ls) = (approx_val G hp s l \<and> approx_loc G hp xs ls)"
by (simp add: approx_loc_def)

lemma assConv_approx_stk_imp_approx_loc [rulified]:
  "wf_prog wt G \<Longrightarrow> (\<forall>tt'\<in>set (zip tys_n ts). tt' \<in> widen G) 
  \<longrightarrow> length tys_n = length ts \<longrightarrow> approx_stk G hp s tys_n \<longrightarrow> 
  approx_loc G hp s (map Ok ts)"
apply (unfold approx_stk_def approx_loc_def list_all2_def)
apply (clarsimp simp add: all_set_conv_all_nth)
apply (rule approx_val_imp_approx_val_assConvertible)
apply auto
.


lemma approx_loc_imp_approx_loc_sup_heap [rulified]:
  "\<forall>lvars. approx_loc G hp lvars lt \<longrightarrow> hp \<le>| hp' \<longrightarrow> approx_loc G hp' lvars lt"
apply (unfold approx_loc_def list_all2_def)
apply (cases lt)
 apply simp
apply clarsimp
apply (rule approx_val_imp_approx_val_sup_heap)
apply auto
.

lemma approx_loc_imp_approx_loc_sup [rulified]:
  "wf_prog wt G \<Longrightarrow> approx_loc G hp lvars lt \<longrightarrow> G \<turnstile> lt <=l lt' \<longrightarrow> approx_loc G hp lvars lt'"
apply (unfold sup_loc_def approx_loc_def list_all2_def)
apply (auto simp add: all_set_conv_all_nth)
apply (auto elim: approx_val_imp_approx_val_sup)
.


lemma approx_loc_imp_approx_loc_subst [rulified]:
  "\<forall>loc idx x X. (approx_loc G hp loc LT) \<longrightarrow> (approx_val G hp x X) 
  \<longrightarrow> (approx_loc G hp (loc[idx:=x]) (LT[idx:=X]))"
apply (unfold approx_loc_def list_all2_def)
apply (auto dest: subsetD [OF set_update_subset_insert] simp add: zip_update)
.


lemmas [cong] = conj_cong 

lemma approx_loc_append [rulified]:
  "\<forall>L1 l2 L2. length l1=length L1 \<longrightarrow> 
  approx_loc G hp (l1@l2) (L1@L2) = (approx_loc G hp l1 L1 \<and> approx_loc G hp l2 L2)"
apply (unfold approx_loc_def list_all2_def)
apply simp
apply blast
.

lemmas [cong del] = conj_cong


(** approx_stk **)

lemma approx_stk_rev_lem:
  "approx_stk G hp (rev s) (rev t) = approx_stk G hp s t"
apply (unfold approx_stk_def approx_loc_def list_all2_def)
apply (auto simp add: zip_rev sym [OF rev_map])
.

lemma approx_stk_rev:
  "approx_stk G hp (rev s) t = approx_stk G hp s (rev t)"
by (auto intro: subst [OF approx_stk_rev_lem])


lemma approx_stk_imp_approx_stk_sup_heap [rulified]:
  "\<forall>lvars. approx_stk G hp lvars lt \<longrightarrow> hp \<le>| hp' \<longrightarrow> approx_stk G hp' lvars lt"
by (auto intro: approx_loc_imp_approx_loc_sup_heap simp add: approx_stk_def)

lemma approx_stk_imp_approx_stk_sup [rulified]:
  "wf_prog wt G \<Longrightarrow> approx_stk G hp lvars st \<longrightarrow> (G \<turnstile> map Ok st <=l (map Ok st')) 
  \<longrightarrow> approx_stk G hp lvars st'" 
by (auto intro: approx_loc_imp_approx_loc_sup simp add: approx_stk_def)

lemma approx_stk_Nil [iff]:
  "approx_stk G hp [] []"
by (simp add: approx_stk_def approx_loc_def)

lemma approx_stk_Cons [iff]:
  "approx_stk G hp (x # stk) (S#ST) = 
   (approx_val G hp x (Ok S) \<and> approx_stk G hp stk ST)"
by (simp add: approx_stk_def approx_loc_def)

lemma approx_stk_Cons_lemma [iff]:
  "approx_stk G hp stk (S#ST') = 
  (\<exists>s stk'. stk = s#stk' \<and> approx_val G hp s (Ok S) \<and> approx_stk G hp stk' ST')"
by (simp add: list_all2_Cons2 approx_stk_def approx_loc_def)

lemma approx_stk_append_lemma:
  "approx_stk G hp stk (S@ST') \<Longrightarrow>
   (\<exists>s stk'. stk = s@stk' \<and> length s = length S \<and> length stk' = length ST' \<and> 
             approx_stk G hp s S \<and> approx_stk G hp stk' ST')"
by (simp add: list_all2_append2 approx_stk_def approx_loc_def)


(** oconf **)

lemma correct_init_obj:
  "\<lbrakk>is_class G C; wf_prog wt G\<rbrakk> \<Longrightarrow> 
  G,h \<turnstile> (C, map_of (map (\<lambda>(f,fT).(f,default_val fT)) (fields(G,C)))) \<surd>"
apply (unfold oconf_def lconf_def)
apply (simp add: map_of_map)
apply (force intro: defval_conf dest: map_of_SomeD is_type_fields)
.


lemma oconf_imp_oconf_field_update [rulified]:
  "\<lbrakk>map_of (fields (G, oT)) FD = Some T; G,hp\<turnstile>v\<Colon>\<preceq>T; G,hp\<turnstile>(oT,fs)\<surd> \<rbrakk>
  \<Longrightarrow> G,hp\<turnstile>(oT, fs(FD\<mapsto>v))\<surd>"
by (simp add: oconf_def lconf_def)


lemma oconf_imp_oconf_heap_newref [rulified]:
"hp x = None \<longrightarrow> G,hp\<turnstile>obj\<surd> \<longrightarrow> G,hp\<turnstile>obj'\<surd> \<longrightarrow> G,(hp(newref hp\<mapsto>obj'))\<turnstile>obj\<surd>"
apply (unfold oconf_def lconf_def)
apply simp
apply (fast intro: conf_hext sup_heap_newref)
.


lemma oconf_imp_oconf_heap_update [rulified]:
  "hp a = Some obj' \<longrightarrow> obj_ty obj' = obj_ty obj'' \<longrightarrow> G,hp\<turnstile>obj\<surd> 
  \<longrightarrow> G,hp(a\<mapsto>obj'')\<turnstile>obj\<surd>"
apply (unfold oconf_def lconf_def)
apply simp
apply (force intro: approx_val_imp_approx_val_heap_update)
.


(** hconf **)


lemma hconf_imp_hconf_newref [rulified]:
  "hp x = None \<longrightarrow> G\<turnstile>h hp\<surd> \<longrightarrow> G,hp\<turnstile>obj\<surd> \<longrightarrow> G\<turnstile>h hp(newref hp\<mapsto>obj)\<surd>"
apply (simp add: hconf_def)
apply (fast intro: oconf_imp_oconf_heap_newref)
.

lemma hconf_imp_hconf_field_update [rulified]:
  "map_of (fields (G, oT)) (F, D) = Some T \<and> hp oloc = Some(oT,fs) \<and> 
  G,hp\<turnstile>v\<Colon>\<preceq>T \<and> G\<turnstile>h hp\<surd> \<longrightarrow> G\<turnstile>h hp(oloc \<mapsto> (oT, fs((F,D)\<mapsto>v)))\<surd>"
apply (simp add: hconf_def)
apply (force intro: oconf_imp_oconf_heap_update oconf_imp_oconf_field_update 
             simp add: obj_ty_def)
.

(** correct_frames **)

lemmas [simp del] = fun_upd_apply

lemma correct_frames_imp_correct_frames_field_update [rulified]:
  "\<forall>rT C sig. correct_frames G hp phi rT sig frs \<longrightarrow> 
  hp a = Some (C,od) \<longrightarrow> map_of (fields (G, C)) fl = Some fd \<longrightarrow> 
  G,hp\<turnstile>v\<Colon>\<preceq>fd 
  \<longrightarrow> correct_frames G (hp(a \<mapsto> (C, od(fl\<mapsto>v)))) phi rT sig frs";
apply (induct frs)
 apply simp
apply (clarsimp simp add: correct_frame_def) (*takes long*)
apply (intro exI conjI)
     apply simp
    apply simp
   apply force
  apply simp
 apply (rule approx_stk_imp_approx_stk_sup_heap)
  apply simp
 apply (rule sup_heap_update_value)
 apply simp
apply (rule approx_loc_imp_approx_loc_sup_heap)
 apply simp
apply (rule sup_heap_update_value)
apply simp
.

lemma correct_frames_imp_correct_frames_newref [rulified]:
  "\<forall>rT C sig. hp x = None \<longrightarrow> correct_frames G hp phi rT sig frs \<and> oconf G hp obj 
  \<longrightarrow> correct_frames G (hp(newref hp \<mapsto> obj)) phi rT sig frs"
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
 apply (rule sup_heap_newref)
 apply simp
apply (rule approx_loc_imp_approx_loc_sup_heap)
 apply simp
apply (rule sup_heap_newref)
apply simp
.

end

