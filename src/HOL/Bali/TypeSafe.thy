(*  Title:      HOL/Bali/TypeSafe.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* The type soundness proof for Java *}

theory TypeSafe = Eval + WellForm + Conform:

section "error free"
 
lemma error_free_halloc:
  assumes halloc: "G\<turnstile>s0 \<midarrow>halloc oi\<succ>a\<rightarrow> s1" and
          error_free_s0: "error_free s0"
  shows "error_free s1"
proof -
  from halloc error_free_s0
  obtain abrupt0 store0 abrupt1 store1
    where eqs: "s0=(abrupt0,store0)" "s1=(abrupt1,store1)" and
          halloc': "G\<turnstile>(abrupt0,store0) \<midarrow>halloc oi\<succ>a\<rightarrow> (abrupt1,store1)" and
          error_free_s0': "error_free (abrupt0,store0)"
    by (cases s0,cases s1) auto
  from halloc' error_free_s0'
  have "error_free (abrupt1,store1)"
  proof (induct)
    case Abrupt 
    then show ?case
      .
  next
    case New
    then show ?case
      by (auto split: split_if_asm)
  qed
  with eqs 
  show ?thesis
    by simp
qed

lemma error_free_sxalloc:
  assumes sxalloc: "G\<turnstile>s0 \<midarrow>sxalloc\<rightarrow> s1" and error_free_s0: "error_free s0"
  shows "error_free s1"
proof -
  from sxalloc error_free_s0
  obtain abrupt0 store0 abrupt1 store1
    where eqs: "s0=(abrupt0,store0)" "s1=(abrupt1,store1)" and
          sxalloc': "G\<turnstile>(abrupt0,store0) \<midarrow>sxalloc\<rightarrow> (abrupt1,store1)" and
          error_free_s0': "error_free (abrupt0,store0)"
    by (cases s0,cases s1) auto
  from sxalloc' error_free_s0'
  have "error_free (abrupt1,store1)"
  proof (induct)
  qed (auto)
  with eqs 
  show ?thesis 
    by simp
qed

lemma error_free_check_field_access_eq:
 "error_free (check_field_access G accC statDeclC fn stat a s)
 \<Longrightarrow> (check_field_access G accC statDeclC fn stat a s) = s"
apply (cases s)
apply (auto simp add: check_field_access_def Let_def error_free_def 
                      abrupt_if_def 
            split: split_if_asm)
done

lemma error_free_check_method_access_eq:
"error_free (check_method_access G accC statT mode sig a' s)
 \<Longrightarrow> (check_method_access G accC statT mode sig a' s) = s"
apply (cases s)
apply (auto simp add: check_method_access_def Let_def error_free_def 
                      abrupt_if_def 
            split: split_if_asm)
done

lemma error_free_FVar_lemma: 
     "error_free s 
       \<Longrightarrow> error_free (abupd (if stat then id else np a) s)"
  by (case_tac s) (auto split: split_if) 

lemma error_free_init_lvars [simp,intro]:
"error_free s \<Longrightarrow> 
  error_free (init_lvars G C sig mode a pvs s)"
by (cases s) (auto simp add: init_lvars_def Let_def split: split_if)

lemma error_free_LVar_lemma:   
"error_free s \<Longrightarrow> error_free (assign (\<lambda>v. supd lupd(vn\<mapsto>v)) w s)"
by (cases s) simp

lemma error_free_throw [simp,intro]:
  "error_free s \<Longrightarrow> error_free (abupd (throw x) s)"
by (cases s) (simp add: throw_def)


section "result conformance"

constdefs
  assign_conforms :: "st \<Rightarrow> (val \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> ty \<Rightarrow> env_ \<Rightarrow> bool"
          ("_\<le>|_\<preceq>_\<Colon>\<preceq>_"                                        [71,71,71,71] 70)
"s\<le>|f\<preceq>T\<Colon>\<preceq>E \<equiv>
 (\<forall>s' w. Norm s'\<Colon>\<preceq>E \<longrightarrow> fst E,s'\<turnstile>w\<Colon>\<preceq>T \<longrightarrow> s\<le>|s' \<longrightarrow> assign f w (Norm s')\<Colon>\<preceq>E) \<and>
 (\<forall>s' w. error_free s' \<longrightarrow> (error_free (assign f w s')))"      

  rconf :: "prog \<Rightarrow> lenv \<Rightarrow> st \<Rightarrow> term \<Rightarrow> vals \<Rightarrow> tys \<Rightarrow> bool"
          ("_,_,_\<turnstile>_\<succ>_\<Colon>\<preceq>_"                               [71,71,71,71,71,71] 70)
  "G,L,s\<turnstile>t\<succ>v\<Colon>\<preceq>T 
    \<equiv> case T of
        Inl T  \<Rightarrow> if (\<exists>vf. t=In2 vf)
                  then G,s\<turnstile>fst (the_In2 v)\<Colon>\<preceq>T \<and> s\<le>|snd (the_In2 v)\<preceq>T\<Colon>\<preceq>(G,L)
                  else G,s\<turnstile>the_In1 v\<Colon>\<preceq>T
      | Inr Ts \<Rightarrow> list_all2 (conf G s) (the_In3 v) Ts"

lemma rconf_In1 [simp]: 
 "G,L,s\<turnstile>In1 ec\<succ>In1 v \<Colon>\<preceq>Inl T  =  G,s\<turnstile>v\<Colon>\<preceq>T"
apply (unfold rconf_def)
apply (simp (no_asm))
done

lemma rconf_In2 [simp]: 
 "G,L,s\<turnstile>In2 va\<succ>In2 vf\<Colon>\<preceq>Inl T  = (G,s\<turnstile>fst vf\<Colon>\<preceq>T \<and> s\<le>|snd vf\<preceq>T\<Colon>\<preceq>(G,L))"
apply (unfold rconf_def)
apply (simp (no_asm))
done

lemma rconf_In3 [simp]: 
 "G,L,s\<turnstile>In3 es\<succ>In3 vs\<Colon>\<preceq>Inr Ts = list_all2 (\<lambda>v T. G,s\<turnstile>v\<Colon>\<preceq>T) vs Ts"
apply (unfold rconf_def)
apply (simp (no_asm))
done

section "fits and conf"

(* unused *)
lemma conf_fits: "G,s\<turnstile>v\<Colon>\<preceq>T \<Longrightarrow> G,s\<turnstile>v fits T"
apply (unfold fits_def)
apply clarify
apply (erule swap, simp (no_asm_use))
apply (drule conf_RefTD)
apply auto
done

lemma fits_conf: 
  "\<lbrakk>G,s\<turnstile>v\<Colon>\<preceq>T; G\<turnstile>T\<preceq>? T'; G,s\<turnstile>v fits T'; ws_prog G\<rbrakk> \<Longrightarrow> G,s\<turnstile>v\<Colon>\<preceq>T'"
apply (auto dest!: fitsD cast_PrimT2 cast_RefT2)
apply (force dest: conf_RefTD intro: conf_AddrI)
done

lemma fits_Array: 
 "\<lbrakk>G,s\<turnstile>v\<Colon>\<preceq>T; G\<turnstile>T'.[]\<preceq>T.[]; G,s\<turnstile>v fits T'; ws_prog G\<rbrakk> \<Longrightarrow> G,s\<turnstile>v\<Colon>\<preceq>T'"
apply (auto dest!: fitsD widen_ArrayPrimT widen_ArrayRefT)
apply (force dest: conf_RefTD intro: conf_AddrI)
done



section "gext"

lemma halloc_gext: "\<And>s1 s2. G\<turnstile>s1 \<midarrow>halloc oi\<succ>a\<rightarrow> s2 \<Longrightarrow> snd s1\<le>|snd s2"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule halloc.induct)
apply  (auto dest!: new_AddrD)
done

lemma sxalloc_gext: "\<And>s1 s2. G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2 \<Longrightarrow> snd s1\<le>|snd s2"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule sxalloc.induct)
apply   (auto dest!: halloc_gext)
done

lemma eval_gext_lemma [rule_format (no_asm)]: 
 "G\<turnstile>s \<midarrow>t\<succ>\<rightarrow> (w,s') \<Longrightarrow> snd s\<le>|snd s' \<and> (case w of  
    In1 v \<Rightarrow> True  
  | In2 vf \<Rightarrow> normal s \<longrightarrow> (\<forall>v x s. s\<le>|snd (assign (snd vf) v (x,s)))  
  | In3 vs \<Rightarrow> True)"
apply (erule eval_induct)
prefer 26 
  apply (case_tac "inited C (globs s0)", clarsimp, erule thin_rl) (* Init *)
apply (auto del: conjI  dest!: not_initedD gext_new sxalloc_gext halloc_gext
 simp  add: lvar_def fvar_def2 avar_def2 init_lvars_def2 
            check_field_access_def check_method_access_def Let_def
 split del: split_if_asm split add: sum3.split)
(* 6 subgoals *)
apply force+
done

lemma evar_gext_f: 
  "G\<turnstile>Norm s1 \<midarrow>e=\<succ>vf \<rightarrow> s2 \<Longrightarrow> s\<le>|snd (assign (snd vf) v (x,s))"
apply (drule eval_gext_lemma [THEN conjunct2])
apply auto
done

lemmas eval_gext = eval_gext_lemma [THEN conjunct1]

lemma eval_gext': "G\<turnstile>(x1,s1) \<midarrow>t\<succ>\<rightarrow> (w,x2,s2) \<Longrightarrow> s1\<le>|s2"
apply (drule eval_gext)
apply auto
done

lemma init_yields_initd: "G\<turnstile>Norm s1 \<midarrow>Init C\<rightarrow> s2 \<Longrightarrow> initd C s2"
apply (erule eval_cases , auto split del: split_if_asm)
apply (case_tac "inited C (globs s1)")
apply  (clarsimp split del: split_if_asm)+
apply (drule eval_gext')+
apply (drule init_class_obj_inited)
apply (erule inited_gext)
apply (simp (no_asm_use))
done


section "Lemmas"

lemma obj_ty_obj_class1: 
 "\<lbrakk>wf_prog G; is_type G (obj_ty obj)\<rbrakk> \<Longrightarrow> is_class G (obj_class obj)"
apply (case_tac "tag obj")
apply (auto simp add: obj_ty_def obj_class_def)
done

lemma oconf_init_obj: 
 "\<lbrakk>wf_prog G;  
 (case r of Heap a \<Rightarrow> is_type G (obj_ty obj) | Stat C \<Rightarrow> is_class G C)
\<rbrakk> \<Longrightarrow> G,s\<turnstile>obj \<lparr>values:=init_vals (var_tys G (tag obj) r)\<rparr>\<Colon>\<preceq>\<surd>r"
apply (auto intro!: oconf_init_obj_lemma unique_fields)
done

(*
lemma obj_split: "P obj = (\<forall> oi vs. obj = \<lparr>tag=oi,values=vs\<rparr> \<longrightarrow> ?P \<lparr>tag=oi,values=vs\<rparr>)"
apply auto
apply (case_tac "obj")
apply auto
*)

lemma conforms_newG: "\<lbrakk>globs s oref = None; (x, s)\<Colon>\<preceq>(G,L);   
  wf_prog G; case oref of Heap a \<Rightarrow> is_type G (obj_ty \<lparr>tag=oi,values=vs\<rparr>)  
                        | Stat C \<Rightarrow> is_class G C\<rbrakk> \<Longrightarrow>  
  (x, init_obj G oi oref s)\<Colon>\<preceq>(G, L)"
apply (unfold init_obj_def)
apply (auto elim!: conforms_gupd dest!: oconf_init_obj 
            simp add: obj.update_defs)
done

lemma conforms_init_class_obj: 
 "\<lbrakk>(x,s)\<Colon>\<preceq>(G, L); wf_prog G; class G C=Some y; \<not> inited C (globs s)\<rbrakk> \<Longrightarrow> 
  (x,init_class_obj G C s)\<Colon>\<preceq>(G, L)"
apply (rule not_initedD [THEN conforms_newG])
apply    (auto)
done


lemma fst_init_lvars[simp]: 
 "fst (init_lvars G C sig (invmode m e) a' pvs (x,s)) = 
  (if is_static m then x else (np a') x)"
apply (simp (no_asm) add: init_lvars_def2)
done


lemma halloc_conforms: "\<And>s1. \<lbrakk>G\<turnstile>s1 \<midarrow>halloc oi\<succ>a\<rightarrow> s2; wf_prog G; s1\<Colon>\<preceq>(G, L); 
  is_type G (obj_ty \<lparr>tag=oi,values=fs\<rparr>)\<rbrakk> \<Longrightarrow> s2\<Colon>\<preceq>(G, L)"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (case_tac "aa")
apply  (auto elim!: halloc_elim_cases dest!: new_AddrD 
       intro!: conforms_newG [THEN conforms_xconf] conf_AddrI)
done

lemma halloc_type_sound: 
"\<And>s1. \<lbrakk>G\<turnstile>s1 \<midarrow>halloc oi\<succ>a\<rightarrow> (x,s); wf_prog G; s1\<Colon>\<preceq>(G, L);
  T = obj_ty \<lparr>tag=oi,values=fs\<rparr>; is_type G T\<rbrakk> \<Longrightarrow>  
  (x,s)\<Colon>\<preceq>(G, L) \<and> (x = None \<longrightarrow> G,s\<turnstile>Addr a\<Colon>\<preceq>T)"
apply (auto elim!: halloc_conforms)
apply (case_tac "aa")
apply (subst obj_ty_eq)
apply  (auto elim!: halloc_elim_cases dest!: new_AddrD intro!: conf_AddrI)
done

lemma sxalloc_type_sound: 
 "\<And>s1 s2. \<lbrakk>G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2; wf_prog G\<rbrakk> \<Longrightarrow> case fst s1 of  
  None \<Rightarrow> s2 = s1 | Some x \<Rightarrow>  
  (\<exists>a. fst s2 = Some(Xcpt (Loc a)) \<and> (\<forall>L. s1\<Colon>\<preceq>(G,L) \<longrightarrow> s2\<Colon>\<preceq>(G,L)))"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule sxalloc.induct)
apply   auto
apply (rule halloc_conforms [THEN conforms_xconf])
apply     (auto elim!: halloc_elim_cases dest!: new_AddrD intro!: conf_AddrI)
done

lemma wt_init_comp_ty: 
"is_acc_type G (pid C) T \<Longrightarrow> \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>init_comp_ty T\<Colon>\<surd>"
apply (unfold init_comp_ty_def)
apply (clarsimp simp add: accessible_in_RefT_simp 
                          is_acc_type_def is_acc_class_def)
done


declare fun_upd_same [simp]

declare fun_upd_apply [simp del]


constdefs
  DynT_prop::"[prog,inv_mode,qtname,ref_ty] \<Rightarrow> bool" 
                                              ("_\<turnstile>_\<rightarrow>_\<preceq>_"[71,71,71,71]70)
 "G\<turnstile>mode\<rightarrow>D\<preceq>t \<equiv> mode = IntVir \<longrightarrow> is_class G D \<and> 
                     (if (\<exists>T. t=ArrayT T) then D=Object else G\<turnstile>Class D\<preceq>RefT t)"

lemma DynT_propI: 
 "\<lbrakk>(x,s)\<Colon>\<preceq>(G, L); G,s\<turnstile>a'\<Colon>\<preceq>RefT statT; wf_prog G; mode = IntVir \<longrightarrow> a' \<noteq> Null\<rbrakk> 
  \<Longrightarrow>  G\<turnstile>mode\<rightarrow>invocation_class mode s a' statT\<preceq>statT"
proof (unfold DynT_prop_def)
  assume state_conform: "(x,s)\<Colon>\<preceq>(G, L)"
     and      statT_a': "G,s\<turnstile>a'\<Colon>\<preceq>RefT statT"
     and            wf: "wf_prog G"
     and          mode: "mode = IntVir \<longrightarrow> a' \<noteq> Null"
  let ?invCls = "(invocation_class mode s a' statT)"
  let ?IntVir = "mode = IntVir"
  let ?Concl  = "\<lambda>invCls. is_class G invCls \<and>
                          (if \<exists>T. statT = ArrayT T
                                  then invCls = Object
                                  else G\<turnstile>Class invCls\<preceq>RefT statT)"
  show "?IntVir \<longrightarrow> ?Concl ?invCls"
  proof  
    assume modeIntVir: ?IntVir 
    with mode have not_Null: "a' \<noteq> Null" ..
    from statT_a' not_Null state_conform 
    obtain a obj 
      where obj_props:  "a' = Addr a" "globs s (Inl a) = Some obj"   
                        "G\<turnstile>obj_ty obj\<preceq>RefT statT" "is_type G (obj_ty obj)"
      by (blast dest: conforms_RefTD)
    show "?Concl ?invCls"
    proof (cases "tag obj")
      case CInst
      with modeIntVir obj_props
      show ?thesis 
	by (auto dest!: widen_Array2 split add: split_if)
    next
      case Arr
      from Arr obtain T where "obj_ty obj = T.[]" by (blast dest: obj_ty_Arr1)
      moreover from Arr have "obj_class obj = Object" 
	by (blast dest: obj_class_Arr1)
      moreover note modeIntVir obj_props wf 
      ultimately show ?thesis by (auto dest!: widen_Array )
    qed
  qed
qed

lemma invocation_methd:
"\<lbrakk>wf_prog G; statT \<noteq> NullT; 
 (\<forall> statC. statT = ClassT statC \<longrightarrow> is_class G statC);
 (\<forall>     I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> mode \<noteq> SuperM);
 (\<forall>     T. statT = ArrayT T \<longrightarrow> mode \<noteq> SuperM);
 G\<turnstile>mode\<rightarrow>invocation_class mode s a' statT\<preceq>statT;  
 dynlookup G statT (invocation_class mode s a' statT) sig = Some m \<rbrakk> 
\<Longrightarrow> methd G (invocation_declclass G mode s a' statT sig) sig = Some m"
proof -
  assume         wf: "wf_prog G"
     and  not_NullT: "statT \<noteq> NullT"
     and statC_prop: "(\<forall> statC. statT = ClassT statC \<longrightarrow> is_class G statC)"
     and statI_prop: "(\<forall> I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> mode \<noteq> SuperM)"
     and statA_prop: "(\<forall>     T. statT = ArrayT T \<longrightarrow> mode \<noteq> SuperM)"
     and  invC_prop: "G\<turnstile>mode\<rightarrow>invocation_class mode s a' statT\<preceq>statT"
     and  dynlookup: "dynlookup G statT (invocation_class mode s a' statT) sig 
                      = Some m"
  show ?thesis
  proof (cases statT)
    case NullT
    with not_NullT show ?thesis by simp
  next
    case IfaceT
    with statI_prop obtain I 
      where    statI: "statT = IfaceT I" and 
            is_iface: "is_iface G I"     and
          not_SuperM: "mode \<noteq> SuperM" by blast            
    
    show ?thesis 
    proof (cases mode)
      case Static
      with wf dynlookup statI is_iface 
      show ?thesis
	by (auto simp add: invocation_declclass_def dynlookup_def 
                           dynimethd_def dynmethd_C_C 
	            intro: dynmethd_declclass
	            dest!: wf_imethdsD
                     dest: table_of_map_SomeI
                    split: split_if_asm)
    next	
      case SuperM
      with not_SuperM show ?thesis ..
    next
      case IntVir
      with wf dynlookup IfaceT invC_prop show ?thesis 
	by (auto simp add: invocation_declclass_def dynlookup_def dynimethd_def
                           DynT_prop_def
	            intro: methd_declclass dynmethd_declclass
	            split: split_if_asm)
    qed
  next
    case ClassT
    show ?thesis
    proof (cases mode)
      case Static
      with wf ClassT dynlookup statC_prop 
      show ?thesis by (auto simp add: invocation_declclass_def dynlookup_def
                               intro: dynmethd_declclass)
    next
      case SuperM
      with wf ClassT dynlookup statC_prop 
      show ?thesis by (auto simp add: invocation_declclass_def dynlookup_def
                               intro: dynmethd_declclass)
    next
      case IntVir
      with wf ClassT dynlookup statC_prop invC_prop 
      show ?thesis
	by (auto simp add: invocation_declclass_def dynlookup_def dynimethd_def
                           DynT_prop_def
	            intro: dynmethd_declclass)
    qed
  next
    case ArrayT
    show ?thesis
    proof (cases mode)
      case Static
      with wf ArrayT dynlookup show ?thesis
	by (auto simp add: invocation_declclass_def dynlookup_def 
                           dynimethd_def dynmethd_C_C
                    intro: dynmethd_declclass
                     dest: table_of_map_SomeI)
    next
      case SuperM
      with ArrayT statA_prop show ?thesis by blast
    next
      case IntVir
      with wf ArrayT dynlookup invC_prop show ?thesis
	by (auto simp add: invocation_declclass_def dynlookup_def dynimethd_def
                           DynT_prop_def dynmethd_C_C
                    intro: dynmethd_declclass
                     dest: table_of_map_SomeI)
    qed
  qed
qed

lemma DynT_mheadsD: 
"\<lbrakk>G\<turnstile>invmode sm e\<rightarrow>invC\<preceq>statT; 
  wf_prog G; \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT; 
  (statDeclT,sm) \<in> mheads G C statT sig; 
  invC = invocation_class (invmode sm e) s a' statT;
  declC =invocation_declclass G (invmode sm e) s a' statT sig
 \<rbrakk> \<Longrightarrow> 
  \<exists> dm. 
  methd G declC sig = Some dm \<and> dynlookup G statT invC sig = Some dm  \<and> 
  G\<turnstile>resTy (mthd dm)\<preceq>resTy sm \<and> 
  wf_mdecl G declC (sig, mthd dm) \<and>
  declC = declclass dm \<and>
  is_static dm = is_static sm \<and>  
  is_class G invC \<and> is_class G declC  \<and> G\<turnstile>invC\<preceq>\<^sub>C declC \<and>  
  (if invmode sm e = IntVir
      then (\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>invC \<preceq>\<^sub>C statC)
      else (  (\<exists> statC. statT=ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C declC)
            \<or> (\<forall> statC. statT\<noteq>ClassT statC \<and> declC=Object)) \<and> 
            statDeclT = ClassT (declclass dm))"
proof -
  assume invC_prop: "G\<turnstile>invmode sm e\<rightarrow>invC\<preceq>statT" 
     and        wf: "wf_prog G" 
     and      wt_e: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT"
     and        sm: "(statDeclT,sm) \<in> mheads G C statT sig" 
     and      invC: "invC = invocation_class (invmode sm e) s a' statT"
     and     declC: "declC = 
                    invocation_declclass G (invmode sm e) s a' statT sig"
  from wt_e wf have type_statT: "is_type G (RefT statT)"
    by (auto dest: ty_expr_is_type)
  from sm have not_Null: "statT \<noteq> NullT" by auto
  from type_statT 
  have wf_C: "(\<forall> statC. statT = ClassT statC \<longrightarrow> is_class G statC)"
    by (auto)
  from type_statT wt_e 
  have wf_I: "(\<forall>I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> 
                                        invmode sm e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  from wt_e
  have wf_A: "(\<forall>     T. statT = ArrayT T \<longrightarrow> invmode sm e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  show ?thesis
  proof (cases "invmode sm e = IntVir")
    case True
    with invC_prop not_Null
    have invC_prop': " is_class G invC \<and> 
                      (if (\<exists>T. statT=ArrayT T) then invC=Object 
                                              else G\<turnstile>Class invC\<preceq>RefT statT)"
      by (auto simp add: DynT_prop_def) 
    from True 
    have "\<not> is_static sm"
      by (simp add: invmode_IntVir_eq member_is_static_simp)
    with invC_prop' not_Null
    have "G,statT \<turnstile> invC valid_lookup_cls_for (is_static sm)"
      by (cases statT) auto
    with sm wf type_statT obtain dm where
           dm: "dynlookup G statT invC sig = Some dm" and
      resT_dm: "G\<turnstile>resTy (mthd dm)\<preceq>resTy sm"      and
       static: "is_static dm = is_static sm"
      by  - (drule dynamic_mheadsD,force+)
    with declC invC not_Null 
    have declC': "declC = (declclass dm)" 
      by (auto simp add: invocation_declclass_def)
    with wf invC declC not_Null wf_C wf_I wf_A invC_prop dm 
    have dm': "methd G declC sig = Some dm"
      by - (drule invocation_methd,auto)
    from wf dm invC_prop' declC' type_statT 
    have declC_prop: "G\<turnstile>invC \<preceq>\<^sub>C declC \<and> is_class G declC"
      by (auto dest: dynlookup_declC)
    from wf dm' declC_prop declC' 
    have wf_dm: "wf_mdecl G declC (sig,(mthd dm))"
      by (auto dest: methd_wf_mdecl)
    from invC_prop' 
    have statC_prop: "(\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>invC \<preceq>\<^sub>C statC)"
      by auto
    from True dm' resT_dm wf_dm invC_prop' declC_prop statC_prop declC' static
         dm
    show ?thesis by auto
  next
    case False
    with type_statT wf invC not_Null wf_I wf_A
    have invC_prop': "is_class G invC \<and>  
                     ((\<exists> statC. statT=ClassT statC \<and> invC=statC) \<or>
                      (\<forall> statC. statT\<noteq>ClassT statC \<and> invC=Object))"
        by (case_tac "statT") (auto simp add: invocation_class_def 
                                       split: inv_mode.splits)
    with not_Null wf
    have dynlookup_static: "dynlookup G statT invC sig = methd G invC sig"
      by (case_tac "statT") (auto simp add: dynlookup_def dynmethd_C_C
                                            dynimethd_def)
    from sm wf wt_e not_Null False invC_prop' obtain "dm" where
                    dm: "methd G invC sig = Some dm"          and
	eq_declC_sm_dm:"statDeclT = ClassT (declclass dm)"  and
	     eq_mheads:"sm=mhead (mthd dm) "
      by - (drule static_mheadsD, (force dest: accmethd_SomeD)+)
    then have static: "is_static dm = is_static sm" by - (auto)
    with declC invC dynlookup_static dm
    have declC': "declC = (declclass dm)"  
      by (auto simp add: invocation_declclass_def)
    from invC_prop' wf declC' dm 
    have dm': "methd G declC sig = Some dm"
      by (auto intro: methd_declclass)
    from dynlookup_static dm 
    have dm'': "dynlookup G statT invC sig = Some dm"
      by simp
    from wf dm invC_prop' declC' type_statT 
    have declC_prop: "G\<turnstile>invC \<preceq>\<^sub>C declC \<and> is_class G declC"
      by (auto dest: methd_declC )
    then have declC_prop1: "invC=Object \<longrightarrow> declC=Object"  by auto
    from wf dm' declC_prop declC' 
    have wf_dm: "wf_mdecl G declC (sig,(mthd dm))"
      by (auto dest: methd_wf_mdecl)
    from invC_prop' declC_prop declC_prop1
    have statC_prop: "(   (\<exists> statC. statT=ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C declC)
                       \<or>  (\<forall> statC. statT\<noteq>ClassT statC \<and> declC=Object))" 
      by auto
    from False dm' dm'' wf_dm invC_prop' declC_prop statC_prop declC' 
         eq_declC_sm_dm eq_mheads static
    show ?thesis by auto
  qed
qed   

lemma DynT_conf: "\<lbrakk>G\<turnstile>invocation_class mode s a' statT \<preceq>\<^sub>C declC; wf_prog G;
 isrtype G (statT);
 G,s\<turnstile>a'\<Colon>\<preceq>RefT statT; mode = IntVir \<longrightarrow> a' \<noteq> Null;  
  mode \<noteq> IntVir \<longrightarrow>    (\<exists> statC. statT=ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C declC)
                    \<or>  (\<forall> statC. statT\<noteq>ClassT statC \<and> declC=Object)\<rbrakk> 
 \<Longrightarrow>G,s\<turnstile>a'\<Colon>\<preceq> Class declC"
apply (case_tac "mode = IntVir")
apply (drule conf_RefTD)
apply (force intro!: conf_AddrI 
            simp add: obj_class_def split add: obj_tag.split_asm)
apply  clarsimp
apply  safe
apply    (erule (1) widen.subcls [THEN conf_widen])
apply    (erule wf_ws_prog)

apply    (frule widen_Object) apply (erule wf_ws_prog)
apply    (erule (1) conf_widen) apply (erule wf_ws_prog)
done

lemma Ass_lemma:
"\<lbrakk> G\<turnstile>Norm s0 \<midarrow>var=\<succ>(w, f)\<rightarrow> Norm s1; G\<turnstile>Norm s1 \<midarrow>e-\<succ>v\<rightarrow> Norm s2;
   G,s2\<turnstile>v\<Colon>\<preceq>eT;s1\<le>|s2 \<longrightarrow> assign f v (Norm s2)\<Colon>\<preceq>(G, L)\<rbrakk>
\<Longrightarrow> assign f v (Norm s2)\<Colon>\<preceq>(G, L) \<and>
      (normal (assign f v (Norm s2)) \<longrightarrow> G,store (assign f v (Norm s2))\<turnstile>v\<Colon>\<preceq>eT)"
apply (drule_tac x = "None" and s = "s2" and v = "v" in evar_gext_f)
apply (drule eval_gext', clarsimp)
apply (erule conf_gext)
apply simp
done

lemma Throw_lemma: "\<lbrakk>G\<turnstile>tn\<preceq>\<^sub>C SXcpt Throwable; wf_prog G; (x1,s1)\<Colon>\<preceq>(G, L);  
    x1 = None \<longrightarrow> G,s1\<turnstile>a'\<Colon>\<preceq> Class tn\<rbrakk> \<Longrightarrow> (throw a' x1, s1)\<Colon>\<preceq>(G, L)"
apply (auto split add: split_abrupt_if simp add: throw_def2)
apply (erule conforms_xconf)
apply (frule conf_RefTD)
apply (auto elim: widen.subcls [THEN conf_widen])
done

lemma Try_lemma: "\<lbrakk>G\<turnstile>obj_ty (the (globs s1' (Heap a)))\<preceq> Class tn; 
 (Some (Xcpt (Loc a)), s1')\<Colon>\<preceq>(G, L); wf_prog G\<rbrakk> 
 \<Longrightarrow> Norm (lupd(vn\<mapsto>Addr a) s1')\<Colon>\<preceq>(G, L(vn\<mapsto>Class tn))"
apply (rule conforms_allocL)
apply  (erule conforms_NormI)
apply (drule conforms_XcptLocD [THEN conf_RefTD],rule HOL.refl)
apply (auto intro!: conf_AddrI)
done

lemma Fin_lemma: 
"\<lbrakk>G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> (x2,s2); wf_prog G; (Some a, s1)\<Colon>\<preceq>(G, L); (x2,s2)\<Colon>\<preceq>(G, L)\<rbrakk> 
\<Longrightarrow>  (abrupt_if True (Some a) x2, s2)\<Colon>\<preceq>(G, L)"
apply (force elim: eval_gext' conforms_xgext split add: split_abrupt_if)
done

lemma FVar_lemma1: 
"\<lbrakk>table_of (DeclConcepts.fields G statC) (fn, statDeclC) = Some f ; 
  x2 = None \<longrightarrow> G,s2\<turnstile>a\<Colon>\<preceq> Class statC; wf_prog G; G\<turnstile>statC\<preceq>\<^sub>C statDeclC; 
  statDeclC \<noteq> Object; 
  class G statDeclC = Some y; (x2,s2)\<Colon>\<preceq>(G, L); s1\<le>|s2; 
  inited statDeclC (globs s1); 
  (if static f then id else np a) x2 = None\<rbrakk> 
 \<Longrightarrow>  
  \<exists>obj. globs s2 (if static f then Inr statDeclC else Inl (the_Addr a)) 
                  = Some obj \<and> 
  var_tys G (tag obj)  (if static f then Inr statDeclC else Inl(the_Addr a)) 
          (Inl(fn,statDeclC)) = Some (type f)"
apply (drule initedD)
apply (frule subcls_is_class2, simp (no_asm_simp))
apply (case_tac "static f")
apply  clarsimp
apply  (drule (1) rev_gext_objD, clarsimp)
apply  (frule fields_declC, erule wf_ws_prog, simp (no_asm_simp))
apply  (rule var_tys_Some_eq [THEN iffD2])
apply  clarsimp
apply  (erule fields_table_SomeI, simp (no_asm))
apply clarsimp
apply (drule conf_RefTD, clarsimp, rule var_tys_Some_eq [THEN iffD2])
apply (auto dest!: widen_Array split add: obj_tag.split)
apply (rotate_tac -1) (* to front: tag obja = CInst pid_field_type to enable
                         conditional rewrite *)
apply (rule fields_table_SomeI)
apply (auto elim!: fields_mono subcls_is_class2)
done

lemma FVar_lemma2: "error_free state
       \<Longrightarrow> error_free
           (assign
             (\<lambda>v. supd
                   (upd_gobj
                     (if static field then Inr statDeclC
                      else Inl (the_Addr a))
                     (Inl (fn, statDeclC)) v))
             w state)"
proof -
  assume error_free: "error_free state"
  obtain a s where "state=(a,s)"
    by (cases state) simp
  with error_free
  show ?thesis
    by (cases a) auto
qed

declare split_paired_All [simp del] split_paired_Ex [simp del] 
declare split_if     [split del] split_if_asm     [split del] 
        option.split [split del] option.split_asm [split del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac";
claset_ref () := claset () delSWrapper "split_all_tac"
*}
lemma FVar_lemma: 
"\<lbrakk>((v, f), Norm s2') = fvar statDeclC (static field) fn a (x2, s2); 
  G\<turnstile>statC\<preceq>\<^sub>C statDeclC;  
  table_of (DeclConcepts.fields G statC) (fn, statDeclC) = Some field; 
  wf_prog G;   
  x2 = None \<longrightarrow> G,s2\<turnstile>a\<Colon>\<preceq>Class statC; 
  statDeclC \<noteq> Object; class G statDeclC = Some y;   
  (x2, s2)\<Colon>\<preceq>(G, L); s1\<le>|s2; inited statDeclC (globs s1)\<rbrakk> \<Longrightarrow>  
  G,s2'\<turnstile>v\<Colon>\<preceq>type field \<and> s2'\<le>|f\<preceq>type field\<Colon>\<preceq>(G, L)"
apply (unfold assign_conforms_def)
apply (drule sym)
apply (clarsimp simp add: fvar_def2)
apply (drule (9) FVar_lemma1)
apply (clarsimp)
apply (drule (2) conforms_globsD [THEN oconf_lconf, THEN lconfD])
apply clarsimp
apply (rule conjI)
apply   clarsimp
apply   (drule (1) rev_gext_objD)
apply   (force elim!: conforms_upd_gobj)

apply   (blast intro: FVar_lemma2)
done
declare split_paired_All [simp] split_paired_Ex [simp] 
declare split_if     [split] split_if_asm     [split] 
        option.split [split] option.split_asm [split]
ML_setup {*
claset_ref()  := claset() addSbefore ("split_all_tac", split_all_tac);
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}


lemma AVar_lemma1: "\<lbrakk>globs s (Inl a) = Some obj;tag obj=Arr ty i; 
 the_Intg i' in_bounds i; wf_prog G; G\<turnstile>ty.[]\<preceq>Tb.[]; Norm s\<Colon>\<preceq>(G, L)
\<rbrakk> \<Longrightarrow> G,s\<turnstile>the ((values obj) (Inr (the_Intg i')))\<Colon>\<preceq>Tb"
apply (erule widen_Array_Array [THEN conf_widen])
apply  (erule_tac [2] wf_ws_prog)
apply (drule (1) conforms_globsD [THEN oconf_lconf, THEN lconfD])
defer apply assumption
apply (force intro: var_tys_Some_eq [THEN iffD2])
done

lemma obj_split: "\<And> obj. \<exists> t vs. obj = \<lparr>tag=t,values=vs\<rparr>"
proof record_split
  fix tag values more
  show "\<exists>t vs. \<lparr>tag = tag, values = values, \<dots> = more\<rparr> = \<lparr>tag = t, values = vs\<rparr>"
    by auto
qed
 
lemma AVar_lemma2: "error_free state 
       \<Longrightarrow> error_free
           (assign
             (\<lambda>v (x, s').
                 ((raise_if (\<not> G,s'\<turnstile>v fits T) ArrStore) x,
                  upd_gobj (Inl a) (Inr (the_Intg i)) v s'))
             w state)"
proof -
  assume error_free: "error_free state"
  obtain a s where "state=(a,s)"
    by (cases state) simp
  with error_free
  show ?thesis
    by (cases a) auto
qed

lemma AVar_lemma: "\<lbrakk>wf_prog G; G\<turnstile>(x1, s1) \<midarrow>e2-\<succ>i\<rightarrow> (x2, s2);  
  ((v,f), Norm s2') = avar G i a (x2, s2); x1 = None \<longrightarrow> G,s1\<turnstile>a\<Colon>\<preceq>Ta.[];  
  (x2, s2)\<Colon>\<preceq>(G, L); s1\<le>|s2\<rbrakk> \<Longrightarrow> G,s2'\<turnstile>v\<Colon>\<preceq>Ta \<and> s2'\<le>|f\<preceq>Ta\<Colon>\<preceq>(G, L)"
apply (unfold assign_conforms_def)
apply (drule sym)
apply (clarsimp simp add: avar_def2)
apply (drule (1) conf_gext)
apply (drule conf_RefTD, clarsimp)
apply (subgoal_tac "\<exists> t vs. obj = \<lparr>tag=t,values=vs\<rparr>")
defer
apply   (rule obj_split)
apply clarify
apply (frule obj_ty_widenD)
apply (auto dest!: widen_Class)
apply   (force dest: AVar_lemma1)

apply   (force elim!: fits_Array dest: gext_objD 
         intro: var_tys_Some_eq [THEN iffD2] conforms_upd_gobj)
done

section "Call"

lemma conforms_init_lvars_lemma: "\<lbrakk>wf_prog G;  
  wf_mhead G P sig mh; 
  Ball (set lvars) (split (\<lambda>vn. is_type G)); 
  list_all2 (conf G s) pvs pTsa; G\<turnstile>pTsa[\<preceq>](parTs sig)\<rbrakk> \<Longrightarrow>  
  G,s\<turnstile>init_vals (table_of lvars)(pars mh[\<mapsto>]pvs)
      [\<Colon>\<preceq>]table_of lvars(pars mh[\<mapsto>]parTs sig)"
apply (unfold wf_mhead_def)
apply clarify
apply (erule (2) Ball_set_table [THEN lconf_init_vals, THEN lconf_ext_list])
apply (drule wf_ws_prog)
apply (erule (2) conf_list_widen)
done


lemma lconf_map_lname [simp]: 
  "G,s\<turnstile>(lname_case l1 l2)[\<Colon>\<preceq>](lname_case L1 L2)
   =
  (G,s\<turnstile>l1[\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>(\<lambda>x::unit . l2)[\<Colon>\<preceq>](\<lambda>x::unit. L2))"
apply (unfold lconf_def)
apply safe
apply (case_tac "n")
apply (force split add: lname.split)+
done

lemma lconf_map_ename [simp]:
  "G,s\<turnstile>(ename_case l1 l2)[\<Colon>\<preceq>](ename_case L1 L2)
   =
  (G,s\<turnstile>l1[\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>(\<lambda>x::unit. l2)[\<Colon>\<preceq>](\<lambda>x::unit. L2))"
apply (unfold lconf_def)
apply safe
apply (force split add: ename.split)+
done


lemma defval_conf1 [rule_format (no_asm), elim]: 
  "is_type G T \<longrightarrow> (\<exists>v\<in>Some (default_val T): G,s\<turnstile>v\<Colon>\<preceq>T)"
apply (unfold conf_def)
apply (induct "T")
apply (auto intro: prim_ty.induct)
done

declare split_paired_All [simp del] split_paired_Ex [simp del] 
declare split_if     [split del] split_if_asm     [split del] 
        option.split [split del] option.split_asm [split del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac";
claset_ref () := claset () delSWrapper "split_all_tac"
*}
lemma conforms_init_lvars: 
"\<lbrakk>wf_mhead G (pid declC) sig (mhead (mthd dm)); wf_prog G;  
  list_all2 (conf G s) pvs pTsa; G\<turnstile>pTsa[\<preceq>](parTs sig);  
  (x, s)\<Colon>\<preceq>(G, L); 
  methd G declC sig = Some dm;  
  isrtype G statT;
  G\<turnstile>invC\<preceq>\<^sub>C declC; 
  G,s\<turnstile>a'\<Colon>\<preceq>RefT statT;  
  invmode (mhd sm) e = IntVir \<longrightarrow> a' \<noteq> Null; 
  invmode (mhd sm) e \<noteq> IntVir \<longrightarrow>  
       (\<exists> statC. statT=ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C declC)
    \<or>  (\<forall> statC. statT\<noteq>ClassT statC \<and> declC=Object);
  invC  = invocation_class (invmode (mhd sm) e) s a' statT;
  declC = invocation_declclass G (invmode (mhd sm) e) s a' statT sig;
  Ball (set (lcls (mbody (mthd dm)))) 
       (split (\<lambda>vn. is_type G)) 
 \<rbrakk> \<Longrightarrow>  
  init_lvars G declC sig (invmode (mhd sm) e) a'  
  pvs (x,s)\<Colon>\<preceq>(G,\<lambda> k. 
                (case k of
                   EName e \<Rightarrow> (case e of 
                                 VNam v 
                                  \<Rightarrow> (table_of (lcls (mbody (mthd dm)))
                                        (pars (mthd dm)[\<mapsto>]parTs sig)) v
                               | Res \<Rightarrow> Some (resTy (mthd dm)))
                 | This \<Rightarrow> if (is_static (mthd sm)) 
                              then None else Some (Class declC)))"
apply (simp add: init_lvars_def2)
apply (rule conforms_set_locals)
apply  (simp (no_asm_simp) split add: split_if)
apply (drule  (4) DynT_conf)
apply clarsimp
(* apply intro *)
apply (drule (4) conforms_init_lvars_lemma)
apply (case_tac "dm",simp)
apply (rule conjI)
apply (unfold lconf_def, clarify)
apply (rule defval_conf1)
apply (clarsimp simp add: wf_mhead_def is_acc_type_def)
apply (case_tac "is_static sm")
apply simp_all
done
declare split_paired_All [simp] split_paired_Ex [simp] 
declare split_if     [split] split_if_asm     [split] 
        option.split [split] option.split_asm [split]
ML_setup {*
claset_ref()  := claset() addSbefore ("split_all_tac", split_all_tac);
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}



subsection "accessibility"

text {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)

(* #### stat raus und gleich is_static f schreiben *) 
theorem dynamic_field_access_ok:
  assumes wf: "wf_prog G" and
    not_Null: "\<not> stat \<longrightarrow> a\<noteq>Null" and
   conform_a: "G,(store s)\<turnstile>a\<Colon>\<preceq> Class statC" and
   conform_s: "s\<Colon>\<preceq>(G, L)" and 
    normal_s: "normal s" and
        wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
           f: "accfield G accC statC fn = Some f" and
        dynC: "if stat then dynC=declclass f  
                       else dynC=obj_class (lookup_obj (store s) a)" and
        stat: "if stat then (is_static f) else (\<not> is_static f)"
  shows "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f) \<and> 
     G\<turnstile>Field fn f in dynC dyn_accessible_from accC"
proof (cases "stat")
  case True
  with stat have static: "(is_static f)" by simp
  from True dynC 
  have dynC': "dynC=declclass f" by simp
  with f
  have "table_of (DeclConcepts.fields G statC) (fn,declclass f) = Some (fld f)"
    by (auto simp add: accfield_def Let_def intro!: table_of_remap_SomeD)
  moreover
  from wt_e wf have "is_class G statC"
    by (auto dest!: ty_expr_is_type)
  moreover note wf dynC'
  ultimately have
     "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f)"
    by (auto dest: fields_declC)
  with dynC' f static wf
  show ?thesis
    by (auto dest: static_to_dynamic_accessible_from_static
            dest!: accfield_accessibleD )
next
  case False
  with wf conform_a not_Null conform_s dynC
  obtain subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
    "is_class G dynC"
    by (auto dest!: conforms_RefTD [of _ _ _ _ "(fst s)" L]
              dest: obj_ty_obj_class1
          simp add: obj_ty_obj_class )
  with wf f
  have "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f)"
    by (auto simp add: accfield_def Let_def
                 dest: fields_mono
                dest!: table_of_remap_SomeD)
  moreover
  from f subclseq
  have "G\<turnstile>Field fn f in dynC dyn_accessible_from accC"
    by (auto intro!: static_to_dynamic_accessible_from 
               dest: accfield_accessibleD)
  ultimately show ?thesis
    by blast
qed

(*
theorem dynamic_field_access_ok:
  (assumes wf: "wf_prog G" and
     not_Null: "\<not> is_static f \<longrightarrow> a\<noteq>Null" and
    conform_a: "G,(store s)\<turnstile>a\<Colon>\<preceq> Class statC" and
    conform_s: "s\<Colon>\<preceq>(G, L)" and 
     normal_s: "normal s" and
         wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
            f: "accfield G accC statC fn = Some f" and
         dynC: "if is_static f 
                   then dynC=declclass f  
                   else dynC=obj_class (lookup_obj (store s) a)" 
  ) "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f) \<and> 
     G\<turnstile>Field fn f in dynC dyn_accessible_from accC"
proof (cases "is_static f")
  case True
  from True dynC 
  have dynC': "dynC=declclass f" by simp
  with f
  have "table_of (DeclConcepts.fields G statC) (fn,declclass f) = Some (fld f)"
    by (auto simp add: accfield_def Let_def intro!: table_of_remap_SomeD)
  moreover
  from wt_e wf have "is_class G statC"
    by (auto dest!: ty_expr_is_type)
  moreover note wf dynC'
  ultimately have
     "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f)"
    by (auto dest: fields_declC)
  with dynC' f True wf
  show ?thesis
    by (auto dest: static_to_dynamic_accessible_from_static
            dest!: accfield_accessibleD )
next
  case False
  with wf conform_a not_Null conform_s dynC
  obtain subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
    "is_class G dynC"
    by (auto dest!: conforms_RefTD [of _ _ _ _ "(fst s)" L]
              dest: obj_ty_obj_class1
          simp add: obj_ty_obj_class )
  with wf f
  have "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f)"
    by (auto simp add: accfield_def Let_def
                 dest: fields_mono
                dest!: table_of_remap_SomeD)
  moreover
  from f subclseq
  have "G\<turnstile>Field fn f in dynC dyn_accessible_from accC"
    by (auto intro!: static_to_dynamic_accessible_from 
               dest: accfield_accessibleD)
  ultimately show ?thesis
    by blast
qed
*)


(* ### Einsetzen in case FVar des TypeSoundness Proofs *)
(*
lemma FVar_check_error_free:
(assumes fvar: "(v, s2') = fvar statDeclC stat fn a s2" and 
        check: "s3 = check_field_access G accC statDeclC fn stat a s2'" and
       conf_a: "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC" and
      conf_s2: "s2\<Colon>\<preceq>(G, L)" and
    initd_statDeclC_s2: "initd statDeclC s2" and
    wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
    accfield: "accfield G accC statC fn = Some (statDeclC,f)" and
    stat: "stat=is_static f" and
      wf: "wf_prog G"
)  "s3=s2'"
proof -
  from fvar 
  have store_s2': "store s2'=store s2"
    by (cases s2) (simp add: fvar_def2)
  with fvar conf_s2 
  have conf_s2': "s2'\<Colon>\<preceq>(G, L)"
    by (cases s2,cases stat) (auto simp add: fvar_def2)
  from initd_statDeclC_s2 store_s2' 
  have initd_statDeclC_s2': "initd statDeclC s2"
    by simp
  show ?thesis
  proof (cases "normal s2'")
    case False
    with check show ?thesis 
      by (auto simp add: check_field_access_def Let_def)
  next
    case True
    with fvar store_s2' 
    have not_Null: "\<not> stat \<longrightarrow> a\<noteq>Null" 
      by (cases s2) (auto simp add: fvar_def2)
    from True fvar store_s2'
    have "normal s2"
      by (cases s2,cases stat) (auto simp add: fvar_def2)
    with conf_a store_s2'
    have conf_a': "G,store s2'\<turnstile>a\<Colon>\<preceq>Class statC"
      by simp 
    from conf_a' conf_s2'  check True initd_statDeclC_s2' 
      dynamic_field_access_ok [OF wf not_Null conf_a' conf_s2' 
                                   True wt_e accfield ] stat
    show ?thesis
      by (cases stat)
         (auto dest!: initedD
           simp add: check_field_access_def Let_def)
  qed
qed
*)

lemma error_free_field_access:
  assumes accfield: "accfield G accC statC fn = Some (statDeclC, f)" and
              wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-Class statC" and
         eval_init: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<rightarrow> s1" and
            eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2" and
           conf_s2: "s2\<Colon>\<preceq>(G, L)" and
            conf_a: "normal s2 \<Longrightarrow> G, store s2\<turnstile>a\<Colon>\<preceq>Class statC" and
              fvar: "(v,s2')=fvar statDeclC (is_static f) fn a s2" and
                wf: "wf_prog G"   
  shows "check_field_access G accC statDeclC fn (is_static f) a s2' = s2'"
proof -
  from fvar
  have store_s2': "store s2'=store s2"
    by (cases s2) (simp add: fvar_def2)
  with fvar conf_s2 
  have conf_s2': "s2'\<Colon>\<preceq>(G, L)"
    by (cases s2,cases "is_static f") (auto simp add: fvar_def2)
  from eval_init 
  have initd_statDeclC_s1: "initd statDeclC s1"
    by (rule init_yields_initd)
  with eval_e store_s2'
  have initd_statDeclC_s2': "initd statDeclC s2'"
    by (auto dest: eval_gext intro: inited_gext)
  show ?thesis
  proof (cases "normal s2'")
    case False
    then show ?thesis 
      by (auto simp add: check_field_access_def Let_def)
  next
    case True
    with fvar store_s2' 
    have not_Null: "\<not> (is_static f) \<longrightarrow> a\<noteq>Null" 
      by (cases s2) (auto simp add: fvar_def2)
    from True fvar store_s2'
    have "normal s2"
      by (cases s2,cases "is_static f") (auto simp add: fvar_def2)
    with conf_a store_s2'
    have conf_a': "G,store s2'\<turnstile>a\<Colon>\<preceq>Class statC"
      by simp
    from conf_a' conf_s2' True initd_statDeclC_s2' 
      dynamic_field_access_ok [OF wf not_Null conf_a' conf_s2' 
                                   True wt_e accfield ] 
    show ?thesis
      by  (cases "is_static f")
          (auto dest!: initedD
           simp add: check_field_access_def Let_def)
  qed
qed

lemma call_access_ok:
  assumes invC_prop: "G\<turnstile>invmode statM e\<rightarrow>invC\<preceq>statT" 
      and        wf: "wf_prog G" 
      and      wt_e: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT"
      and     statM: "(statDeclT,statM) \<in> mheads G accC statT sig" 
      and      invC: "invC = invocation_class (invmode statM e) s a statT"
  shows "\<exists> dynM. dynlookup G statT invC sig = Some dynM \<and>
  G\<turnstile>Methd sig dynM in invC dyn_accessible_from accC"
proof -
  from wt_e wf have type_statT: "is_type G (RefT statT)"
    by (auto dest: ty_expr_is_type)
  from statM have not_Null: "statT \<noteq> NullT" by auto
  from type_statT wt_e 
  have wf_I: "(\<forall>I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> 
                                        invmode statM e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  from wt_e
  have wf_A: "(\<forall>     T. statT = ArrayT T \<longrightarrow> invmode statM e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  show ?thesis
  proof (cases "invmode statM e = IntVir")
    case True
    with invC_prop not_Null
    have invC_prop': "is_class G invC \<and>  
                      (if (\<exists>T. statT=ArrayT T) then invC=Object 
                                              else G\<turnstile>Class invC\<preceq>RefT statT)"
      by (auto simp add: DynT_prop_def)
    with True not_Null
    have "G,statT \<turnstile> invC valid_lookup_cls_for is_static statM"
     by (cases statT) (auto simp add: invmode_def) 
    with statM type_statT wf 
    show ?thesis
      by - (rule dynlookup_access,auto)
  next
    case False
    with type_statT wf invC not_Null wf_I wf_A
    have invC_prop': " is_class G invC \<and>
                      ((\<exists> statC. statT=ClassT statC \<and> invC=statC) \<or>
                      (\<forall> statC. statT\<noteq>ClassT statC \<and> invC=Object)) "
        by (case_tac "statT") (auto simp add: invocation_class_def 
                                       split: inv_mode.splits)
    with not_Null wf
    have dynlookup_static: "dynlookup G statT invC sig = methd G invC sig"
      by (case_tac "statT") (auto simp add: dynlookup_def dynmethd_C_C
                                            dynimethd_def)
   from statM wf wt_e not_Null False invC_prop' obtain dynM where
                "accmethd G accC invC sig = Some dynM" 
     by (auto dest!: static_mheadsD)
   from invC_prop' False not_Null wf_I
   have "G,statT \<turnstile> invC valid_lookup_cls_for is_static statM"
     by (cases statT) (auto simp add: invmode_def) 
   with statM type_statT wf 
    show ?thesis
      by - (rule dynlookup_access,auto)
  qed
qed

lemma error_free_call_access:
  assumes
   eval_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2" and
        wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-(RefT statT)" and  
       statM: "max_spec G accC statT \<lparr>name = mn, parTs = pTs\<rparr> 
               = {((statDeclT, statM), pTs')}" and
     conf_s2: "s2\<Colon>\<preceq>(G, L)" and
      conf_a: "normal s1 \<Longrightarrow> G, store s1\<turnstile>a\<Colon>\<preceq>RefT statT" and
     invProp: "normal s3 \<Longrightarrow>
                G\<turnstile>invmode statM e\<rightarrow>invC\<preceq>statT" and
          s3: "s3=init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> 
                        (invmode statM e) a vs s2" and
        invC: "invC = invocation_class (invmode statM e) (store s2) a statT"and
    invDeclC: "invDeclC = invocation_declclass G (invmode statM e) (store s2) 
                             a statT \<lparr>name = mn, parTs = pTs'\<rparr>" and
          wf: "wf_prog G"
  shows "check_method_access G accC statT (invmode statM e) \<lparr>name=mn,parTs=pTs'\<rparr> a s3
   = s3"
proof (cases "normal s2")
  case False
  with s3 
  have "abrupt s3 = abrupt s2"  
    by (auto simp add: init_lvars_def2)
  with False
  show ?thesis
    by (auto simp add: check_method_access_def Let_def)
next
  case True
  note normal_s2 = True
  with eval_args
  have normal_s1: "normal s1"
    by (cases "normal s1") auto
  with conf_a eval_args 
  have conf_a_s2: "G, store s2\<turnstile>a\<Colon>\<preceq>RefT statT"
    by (auto dest: eval_gext intro: conf_gext)
  show ?thesis
  proof (cases "a=Null \<longrightarrow> (is_static statM)")
    case False
    then obtain "\<not> is_static statM" "a=Null" 
      by blast
    with normal_s2 s3
    have "abrupt s3 = Some (Xcpt (Std NullPointer))" 
      by (auto simp add: init_lvars_def2)
    then show ?thesis
      by (auto simp add: check_method_access_def Let_def)
  next
    case True
    from statM 
    obtain
      statM': "(statDeclT,statM)\<in>mheads G accC statT \<lparr>name=mn,parTs=pTs'\<rparr>" 
      by (blast dest: max_spec2mheads)
    from True normal_s2 s3
    have "normal s3"
      by (auto simp add: init_lvars_def2)
    then have "G\<turnstile>invmode statM e\<rightarrow>invC\<preceq>statT"
      by (rule invProp)
    with wt_e statM' wf invC
    obtain dynM where 
      dynM: "dynlookup G statT invC  \<lparr>name=mn,parTs=pTs'\<rparr> = Some dynM" and
      acc_dynM: "G \<turnstile>Methd  \<lparr>name=mn,parTs=pTs'\<rparr> dynM 
                          in invC dyn_accessible_from accC"
      by (force dest!: call_access_ok)
    moreover
    from s3 invC
    have invC': "invC=(invocation_class (invmode statM e) (store s3) a statT)"
      by (cases s2,cases "invmode statM e") 
         (simp add: init_lvars_def2 del: invmode_Static_eq)+
    ultimately
    show ?thesis
      by (auto simp add: check_method_access_def Let_def)
  qed
qed

section "main proof of type safety"

lemma eval_type_sound:
  assumes eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" and
            wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T" and
            wf: "wf_prog G" and 
       conf_s0: "s0\<Colon>\<preceq>(G,L)"           
  shows "s1\<Colon>\<preceq>(G,L) \<and>  (normal s1 \<longrightarrow> G,L,store s1\<turnstile>t\<succ>v\<Colon>\<preceq>T) \<and> 
         (error_free s0 = error_free s1)"
proof -
  from eval 
  have "\<And> L accC T. \<lbrakk>s0\<Colon>\<preceq>(G,L);\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T\<rbrakk>  
        \<Longrightarrow> s1\<Colon>\<preceq>(G,L) \<and> (normal s1 \<longrightarrow> G,L,store s1\<turnstile>t\<succ>v\<Colon>\<preceq>T)
            \<and> (error_free s0 = error_free s1)"
   (is "PROP ?TypeSafe s0 s1 t v"
    is "\<And> L accC T. ?Conform L s0 \<Longrightarrow> ?WellTyped L accC T t  
                 \<Longrightarrow> ?Conform L s1 \<and> ?ValueTyped L T s1 t v \<and>
                     ?ErrorFree s0 s1")
  proof (induct)
    case (Abrupt s t xc L accC T) 
    have "(Some xc, s)\<Colon>\<preceq>(G,L)" .
    then show "(Some xc, s)\<Colon>\<preceq>(G,L) \<and> 
      (normal (Some xc, s) 
      \<longrightarrow> G,L,store (Some xc,s)\<turnstile>t\<succ>arbitrary3 t\<Colon>\<preceq>T) \<and> 
      (error_free (Some xc, s) = error_free (Some xc, s))"
      by (simp)
  next
    case (Skip s L accC T)
    have "Norm s\<Colon>\<preceq>(G, L)" and  
           "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r Skip\<Colon>T" .
    then show "Norm s\<Colon>\<preceq>(G, L) \<and>
              (normal (Norm s) \<longrightarrow> G,L,store (Norm s)\<turnstile>In1r Skip\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and> 
              (error_free (Norm s) = error_free (Norm s))"
      by (simp)
  next
    case (Expr e s0 s1 v L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1" .
    have     hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Expr e)\<Colon>T" .
    then obtain eT 
      where "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l e\<Colon>eT"
      by (rule wt_elim_cases) (blast)
    with conf_s0 hyp 
    obtain "s1\<Colon>\<preceq>(G, L)" and "error_free s1"
      by (blast)
    with wt
    show "s1\<Colon>\<preceq>(G, L) \<and>
          (normal s1 \<longrightarrow> G,L,store s1\<turnstile>In1r (Expr e)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and> 
          (error_free (Norm s0) = error_free s1)"
      by (simp)
  next
    case (Lab c l s0 s1 L accC T)
    have     hyp: "PROP ?TypeSafe (Norm s0) s1 (In1r c) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (l\<bullet> c)\<Colon>T" .
    then have "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    with conf_s0 hyp
    obtain       conf_s1: "s1\<Colon>\<preceq>(G, L)" and 
           error_free_s1: "error_free s1" 
      by (blast)
    from conf_s1 have "abupd (absorb l) s1\<Colon>\<preceq>(G, L)"
      by (cases s1) (auto intro: conforms_absorb)
    with wt error_free_s1
    show "abupd (absorb l) s1\<Colon>\<preceq>(G, L) \<and>
          (normal (abupd (absorb l) s1)
           \<longrightarrow> G,L,store (abupd (absorb l) s1)\<turnstile>In1r (l\<bullet> c)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free (abupd (absorb l) s1))"
      by (simp)
  next
    case (Comp c1 c2 s0 s1 s2 L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
    have "G\<turnstile>s1 \<midarrow>c2\<rightarrow> s2" .
    have  hyp_c1: "PROP ?TypeSafe (Norm s0) s1 (In1r c1) \<diamondsuit>" .
    have  hyp_c2: "PROP ?TypeSafe s1        s2 (In1r c2) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (c1;; c2)\<Colon>T" .
    then obtain wt_c1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
                wt_c2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    with conf_s0 hyp_c1 hyp_c2
    obtain "s2\<Colon>\<preceq>(G, L)" and "error_free s2"
      by (blast)
    with wt
    show "s2\<Colon>\<preceq>(G, L) \<and>
          (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1r (c1;; c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s2)"
      by (simp)
  next
    case (If b c1 c2 e s0 s1 s2 L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" .
    have "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2" .
    have hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 b)" .
    have hyp_then_else: 
            "PROP ?TypeSafe s1 s2 (In1r (if the_Bool b then c1 else c2)) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (If(e) c1 Else c2)\<Colon>T" .
    then obtain "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean"
                "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
      by (rule wt_elim_cases) (auto split add: split_if)
    with conf_s0 hyp_e hyp_then_else
    obtain "s2\<Colon>\<preceq>(G, L)" and "error_free s2"
      by (blast)
    with wt
    show "s2\<Colon>\<preceq>(G, L) \<and>
           (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1r (If(e) c1 Else c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s2)"
      by (simp)
  next
    case (Loop b c e l s0 s1 s2 s3 L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" .
    have hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 b)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (l\<bullet> While(e) c)\<Colon>T" .
    then obtain wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
                wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    from conf_s0 wt_e hyp_e
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by blast
    show "s3\<Colon>\<preceq>(G, L) \<and>
          (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1r (l\<bullet> While(e) c)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s3)"
    proof (cases "normal s1 \<and> the_Bool b")
      case True
      from Loop True have "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" by auto
      from Loop True have "G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"
	by auto
      from Loop True have hyp_c: "PROP ?TypeSafe s1 s2 (In1r c) \<diamondsuit>"
	by (auto)
      from Loop True have hyp_w: "PROP ?TypeSafe (abupd (absorb (Cont l)) s2)
                                       s3 (In1r (l\<bullet> While(e) c)) \<diamondsuit>"
	by (auto)
      from conf_s1 error_free_s1 wt_c hyp_c
      obtain conf_s2:  "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
	by blast
      from conf_s2 have "abupd (absorb (Cont l)) s2 \<Colon>\<preceq>(G, L)"
	by (cases s2) (auto intro: conforms_absorb)
      moreover
      from error_free_s2 have "error_free (abupd (absorb (Cont l)) s2)"
	by simp
      moreover note wt hyp_w
      ultimately obtain "s3\<Colon>\<preceq>(G, L)" and "error_free s3"
	by blast
      with wt 
      show ?thesis
	by (simp)
    next
      case False
      with Loop have "s3=s1" by simp
      with conf_s1 error_free_s1 wt
      show ?thesis
	by (simp)
    qed
  next
    case (Do j s L accC T)
    have "Norm s\<Colon>\<preceq>(G, L)" .
    then 
    show "(Some (Jump j), s)\<Colon>\<preceq>(G, L) \<and>
           (normal (Some (Jump j), s) 
           \<longrightarrow> G,L,store (Some (Jump j), s)\<turnstile>In1r (Do j)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
           (error_free (Norm s) = error_free (Some (Jump j), s))"
      by simp
  next
    case (Throw a e s0 s1 L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1" .
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 a)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Throw e)\<Colon>T" .
    then obtain tn 
      where      wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-Class tn" and
            throwable: "G\<turnstile>tn\<preceq>\<^sub>C SXcpt Throwable"
      by (rule wt_elim_cases) (auto)
    from conf_s0 wt_e hyp obtain
      "s1\<Colon>\<preceq>(G, L)" and
      "(normal s1 \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>Class tn)" and
      error_free_s1: "error_free s1"
      by force
    with wf throwable
    have "abupd (throw a) s1\<Colon>\<preceq>(G, L)" 
      by (cases s1) (auto dest: Throw_lemma)
    with wt error_free_s1
    show "abupd (throw a) s1\<Colon>\<preceq>(G, L) \<and>
            (normal (abupd (throw a) s1) \<longrightarrow>
            G,L,store (abupd (throw a) s1)\<turnstile>In1r (Throw e)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
            (error_free (Norm s0) = error_free (abupd (throw a) s1))"
      by simp
  next
    case (Try catchC c1 c2 s0 s1 s2 s3 vn L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
    have sx_alloc: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
    have hyp_c1: "PROP ?TypeSafe (Norm s0) s1 (In1r c1) \<diamondsuit>" .
    have conf_s0:"Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt:"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>In1r (Try c1 Catch(catchC vn) c2)\<Colon>T" .
    then obtain 
      wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<lparr>lcl := L(VName vn\<mapsto>Class catchC)\<rparr>\<turnstile>c2\<Colon>\<surd>" and
      fresh_vn: "L(VName vn)=None"
      by (rule wt_elim_cases) (auto)
    with conf_s0 hyp_c1
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by blast
    from conf_s1 sx_alloc wf 
    have conf_s2: "s2\<Colon>\<preceq>(G, L)" 
      by (auto dest: sxalloc_type_sound split: option.splits)
    from sx_alloc error_free_s1 
    have error_free_s2: "error_free s2"
      by (rule error_free_sxalloc)
    show "s3\<Colon>\<preceq>(G, L) \<and>
          (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1r (Try c1 Catch(catchC vn) c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T)\<and>
          (error_free (Norm s0) = error_free s3)"
    proof (cases "normal s1")  
      case True
      with sx_alloc wf 
      have eq_s2_s1: "s2=s1"
	by (auto dest: sxalloc_type_sound split: option.splits)
      with True 
      have "\<not>  G,s2\<turnstile>catch catchC"
	by (simp add: catch_def)
      with Try
      have "s3=s2"
	by simp
      with wt conf_s1 error_free_s1 eq_s2_s1
      show ?thesis
	by simp
    next
      case False
      note exception_s1 = this
      show ?thesis
      proof (cases "G,s2\<turnstile>catch catchC") 
	case False
	with Try
	have "s3=s2"
	  by simp
	with wt conf_s2 error_free_s2 
	show ?thesis
	  by simp
      next
	case True
	with Try have "G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<rightarrow> s3" by simp
	from True Try 
	have hyp_c2: "PROP ?TypeSafe (new_xcpt_var vn s2) s3 (In1r c2) \<diamondsuit>"
	  by auto
	from exception_s1 sx_alloc wf
	obtain a 
	  where xcpt_s2: "abrupt s2 = Some (Xcpt (Loc a))"
	  by (auto dest!: sxalloc_type_sound split: option.splits)
	with True
	have "G\<turnstile>obj_ty (the (globs (store s2) (Heap a)))\<preceq>Class catchC"
	  by (cases s2) simp
	with xcpt_s2 conf_s2 wf
	have "Norm (lupd(VName vn\<mapsto>Addr a) (store s2))
              \<Colon>\<preceq>(G, L(VName vn\<mapsto>Class catchC))"
	  by (auto dest: Try_lemma)
	with hyp_c2 wt_c2 xcpt_s2 error_free_s2
	obtain       conf_s3: "s3\<Colon>\<preceq>(G, L(VName vn\<mapsto>Class catchC))" and
               error_free_s3: "error_free s3"
	  by (cases s2) auto
	from conf_s3 fresh_vn 
	have "s3\<Colon>\<preceq>(G,L)"
	  by (blast intro: conforms_deallocL)
	with wt error_free_s3
	show ?thesis
	  by simp
      qed
    qed
  next
    case (Fin c1 c2 s0 s1 s2 s3 x1 L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (x1, s1)" .
    have c2: "G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2" .
    have s3: "s3= (if \<exists>err. x1 = Some (Error err) 
                     then (x1, s1)
                     else abupd (abrupt_if (x1 \<noteq> None) x1) s2)" .
    have  hyp_c1: "PROP ?TypeSafe (Norm s0) (x1,s1) (In1r c1) \<diamondsuit>" .
    have  hyp_c2: "PROP ?TypeSafe (Norm s1) s2      (In1r c2) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (c1 Finally c2)\<Colon>T" .
    then obtain
      wt_c1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (rule wt_elim_cases) blast
    from conf_s0 wt_c1 hyp_c1  
    obtain conf_s1: "(x1,s1)\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free (x1,s1)"
      by blast
    from conf_s1 have "Norm s1\<Colon>\<preceq>(G, L)"
      by (rule conforms_NormI)
    with wt_c2 hyp_c2
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by blast
    from error_free_s1 s3 
    have s3': "s3=abupd (abrupt_if (x1 \<noteq> None) x1) s2"
      by simp
    show "s3\<Colon>\<preceq>(G, L) \<and>
          (normal s3 \<longrightarrow> G,L,store s3 \<turnstile>In1r (c1 Finally c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and> 
          (error_free (Norm s0) = error_free s3)"
    proof (cases x1)
      case None with conf_s2 s3' wt show ?thesis by auto
    next
      case (Some x) 
      with c2 wf conf_s1 conf_s2
      have conf: "(abrupt_if True (Some x) (abrupt s2), store s2)\<Colon>\<preceq>(G, L)"
	by (cases s2) (auto dest: Fin_lemma)
      from Some error_free_s1
      have "\<not> (\<exists> err. x=Error err)"
	by (simp add: error_free_def)
      with error_free_s2
      have "error_free (abrupt_if True (Some x) (abrupt s2), store s2)"
	by (cases s2) simp
      with Some wt conf s3' show ?thesis
	by (cases s2) auto
    qed
  next
    case (Init C c s0 s1 s2 s3 L accC T)
    have     cls: "the (class G C) = c" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Init C)\<Colon>T" .
    with cls
    have cls_C: "class G C = Some c"
      by - (erule wt_elim_cases,auto)
    show "s3\<Colon>\<preceq>(G, L) \<and> (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1r (Init C)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s3)"
    proof (cases "inited C (globs s0)")
      case True
      with Init have "s3 = Norm s0"
	by simp
      with conf_s0 wt show ?thesis 
	by simp
    next
      case False
      with Init 
      have "G\<turnstile>Norm ((init_class_obj G C) s0) 
              \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1" and
        eval_init: "G\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<rightarrow> s2" and
	s3: "s3 = (set_lvars (locals (store s1))) s2" 
	by auto
      from False Init 
      have hyp_init_super: 
             "PROP ?TypeSafe (Norm ((init_class_obj G C) s0)) s1
	              (In1r (if C = Object then Skip else Init (super c))) \<diamondsuit>"
	by auto
      with False Init (* without chaining hyp_init_super, the simplifier will
                          loop! *)
      have hyp_init_c:
	"PROP ?TypeSafe ((set_lvars empty) s1) s2 (In1r (init c)) \<diamondsuit>"
	by auto
      from conf_s0 wf cls_C False
      have conf_s0': "(Norm ((init_class_obj G C) s0))\<Colon>\<preceq>(G, L)"
	by (auto dest: conforms_init_class_obj)
      from wf cls_C have
	wt_super:"\<lparr>prg = G, cls = accC, lcl = L\<rparr>
                   \<turnstile>(if C = Object then Skip else Init (super c))\<Colon>\<surd>"
	by (cases "C=Object")
           (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD)
      with conf_s0' hyp_init_super
      obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
	by blast 
      then
      have "(set_lvars empty) s1\<Colon>\<preceq>(G, empty)"
	by (cases s1) (auto dest: conforms_set_locals )
      moreover from error_free_s1
      have "error_free ((set_lvars empty) s1)"
	by simp
      moreover note hyp_init_c wf cls_C 
      ultimately
      obtain conf_s2: "s2\<Colon>\<preceq>(G, empty)" and error_free_s2: "error_free s2"
	by (auto dest!: wf_prog_cdecl wf_cdecl_wt_init)
      with s3 conf_s1 eval_init
      have "s3\<Colon>\<preceq>(G, L)"
	by (cases s2,cases s1) (force dest: conforms_return eval_gext')
      moreover from error_free_s2 s3
      have "error_free s3"
	by simp
      moreover note wt
      ultimately show ?thesis
	by simp
    qed
  next
    case (NewC C a s0 s1 s2 L accC T)
    have         "G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s1" .
    have halloc: "G\<turnstile>s1 \<midarrow>halloc CInst C\<succ>a\<rightarrow> s2" .
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1r (Init C)) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (NewC C)\<Colon>T" .
    then obtain is_cls_C: "is_class G C" and
                       T: "T=Inl (Class C)"
      by (rule wt_elim_cases) (auto dest: is_acc_classD)
    with conf_s0 hyp
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by auto
    from conf_s1 halloc wf is_cls_C
    obtain halloc_type_safe: "s2\<Colon>\<preceq>(G, L)" 
                             "(normal s2 \<longrightarrow> G,store s2\<turnstile>Addr a\<Colon>\<preceq>Class C)"
      by (cases s2) (auto dest!: halloc_type_sound)
    from halloc error_free_s1 
    have "error_free s2"
      by (rule error_free_halloc)
    with halloc_type_safe T
    show "s2\<Colon>\<preceq>(G, L) \<and> 
          (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1l (NewC C)\<succ>In1 (Addr a)\<Colon>\<preceq>T)  \<and>
          (error_free (Norm s0) = error_free s2)"
      by auto
  next
    case (NewA T a e i s0 s1 s2 s3 L accC Ta)
    have "G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<rightarrow> s1" .
    have "G\<turnstile>s1 \<midarrow>e-\<succ>i\<rightarrow> s2" .
    have halloc: "G\<turnstile>abupd (check_neg i) s2\<midarrow>halloc Arr T (the_Intg i)\<succ>a\<rightarrow> s3" .
    have hyp_init: "PROP ?TypeSafe (Norm s0) s1 (In1r (init_comp_ty T)) \<diamondsuit>" .
    have hyp_size: "PROP ?TypeSafe s1 s2 (In1l e) (In1 i)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have     wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (New T[e])\<Colon>Ta" .
    then obtain
      wt_init: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>init_comp_ty T\<Colon>\<surd>" and
      wt_size: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Integer" and
            T: "is_type G T" and
           Ta: "Ta=Inl (T.[])"
      by (rule wt_elim_cases) (auto intro: wt_init_comp_ty dest: is_acc_typeD)
    from conf_s0 wt_init hyp_init
    obtain "s1\<Colon>\<preceq>(G, L)" "error_free s1"
      by blast
    with wt_size hyp_size
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by blast
    from conf_s2 have "abupd (check_neg i) s2\<Colon>\<preceq>(G, L)"
      by (cases s2) auto
    with halloc wf T 
    have halloc_type_safe:
          "s3\<Colon>\<preceq>(G, L) \<and> (normal s3 \<longrightarrow> G,store s3\<turnstile>Addr a\<Colon>\<preceq>T.[])"
      by (cases s3) (auto dest!: halloc_type_sound)
    from halloc error_free_s2
    have "error_free s3"
      by (auto dest: error_free_halloc)
    with halloc_type_safe Ta
    show "s3\<Colon>\<preceq>(G, L) \<and> 
          (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1l (New T[e])\<succ>In1 (Addr a)\<Colon>\<preceq>Ta) \<and>
          (error_free (Norm s0) = error_free s3) "
      by simp
  next
    case (Cast castT e s0 s1 s2 v L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1" .
    have s2:"s2 = abupd (raise_if (\<not> G,store s1\<turnstile>v fits castT) ClassCast) s1" .
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (Cast castT e)\<Colon>T" .
    then obtain eT
      where wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" and
              eT: "G\<turnstile>eT\<preceq>? castT" and 
               T: "T=Inl castT"
      by (rule wt_elim_cases) auto
    with conf_s0 hyp
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by blast
    from conf_s1 s2 
    have conf_s2: "s2\<Colon>\<preceq>(G, L)"
      by (cases s1) simp
    from error_free_s1 s2
    have error_free_s2: "error_free s2"
      by simp
    {
      assume norm_s2: "normal s2"
      have "G,L,store s2\<turnstile>In1l (Cast castT e)\<succ>In1 v\<Colon>\<preceq>T"
      proof -
	from s2 norm_s2 have "normal s1"
	  by (cases s1) simp
	with wt_e conf_s0 hyp 
	have "G,store s1\<turnstile>v\<Colon>\<preceq>eT"
	  by force
	with eT wf s2 T norm_s2
	show ?thesis
	  by (cases s1) (auto dest: fits_conf)
      qed
    }
    with conf_s2 error_free_s2
    show "s2\<Colon>\<preceq>(G, L) \<and> 
           (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1l (Cast castT e)\<succ>In1 v\<Colon>\<preceq>T)  \<and>
           (error_free (Norm s0) = error_free s2)"
      by blast
  next
    case (Inst T b e s0 s1 v L accC T')
    then show ?case
      by (auto elim!: wt_elim_cases)
  next
    case (Lit s v L accC T)
    then show ?case
      by (auto elim!: wt_elim_cases 
               intro: conf_litval simp add: empty_dt_def)
  next
    case (UnOp e s0 s1 unop v L accC T)
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (UnOp unop e)\<Colon>T" .
    then obtain eT
      where    wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" and
            wt_unop: "wt_unop unop eT" and
                  T: "T=Inl (PrimT (unop_type unop))" 
      by (auto elim!: wt_elim_cases)
    from conf_s0 wt_e 
    obtain     conf_s1: "s1\<Colon>\<preceq>(G, L)"  and
                  wt_v: "normal s1 \<longrightarrow> G,store s1\<turnstile>v\<Colon>\<preceq>eT" and
         error_free_s1: "error_free s1"
      by (auto dest!: hyp)
    from wt_v T wt_unop
    have "normal s1\<longrightarrow>G,L,snd s1\<turnstile>In1l (UnOp unop e)\<succ>In1 (eval_unop unop v)\<Colon>\<preceq>T"
      by (cases unop) auto
    with conf_s1 error_free_s1
    show "s1\<Colon>\<preceq>(G, L) \<and>
     (normal s1 \<longrightarrow> G,L,snd s1\<turnstile>In1l (UnOp unop e)\<succ>In1 (eval_unop unop v)\<Colon>\<preceq>T) \<and>
     error_free (Norm s0) = error_free s1"
      by simp
  next
    case (BinOp binop e1 e2 s0 s1 s2 v1 v2 L accC T)
    have hyp_e1: "PROP ?TypeSafe (Norm s0) s1 (In1l e1) (In1 v1)" .
    have hyp_e2: "PROP ?TypeSafe       s1  s2 
                   (if need_second_arg binop v1 then In1l e2 else In1r Skip) 
                   (In1 v2)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (BinOp binop e1 e2)\<Colon>T" .
    then obtain e1T e2T where
         wt_e1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e1\<Colon>-e1T" and
         wt_e2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e2\<Colon>-e2T" and
      wt_binop: "wt_binop G binop e1T e2T" and
             T: "T=Inl (PrimT (binop_type binop))"
      by (auto elim!: wt_elim_cases)
    have wt_Skip: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>Skip\<Colon>\<surd>"
      by simp
    from conf_s0 wt_e1 
    obtain      conf_s1: "s1\<Colon>\<preceq>(G, L)"  and
                  wt_v1: "normal s1 \<longrightarrow> G,store s1\<turnstile>v1\<Colon>\<preceq>e1T" and
          error_free_s1: "error_free s1"
      by (auto dest!: hyp_e1)
    from conf_s1 wt_e2 wt_Skip error_free_s1
    obtain      conf_s2: "s2\<Colon>\<preceq>(G, L)"  and
          error_free_s2: "error_free s2"
      by (cases "need_second_arg binop v1")
         (auto dest!: hyp_e2 )
    from wt_binop T
    have "G,L,snd s2\<turnstile>In1l (BinOp binop e1 e2)\<succ>In1 (eval_binop binop v1 v2)\<Colon>\<preceq>T"
      by (cases binop) auto
    with conf_s2 conf_s1 error_free_s2 error_free_s1
    show "s2\<Colon>\<preceq>(G, L) \<and>
          (normal s2 \<longrightarrow>
        G,L,snd s2\<turnstile>In1l (BinOp binop e1 e2)\<succ>In1 (eval_binop binop v1 v2)\<Colon>\<preceq>T) \<and>
          error_free (Norm s0) = error_free s2"
      by simp
  next
    case (Super s L accC T)
    have conf_s: "Norm s\<Colon>\<preceq>(G, L)" .
    have     wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l Super\<Colon>T" .
    then obtain C c where
             C: "L This = Some (Class C)" and
       neq_Obj: "C\<noteq>Object" and
         cls_C: "class G C = Some c" and
             T: "T=Inl (Class (super c))"
      by (rule wt_elim_cases) auto
    from C conf_s have "G,s\<turnstile>val_this s\<Colon>\<preceq>Class C"
      by (blast intro: conforms_localD [THEN lconfD])
    with neq_Obj cls_C wf
    have "G,s\<turnstile>val_this s\<Colon>\<preceq>Class (super c)"
      by (auto intro: conf_widen
                dest: subcls_direct[THEN widen.subcls])
    with T conf_s
    show "Norm s\<Colon>\<preceq>(G, L) \<and>
           (normal (Norm s) \<longrightarrow> 
              G,L,store (Norm s)\<turnstile>In1l Super\<succ>In1 (val_this s)\<Colon>\<preceq>T) \<and>
           (error_free (Norm s) = error_free (Norm s))"
      by simp
  next
    case (Acc f s0 s1 v va L accC T)
    then show ?case
      by (force elim!: wt_elim_cases)
  next
    case (Ass e f s0 s1 s2 v var w L accC T)
    have eval_var: "G\<turnstile>Norm s0 \<midarrow>var=\<succ>(w, f)\<rightarrow> s1" .
    have   eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>v\<rightarrow> s2" .
    have  hyp_var: "PROP ?TypeSafe (Norm s0) s1 (In2 var) (In2 (w,f))" .
    have    hyp_e: "PROP ?TypeSafe s1 s2 (In1l e) (In1 v)" .
    have  conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have       wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (var:=e)\<Colon>T" .
    then obtain varT eT where
	 wt_var: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>var\<Colon>=varT" and
	   wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" and
	  widen: "G\<turnstile>eT\<preceq>varT" and
              T: "T=Inl eT"
      by (rule wt_elim_cases) auto
    from conf_s0 wt_var hyp_var
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by blast
    with wt_e hyp_e
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by blast
    show "assign f v s2\<Colon>\<preceq>(G, L) \<and>
           (normal (assign f v s2) \<longrightarrow>
            G,L,store (assign f v s2)\<turnstile>In1l (var:=e)\<succ>In1 v\<Colon>\<preceq>T) \<and>
            (error_free (Norm s0) = error_free (assign f v s2))"
    proof (cases "normal s1")
      case False
      with eval_e 
      have "s2=s1"
	by auto
      with False conf_s1 error_free_s1
      show ?thesis
	by auto
    next
      case True
      note normal_s1=this
      show ?thesis 
      proof (cases "normal s2")
	case False
	with conf_s2 error_free_s2 
	show ?thesis
	  by auto
      next
	case True
	from True normal_s1 conf_s1 wt_e hyp_e
	have conf_v_eT: "G,store s2\<turnstile>v\<Colon>\<preceq>eT"
	  by force
	with widen wf
	have conf_v_varT: "G,store s2\<turnstile>v\<Colon>\<preceq>varT"
	  by (auto intro: conf_widen)
	from conf_s0 normal_s1 wt_var hyp_var
	have "G,L,store s1\<turnstile>In2 var\<succ>In2 (w, f)\<Colon>\<preceq>Inl varT"
	  by blast
	then 
	have conf_assign:  "store s1\<le>|f\<preceq>varT\<Colon>\<preceq>(G, L)" 
	  by auto
	from conf_v_eT conf_v_varT conf_assign normal_s1 True wf eval_var 
	  eval_e T conf_s2 error_free_s2
	show ?thesis
	  by (cases s1, cases s2) 
	     (auto dest!: Ass_lemma simp add: assign_conforms_def)
      qed
    qed
  next
    case (Cond b e0 e1 e2 s0 s1 s2 v L accC T)
    have eval_e0: "G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1" .
    have "G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<rightarrow> s2" .
    have hyp_e0: "PROP ?TypeSafe (Norm s0) s1 (In1l e0) (In1 b)" .
    have hyp_if: "PROP ?TypeSafe s1 s2 
                       (In1l (if the_Bool b then e1 else e2)) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (e0 ? e1 : e2)\<Colon>T" .
    then obtain T1 T2 statT where
      wt_e0: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e0\<Colon>-PrimT Boolean" and
      wt_e1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e1\<Colon>-T1" and
      wt_e2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e2\<Colon>-T2" and 
      statT: "G\<turnstile>T1\<preceq>T2 \<and> statT = T2  \<or>  G\<turnstile>T2\<preceq>T1 \<and> statT =  T1" and
      T    : "T=Inl statT"
      by (rule wt_elim_cases) auto
    with wt_e0 conf_s0 hyp_e0
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1" 
      by blast
    with wt_e1 wt_e2 statT hyp_if
    obtain dynT where
      conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2" and
      conf_res: 
          "(normal s2 \<longrightarrow>
        G,L,store s2\<turnstile>In1l (if the_Bool b then e1 else e2)\<succ>In1 v\<Colon>\<preceq>Inl dynT)" and
      dynT: "dynT = (if the_Bool b then T1 else T2)"
      by (cases "the_Bool b") force+
    from statT dynT  
    have "G\<turnstile>dynT\<preceq>statT"
      by (cases "the_Bool b") auto
    with conf_s2 conf_res error_free_s2 T wf
    show "s2\<Colon>\<preceq>(G, L) \<and>
           (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1l (e0 ? e1 : e2)\<succ>In1 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s2)"
      by (auto)
  next
    case (Call invDeclC a' accC' args e mn mode pTs' s0 s1 s2 s3 s3' s4 statT 
           v vs L accC T)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<rightarrow> s1" .
    have eval_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2" .
    have invDeclC: "invDeclC 
                      = invocation_declclass G mode (store s2) a' statT 
                           \<lparr>name = mn, parTs = pTs'\<rparr>" .
    have init_lvars: 
           "s3 = init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2".
    have check: "s3' =
       check_method_access G accC' statT mode \<lparr>name = mn, parTs = pTs'\<rparr> a' s3" .
    have eval_methd: 
           "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<rightarrow> s4" .
    have     hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 a')" .
    have  hyp_args: "PROP ?TypeSafe s1 s2 (In3 args) (In3 vs)" .
    have hyp_methd: "PROP ?TypeSafe s3' s4 
               (In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)) (In1 v)".
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>
                    \<turnstile>In1l ({accC',statT,mode}e\<cdot>mn( {pTs'}args))\<Colon>T" .
    from wt obtain pTs statDeclT statM where
                 wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT" and
              wt_args: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>args\<Colon>\<doteq>pTs" and
                statM: "max_spec G accC statT \<lparr>name=mn,parTs=pTs\<rparr> 
                         = {((statDeclT,statM),pTs')}" and
                 mode: "mode = invmode statM e" and
                    T: "T =Inl (resTy statM)" and
        eq_accC_accC': "accC=accC'"
      by (rule wt_elim_cases) fastsimp+
    from conf_s0 wt_e hyp_e 
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
           conf_a': "normal s1 \<Longrightarrow> G, store s1\<turnstile>a'\<Colon>\<preceq>RefT statT" and
           error_free_s1: "error_free s1" 
      by force
    with wt_args hyp_args
    obtain    conf_s2: "s2\<Colon>\<preceq>(G, L)" and
            conf_args: "normal s2 
                         \<Longrightarrow>  list_all2 (conf G (store s2)) vs pTs" and
        error_free_s2: "error_free s2" 
      by force
    from error_free_s2 init_lvars
    have error_free_s3: "error_free s3"
      by (auto simp add: init_lvars_def2)
    from statM 
    obtain
      statM': "(statDeclT,statM)\<in>mheads G accC statT \<lparr>name=mn,parTs=pTs'\<rparr>" and
      pTs_widen: "G\<turnstile>pTs[\<preceq>]pTs'"
      by (blast dest: max_spec2mheads)
    from check
    have eq_store_s3'_s3: "store s3'=store s3"
      by (cases s3) (simp add: check_method_access_def Let_def)
    obtain invC
      where invC: "invC = invocation_class mode (store s2) a' statT"
      by simp
    with init_lvars
    have invC': "invC = (invocation_class mode (store s3) a' statT)"
      by (cases s2,cases mode) (auto simp add: init_lvars_def2 )
    show "(set_lvars (locals (store s2))) s4\<Colon>\<preceq>(G, L) \<and>
             (normal ((set_lvars (locals (store s2))) s4) \<longrightarrow>
               G,L,store ((set_lvars (locals (store s2))) s4)
               \<turnstile>In1l ({accC',statT,mode}e\<cdot>mn( {pTs'}args))\<succ>In1 v\<Colon>\<preceq>T) \<and>
             (error_free (Norm s0) =
                error_free ((set_lvars (locals (store s2))) s4))"
    proof (cases "normal s2")
      case False
      with init_lvars 
      obtain keep_abrupt: "abrupt s3 = abrupt s2" and
             "store s3 = store (init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> 
                                            mode a' vs s2)" 
	by (auto simp add: init_lvars_def2)
      moreover
      from keep_abrupt False check
      have eq_s3'_s3: "s3'=s3" 
	by (auto simp add: check_method_access_def Let_def)
      moreover
      from eq_s3'_s3 False keep_abrupt eval_methd
      have "s4=s3'"
	by auto
      ultimately have
	"set_lvars (locals (store s2)) s4 = s2"
	by (cases s2) (cases s4, fastsimp simp add: init_lvars_def2)
      with False conf_s2 error_free_s2
      show ?thesis
	by auto
    next
      case True
      note normal_s2 = True
      with eval_args
      have normal_s1: "normal s1"
	by (cases "normal s1") auto
      with conf_a' eval_args 
      have conf_a'_s2: "G, store s2\<turnstile>a'\<Colon>\<preceq>RefT statT"
	by (auto dest: eval_gext intro: conf_gext)
      show ?thesis
      proof (cases "a'=Null \<longrightarrow> is_static statM")
	case False
	then obtain not_static: "\<not> is_static statM" and Null: "a'=Null" 
	  by blast
	with normal_s2 init_lvars mode
	obtain np: "abrupt s3 = Some (Xcpt (Std NullPointer))" and
                   "store s3 = store (init_lvars G invDeclC 
                                       \<lparr>name = mn, parTs = pTs'\<rparr> mode a' vs s2)"
	  by (auto simp add: init_lvars_def2)
	moreover
	from np check
	have eq_s3'_s3: "s3'=s3" 
	  by (auto simp add: check_method_access_def Let_def)
	moreover
	from eq_s3'_s3 np eval_methd
	have "s4=s3'"
	  by auto
	ultimately have
	  "set_lvars (locals (store s2)) s4 
           = (Some (Xcpt (Std NullPointer)),store s2)"
	  by (cases s2) (cases s4, fastsimp simp add: init_lvars_def2)
	with conf_s2 error_free_s2
	show ?thesis
	  by (cases s2) (auto dest: conforms_NormI)
      next
	case True
	with mode have notNull: "mode = IntVir \<longrightarrow> a' \<noteq> Null"
	  by (auto dest!: Null_staticD)
	with conf_s2 conf_a'_s2 wf invC  
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
	from dynT_prop wf wt_e statM' mode invC invDeclC dynM 
	obtain 
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
	  by (auto dest: DynT_mheadsD)
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
             wf eval_args conf_a' mode notNull wf_dynM involved_classes_prop
	have conf_s3: "s3\<Colon>\<preceq>(G,L')"
	  apply - 
             (* FIXME confomrs_init_lvars should be 
                adjusted to be more directy applicable *)
	  apply (drule conforms_init_lvars [of G invDeclC 
                  "\<lparr>name=mn,parTs=pTs'\<rparr>" dynM "store s2" vs pTs "abrupt s2" 
                  L statT invC a' "(statDeclT,statM)" e])
	  apply (rule wf)
	  apply (rule conf_args,assumption)
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
	  apply (force dest: wf_mdeclD1 is_acc_typeD)
	  apply (cases s2, simp add: L' init_lvars
	                      cong add: lname.case_cong ename.case_cong)
	  done 
	from  is_static_eq wf_dynM L'
	obtain mthdT where
	   "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
            \<turnstile>Body invDeclC (stmt (mbody (mthd dynM)))\<Colon>-mthdT" and
	   mthdT_widen: "G\<turnstile>mthdT\<preceq>resTy dynM"
	  by - (drule wf_mdecl_bodyD,
                auto simp: cong add: lname.case_cong ename.case_cong)
	with dynM' iscls_invDeclC invDeclC'
	have
	   "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
            \<turnstile>(Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)\<Colon>-mthdT"
	  by (auto intro: wt.Methd)
	with eq_s3'_s3 conf_s3 error_free_s3 
             hyp_methd [of L' invDeclC "Inl mthdT"]
	obtain  conf_s4: "s4\<Colon>\<preceq>(G, L')" and 
	       conf_Res: "normal s4 \<longrightarrow> G,store s4\<turnstile>v\<Colon>\<preceq>mthdT" and
	  error_free_s4: "error_free s4"
	  by auto
	from init_lvars eval_methd eq_s3'_s3 
	have "store s2\<le>|store s4"
	  by (cases s2) (auto dest!: eval_gext simp add: init_lvars_def2 )
	with conf_s2 conf_s4
	have "(set_lvars (locals (store s2))) s4\<Colon>\<preceq>(G, L)"
	  by (cases s2,cases s4) (auto intro: conforms_return)
	moreover 
	from conf_Res mthdT_widen resTy_widen wf
	have "normal s4 
             \<longrightarrow> G,store s4\<turnstile>v\<Colon>\<preceq>(resTy statM)"
	  by (auto dest: widen_trans)
	then
	have "normal ((set_lvars (locals (store s2))) s4)
             \<longrightarrow> G,store((set_lvars (locals (store s2))) s4) \<turnstile>v\<Colon>\<preceq>(resTy statM)"
	  by (cases s4) auto
	moreover note error_free_s4 T
	ultimately 
	show ?thesis
	  by simp
      qed
    qed
  next
    case (Methd D s0 s1 sig v L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<rightarrow> s1" .
    have hyp:"PROP ?TypeSafe (Norm s0) s1 (In1l (body G D sig)) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (Methd D sig)\<Colon>T" .
    then obtain m bodyT where
      D: "is_class G D" and
      m: "methd G D sig = Some m" and
      wt_body: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>
                  \<turnstile>Body (declclass m) (stmt (mbody (mthd m)))\<Colon>-bodyT" and
      T: "T=Inl bodyT"
      by (rule wt_elim_cases) auto
    with hyp [of _ _ "(Inl bodyT)"] conf_s0 
    show "s1\<Colon>\<preceq>(G, L) \<and> 
           (normal s1 \<longrightarrow> G,L,snd s1\<turnstile>In1l (Methd D sig)\<succ>In1 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s1)"
      by (auto simp add: Let_def body_def)
  next
    case (Body D c s0 s1 s2 L accC T)
    have "G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1" .
    have "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" .
    have hyp_init: "PROP ?TypeSafe (Norm s0) s1 (In1r (Init D)) \<diamondsuit>" .
    have hyp_c: "PROP ?TypeSafe s1 s2 (In1r c) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (Body D c)\<Colon>T" .
    then obtain bodyT where
         iscls_D: "is_class G D" and
            wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>" and
         resultT: "L Result = Some bodyT" and
      isty_bodyT: "is_type G bodyT" and (* ### not needed! remove from wt? *)
               T: "T=Inl bodyT"
      by (rule wt_elim_cases) auto
    from conf_s0 iscls_D hyp_init
    obtain "s1\<Colon>\<preceq>(G, L)" "error_free s1"
      by auto
    with wt_c hyp_c
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by blast
    from conf_s2
    have "abupd (absorb Ret) s2\<Colon>\<preceq>(G, L)"
      by (cases s2) (auto intro: conforms_absorb)
    moreover
    from error_free_s2
    have "error_free (abupd (absorb Ret) s2)"
      by simp
    moreover note T resultT
    ultimately
    show "abupd (absorb Ret) s2\<Colon>\<preceq>(G, L) \<and>
           (normal (abupd (absorb Ret) s2) \<longrightarrow>
             G,L,store (abupd (absorb Ret) s2)
             \<turnstile>In1l (Body D c)\<succ>In1 (the (locals (store s2) Result))\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free (abupd (absorb Ret) s2)) "
      by (cases s2) (auto intro: conforms_locals)
  next
    case (LVar s vn L accC T)
    have conf_s: "Norm s\<Colon>\<preceq>(G, L)" and 
             wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In2 (LVar vn)\<Colon>T" .
    then obtain vnT where
      vnT: "L vn = Some vnT" and
        T: "T=Inl vnT"
      by (auto elim!: wt_elim_cases)
    from conf_s vnT
    have conf_fst: "G,s\<turnstile>fst (lvar vn s)\<Colon>\<preceq>vnT"  
      by (auto elim: conforms_localD [THEN lconfD]  
               simp add: lvar_def)
    moreover
    from conf_s conf_fst vnT 
    have "s\<le>|snd (lvar vn s)\<preceq>vnT\<Colon>\<preceq>(G, L)"
      by (auto elim: conforms_lupd simp add: assign_conforms_def lvar_def)
    moreover note conf_s T
    ultimately 
    show "Norm s\<Colon>\<preceq>(G, L) \<and>
                 (normal (Norm s) \<longrightarrow>
                    G,L,store (Norm s)\<turnstile>In2 (LVar vn)\<succ>In2 (lvar vn s)\<Colon>\<preceq>T) \<and>
                 (error_free (Norm s) = error_free (Norm s))"
      by simp 
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v L accC' T)
    have eval_init: "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<rightarrow> s1" .
    have eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2" .
    have fvar: "(v, s2') = fvar statDeclC stat fn a s2" .
    have check: "s3 = check_field_access G accC statDeclC fn stat a s2'" .
    have hyp_init: "PROP ?TypeSafe (Norm s0) s1 (In1r (Init statDeclC)) \<diamondsuit>" .
    have hyp_e: "PROP ?TypeSafe s1 s2 (In1l e) (In1 a)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg=G, cls=accC', lcl=L\<rparr>\<turnstile>In2 ({accC,statDeclC,stat}e..fn)\<Colon>T" .
    then obtain statC f where
                wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-Class statC" and
            accfield: "accfield G accC statC fn = Some (statDeclC,f)" and
       eq_accC_accC': "accC=accC'" and
                stat: "stat=is_static f" and
	           T: "T=(Inl (type f))"
      by (rule wt_elim_cases) (auto simp add: member_is_static_simp)
    from wf wt_e 
    have iscls_statC: "is_class G statC"
      by (auto dest: ty_expr_is_type type_is_class)
    with wf accfield 
    have iscls_statDeclC: "is_class G statDeclC"
      by (auto dest!: accfield_fields dest: fields_declC)
    with conf_s0 hyp_init
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by auto
    from conf_s1 wt_e hyp_e
    obtain       conf_s2: "s2\<Colon>\<preceq>(G, L)" and
                  conf_a: "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC" 
      by force
    from conf_s1 wt_e error_free_s1 hyp_e
    have error_free_s2: "error_free s2"
      by auto
    from fvar 
    have store_s2': "store s2'=store s2"
      by (cases s2) (simp add: fvar_def2)
    with fvar conf_s2 
    have conf_s2': "s2'\<Colon>\<preceq>(G, L)"
      by (cases s2,cases stat) (auto simp add: fvar_def2)
    from eval_init 
    have initd_statDeclC_s1: "initd statDeclC s1"
      by (rule init_yields_initd)
    from accfield wt_e eval_init eval_e conf_s2 conf_a fvar stat check  wf
    have eq_s3_s2': "s3=s2'"  
      by (auto dest!: error_free_field_access)
    have conf_v: "normal s2' \<Longrightarrow> 
           G,store s2'\<turnstile>fst v\<Colon>\<preceq>type f \<and> store s2'\<le>|snd v\<preceq>type f\<Colon>\<preceq>(G, L)"
    proof - (*###FVar_lemma should be adjusted to be more directy applicable *)
      assume normal: "normal s2'"
      obtain vv vf x2 store2 store2'
	where  v: "v=(vv,vf)" and
              s2: "s2=(x2,store2)" and
         store2': "store s2' = store2'"
	by (cases v,cases s2,cases s2') blast
      from iscls_statDeclC obtain c
	where c: "class G statDeclC = Some c"
	by auto
      have "G,store2'\<turnstile>vv\<Colon>\<preceq>type f \<and> store2'\<le>|vf\<preceq>type f\<Colon>\<preceq>(G, L)"
      proof (rule FVar_lemma [of vv vf store2' statDeclC f fn a x2 store2 
                               statC G c L "store s1"])
	from v normal s2 fvar stat store2' 
	show "((vv, vf), Norm store2') = 
               fvar statDeclC (static f) fn a (x2, store2)"
	  by (auto simp add: member_is_static_simp)
	from accfield iscls_statC wf
	show "G\<turnstile>statC\<preceq>\<^sub>C statDeclC"
	  by (auto dest!: accfield_fields dest: fields_declC)
	from accfield
	show fld: "table_of (fields G statC) (fn, statDeclC) = Some f"
	  by (auto dest!: accfield_fields)
	from wf show "wf_prog G" .
	from conf_a s2 show "x2 = None \<longrightarrow> G,store2\<turnstile>a\<Colon>\<preceq>Class statC"
	  by auto
	from fld wf iscls_statC
	show "statDeclC \<noteq> Object "
	  by (cases "statDeclC=Object") (drule fields_declC,simp+)+
	from c show "class G statDeclC = Some c" .
	from conf_s2 s2 show "(x2, store2)\<Colon>\<preceq>(G, L)" by simp
	from eval_e s2 show "snd s1\<le>|store2" by (auto dest: eval_gext)
	from initd_statDeclC_s1 show "inited statDeclC (globs (snd s1))" 
	  by simp
      qed
      with v s2 store2'  
      show ?thesis
	by simp
    qed
    from fvar error_free_s2
    have "error_free s2'"
      by (cases s2)
         (auto simp add: fvar_def2 intro!: error_free_FVar_lemma)
    with conf_v T conf_s2' eq_s3_s2'
    show "s3\<Colon>\<preceq>(G, L) \<and>
          (normal s3 
           \<longrightarrow> G,L,store s3\<turnstile>In2 ({accC,statDeclC,stat}e..fn)\<succ>In2 v\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s3)"
      by auto
  next
    case (AVar a e1 e2 i s0 s1 s2 s2' v L accC T)
    have eval_e1: "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>a\<rightarrow> s1" .
    have eval_e2: "G\<turnstile>s1 \<midarrow>e2-\<succ>i\<rightarrow> s2" .
    have hyp_e1: "PROP ?TypeSafe (Norm s0) s1 (In1l e1) (In1 a)" .
    have hyp_e2: "PROP ?TypeSafe s1 s2 (In1l e2) (In1 i)" .
    have avar: "(v, s2') = avar G i a s2" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt:  "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In2 (e1.[e2])\<Colon>T" .
    then obtain elemT
       where wt_e1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e1\<Colon>-elemT.[]" and
             wt_e2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e2\<Colon>-PrimT Integer" and
                 T: "T= Inl elemT"
      by (rule wt_elim_cases) auto
    from  conf_s0 wt_e1 hyp_e1 
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
            conf_a: "(normal s1 \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>elemT.[])" and
            error_free_s1: "error_free s1"
      by force
    from conf_s1 error_free_s1 wt_e2 hyp_e2
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by blast
    from avar 
    have "store s2'=store s2"
      by (cases s2) (simp add: avar_def2)
    with avar conf_s2 
    have conf_s2': "s2'\<Colon>\<preceq>(G, L)"
      by (cases s2) (auto simp add: avar_def2)
    from avar error_free_s2
    have error_free_s2': "error_free s2'"
      by (cases s2) (auto simp add: avar_def2 )
    have "normal s2' \<Longrightarrow> 
           G,store s2'\<turnstile>fst v\<Colon>\<preceq>elemT \<and> store s2'\<le>|snd v\<preceq>elemT\<Colon>\<preceq>(G, L)"
    proof -(*###AVar_lemma should be adjusted to be more directy applicable *)
      assume normal: "normal s2'"
      show ?thesis
      proof -
	obtain vv vf x1 store1 x2 store2 store2'
	   where  v: "v=(vv,vf)" and
                 s1: "s1=(x1,store1)" and
                 s2: "s2=(x2,store2)" and
	    store2': "store2'=store s2'"
	  by (cases v,cases s1, cases s2, cases s2') blast 
	have "G,store2'\<turnstile>vv\<Colon>\<preceq>elemT \<and> store2'\<le>|vf\<preceq>elemT\<Colon>\<preceq>(G, L)"
	proof (rule AVar_lemma [of G x1 store1 e2 i x2 store2 vv vf store2' a,
                                 OF wf])
	  from s1 s2 eval_e2 show "G\<turnstile>(x1, store1) \<midarrow>e2-\<succ>i\<rightarrow> (x2, store2)"
	    by simp
	  from v normal s2 store2' avar 
	  show "((vv, vf), Norm store2') = avar G i a (x2, store2)"
	    by auto
	  from s2 conf_s2 show "(x2, store2)\<Colon>\<preceq>(G, L)" by simp
	  from s1 conf_a show  "x1 = None \<longrightarrow> G,store1\<turnstile>a\<Colon>\<preceq>elemT.[]" by simp 
	  from eval_e2 s1 s2 show "store1\<le>|store2" by (auto dest: eval_gext)
	qed
	with v s1 s2 store2' 
	show ?thesis
	  by simp
      qed
    qed
    with conf_s2' error_free_s2' T 
    show "s2'\<Colon>\<preceq>(G, L) \<and>
           (normal s2' \<longrightarrow> G,L,store s2'\<turnstile>In2 (e1.[e2])\<succ>In2 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s2') "
      by auto
  next
    case (Nil s0 L accC T)
    then show ?case
      by (auto elim!: wt_elim_cases)
  next
    case (Cons e es s0 s1 s2 v vs L accC T)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1" .
    have eval_es: "G\<turnstile>s1 \<midarrow>es\<doteq>\<succ>vs\<rightarrow> s2" .
    have hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have hyp_es: "PROP ?TypeSafe s1 s2 (In3 es) (In3 vs)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In3 (e # es)\<Colon>T" .
    then obtain eT esT where
       wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" and
       wt_es: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>es\<Colon>\<doteq>esT" and
       T: "T=Inr (eT#esT)"
      by (rule wt_elim_cases) blast
    from hyp_e [OF conf_s0 wt_e]
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1" and 
      conf_v: "normal s1 \<longrightarrow> G,store s1\<turnstile>v\<Colon>\<preceq>eT"
      by auto
    from eval_es conf_v 
    have conf_v': "normal s2 \<longrightarrow> G,store s2\<turnstile>v\<Colon>\<preceq>eT"
      apply clarify
      apply (rule conf_gext)
      apply (auto dest: eval_gext)
      done
    from hyp_es [OF conf_s1 wt_es] error_free_s1 
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and 
           error_free_s2: "error_free s2" and
           conf_vs: "normal s2 \<longrightarrow> list_all2 (conf G (store s2)) vs esT"
      by auto
    with conf_v' T
    show 
      "s2\<Colon>\<preceq>(G, L) \<and> 
      (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In3 (e # es)\<succ>In3 (v # vs)\<Colon>\<preceq>T) \<and>
      (error_free (Norm s0) = error_free s2) "
      by auto
  qed
  then show ?thesis .
qed

text {* 


*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
 
corollary eval_ts: 
 "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v \<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-T\<rbrakk> 
\<Longrightarrow>  s'\<Colon>\<preceq>(G,L) \<and> (normal s' \<longrightarrow> G,store s'\<turnstile>v\<Colon>\<preceq>T) \<and> 
     (error_free s = error_free s')"
apply (drule (3) eval_type_sound)
apply clarsimp
done

corollary evals_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>es\<doteq>\<succ>vs\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>es\<Colon>\<doteq>Ts\<rbrakk> 
\<Longrightarrow>  s'\<Colon>\<preceq>(G,L) \<and> (normal s' \<longrightarrow> list_all2 (conf G (store s')) vs Ts) \<and> 
     (error_free s = error_free s')" 
apply (drule (3) eval_type_sound)
apply clarsimp
done

corollary evar_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>v=\<succ>vf\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>v\<Colon>=T\<rbrakk> \<Longrightarrow>  
  s'\<Colon>\<preceq>(G,L) \<and> (normal s' \<longrightarrow> G,L,(store s')\<turnstile>In2 v\<succ>In2 vf\<Colon>\<preceq>Inl T) \<and> 
  (error_free s = error_free s')"
apply (drule (3) eval_type_sound)
apply clarsimp
done

theorem exec_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>s0\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>s0\<Colon>\<surd>\<rbrakk> 
 \<Longrightarrow> s'\<Colon>\<preceq>(G,L) \<and> (error_free s \<longrightarrow> error_free s')"
apply (drule (3) eval_type_sound)
apply clarsimp
done

lemma wf_eval_Fin: 
  assumes wf:    "wf_prog G" and
          wt_c1: "\<lparr>prg = G, cls = C, lcl = L\<rparr>\<turnstile>In1r c1\<Colon>Inl (PrimT Void)" and
        conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" and
        eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (x1,s1)" and
        eval_c2: "G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2" and
            s3: "s3=abupd (abrupt_if (x1\<noteq>None) x1) s2"
  shows "G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<rightarrow> s3"
proof -
  from eval_c1 wt_c1 wf conf_s0
  have "error_free (x1,s1)"
    by (auto dest: eval_type_sound)
  with eval_c1 eval_c2 s3
  show ?thesis
    by - (rule eval.Fin, auto simp add: error_free_def)
qed

end
