(*  Title:      HOL/Bali/TypeSafe.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen
*)
header {* The type soundness proof for Java *}


theory TypeSafe = Eval + WellForm + Conform:

section "result conformance"

constdefs
  assign_conforms :: "st \<Rightarrow> (val \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> ty \<Rightarrow> env_ \<Rightarrow> bool"
          ("_\<le>|_\<preceq>_\<Colon>\<preceq>_"                                        [71,71,71,71] 70)
 "s\<le>|f\<preceq>T\<Colon>\<preceq>E \<equiv>
  \<forall>s' w. Norm s'\<Colon>\<preceq>E \<longrightarrow> fst E,s'\<turnstile>w\<Colon>\<preceq>T \<longrightarrow> s\<le>|s' \<longrightarrow> assign f w (Norm s')\<Colon>\<preceq>E"

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
prefer 24 
  apply (case_tac "inited C (globs s0)", clarsimp, erule thin_rl) (* Init *)
apply (auto del: conjI  dest!: not_initedD gext_new sxalloc_gext halloc_gext
 simp  add: lvar_def fvar_def2 avar_def2 init_lvars_def2
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
  (if static m then x else (np a') x)"
apply (simp (no_asm) add: init_lvars_def2)
done


lemma halloc_conforms: "\<And>s1. \<lbrakk>G\<turnstile>s1 \<midarrow>halloc oi\<succ>a\<rightarrow> s2; wf_prog G; s1\<Colon>\<preceq>(G, L); 
  is_type G (obj_ty \<lparr>tag=oi,values=fs\<rparr>)\<rbrakk> \<Longrightarrow> s2\<Colon>\<preceq>(G, L)"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (case_tac "aa")
apply  (auto elim!: halloc_elim_cases dest!: new_AddrD 
       intro!: conforms_newG [THEN conforms_xconf] conf_AddrI)
done

lemma halloc_type_sound: "\<And>s1. \<lbrakk>G\<turnstile>s1 \<midarrow>halloc oi\<succ>a\<rightarrow> (x,s); wf_prog G; s1\<Colon>\<preceq>(G, L);
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
   
declare split_paired_All [simp del] split_paired_Ex [simp del] 
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac";
claset_ref () := claset () delSWrapper "split_all_tac"
*}
lemma DynT_mheadsD: 
"\<lbrakk>G\<turnstile>invmode (mhd sm) e\<rightarrow>invC\<preceq>statT; 
  wf_prog G; \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT; 
  sm \<in> mheads G C statT sig; 
  invC = invocation_class (invmode (mhd sm) e) s a' statT;
  declC =invocation_declclass G (invmode (mhd sm) e) s a' statT sig
 \<rbrakk> \<Longrightarrow> 
  \<exists> dm. 
  methd G declC sig = Some dm  \<and> G\<turnstile>resTy (mthd dm)\<preceq>resTy (mhd sm) \<and> 
  wf_mdecl G declC (sig, mthd dm) \<and>
  declC = declclass dm \<and>
  is_static dm = is_static sm \<and>  
  is_class G invC \<and> is_class G declC  \<and> G\<turnstile>invC\<preceq>\<^sub>C declC \<and>  
  (if invmode (mhd sm) e = IntVir
      then (\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>invC \<preceq>\<^sub>C statC)
      else (  (\<exists> statC. statT=ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C declC)
            \<or> (\<forall> statC. statT\<noteq>ClassT statC \<and> declC=Object)) \<and> 
           (declrefT sm) = ClassT (declclass dm))"
proof -
  assume invC_prop: "G\<turnstile>invmode (mhd sm) e\<rightarrow>invC\<preceq>statT" 
     and        wf: "wf_prog G" 
     and      wt_e: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT"
     and        sm: "sm \<in> mheads G C statT sig" 
     and      invC: "invC = invocation_class (invmode (mhd sm) e) s a' statT"
     and     declC: "declC = 
                    invocation_declclass G (invmode (mhd sm) e) s a' statT sig"
  from wt_e wf have type_statT: "is_type G (RefT statT)"
    by (auto dest: ty_expr_is_type)
  from sm have not_Null: "statT \<noteq> NullT" by auto
  from type_statT 
  have wf_C: "(\<forall> statC. statT = ClassT statC \<longrightarrow> is_class G statC)"
    by (auto)
  from type_statT wt_e 
  have wf_I: "(\<forall>I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> 
                                        invmode (mhd sm) e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  from wt_e
  have wf_A: "(\<forall>     T. statT = ArrayT T \<longrightarrow> invmode (mhd sm) e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  show ?thesis
  proof (cases "invmode (mhd sm) e = IntVir")
    case True
    with invC_prop not_Null
    have invC_prop': " is_class G invC \<and> 
                      (if (\<exists>T. statT=ArrayT T) then invC=Object 
                                              else G\<turnstile>Class invC\<preceq>RefT statT)"
      by (auto simp add: DynT_prop_def) 
    from True 
    have "\<not> is_static sm"
      by (simp add: invmode_IntVir_eq)
    with invC_prop' not_Null
    have "G,statT \<turnstile> invC valid_lookup_cls_for (is_static sm)"
      by (cases statT) auto
    with sm wf type_statT obtain dm where
           dm: "dynlookup G statT invC sig = Some dm" and
      resT_dm: "G\<turnstile>resTy (mthd dm)\<preceq>resTy (mhd sm)"      and
       static: "is_static dm = is_static sm"
      by - (drule dynamic_mheadsD,auto)
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
    show ?thesis by auto
  next
    case False
    with type_statT wf invC not_Null wf_I wf_A
    have invC_prop': "is_class G invC \<and>  
                     ((\<exists> statC. statT=ClassT statC \<and> invC=statC) \<or>
                      (\<forall> statC. statT\<noteq>ClassT statC \<and> invC=Object)) "
        by (case_tac "statT") (auto simp add: invocation_class_def 
                                       split: inv_mode.splits)
    with not_Null wf
    have dynlookup_static: "dynlookup G statT invC sig = methd G invC sig"
      by (case_tac "statT") (auto simp add: dynlookup_def dynmethd_C_C
                                            dynimethd_def)
    from sm wf wt_e not_Null False invC_prop' obtain "dm" where
                    dm: "methd G invC sig = Some dm"          and
	eq_declC_sm_dm:"declrefT sm = ClassT (declclass dm)"  and
	     eq_mheads:"mhd sm=mhead (mthd dm) "
      by - (drule static_mheadsD, auto dest: accmethd_SomeD)
    then have static: "is_static dm = is_static sm" by - (case_tac "sm",auto)
    with declC invC dynlookup_static dm
    have declC': "declC = (declclass dm)"  
      by (auto simp add: invocation_declclass_def)
    from invC_prop' wf declC' dm 
    have dm': "methd G declC sig = Some dm"
      by (auto intro: methd_declclass)
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
    from False dm' wf_dm invC_prop' declC_prop statC_prop declC' 
         eq_declC_sm_dm eq_mheads static
    show ?thesis by auto
  qed
qed

(*
lemma DynT_mheadsD: 
"\<lbrakk>G\<turnstile>invmode (mhd sm) e\<rightarrow>invC\<preceq>statT; 
  wf_prog G; \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT; 
  sm \<in> mheads G C statT sig; 
  invC = invocation_class (invmode (mhd sm) e) s a' statT;
  declC =invocation_declclass G (invmode (mhd sm) e) s a' statT sig
 \<rbrakk> \<Longrightarrow> 
  \<exists> dm. 
  methd G declC sig = Some dm  \<and> G\<turnstile>resTy (mthd dm)\<preceq>resTy (mhd sm) \<and> 
  wf_mdecl G declC (sig, mthd dm) \<and>  
  is_class G invC \<and> is_class G declC  \<and> G\<turnstile>invC\<preceq>\<^sub>C declC \<and>  
  (if invmode (mhd sm) e = IntVir
      then (\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>invC \<preceq>\<^sub>C statC)
      else (\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>statC \<preceq>\<^sub>C declC) \<and> 
           (declrefT sm) = ClassT (declclass dm))"
proof -
  assume invC_prop: "G\<turnstile>invmode (mhd sm) e\<rightarrow>invC\<preceq>statT" 
     and        wf: "wf_prog G" 
     and      wt_e: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT"
     and        sm: "sm \<in> mheads G C statT sig" 
     and      invC: "invC = invocation_class (invmode (mhd sm) e) s a' statT"
     and     declC: "declC = 
                    invocation_declclass G (invmode (mhd sm) e) s a' statT sig"
  from wt_e wf have type_statT: "is_type G (RefT statT)"
    by (auto dest: ty_expr_is_type)
  from sm have not_Null: "statT \<noteq> NullT" by auto
  from type_statT 
  have wf_C: "(\<forall> statC. statT = ClassT statC \<longrightarrow> is_class G statC)"
    by (auto)
  from type_statT wt_e 
  have wf_I: "(\<forall>I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> 
                                        invmode (mhd sm) e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  from wt_e
  have wf_A: "(\<forall>     T. statT = ArrayT T \<longrightarrow> invmode (mhd sm) e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  show ?thesis
  proof (cases "invmode (mhd sm) e = IntVir")
    case True
    with invC_prop not_Null
    have invC_prop': "is_class G invC \<and>  
                      (if (\<exists>T. statT=ArrayT T) then invC=Object 
                                              else G\<turnstile>Class invC\<preceq>RefT statT)"
      by (auto simp add: DynT_prop_def) 
    with sm wf type_statT not_Null obtain dm where
           dm: "dynlookup G statT invC sig = Some dm" and
      resT_dm: "G\<turnstile>resTy (mthd dm)\<preceq>resTy (mhd sm)"
      by - (clarify,drule dynamic_mheadsD,auto)
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
    from True dm' resT_dm wf_dm invC_prop' declC_prop statC_prop
    show ?thesis by auto
  next
    case False
    
    with type_statT wf invC not_Null wf_I wf_A
    have invC_prop': "is_class G invC \<and>  
                     ((\<exists> statC. statT=ClassT statC \<and> invC=statC) \<or>
                      (\<forall> statC. statT\<noteq>ClassT statC \<and> invC=Object)) "
        
        by (case_tac "statT") (auto simp add: invocation_class_def 
                                       split: inv_mode.splits)
    with not_Null 
    have dynlookup_static: "dynlookup G statT invC sig = methd G invC sig"
      by (case_tac "statT") (auto simp add: dynlookup_def dynmethd_def 
                                            dynimethd_def)
    from sm wf wt_e not_Null False invC_prop' obtain "dm" where
                    dm: "methd G invC sig = Some dm"          and
	eq_declC_sm_dm:"declrefT sm = ClassT (declclass dm)"  and
	     eq_mheads:"mhd sm=mhead (mthd dm) "
      by - (drule static_mheadsD, auto dest: accmethd_SomeD)
    with declC invC dynlookup_static dm
    have declC': "declC = (declclass dm)"  
      by (auto simp add: invocation_declclass_def)
    from invC_prop' wf declC' dm 
    have dm': "methd G declC sig = Some dm"
      by (auto intro: methd_declclass)
    from wf dm invC_prop' declC' type_statT 
    have declC_prop: "G\<turnstile>invC \<preceq>\<^sub>C declC \<and> is_class G declC"
      by (auto dest: methd_declC )   
    from wf dm' declC_prop declC' 
    have wf_dm: "wf_mdecl G declC (sig,(mthd dm))"
      by (auto dest: methd_wf_mdecl)
    from invC_prop' declC_prop
    have statC_prop: "(\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>statC \<preceq>\<^sub>C declC)" 
      by auto
    from False dm' wf_dm invC_prop' declC_prop statC_prop 
         eq_declC_sm_dm eq_mheads
    show ?thesis by auto
  qed
qed	
*)

declare split_paired_All [simp del] split_paired_Ex [simp del] 
declare split_if     [split del] split_if_asm     [split del] 
        option.split [split del] option.split_asm [split del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac";
claset_ref () := claset () delSWrapper "split_all_tac"
*}

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
 "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(w, f)\<rightarrow> Norm s1; G\<turnstile>Norm s1 \<midarrow>e-\<succ>v\<rightarrow> Norm s2; G,s2\<turnstile>v\<Colon>\<preceq>T'; 
   s1\<le>|s2 \<longrightarrow> assign f v (Norm s2)\<Colon>\<preceq>(G, L)
  \<rbrakk> \<Longrightarrow> assign f v (Norm s2)\<Colon>\<preceq>(G, L) \<and> 
        (\<lambda>(x',s'). x' = None \<longrightarrow> G,s'\<turnstile>v\<Colon>\<preceq>T') (assign f v (Norm s2))"
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

lemma FVar_lemma1: "\<lbrakk>table_of (DeclConcepts.fields G Ca) (fn, C) = Some f ; 
  x2 = None \<longrightarrow> G,s2\<turnstile>a\<Colon>\<preceq> Class Ca; wf_prog G; G\<turnstile>Ca\<preceq>\<^sub>C C; C \<noteq> Object; 
  class G C = Some y; (x2,s2)\<Colon>\<preceq>(G, L); s1\<le>|s2; inited C (globs s1); 
  (if static f then id else np a) x2 = None\<rbrakk> 
 \<Longrightarrow>  
  \<exists>obj. globs s2 (if static f then Inr C else Inl (the_Addr a)) = Some obj \<and> 
  var_tys G (tag obj)  (if static f then Inr C else Inl(the_Addr a)) 
          (Inl(fn,C)) = Some (type f)"
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

lemma FVar_lemma: 
"\<lbrakk>((v, f), Norm s2') = fvar C (static field) fn a (x2, s2); G\<turnstile>Ca\<preceq>\<^sub>C C;  
  table_of (DeclConcepts.fields G Ca) (fn, C) = Some field; wf_prog G;   
  x2 = None \<longrightarrow> G,s2\<turnstile>a\<Colon>\<preceq>Class Ca; C \<noteq> Object; class G C = Some y;   
  (x2, s2)\<Colon>\<preceq>(G, L); s1\<le>|s2; inited C (globs s1)\<rbrakk> \<Longrightarrow>  
  G,s2'\<turnstile>v\<Colon>\<preceq>type field \<and> s2'\<le>|f\<preceq>type field\<Colon>\<preceq>(G, L)"
apply (unfold assign_conforms_def)
apply (drule sym)
apply (clarsimp simp add: fvar_def2)
apply (drule (9) FVar_lemma1)
apply (clarsimp)
apply (drule (2) conforms_globsD [THEN oconf_lconf, THEN lconfD])
apply clarsimp
apply (drule (1) rev_gext_objD)
apply (auto elim!: conforms_upd_gobj)
done


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
apply  (force dest: AVar_lemma1)
apply (auto split add: split_if)
apply (force elim!: fits_Array dest: gext_objD 
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
                 | This \<Rightarrow> if (static (mthd sm)) 
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


lemma Call_type_sound: "\<lbrakk>wf_prog G; G\<turnstile>(x1, s1) \<midarrow>ps\<doteq>\<succ>pvs\<rightarrow> (x2, s2);  
 declC 
 = invocation_declclass G (invmode (mhd esm) e) s2 a' statT \<lparr>name=mn,parTs=pTs\<rparr>;
s2'=init_lvars G declC \<lparr>name=mn,parTs=pTs\<rparr> (invmode (mhd esm) e) a' pvs (x2,s2);
 G\<turnstile>s2' \<midarrow>Methd declC \<lparr>name=mn,parTs=pTs\<rparr>-\<succ>v\<rightarrow> (x3, s3);    
 \<forall>L. s2'\<Colon>\<preceq>(G, L) 
     \<longrightarrow> (\<forall>T. \<lparr>prg=G,cls=declC,lcl=L\<rparr>\<turnstile> Methd declC \<lparr>name=mn,parTs=pTs\<rparr>\<Colon>-T 
     \<longrightarrow> (x3, s3)\<Colon>\<preceq>(G, L) \<and> (x3 = None \<longrightarrow> G,s3\<turnstile>v\<Colon>\<preceq>T));  
 Norm s0\<Colon>\<preceq>(G, L); 
 \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT; \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>ps\<Colon>\<doteq>pTsa;  
 max_spec G C statT \<lparr>name=mn,parTs=pTsa\<rparr> = {(esm, pTs)}; 
 (x1, s1)\<Colon>\<preceq>(G, L); 
 x1 = None \<longrightarrow> G,s1\<turnstile>a'\<Colon>\<preceq>RefT statT; (x2, s2)\<Colon>\<preceq>(G, L);  
 x2 = None \<longrightarrow> list_all2 (conf G s2) pvs pTsa;
 sm=(mhd esm)\<rbrakk> \<Longrightarrow>     
 (x3, set_locals (locals s2) s3)\<Colon>\<preceq>(G, L) \<and> 
 (x3 = None \<longrightarrow> G,s3\<turnstile>v\<Colon>\<preceq>resTy sm)"
apply clarify
apply (case_tac "x2")
defer
apply  (clarsimp split add: split_if_asm simp add: init_lvars_def2)
apply (case_tac "a' = Null \<and> \<not> (static (mhd esm)) \<and> e \<noteq> Super")
apply  (clarsimp simp add: init_lvars_def2)
apply clarsimp
apply (drule eval_gext')
apply (frule (1) conf_gext)
apply (drule max_spec2mheads, clarsimp)
apply (subgoal_tac "invmode (mhd esm) e = IntVir \<longrightarrow> a' \<noteq> Null")
defer  
apply  (clarsimp simp add: invmode_IntVir_eq)
apply (frule (6) DynT_mheadsD [OF DynT_propI,of _ "s2"],(rule HOL.refl)+)
apply clarify
apply (drule wf_mdeclD1, clarsimp) 
apply (frule  ty_expr_is_type) apply simp
apply (frule (2) conforms_init_lvars)
apply   simp
apply   assumption+
apply   simp
apply   assumption+
apply   clarsimp
apply   (rule HOL.refl)
apply   simp
apply   (rule Ball_weaken)
apply     assumption
apply     (force simp add: is_acc_type_def)
apply (tactic "smp_tac 1 1")
apply (frule (2) wt_MethdI, clarsimp)
apply (subgoal_tac "is_static dm = (static (mthd esm))") 
apply   (simp only:)
apply   (tactic "smp_tac 1 1")
apply   (rule conjI)
apply     (erule  conforms_return)
apply     blast

apply     (force dest!: eval_gext del: impCE simp add: init_lvars_def2)
apply     clarsimp
apply     (drule (2) widen_trans, erule (1) conf_widen)
apply     (erule wf_ws_prog)

apply   auto
done


subsection "accessibility"

theorem dynamic_field_access_ok:
  (assumes wf: "wf_prog G" and
       eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>a\<rightarrow> s2" and
     not_Null: "a\<noteq>Null" and
    conform_a: "G,(store s2)\<turnstile>a\<Colon>\<preceq> Class statC" and
   conform_s2: "s2\<Colon>\<preceq>(G, L)" and 
    normal_s2: "normal s2" and
         wt_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>,dt\<Turnstile>e\<Colon>-Class statC" and
            f: "accfield G accC statC fn = Some f" and
         dynC: "if stat then dynC=statC  
                        else dynC=obj_class (lookup_obj (store s2) a)"
  ) "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f) \<and> 
     G\<turnstile>Field fn f in dynC dyn_accessible_from accC"
proof (cases "stat")
  case True
  with dynC 
  have dynC': "dynC=statC" by simp
  with f
  have "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f)"
    by (auto simp add: accfield_def Let_def intro!: table_of_remap_SomeD)
  with dynC' f
  show ?thesis
    by (auto intro!: static_to_dynamic_accessible_from
         dest: accfield_accessibleD accessible_from_commonD)
next
  case False
  with wf conform_a not_Null conform_s2 dynC
  obtain subclseq: "G\<turnstile>dynC \<preceq>\<^sub>C statC" and
    "is_class G dynC"
    by (auto dest!: conforms_RefTD [of _ _ _ _ "(fst s2)" L]
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

lemma call_access_ok: 
(assumes invC_prop: "G\<turnstile>invmode (mhd statM) e\<rightarrow>invC\<preceq>statT" 
     and        wf: "wf_prog G" 
     and      wt_e: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT"
     and     statM: "statM \<in> mheads G accC statT sig" 
     and      invC: "invC = invocation_class (invmode (mhd statM) e) s a statT"
)"\<exists> dynM. dynlookup G statT invC sig = Some dynM \<and>
  G\<turnstile>Methd sig dynM in invC dyn_accessible_from accC"
proof -
  from wt_e wf have type_statT: "is_type G (RefT statT)"
    by (auto dest: ty_expr_is_type)
  from statM have not_Null: "statT \<noteq> NullT" by auto
  from type_statT wt_e 
  have wf_I: "(\<forall>I. statT = IfaceT I \<longrightarrow> is_iface G I \<and> 
                                        invmode (mhd statM) e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  from wt_e
  have wf_A: "(\<forall>     T. statT = ArrayT T \<longrightarrow> invmode (mhd statM) e \<noteq> SuperM)"
    by (auto dest: invocationTypeExpr_noClassD)
  show ?thesis
  proof (cases "invmode (mhd statM) e = IntVir")
    case True
    with invC_prop not_Null
    have invC_prop': "is_class G invC \<and>  
                      (if (\<exists>T. statT=ArrayT T) then invC=Object 
                                              else G\<turnstile>Class invC\<preceq>RefT statT)"
      by (auto simp add: DynT_prop_def)
    with True not_Null
    have "G,statT \<turnstile> invC valid_lookup_cls_for is_static statM"
     by (cases statT) (auto simp add: invmode_def 
                         split: split_if split_if_asm) (*  was deleted above *)
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
     by (cases statT) (auto simp add: invmode_def
                        split: split_if split_if_asm) (*  was deleted above *)
   with statM type_statT wf 
    show ?thesis
      by - (rule dynlookup_access,auto)
  qed
qed

section "main proof of type safety"

ML {*
val forward_hyp_tac = EVERY' [smp_tac 1,
	FIRST'[mp_tac,etac exI,smp_tac 2,smp_tac 1,EVERY'[etac impE,etac exI]],
	REPEAT o (etac conjE)];
val typD_tac = eresolve_tac (thms "wt_elim_cases") THEN_ALL_NEW 
	EVERY' [full_simp_tac (simpset() setloop (K no_tac)), 
         clarify_tac(claset() addSEs[])]
*}

lemma conforms_locals [rule_format]: 
  "(a,b)\<Colon>\<preceq>(G, L) \<longrightarrow> L x = Some T \<longrightarrow> G,b\<turnstile>the (locals b x)\<Colon>\<preceq>T"
apply (force simp: conforms_def Let_def lconf_def)
done

lemma eval_type_sound [rule_format (no_asm)]: 
 "wf_prog G \<Longrightarrow> G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1) \<Longrightarrow> (\<forall>L. s0\<Colon>\<preceq>(G,L) \<longrightarrow>    
  (\<forall>C T. \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T \<longrightarrow> s1\<Colon>\<preceq>(G,L) \<and>  
  (let (x,s) = s1 in x = None \<longrightarrow> G,L,s\<turnstile>t\<succ>v\<Colon>\<preceq>T)))"
apply (erule eval_induct)

(* 29 subgoals *)
(* Xcpt, Inst, Methd, Nil, Skip, Expr, Comp *)
apply         (simp_all (no_asm_use) add: Let_def body_def)
apply       (tactic "ALLGOALS (EVERY'[Clarify_tac, TRY o typD_tac, 
                     TRY o forward_hyp_tac])")
apply      (tactic"ALLGOALS(EVERY'[asm_simp_tac(simpset()),TRY o Clarify_tac])")

(* 20 subgoals *)

(* Break *)
apply (erule conforms_absorb)

(* Cons *)
apply (erule_tac V = "G\<turnstile>Norm s0 \<midarrow>?ea\<succ>\<rightarrow> ?vs1" in thin_rl)
apply (frule eval_gext')
apply force

(* LVar *)
apply (force elim: conforms_localD [THEN lconfD] conforms_lupd 
       simp add: assign_conforms_def lvar_def)

(* Cast *)
apply (force dest: fits_conf)

(* Lit *)
apply (rule conf_litval)
apply (simp add: empty_dt_def)

(* Super *)
apply (rule conf_widen)
apply   (erule (1) subcls_direct [THEN widen.subcls])
apply  (erule (1) conforms_localD [THEN lconfD])
apply (erule wf_ws_prog)

(* Acc *)
apply fast

(* Body *)
apply (rule conjI)
apply (rule conforms_absorb)
apply (fast)
apply (fast intro: conforms_locals)

(* Cond *)
apply (simp split: split_if_asm)
apply  (tactic "forward_hyp_tac 1", force)
apply (tactic "forward_hyp_tac 1", force)

(* If *)
apply (force split add: split_if_asm)

(* Loop *)
apply (drule (1) wt.Loop)
apply (clarsimp split: split_if_asm)
apply (fast intro: conforms_absorb)

(* Fin *)
apply (case_tac "x1", force)
apply (drule spec, erule impE, erule conforms_NormI)
apply (erule impE)
apply   blast
apply (clarsimp)
apply (erule (3) Fin_lemma)

(* Throw *)
apply (erule (3) Throw_lemma)

(* NewC *)
apply (clarsimp simp add: is_acc_class_def)
apply (drule (1) halloc_type_sound,blast, rule HOL.refl, simp, simp)

(* NewA *)
apply (tactic "smp_tac 1 1",frule wt_init_comp_ty,erule impE,blast)
apply (tactic "forward_hyp_tac 1")
apply (case_tac "check_neg i' ab")
apply  (clarsimp simp add: is_acc_type_def)
apply  (drule (2) halloc_type_sound, rule HOL.refl, simp, simp)
apply force

(* Level 34, 6 subgoals *)

(* Init *)
apply (case_tac "inited C (globs s0)")
apply  (clarsimp)
apply (clarsimp)
apply (frule (1) wf_prog_cdecl)
apply (drule spec, erule impE, erule (3) conforms_init_class_obj)
apply (drule_tac "psi" = "class G C = ?x" in asm_rl,erule impE,
      force dest!: wf_cdecl_supD split add: split_if simp add: is_acc_class_def)
apply (drule spec, erule impE, erule conforms_set_locals, rule lconf_empty)
apply (erule impE) apply (rule exI) apply (erule wf_cdecl_wt_init)
apply (drule (1) conforms_return, force dest: eval_gext', assumption)


(* Ass *)
apply (tactic "forward_hyp_tac 1")
apply (rename_tac x1 s1 x2 s2 v va w L C Ta T', case_tac x1)
prefer 2 apply force
apply (case_tac x2)
prefer 2 apply force
apply (simp, drule conjunct2)
apply (drule (1) conf_widen)
apply  (erule wf_ws_prog)
apply (erule (2) Ass_lemma)
apply (clarsimp simp add: assign_conforms_def)

(* Try *)
apply (drule (1) sxalloc_type_sound, simp (no_asm_use))
apply (case_tac a)
apply  clarsimp
apply clarsimp
apply (tactic "smp_tac 1 1")
apply (simp split add: split_if_asm)
apply (fast dest: conforms_deallocL Try_lemma)

(* FVar *)

apply (frule accfield_fields)
apply (frule ty_expr_is_type [THEN type_is_class],simp)
apply simp
apply (frule wf_ws_prog)
apply (frule (1) fields_declC,simp)
apply clarsimp 
(*b y EVERY'[datac cfield_defpl_is_class 2, Clarsimp_tac] 1; not useful here*)
apply (tactic "smp_tac 1 1")
apply (tactic "forward_hyp_tac 1")
apply (rule conjI, force split add: split_if simp add: fvar_def2)
apply (drule init_yields_initd, frule eval_gext')
apply clarsimp
apply (case_tac "C=Object")
apply  clarsimp
apply (erule (9) FVar_lemma)

(* AVar *)
apply (tactic "forward_hyp_tac 1")
apply (erule_tac V = "G\<turnstile>Norm s0 \<midarrow>?e1-\<succ>?a'\<rightarrow> (?x1 1, ?s1)" in thin_rl, 
         frule eval_gext')
apply (rule conjI)
apply  (clarsimp simp add: avar_def2)
apply clarsimp
apply (erule (5) AVar_lemma)

(* Call *)
apply (tactic "forward_hyp_tac 1")
apply (rule Call_type_sound)
apply auto
done


declare fun_upd_apply [simp]
declare split_paired_All [simp] split_paired_Ex [simp]
declare split_if     [split] split_if_asm     [split] 
        option.split [split] option.split_asm [split]
ML_setup {* 
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac);
claset_ref()  := claset () addSbefore ("split_all_tac", split_all_tac)
*}

theorem eval_ts: 
 "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v \<rightarrow> (x',s'); wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-T\<rbrakk> 
\<Longrightarrow>  (x',s')\<Colon>\<preceq>(G,L) \<and> (x'=None \<longrightarrow> G,s'\<turnstile>v\<Colon>\<preceq>T)"
apply (drule (3) eval_type_sound)
apply (unfold Let_def)
apply clarsimp
done

theorem evals_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>es\<doteq>\<succ>vs\<rightarrow> (x',s'); wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>es\<Colon>\<doteq>Ts\<rbrakk> 
\<Longrightarrow>  (x',s')\<Colon>\<preceq>(G,L) \<and> (x'=None \<longrightarrow> list_all2 (conf G s') vs Ts)"
apply (drule (3) eval_type_sound)
apply (unfold Let_def)
apply clarsimp
done

theorem evar_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>v=\<succ>vf\<rightarrow> (x',s'); wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>v\<Colon>=T\<rbrakk> \<Longrightarrow>  
  (x',s')\<Colon>\<preceq>(G,L) \<and> (x'=None \<longrightarrow> G,L,s'\<turnstile>In2 v\<succ>In2 vf\<Colon>\<preceq>Inl T)"
apply (drule (3) eval_type_sound)
apply (unfold Let_def)
apply clarsimp
done

theorem exec_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>s0\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>s0\<Colon>\<surd>\<rbrakk> \<Longrightarrow> s'\<Colon>\<preceq>(G,L)"
apply (drule (3) eval_type_sound)
apply (unfold Let_def)
apply clarsimp
done

(*
theorem dyn_methods_understood: 
 "\<And>s. \<lbrakk>wf_prog G; \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>{t,md,IntVir}e..mn({pTs'}ps)\<Colon>-rT;  
  s\<Colon>\<preceq>(G,L); G\<turnstile>s \<midarrow>e-\<succ>a'\<rightarrow> Norm s'; a' \<noteq> Null\<rbrakk> \<Longrightarrow>  
  \<exists>a obj. a'=Addr a \<and> heap s' a = Some obj \<and> 
  cmethd G (obj_class obj) (mn, pTs') \<noteq> None"
apply (erule wt_elim_cases)
apply (drule max_spec2mheads)
apply (drule (3) eval_ts)
apply (clarsimp split del: split_if split_if_asm)
apply (drule (2) DynT_propI)
apply  (simp (no_asm_simp))
apply (tactic *) (* {* exhaust_cmethd_tac "the (cmethd G (target (invmode m e) s' a' md) (mn, pTs'))" 1 *} *)(*)
apply (drule (4) DynT_mheadsD [THEN conjunct1], rule HOL.refl)
apply (drule conf_RefTD)
apply clarsimp
done 
*)

end
