(*  Title:      HOL/Bali/TypeSafe.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* The type soundness proof for Java *}

theory TypeSafe = DefiniteAssignmentCorrect + Conform:

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
    then show ?case .
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


constdefs
  rconf :: "prog \<Rightarrow> lenv \<Rightarrow> st \<Rightarrow> term \<Rightarrow> vals \<Rightarrow> tys \<Rightarrow> bool"
          ("_,_,_\<turnstile>_\<succ>_\<Colon>\<preceq>_"                               [71,71,71,71,71,71] 70)
  "G,L,s\<turnstile>t\<succ>v\<Colon>\<preceq>T 
    \<equiv> case T of
        Inl T  \<Rightarrow> if (\<exists> var. t=In2 var)
                  then (\<forall> n. (the_In2 t) = LVar n 
                         \<longrightarrow> (fst (the_In2 v) = the (locals s n)) \<and>
                             (locals s n \<noteq> None \<longrightarrow> G,s\<turnstile>fst (the_In2 v)\<Colon>\<preceq>T)) \<and>
                      (\<not> (\<exists> n. the_In2 t=LVar n) \<longrightarrow> (G,s\<turnstile>fst (the_In2 v)\<Colon>\<preceq>T))\<and>
                      (s\<le>|snd (the_In2 v)\<preceq>T\<Colon>\<preceq>(G,L))
                  else G,s\<turnstile>the_In1 v\<Colon>\<preceq>T
      | Inr Ts \<Rightarrow> list_all2 (conf G s) (the_In3 v) Ts"

text {*
 With @{term rconf} we describe the conformance of the result value of a term.
 This definition gets rather complicated because of the relations between the
 injections of the different terms, types and values. The main case distinction
 is between single values and value lists. In case of value lists, every 
 value has to conform to its type. For single values we have to do a further
 case distinction, between values of variables @{term "\<exists>var. t=In2 var" } and
 ordinary values. Values of variables are modelled as pairs consisting of the
 current value and an update function which will perform an assignment to the
 variable. This stems form the decision, that we only have one evaluation rule
 for each kind of variable. The decision if we read or write to the 
 variable is made by syntactic enclosing rules. So conformance of 
 variable-values must ensure that both the current value and an update will 
 conform to the type. With the introduction of definite assignment of local
 variables we have to do another case distinction. For the notion of conformance
 local variables are allowed to be @{term None}, since the definedness is not 
 ensured by conformance but by definite assignment. Field and array variables 
 must contain a value. 
*}
 


lemma rconf_In1 [simp]: 
 "G,L,s\<turnstile>In1 ec\<succ>In1 v \<Colon>\<preceq>Inl T  =  G,s\<turnstile>v\<Colon>\<preceq>T"
apply (unfold rconf_def)
apply (simp (no_asm))
done

lemma rconf_In2_no_LVar [simp]: 
 "\<forall> n. va\<noteq>LVar n \<Longrightarrow> 
   G,L,s\<turnstile>In2 va\<succ>In2 vf\<Colon>\<preceq>Inl T  = (G,s\<turnstile>fst vf\<Colon>\<preceq>T \<and> s\<le>|snd vf\<preceq>T\<Colon>\<preceq>(G,L))"
apply (unfold rconf_def)
apply auto
done

lemma rconf_In2_LVar [simp]: 
 "va=LVar n \<Longrightarrow> 
   G,L,s\<turnstile>In2 va\<succ>In2 vf\<Colon>\<preceq>Inl T  
    = ((fst vf = the (locals s n)) \<and>
       (locals s n \<noteq> None \<longrightarrow> G,s\<turnstile>fst vf\<Colon>\<preceq>T) \<and> s\<le>|snd vf\<preceq>T\<Colon>\<preceq>(G,L))"
apply (unfold rconf_def)
by simp

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
 "\<And>s1 s2. \<lbrakk>G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2; wf_prog G\<rbrakk> \<Longrightarrow> 
  case fst s1 of  
    None \<Rightarrow> s2 = s1 
  | Some abr \<Rightarrow> (case abr of
                   Xcpt x \<Rightarrow> (\<exists>a. fst s2 = Some(Xcpt (Loc a)) \<and> 
                                  (\<forall>L. s1\<Colon>\<preceq>(G,L) \<longrightarrow> s2\<Colon>\<preceq>(G,L)))
                 | Jump j \<Rightarrow> s2 = s1
                 | Error e \<Rightarrow> s2 = s1)"
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

corollary DynT_mheadsE [consumes 7]: 
--{* Same as @{text DynT_mheadsD} but better suited for application in 
typesafety proof   *}
 assumes invC_compatible: "G\<turnstile>mode\<rightarrow>invC\<preceq>statT" 
     and wf: "wf_prog G" 
     and wt_e: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-RefT statT"
     and mheads: "(statDeclT,sm) \<in> mheads G C statT sig"
     and mode: "mode=invmode sm e" 
     and invC: "invC = invocation_class mode s a' statT"
     and declC: "declC =invocation_declclass G mode s a' statT sig"
     and dm: "\<And> dm. \<lbrakk>methd G declC sig = Some dm; 
                      dynlookup G statT invC sig = Some dm; 
                      G\<turnstile>resTy (mthd dm)\<preceq>resTy sm; 
                      wf_mdecl G declC (sig, mthd dm);
                      declC = declclass dm;
                      is_static dm = is_static sm;  
                      is_class G invC; is_class G declC; G\<turnstile>invC\<preceq>\<^sub>C declC;  
                      (if invmode sm e = IntVir
                      then (\<forall> statC. statT=ClassT statC \<longrightarrow> G\<turnstile>invC \<preceq>\<^sub>C statC)
                      else (  (\<exists> statC. statT=ClassT statC \<and> G\<turnstile>statC\<preceq>\<^sub>C declC)
                             \<or> (\<forall> statC. statT\<noteq>ClassT statC \<and> declC=Object)) \<and>
                             statDeclT = ClassT (declclass dm))\<rbrakk> \<Longrightarrow> P"
   shows "P"
proof -
    from invC_compatible mode have "G\<turnstile>invmode sm e\<rightarrow>invC\<preceq>statT" by simp 
    moreover note wf wt_e mheads
    moreover from invC mode 
    have "invC = invocation_class (invmode sm e) s a' statT" by simp
    moreover from declC mode 
    have "declC =invocation_declclass G (invmode sm e) s a' statT sig" by simp
    ultimately show ?thesis
      by (rule DynT_mheadsD [THEN exE,rule_format])
         (elim conjE,rule dm)
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
"\<lbrakk>G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> (x2,s2); wf_prog G; (Some a, s1)\<Colon>\<preceq>(G, L); (x2,s2)\<Colon>\<preceq>(G, L);
  dom (locals s1) \<subseteq> dom (locals s2)\<rbrakk> 
\<Longrightarrow>  (abrupt_if True (Some a) x2, s2)\<Colon>\<preceq>(G, L)"
apply (auto elim: eval_gext' conforms_xgext split add: split_abrupt_if)
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
  list_all2 (conf G s) pvs pTsa; G\<turnstile>pTsa[\<preceq>](parTs sig)\<rbrakk> \<Longrightarrow>  
  G,s\<turnstile>empty (pars mh[\<mapsto>]pvs)
      [\<sim>\<Colon>\<preceq>]table_of lvars(pars mh[\<mapsto>]parTs sig)"
apply (unfold wf_mhead_def)
apply clarify
apply (erule (1) wlconf_empty_vals [THEN wlconf_ext_list])
apply (drule wf_ws_prog)
apply (erule (2) conf_list_widen)
done


lemma lconf_map_lname [simp]: 
  "G,s\<turnstile>(lname_case l1 l2)[\<Colon>\<preceq>](lname_case L1 L2)
   =
  (G,s\<turnstile>l1[\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>(\<lambda>x::unit . l2)[\<Colon>\<preceq>](\<lambda>x::unit. L2))"
apply (unfold lconf_def)
apply (auto split add: lname.splits)
done

lemma wlconf_map_lname [simp]: 
  "G,s\<turnstile>(lname_case l1 l2)[\<sim>\<Colon>\<preceq>](lname_case L1 L2)
   =
  (G,s\<turnstile>l1[\<sim>\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>(\<lambda>x::unit . l2)[\<sim>\<Colon>\<preceq>](\<lambda>x::unit. L2))"
apply (unfold wlconf_def)
apply (auto split add: lname.splits)
done

lemma lconf_map_ename [simp]:
  "G,s\<turnstile>(ename_case l1 l2)[\<Colon>\<preceq>](ename_case L1 L2)
   =
  (G,s\<turnstile>l1[\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>(\<lambda>x::unit. l2)[\<Colon>\<preceq>](\<lambda>x::unit. L2))"
apply (unfold lconf_def)
apply (auto split add: ename.splits)
done

lemma wlconf_map_ename [simp]:
  "G,s\<turnstile>(ename_case l1 l2)[\<sim>\<Colon>\<preceq>](ename_case L1 L2)
   =
  (G,s\<turnstile>l1[\<sim>\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>(\<lambda>x::unit. l2)[\<sim>\<Colon>\<preceq>](\<lambda>x::unit. L2))"
apply (unfold wlconf_def)
apply (auto split add: ename.splits)
done



lemma defval_conf1 [rule_format (no_asm), elim]: 
  "is_type G T \<longrightarrow> (\<exists>v\<in>Some (default_val T): G,s\<turnstile>v\<Colon>\<preceq>T)"
apply (unfold conf_def)
apply (induct "T")
apply (auto intro: prim_ty.induct)
done

lemma np_no_jump: "x\<noteq>Some (Jump j) \<Longrightarrow> (np a') x \<noteq> Some (Jump j)"
by (auto simp add: abrupt_if_def)

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
  x\<noteq>Some (Jump Ret) 
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
apply (drule (3) conforms_init_lvars_lemma 
                 [where ?lvars="(lcls (mbody (mthd dm)))"])
apply (case_tac "dm",simp)
apply (rule conjI)
apply (unfold wlconf_def, clarify)
apply   (clarsimp simp add: wf_mhead_def is_acc_type_def)
apply   (case_tac "is_static sm")
apply     simp
apply     simp

apply   simp
apply   (case_tac "is_static sm")
apply     simp
apply     (simp add: np_no_jump)
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
  shows "table_of (DeclConcepts.fields G dynC) (fn,declclass f) = Some (fld f)\<and>
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

lemma map_upds_eq_length_append_simp:
  "\<And> tab qs. length ps = length qs \<Longrightarrow>  tab(ps[\<mapsto>]qs@zs) = tab(ps[\<mapsto>]qs)"
proof (induct ps) 
  case Nil thus ?case by simp
next
  case (Cons p ps tab qs)
  have "length (p#ps) = length qs" .
  then obtain q qs' where qs: "qs=q#qs'" and eq_length: "length ps=length qs'"
    by (cases qs) auto
  from eq_length have "(tab(p\<mapsto>q))(ps[\<mapsto>]qs'@zs)=(tab(p\<mapsto>q))(ps[\<mapsto>]qs')"
    by (rule Cons.hyps)
  with qs show ?case 
    by simp
qed

lemma map_upds_upd_eq_length_simp:
  "\<And> tab qs x y. length ps = length qs 
                  \<Longrightarrow> tab(ps[\<mapsto>]qs)(x\<mapsto>y) = tab(ps@[x][\<mapsto>]qs@[y])"
proof (induct "ps")
  case Nil thus ?case by simp
next
  case (Cons p ps tab qs x y)
  have "length (p#ps) = length qs" .
  then obtain q qs' where qs: "qs=q#qs'" and eq_length: "length ps=length qs'"
    by (cases qs) auto
  from eq_length 
  have "(tab(p\<mapsto>q))(ps[\<mapsto>]qs')(x\<mapsto>y) = (tab(p\<mapsto>q))(ps@[x][\<mapsto>]qs'@[y])"
    by (rule Cons.hyps)
  with qs show ?case
    by simp
qed


lemma map_upd_cong: "tab=tab'\<Longrightarrow> tab(x\<mapsto>y) = tab'(x\<mapsto>y)"
by simp

lemma map_upd_cong_ext: "tab z=tab' z\<Longrightarrow> (tab(x\<mapsto>y)) z = (tab'(x\<mapsto>y)) z"
by (simp add: fun_upd_def)

lemma map_upds_cong: "tab=tab'\<Longrightarrow> tab(xs[\<mapsto>]ys) = tab'(xs[\<mapsto>]ys)"
by (cases xs) simp+

lemma map_upds_cong_ext: 
 "\<And> tab tab' ys. tab z=tab' z \<Longrightarrow> (tab(xs[\<mapsto>]ys)) z = (tab'(xs[\<mapsto>]ys)) z"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs tab tab' ys)
  note Hyps = this
  show ?case
  proof (cases ys)
    case Nil
    thus ?thesis by simp
  next
    case (Cons y ys')
    have "(tab(x\<mapsto>y)(xs[\<mapsto>]ys')) z = (tab'(x\<mapsto>y)(xs[\<mapsto>]ys')) z"
      by (rules intro: Hyps map_upd_cong_ext)
    with Cons show ?thesis
      by simp
  qed
qed
   
lemma map_upd_override: "(tab(x\<mapsto>y)) x = (tab'(x\<mapsto>y)) x"
  by simp

lemma map_upds_eq_length_suffix: "\<And> tab qs. 
        length ps = length qs \<Longrightarrow> tab(ps@xs[\<mapsto>]qs) = tab(ps[\<mapsto>]qs)(xs[\<mapsto>][])"
proof (induct ps)
  case Nil thus ?case by simp
next
  case (Cons p ps tab qs)
  then obtain q qs' where qs: "qs=q#qs'" and eq_length: "length ps=length qs'"
    by (cases qs) auto
  from eq_length
  have "tab(p\<mapsto>q)(ps @ xs[\<mapsto>]qs') = tab(p\<mapsto>q)(ps[\<mapsto>]qs')(xs[\<mapsto>][])"
    by (rule Cons.hyps)
  with qs show ?case 
    by simp
qed
  
  
lemma map_upds_upds_eq_length_prefix_simp:
  "\<And> tab qs. length ps = length qs
              \<Longrightarrow> tab(ps[\<mapsto>]qs)(xs[\<mapsto>]ys) = tab(ps@xs[\<mapsto>]qs@ys)"
proof (induct ps)
  case Nil thus ?case by simp
next
  case (Cons p ps tab qs)
  then obtain q qs' where qs: "qs=q#qs'" and eq_length: "length ps=length qs'"
    by (cases qs) auto
  from eq_length 
  have "tab(p\<mapsto>q)(ps[\<mapsto>]qs')(xs[\<mapsto>]ys) = tab(p\<mapsto>q)(ps @ xs[\<mapsto>](qs' @ ys))"
    by (rule Cons.hyps)
  with qs 
  show ?case by simp
qed

lemma map_upd_cut_irrelevant:
"\<lbrakk>(tab(x\<mapsto>y)) vn = Some el; (tab'(x\<mapsto>y)) vn = None\<rbrakk>
    \<Longrightarrow> tab vn = Some el"
by (cases "tab' vn = None") (simp add: fun_upd_def)+

lemma map_upd_Some_expand:
"\<lbrakk>tab vn = Some z\<rbrakk>
    \<Longrightarrow> \<exists> z. (tab(x\<mapsto>y)) vn = Some z"
by (simp add: fun_upd_def)

lemma map_upds_Some_expand:
"\<And> tab ys z. \<lbrakk>tab vn = Some z\<rbrakk>
    \<Longrightarrow> \<exists> z. (tab(xs[\<mapsto>]ys)) vn = Some z"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs tab ys z)
  have z: "tab vn = Some z" .
  show ?case
  proof (cases ys)
    case Nil
    with z show ?thesis by simp
  next
    case (Cons y ys')
    have ys: "ys = y#ys'".
    from z obtain z' where "(tab(x\<mapsto>y)) vn = Some z'"
      by (rule map_upd_Some_expand [of tab,elim_format]) blast
    hence "\<exists>z. ((tab(x\<mapsto>y))(xs[\<mapsto>]ys')) vn = Some z"
      by (rule Cons.hyps)
    with ys show ?thesis
      by simp
  qed
qed


lemma map_upd_Some_swap:
 "(tab(r\<mapsto>w)(u\<mapsto>v)) vn = Some z \<Longrightarrow> \<exists> z. (tab(u\<mapsto>v)(r\<mapsto>w)) vn = Some z"
by (simp add: fun_upd_def)

lemma map_upd_None_swap:
 "(tab(r\<mapsto>w)(u\<mapsto>v)) vn = None \<Longrightarrow> (tab(u\<mapsto>v)(r\<mapsto>w)) vn = None"
by (simp add: fun_upd_def)


lemma map_eq_upd_eq: "tab vn = tab' vn \<Longrightarrow> (tab(x\<mapsto>y)) vn = (tab'(x\<mapsto>y)) vn"
by (simp add: fun_upd_def)

lemma map_upd_in_expansion_map_swap:
 "\<lbrakk>(tab(x\<mapsto>y)) vn = Some z;tab vn \<noteq> Some z\<rbrakk> 
                 \<Longrightarrow>  (tab'(x\<mapsto>y)) vn = Some z"
by (simp add: fun_upd_def)

lemma map_upds_in_expansion_map_swap:
 "\<And>tab tab' ys z. \<lbrakk>(tab(xs[\<mapsto>]ys)) vn = Some z;tab vn \<noteq> Some z\<rbrakk> 
                 \<Longrightarrow>  (tab'(xs[\<mapsto>]ys)) vn = Some z"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs tab tab' ys z)
  have some: "(tab(x # xs[\<mapsto>]ys)) vn = Some z" .
  have tab_not_z: "tab vn \<noteq> Some z".
  show ?case
  proof (cases "ys")
    case Nil with some tab_not_z show ?thesis by simp
  next
    case (Cons y tl)
    have ys: "ys = y#tl".
    show ?thesis
    proof (cases "(tab(x\<mapsto>y)) vn \<noteq> Some z")
      case True
      with some ys have "(tab'(x\<mapsto>y)(xs[\<mapsto>]tl)) vn = Some z"
	by (fastsimp intro: Cons.hyps)
      with ys show ?thesis 
	by simp
    next
      case False
      hence tabx_z: "(tab(x\<mapsto>y)) vn = Some z" by blast
      moreover
      from tabx_z tab_not_z
      have "(tab'(x\<mapsto>y)) vn = Some z" 
	by (rule map_upd_in_expansion_map_swap)
      ultimately
      have "(tab(x\<mapsto>y)) vn =(tab'(x\<mapsto>y)) vn"
	by simp
      hence "(tab(x\<mapsto>y)(xs[\<mapsto>]tl)) vn = (tab'(x\<mapsto>y)(xs[\<mapsto>]tl)) vn"
	by (rule map_upds_cong_ext)
      with some ys
      show ?thesis 
	by simp
    qed
  qed
qed
   
lemma map_upds_Some_swap: 
 assumes r_u: "(tab(r\<mapsto>w)(u\<mapsto>v)(xs[\<mapsto>]ys)) vn = Some z"
    shows "\<exists> z. (tab(u\<mapsto>v)(r\<mapsto>w)(xs[\<mapsto>]ys)) vn = Some z"
proof (cases "(tab(r\<mapsto>w)(u\<mapsto>v)) vn = Some z")
  case True
  then obtain z' where "(tab(u\<mapsto>v)(r\<mapsto>w)) vn = Some z'"
    by (rule map_upd_Some_swap [elim_format]) blast
  thus "\<exists> z. (tab(u\<mapsto>v)(r\<mapsto>w)(xs[\<mapsto>]ys)) vn = Some z"
    by (rule map_upds_Some_expand)
next
  case False
  with r_u
  have "(tab(u\<mapsto>v)(r\<mapsto>w)(xs[\<mapsto>]ys)) vn = Some z"
    by (rule map_upds_in_expansion_map_swap)
  thus ?thesis
    by simp
qed
 
lemma map_upds_Some_insert:
  assumes z: "(tab(xs[\<mapsto>]ys)) vn = Some z"
    shows "\<exists> z. (tab(u\<mapsto>v)(xs[\<mapsto>]ys)) vn = Some z"
proof (cases "\<exists> z. tab vn = Some z")
  case True
  then obtain z' where "tab vn = Some z'" by blast
  then obtain z'' where "(tab(u\<mapsto>v)) vn = Some z''"
    by (rule map_upd_Some_expand [elim_format]) blast
  thus ?thesis
    by (rule map_upds_Some_expand)
next
  case False
  hence "tab vn \<noteq> Some z" by simp
  with z
  have "(tab(u\<mapsto>v)(xs[\<mapsto>]ys)) vn = Some z"
    by (rule map_upds_in_expansion_map_swap)
  thus ?thesis ..
qed
   
lemma map_upds_None_cut:
assumes expand_None: "(tab(xs[\<mapsto>]ys)) vn = None"
  shows "tab vn = None"
proof (cases "tab vn = None")
  case True thus ?thesis by simp
next
  case False then obtain z where "tab vn = Some z" by blast
  then obtain z' where "(tab(xs[\<mapsto>]ys)) vn = Some z'"
    by (rule map_upds_Some_expand [where  ?tab="tab",elim_format]) blast
  with expand_None show ?thesis
    by simp
qed
    

lemma map_upds_cut_irrelevant:
"\<And> tab tab' ys. \<lbrakk>(tab(xs[\<mapsto>]ys)) vn = Some el; (tab'(xs[\<mapsto>]ys)) vn = None\<rbrakk>
                  \<Longrightarrow> tab vn = Some el"
proof  (induct "xs")
  case Nil thus ?case by simp
next
  case (Cons x xs tab tab' ys)
  have tab_vn: "(tab(x # xs[\<mapsto>]ys)) vn = Some el".
  have tab'_vn: "(tab'(x # xs[\<mapsto>]ys)) vn = None".
  show ?case
  proof (cases ys)
    case Nil
    with tab_vn show ?thesis by simp
  next
    case (Cons y tl)
    have ys: "ys=y#tl".
    with tab_vn tab'_vn 
    have "(tab(x\<mapsto>y)) vn = Some el"
      by - (rule Cons.hyps,auto)
    moreover from tab'_vn ys
    have "(tab'(x\<mapsto>y)(xs[\<mapsto>]tl)) vn = None" 
      by simp
    hence "(tab'(x\<mapsto>y)) vn = None"
      by (rule map_upds_None_cut)
    ultimately show "tab vn = Some el" 
      by (rule map_upd_cut_irrelevant)
  qed
qed

   
lemma dom_vname_split:
 "dom (lname_case (ename_case (tab(x\<mapsto>y)(xs[\<mapsto>]ys)) a) b)
   = dom (lname_case (ename_case (tab(x\<mapsto>y)) a) b) \<union> 
     dom (lname_case (ename_case (tab(xs[\<mapsto>]ys)) a) b)"
  (is "?List x xs y ys = ?Hd x y \<union> ?Tl xs ys")
proof 
  show "?List x xs y ys \<subseteq> ?Hd x y \<union> ?Tl xs ys"
  proof 
    fix el 
    assume el_in_list: "el \<in> ?List x xs y ys"
    show "el \<in>  ?Hd x y \<union> ?Tl xs ys"
    proof (cases el)
      case This
      with el_in_list show ?thesis by (simp add: dom_def)
    next
      case (EName en)
      show ?thesis
      proof (cases en)
	case Res
	with EName el_in_list show ?thesis by (simp add: dom_def)
      next
	case (VNam vn)
	with EName el_in_list show ?thesis 
	  by (auto simp add: dom_def dest: map_upds_cut_irrelevant)
      qed
    qed
  qed
next
  show "?Hd x y \<union> ?Tl xs ys  \<subseteq> ?List x xs y ys" 
  proof 
    fix el 
    assume  el_in_hd_tl: "el \<in>  ?Hd x y \<union> ?Tl xs ys"
    show "el \<in> ?List x xs y ys"
    proof (cases el)
      case This
      with el_in_hd_tl show ?thesis by (simp add: dom_def)
    next
      case (EName en)
      show ?thesis
      proof (cases en)
	case Res
	with EName el_in_hd_tl show ?thesis by (simp add: dom_def)
      next
	case (VNam vn)
	with EName el_in_hd_tl show ?thesis 
	  by (auto simp add: dom_def intro: map_upds_Some_expand 
                                            map_upds_Some_insert)
      qed
    qed
  qed
qed

lemma dom_map_upd: "\<And> tab. dom (tab(x\<mapsto>y)) = dom tab \<union> {x}"
by (auto simp add: dom_def fun_upd_def)

lemma dom_map_upds: "\<And> tab ys. length xs = length ys 
  \<Longrightarrow> dom (tab(xs[\<mapsto>]ys)) = dom tab \<union> set xs"
proof (induct xs)
  case Nil thus ?case by (simp add: dom_def)
next
  case (Cons x xs tab ys)
  note Hyp = Cons.hyps
  have len: "length (x#xs)=length ys".
  show ?case
  proof (cases ys)
    case Nil with len show ?thesis by simp
  next
    case (Cons y tl)
    with len have "dom (tab(x\<mapsto>y)(xs[\<mapsto>]tl)) = dom (tab(x\<mapsto>y)) \<union> set xs"
      by - (rule Hyp,simp)
    moreover 
    have "dom (tab(x\<mapsto>hd ys)) = dom tab \<union> {x}"
      by (rule dom_map_upd)
    ultimately
    show ?thesis using Cons
      by simp
  qed
qed
 
lemma dom_ename_case_None_simp:
 "dom (ename_case vname_tab None) = VNam ` (dom vname_tab)"
  apply (auto simp add: dom_def image_def )
  apply (case_tac "x")
  apply auto
  done

lemma dom_ename_case_Some_simp:
 "dom (ename_case vname_tab (Some a)) = VNam ` (dom vname_tab) \<union> {Res}"
  apply (auto simp add: dom_def image_def )
  apply (case_tac "x")
  apply auto
  done

lemma dom_lname_case_None_simp:
  "dom (lname_case ename_tab None) = EName ` (dom ename_tab)"
  apply (auto simp add: dom_def image_def )
  apply (case_tac "x")
  apply auto
  done

lemma dom_lname_case_Some_simp:
 "dom (lname_case ename_tab (Some a)) = EName ` (dom ename_tab) \<union> {This}"
  apply (auto simp add: dom_def image_def)
  apply (case_tac "x")
  apply auto
  done

lemmas dom_lname_ename_case_simps =  
     dom_ename_case_None_simp dom_ename_case_Some_simp 
     dom_lname_case_None_simp dom_lname_case_Some_simp

lemma image_comp: 
 "f ` g ` A = (f \<circ> g) ` A"
by (auto simp add: image_def)


lemma dom_locals_init_lvars: 
  assumes m: "m=(mthd (the (methd G C sig)))"  
  assumes len: "length (pars m) = length pvs"
  shows "dom (locals (store (init_lvars G C sig (invmode m e) a pvs s)))  
           = parameters m"
proof -
  from m
  have static_m': "is_static m = static m"
    by simp
  from len
  have dom_vnames: "dom (empty(pars m[\<mapsto>]pvs))=set (pars m)"
    by (simp add: dom_map_upds)
  show ?thesis
  proof (cases "static m")
    case True
    with static_m' dom_vnames m
    show ?thesis
      by (cases s) (simp add: init_lvars_def Let_def parameters_def
                              dom_lname_ename_case_simps image_comp)
  next
    case False
    with static_m' dom_vnames m
    show ?thesis
      by (cases s) (simp add: init_lvars_def Let_def parameters_def
                              dom_lname_ename_case_simps image_comp)
  qed
qed


lemma da_e2_BinOp:
  assumes da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile>dom (locals (store s0)) \<guillemotright>\<langle>BinOp binop e1 e2\<rangle>\<^sub>e\<guillemotright> A"
    and wt_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e1\<Colon>-e1T"
    and wt_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e2\<Colon>-e2T" 
    and wt_binop: "wt_binop G binop e1T e2T" 
    and conf_s0: "s0\<Colon>\<preceq>(G,L)"  
    and normal_s1: "normal s1"
    and	eval_e1: "G\<turnstile>s0 \<midarrow>e1-\<succ>v1\<rightarrow> s1"
    and conf_v1: "G,store s1\<turnstile>v1\<Colon>\<preceq>e1T"
    and wf: "wf_prog G"
  shows "\<exists> E2. \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) 
         \<guillemotright>(if need_second_arg binop v1 then \<langle>e2\<rangle>\<^sub>e else \<langle>Skip\<rangle>\<^sub>s)\<guillemotright> E2"
proof -
  note inj_term_simps [simp]
  from da obtain E1 where
    da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e1\<rangle>\<^sub>e\<guillemotright> E1"
    by cases simp+
  obtain E2 where
    "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) 
      \<guillemotright>(if need_second_arg binop v1 then \<langle>e2\<rangle>\<^sub>e else \<langle>Skip\<rangle>\<^sub>s)\<guillemotright> E2"
  proof (cases "need_second_arg binop v1")
    case False
    obtain S where
      daSkip: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>Skip\<rangle>\<^sub>s\<guillemotright> S"
      by (auto intro: da_Skip [simplified] assigned.select_convs)
    thus ?thesis
      using that by (simp add: False)
  next
    case True
    from eval_e1 have 
      s0_s1:"dom (locals (store s0)) \<subseteq> dom (locals (store s1))"
      by (rule dom_locals_eval_mono_elim)
    {
      assume condAnd: "binop=CondAnd"
      have ?thesis
      proof -
	from da obtain E2' where
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
             \<turnstile> dom (locals (store s0)) \<union> assigns_if True e1 \<guillemotright>\<langle>e2\<rangle>\<^sub>e\<guillemotright> E2'"
	  by cases (simp add: condAnd)+
	moreover
	have "dom (locals (store s0)) 
          \<union> assigns_if True e1 \<subseteq> dom (locals (store s1))"
	proof -
	  from condAnd wt_binop have e1T: "e1T=PrimT Boolean"
	    by simp
	  with normal_s1 conf_v1 obtain b where "v1=Bool b"
	    by (auto dest: conf_Boolean)
	  with True condAnd
	  have v1: "v1=Bool True"
	    by simp
	  from eval_e1 normal_s1 
	  have "assigns_if True e1 \<subseteq> dom (locals (store s1))"
	    by (rule assigns_if_good_approx' [elim_format])
	       (insert wt_e1, simp_all add: e1T v1)
	  with s0_s1 show ?thesis by (rule Un_least)
	qed
	ultimately
	show ?thesis
	  using that by (cases rule: da_weakenE) (simp add: True)
      qed
    }
    moreover
    { 
      assume condOr: "binop=CondOr"
      have ?thesis
	(* Beweis durch Analogie/Example/Pattern?, True\<rightarrow>False; And\<rightarrow>Or *)
      proof -
	from da obtain E2' where
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
              \<turnstile> dom (locals (store s0)) \<union> assigns_if False e1 \<guillemotright>\<langle>e2\<rangle>\<^sub>e\<guillemotright> E2'"
	  by cases (simp add: condOr)+
	moreover
	have "dom (locals (store s0)) 
                     \<union> assigns_if False e1 \<subseteq> dom (locals (store s1))"
	proof -
	  from condOr wt_binop have e1T: "e1T=PrimT Boolean"
	    by simp
	  with normal_s1 conf_v1 obtain b where "v1=Bool b"
	    by (auto dest: conf_Boolean)
	  with True condOr
	  have v1: "v1=Bool False"
	    by simp
	  from eval_e1 normal_s1 
	  have "assigns_if False e1 \<subseteq> dom (locals (store s1))"
	    by (rule assigns_if_good_approx' [elim_format])
	       (insert wt_e1, simp_all add: e1T v1)
	  with s0_s1 show ?thesis by (rule Un_least)
	qed
	ultimately
	show ?thesis
	  using that by (rule da_weakenE) (simp add: True)
      qed
    }
    moreover
    {
      assume notAndOr: "binop\<noteq>CondAnd" "binop\<noteq>CondOr"
      have ?thesis
      proof -
	from da notAndOr obtain E1' where
          da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store s0)) \<guillemotright>\<langle>e1\<rangle>\<^sub>e\<guillemotright> E1'"
	  and da_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm E1' \<guillemotright>In1l e2\<guillemotright> A"
	  by cases simp+
	from eval_e1 wt_e1 da_e1 wf normal_s1 
	have "nrm E1' \<subseteq> dom (locals (store s1))"
	  by (cases rule: da_good_approxE') rules
	with da_e2 show ?thesis
	  using that by (rule da_weakenE) (simp add: True)
      qed
    }
    ultimately show ?thesis
      by (cases binop) auto
  qed
  thus ?thesis ..
qed

section "main proof of type safety"
    
lemma eval_type_sound:
  assumes  eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" 
   and      wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T" 
   and      da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>A"
   and      wf: "wf_prog G" 
   and conf_s0: "s0\<Colon>\<preceq>(G,L)"           
  shows "s1\<Colon>\<preceq>(G,L) \<and>  (normal s1 \<longrightarrow> G,L,store s1\<turnstile>t\<succ>v\<Colon>\<preceq>T) \<and> 
         (error_free s0 = error_free s1)"
proof -
  note inj_term_simps [simp]
  let ?TypeSafeObj = "\<lambda> s0 s1 t v. 
          \<forall>  L accC T A. s0\<Colon>\<preceq>(G,L) \<longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T
                      \<longrightarrow> \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>A  
                      \<longrightarrow> s1\<Colon>\<preceq>(G,L) \<and> (normal s1 \<longrightarrow> G,L,store s1\<turnstile>t\<succ>v\<Colon>\<preceq>T)
                          \<and> (error_free s0 = error_free s1)"
  from eval 
  have "\<And> L accC T A. \<lbrakk>s0\<Colon>\<preceq>(G,L);\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T;
                      \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>A\<rbrakk>  
        \<Longrightarrow> s1\<Colon>\<preceq>(G,L) \<and> (normal s1 \<longrightarrow> G,L,store s1\<turnstile>t\<succ>v\<Colon>\<preceq>T)
            \<and> (error_free s0 = error_free s1)"
   (is "PROP ?TypeSafe s0 s1 t v"
    is "\<And> L accC T A. ?Conform L s0 \<Longrightarrow> ?WellTyped L accC T t  
                 \<Longrightarrow> ?DefAss L accC s0 t A 
                 \<Longrightarrow> ?Conform L s1 \<and> ?ValueTyped L T s1 t v \<and>
                     ?ErrorFree s0 s1")
  proof (induct)
    case (Abrupt s t xc L accC T A) 
    have "(Some xc, s)\<Colon>\<preceq>(G,L)" .
    then show "(Some xc, s)\<Colon>\<preceq>(G,L) \<and> 
      (normal (Some xc, s) 
      \<longrightarrow> G,L,store (Some xc,s)\<turnstile>t\<succ>arbitrary3 t\<Colon>\<preceq>T) \<and> 
      (error_free (Some xc, s) = error_free (Some xc, s))"
      by (simp)
  next
    case (Skip s L accC T A)
    have "Norm s\<Colon>\<preceq>(G, L)" and  
           "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r Skip\<Colon>T" .
    then show "Norm s\<Colon>\<preceq>(G, L) \<and>
              (normal (Norm s) \<longrightarrow> G,L,store (Norm s)\<turnstile>In1r Skip\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and> 
              (error_free (Norm s) = error_free (Norm s))"
      by (simp)
  next
    case (Expr e s0 s1 v L accC T A)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1" .
    have     hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    moreover
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Expr e)\<Colon>T" .
    then obtain eT 
      where "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l e\<Colon>eT"
      by (rule wt_elim_cases) (blast)
    moreover
    from Expr.prems obtain E where
      "\<lparr>prg=G,cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store ((Norm s0)::state)))\<guillemotright>In1l e\<guillemotright>E"
      by (elim da_elim_cases) simp
    ultimately 
    obtain "s1\<Colon>\<preceq>(G, L)" and "error_free s1"
      by (rule hyp [elim_format]) simp
    with wt
    show "s1\<Colon>\<preceq>(G, L) \<and>
          (normal s1 \<longrightarrow> G,L,store s1\<turnstile>In1r (Expr e)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and> 
          (error_free (Norm s0) = error_free s1)"
      by (simp)
  next
    case (Lab c l s0 s1 L accC T A)
    have     hyp: "PROP ?TypeSafe (Norm s0) s1 (In1r c) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    moreover
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (l\<bullet> c)\<Colon>T" .
    then have "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    moreover from Lab.prems obtain C where
     "\<lparr>prg=G,cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store ((Norm s0)::state)))\<guillemotright>In1r c\<guillemotright>C"
      by (elim da_elim_cases) simp
    ultimately
    obtain       conf_s1: "s1\<Colon>\<preceq>(G, L)" and 
           error_free_s1: "error_free s1" 
      by (rule hyp [elim_format]) simp
    from conf_s1 have "abupd (absorb l) s1\<Colon>\<preceq>(G, L)"
      by (cases s1) (auto intro: conforms_absorb)
    with wt error_free_s1
    show "abupd (absorb l) s1\<Colon>\<preceq>(G, L) \<and>
          (normal (abupd (absorb l) s1)
           \<longrightarrow> G,L,store (abupd (absorb l) s1)\<turnstile>In1r (l\<bullet> c)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free (abupd (absorb l) s1))"
      by (simp)
  next
    case (Comp c1 c2 s0 s1 s2 L accC T A)
    have eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
    have eval_c2: "G\<turnstile>s1 \<midarrow>c2\<rightarrow> s2" .
    have  hyp_c1: "PROP ?TypeSafe (Norm s0) s1 (In1r c1) \<diamondsuit>" .
    have  hyp_c2: "PROP ?TypeSafe s1        s2 (In1r c2) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (c1;; c2)\<Colon>T" .
    then obtain wt_c1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
                wt_c2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    from Comp.prems
    obtain C1 C2
      where da_c1: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile> 
                      dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r c1\<guillemotright> C1" and 
            da_c2: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>  nrm C1 \<guillemotright>In1r c2\<guillemotright> C2" 
      by (elim da_elim_cases) simp
    from conf_s0 wt_c1 da_c1
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and 
           error_free_s1: "error_free s1"
      by (rule hyp_c1 [elim_format]) simp
    show "s2\<Colon>\<preceq>(G, L) \<and>
          (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1r (c1;; c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s2)"
    proof (cases "normal s1")
      case False
      with eval_c2 have "s2=s1" by auto
      with conf_s1 error_free_s1 False wt show ?thesis
	by simp
    next
      case True
      obtain C2' where 
	"\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>In1r c2\<guillemotright> C2'"
      proof -
	from eval_c1 wt_c1 da_c1 wf True
	have "nrm C1 \<subseteq> dom (locals (store s1))"
	  by (cases rule: da_good_approxE') rules
	with da_c2 show ?thesis
	  by (rule da_weakenE)
      qed
      with conf_s1 wt_c2 
      obtain "s2\<Colon>\<preceq>(G, L)" and "error_free s2"
	by (rule hyp_c2 [elim_format]) (simp add: error_free_s1)
      thus ?thesis
	using wt by simp
    qed
  next
    case (If b c1 c2 e s0 s1 s2 L accC T)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" .
    have eval_then_else: "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2" .
    have hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 b)" .
    have hyp_then_else: 
            "PROP ?TypeSafe s1 s2 (In1r (if the_Bool b then c1 else c2)) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (If(e) c1 Else c2)\<Colon>T" .
    then obtain 
              wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
      wt_then_else: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
      (*
                wt_c1: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
                wt_c2: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>c2\<Colon>\<surd>"*)
      by (rule wt_elim_cases) (auto split add: split_if)
    from If.prems obtain E C where
      da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store ((Norm s0)::state))) 
                                       \<guillemotright>In1l e\<guillemotright> E" and
      da_then_else: 
      "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
         (dom (locals (store ((Norm s0)::state))) \<union> assigns_if (the_Bool b) e)
          \<guillemotright>In1r (if the_Bool b then c1 else c2)\<guillemotright> C"
     (*
     da_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                                      \<union> assigns_if True e) \<guillemotright>In1r c1\<guillemotright> C1" and
     da_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                                       \<union> assigns_if False e) \<guillemotright>In1r c2\<guillemotright> C2" *)
      by (elim da_elim_cases) (cases "the_Bool b",auto)
    from conf_s0 wt_e da_e  
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by (rule hyp_e [elim_format]) simp
    show "s2\<Colon>\<preceq>(G, L) \<and>
           (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1r (If(e) c1 Else c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s2)"
    proof (cases "normal s1")
      case False
      with eval_then_else have "s2=s1" by auto
      with conf_s1 error_free_s1 False wt show ?thesis
	by simp
    next
      case True
      obtain C' where
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
          (dom (locals (store s1)))\<guillemotright>In1r (if the_Bool b then c1 else c2)\<guillemotright> C'"
      proof -
	from eval_e have 
	  "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
	  by (rule dom_locals_eval_mono_elim)
        moreover
	from eval_e True wt_e 
	have "assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
	  by (rule assigns_if_good_approx')
	ultimately 
	have "dom (locals (store ((Norm s0)::state))) 
                \<union> assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
	  by (rule Un_least)
	with da_then_else show ?thesis
	  by (rule da_weakenE)
      qed
      with conf_s1 wt_then_else  
      obtain "s2\<Colon>\<preceq>(G, L)" and "error_free s2"
	by (rule hyp_then_else [elim_format]) (simp add: error_free_s1)
      with wt show ?thesis
	by simp
    qed
    -- {* Note that we don't have to show that @{term b} really is a boolean 
          value. With @{term the_Bool} we enforce to get a value of boolean 
          type. So execution will be type safe, even if b would be
          a string, for example. We might not expect such a behaviour to be
          called type safe. To remedy the situation we would have to change
          the evaulation rule, so that it only has a type safe evaluation if
          we actually get a boolean value for the condition. That b is actually
          a boolean value is part of @{term hyp_e}. See also Loop 
       *}
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Loop b c e l s0 s1 s2 s3 L accC T A)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" .
    have hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 b)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (l\<bullet> While(e) c)\<Colon>T" .
    then obtain wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
                wt_c: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (rule wt_elim_cases) (blast)
    have da:"\<lparr>prg=G, cls=accC, lcl=L\<rparr>
            \<turnstile> dom (locals(store ((Norm s0)::state))) \<guillemotright>In1r (l\<bullet> While(e) c)\<guillemotright> A".
    then
    obtain E C where
      da_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>
              \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> E" and
      da_c: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>
              \<turnstile> (dom (locals (store ((Norm s0)::state))) 
                   \<union> assigns_if True e) \<guillemotright>In1r c\<guillemotright> C" 
      by (rule da_elim_cases) simp
    from conf_s0 wt_e da_e 
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by (rule hyp_e [elim_format]) simp
    show "s3\<Colon>\<preceq>(G, L) \<and>
          (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1r (l\<bullet> While(e) c)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s3)"
    proof (cases "normal s1")
      case True
      note normal_s1 = this
      show ?thesis
      proof (cases "the_Bool b")
	case True
	with Loop.hyps  obtain
          eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" and 
          eval_while: "G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"
	  by simp 
	have "?TypeSafeObj s1 s2 (In1r c) \<diamondsuit>"
	  using Loop.hyps True by simp
	note hyp_c = this [rule_format]
	have "?TypeSafeObj (abupd (absorb (Cont l)) s2)
          s3 (In1r (l\<bullet> While(e) c)) \<diamondsuit>"
	  using Loop.hyps True by simp
	note hyp_w = this [rule_format]
	from eval_e have 
	  s0_s1: "dom (locals (store ((Norm s0)::state)))
                    \<subseteq> dom (locals (store s1))"
	  by (rule dom_locals_eval_mono_elim)
	obtain C' where
	  "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(dom (locals (store s1)))\<guillemotright>In1r c\<guillemotright> C'" 
	proof -
	  note s0_s1
          moreover
	  from eval_e normal_s1 wt_e 
	  have "assigns_if True e \<subseteq> dom (locals (store s1))"
	    by (rule assigns_if_good_approx' [elim_format]) (simp add: True)
	  ultimately 
	  have "dom (locals (store ((Norm s0)::state))) 
                 \<union> assigns_if True e \<subseteq> dom (locals (store s1))"
	    by (rule Un_least)
	  with da_c show ?thesis
	    by (rule da_weakenE)
	qed
	with conf_s1 wt_c  
	obtain conf_s2:  "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
	  by (rule hyp_c [elim_format]) (simp add: error_free_s1)
	from error_free_s2 
	have error_free_ab_s2: "error_free (abupd (absorb (Cont l)) s2)"
	  by simp
	from conf_s2 have "abupd (absorb (Cont l)) s2 \<Colon>\<preceq>(G, L)"
	  by (cases s2) (auto intro: conforms_absorb)
	moreover note wt
	moreover
	obtain A' where 
          "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
              dom (locals(store (abupd (absorb (Cont l)) s2)))
                \<guillemotright>In1r (l\<bullet> While(e) c)\<guillemotright> A'"
	proof -
	  note s0_s1
	  also from eval_c 
	  have "dom (locals (store s1)) \<subseteq> dom (locals (store s2))"
	    by (rule dom_locals_eval_mono_elim)
	  also have "\<dots> \<subseteq> dom (locals (store (abupd (absorb (Cont l)) s2)))"
	    by simp
	  finally
          have "dom (locals (store ((Norm s0)::state))) \<subseteq> \<dots>" .
	  with da show ?thesis
	    by (rule da_weakenE)
	qed
	ultimately obtain "s3\<Colon>\<preceq>(G, L)" and "error_free s3"
	  by (rule hyp_w [elim_format]) (simp add: error_free_ab_s2)
	with wt show ?thesis
	  by simp
      next
	case False
	with Loop.hyps have "s3=s1" by simp
	with conf_s1 error_free_s1 wt
	show ?thesis
	  by simp
      qed
    next
      case False
      have "s3=s1"
      proof -
	from False obtain abr where abr: "abrupt s1 = Some abr"
	  by (cases s1) auto
	from eval_e _ wt_e have no_jmp: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	  by (rule eval_expression_no_jump 
               [where ?Env="\<lparr>prg=G,cls=accC,lcl=L\<rparr>",simplified]) 
             (simp_all add: wf)
	    
	show ?thesis
	proof (cases "the_Bool b")
	  case True  
	  with Loop.hyps obtain
            eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" and 
            eval_while: "G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"
	    by simp
	  from eval_c abr have "s2=s1" by auto
	  moreover from calculation no_jmp have "abupd (absorb (Cont l)) s2=s2"
	    by (cases s1) (simp add: absorb_def)
	  ultimately show ?thesis
	    using eval_while abr
	    by auto
	next
	  case False
	  with Loop.hyps show ?thesis by simp
	qed
      qed
      with conf_s1 error_free_s1 wt
      show ?thesis
	by simp
    qed
  next
    case (Jmp j s L accC T A)
    have "Norm s\<Colon>\<preceq>(G, L)" .
    moreover
    from Jmp.prems 
    have "j=Ret \<longrightarrow> Result \<in> dom (locals (store ((Norm s)::state)))"
      by (elim da_elim_cases)
    ultimately have "(Some (Jump j), s)\<Colon>\<preceq>(G, L)" by auto
    then 
    show "(Some (Jump j), s)\<Colon>\<preceq>(G, L) \<and>
           (normal (Some (Jump j), s) 
           \<longrightarrow> G,L,store (Some (Jump j), s)\<turnstile>In1r (Jmp j)\<succ>\<diamondsuit>\<Colon>\<preceq>T) \<and>
           (error_free (Norm s) = error_free (Some (Jump j), s))"
      by simp
  next
    case (Throw a e s0 s1 L accC T A)
    have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1" .
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 a)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (Throw e)\<Colon>T" .
    then obtain tn 
      where      wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-Class tn" and
            throwable: "G\<turnstile>tn\<preceq>\<^sub>C SXcpt Throwable"
      by (rule wt_elim_cases) (auto)
    from Throw.prems obtain E where 
      da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
             \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> E"
      by (elim da_elim_cases) simp
    from conf_s0 wt_e da_e obtain
      "s1\<Colon>\<preceq>(G, L)" and
      "(normal s1 \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>Class tn)" and
      error_free_s1: "error_free s1"
      by (rule hyp [elim_format]) simp
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
    case (Try catchC c1 c2 s0 s1 s2 s3 vn L accC T A)
    have eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
    have sx_alloc: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
    have hyp_c1: "PROP ?TypeSafe (Norm s0) s1 (In1r c1) \<diamondsuit>" .
    have conf_s0:"Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt:"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>In1r (Try c1 Catch(catchC vn) c2)\<Colon>T" .
    then obtain 
      wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg=G,cls=accC,lcl=L(VName vn\<mapsto>Class catchC)\<rparr>\<turnstile>c2\<Colon>\<surd>" and
      fresh_vn: "L(VName vn)=None"
      by (rule wt_elim_cases) simp
    from Try.prems obtain C1 C2 where
      da_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r c1\<guillemotright> C1"  and
      da_c2:
       "\<lparr>prg=G,cls=accC,lcl=L(VName vn\<mapsto>Class catchC)\<rparr>
        \<turnstile> (dom (locals (store ((Norm s0)::state))) \<union> {VName vn}) \<guillemotright>In1r c2\<guillemotright> C2"
      by (elim da_elim_cases) simp
    from conf_s0 wt_c1 da_c1
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by (rule hyp_c1 [elim_format]) simp
    from conf_s1 sx_alloc wf 
    have conf_s2: "s2\<Colon>\<preceq>(G, L)" 
      by (auto dest: sxalloc_type_sound split: option.splits abrupt.splits)
    from sx_alloc error_free_s1 
    have error_free_s2: "error_free s2"
      by (rule error_free_sxalloc)
    show "s3\<Colon>\<preceq>(G, L) \<and>
          (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1r (Try c1 Catch(catchC vn) c2)\<succ>\<diamondsuit>\<Colon>\<preceq>T)\<and>
          (error_free (Norm s0) = error_free s3)"
    proof (cases "\<exists> x. abrupt s1 = Some (Xcpt x)")
      case False
      from sx_alloc wf
      have eq_s2_s1: "s2=s1"
	by (rule sxalloc_type_sound [elim_format])
	   (insert False, auto split: option.splits abrupt.splits )
      with False 
      have "\<not>  G,s2\<turnstile>catch catchC"
	by (simp add: catch_def)
      with Try
      have "s3=s2"
	by simp
      with wt conf_s1 error_free_s1 eq_s2_s1
      show ?thesis
	by simp
    next
      case True
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
	from True Try.hyps
	have "?TypeSafeObj (new_xcpt_var vn s2) s3 (In1r c2) \<diamondsuit>"
	  by simp
	note hyp_c2 = this [rule_format]
	from exception_s1 sx_alloc wf
	obtain a 
	  where xcpt_s2: "abrupt s2 = Some (Xcpt (Loc a))"
	  by (auto dest!: sxalloc_type_sound split: option.splits abrupt.splits)
	with True
	have "G\<turnstile>obj_ty (the (globs (store s2) (Heap a)))\<preceq>Class catchC"
	  by (cases s2) simp
	with xcpt_s2 conf_s2 wf
	have "new_xcpt_var vn s2 \<Colon>\<preceq>(G, L(VName vn\<mapsto>Class catchC))"
	  by (auto dest: Try_lemma)
	moreover note wt_c2
	moreover
	obtain C2' where
	  "\<lparr>prg=G,cls=accC,lcl=L(VName vn\<mapsto>Class catchC)\<rparr>
          \<turnstile> (dom (locals (store (new_xcpt_var vn s2)))) \<guillemotright>In1r c2\<guillemotright> C2'"
	proof -
	  have "(dom (locals (store ((Norm s0)::state))) \<union> {VName vn}) 
                  \<subseteq> dom (locals (store (new_xcpt_var vn s2)))"
          proof -
            have "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
            hence "dom (locals (store ((Norm s0)::state))) 
                    \<subseteq> dom (locals (store s1))"
              by (rule dom_locals_eval_mono_elim)
            also
            from sx_alloc
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
	ultimately
	obtain       conf_s3: "s3\<Colon>\<preceq>(G, L(VName vn\<mapsto>Class catchC))" and
               error_free_s3: "error_free s3"
	  by (rule hyp_c2 [elim_format])
             (cases s2, simp add: xcpt_s2 error_free_s2) 
	from conf_s3 fresh_vn 
	have "s3\<Colon>\<preceq>(G,L)"
	  by (blast intro: conforms_deallocL)
	with wt error_free_s3
	show ?thesis
	  by simp
      qed
    qed
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Fin c1 c2 s0 s1 s2 s3 x1 L accC T A)
    have eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (x1, s1)" .
    have eval_c2: "G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2" .
    have s3: "s3= (if \<exists>err. x1 = Some (Error err) 
                     then (x1, s1)
                     else abupd (abrupt_if (x1 \<noteq> None) x1) s2)" .
    have  hyp_c1: "PROP ?TypeSafe (Norm s0) (x1,s1) (In1r c1) \<diamondsuit>" .
    have  hyp_c2: "PROP ?TypeSafe (Norm s1) s2      (In1r c2) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1r (c1 Finally c2)\<Colon>T" .
    then obtain
      wt_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (rule wt_elim_cases) blast
    from Fin.prems obtain C1 C2 where 
      da_c1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
               \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r c1\<guillemotright> C1" and
      da_c2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
               \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r c2\<guillemotright> C2"
      by (elim da_elim_cases) simp 
    from conf_s0 wt_c1 da_c1   
    obtain conf_s1: "(x1,s1)\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free (x1,s1)"
      by (rule hyp_c1 [elim_format]) simp
    from conf_s1 have "Norm s1\<Colon>\<preceq>(G, L)"
      by (rule conforms_NormI)
    moreover note wt_c2
    moreover obtain C2'
      where "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
               \<turnstile> dom (locals (store ((Norm s1)::state))) \<guillemotright>In1r c2\<guillemotright> C2'"
    proof -
      from eval_c1
      have "dom (locals (store ((Norm s0)::state))) 
             \<subseteq> dom (locals (store (x1,s1)))"
        by (rule dom_locals_eval_mono_elim)
      hence "dom (locals (store ((Norm s0)::state))) 
              \<subseteq> dom (locals (store ((Norm s1)::state)))"
	by simp
      with da_c2 show ?thesis
	by (rule da_weakenE)
    qed
    ultimately
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by (rule hyp_c2 [elim_format]) simp
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
      from eval_c2 have 
	"dom (locals (store ((Norm s1)::state))) \<subseteq> dom (locals (store s2))"
	by (rule dom_locals_eval_mono_elim)
      with Some eval_c2 wf conf_s1 conf_s2
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
      with Init.hyps have "s3 = Norm s0"
	by simp
      with conf_s0 wt show ?thesis 
	by simp
    next
      case False
      with Init.hyps obtain 
           eval_init_super: 
           "G\<turnstile>Norm ((init_class_obj G C) s0) 
              \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1" and
        eval_init: "G\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<rightarrow> s2" and
	s3: "s3 = (set_lvars (locals (store s1))) s2" 
	by simp
      have "?TypeSafeObj (Norm ((init_class_obj G C) s0)) s1
	              (In1r (if C = Object then Skip else Init (super c))) \<diamondsuit>"
	using False Init.hyps by simp
      note hyp_init_super = this [rule_format] 
      have "?TypeSafeObj ((set_lvars empty) s1) s2 (In1r (init c)) \<diamondsuit>"
	using False Init.hyps by simp
      note hyp_init_c = this [rule_format]
      from conf_s0 wf cls_C False
      have "(Norm ((init_class_obj G C) s0))\<Colon>\<preceq>(G, L)"
	by (auto dest: conforms_init_class_obj)
      moreover from wf cls_C have
	wt_init_super: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>
                         \<turnstile>(if C = Object then Skip else Init (super c))\<Colon>\<surd>"
	by (cases "C=Object")
           (auto dest: wf_prog_cdecl wf_cdecl_supD is_acc_classD)
      moreover
      obtain S where
	da_init_super:
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>
          \<turnstile> dom (locals (store ((Norm ((init_class_obj G C) s0))::state))) 
               \<guillemotright>In1r (if C = Object then Skip else Init (super c))\<guillemotright> S"
      proof (cases "C=Object")
	case True 
	with da_Skip show ?thesis
	  using that by (auto intro: assigned.select_convs)
      next
	case False 
	with da_Init show ?thesis
	  by - (rule that, auto intro: assigned.select_convs)
      qed
      ultimately 
      obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
	by (rule hyp_init_super [elim_format]) simp
      from eval_init_super wt_init_super wf
      have s1_no_ret: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	by - (rule eval_statement_no_jump [where ?Env="\<lparr>prg=G,cls=accC,lcl=L\<rparr>"],
              auto)
      with conf_s1
      have "(set_lvars empty) s1\<Colon>\<preceq>(G, empty)"
	by (cases s1) (auto intro: conforms_set_locals)
      moreover 
      from error_free_s1
      have error_free_empty: "error_free ((set_lvars empty) s1)"
	by simp
      from cls_C wf have wt_init_c: "\<lparr>prg=G, cls=C,lcl=empty\<rparr>\<turnstile>(init c)\<Colon>\<surd>"
	by (rule wf_prog_cdecl [THEN wf_cdecl_wt_init])
      moreover from cls_C wf obtain I
	where "\<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile> {} \<guillemotright>In1r (init c)\<guillemotright> I"
	by (rule wf_prog_cdecl [THEN wf_cdeclE,simplified]) blast
       (*  simplified: to rewrite \<langle>init c\<rangle> to In1r (init c) *) 
      then obtain I' where
	"\<lparr>prg=G,cls=C,lcl=empty\<rparr>\<turnstile>dom (locals (store ((set_lvars empty) s1))) 
            \<guillemotright>In1r (init c)\<guillemotright> I'"
	  by (rule da_weakenE) simp
      ultimately
      obtain conf_s2: "s2\<Colon>\<preceq>(G, empty)" and error_free_s2: "error_free s2"
	by (rule hyp_init_c [elim_format]) (simp add: error_free_empty)
      have "abrupt s2 \<noteq> Some (Jump Ret)"
      proof -
	from s1_no_ret 
	have "\<And> j. abrupt ((set_lvars empty) s1) \<noteq> Some (Jump j)"
	  by simp
	moreover
	from cls_C wf have "jumpNestingOkS {} (init c)"
	  by (rule wf_prog_cdecl [THEN wf_cdeclE])
	ultimately 
	show ?thesis
	  using eval_init wt_init_c wf
	  by - (rule eval_statement_no_jump 
                     [where ?Env="\<lparr>prg=G,cls=C,lcl=empty\<rparr>"],simp+)
      qed
      with conf_s2 s3 conf_s1 eval_init
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
    case (NewC C a s0 s1 s2 L accC T A)
    have         "G\<turnstile>Norm s0 \<midarrow>Init C\<rightarrow> s1" .
    have halloc: "G\<turnstile>s1 \<midarrow>halloc CInst C\<succ>a\<rightarrow> s2" .
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1r (Init C)) \<diamondsuit>" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    moreover
    have      wt: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>In1l (NewC C)\<Colon>T" .
    then obtain is_cls_C: "is_class G C" and
                       T: "T=Inl (Class C)"
      by (rule wt_elim_cases) (auto dest: is_acc_classD)
    hence "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>Init C\<Colon>\<surd>" by auto
    moreover obtain I where 
      "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
          \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r (Init C)\<guillemotright> I"
      by (auto intro: da_Init [simplified] assigned.select_convs)
     (* simplified: to rewrite \<langle>Init C\<rangle> to In1r (Init C) *)
    ultimately 
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by (rule hyp [elim_format]) simp 
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
    case (NewA elT a e i s0 s1 s2 s3 L accC T A)
    have eval_init: "G\<turnstile>Norm s0 \<midarrow>init_comp_ty elT\<rightarrow> s1" .
    have eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>i\<rightarrow> s2" .
    have halloc: "G\<turnstile>abupd (check_neg i) s2\<midarrow>halloc Arr elT (the_Intg i)\<succ>a\<rightarrow> s3".
    have hyp_init: "PROP ?TypeSafe (Norm s0) s1 (In1r (init_comp_ty elT)) \<diamondsuit>" .
    have hyp_size: "PROP ?TypeSafe s1 s2 (In1l e) (In1 i)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have     wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (New elT[e])\<Colon>T" .
    then obtain
      wt_init: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>init_comp_ty elT\<Colon>\<surd>" and
      wt_size: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-PrimT Integer" and
            elT: "is_type G elT" and
           T: "T=Inl (elT.[])"
      by (rule wt_elim_cases) (auto intro: wt_init_comp_ty dest: is_acc_typeD)
    from NewA.prems 
    have da_e:"\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                 \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> A"
      by (elim da_elim_cases) simp
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
    proof -
      note conf_s0 wt_init
      moreover obtain I where
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>
         \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r (init_comp_ty elT)\<guillemotright> I"
      proof (cases "\<exists>C. elT = Class C")
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
      ultimately show ?thesis
	by (rule hyp_init [elim_format]) auto
    qed 
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
    proof -
      from eval_init 
      have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
	by (rule dom_locals_eval_mono_elim)
      with da_e 
      obtain A' where
       "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
            \<turnstile> dom (locals (store s1)) \<guillemotright>In1l e\<guillemotright> A'"
	by (rule da_weakenE)
      with conf_s1 wt_size
      show ?thesis
	by (rule hyp_size [elim_format]) (simp add: that error_free_s1) 
    qed
    from conf_s2 have "abupd (check_neg i) s2\<Colon>\<preceq>(G, L)"
      by (cases s2) auto
    with halloc wf elT 
    have halloc_type_safe:
          "s3\<Colon>\<preceq>(G, L) \<and> (normal s3 \<longrightarrow> G,store s3\<turnstile>Addr a\<Colon>\<preceq>elT.[])"
      by (cases s3) (auto dest!: halloc_type_sound)
    from halloc error_free_s2
    have "error_free s3"
      by (auto dest: error_free_halloc)
    with halloc_type_safe T
    show "s3\<Colon>\<preceq>(G, L) \<and> 
          (normal s3 \<longrightarrow> G,L,store s3\<turnstile>In1l (New elT[e])\<succ>In1 (Addr a)\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free s3) "
      by simp
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Cast castT e s0 s1 s2 v L accC T A)
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
    from Cast.prems 
    have "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                 \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> A"
      by (elim da_elim_cases) simp
    with conf_s0 wt_e
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
           v_ok: "normal s1 \<longrightarrow> G,store s1\<turnstile>v\<Colon>\<preceq>eT" and
      error_free_s1: "error_free s1"
      by (rule hyp [elim_format]) simp
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
	with v_ok 
	have "G,store s1\<turnstile>v\<Colon>\<preceq>eT"
	  by simp
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
    case (Inst instT b e s0 s1 v L accC T A)
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    from Inst.prems obtain eT
    where wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-RefT eT"  and
             T: "T=Inl (PrimT Boolean)" 
      by (elim wt_elim_cases) simp
    from Inst.prems 
    have da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                 \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> A"
      by (elim da_elim_cases) simp
    from conf_s0 wt_e da_e
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
              v_ok: "normal s1 \<longrightarrow> G,store s1\<turnstile>v\<Colon>\<preceq>RefT eT" and
      error_free_s1: "error_free s1"
      by (rule hyp [elim_format]) simp
    with T show ?case
      by simp
  next
    case (Lit s v L accC T A)
    then show ?case
      by (auto elim!: wt_elim_cases 
               intro: conf_litval simp add: empty_dt_def)
  next
    case (UnOp e s0 s1 unop v L accC T A)
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 v)" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have      wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (UnOp unop e)\<Colon>T" .
    then obtain eT
      where    wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" and
            wt_unop: "wt_unop unop eT" and
                  T: "T=Inl (PrimT (unop_type unop))" 
      by (auto elim!: wt_elim_cases)
    from UnOp.prems obtain A where
       da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> A"
      by (elim da_elim_cases) simp
    from conf_s0 wt_e da_e
    obtain     conf_s1: "s1\<Colon>\<preceq>(G, L)"  and
                  wt_v: "normal s1 \<longrightarrow> G,store s1\<turnstile>v\<Colon>\<preceq>eT" and
         error_free_s1: "error_free s1"
      by (rule hyp [elim_format]) simp
    from wt_v T wt_unop
    have "normal s1\<longrightarrow>G,L,snd s1\<turnstile>In1l (UnOp unop e)\<succ>In1 (eval_unop unop v)\<Colon>\<preceq>T"
      by (cases unop) auto
    with conf_s1 error_free_s1
    show "s1\<Colon>\<preceq>(G, L) \<and>
     (normal s1 \<longrightarrow> G,L,snd s1\<turnstile>In1l (UnOp unop e)\<succ>In1 (eval_unop unop v)\<Colon>\<preceq>T) \<and>
     error_free (Norm s0) = error_free s1"
      by simp
  next
    case (BinOp binop e1 e2 s0 s1 s2 v1 v2 L accC T A)
    have eval_e1: "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>v1\<rightarrow> s1" .
    have eval_e2: "G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then In1l e2
                             else In1r Skip)\<succ>\<rightarrow> (In1 v2, s2)" .
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
      by (elim wt_elim_cases) simp
    have wt_Skip: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>Skip\<Colon>\<surd>"
      by simp
    obtain S where
      daSkip: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store s1)) \<guillemotright>In1r Skip\<guillemotright> S"
      by (auto intro: da_Skip [simplified] assigned.select_convs)
    have da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store ((Norm s0::state)))) 
                  \<guillemotright>\<langle>BinOp binop e1 e2\<rangle>\<^sub>e\<guillemotright> A".
    then obtain E1 where
      da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e1\<guillemotright> E1"
      by (elim da_elim_cases) simp+
    from conf_s0 wt_e1 da_e1
    obtain      conf_s1: "s1\<Colon>\<preceq>(G, L)"  and
                  wt_v1: "normal s1 \<longrightarrow> G,store s1\<turnstile>v1\<Colon>\<preceq>e1T" and
          error_free_s1: "error_free s1"
      by (rule hyp_e1 [elim_format]) simp
    from wt_binop T
    have conf_v:
      "G,L,snd s2\<turnstile>In1l (BinOp binop e1 e2)\<succ>In1 (eval_binop binop v1 v2)\<Colon>\<preceq>T"
      by (cases binop) auto
    -- {* Note that we don't use the information that v1 really is compatible 
          with the expected type e1T and v2 is compatible with e2T, 
          because @{text eval_binop} will anyway produce an output of 
          the right type.
          So evaluating the addition of an integer with a string is type
          safe. This is a little bit annoying since we may regard such a
          behaviour as not type safe.
          If we want to avoid this we can redefine @{text eval_binop} so that
          it only produces a output of proper type if it is assigned to 
          values of the expected types, and arbitrary if the inputs have 
          unexpected types. The proof can easily be adapted since we
          have the hypothesis that the values have a proper type.
          This also applies to unary operations.
       *}
    from eval_e1 have 
      s0_s1:"dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by (rule dom_locals_eval_mono_elim)
    show "s2\<Colon>\<preceq>(G, L) \<and>
          (normal s2 \<longrightarrow>
        G,L,snd s2\<turnstile>In1l (BinOp binop e1 e2)\<succ>In1 (eval_binop binop v1 v2)\<Colon>\<preceq>T) \<and>
          error_free (Norm s0) = error_free s2"
    proof (cases "normal s1")
      case False
      with eval_e2 have "s2=s1" by auto
      with conf_s1 error_free_s1 False show ?thesis
	by auto
    next
      case True
      note normal_s1 = this
      show ?thesis 
      proof (cases "need_second_arg binop v1")
	case False
	with normal_s1 eval_e2 have "s2=s1"
	  by (cases s1) (simp, elim eval_elim_cases,simp)
	with conf_s1 conf_v error_free_s1
	show ?thesis by simp
      next
	case True
	note need_second_arg = this
	with hyp_e2 
	have hyp_e2': "PROP ?TypeSafe s1 s2 (In1l e2) (In1 v2)" by simp
	from da wt_e1 wt_e2 wt_binop conf_s0 normal_s1 eval_e1 
          wt_v1 [rule_format,OF normal_s1] wf
	obtain E2 where
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>In1l e2\<guillemotright> E2"
	  by (rule da_e2_BinOp [elim_format]) 
             (auto simp add: need_second_arg )
	with conf_s1 wt_e2 
	obtain "s2\<Colon>\<preceq>(G, L)" and "error_free s2"
	  by (rule hyp_e2' [elim_format]) (simp add: error_free_s1)
	with conf_v show ?thesis by simp
      qed
    qed
  next
    case (Super s L accC T A)
    have conf_s: "Norm s\<Colon>\<preceq>(G, L)" .
    have     wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l Super\<Colon>T" .
    then obtain C c where
             C: "L This = Some (Class C)" and
       neq_Obj: "C\<noteq>Object" and
         cls_C: "class G C = Some c" and
             T: "T=Inl (Class (super c))"
      by (rule wt_elim_cases) auto
    from Super.prems
    obtain "This \<in> dom (locals s)"
      by (elim da_elim_cases) simp
    with conf_s C  have "G,s\<turnstile>val_this s\<Colon>\<preceq>Class C"
      by (auto dest: conforms_localD [THEN wlconfD])
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
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Acc upd s0 s1 w v L accC T A) 
    have hyp: "PROP ?TypeSafe (Norm s0) s1 (In2 v) (In2 (w,upd))" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    from Acc.prems obtain vT where
      wt_v: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>v\<Colon>=vT" and
         T: "T=Inl vT"
      by (elim wt_elim_cases) simp
    from Acc.prems obtain V where
      da_v: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In2 v\<guillemotright> V"
      by (cases "\<exists> n. v=LVar n") (insert da.LVar,auto elim!: da_elim_cases)
    {
      fix n assume lvar: "v=LVar n"
      have "locals (store s1) n \<noteq> None"
      proof -
	from Acc.prems lvar have 
	  "n \<in> dom (locals s0)"
	  by (cases "\<exists> n. v=LVar n") (auto elim!: da_elim_cases)
	also
	have "dom (locals s0) \<subseteq> dom (locals (store s1))"
	proof -
	  have "G\<turnstile>Norm s0 \<midarrow>v=\<succ>(w, upd)\<rightarrow> s1" .
	  thus ?thesis
	    by (rule dom_locals_eval_mono_elim) simp
	qed
	finally show ?thesis
	  by blast
      qed
    } note lvar_in_locals = this 
    from conf_s0 wt_v da_v
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)"
      and  conf_var: "(normal s1 \<longrightarrow> G,L,store s1\<turnstile>In2 v\<succ>In2 (w, upd)\<Colon>\<preceq>Inl vT)"
      and  error_free_s1: "error_free s1"
      by (rule hyp [elim_format]) simp
    from lvar_in_locals conf_var T
    have "(normal s1 \<longrightarrow> G,L,store s1\<turnstile>In1l (Acc v)\<succ>In1 w\<Colon>\<preceq>T)"
      by (cases "\<exists> n. v=LVar n") auto
    with conf_s1 error_free_s1 show ?case
      by simp
  next
    case (Ass e upd s0 s1 s2 v var w L accC T A)
    have eval_var: "G\<turnstile>Norm s0 \<midarrow>var=\<succ>(w, upd)\<rightarrow> s1" .
    have   eval_e: "G\<turnstile>s1 \<midarrow>e-\<succ>v\<rightarrow> s2" .
    have  hyp_var: "PROP ?TypeSafe (Norm s0) s1 (In2 var) (In2 (w,upd))" .
    have    hyp_e: "PROP ?TypeSafe s1 s2 (In1l e) (In1 v)" .
    have  conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have       wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In1l (var:=e)\<Colon>T" .
    then obtain varT eT where
	 wt_var: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>var\<Colon>=varT" and
	   wt_e: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT" and
	  widen: "G\<turnstile>eT\<preceq>varT" and
              T: "T=Inl eT"
      by (rule wt_elim_cases) auto
    show "assign upd v s2\<Colon>\<preceq>(G, L) \<and>
           (normal (assign upd v s2) \<longrightarrow>
            G,L,store (assign upd v s2)\<turnstile>In1l (var:=e)\<succ>In1 v\<Colon>\<preceq>T) \<and>
      (error_free (Norm s0) = error_free (assign upd v s2))"
    proof (cases "\<exists> vn. var=LVar vn")
      case False
      with Ass.prems
      obtain V E where
	da_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In2 var\<guillemotright> V" and
	da_e:   "\<lparr>prg=G,cls=accC,lcl=L\<rparr> \<turnstile> nrm V \<guillemotright>In1l e\<guillemotright> E"
	by (elim da_elim_cases) simp+
      from conf_s0 wt_var da_var 
      obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" 
	and  conf_var: "normal s1 
                         \<longrightarrow> G,L,store s1\<turnstile>In2 var\<succ>In2 (w, upd)\<Colon>\<preceq>Inl varT"
	and  error_free_s1: "error_free s1"
	by (rule hyp_var [elim_format]) simp
      show ?thesis
      proof (cases "normal s1")
	case False
	with eval_e have "s2=s1" by auto
	with False have "assign upd v s2=s1"
	  by simp
	with conf_s1 error_free_s1 False show ?thesis
	  by auto
      next
	case True
	note normal_s1=this
	obtain A' where "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                         \<turnstile> dom (locals (store s1)) \<guillemotright>In1l e\<guillemotright> A'"
	proof -
	  from eval_var wt_var da_var wf normal_s1
	  have "nrm V \<subseteq>  dom (locals (store s1))"
	    by (cases rule: da_good_approxE') rules
	  with da_e show ?thesis
	    by (rule da_weakenE) 
	qed
	with conf_s1 wt_e 
	obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and 
          conf_v: "normal s2 \<longrightarrow> G,store s2\<turnstile>v\<Colon>\<preceq>eT" and
          error_free_s2: "error_free s2"
	  by (rule hyp_e [elim_format]) (simp add: error_free_s1)
	show ?thesis 
	proof (cases "normal s2")
	  case False
	  with conf_s2 error_free_s2 
	  show ?thesis
	    by auto
	next
	  case True
	  from True conf_v
	  have conf_v_eT: "G,store s2\<turnstile>v\<Colon>\<preceq>eT"
	    by simp
	  with widen wf
	  have conf_v_varT: "G,store s2\<turnstile>v\<Colon>\<preceq>varT"
	    by (auto intro: conf_widen)
	  from normal_s1 conf_var
	  have "G,L,store s1\<turnstile>In2 var\<succ>In2 (w, upd)\<Colon>\<preceq>Inl varT"
	    by simp
	  then 
	  have conf_assign:  "store s1\<le>|upd\<preceq>varT\<Colon>\<preceq>(G, L)" 
	    by (simp add: rconf_def)
	  from conf_v_eT conf_v_varT conf_assign normal_s1 True wf eval_var 
	    eval_e T conf_s2 error_free_s2
	  show ?thesis
	    by (cases s1, cases s2) 
	       (auto dest!: Ass_lemma simp add: assign_conforms_def)
	qed
      qed
    next
      case True
      then obtain vn where vn: "var=LVar vn"
	by blast
      with Ass.prems
      obtain E where
	da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr> 
	           \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1l e\<guillemotright> E"
	by (elim da_elim_cases) simp+
      from da.LVar vn obtain V where
	da_var: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In2 var\<guillemotright> V"
	by auto
      obtain E' where
	da_e': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> dom (locals (store s1)) \<guillemotright>In1l e\<guillemotright> E'"
      proof -
	have "dom (locals (store ((Norm s0)::state))) 
                \<subseteq> dom (locals (store (s1)))"
	  by (rule dom_locals_eval_mono_elim)
	with da_e show ?thesis
	  by (rule da_weakenE)
      qed
      from conf_s0 wt_var da_var 
      obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" 
	and  conf_var: "normal s1 
                         \<longrightarrow> G,L,store s1\<turnstile>In2 var\<succ>In2 (w, upd)\<Colon>\<preceq>Inl varT"
	and  error_free_s1: "error_free s1"
	by (rule hyp_var [elim_format]) simp
      show ?thesis
      proof (cases "normal s1")
	case False
	with eval_e have "s2=s1" by auto
	with False have "assign upd v s2=s1"
	  by simp
	with conf_s1 error_free_s1 False show ?thesis
	  by auto
      next
	case True
	note normal_s1 = this
	from conf_s1 wt_e da_e'
	obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and 
          conf_v: "normal s2 \<longrightarrow> G,store s2\<turnstile>v\<Colon>\<preceq>eT" and
          error_free_s2: "error_free s2"
	  by (rule hyp_e [elim_format]) (simp add: error_free_s1)
	show ?thesis 
	proof (cases "normal s2")
	  case False
	  with conf_s2 error_free_s2 
	  show ?thesis
	    by auto
	next
	  case True
	  from True conf_v
	  have conf_v_eT: "G,store s2\<turnstile>v\<Colon>\<preceq>eT"
	    by simp
	  with widen wf
	  have conf_v_varT: "G,store s2\<turnstile>v\<Colon>\<preceq>varT"
	    by (auto intro: conf_widen)
	  from normal_s1 conf_var
	  have "G,L,store s1\<turnstile>In2 var\<succ>In2 (w, upd)\<Colon>\<preceq>Inl varT"
	    by simp
	  then 
	  have conf_assign:  "store s1\<le>|upd\<preceq>varT\<Colon>\<preceq>(G, L)" 
	    by (simp add: rconf_def)
	  from conf_v_eT conf_v_varT conf_assign normal_s1 True wf eval_var 
	    eval_e T conf_s2 error_free_s2
	  show ?thesis
	    by (cases s1, cases s2) 
	       (auto dest!: Ass_lemma simp add: assign_conforms_def)
	qed
      qed
    qed
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Cond b e0 e1 e2 s0 s1 s2 v L accC T A)
    have eval_e0: "G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1" .
    have eval_e1_e2: "G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<rightarrow> s2" .
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
    with Cond.prems obtain E0 E1 E2 where
         da_e0: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> dom (locals (store ((Norm s0)::state))) 
                      \<guillemotright>In1l e0\<guillemotright> E0" and
         da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> (dom (locals (store ((Norm s0)::state))) 
                         \<union> assigns_if True e0) \<guillemotright>In1l e1\<guillemotright> E1" and
         da_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                  \<turnstile> (dom (locals (store ((Norm s0)::state))) 
                        \<union> assigns_if False e0) \<guillemotright>In1l e2\<guillemotright> E2"
       by (elim da_elim_cases) simp+
    from conf_s0 wt_e0 da_e0  
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1" 
      by (rule hyp_e0 [elim_format]) simp
    show "s2\<Colon>\<preceq>(G, L) \<and>
           (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1l (e0 ? e1 : e2)\<succ>In1 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s2)"
    proof (cases "normal s1")
      case False
      with eval_e1_e2 have "s2=s1" by auto
      with conf_s1 error_free_s1 False show ?thesis
	by auto
    next
      case True
      have s0_s1: "dom (locals (store ((Norm s0)::state))) 
                    \<union> assigns_if (the_Bool b) e0 \<subseteq> dom (locals (store s1))"
      proof -
	from eval_e0 have 
	  "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
	  by (rule dom_locals_eval_mono_elim)
        moreover
	from eval_e0 True wt_e0 
	have "assigns_if (the_Bool b) e0 \<subseteq> dom (locals (store s1))"
	  by (rule assigns_if_good_approx') 
	ultimately show ?thesis by (rule Un_least)
      qed 
      show ?thesis
      proof (cases "the_Bool b")
	case True
	with hyp_if have hyp_e1: "PROP ?TypeSafe s1 s2 (In1l e1) (In1 v)" 
	  by simp
	from da_e1 s0_s1 True obtain E1' where
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s1)))\<guillemotright>In1l e1\<guillemotright> E1'"
	  by - (rule da_weakenE,auto)
	with conf_s1 wt_e1
	obtain 
	  "s2\<Colon>\<preceq>(G, L)"
	  "(normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1l e1\<succ>In1 v\<Colon>\<preceq>Inl T1)"
	  "error_free s2"            
	  by (rule hyp_e1 [elim_format]) (simp add: error_free_s1)
	moreover
	from statT  
	have "G\<turnstile>T1\<preceq>statT"
	  by auto
	ultimately show ?thesis
	  using T wf by auto
      next
	case False
	with hyp_if have hyp_e2: "PROP ?TypeSafe s1 s2 (In1l e2) (In1 v)" 
	  by simp
	from da_e2 s0_s1 False obtain E2' where
	  "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s1)))\<guillemotright>In1l e2\<guillemotright> E2'"
	  by - (rule da_weakenE,auto)
	with conf_s1 wt_e2
	obtain 
	  "s2\<Colon>\<preceq>(G, L)"
	  "(normal s2 \<longrightarrow> G,L,store s2\<turnstile>In1l e2\<succ>In1 v\<Colon>\<preceq>Inl T2)"
	  "error_free s2"            
	  by (rule hyp_e2 [elim_format]) (simp add: error_free_s1)
	moreover
	from statT  
	have "G\<turnstile>T2\<preceq>statT"
	  by auto
	ultimately show ?thesis
	  using T wf by auto
      qed
    qed
  next
    case (Call invDeclC a accC' args e mn mode pTs' s0 s1 s2 s3 s3' s4 statT 
           v vs L accC T A)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1" .
    have eval_args: "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<rightarrow> s2" .
    have invDeclC: "invDeclC 
                      = invocation_declclass G mode (store s2) a statT 
                           \<lparr>name = mn, parTs = pTs'\<rparr>" .
    have init_lvars: 
           "s3 = init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> mode a vs s2".
    have check: "s3' =
       check_method_access G accC' statT mode \<lparr>name = mn, parTs = pTs'\<rparr> a s3" .
    have eval_methd: 
           "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>-\<succ>v\<rightarrow> s4" .
    have     hyp_e: "PROP ?TypeSafe (Norm s0) s1 (In1l e) (In1 a)" .
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
    from Call.prems obtain E where
      da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
               \<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>In1l e\<guillemotright> E" and
      da_args: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm E \<guillemotright>In3 args\<guillemotright> A" 
      by (elim da_elim_cases) simp
    from conf_s0 wt_e da_e  
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
           conf_a: "normal s1 \<Longrightarrow> G, store s1\<turnstile>a\<Colon>\<preceq>RefT statT" and
           error_free_s1: "error_free s1" 
      by (rule hyp_e [elim_format]) simp
    { 
      assume abnormal_s2: "\<not> normal s2"
      have "set_lvars (locals (store s2)) s4 = s2"
      proof -
	from abnormal_s2 init_lvars 
	obtain keep_abrupt: "abrupt s3 = abrupt s2" and
             "store s3 = store (init_lvars G invDeclC \<lparr>name = mn, parTs = pTs'\<rparr> 
                                            mode a vs s2)" 
	  by (auto simp add: init_lvars_def2)
	moreover
	from keep_abrupt abnormal_s2 check
	have eq_s3'_s3: "s3'=s3" 
	  by (auto simp add: check_method_access_def Let_def)
	moreover
	from eq_s3'_s3 abnormal_s2 keep_abrupt eval_methd
	have "s4=s3'"
	  by auto
	ultimately show
	  "set_lvars (locals (store s2)) s4 = s2"
	  by (cases s2,cases s3) (simp add: init_lvars_def2)
      qed
    } note propagate_abnormal_s2 = this
    show "(set_lvars (locals (store s2))) s4\<Colon>\<preceq>(G, L) \<and>
           (normal ((set_lvars (locals (store s2))) s4) \<longrightarrow>
             G,L,store ((set_lvars (locals (store s2))) s4)
               \<turnstile>In1l ({accC',statT,mode}e\<cdot>mn( {pTs'}args))\<succ>In1 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) =
                error_free ((set_lvars (locals (store s2))) s4))"
    proof (cases "normal s1")
      case False
      with eval_args have "s2=s1" by auto
      with False propagate_abnormal_s2 conf_s1 error_free_s1 
      show ?thesis
	by auto
    next
      case True
      note normal_s1 = this
      obtain A' where 
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>In3 args\<guillemotright> A'"
      proof -
	from eval_e wt_e da_e wf normal_s1
	have "nrm E \<subseteq>  dom (locals (store s1))"
	  by (cases rule: da_good_approxE') rules
	with da_args show ?thesis
	  by (rule da_weakenE) 
      qed
      with conf_s1 wt_args 
      obtain    conf_s2: "s2\<Colon>\<preceq>(G, L)" and
              conf_args: "normal s2 
                         \<Longrightarrow>  list_all2 (conf G (store s2)) vs pTs" and
          error_free_s2: "error_free s2" 
	by (rule hyp_args [elim_format]) (simp add: error_free_s1)
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
	where invC: "invC = invocation_class mode (store s2) a statT"
	by simp
      with init_lvars
      have invC': "invC = (invocation_class mode (store s3) a statT)"
	by (cases s2,cases mode) (auto simp add: init_lvars_def2 )
      show ?thesis
      proof (cases "normal s2")
	case False
	with propagate_abnormal_s2 conf_s2 error_free_s2
	show ?thesis
	  by auto
      next
	case True
	note normal_s2 = True
	with normal_s1 conf_a eval_args 
	have conf_a_s2: "G, store s2\<turnstile>a\<Colon>\<preceq>RefT statT"
	  by (auto dest: eval_gext intro: conf_gext)
	show ?thesis
	proof (cases "a=Null \<longrightarrow> is_static statM")
	  case False
	  then obtain not_static: "\<not> is_static statM" and Null: "a=Null" 
	    by blast
	  with normal_s2 init_lvars mode
	  obtain np: "abrupt s3 = Some (Xcpt (Std NullPointer))" and
                     "store s3 = store (init_lvars G invDeclC 
                                       \<lparr>name = mn, parTs = pTs'\<rparr> mode a vs s2)"
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
	    by (cases s2,cases s3) (simp add: init_lvars_def2)
	  with conf_s2 error_free_s2
	  show ?thesis
	    by (cases s2) (auto dest: conforms_NormI)
	next
	  case True
	  with mode have notNull: "mode = IntVir \<longrightarrow> a \<noteq> Null"
	    by (auto dest!: Null_staticD)
	  with conf_s2 conf_a_s2 wf invC  
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
	    apply (simp add: normal_s2)
	    apply (cases s2, simp add: L' init_lvars
	                     cong add: lname.case_cong ename.case_cong)
	    done
	  with eq_s3'_s3 
	  have conf_s3': "s3'\<Colon>\<preceq>(G,L')" by simp
	  moreover
	  from  is_static_eq wf_dynM L'
	  obtain mthdT where
	    "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
               \<turnstile>Body invDeclC (stmt (mbody (mthd dynM)))\<Colon>-mthdT" and
	    mthdT_widen: "G\<turnstile>mthdT\<preceq>resTy dynM"
	    by - (drule wf_mdecl_bodyD,
                 auto simp add: callee_lcl_def  
                      cong add: lname.case_cong ename.case_cong)
	  with dynM' iscls_invDeclC invDeclC'
	  have
	    "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr>
               \<turnstile>(Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)\<Colon>-mthdT"
	    by (auto intro: wt.Methd)
	  moreover
	  obtain M where 
	    "\<lparr>prg=G,cls=invDeclC,lcl=L'\<rparr> 
	       \<turnstile> dom (locals (store s3')) 
	          \<guillemotright>In1l (Methd invDeclC \<lparr>name = mn, parTs = pTs'\<rparr>)\<guillemotright> M"
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
	      moreover
	      have "length (pars (mthd dynM)) = length vs" 
	      proof -
		from normal_s2 conf_args
		have "length vs = length pTs"
		  by (simp add: list_all2_def)
		also from pTs_widen
		have "\<dots> = length pTs'"
		  by (simp add: widens_def list_all2_def)
		also from wf_dynM
		have "\<dots> = length (pars (mthd dynM))"
		  by (simp add: wf_mdecl_def wf_mhead_def)
		finally show ?thesis ..
	      qed
	      moreover note init_lvars dynM' is_static_eq normal_s2 mode 
	      ultimately
	      have "parameters (mthd dynM) = dom (locals (store s3))"
		using dom_locals_init_lvars 
                  [of "mthd dynM" G invDeclC "\<lparr>name=mn,parTs=pTs'\<rparr>" vs e a s2]
		by simp
	      also from check
	      have "dom (locals (store s3)) \<subseteq>  dom (locals (store s3'))"
		by (simp add:  eq_s3'_s3)
	      finally show ?thesis .
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
	  ultimately obtain  
	    conf_s4: "s4\<Colon>\<preceq>(G, L')" and 
	    conf_Res: "normal s4 \<longrightarrow> G,store s4\<turnstile>v\<Colon>\<preceq>mthdT" and
	    error_free_s4: "error_free s4"
	    by (rule hyp_methd [elim_format]) 
               (simp add: error_free_s3 eq_s3'_s3)
	  from init_lvars eval_methd eq_s3'_s3 
	  have "store s2\<le>|store s4"
	    by (cases s2) (auto dest!: eval_gext simp add: init_lvars_def2 )
	  moreover
	  have "abrupt s4 \<noteq> Some (Jump Ret)"
	  proof -
	    from normal_s2 init_lvars
	    have "abrupt s3 \<noteq> Some (Jump Ret)"
	      by (cases s2) (simp add: init_lvars_def2 abrupt_if_def)
	    with check
	    have "abrupt s3' \<noteq> Some (Jump Ret)"
	      by (cases s3) (auto simp add: check_method_access_def Let_def)
	    with eval_methd
	    show ?thesis
	      by (rule Methd_no_jump)
	  qed
	  ultimately 
	  have "(set_lvars (locals (store s2))) s4\<Colon>\<preceq>(G, L)"
	    using conf_s2 conf_s4
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
    qed
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Methd D s0 s1 sig v L accC T A)
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
    moreover
    from Methd.prems m have 
       da_body: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> (dom (locals (store ((Norm s0)::state))))
                       \<guillemotright>In1l (Body (declclass m) (stmt (mbody (mthd m))))\<guillemotright> A"
      by - (erule da_elim_cases,simp)
    ultimately
    show "s1\<Colon>\<preceq>(G, L) \<and> 
           (normal s1 \<longrightarrow> G,L,snd s1\<turnstile>In1l (Methd D sig)\<succ>In1 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s1)"
      using hyp [of _ _ "(Inl bodyT)"] conf_s0 
      by (auto simp add: Let_def body_def)
  next
    case (Body D c s0 s1 s2 s3 L accC T A)
    have eval_init: "G\<turnstile>Norm s0 \<midarrow>Init D\<rightarrow> s1" .
    have eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" .
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
    from Body.prems obtain C where
      da_c: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                   \<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>In1r c\<guillemotright> C" and
      jmpOk: "jumpNestingOkS {Ret} c" and
      res: "Result \<in> nrm C"
      by (elim da_elim_cases) simp
    note conf_s0
    moreover from iscls_D 
    have "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>Init D\<Colon>\<surd>" by auto
    moreover obtain I where 
      "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
          \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r (Init D)\<guillemotright> I"
      by (auto intro: da_Init [simplified] assigned.select_convs)
    ultimately obtain
      conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1:  "error_free s1"
       by (rule hyp_init [elim_format]) simp
    obtain C' where da_C': "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                             \<turnstile> (dom (locals (store s1)))\<guillemotright>In1r c\<guillemotright> C'"
               and nrm_C': "nrm C \<subseteq> nrm C'"
    proof -
      from eval_init 
      have "(dom (locals (store ((Norm s0)::state)))) 
                     \<subseteq> (dom (locals (store s1)))"
	by (rule dom_locals_eval_mono_elim)
      with da_c show ?thesis by (rule da_weakenE)
    qed
    from conf_s1 wt_c da_C' 
    obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
      by (rule hyp_c [elim_format]) (simp add: error_free_s1)
    from conf_s2
    have "abupd (absorb Ret) s2\<Colon>\<preceq>(G, L)"
      by (cases s2) (auto intro: conforms_absorb)
    moreover
    from error_free_s2
    have "error_free (abupd (absorb Ret) s2)"
      by simp
    moreover have "abrupt (abupd (absorb Ret) s3) \<noteq> Some (Jump Ret)"
      by (cases s3) (simp add: absorb_def)
    moreover have "s3=s2"
    proof -
      from iscls_D
      have wt_init: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(Init D)\<Colon>\<surd>"
	by auto
      from eval_init wf
      have s1_no_jmp: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	by - (rule eval_statement_no_jump [OF _ _ _ wt_init],auto)
      from eval_c _ wt_c wf
      have "\<And> j. abrupt s2 = Some (Jump j) \<Longrightarrow> j=Ret"
	by (rule jumpNestingOk_evalE) (auto intro: jmpOk simp add: s1_no_jmp)
      moreover 
      have "s3 =
                (if \<exists>l. abrupt s2 = Some (Jump (Break l)) \<or> 
                        abrupt s2 = Some (Jump (Cont l))
                 then abupd (\<lambda>x. Some (Error CrossMethodJump)) s2 else s2)" .
      ultimately show ?thesis 
	by force
    qed
    moreover
    {
      assume normal_upd_s2:  "normal (abupd (absorb Ret) s2)"
      have "Result \<in> dom (locals (store s2))"
      proof -
	from normal_upd_s2
	have "normal s2 \<or> abrupt s2 = Some (Jump Ret)"
	  by (cases s2) (simp add: absorb_def)
	thus ?thesis
	proof 
	  assume "normal s2"
	  with eval_c wt_c da_C' wf res nrm_C'
	  show ?thesis
	    by (cases rule: da_good_approxE') blast
	next
	  assume "abrupt s2 = Some (Jump Ret)"
	  with conf_s2 show ?thesis
	    by (cases s2) (auto dest: conforms_RetD simp add: dom_def)
	qed 
      qed
    }
    moreover note T resultT
    ultimately
    show "abupd (absorb Ret) s3\<Colon>\<preceq>(G, L) \<and>
           (normal (abupd (absorb Ret) s3) \<longrightarrow>
             G,L,store (abupd (absorb Ret) s3)
             \<turnstile>In1l (Body D c)\<succ>In1 (the (locals (store s2) Result))\<Colon>\<preceq>T) \<and>
          (error_free (Norm s0) = error_free (abupd (absorb Ret) s3)) "
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
    have conf_fst: "locals s vn \<noteq> None \<longrightarrow> G,s\<turnstile>fst (lvar vn s)\<Colon>\<preceq>vnT"  
     by (auto elim: conforms_localD [THEN wlconfD]  
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
      by (simp add: lvar_def) 
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v L accC' T A)
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
    from FVar.prems eq_accC_accC'
    have da_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>
                 \<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>In1l e\<guillemotright> A"
      by (elim da_elim_cases) simp
    note conf_s0
    moreover
    from wf wt_e 
    have iscls_statC: "is_class G statC"
      by (auto dest: ty_expr_is_type type_is_class)
    with wf accfield 
    have iscls_statDeclC: "is_class G statDeclC"
      by (auto dest!: accfield_fields dest: fields_declC)
    hence "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(Init statDeclC)\<Colon>\<surd>"
      by simp
    moreover obtain I where 
      "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
        \<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>In1r (Init statDeclC)\<guillemotright> I"
      by (auto intro: da_Init [simplified] assigned.select_convs)
    ultimately 
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1"
      by (rule hyp_init [elim_format]) simp
    obtain A' where 
      "\<lparr>prg=G, cls=accC, lcl=L\<rparr> \<turnstile> (dom (locals (store s1)))\<guillemotright>In1l e\<guillemotright> A'"
    proof -
      from eval_init
      have "(dom (locals (store ((Norm s0)::state)))) 
	       \<subseteq> (dom (locals (store s1)))"
	by (rule dom_locals_eval_mono_elim)
      with da_e show ?thesis
	by (rule da_weakenE)
    qed
    with conf_s1 wt_e 
    obtain       conf_s2: "s2\<Colon>\<preceq>(G, L)" and
                  conf_a: "normal s2 \<longrightarrow> G,store s2\<turnstile>a\<Colon>\<preceq>Class statC" and
           error_free_s2: "error_free s2"
      by (rule hyp_e [elim_format]) (simp add: error_free_s1)
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
    case (AVar a e1 e2 i s0 s1 s2 s2' v L accC T A)
    have eval_e1: "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>a\<rightarrow> s1" .
    have eval_e2: "G\<turnstile>s1 \<midarrow>e2-\<succ>i\<rightarrow> s2" .
    have hyp_e1: "PROP ?TypeSafe (Norm s0) s1 (In1l e1) (In1 a)" .
    have hyp_e2: "PROP ?TypeSafe s1 s2 (In1l e2) (In1 i)" .
    have avar: "(v, s2') = avar G i a s2" .
    have conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" .
    have wt:  "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>In2 (e1.[e2])\<Colon>T" .
    then obtain elemT
       where wt_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e1\<Colon>-elemT.[]" and
             wt_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e2\<Colon>-PrimT Integer" and
                 T: "T= Inl elemT"
      by (rule wt_elim_cases) auto
    from AVar.prems obtain E1 where
      da_e1: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                \<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>In1l e1\<guillemotright> E1" and
      da_e2: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm E1 \<guillemotright>In1l e2\<guillemotright> A" 
      by (elim da_elim_cases) simp
    from conf_s0 wt_e1 da_e1  
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and
            conf_a: "(normal s1 \<longrightarrow> G,store s1\<turnstile>a\<Colon>\<preceq>elemT.[])" and
            error_free_s1: "error_free s1"
      by (rule hyp_e1 [elim_format]) simp
    show "s2'\<Colon>\<preceq>(G, L) \<and>
           (normal s2' \<longrightarrow> G,L,store s2'\<turnstile>In2 (e1.[e2])\<succ>In2 v\<Colon>\<preceq>T) \<and>
           (error_free (Norm s0) = error_free s2') "
    proof (cases "normal s1")
      case False
      moreover
      from False eval_e2 have eq_s2_s1: "s2=s1" by auto
      moreover
      from eq_s2_s1 False have  "\<not> normal s2" by simp
      then have "snd (avar G i a s2) = s2"
	by (cases s2) (simp add: avar_def2)
      with avar have "s2'=s2"
	by (cases "(avar G i a s2)") simp
      ultimately show ?thesis
	using conf_s1 error_free_s1
	by auto
    next
      case True
      obtain A' where 
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>In1l e2\<guillemotright> A'"
      proof -
	from eval_e1 wt_e1 da_e1 wf True
	have "nrm E1 \<subseteq> dom (locals (store s1))"
	  by (cases rule: da_good_approxE') rules
	with da_e2 show ?thesis
	  by (rule da_weakenE)
      qed
      with conf_s1 wt_e2
      obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and error_free_s2: "error_free s2"
	by (rule hyp_e2 [elim_format]) (simp add: error_free_s1)
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
      show ?thesis 
	by auto
    qed
  next
    case (Nil s0 L accC T)
    then show ?case
      by (auto elim!: wt_elim_cases)
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Cons e es s0 s1 s2 v vs L accC T A)
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
    from Cons.prems obtain E where
      da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                \<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>In1l e\<guillemotright> E" and
      da_es: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> nrm E \<guillemotright>In3 es\<guillemotright> A" 
      by (elim da_elim_cases) simp
    from conf_s0 wt_e da_e 
    obtain conf_s1: "s1\<Colon>\<preceq>(G, L)" and error_free_s1: "error_free s1" and 
      conf_v: "normal s1 \<longrightarrow> G,store s1\<turnstile>v\<Colon>\<preceq>eT"
      by (rule hyp_e [elim_format]) simp
    show 
      "s2\<Colon>\<preceq>(G, L) \<and> 
      (normal s2 \<longrightarrow> G,L,store s2\<turnstile>In3 (e # es)\<succ>In3 (v # vs)\<Colon>\<preceq>T) \<and>
      (error_free (Norm s0) = error_free s2)"
    proof (cases "normal s1")
      case False
      with eval_es have "s2=s1" by auto
      with False conf_s1 error_free_s1
      show ?thesis
	by auto
    next
      case True
      obtain A' where 
	"\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>In3 es\<guillemotright> A'"
      proof -
	from eval_e wt_e da_e wf True
	have "nrm E \<subseteq> dom (locals (store s1))"
	  by (cases rule: da_good_approxE') rules
	with da_es show ?thesis
	  by (rule da_weakenE)
      qed
      with conf_s1 wt_es
      obtain conf_s2: "s2\<Colon>\<preceq>(G, L)" and 
           error_free_s2: "error_free s2" and
           conf_vs: "normal s2 \<longrightarrow> list_all2 (conf G (store s2)) vs esT"
	by (rule hyp_es [elim_format]) (simp add: error_free_s1)
      moreover
      from True eval_es conf_v 
      have conf_v': "G,store s2\<turnstile>v\<Colon>\<preceq>eT"
	apply clarify
	apply (rule conf_gext)
	apply (auto dest: eval_gext)
	done
      ultimately show ?thesis using T by simp
    qed
  qed
  then show ?thesis .
qed

text {* 


*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)

corollary eval_type_soundE [consumes 5]:
  assumes eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v, s1)"
  and     conf: "s0\<Colon>\<preceq>(G, L)"
  and       wt: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>t\<Colon>T"
  and       da: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile> dom (locals (snd s0)) \<guillemotright>t\<guillemotright> A"
  and       wf: "wf_prog G"
  and     elim: "\<lbrakk>s1\<Colon>\<preceq>(G, L); normal s1 \<Longrightarrow> G,L,snd s1\<turnstile>t\<succ>v\<Colon>\<preceq>T; 
                  error_free s0 = error_free s1\<rbrakk> \<Longrightarrow> P"
  shows "P"
using eval wt da wf conf
by (rule eval_type_sound [elim_format]) (rules intro: elim) 

 
corollary eval_ts: 
 "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v \<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>-T;
   \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>In1l e\<guillemotright>A\<rbrakk> 
\<Longrightarrow>  s'\<Colon>\<preceq>(G,L) \<and> (normal s' \<longrightarrow> G,store s'\<turnstile>v\<Colon>\<preceq>T) \<and> 
     (error_free s = error_free s')"
apply (drule (4) eval_type_sound)
apply clarsimp
done

corollary evals_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>es\<doteq>\<succ>vs\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>es\<Colon>\<doteq>Ts;
  \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>In3 es\<guillemotright>A\<rbrakk> 
\<Longrightarrow>  s'\<Colon>\<preceq>(G,L) \<and> (normal s' \<longrightarrow> list_all2 (conf G (store s')) vs Ts) \<and> 
     (error_free s = error_free s')" 
apply (drule (4) eval_type_sound)
apply clarsimp
done

corollary evar_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>v=\<succ>vf\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>v\<Colon>=T;
 \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>In2 v\<guillemotright>A\<rbrakk> \<Longrightarrow>  
  s'\<Colon>\<preceq>(G,L) \<and> (normal s' \<longrightarrow> G,L,(store s')\<turnstile>In2 v\<succ>In2 vf\<Colon>\<preceq>Inl T) \<and> 
  (error_free s = error_free s')"
apply (drule (4) eval_type_sound)
apply clarsimp
done

theorem exec_ts: 
"\<lbrakk>G\<turnstile>s \<midarrow>c\<rightarrow> s'; wf_prog G; s\<Colon>\<preceq>(G,L); \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>;
 \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store s))\<guillemotright>In1r c\<guillemotright>A\<rbrakk> 
 \<Longrightarrow> s'\<Colon>\<preceq>(G,L) \<and> (error_free s \<longrightarrow> error_free s')"
apply (drule (4) eval_type_sound)
apply clarsimp
done

lemma wf_eval_Fin: 
  assumes wf:    "wf_prog G" 
    and   wt_c1: "\<lparr>prg = G, cls = C, lcl = L\<rparr>\<turnstile>In1r c1\<Colon>Inl (PrimT Void)"
    and   da_c1: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>dom (locals (store (Norm s0)))\<guillemotright>In1r c1\<guillemotright>A"
    and conf_s0: "Norm s0\<Colon>\<preceq>(G, L)" 
    and eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> (x1,s1)" 
    and eval_c2: "G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2" 
    and      s3: "s3=abupd (abrupt_if (x1\<noteq>None) x1) s2"
  shows "G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<rightarrow> s3"
proof -
  from eval_c1 wt_c1 da_c1 wf conf_s0
  have "error_free (x1,s1)"
    by (auto dest: eval_type_sound)
  with eval_c1 eval_c2 s3
  show ?thesis
    by - (rule eval.Fin, auto simp add: error_free_def)
qed

subsection "Ideas for the future"

text {* In the type soundness proof and the correctness proof of 
definite assignment we perform induction on the evaluation relation with the 
further preconditions that the term is welltyped and definitely assigned. During
the proofs we have to establish the welltypedness and definite assignment of 
the subterms to be able to apply the induction hypothesis. So large parts of
both proofs are the same work in propagating welltypedness and definite 
assignment. So we can derive a new induction rule for induction on the 
evaluation of a wellformed term, were these propagations is already done, once
and forever. 
Then we can do the proofs with this rule and can enjoy the time we have saved.
Here is a first and incomplete sketch of such a rule.*}
theorem wellformed_eval_induct [consumes 4, case_names Abrupt Skip Expr Lab 
                                Comp If]:
  assumes  eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" 
   and      wt: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T" 
   and      da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>A"
   and      wf: "wf_prog G" 
   and  abrupt: "\<And> s t abr L accC T A. 
                  \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T; 
                   \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store (Some abr,s)))\<guillemotright>t\<guillemotright>A
                  \<rbrakk> \<Longrightarrow> P L accC (Some abr, s) t (arbitrary3 t) (Some abr, s)"
   and    skip: "\<And> s L accC. P L accC (Norm s) \<langle>Skip\<rangle>\<^sub>s \<diamondsuit> (Norm s)"
   and    expr: "\<And> e s0 s1 v L accC eT E.
                 \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-eT;
                  \<lparr>prg=G,cls=accC,lcl=L\<rparr>
                     \<turnstile>dom (locals (store ((Norm s0)::state)))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright>E;
                  P L accC (Norm s0) \<langle>e\<rangle>\<^sub>e \<lfloor>v\<rfloor>\<^sub>e s1\<rbrakk> 
                 \<Longrightarrow>  P L accC (Norm s0) \<langle>Expr e\<rangle>\<^sub>s \<diamondsuit> s1"
   and     lab: "\<And> c l s0 s1 L accC C.
                 \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c\<Colon>\<surd>;
                  \<lparr>prg=G,cls=accC, lcl=L\<rparr>
                     \<turnstile>dom (locals (store ((Norm s0)::state)))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright>C;
                  P L accC (Norm s0) \<langle>c\<rangle>\<^sub>s \<diamondsuit> s1\<rbrakk>
                  \<Longrightarrow> P L accC (Norm s0) \<langle>l\<bullet> c\<rangle>\<^sub>s \<diamondsuit> (abupd (absorb l) s1)"
   and    comp: "\<And> c1 c2 s0 s1 s2 L accC C1.
                 \<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1 \<rightarrow> s1;G\<turnstile>s1 \<midarrow>c2 \<rightarrow> s2;
                  \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c1\<Colon>\<surd>;
                  \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>c2\<Colon>\<surd>;
                  \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
                     dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1;
                  P L accC (Norm s0) \<langle>c1\<rangle>\<^sub>s \<diamondsuit> s1;
                  \<And> Q. \<lbrakk>normal s1; 
                         \<And> C2.\<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>
                                  \<turnstile>dom (locals (store s1)) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2;
                               P L accC s1 \<langle>c2\<rangle>\<^sub>s \<diamondsuit> s2\<rbrakk> \<Longrightarrow> Q
                        \<rbrakk> \<Longrightarrow> Q 
                  \<rbrakk>\<Longrightarrow> P L accC (Norm s0) \<langle>c1;; c2\<rangle>\<^sub>s \<diamondsuit> s2" 
    and    if: "\<And> b c1 c2 e s0 s1 s2 L accC E.
                \<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1;
                 G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2;
                 \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean;
                 \<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>;
                 \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
                     dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E;
                 P L accC (Norm s0) \<langle>e\<rangle>\<^sub>e \<lfloor>b\<rfloor>\<^sub>e s1;
                 \<And> Q. \<lbrakk>normal s1;
                        \<And> C. \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s1)))
                                   \<guillemotright>\<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s\<guillemotright> C;
                              P L accC s1 \<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s \<diamondsuit> s2
                              \<rbrakk> \<Longrightarrow> Q
                       \<rbrakk> \<Longrightarrow> Q
                \<rbrakk> \<Longrightarrow> P L accC (Norm s0) \<langle>If(e) c1 Else c2\<rangle>\<^sub>s \<diamondsuit> s2" 
   shows "P L accC s0 t v s1"  
proof -
  note inj_term_simps [simp]
  from eval 
  show "\<And> L accC T A. \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>t\<Colon>T;
                       \<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s0))\<guillemotright>t\<guillemotright>A\<rbrakk>  
        \<Longrightarrow> P L accC s0 t v s1" (is "PROP ?Hyp s0 t v s1")
  proof (induct)
    case Abrupt with abrupt show ?case .
  next
    case Skip from skip show ?case by simp
  next
    case (Expr e s0 s1 v L accC T A) 
    from Expr.prems obtain eT where 
      "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>e\<Colon>-eT"
      by (elim wt_elim_cases) 
    moreover
    from Expr.prems obtain E where
      "\<lparr>prg=G,cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store ((Norm s0)::state)))\<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright>E"
      by (elim da_elim_cases) simp
    moreover from calculation
    have "P L accC (Norm s0) \<langle>e\<rangle>\<^sub>e \<lfloor>v\<rfloor>\<^sub>e s1"
      by (rule Expr.hyps) 
    ultimately show ?case
      by (rule expr)
  next
    case (Lab c l s0 s1 L accC T A)
    from Lab.prems 
    have "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c\<Colon>\<surd>"
      by (elim wt_elim_cases)
    moreover
    from Lab.prems obtain C where
      "\<lparr>prg=G,cls=accC, lcl=L\<rparr>\<turnstile>dom (locals (store ((Norm s0)::state)))\<guillemotright>\<langle>c\<rangle>\<^sub>s\<guillemotright>C"
      by (elim da_elim_cases) simp
    moreover from calculation
    have "P L accC (Norm s0) \<langle>c\<rangle>\<^sub>s \<diamondsuit> s1"
      by (rule  Lab.hyps)  
    ultimately show ?case
      by (rule lab)
  next
    case (Comp c1 c2 s0 s1 s2 L accC T A) 
    have eval_c1: "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
    have eval_c2: "G\<turnstile>s1 \<midarrow>c2\<rightarrow> s2" .
    from Comp.prems obtain 
      wt_c1: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "\<lparr>prg = G, cls = accC, lcl = L\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases) 
    from Comp.prems
    obtain C1 C2
      where da_c1: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile> 
                      dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>c1\<rangle>\<^sub>s\<guillemotright> C1" and 
            da_c2: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>  nrm C1 \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2" 
      by (elim da_elim_cases) simp
    from wt_c1 da_c1
    have P_c1: "P L accC (Norm s0) \<langle>c1\<rangle>\<^sub>s \<diamondsuit> s1"
      by (rule Comp.hyps)
    {
      fix Q
      assume normal_s1: "normal s1"
      assume elim: "\<And> C2'. 
                    \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile>dom (locals (store s1))\<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright>C2';
                       P L accC s1 \<langle>c2\<rangle>\<^sub>s \<diamondsuit> s2\<rbrakk> \<Longrightarrow> Q"
      have Q
      proof -
	obtain C2' where 
	  da: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>c2\<rangle>\<^sub>s\<guillemotright> C2'"
	proof -
	  from eval_c1 wt_c1 da_c1 wf normal_s1
	  have "nrm C1 \<subseteq> dom (locals (store s1))"
	    by (cases rule: da_good_approxE') rules
	  with da_c2 show ?thesis
	    by (rule da_weakenE)
	qed
	with wt_c2 have "P L accC s1 \<langle>c2\<rangle>\<^sub>s \<diamondsuit> s2"
	  by (rule Comp.hyps)
	with da show ?thesis
	  using elim by rules
      qed
    }
    with eval_c1 eval_c2 wt_c1 wt_c2 da_c1 P_c1 
    show ?case
      by (rule comp) rules+
  next
    case (If b c1 c2 e s0 s1 s2 L accC T A)
    have eval_e: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" .
    have eval_then_else: "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2" .
    from If.prems
    obtain 
              wt_e: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>e\<Colon>-PrimT Boolean" and
      wt_then_else: "\<lparr>prg=G, cls=accC, lcl=L\<rparr>\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
      by (elim wt_elim_cases) (auto split add: split_if)
    from If.prems obtain E C where
      da_e: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> dom (locals (store ((Norm s0)::state))) 
                                       \<guillemotright>\<langle>e\<rangle>\<^sub>e\<guillemotright> E" and
      da_then_else: 
      "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
         (dom (locals (store ((Norm s0)::state))) \<union> assigns_if (the_Bool b) e)
          \<guillemotright>\<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s\<guillemotright> C"
      by (elim da_elim_cases) (cases "the_Bool b",auto)
    from wt_e da_e
    have P_e: "P L accC (Norm s0) \<langle>e\<rangle>\<^sub>e \<lfloor>b\<rfloor>\<^sub>e s1"
      by (rule If.hyps)
    {
      fix Q
      assume normal_s1: "normal s1"
      assume elim: "\<And> C. \<lbrakk>\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> (dom (locals (store s1)))
                                   \<guillemotright>\<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s\<guillemotright> C;
                              P L accC s1 \<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s \<diamondsuit> s2
                              \<rbrakk> \<Longrightarrow> Q"
      have Q
      proof -
	obtain C' where
	  da: "\<lparr>prg=G,cls=accC,lcl=L\<rparr>\<turnstile> 
                (dom (locals (store s1)))\<guillemotright>\<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s \<guillemotright> C'"
	proof -
	  from eval_e have 
	    "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
	    by (rule dom_locals_eval_mono_elim)
          moreover
	  from eval_e normal_s1 wt_e 
	  have "assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
	    by (rule assigns_if_good_approx')
	  ultimately 
	  have "dom (locals (store ((Norm s0)::state))) 
            \<union> assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
	    by (rule Un_least)
	  with da_then_else show ?thesis
	    by (rule da_weakenE)
	qed
	with wt_then_else
	have "P L accC s1 \<langle>if the_Bool b then c1 else c2\<rangle>\<^sub>s \<diamondsuit> s2"
	  by (rule If.hyps)
	with da show ?thesis using elim by rules
      qed
    }
    with eval_e eval_then_else wt_e wt_then_else da_e P_e
    show ?case
      by (rule if) rules+
  next
    oops

end
