(*  Title:      HOL/Bali/Conform.thy
    ID:         $Id$
    Author:     David von Oheimb
*)

header {* Conformance notions for the type soundness proof for Java *}

theory Conform = State:

text {*
design issues:
\begin{itemize}
\item lconf allows for (arbitrary) inaccessible values
\item ''conforms'' does not directly imply that the dynamic types of all 
      objects on the heap are indeed existing classes. Yet this can be 
      inferred for all referenced objs.
\end{itemize}
*}

types	env_ = "prog \<times> (lname, ty) table" (* same as env of WellType.thy *)


section "extension of global store"


constdefs

  gext    :: "st \<Rightarrow> st \<Rightarrow> bool"                ("_\<le>|_"       [71,71]   70)
   "s\<le>|s' \<equiv> \<forall>r. \<forall>obj\<in>globs s r: \<exists>obj'\<in>globs s' r: tag obj'= tag obj"

text {* For the the proof of type soundness we will need the 
property that during execution, objects are not lost and moreover retain the 
values of their tags. So the object store grows conservatively. Note that if 
we considered garbage collection, we would have to restrict this property to 
accessible objects.
*}

lemma gext_objD: 
"\<lbrakk>s\<le>|s'; globs s r = Some obj\<rbrakk> 
\<Longrightarrow> \<exists>obj'. globs s' r = Some obj' \<and> tag obj' = tag obj"
apply (simp only: gext_def)
by force

lemma rev_gext_objD: 
"\<lbrakk>globs s r = Some obj; s\<le>|s'\<rbrakk> 
 \<Longrightarrow> \<exists>obj'. globs s' r = Some obj' \<and> tag obj' = tag obj"
by (auto elim: gext_objD)

lemma init_class_obj_inited: 
   "init_class_obj G C s1\<le>|s2 \<Longrightarrow> inited C (globs s2)"
apply (unfold inited_def init_obj_def)
apply (auto dest!: gext_objD)
done

lemma gext_refl [intro!, simp]: "s\<le>|s"
apply (unfold gext_def)
apply (fast del: fst_splitE)
done

lemma gext_gupd [simp, elim!]: "\<And>s. globs s r = None \<Longrightarrow> s\<le>|gupd(r\<mapsto>x)s"
by (auto simp: gext_def)

lemma gext_new [simp, elim!]: "\<And>s. globs s r = None \<Longrightarrow> s\<le>|init_obj G oi r s"
apply (simp only: init_obj_def)
apply (erule_tac gext_gupd)
done

lemma gext_trans [elim]: "\<And>X. \<lbrakk>s\<le>|s'; s'\<le>|s''\<rbrakk> \<Longrightarrow> s\<le>|s''" 
by (force simp: gext_def)

lemma gext_upd_gobj [intro!]: "s\<le>|upd_gobj r n v s"
apply (simp only: gext_def)
apply auto
apply (case_tac "ra = r")
apply auto
apply (case_tac "globs s r = None")
apply auto
done

lemma gext_cong1 [simp]: "set_locals l s1\<le>|s2 = s1\<le>|s2"
by (auto simp: gext_def)

lemma gext_cong2 [simp]: "s1\<le>|set_locals l s2 = s1\<le>|s2"
by (auto simp: gext_def)


lemma gext_lupd1 [simp]: "lupd(vn\<mapsto>v)s1\<le>|s2 = s1\<le>|s2"
by (auto simp: gext_def)

lemma gext_lupd2 [simp]: "s1\<le>|lupd(vn\<mapsto>v)s2 = s1\<le>|s2"
by (auto simp: gext_def)


lemma inited_gext: "\<lbrakk>inited C (globs s); s\<le>|s'\<rbrakk> \<Longrightarrow> inited C (globs s')"
apply (unfold inited_def)
apply (auto dest: gext_objD)
done


section "value conformance"

constdefs

  conf  :: "prog \<Rightarrow> st \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool"    ("_,_\<turnstile>_\<Colon>\<preceq>_"   [71,71,71,71] 70)
	   "G,s\<turnstile>v\<Colon>\<preceq>T \<equiv> \<exists>T'\<in>typeof (\<lambda>a. option_map obj_ty (heap s a)) v:G\<turnstile>T'\<preceq>T"

lemma conf_cong [simp]: "G,set_locals l s\<turnstile>v\<Colon>\<preceq>T = G,s\<turnstile>v\<Colon>\<preceq>T"
by (auto simp: conf_def)

lemma conf_lupd [simp]: "G,lupd(vn\<mapsto>va)s\<turnstile>v\<Colon>\<preceq>T = G,s\<turnstile>v\<Colon>\<preceq>T"
by (auto simp: conf_def)

lemma conf_PrimT [simp]: "\<forall>dt. typeof dt v = Some (PrimT t) \<Longrightarrow> G,s\<turnstile>v\<Colon>\<preceq>PrimT t"
apply (simp add: conf_def)
done

lemma conf_Boolean: "G,s\<turnstile>v\<Colon>\<preceq>PrimT Boolean \<Longrightarrow> \<exists> b. v=Bool b"
by (cases v)
   (auto simp: conf_def obj_ty_def 
         dest: widen_Boolean2 
        split: obj_tag.splits)


lemma conf_litval [rule_format (no_asm)]: 
  "typeof (\<lambda>a. None) v = Some T \<longrightarrow> G,s\<turnstile>v\<Colon>\<preceq>T"
apply (unfold conf_def)
apply (rule val.induct)
apply auto
done

lemma conf_Null [simp]: "G,s\<turnstile>Null\<Colon>\<preceq>T = G\<turnstile>NT\<preceq>T"
by (simp add: conf_def)

lemma conf_Addr: 
  "G,s\<turnstile>Addr a\<Colon>\<preceq>T = (\<exists>obj. heap s a = Some obj \<and> G\<turnstile>obj_ty obj\<preceq>T)"
by (auto simp: conf_def)

lemma conf_AddrI:"\<lbrakk>heap s a = Some obj; G\<turnstile>obj_ty obj\<preceq>T\<rbrakk> \<Longrightarrow> G,s\<turnstile>Addr a\<Colon>\<preceq>T"
apply (rule conf_Addr [THEN iffD2])
by fast

lemma defval_conf [rule_format (no_asm), elim]: 
  "is_type G T \<longrightarrow> G,s\<turnstile>default_val T\<Colon>\<preceq>T"
apply (unfold conf_def)
apply (induct "T")
apply (auto intro: prim_ty.induct)
done

lemma conf_widen [rule_format (no_asm), elim]: 
  "G\<turnstile>T\<preceq>T' \<Longrightarrow> G,s\<turnstile>x\<Colon>\<preceq>T \<longrightarrow> ws_prog G \<longrightarrow> G,s\<turnstile>x\<Colon>\<preceq>T'"
apply (unfold conf_def)
apply (rule val.induct)
apply (auto elim: ws_widen_trans)
done

lemma conf_gext [rule_format (no_asm), elim]: 
  "G,s\<turnstile>v\<Colon>\<preceq>T \<longrightarrow> s\<le>|s' \<longrightarrow> G,s'\<turnstile>v\<Colon>\<preceq>T"
apply (unfold gext_def conf_def)
apply (rule val.induct)
apply force+
done


lemma conf_list_widen [rule_format (no_asm)]: 
"ws_prog G \<Longrightarrow>  
  \<forall>Ts Ts'. list_all2 (conf G s) vs Ts 
           \<longrightarrow>   G\<turnstile>Ts[\<preceq>] Ts' \<longrightarrow> list_all2 (conf G s) vs Ts'"
apply (unfold widens_def)
apply (rule list_all2_trans)
apply auto
done

lemma conf_RefTD [rule_format (no_asm)]: 
 "G,s\<turnstile>a'\<Colon>\<preceq>RefT T 
  \<longrightarrow> a' = Null \<or> (\<exists>a obj T'. a' = Addr a \<and> heap s a = Some obj \<and>  
                    obj_ty obj = T' \<and> G\<turnstile>T'\<preceq>RefT T)"
apply (unfold conf_def)
apply (induct_tac "a'")
apply (auto dest: widen_PrimT)
done


section "value list conformance"

constdefs

  lconf :: "prog \<Rightarrow> st \<Rightarrow> ('a, val) table \<Rightarrow> ('a, ty) table \<Rightarrow> bool"
                                                ("_,_\<turnstile>_[\<Colon>\<preceq>]_" [71,71,71,71] 70)
           "G,s\<turnstile>vs[\<Colon>\<preceq>]Ts \<equiv> \<forall>n. \<forall>T\<in>Ts n: \<exists>v\<in>vs n: G,s\<turnstile>v\<Colon>\<preceq>T"

lemma lconfD: "\<lbrakk>G,s\<turnstile>vs[\<Colon>\<preceq>]Ts; Ts n = Some T\<rbrakk> \<Longrightarrow> G,s\<turnstile>(the (vs n))\<Colon>\<preceq>T"
by (force simp: lconf_def)


lemma lconf_cong [simp]: "\<And>s. G,set_locals x s\<turnstile>l[\<Colon>\<preceq>]L = G,s\<turnstile>l[\<Colon>\<preceq>]L"
by (auto simp: lconf_def)

lemma lconf_lupd [simp]: "G,lupd(vn\<mapsto>v)s\<turnstile>l[\<Colon>\<preceq>]L = G,s\<turnstile>l[\<Colon>\<preceq>]L"
by (auto simp: lconf_def)

(* unused *)
lemma lconf_new: "\<lbrakk>L vn = None; G,s\<turnstile>l[\<Colon>\<preceq>]L\<rbrakk> \<Longrightarrow> G,s\<turnstile>l(vn\<mapsto>v)[\<Colon>\<preceq>]L"
by (auto simp: lconf_def)

lemma lconf_upd: "\<lbrakk>G,s\<turnstile>l[\<Colon>\<preceq>]L; G,s\<turnstile>v\<Colon>\<preceq>T; L vn = Some T\<rbrakk> \<Longrightarrow>  
  G,s\<turnstile>l(vn\<mapsto>v)[\<Colon>\<preceq>]L"
by (auto simp: lconf_def)

lemma lconf_ext: "\<lbrakk>G,s\<turnstile>l[\<Colon>\<preceq>]L; G,s\<turnstile>v\<Colon>\<preceq>T\<rbrakk> \<Longrightarrow> G,s\<turnstile>l(vn\<mapsto>v)[\<Colon>\<preceq>]L(vn\<mapsto>T)"
by (auto simp: lconf_def)

lemma lconf_map_sum [simp]: 
 "G,s\<turnstile>l1 (+) l2[\<Colon>\<preceq>]L1 (+) L2 = (G,s\<turnstile>l1[\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>l2[\<Colon>\<preceq>]L2)"
apply (unfold lconf_def)
apply safe
apply (case_tac [3] "n")
apply (force split add: sum.split)+
done

lemma lconf_ext_list [rule_format (no_asm)]: "
 \<And>X. \<lbrakk>G,s\<turnstile>l[\<Colon>\<preceq>]L\<rbrakk> \<Longrightarrow> 
      \<forall>vs Ts. distinct vns \<longrightarrow> length Ts = length vns 
      \<longrightarrow> list_all2 (conf G s) vs Ts \<longrightarrow> G,s\<turnstile>l(vns[\<mapsto>]vs)[\<Colon>\<preceq>]L(vns[\<mapsto>]Ts)"
apply (unfold lconf_def)
apply (induct_tac "vns")
apply  clarsimp
apply clarify
apply (frule list_all2_lengthD)
apply (clarsimp)
done


lemma lconf_deallocL: "\<lbrakk>G,s\<turnstile>l[\<Colon>\<preceq>]L(vn\<mapsto>T); L vn = None\<rbrakk> \<Longrightarrow> G,s\<turnstile>l[\<Colon>\<preceq>]L"
apply (simp only: lconf_def)
apply safe
apply (drule spec)
apply (drule ospec)
apply auto
done 


lemma lconf_gext [elim]: "\<lbrakk>G,s\<turnstile>l[\<Colon>\<preceq>]L; s\<le>|s'\<rbrakk> \<Longrightarrow> G,s'\<turnstile>l[\<Colon>\<preceq>]L"
apply (simp only: lconf_def)
apply fast
done

lemma lconf_empty [simp, intro!]: "G,s\<turnstile>vs[\<Colon>\<preceq>]empty"
apply (unfold lconf_def)
apply force
done

lemma lconf_init_vals [intro!]: 
	" \<forall>n. \<forall>T\<in>fs n:is_type G T \<Longrightarrow> G,s\<turnstile>init_vals fs[\<Colon>\<preceq>]fs"
apply (unfold lconf_def)
apply force
done

section "weak value list conformance"

text {* Only if the value is defined it has to conform to its type. 
        This is the contribution of the definite assignment analysis to 
        the notion of conformance. The definite assignment analysis ensures
        that the program only attempts to access local variables that 
        actually have a defined value in the state. 
        So conformance must only ensure that the
        defined values are of the right type, and not also that the value
        is defined. 
*}

  
constdefs

  wlconf :: "prog \<Rightarrow> st \<Rightarrow> ('a, val) table \<Rightarrow> ('a, ty) table \<Rightarrow> bool"
                                          ("_,_\<turnstile>_[\<sim>\<Colon>\<preceq>]_" [71,71,71,71] 70)
           "G,s\<turnstile>vs[\<sim>\<Colon>\<preceq>]Ts \<equiv> \<forall>n. \<forall>T\<in>Ts n: \<forall> v\<in>vs n: G,s\<turnstile>v\<Colon>\<preceq>T"

lemma wlconfD: "\<lbrakk>G,s\<turnstile>vs[\<sim>\<Colon>\<preceq>]Ts; Ts n = Some T; vs n = Some v\<rbrakk> \<Longrightarrow> G,s\<turnstile>v\<Colon>\<preceq>T"
by (auto simp: wlconf_def)


lemma wlconf_cong [simp]: "\<And>s. G,set_locals x s\<turnstile>l[\<sim>\<Colon>\<preceq>]L = G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L"
by (auto simp: wlconf_def)

lemma wlconf_lupd [simp]: "G,lupd(vn\<mapsto>v)s\<turnstile>l[\<sim>\<Colon>\<preceq>]L = G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L"
by (auto simp: wlconf_def)


lemma wlconf_upd: "\<lbrakk>G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L; G,s\<turnstile>v\<Colon>\<preceq>T; L vn = Some T\<rbrakk> \<Longrightarrow>  
  G,s\<turnstile>l(vn\<mapsto>v)[\<sim>\<Colon>\<preceq>]L"
by (auto simp: wlconf_def)

lemma wlconf_ext: "\<lbrakk>G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L; G,s\<turnstile>v\<Colon>\<preceq>T\<rbrakk> \<Longrightarrow> G,s\<turnstile>l(vn\<mapsto>v)[\<sim>\<Colon>\<preceq>]L(vn\<mapsto>T)"
by (auto simp: wlconf_def)

lemma wlconf_map_sum [simp]: 
 "G,s\<turnstile>l1 (+) l2[\<sim>\<Colon>\<preceq>]L1 (+) L2 = (G,s\<turnstile>l1[\<sim>\<Colon>\<preceq>]L1 \<and> G,s\<turnstile>l2[\<sim>\<Colon>\<preceq>]L2)"
apply (unfold wlconf_def)
apply safe
apply (case_tac [3] "n")
apply (force split add: sum.split)+
done

lemma wlconf_ext_list [rule_format (no_asm)]: "
 \<And>X. \<lbrakk>G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L\<rbrakk> \<Longrightarrow> 
      \<forall>vs Ts. distinct vns \<longrightarrow> length Ts = length vns 
      \<longrightarrow> list_all2 (conf G s) vs Ts \<longrightarrow> G,s\<turnstile>l(vns[\<mapsto>]vs)[\<sim>\<Colon>\<preceq>]L(vns[\<mapsto>]Ts)"
apply (unfold wlconf_def)
apply (induct_tac "vns")
apply  clarsimp
apply clarify
apply (frule list_all2_lengthD)
apply clarsimp
done


lemma wlconf_deallocL: "\<lbrakk>G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L(vn\<mapsto>T); L vn = None\<rbrakk> \<Longrightarrow> G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L"
apply (simp only: wlconf_def)
apply safe
apply (drule spec)
apply (drule ospec)
defer
apply (drule ospec )
apply auto
done 


lemma wlconf_gext [elim]: "\<lbrakk>G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L; s\<le>|s'\<rbrakk> \<Longrightarrow> G,s'\<turnstile>l[\<sim>\<Colon>\<preceq>]L"
apply (simp only: wlconf_def)
apply fast
done

lemma wlconf_empty [simp, intro!]: "G,s\<turnstile>vs[\<sim>\<Colon>\<preceq>]empty"
apply (unfold wlconf_def)
apply force
done

lemma wlconf_empty_vals: "G,s\<turnstile>empty[\<sim>\<Colon>\<preceq>]ts"
  by (simp add: wlconf_def)

lemma wlconf_init_vals [intro!]: 
	" \<forall>n. \<forall>T\<in>fs n:is_type G T \<Longrightarrow> G,s\<turnstile>init_vals fs[\<sim>\<Colon>\<preceq>]fs"
apply (unfold wlconf_def)
apply force
done

lemma lconf_wlconf:
 "G,s\<turnstile>l[\<Colon>\<preceq>]L \<Longrightarrow> G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L"
by (force simp add: lconf_def wlconf_def)

section "object conformance"

constdefs

  oconf :: "prog \<Rightarrow> st \<Rightarrow> obj \<Rightarrow> oref \<Rightarrow> bool"  ("_,_\<turnstile>_\<Colon>\<preceq>\<surd>_"  [71,71,71,71] 70)
	   "G,s\<turnstile>obj\<Colon>\<preceq>\<surd>r \<equiv> G,s\<turnstile>values obj[\<Colon>\<preceq>]var_tys G (tag obj) r \<and> 
                           (case r of 
		              Heap a \<Rightarrow> is_type G (obj_ty obj) 
                            | Stat C \<Rightarrow> True)"


lemma oconf_is_type: "G,s\<turnstile>obj\<Colon>\<preceq>\<surd>Heap a \<Longrightarrow> is_type G (obj_ty obj)"
by (auto simp: oconf_def Let_def)

lemma oconf_lconf: "G,s\<turnstile>obj\<Colon>\<preceq>\<surd>r \<Longrightarrow> G,s\<turnstile>values obj[\<Colon>\<preceq>]var_tys G (tag obj) r"
by (simp add: oconf_def) 

lemma oconf_cong [simp]: "G,set_locals l s\<turnstile>obj\<Colon>\<preceq>\<surd>r = G,s\<turnstile>obj\<Colon>\<preceq>\<surd>r"
by (auto simp: oconf_def Let_def)

lemma oconf_init_obj_lemma: 
"\<lbrakk>\<And>C c. class G C = Some c \<Longrightarrow> unique (DeclConcepts.fields G C);  
  \<And>C c f fld. \<lbrakk>class G C = Some c; 
                table_of (DeclConcepts.fields G C) f = Some fld \<rbrakk> 
            \<Longrightarrow> is_type G (type fld);  
  (case r of 
     Heap a \<Rightarrow> is_type G (obj_ty obj) 
  | Stat C \<Rightarrow> is_class G C)
\<rbrakk> \<Longrightarrow>  G,s\<turnstile>obj \<lparr>values:=init_vals (var_tys G (tag obj) r)\<rparr>\<Colon>\<preceq>\<surd>r"
apply (auto simp add: oconf_def)
apply (drule_tac var_tys_Some_eq [THEN iffD1]) 
defer
apply (subst obj_ty_cong)
apply(auto dest!: fields_table_SomeD obj_ty_CInst1 obj_ty_Arr1
           split add: sum.split_asm obj_tag.split_asm)
done

section "state conformance"

constdefs

  conforms :: "state \<Rightarrow> env_ \<Rightarrow> bool"          (     "_\<Colon>\<preceq>_"   [71,71]      70)
   "xs\<Colon>\<preceq>E \<equiv> let (G, L) = E; s = snd xs; l = locals s in
    (\<forall>r. \<forall>obj\<in>globs s r:           G,s\<turnstile>obj   \<Colon>\<preceq>\<surd>r) \<and>
                \<spacespace>                   G,s\<turnstile>l    [\<sim>\<Colon>\<preceq>]L\<spacespace> \<and>
    (\<forall>a. fst xs=Some(Xcpt (Loc a)) \<longrightarrow> G,s\<turnstile>Addr a\<Colon>\<preceq> Class (SXcpt Throwable)) \<and>
         (fst xs=Some(Jump Ret) \<longrightarrow> l Result \<noteq> None)"

section "conforms"

lemma conforms_globsD: 
"\<lbrakk>(x, s)\<Colon>\<preceq>(G, L); globs s r = Some obj\<rbrakk> \<Longrightarrow> G,s\<turnstile>obj\<Colon>\<preceq>\<surd>r"
by (auto simp: conforms_def Let_def)

lemma conforms_localD: "(x, s)\<Colon>\<preceq>(G, L) \<Longrightarrow> G,s\<turnstile>locals s[\<sim>\<Colon>\<preceq>]L"
by (auto simp: conforms_def Let_def)

lemma conforms_XcptLocD: "\<lbrakk>(x, s)\<Colon>\<preceq>(G, L); x = Some (Xcpt (Loc a))\<rbrakk> \<Longrightarrow>  
	  G,s\<turnstile>Addr a\<Colon>\<preceq> Class (SXcpt Throwable)"
by (auto simp: conforms_def Let_def)

lemma conforms_RetD: "\<lbrakk>(x, s)\<Colon>\<preceq>(G, L); x = Some (Jump Ret)\<rbrakk> \<Longrightarrow>  
	  (locals s) Result \<noteq> None"
by (auto simp: conforms_def Let_def)

lemma conforms_RefTD: 
 "\<lbrakk>G,s\<turnstile>a'\<Colon>\<preceq>RefT t; a' \<noteq> Null; (x,s) \<Colon>\<preceq>(G, L)\<rbrakk> \<Longrightarrow>  
   \<exists>a obj. a' = Addr a \<and> globs s (Inl a) = Some obj \<and>  
   G\<turnstile>obj_ty obj\<preceq>RefT t \<and> is_type G (obj_ty obj)"
apply (drule_tac conf_RefTD)
apply clarsimp
apply (rule conforms_globsD [THEN oconf_is_type])
apply auto
done

lemma conforms_Jump [iff]:
  "j=Ret \<longrightarrow> locals s Result \<noteq> None 
   \<Longrightarrow> ((Some (Jump j), s)\<Colon>\<preceq>(G, L)) = (Norm s\<Colon>\<preceq>(G, L))"
by (auto simp: conforms_def Let_def)

lemma conforms_StdXcpt [iff]: 
  "((Some (Xcpt (Std xn)), s)\<Colon>\<preceq>(G, L)) = (Norm s\<Colon>\<preceq>(G, L))"
by (auto simp: conforms_def)

lemma conforms_Err [iff]:
   "((Some (Error e), s)\<Colon>\<preceq>(G, L)) = (Norm s\<Colon>\<preceq>(G, L))"
  by (auto simp: conforms_def)  

lemma conforms_raise_if [iff]: 
  "((raise_if c xn x, s)\<Colon>\<preceq>(G, L)) = ((x, s)\<Colon>\<preceq>(G, L))"
by (auto simp: abrupt_if_def)

lemma conforms_error_if [iff]: 
  "((error_if c err x, s)\<Colon>\<preceq>(G, L)) = ((x, s)\<Colon>\<preceq>(G, L))"
by (auto simp: abrupt_if_def split: split_if)

lemma conforms_NormI: "(x, s)\<Colon>\<preceq>(G, L) \<Longrightarrow> Norm s\<Colon>\<preceq>(G, L)"
by (auto simp: conforms_def Let_def)

lemma conforms_absorb [rule_format]:
  "(a, b)\<Colon>\<preceq>(G, L) \<longrightarrow> (absorb j a, b)\<Colon>\<preceq>(G, L)"
apply (rule impI)
apply ( case_tac a)
apply (case_tac "absorb j a")
apply auto
apply (case_tac "absorb j (Some a)",auto)
apply (erule conforms_NormI)
done

lemma conformsI: "\<lbrakk>\<forall>r. \<forall>obj\<in>globs s r: G,s\<turnstile>obj\<Colon>\<preceq>\<surd>r;  
     G,s\<turnstile>locals s[\<sim>\<Colon>\<preceq>]L;  
     \<forall>a. x = Some (Xcpt (Loc a)) \<longrightarrow> G,s\<turnstile>Addr a\<Colon>\<preceq> Class (SXcpt Throwable);
     x = Some (Jump Ret)\<longrightarrow> locals s Result \<noteq> None\<rbrakk> \<Longrightarrow> 
  (x, s)\<Colon>\<preceq>(G, L)"
by (auto simp: conforms_def Let_def)

lemma conforms_xconf: "\<lbrakk>(x, s)\<Colon>\<preceq>(G,L);   
 \<forall>a. x' = Some (Xcpt (Loc a)) \<longrightarrow> G,s\<turnstile>Addr a\<Colon>\<preceq> Class (SXcpt Throwable);
     x' = Some (Jump Ret) \<longrightarrow> locals s Result \<noteq> None\<rbrakk> \<Longrightarrow> 
 (x',s)\<Colon>\<preceq>(G,L)"
by (fast intro: conformsI elim: conforms_globsD conforms_localD)

lemma conforms_lupd: 
 "\<lbrakk>(x, s)\<Colon>\<preceq>(G, L); L vn = Some T; G,s\<turnstile>v\<Colon>\<preceq>T\<rbrakk> \<Longrightarrow> (x, lupd(vn\<mapsto>v)s)\<Colon>\<preceq>(G, L)"
by (force intro: conformsI wlconf_upd dest: conforms_globsD conforms_localD 
                                           conforms_XcptLocD conforms_RetD 
          simp: oconf_def)


lemmas conforms_allocL_aux = conforms_localD [THEN wlconf_ext]

lemma conforms_allocL: 
  "\<lbrakk>(x, s)\<Colon>\<preceq>(G, L); G,s\<turnstile>v\<Colon>\<preceq>T\<rbrakk> \<Longrightarrow> (x, lupd(vn\<mapsto>v)s)\<Colon>\<preceq>(G, L(vn\<mapsto>T))"
by (force intro: conformsI dest: conforms_globsD conforms_RetD 
          elim: conforms_XcptLocD  conforms_allocL_aux 
          simp: oconf_def)

lemmas conforms_deallocL_aux = conforms_localD [THEN wlconf_deallocL]

lemma conforms_deallocL: "\<And>s.\<lbrakk>s\<Colon>\<preceq>(G, L(vn\<mapsto>T)); L vn = None\<rbrakk> \<Longrightarrow> s\<Colon>\<preceq>(G,L)"
by (fast intro: conformsI dest: conforms_globsD conforms_RetD
         elim: conforms_XcptLocD conforms_deallocL_aux)

lemma conforms_gext: "\<lbrakk>(x, s)\<Colon>\<preceq>(G,L); s\<le>|s';  
  \<forall>r. \<forall>obj\<in>globs s' r: G,s'\<turnstile>obj\<Colon>\<preceq>\<surd>r;  
   locals s'=locals s\<rbrakk> \<Longrightarrow> (x,s')\<Colon>\<preceq>(G,L)"
apply (rule conformsI)
apply     assumption
apply    (drule conforms_localD) apply force
apply   (intro strip)
apply  (drule (1) conforms_XcptLocD) apply force 
apply (intro strip)
apply (drule (1) conforms_RetD) apply force
done



lemma conforms_xgext: 
  "\<lbrakk>(x ,s)\<Colon>\<preceq>(G,L); (x', s')\<Colon>\<preceq>(G, L); s'\<le>|s;dom (locals s') \<subseteq> dom (locals s)\<rbrakk> 
   \<Longrightarrow> (x',s)\<Colon>\<preceq>(G,L)"
apply (erule_tac conforms_xconf)
apply  (fast dest: conforms_XcptLocD)
apply (intro strip)
apply (drule (1) conforms_RetD) 
apply (auto dest: domI)
done

lemma conforms_gupd: "\<And>obj. \<lbrakk>(x, s)\<Colon>\<preceq>(G, L); G,s\<turnstile>obj\<Colon>\<preceq>\<surd>r; s\<le>|gupd(r\<mapsto>obj)s\<rbrakk> 
\<Longrightarrow>  (x, gupd(r\<mapsto>obj)s)\<Colon>\<preceq>(G, L)"
apply (rule conforms_gext)
apply    auto
apply (force dest: conforms_globsD simp add: oconf_def)+
done

lemma conforms_upd_gobj: "\<lbrakk>(x,s)\<Colon>\<preceq>(G, L); globs s r = Some obj; 
  var_tys G (tag obj) r n = Some T; G,s\<turnstile>v\<Colon>\<preceq>T\<rbrakk> \<Longrightarrow> (x,upd_gobj r n v s)\<Colon>\<preceq>(G,L)"
apply (rule conforms_gext)
apply auto
apply (drule (1) conforms_globsD)
apply (simp add: oconf_def)
apply safe
apply (rule lconf_upd)
apply auto
apply (simp only: obj_ty_cong) 
apply (force dest: conforms_globsD intro!: lconf_upd 
       simp add: oconf_def cong del: sum.weak_case_cong)
done

lemma conforms_set_locals: 
  "\<lbrakk>(x,s)\<Colon>\<preceq>(G, L'); G,s\<turnstile>l[\<sim>\<Colon>\<preceq>]L; x=Some (Jump Ret) \<longrightarrow> l Result \<noteq> None\<rbrakk> 
   \<Longrightarrow> (x,set_locals l s)\<Colon>\<preceq>(G,L)"
apply (rule conformsI)
apply     (intro strip)
apply     simp
apply     (drule (2) conforms_globsD)
apply    simp
apply   (intro strip)
apply   (drule (1) conforms_XcptLocD)
apply   simp
apply (intro strip)
apply (drule (1) conforms_RetD)
apply simp
done

lemma conforms_locals: 
  "\<lbrakk>(a,b)\<Colon>\<preceq>(G, L); L x = Some T;locals b x \<noteq>None\<rbrakk>
   \<Longrightarrow> G,b\<turnstile>the (locals b x)\<Colon>\<preceq>T"
apply (force simp: conforms_def Let_def wlconf_def)
done

lemma conforms_return: 
"\<And>s'. \<lbrakk>(x,s)\<Colon>\<preceq>(G, L); (x',s')\<Colon>\<preceq>(G, L'); s\<le>|s';x'\<noteq>Some (Jump Ret)\<rbrakk> \<Longrightarrow>  
  (x',set_locals (locals s) s')\<Colon>\<preceq>(G, L)"
apply (rule conforms_xconf)
prefer 2 apply (force dest: conforms_XcptLocD)
apply (erule conforms_gext)
apply (force dest: conforms_globsD)+
done


end
