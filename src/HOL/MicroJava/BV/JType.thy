(*  Title:      HOL/BCV/JType.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The type system of the JVM
*)

header "JVM Type System as Semilattice"

theory JType = WellForm + Err:

constdefs
  is_ref :: "ty => bool"
  "is_ref T == case T of PrimT t => False | RefT r => True"

  sup :: "'c prog => ty => ty => ty err"
  "sup G T1 T2 ==
  case T1 of PrimT P1 => (case T2 of PrimT P2 => (if P1 = P2 then OK (PrimT P1) else Err) | RefT R => Err)
           | RefT R1 => (case T2 of PrimT P => Err | RefT R2 => 
  (case R1 of NullT => (case R2 of NullT => OK NT | ClassT C => OK (Class C))
            | ClassT C => (case R2 of NullT => OK (Class C) 
                                    | ClassT D => OK (Class (some_lub ((subcls1 G)^* ) C D)))))"

  subtype :: "'c prog => ty => ty => bool"
  "subtype G T1 T2 == G \<turnstile> T1 \<preceq> T2"

  is_ty :: "'c prog => ty => bool"
  "is_ty G T == case T of PrimT P => True | RefT R =>
               (case R of NullT => True | ClassT C => (C,Object):(subcls1 G)^*)"

translations
  "types G" == "Collect (is_type G)"

constdefs
  esl :: "'c prog => ty esl"
  "esl G == (types G, subtype G, sup G)"

lemma PrimT_PrimT: "(G \<turnstile> xb \<preceq> PrimT p) = (xb = PrimT p)"
  by (auto elim: widen.elims)

lemma PrimT_PrimT2: "(G \<turnstile> PrimT p \<preceq> xb) = (xb = PrimT p)"
  by (auto elim: widen.elims)

lemma is_tyI:
  "[| is_type G T; wf_prog wf_mb G |] ==> is_ty G T"
  by (auto simp add: is_ty_def dest: subcls_C_Object 
           split: ty.splits ref_ty.splits)

lemma is_type_conv: 
  "wf_prog wf_mb G ==> is_type G T = is_ty G T"
proof
  assume "is_type G T" "wf_prog wf_mb G" 
  thus "is_ty G T"
    by (rule is_tyI)
next
  assume wf: "wf_prog wf_mb G" and
         ty: "is_ty G T"

  show "is_type G T"
  proof (cases T)
    case PrimT
    thus ?thesis by simp
  next
    fix R assume R: "T = RefT R"
    with wf
    have "R = ClassT Object \<Longrightarrow> ?thesis" by simp
    moreover    
    from R wf ty
    have "R \<noteq> ClassT Object \<Longrightarrow> ?thesis"
      by (auto simp add: is_ty_def subcls1_def is_class_def class_def 
               elim: converse_rtranclE
               split: ref_ty.splits)    
    ultimately    
    show ?thesis by blast
  qed
qed


lemma order_widen:
  "acyclic (subcls1 G) ==> order (subtype G)"
  apply (unfold order_def lesub_def subtype_def)
  apply (auto intro: widen_trans)
  apply (case_tac x)
   apply (case_tac y)
    apply (auto simp add: PrimT_PrimT)
   apply (case_tac y)
    apply simp
  apply simp
  apply (case_tac ref_ty)
   apply (case_tac ref_tya)
    apply simp
   apply simp
  apply (case_tac ref_tya)
   apply simp
  apply simp
  apply (auto dest: acyclic_impl_antisym_rtrancl antisymD)  
  done

lemma closed_err_types:
  "[| wf_prog wf_mb G; univalent (subcls1 G); acyclic (subcls1 G) |] 
  ==> closed (err (types G)) (lift2 (sup G))"
  apply (unfold closed_def plussub_def lift2_def sup_def)
  apply (auto split: err.split)
  apply (drule is_tyI, assumption)
  apply (auto simp add: is_ty_def is_type_conv simp del: is_type.simps 
              split: ty.split ref_ty.split)
  apply (blast dest!: is_lub_some_lub is_lubD is_ubD intro!: is_ubI)
  done


lemma err_semilat_JType_esl_lemma:
  "[| wf_prog wf_mb G; univalent (subcls1 G); acyclic (subcls1 G) |] 
  ==> err_semilat (esl G)"
proof -
  assume wf_prog:   "wf_prog wf_mb G"
  assume univalent: "univalent (subcls1 G)" 
  assume acyclic:   "acyclic (subcls1 G)"
  
  hence "order (subtype G)"
    by (rule order_widen)
  moreover
  from wf_prog univalent acyclic
  have "closed (err (types G)) (lift2 (sup G))"
    by (rule closed_err_types)
  moreover
  
  { fix c1 c2
    assume is_class: "is_class G c1" "is_class G c2"
    with wf_prog 
    obtain 
      "G \<turnstile> c1 \<preceq>C Object"
      "G \<turnstile> c2 \<preceq>C Object"
      by (blast intro: subcls_C_Object)
    with wf_prog univalent
    obtain u where
      "is_lub ((subcls1 G)^* ) c1 c2 u"
      by (blast dest: univalent_has_lubs)
    with acyclic
    have "G \<turnstile> c1 \<preceq>C some_lub ((subcls1 G)^* ) c1 c2"
      by (simp add: some_lub_conv) (blast dest: is_lubD is_ubD)
  } note this [intro]
      
  { fix t1 t2 s
    assume "is_type G t1" "is_type G t2" "sup G t1 t2 = OK s"    
    hence "subtype G t1 s"
      by (unfold sup_def subtype_def) 
         (cases s, auto intro: widen.null 
                        split: ty.splits ref_ty.splits if_splits)
  } note this [intro]

  have
    "\<forall>x\<in>err (types G). \<forall>y\<in>err (types G). x <=_(le (subtype G)) x +_(lift2 (sup G)) y"
    by (auto simp add: lesub_def plussub_def le_def lift2_def split: err.split)
  moreover

  { fix c1 c2
    assume "is_class G c1" "is_class G c2"
    with wf_prog
    obtain 
      "G \<turnstile> c1 \<preceq>C Object"
      "G \<turnstile> c2 \<preceq>C Object"
      by (blast intro: subcls_C_Object)
    with wf_prog univalent
    obtain u where
      "is_lub ((subcls1 G)^* ) c2 c1 u"
      by (blast dest: univalent_has_lubs)
    with acyclic
    have "G \<turnstile> c1 \<preceq>C some_lub ((subcls1 G)^* ) c2 c1"
      by (simp add: some_lub_conv) (blast dest: is_lubD is_ubD)
  } note this [intro]
      
  have "\<forall>x\<in>err (types G). \<forall>y\<in>err (types G). 
    y <=_(le (subtype G)) x +_(lift2 (sup G)) y"
    by (auto simp add: lesub_def plussub_def le_def sup_def subtype_def lift2_def 
             split: err.split ty.splits ref_ty.splits if_splits intro: widen.null)
  moreover
    
  have [intro]: 
    "!!a b c. [| G \<turnstile> a \<preceq> c; G \<turnstile> b \<preceq> c; sup G a b = Err |] ==> False"
    by (auto simp add: PrimT_PrimT PrimT_PrimT2 sup_def 
             split: ty.splits ref_ty.splits)

  { fix c1 c2 D
    assume is_class: "is_class G c1" "is_class G c2"
    assume le: "G \<turnstile> c1 \<preceq>C D" "G \<turnstile> c2 \<preceq>C D"
    from wf_prog is_class
    obtain 
      "G \<turnstile> c1 \<preceq>C Object"
      "G \<turnstile> c2 \<preceq>C Object"
      by (blast intro: subcls_C_Object)
    with wf_prog univalent
    obtain u where
      lub: "is_lub ((subcls1 G)^* ) c1 c2 u"
      by (blast dest: univalent_has_lubs)   
    with acyclic
    have "some_lub ((subcls1 G)^* ) c1 c2 = u"
      by (rule some_lub_conv)
    moreover
    from lub le
    have "G \<turnstile> u \<preceq>C D" 
      by (simp add: is_lub_def is_ub_def)
    ultimately     
    have "G \<turnstile> some_lub ((subcls1 G)\<^sup>*) c1 c2 \<preceq>C D"
      by blast
  } note this [intro]

  have [dest!]:
    "!!C T. G \<turnstile> Class C \<preceq> T ==> \<exists>D. T=Class D \<and> G \<turnstile> C \<preceq>C D"
    by (frule widen_Class, auto)

  { fix a b c d
    assume "is_type G a" "is_type G b" "is_type G c" and
           "G \<turnstile> a \<preceq> c" "G \<turnstile> b \<preceq> c" and
           "sup G a b = OK d" 
    hence "G \<turnstile> d \<preceq> c"
      by (auto simp add: sup_def split: ty.splits ref_ty.splits if_splits)
  } note this [intro]

  have
    "\<forall>x\<in>err (types G). \<forall>y\<in>err (types G). \<forall>z\<in>err (types G). 
    x <=_(le (subtype G)) z \<and> y <=_(le (subtype G)) z \<longrightarrow> x +_(lift2 (sup G)) y <=_(le (subtype G)) z"
    by (simp add: lift2_def plussub_def lesub_def subtype_def le_def split: err.splits) blast

  ultimately
  
  show ?thesis
    by (unfold esl_def semilat_def sl_def) auto
qed

lemma univalent_subcls1:
  "wf_prog wf_mb G ==> univalent (subcls1 G)"
  by (unfold wf_prog_def unique_def univalent_def subcls1_def) auto

ML_setup {* bind_thm ("acyclic_subcls1", acyclic_subcls1) *}

theorem "wf_prog wf_mb G ==> err_semilat (esl G)"
  by (frule acyclic_subcls1, frule univalent_subcls1, rule err_semilat_JType_esl_lemma)

end
