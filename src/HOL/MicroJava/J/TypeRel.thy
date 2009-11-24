(*  Title:      HOL/MicroJava/J/TypeRel.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Relations between Java Types} *}

theory TypeRel imports Decl begin

-- "direct subclass, cf. 8.1.3"

inductive_set
  subcls1 :: "'c prog => (cname \<times> cname) set"
  and subcls1' :: "'c prog => cname \<Rightarrow> cname => bool" ("_ \<turnstile> _ \<prec>C1 _" [71,71,71] 70)
  for G :: "'c prog"
where
  "G \<turnstile> C \<prec>C1 D \<equiv> (C, D) \<in> subcls1 G"
  | subcls1I: "\<lbrakk>class G C = Some (D,rest); C \<noteq> Object\<rbrakk> \<Longrightarrow> G \<turnstile> C \<prec>C1 D"

abbreviation
  subcls  :: "'c prog => cname \<Rightarrow> cname => bool" ("_ \<turnstile> _ \<preceq>C _"  [71,71,71] 70)
  where "G \<turnstile> C \<preceq>C D \<equiv> (C, D) \<in> (subcls1 G)^*"

lemma subcls1D: 
  "G\<turnstile>C\<prec>C1D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class G C = Some (D,fs,ms))"
apply (erule subcls1.cases)
apply auto
done

lemma subcls1_def2:
  "subcls1 P =
     (SIGMA C:{C. is_class P C}. {D. C\<noteq>Object \<and> fst (the (class P C))=D})"
  by (auto simp add: is_class_def dest: subcls1D intro: subcls1I)

lemma finite_subcls1: "finite (subcls1 G)"
apply(simp add: subcls1_def2 del: mem_Sigma_iff)
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{fst (the (class G C))}" in finite_subset)
apply  auto
done

lemma subcls_is_class: "(C, D) \<in> (subcls1 G)^+  ==> is_class G C"
apply (unfold is_class_def)
apply(erule trancl_trans_induct)
apply (auto dest!: subcls1D)
done

lemma subcls_is_class2 [rule_format (no_asm)]: 
  "G\<turnstile>C\<preceq>C D \<Longrightarrow> is_class G D \<longrightarrow> is_class G C"
apply (unfold is_class_def)
apply (erule rtrancl_induct)
apply  (drule_tac [2] subcls1D)
apply  auto
done

constdefs
  class_rec :: "'c prog \<Rightarrow> cname \<Rightarrow> 'a \<Rightarrow>
    (cname \<Rightarrow> fdecl list \<Rightarrow> 'c mdecl list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a"
  "class_rec G == wfrec ((subcls1 G)^-1)
    (\<lambda>r C t f. case class G C of
         None \<Rightarrow> undefined
       | Some (D,fs,ms) \<Rightarrow> 
           f C fs ms (if C = Object then t else r D t f))"

lemma class_rec_lemma:
  assumes wf: "wf ((subcls1 G)^-1)"
    and cls: "class G C = Some (D, fs, ms)"
  shows "class_rec G C t f = f C fs ms (if C=Object then t else class_rec G D t f)"
proof -
  from wf have step: "\<And>H a. wfrec ((subcls1 G)\<inverse>) H a =
    H (cut (wfrec ((subcls1 G)\<inverse>) H) ((subcls1 G)\<inverse>) a) a"
    by (rule wfrec)
  have cut: "\<And>f. C \<noteq> Object \<Longrightarrow> cut f ((subcls1 G)\<inverse>) C D = f D"
    by (rule cut_apply [where r="(subcls1 G)^-1", simplified, OF subcls1I, OF cls])
  from cls show ?thesis by (simp add: step cut class_rec_def)
qed

definition
  "wf_class G = wf ((subcls1 G)^-1)"


text {* Code generator setup (FIXME!) *}

consts_code
  "wfrec"   ("\<module>wfrec?")
attach {*
fun wfrec f x = f (wfrec f) x;
*}

consts

  method :: "'c prog \<times> cname => ( sig   \<rightharpoonup> cname \<times> ty \<times> 'c)" (* ###curry *)
  field  :: "'c prog \<times> cname => ( vname \<rightharpoonup> cname \<times> ty     )" (* ###curry *)
  fields :: "'c prog \<times> cname => ((vname \<times> cname) \<times> ty) list" (* ###curry *)

-- "methods of a class, with inheritance, overriding and hiding, cf. 8.4.6"
defs method_def: "method \<equiv> \<lambda>(G,C). class_rec G C empty (\<lambda>C fs ms ts.
                           ts ++ map_of (map (\<lambda>(s,m). (s,(C,m))) ms))"

lemma method_rec_lemma: "[|class G C = Some (D,fs,ms); wf ((subcls1 G)^-1)|] ==>
  method (G,C) = (if C = Object then empty else method (G,D)) ++  
  map_of (map (\<lambda>(s,m). (s,(C,m))) ms)"
apply (unfold method_def)
apply (simp split del: split_if)
apply (erule (1) class_rec_lemma [THEN trans]);
apply auto
done


-- "list of fields of a class, including inherited and hidden ones"
defs fields_def: "fields \<equiv> \<lambda>(G,C). class_rec G C []    (\<lambda>C fs ms ts.
                           map (\<lambda>(fn,ft). ((fn,C),ft)) fs @ ts)"

lemma fields_rec_lemma: "[|class G C = Some (D,fs,ms); wf ((subcls1 G)^-1)|] ==>
 fields (G,C) = 
  map (\<lambda>(fn,ft). ((fn,C),ft)) fs @ (if C = Object then [] else fields (G,D))"
apply (unfold fields_def)
apply (simp split del: split_if)
apply (erule (1) class_rec_lemma [THEN trans]);
apply auto
done


defs field_def: "field == map_of o (map (\<lambda>((fn,fd),ft). (fn,(fd,ft)))) o fields"

lemma field_fields: 
"field (G,C) fn = Some (fd, fT) \<Longrightarrow> map_of (fields (G,C)) (fn, fd) = Some fT"
apply (unfold field_def)
apply (rule table_of_remap_SomeD)
apply simp
done


-- "widening, viz. method invocation conversion,cf. 5.3 i.e. sort of syntactic subtyping"
inductive
  widen   :: "'c prog => [ty   , ty   ] => bool" ("_ \<turnstile> _ \<preceq> _"   [71,71,71] 70)
  for G :: "'c prog"
where
  refl   [intro!, simp]:       "G\<turnstile>      T \<preceq> T"   -- "identity conv., cf. 5.1.1"
| subcls         : "G\<turnstile>C\<preceq>C D ==> G\<turnstile>Class C \<preceq> Class D"
| null   [intro!]:             "G\<turnstile>     NT \<preceq> RefT R"

lemmas refl = HOL.refl

-- "casting conversion, cf. 5.5 / 5.1.5"
-- "left out casts on primitve types"
inductive
  cast    :: "'c prog => [ty   , ty   ] => bool" ("_ \<turnstile> _ \<preceq>? _"  [71,71,71] 70)
  for G :: "'c prog"
where
  widen:  "G\<turnstile> C\<preceq> D ==> G\<turnstile>C \<preceq>? D"
| subcls: "G\<turnstile> D\<preceq>C C ==> G\<turnstile>Class C \<preceq>? Class D"

lemma widen_PrimT_RefT [iff]: "(G\<turnstile>PrimT pT\<preceq>RefT rT) = False"
apply (rule iffI)
apply (erule widen.cases)
apply auto
done

lemma widen_RefT: "G\<turnstile>RefT R\<preceq>T ==> \<exists>t. T=RefT t"
apply (ind_cases "G\<turnstile>RefT R\<preceq>T")
apply auto
done

lemma widen_RefT2: "G\<turnstile>S\<preceq>RefT R ==> \<exists>t. S=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>RefT R")
apply auto
done

lemma widen_Class: "G\<turnstile>Class C\<preceq>T ==> \<exists>D. T=Class D"
apply (ind_cases "G\<turnstile>Class C\<preceq>T")
apply auto
done

lemma widen_Class_NullT [iff]: "(G\<turnstile>Class C\<preceq>NT) = False"
apply (rule iffI)
apply (ind_cases "G\<turnstile>Class C\<preceq>NT")
apply auto
done

lemma widen_Class_Class [iff]: "(G\<turnstile>Class C\<preceq> Class D) = (G\<turnstile>C\<preceq>C D)"
apply (rule iffI)
apply (ind_cases "G\<turnstile>Class C \<preceq> Class D")
apply (auto elim: widen.subcls)
done

lemma widen_NT_Class [simp]: "G \<turnstile> T \<preceq> NT \<Longrightarrow> G \<turnstile> T \<preceq> Class D"
by (ind_cases "G \<turnstile> T \<preceq> NT",  auto)

lemma cast_PrimT_RefT [iff]: "(G\<turnstile>PrimT pT\<preceq>? RefT rT) = False"
apply (rule iffI)
apply (erule cast.cases)
apply auto
done

lemma cast_RefT: "G \<turnstile> C \<preceq>? Class D \<Longrightarrow> \<exists> rT. C = RefT rT"
apply (erule cast.cases)
apply simp apply (erule widen.cases) 
apply auto
done

theorem widen_trans[trans]: "\<lbrakk>G\<turnstile>S\<preceq>U; G\<turnstile>U\<preceq>T\<rbrakk> \<Longrightarrow> G\<turnstile>S\<preceq>T"
proof -
  assume "G\<turnstile>S\<preceq>U" thus "\<And>T. G\<turnstile>U\<preceq>T \<Longrightarrow> G\<turnstile>S\<preceq>T"
  proof induct
    case (refl T T') thus "G\<turnstile>T\<preceq>T'" .
  next
    case (subcls C D T)
    then obtain E where "T = Class E" by (blast dest: widen_Class)
    with subcls show "G\<turnstile>Class C\<preceq>T" by auto
  next
    case (null R RT)
    then obtain rt where "RT = RefT rt" by (blast dest: widen_RefT)
    thus "G\<turnstile>NT\<preceq>RT" by auto
  qed
qed

end
