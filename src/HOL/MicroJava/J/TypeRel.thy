(*  Title:      HOL/MicroJava/J/TypeRel.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header "Relations between Java Types"

theory TypeRel = Decl:

consts
  subcls1 :: "'c prog => (cname \<times> cname) set"  (* subclass *)
  widen   :: "'c prog => (ty    \<times> ty   ) set"  (* widening *)
  cast    :: "'c prog => (cname \<times> cname) set"  (* casting *)

syntax (xsymbols)
  subcls1 :: "'c prog => [cname, cname] => bool" ("_ \<turnstile> _ \<prec>C1 _" [71,71,71] 70)
  subcls  :: "'c prog => [cname, cname] => bool" ("_ \<turnstile> _ \<preceq>C _"  [71,71,71] 70)
  widen   :: "'c prog => [ty   , ty   ] => bool" ("_ \<turnstile> _ \<preceq> _"   [71,71,71] 70)
  cast    :: "'c prog => [cname, cname] => bool" ("_ \<turnstile> _ \<preceq>? _"  [71,71,71] 70)

syntax
  subcls1 :: "'c prog => [cname, cname] => bool" ("_ |- _ <=C1 _" [71,71,71] 70)
  subcls  :: "'c prog => [cname, cname] => bool" ("_ |- _ <=C _"  [71,71,71] 70)
  widen   :: "'c prog => [ty   , ty   ] => bool" ("_ |- _ <= _"   [71,71,71] 70)
  cast    :: "'c prog => [cname, cname] => bool" ("_ |- _ <=? _"  [71,71,71] 70)

translations
  "G\<turnstile>C \<prec>C1 D" == "(C,D) \<in> subcls1 G"
  "G\<turnstile>C \<preceq>C  D" == "(C,D) \<in> (subcls1 G)^*"
  "G\<turnstile>S \<preceq>   T" == "(S,T) \<in> widen   G"
  "G\<turnstile>C \<preceq>?  D" == "(C,D) \<in> cast    G"

defs

  (* direct subclass, cf. 8.1.3 *)
 subcls1_def: "subcls1 G \<equiv> {(C,D). C\<noteq>Object \<and> (\<exists>c. class G C=Some c \<and> fst c=D)}"
  
lemma subcls1D: 
  "G\<turnstile>C\<prec>C1D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class G C = Some (D,fs,ms))"
apply (unfold subcls1_def)
apply auto
done

lemma subcls1I: "\<lbrakk>class G C = Some (D,rest); C \<noteq> Object\<rbrakk> \<Longrightarrow> G\<turnstile>C\<prec>C1D"
apply (unfold subcls1_def)
apply auto
done

lemma subcls1_def2: 
"subcls1 G = (\<Sigma>C\<in>{C. is_class G C} . {D. C\<noteq>Object \<and> fst (the (class G C))=D})"
apply (unfold subcls1_def is_class_def)
apply auto
done

lemma finite_subcls1: "finite (subcls1 G)"
apply(subst subcls1_def2)
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{fst (the (class G C))}" in finite_subset)
apply  auto
done

lemma subcls_is_class: "(C,D) \<in> (subcls1 G)^+ ==> is_class G C"
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

consts class_rec ::"'c prog \<times> cname \<Rightarrow> 
        'a \<Rightarrow> (cname \<Rightarrow> fdecl list \<Rightarrow> 'c mdecl list \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a"

recdef class_rec "same_fst (\<lambda>G. wf ((subcls1 G)^-1)) (\<lambda>G. (subcls1 G)^-1)"
      "class_rec (G,C) = (\<lambda>t f. case class G C of None \<Rightarrow> arbitrary 
                         | Some (D,fs,ms) \<Rightarrow> if wf ((subcls1 G)^-1) then 
      f C fs ms (if C = Object then t else class_rec (G,D) t f) else arbitrary)"
(hints intro: subcls1I)

declare class_rec.simps [simp del]


lemma class_rec_lemma: "\<lbrakk> wf ((subcls1 G)^-1); class G C = Some (D,fs,ms)\<rbrakk> \<Longrightarrow>
 class_rec (G,C) t f = f C fs ms (if C=Object then t else class_rec (G,D) t f)";
  apply (rule class_rec.simps [THEN trans [THEN fun_cong [THEN fun_cong]]])
  apply simp
  done

consts

  method :: "'c prog \<times> cname => ( sig   \<leadsto> cname \<times> ty \<times> 'c)" (* ###curry *)
  field  :: "'c prog \<times> cname => ( vname \<leadsto> cname \<times> ty     )" (* ###curry *)
  fields :: "'c prog \<times> cname => ((vname \<times> cname) \<times> ty) list" (* ###curry *)

(* methods of a class, with inheritance, overriding and hiding, cf. 8.4.6 *)
defs method_def: "method \<equiv> \<lambda>(G,C). class_rec (G,C) empty (\<lambda>C fs ms ts.
                           ts ++ map_of (map (\<lambda>(s,m). (s,(C,m))) ms))"

lemma method_rec_lemma: "[|class G C = Some (D,fs,ms); wf ((subcls1 G)^-1)|] ==>
  method (G,C) = (if C = Object then empty else method (G,D)) ++  
  map_of (map (\<lambda>(s,m). (s,(C,m))) ms)"
apply (unfold method_def)
apply (simp split del: split_if)
apply (erule (1) class_rec_lemma [THEN trans]);
apply auto
done


(* list of fields of a class, including inherited and hidden ones *)
defs fields_def: "fields \<equiv> \<lambda>(G,C). class_rec (G,C) []    (\<lambda>C fs ms ts.
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


inductive "widen G" intros (*widening, viz. method invocation conversion,cf. 5.3
			     i.e. sort of syntactic subtyping *)
  refl   [intro!, simp]:       "G\<turnstile>      T \<preceq> T" 	 (* identity conv., cf. 5.1.1 *)
  subcls         : "G\<turnstile>C\<preceq>C D ==> G\<turnstile>Class C \<preceq> Class D"
  null   [intro!]:             "G\<turnstile>     NT \<preceq> RefT R"

inductive "cast G" intros (* casting conversion, cf. 5.5 / 5.1.5 *)
                          (* left out casts on primitve types    *)
  widen:  "G\<turnstile>C\<preceq>C D ==> G\<turnstile>C \<preceq>? D"
  subcls: "G\<turnstile>D\<preceq>C C ==> G\<turnstile>C \<preceq>? D"

lemma widen_PrimT_RefT [iff]: "(G\<turnstile>PrimT pT\<preceq>RefT rT) = False"
apply (rule iffI)
apply (erule widen.elims)
apply auto
done

lemma widen_RefT: "G\<turnstile>RefT R\<preceq>T ==> \<exists>t. T=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>T")
apply auto
done

lemma widen_RefT2: "G\<turnstile>S\<preceq>RefT R ==> \<exists>t. S=RefT t"
apply (ind_cases "G\<turnstile>S\<preceq>T")
apply auto
done

lemma widen_Class: "G\<turnstile>Class C\<preceq>T ==> \<exists>D. T=Class D"
apply (ind_cases "G\<turnstile>S\<preceq>T")
apply auto
done

lemma widen_Class_NullT [iff]: "(G\<turnstile>Class C\<preceq>NT) = False"
apply (rule iffI)
apply (ind_cases "G\<turnstile>S\<preceq>T")
apply auto
done

lemma widen_Class_Class [iff]: "(G\<turnstile>Class C\<preceq> Class D) = (G\<turnstile>C\<preceq>C D)"
apply (rule iffI)
apply (ind_cases "G\<turnstile>S\<preceq>T")
apply (auto elim: widen.subcls)
done

lemma widen_trans [rule_format (no_asm)]: "G\<turnstile>S\<preceq>U ==> \<forall>T. G\<turnstile>U\<preceq>T --> G\<turnstile>S\<preceq>T"
apply (erule widen.induct)
apply   safe
apply  (frule widen_Class)
apply  (frule_tac [2] widen_RefT)
apply  safe
apply(erule (1) rtrancl_trans)
done


(*####theorem widen_trans: "\<lbrakk>G\<turnstile>S\<preceq>U; G\<turnstile>U\<preceq>T\<rbrakk> \<Longrightarrow> G\<turnstile>S\<preceq>T"
proof -
  assume "G\<turnstile>S\<preceq>U"
  thus "\<And>T. G\<turnstile>U\<preceq>T \<Longrightarrow> G\<turnstile>S\<preceq>T" ( *(is "PROP ?P S U")* )
  proof (induct ( *cases* ) (open) ( *?P S U* ) rule: widen.induct [consumes 1])
    case refl
    fix T' assume "G\<turnstile>T\<preceq>T'" thus "G\<turnstile>T\<preceq>T'".
      ( * fix T' show "PROP ?P T T".* )
  next
    case subcls
    fix T assume "G\<turnstile>Class D\<preceq>T"
    then obtain E where "T = Class E" by (blast dest: widen_Class)
    from prems show "G\<turnstile>Class C\<preceq>T" proof (auto elim: rtrancl_trans) qed
  next
    case null
    fix RT assume "G\<turnstile>RefT R\<preceq>RT"
    then obtain rt where "RT = RefT rt" by (blast dest: widen_RefT)
    thus "G\<turnstile>NT\<preceq>RT" by auto
  qed
qed
*)

theorem widen_trans: "\<lbrakk>G\<turnstile>S\<preceq>U; G\<turnstile>U\<preceq>T\<rbrakk> \<Longrightarrow> G\<turnstile>S\<preceq>T"
proof -
  assume "G\<turnstile>S\<preceq>U"
  thus "\<And>T. G\<turnstile>U\<preceq>T \<Longrightarrow> G\<turnstile>S\<preceq>T"
  proof induct
    case (refl T T')
    thus "G\<turnstile>T\<preceq>T'" .
  next
    case (subcls C D T)
    then obtain E where "T = Class E" by (blast dest: widen_Class)
    with subcls show "G\<turnstile>Class C\<preceq>T" by (auto elim: rtrancl_trans)
  next
    case (null R RT)
    then obtain rt where "RT = RefT rt" by (blast dest: widen_RefT)
    thus "G\<turnstile>NT\<preceq>RT" by auto
  qed
qed

end
