(*  Title:      HOL/NanoJava/TypeRel.thy
    Author:     David von Oheimb, Technische Universitaet Muenchen
*)

header "Type relations"

theory TypeRel imports Decl "~~/src/HOL/Library/Wfrec" begin

text{* Direct subclass relation *}

definition subcls1 :: "(cname \<times> cname) set"
where
  "subcls1 \<equiv> {(C,D). C\<noteq>Object \<and> (\<exists>c. class C = Some c \<and> super c=D)}"

abbreviation
  subcls1_syntax :: "[cname, cname] => bool"  ("_ <=C1 _" [71,71] 70)
  where "C <=C1 D == (C,D) \<in> subcls1"
abbreviation
  subcls_syntax  :: "[cname, cname] => bool" ("_ <=C _"  [71,71] 70)
  where "C <=C D == (C,D) \<in> subcls1^*"

notation (xsymbols)
  subcls1_syntax  ("_ \<prec>C1 _"  [71,71] 70) and
  subcls_syntax  ("_ \<preceq>C _"   [71,71] 70)


subsection "Declarations and properties not used in the meta theory"

text{* Widening, viz. method invocation conversion *}
inductive
  widen :: "ty => ty => bool"  ("_ \<preceq> _" [71,71] 70)
where
  refl [intro!, simp]: "T \<preceq> T"
| subcls: "C\<preceq>C D \<Longrightarrow> Class C \<preceq> Class D"
| null [intro!]: "NT \<preceq> R"

lemma subcls1D: 
  "C\<prec>C1D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>c. class C = Some c \<and> super c=D)"
apply (unfold subcls1_def)
apply auto
done

lemma subcls1I: "\<lbrakk>class C = Some m; super m = D; C \<noteq> Object\<rbrakk> \<Longrightarrow> C\<prec>C1D"
apply (unfold subcls1_def)
apply auto
done

lemma subcls1_def2: 
  "subcls1 = 
    (SIGMA C: {C. is_class C} . {D. C\<noteq>Object \<and> super (the (class C)) = D})"
apply (unfold subcls1_def is_class_def)
apply (auto split:split_if_asm)
done

lemma finite_subcls1: "finite subcls1"
apply(subst subcls1_def2)
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{super (the (class C))}" in finite_subset)
apply  auto
done

definition ws_prog :: "bool" where
 "ws_prog \<equiv> \<forall>(C,c)\<in>set Prog. C\<noteq>Object \<longrightarrow> 
                              is_class (super c) \<and> (super c,C)\<notin>subcls1^+"

lemma ws_progD: "\<lbrakk>class C = Some c; C\<noteq>Object; ws_prog\<rbrakk> \<Longrightarrow>  
  is_class (super c) \<and> (super c,C)\<notin>subcls1^+"
apply (unfold ws_prog_def class_def)
apply (drule_tac map_of_SomeD)
apply auto
done

lemma subcls1_irrefl_lemma1: "ws_prog \<Longrightarrow> subcls1^-1 \<inter> subcls1^+ = {}"
by (fast dest: subcls1D ws_progD)

(* irrefl_tranclI in Transitive_Closure.thy is more general *)
lemma irrefl_tranclI': "r^-1 Int r^+ = {} ==> !x. (x, x) ~: r^+"
by(blast elim: tranclE dest: trancl_into_rtrancl)


lemmas subcls1_irrefl_lemma2 = subcls1_irrefl_lemma1 [THEN irrefl_tranclI']

lemma subcls1_irrefl: "\<lbrakk>(x, y) \<in> subcls1; ws_prog\<rbrakk> \<Longrightarrow> x \<noteq> y"
apply (rule irrefl_trancl_rD)
apply (rule subcls1_irrefl_lemma2)
apply auto
done

lemmas subcls1_acyclic = subcls1_irrefl_lemma2 [THEN acyclicI]

lemma wf_subcls1: "ws_prog \<Longrightarrow> wf (subcls1\<inverse>)"
by (auto intro: finite_acyclic_wf_converse finite_subcls1 subcls1_acyclic)

definition class_rec ::"cname \<Rightarrow> (class \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  "class_rec \<equiv> wfrec (subcls1\<inverse>) (\<lambda>rec C f.
     case class C of None \<Rightarrow> undefined
      | Some m \<Rightarrow> (if C = Object then empty else rec (super m) f) ++ map_of (f m))"

lemma class_rec: "\<lbrakk>class C = Some m;  ws_prog\<rbrakk> \<Longrightarrow>
 class_rec C f = (if C = Object then empty else class_rec (super m) f) ++ 
                 map_of (f m)"
apply (drule wf_subcls1)
apply (subst def_wfrec[OF class_rec_def], auto)
apply (subst cut_apply, auto intro: subcls1I)
done

--{* Methods of a class, with inheritance and hiding *}
definition method :: "cname => (mname \<rightharpoonup> methd)" where
  "method C \<equiv> class_rec C methods"

lemma method_rec: "\<lbrakk>class C = Some m; ws_prog\<rbrakk> \<Longrightarrow>
method C = (if C=Object then empty else method (super m)) ++ map_of (methods m)"
apply (unfold method_def)
apply (erule (1) class_rec [THEN trans]);
apply simp
done


--{* Fields of a class, with inheritance and hiding *}
definition field  :: "cname => (fname \<rightharpoonup> ty)" where
  "field C \<equiv> class_rec C flds"

lemma flds_rec: "\<lbrakk>class C = Some m; ws_prog\<rbrakk> \<Longrightarrow>
field C = (if C=Object then empty else field (super m)) ++ map_of (flds m)"
apply (unfold field_def)
apply (erule (1) class_rec [THEN trans]);
apply simp
done

end
