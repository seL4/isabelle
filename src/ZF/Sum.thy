(*  Title:      ZF/Sum.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header{*Disjoint Sums*}

theory Sum imports Bool equalities begin

text{*And the "Part" primitive for simultaneous recursive type definitions*}

definition sum :: "[i,i]=>i" (infixr "+" 65) where
     "A+B == {0}*A \<union> {1}*B"

definition Inl :: "i=>i" where
     "Inl(a) == <0,a>"

definition Inr :: "i=>i" where
     "Inr(b) == <1,b>"

definition "case" :: "[i=>i, i=>i, i]=>i" where
     "case(c,d) == (%<y,z>. cond(y, d(z), c(z)))"

  (*operator for selecting out the various summands*)
definition Part :: "[i,i=>i] => i" where
     "Part(A,h) == {x: A. \<exists>z. x = h(z)}"

subsection{*Rules for the @{term Part} Primitive*}

lemma Part_iff: 
    "a \<in> Part(A,h) \<longleftrightarrow> a:A & (\<exists>y. a=h(y))"
apply (unfold Part_def)
apply (rule separation)
done

lemma Part_eqI [intro]: 
    "[| a \<in> A;  a=h(b) |] ==> a \<in> Part(A,h)"
by (unfold Part_def, blast)

lemmas PartI = refl [THEN [2] Part_eqI]

lemma PartE [elim!]: 
    "[| a \<in> Part(A,h);  !!z. [| a \<in> A;  a=h(z) |] ==> P   
     |] ==> P"
apply (unfold Part_def, blast)
done

lemma Part_subset: "Part(A,h) \<subseteq> A"
apply (unfold Part_def)
apply (rule Collect_subset)
done


subsection{*Rules for Disjoint Sums*}

lemmas sum_defs = sum_def Inl_def Inr_def case_def

lemma Sigma_bool: "Sigma(bool,C) = C(0) + C(1)"
by (unfold bool_def sum_def, blast)

(** Introduction rules for the injections **)

lemma InlI [intro!,simp,TC]: "a \<in> A ==> Inl(a) \<in> A+B"
by (unfold sum_defs, blast)

lemma InrI [intro!,simp,TC]: "b \<in> B ==> Inr(b) \<in> A+B"
by (unfold sum_defs, blast)

(** Elimination rules **)

lemma sumE [elim!]:
    "[| u: A+B;   
        !!x. [| x:A;  u=Inl(x) |] ==> P;  
        !!y. [| y:B;  u=Inr(y) |] ==> P  
     |] ==> P"
by (unfold sum_defs, blast) 

(** Injection and freeness equivalences, for rewriting **)

lemma Inl_iff [iff]: "Inl(a)=Inl(b) \<longleftrightarrow> a=b"
by (simp add: sum_defs)

lemma Inr_iff [iff]: "Inr(a)=Inr(b) \<longleftrightarrow> a=b"
by (simp add: sum_defs)

lemma Inl_Inr_iff [simp]: "Inl(a)=Inr(b) \<longleftrightarrow> False"
by (simp add: sum_defs)

lemma Inr_Inl_iff [simp]: "Inr(b)=Inl(a) \<longleftrightarrow> False"
by (simp add: sum_defs)

lemma sum_empty [simp]: "0+0 = 0"
by (simp add: sum_defs)

(*Injection and freeness rules*)

lemmas Inl_inject = Inl_iff [THEN iffD1]
lemmas Inr_inject = Inr_iff [THEN iffD1]
lemmas Inl_neq_Inr = Inl_Inr_iff [THEN iffD1, THEN FalseE, elim!]
lemmas Inr_neq_Inl = Inr_Inl_iff [THEN iffD1, THEN FalseE, elim!]


lemma InlD: "Inl(a): A+B ==> a: A"
by blast

lemma InrD: "Inr(b): A+B ==> b: B"
by blast

lemma sum_iff: "u: A+B \<longleftrightarrow> (\<exists>x. x:A & u=Inl(x)) | (\<exists>y. y:B & u=Inr(y))"
by blast

lemma Inl_in_sum_iff [simp]: "(Inl(x) \<in> A+B) \<longleftrightarrow> (x \<in> A)";
by auto

lemma Inr_in_sum_iff [simp]: "(Inr(y) \<in> A+B) \<longleftrightarrow> (y \<in> B)";
by auto

lemma sum_subset_iff: "A+B \<subseteq> C+D \<longleftrightarrow> A<=C & B<=D"
by blast

lemma sum_equal_iff: "A+B = C+D \<longleftrightarrow> A=C & B=D"
by (simp add: extension sum_subset_iff, blast)

lemma sum_eq_2_times: "A+A = 2*A"
by (simp add: sum_def, blast)


subsection{*The Eliminator: @{term case}*}

lemma case_Inl [simp]: "case(c, d, Inl(a)) = c(a)"
by (simp add: sum_defs)

lemma case_Inr [simp]: "case(c, d, Inr(b)) = d(b)"
by (simp add: sum_defs)

lemma case_type [TC]:
    "[| u: A+B;  
        !!x. x: A ==> c(x): C(Inl(x));    
        !!y. y: B ==> d(y): C(Inr(y))  
     |] ==> case(c,d,u) \<in> C(u)"
by auto

lemma expand_case: "u: A+B ==>    
        R(case(c,d,u)) \<longleftrightarrow>  
        ((\<forall>x\<in>A. u = Inl(x) \<longrightarrow> R(c(x))) &  
        (\<forall>y\<in>B. u = Inr(y) \<longrightarrow> R(d(y))))"
by auto

lemma case_cong:
  "[| z: A+B;    
      !!x. x:A ==> c(x)=c'(x);   
      !!y. y:B ==> d(y)=d'(y)    
   |] ==> case(c,d,z) = case(c',d',z)"
by auto 

lemma case_case: "z: A+B ==>    
        case(c, d, case(%x. Inl(c'(x)), %y. Inr(d'(y)), z)) =  
        case(%x. c(c'(x)), %y. d(d'(y)), z)"
by auto


subsection{*More Rules for @{term "Part(A,h)"}*}

lemma Part_mono: "A<=B ==> Part(A,h)<=Part(B,h)"
by blast

lemma Part_Collect: "Part(Collect(A,P), h) = Collect(Part(A,h), P)"
by blast

lemmas Part_CollectE =
     Part_Collect [THEN equalityD1, THEN subsetD, THEN CollectE]

lemma Part_Inl: "Part(A+B,Inl) = {Inl(x). x: A}"
by blast

lemma Part_Inr: "Part(A+B,Inr) = {Inr(y). y: B}"
by blast

lemma PartD1: "a \<in> Part(A,h) ==> a \<in> A"
by (simp add: Part_def)

lemma Part_id: "Part(A,%x. x) = A"
by blast

lemma Part_Inr2: "Part(A+B, %x. Inr(h(x))) = {Inr(y). y: Part(B,h)}"
by blast

lemma Part_sum_equality: "C \<subseteq> A+B ==> Part(C,Inl) \<union> Part(C,Inr) = C"
by blast

end
