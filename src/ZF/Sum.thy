(*  Title:      ZF/sum.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

header{*Disjoint Sums*}

theory Sum = Bool + equalities:

text{*And the "Part" primitive for simultaneous recursive type definitions*}

global

constdefs
  sum     :: "[i,i]=>i"                     (infixr "+" 65)
     "A+B == {0}*A Un {1}*B"

  Inl     :: "i=>i"
     "Inl(a) == <0,a>"

  Inr     :: "i=>i"
     "Inr(b) == <1,b>"

  "case"  :: "[i=>i, i=>i, i]=>i"
     "case(c,d) == (%<y,z>. cond(y, d(z), c(z)))"

  (*operator for selecting out the various summands*)
  Part    :: "[i,i=>i] => i"
     "Part(A,h) == {x: A. EX z. x = h(z)}"

local

subsection{*Rules for the @{term Part} Primitive*}

lemma Part_iff: 
    "a : Part(A,h) <-> a:A & (EX y. a=h(y))"
apply (unfold Part_def)
apply (rule separation)
done

lemma Part_eqI [intro]: 
    "[| a : A;  a=h(b) |] ==> a : Part(A,h)"
by (unfold Part_def, blast)

lemmas PartI = refl [THEN [2] Part_eqI]

lemma PartE [elim!]: 
    "[| a : Part(A,h);  !!z. [| a : A;  a=h(z) |] ==> P   
     |] ==> P"
apply (unfold Part_def, blast)
done

lemma Part_subset: "Part(A,h) <= A"
apply (unfold Part_def)
apply (rule Collect_subset)
done


subsection{*Rules for Disjoint Sums*}

lemmas sum_defs = sum_def Inl_def Inr_def case_def

lemma Sigma_bool: "Sigma(bool,C) = C(0) + C(1)"
by (unfold bool_def sum_def, blast)

(** Introduction rules for the injections **)

lemma InlI [intro!,simp,TC]: "a : A ==> Inl(a) : A+B"
by (unfold sum_defs, blast)

lemma InrI [intro!,simp,TC]: "b : B ==> Inr(b) : A+B"
by (unfold sum_defs, blast)

(** Elimination rules **)

lemma sumE [elim!]:
    "[| u: A+B;   
        !!x. [| x:A;  u=Inl(x) |] ==> P;  
        !!y. [| y:B;  u=Inr(y) |] ==> P  
     |] ==> P"
by (unfold sum_defs, blast) 

(** Injection and freeness equivalences, for rewriting **)

lemma Inl_iff [iff]: "Inl(a)=Inl(b) <-> a=b"
by (simp add: sum_defs)

lemma Inr_iff [iff]: "Inr(a)=Inr(b) <-> a=b"
by (simp add: sum_defs)

lemma Inl_Inr_iff [iff]: "Inl(a)=Inr(b) <-> False"
by (simp add: sum_defs)

lemma Inr_Inl_iff [iff]: "Inr(b)=Inl(a) <-> False"
by (simp add: sum_defs)

lemma sum_empty [simp]: "0+0 = 0"
by (simp add: sum_defs)

(*Injection and freeness rules*)

lemmas Inl_inject = Inl_iff [THEN iffD1, standard]
lemmas Inr_inject = Inr_iff [THEN iffD1, standard]
lemmas Inl_neq_Inr = Inl_Inr_iff [THEN iffD1, THEN FalseE]
lemmas Inr_neq_Inl = Inr_Inl_iff [THEN iffD1, THEN FalseE]


lemma InlD: "Inl(a): A+B ==> a: A"
by blast

lemma InrD: "Inr(b): A+B ==> b: B"
by blast

lemma sum_iff: "u: A+B <-> (EX x. x:A & u=Inl(x)) | (EX y. y:B & u=Inr(y))"
by blast

lemma Inl_in_sum_iff [simp]: "(Inl(x) \<in> A+B) <-> (x \<in> A)";
by auto

lemma Inr_in_sum_iff [simp]: "(Inr(y) \<in> A+B) <-> (y \<in> B)";
by auto

lemma sum_subset_iff: "A+B <= C+D <-> A<=C & B<=D"
by blast

lemma sum_equal_iff: "A+B = C+D <-> A=C & B=D"
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
     |] ==> case(c,d,u) : C(u)"
by auto

lemma expand_case: "u: A+B ==>    
        R(case(c,d,u)) <->  
        ((ALL x:A. u = Inl(x) --> R(c(x))) &  
        (ALL y:B. u = Inr(y) --> R(d(y))))"
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
     Part_Collect [THEN equalityD1, THEN subsetD, THEN CollectE, standard]

lemma Part_Inl: "Part(A+B,Inl) = {Inl(x). x: A}"
by blast

lemma Part_Inr: "Part(A+B,Inr) = {Inr(y). y: B}"
by blast

lemma PartD1: "a : Part(A,h) ==> a : A"
by (simp add: Part_def)

lemma Part_id: "Part(A,%x. x) = A"
by blast

lemma Part_Inr2: "Part(A+B, %x. Inr(h(x))) = {Inr(y). y: Part(B,h)}"
by blast

lemma Part_sum_equality: "C <= A+B ==> Part(C,Inl) Un Part(C,Inr) = C"
by blast

ML
{*
val sum_def = thm "sum_def";
val Inl_def = thm "Inl_def";
val Inr_def = thm "Inr_def";
val sum_defs = thms "sum_defs";

val Part_iff = thm "Part_iff";
val Part_eqI = thm "Part_eqI";
val PartI = thm "PartI";
val PartE = thm "PartE";
val Part_subset = thm "Part_subset";
val Sigma_bool = thm "Sigma_bool";
val InlI = thm "InlI";
val InrI = thm "InrI";
val sumE = thm "sumE";
val Inl_iff = thm "Inl_iff";
val Inr_iff = thm "Inr_iff";
val Inl_Inr_iff = thm "Inl_Inr_iff";
val Inr_Inl_iff = thm "Inr_Inl_iff";
val sum_empty = thm "sum_empty";
val Inl_inject = thm "Inl_inject";
val Inr_inject = thm "Inr_inject";
val Inl_neq_Inr = thm "Inl_neq_Inr";
val Inr_neq_Inl = thm "Inr_neq_Inl";
val InlD = thm "InlD";
val InrD = thm "InrD";
val sum_iff = thm "sum_iff";
val sum_subset_iff = thm "sum_subset_iff";
val sum_equal_iff = thm "sum_equal_iff";
val sum_eq_2_times = thm "sum_eq_2_times";
val case_Inl = thm "case_Inl";
val case_Inr = thm "case_Inr";
val case_type = thm "case_type";
val expand_case = thm "expand_case";
val case_cong = thm "case_cong";
val case_case = thm "case_case";
val Part_mono = thm "Part_mono";
val Part_Collect = thm "Part_Collect";
val Part_CollectE = thm "Part_CollectE";
val Part_Inl = thm "Part_Inl";
val Part_Inr = thm "Part_Inr";
val PartD1 = thm "PartD1";
val Part_id = thm "Part_id";
val Part_Inr2 = thm "Part_Inr2";
val Part_sum_equality = thm "Part_sum_equality";

*}



end
