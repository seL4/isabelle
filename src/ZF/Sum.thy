(*  Title:      ZF/sum.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Disjoint sums in Zermelo-Fraenkel Set Theory 
"Part" primitive for simultaneous recursive type definitions
*)

theory Sum = Bool + equalities:

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

(*** Rules for the Part primitive ***)

lemma Part_iff: 
    "a : Part(A,h) <-> a:A & (EX y. a=h(y))"
apply (unfold Part_def)
apply (rule separation)
done

lemma Part_eqI [intro]: 
    "[| a : A;  a=h(b) |] ==> a : Part(A,h)"
apply (unfold Part_def)
apply blast
done

lemmas PartI = refl [THEN [2] Part_eqI]

lemma PartE [elim!]: 
    "[| a : Part(A,h);  !!z. [| a : A;  a=h(z) |] ==> P   
     |] ==> P"
apply (unfold Part_def)
apply blast
done

lemma Part_subset: "Part(A,h) <= A"
apply (unfold Part_def)
apply (rule Collect_subset)
done


(*** Rules for Disjoint Sums ***)

lemmas sum_defs = sum_def Inl_def Inr_def case_def

lemma Sigma_bool: "Sigma(bool,C) = C(0) + C(1)"
apply (unfold bool_def sum_def)
apply blast
done

(** Introduction rules for the injections **)

lemma InlI [intro!,simp,TC]: "a : A ==> Inl(a) : A+B"
apply (unfold sum_defs)
apply blast
done

lemma InrI [intro!,simp,TC]: "b : B ==> Inr(b) : A+B"
apply (unfold sum_defs)
apply blast
done

(** Elimination rules **)

lemma sumE [elim!]:
    "[| u: A+B;   
        !!x. [| x:A;  u=Inl(x) |] ==> P;  
        !!y. [| y:B;  u=Inr(y) |] ==> P  
     |] ==> P"
apply (unfold sum_defs)
apply (blast intro: elim:); 
done

(** Injection and freeness equivalences, for rewriting **)

lemma Inl_iff [iff]: "Inl(a)=Inl(b) <-> a=b"
apply (simp add: sum_defs)
done

lemma Inr_iff [iff]: "Inr(a)=Inr(b) <-> a=b"
apply (simp add: sum_defs)
done

lemma Inl_Inr_iff [iff]: "Inl(a)=Inr(b) <-> False"
apply (simp add: sum_defs)
done

lemma Inr_Inl_iff [iff]: "Inr(b)=Inl(a) <-> False"
apply (simp add: sum_defs)
done

lemma sum_empty [simp]: "0+0 = 0"
apply (simp add: sum_defs)
done

(*Injection and freeness rules*)

lemmas Inl_inject = Inl_iff [THEN iffD1, standard]
lemmas Inr_inject = Inr_iff [THEN iffD1, standard]
lemmas Inl_neq_Inr = Inl_Inr_iff [THEN iffD1, THEN FalseE]
lemmas Inr_neq_Inl = Inr_Inl_iff [THEN iffD1, THEN FalseE]


lemma InlD: "Inl(a): A+B ==> a: A"
apply blast
done

lemma InrD: "Inr(b): A+B ==> b: B"
apply blast
done

lemma sum_iff: "u: A+B <-> (EX x. x:A & u=Inl(x)) | (EX y. y:B & u=Inr(y))"
apply blast
done

lemma sum_subset_iff: "A+B <= C+D <-> A<=C & B<=D"
apply blast
done

lemma sum_equal_iff: "A+B = C+D <-> A=C & B=D"
apply (simp add: extension sum_subset_iff)
apply blast
done

lemma sum_eq_2_times: "A+A = 2*A"
apply (simp add: sum_def)
apply blast
done


(*** Eliminator -- case ***)

lemma case_Inl [simp]: "case(c, d, Inl(a)) = c(a)"
apply (simp add: sum_defs)
done

lemma case_Inr [simp]: "case(c, d, Inr(b)) = d(b)"
apply (simp add: sum_defs)
done

lemma case_type [TC]:
    "[| u: A+B;  
        !!x. x: A ==> c(x): C(Inl(x));    
        !!y. y: B ==> d(y): C(Inr(y))  
     |] ==> case(c,d,u) : C(u)"
apply (auto );  
done

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
by (auto ); 

lemma case_case: "z: A+B ==>    
        case(c, d, case(%x. Inl(c'(x)), %y. Inr(d'(y)), z)) =  
        case(%x. c(c'(x)), %y. d(d'(y)), z)"
by auto


(*** More rules for Part(A,h) ***)

lemma Part_mono: "A<=B ==> Part(A,h)<=Part(B,h)"
apply blast
done

lemma Part_Collect: "Part(Collect(A,P), h) = Collect(Part(A,h), P)"
apply blast
done

lemmas Part_CollectE =
     Part_Collect [THEN equalityD1, THEN subsetD, THEN CollectE, standard]

lemma Part_Inl: "Part(A+B,Inl) = {Inl(x). x: A}"
apply blast
done

lemma Part_Inr: "Part(A+B,Inr) = {Inr(y). y: B}"
apply blast
done

lemma PartD1: "a : Part(A,h) ==> a : A"
apply (simp add: Part_def)
done

lemma Part_id: "Part(A,%x. x) = A"
apply blast
done

lemma Part_Inr2: "Part(A+B, %x. Inr(h(x))) = {Inr(y). y: Part(B,h)}"
apply blast
done

lemma Part_sum_equality: "C <= A+B ==> Part(C,Inl) Un Part(C,Inr) = C"
apply blast
done

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
