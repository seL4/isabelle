(*  Title:      ZF/Ordinal.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Ordinals in Zermelo-Fraenkel Set Theory 
*)

theory Ordinal = WF + Bool + equalities:

constdefs

  Memrel        :: "i=>i"
    "Memrel(A)   == {z: A*A . EX x y. z=<x,y> & x:y }"

  Transset  :: "i=>o"
    "Transset(i) == ALL x:i. x<=i"

  Ord  :: "i=>o"
    "Ord(i)      == Transset(i) & (ALL x:i. Transset(x))"

  lt        :: "[i,i] => o"  (infixl "<" 50)   (*less-than on ordinals*)
    "i<j         == i:j & Ord(j)"

  Limit         :: "i=>o"
    "Limit(i)    == Ord(i) & 0<i & (ALL y. y<i --> succ(y)<i)"

syntax
  "le"          :: "[i,i] => o"  (infixl 50)   (*less-than or equals*)

translations
  "x le y"      == "x < succ(y)"

syntax (xsymbols)
  "op le"       :: "[i,i] => o"  (infixl "\<le>" 50)  (*less-than or equals*)


(*** Rules for Transset ***)

(** Three neat characterisations of Transset **)

lemma Transset_iff_Pow: "Transset(A) <-> A<=Pow(A)"
by (unfold Transset_def, blast)

lemma Transset_iff_Union_succ: "Transset(A) <-> Union(succ(A)) = A"
apply (unfold Transset_def)
apply (blast elim!: equalityE)
done

lemma Transset_iff_Union_subset: "Transset(A) <-> Union(A) <= A"
by (unfold Transset_def, blast)

(** Consequences of downwards closure **)

lemma Transset_doubleton_D: 
    "[| Transset(C); {a,b}: C |] ==> a:C & b: C"
by (unfold Transset_def, blast)

lemma Transset_Pair_D:
    "[| Transset(C); <a,b>: C |] ==> a:C & b: C"
apply (simp add: Pair_def)
apply (blast dest: Transset_doubleton_D)
done

lemma Transset_includes_domain:
    "[| Transset(C); A*B <= C; b: B |] ==> A <= C"
by (blast dest: Transset_Pair_D)

lemma Transset_includes_range:
    "[| Transset(C); A*B <= C; a: A |] ==> B <= C"
by (blast dest: Transset_Pair_D)

(** Closure properties **)

lemma Transset_0: "Transset(0)"
by (unfold Transset_def, blast)

lemma Transset_Un: 
    "[| Transset(i);  Transset(j) |] ==> Transset(i Un j)"
by (unfold Transset_def, blast)

lemma Transset_Int: 
    "[| Transset(i);  Transset(j) |] ==> Transset(i Int j)"
by (unfold Transset_def, blast)

lemma Transset_succ: "Transset(i) ==> Transset(succ(i))"
by (unfold Transset_def, blast)

lemma Transset_Pow: "Transset(i) ==> Transset(Pow(i))"
by (unfold Transset_def, blast)

lemma Transset_Union: "Transset(A) ==> Transset(Union(A))"
by (unfold Transset_def, blast)

lemma Transset_Union_family: 
    "[| !!i. i:A ==> Transset(i) |] ==> Transset(Union(A))"
by (unfold Transset_def, blast)

lemma Transset_Inter_family: 
    "[| !!i. i:A ==> Transset(i) |] ==> Transset(Inter(A))"
by (unfold Inter_def Transset_def, blast)

lemma Transset_UN:
     "(!!x. x \<in> A ==> Transset(B(x))) ==> Transset (UN x:A. B(x))"
by (rule Transset_Union_family, auto) 

lemma Transset_INT:
     "(!!x. x \<in> A ==> Transset(B(x))) ==> Transset (INT x:A. B(x))"
by (rule Transset_Inter_family, auto) 


(*** Natural Deduction rules for Ord ***)

lemma OrdI:
    "[| Transset(i);  !!x. x:i ==> Transset(x) |]  ==>  Ord(i)"
by (simp add: Ord_def) 

lemma Ord_is_Transset: "Ord(i) ==> Transset(i)"
by (simp add: Ord_def) 

lemma Ord_contains_Transset: 
    "[| Ord(i);  j:i |] ==> Transset(j) "
by (unfold Ord_def, blast)

(*** Lemmas for ordinals ***)

lemma Ord_in_Ord: "[| Ord(i);  j:i |] ==> Ord(j)"
by (unfold Ord_def Transset_def, blast)

(*suitable for rewriting PROVIDED i has been fixed*)
lemma Ord_in_Ord': "[| j:i; Ord(i) |] ==> Ord(j)"
by (blast intro: Ord_in_Ord)

(* Ord(succ(j)) ==> Ord(j) *)
lemmas Ord_succD = Ord_in_Ord [OF _ succI1]

lemma Ord_subset_Ord: "[| Ord(i);  Transset(j);  j<=i |] ==> Ord(j)"
by (simp add: Ord_def Transset_def, blast)

lemma OrdmemD: "[| j:i;  Ord(i) |] ==> j<=i"
by (unfold Ord_def Transset_def, blast)

lemma Ord_trans: "[| i:j;  j:k;  Ord(k) |] ==> i:k"
by (blast dest: OrdmemD)

lemma Ord_succ_subsetI: "[| i:j;  Ord(j) |] ==> succ(i) <= j"
by (blast dest: OrdmemD)


(*** The construction of ordinals: 0, succ, Union ***)

lemma Ord_0 [iff,TC]: "Ord(0)"
by (blast intro: OrdI Transset_0)

lemma Ord_succ [TC]: "Ord(i) ==> Ord(succ(i))"
by (blast intro: OrdI Transset_succ Ord_is_Transset Ord_contains_Transset)

lemmas Ord_1 = Ord_0 [THEN Ord_succ]

lemma Ord_succ_iff [iff]: "Ord(succ(i)) <-> Ord(i)"
by (blast intro: Ord_succ dest!: Ord_succD)

lemma Ord_Un [intro,simp,TC]: "[| Ord(i); Ord(j) |] ==> Ord(i Un j)"
apply (unfold Ord_def)
apply (blast intro!: Transset_Un)
done

lemma Ord_Int [TC]: "[| Ord(i); Ord(j) |] ==> Ord(i Int j)"
apply (unfold Ord_def)
apply (blast intro!: Transset_Int)
done

(*There is no set of all ordinals, for then it would contain itself*)
lemma ON_class: "~ (ALL i. i:X <-> Ord(i))"
apply (rule notI)
apply (frule_tac x = "X" in spec)
apply (safe elim!: mem_irrefl)
apply (erule swap, rule OrdI [OF _ Ord_is_Transset])
apply (simp add: Transset_def)
apply (blast intro: Ord_in_Ord)+
done

(*** < is 'less than' for ordinals ***)

lemma ltI: "[| i:j;  Ord(j) |] ==> i<j"
by (unfold lt_def, blast)

lemma ltE:
    "[| i<j;  [| i:j;  Ord(i);  Ord(j) |] ==> P |] ==> P"
apply (unfold lt_def)
apply (blast intro: Ord_in_Ord)
done

lemma ltD: "i<j ==> i:j"
by (erule ltE, assumption)

lemma not_lt0 [simp]: "~ i<0"
by (unfold lt_def, blast)

lemma lt_Ord: "j<i ==> Ord(j)"
by (erule ltE, assumption)

lemma lt_Ord2: "j<i ==> Ord(i)"
by (erule ltE, assumption)

(* "ja le j ==> Ord(j)" *)
lemmas le_Ord2 = lt_Ord2 [THEN Ord_succD]

(* i<0 ==> R *)
lemmas lt0E = not_lt0 [THEN notE, elim!]

lemma lt_trans: "[| i<j;  j<k |] ==> i<k"
by (blast intro!: ltI elim!: ltE intro: Ord_trans)

lemma lt_not_sym: "i<j ==> ~ (j<i)"
apply (unfold lt_def)
apply (blast elim: mem_asym)
done

(* [| i<j;  ~P ==> j<i |] ==> P *)
lemmas lt_asym = lt_not_sym [THEN swap]

lemma lt_irrefl [elim!]: "i<i ==> P"
by (blast intro: lt_asym)

lemma lt_not_refl: "~ i<i"
apply (rule notI)
apply (erule lt_irrefl)
done


(** le is less than or equals;  recall  i le j  abbrevs  i<succ(j) !! **)

lemma le_iff: "i le j <-> i<j | (i=j & Ord(j))"
by (unfold lt_def, blast)

(*Equivalently, i<j ==> i < succ(j)*)
lemma leI: "i<j ==> i le j"
by (simp (no_asm_simp) add: le_iff)

lemma le_eqI: "[| i=j;  Ord(j) |] ==> i le j"
by (simp (no_asm_simp) add: le_iff)

lemmas le_refl = refl [THEN le_eqI]

lemma le_refl_iff [iff]: "i le i <-> Ord(i)"
by (simp (no_asm_simp) add: lt_not_refl le_iff)

lemma leCI: "(~ (i=j & Ord(j)) ==> i<j) ==> i le j"
by (simp add: le_iff, blast)

lemma leE:
    "[| i le j;  i<j ==> P;  [| i=j;  Ord(j) |] ==> P |] ==> P"
by (simp add: le_iff, blast)

lemma le_anti_sym: "[| i le j;  j le i |] ==> i=j"
apply (simp add: le_iff)
apply (blast elim: lt_asym)
done

lemma le0_iff [simp]: "i le 0 <-> i=0"
by (blast elim!: leE)

lemmas le0D = le0_iff [THEN iffD1, dest!]

(*** Natural Deduction rules for Memrel ***)

(*The lemmas MemrelI/E give better speed than [iff] here*)
lemma Memrel_iff [simp]: "<a,b> : Memrel(A) <-> a:b & a:A & b:A"
by (unfold Memrel_def, blast)

lemma MemrelI [intro!]: "[| a: b;  a: A;  b: A |] ==> <a,b> : Memrel(A)"
by auto

lemma MemrelE [elim!]:
    "[| <a,b> : Memrel(A);   
        [| a: A;  b: A;  a:b |]  ==> P |]  
     ==> P"
by auto

lemma Memrel_type: "Memrel(A) <= A*A"
by (unfold Memrel_def, blast)

lemma Memrel_mono: "A<=B ==> Memrel(A) <= Memrel(B)"
by (unfold Memrel_def, blast)

lemma Memrel_0 [simp]: "Memrel(0) = 0"
by (unfold Memrel_def, blast)

lemma Memrel_1 [simp]: "Memrel(1) = 0"
by (unfold Memrel_def, blast)

(*The membership relation (as a set) is well-founded.
  Proof idea: show A<=B by applying the foundation axiom to A-B *)
lemma wf_Memrel: "wf(Memrel(A))"
apply (unfold wf_def)
apply (rule foundation [THEN disjE, THEN allI], erule disjI1, blast) 
done

(*Transset(i) does not suffice, though ALL j:i.Transset(j) does*)
lemma trans_Memrel: 
    "Ord(i) ==> trans(Memrel(i))"
by (unfold Ord_def Transset_def trans_def, blast)

(*If Transset(A) then Memrel(A) internalizes the membership relation below A*)
lemma Transset_Memrel_iff: 
    "Transset(A) ==> <a,b> : Memrel(A) <-> a:b & b:A"
by (unfold Transset_def, blast)


(*** Transfinite induction ***)

(*Epsilon induction over a transitive set*)
lemma Transset_induct: 
    "[| i: k;  Transset(k);                           
        !!x.[| x: k;  ALL y:x. P(y) |] ==> P(x) |]
     ==>  P(i)"
apply (simp add: Transset_def) 
apply (erule wf_Memrel [THEN wf_induct2], blast)
apply blast 
done

(*Induction over an ordinal*)
lemmas Ord_induct = Transset_induct [OF _ Ord_is_Transset]

(*Induction over the class of ordinals -- a useful corollary of Ord_induct*)

lemma trans_induct:
    "[| Ord(i);  
        !!x.[| Ord(x);  ALL y:x. P(y) |] ==> P(x) |]
     ==>  P(i)"
apply (rule Ord_succ [THEN succI1 [THEN Ord_induct]], assumption)
apply (blast intro: Ord_succ [THEN Ord_in_Ord]) 
done


(*** Fundamental properties of the epsilon ordering (< on ordinals) ***)


(** Proving that < is a linear ordering on the ordinals **)

lemma Ord_linear [rule_format]:
     "Ord(i) ==> (ALL j. Ord(j) --> i:j | i=j | j:i)"
apply (erule trans_induct)
apply (rule impI [THEN allI])
apply (erule_tac i=j in trans_induct) 
apply (blast dest: Ord_trans) 
done

(*The trichotomy law for ordinals!*)
lemma Ord_linear_lt:
    "[| Ord(i);  Ord(j);  i<j ==> P;  i=j ==> P;  j<i ==> P |] ==> P"
apply (simp add: lt_def) 
apply (rule_tac i1=i and j1=j in Ord_linear [THEN disjE], blast+)
done

lemma Ord_linear2:
    "[| Ord(i);  Ord(j);  i<j ==> P;  j le i ==> P |]  ==> P"
apply (rule_tac i = "i" and j = "j" in Ord_linear_lt)
apply (blast intro: leI le_eqI sym ) +
done

lemma Ord_linear_le:
    "[| Ord(i);  Ord(j);  i le j ==> P;  j le i ==> P |]  ==> P"
apply (rule_tac i = "i" and j = "j" in Ord_linear_lt)
apply (blast intro: leI le_eqI ) +
done

lemma le_imp_not_lt: "j le i ==> ~ i<j"
by (blast elim!: leE elim: lt_asym)

lemma not_lt_imp_le: "[| ~ i<j;  Ord(i);  Ord(j) |] ==> j le i"
by (rule_tac i = "i" and j = "j" in Ord_linear2, auto)

(** Some rewrite rules for <, le **)

lemma Ord_mem_iff_lt: "Ord(j) ==> i:j <-> i<j"
by (unfold lt_def, blast)

lemma not_lt_iff_le: "[| Ord(i);  Ord(j) |] ==> ~ i<j <-> j le i"
by (blast dest: le_imp_not_lt not_lt_imp_le)

lemma not_le_iff_lt: "[| Ord(i);  Ord(j) |] ==> ~ i le j <-> j<i"
by (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym])

(*This is identical to 0<succ(i) *)
lemma Ord_0_le: "Ord(i) ==> 0 le i"
by (erule not_lt_iff_le [THEN iffD1], auto)

lemma Ord_0_lt: "[| Ord(i);  i~=0 |] ==> 0<i"
apply (erule not_le_iff_lt [THEN iffD1])
apply (rule Ord_0, blast)
done

lemma Ord_0_lt_iff: "Ord(i) ==> i~=0 <-> 0<i"
by (blast intro: Ord_0_lt)


(*** Results about less-than or equals ***)

(** For ordinals, j<=i (subset) implies j le i (less-than or equals) **)

lemma zero_le_succ_iff [iff]: "0 le succ(x) <-> Ord(x)"
by (blast intro: Ord_0_le elim: ltE)

lemma subset_imp_le: "[| j<=i;  Ord(i);  Ord(j) |] ==> j le i"
apply (rule not_lt_iff_le [THEN iffD1], assumption)
apply assumption
apply (blast elim: ltE mem_irrefl)
done

lemma le_imp_subset: "i le j ==> i<=j"
by (blast dest: OrdmemD elim: ltE leE)

lemma le_subset_iff: "j le i <-> j<=i & Ord(i) & Ord(j)"
by (blast dest: subset_imp_le le_imp_subset elim: ltE)

lemma le_succ_iff: "i le succ(j) <-> i le j | i=succ(j) & Ord(i)"
apply (simp (no_asm) add: le_iff)
apply blast
done

(*Just a variant of subset_imp_le*)
lemma all_lt_imp_le: "[| Ord(i);  Ord(j);  !!x. x<j ==> x<i |] ==> j le i"
by (blast intro: not_lt_imp_le dest: lt_irrefl)

(** Transitive laws **)

lemma lt_trans1: "[| i le j;  j<k |] ==> i<k"
by (blast elim!: leE intro: lt_trans)

lemma lt_trans2: "[| i<j;  j le k |] ==> i<k"
by (blast elim!: leE intro: lt_trans)

lemma le_trans: "[| i le j;  j le k |] ==> i le k"
by (blast intro: lt_trans1)

lemma succ_leI: "i<j ==> succ(i) le j"
apply (rule not_lt_iff_le [THEN iffD1]) 
apply (blast elim: ltE leE lt_asym)+
done

(*Identical to  succ(i) < succ(j) ==> i<j  *)
lemma succ_leE: "succ(i) le j ==> i<j"
apply (rule not_le_iff_lt [THEN iffD1])
apply (blast elim: ltE leE lt_asym)+
done

lemma succ_le_iff [iff]: "succ(i) le j <-> i<j"
by (blast intro: succ_leI succ_leE)

lemma succ_le_imp_le: "succ(i) le succ(j) ==> i le j"
by (blast dest!: succ_leE)

lemma lt_subset_trans: "[| i <= j;  j<k;  Ord(i) |] ==> i<k"
apply (rule subset_imp_le [THEN lt_trans1]) 
apply (blast intro: elim: ltE) +
done

lemma lt_imp_0_lt: "j<i ==> 0<i"
by (blast intro: lt_trans1 Ord_0_le [OF lt_Ord]) 

lemma succ_lt_iff: "succ(i) < j <-> i<j & succ(i) \<noteq> j"
apply auto 
apply (blast intro: lt_trans le_refl dest: lt_Ord) 
apply (frule lt_Ord) 
apply (rule not_le_iff_lt [THEN iffD1]) 
  apply (blast intro: lt_Ord2)
 apply blast  
apply (simp add: lt_Ord lt_Ord2 le_iff) 
apply (blast dest: lt_asym) 
done

lemma Ord_succ_mem_iff: "Ord(j) ==> succ(i) \<in> succ(j) <-> i\<in>j"
apply (insert succ_le_iff [of i j]) 
apply (simp add: lt_def) 
done

(** Union and Intersection **)

lemma Un_upper1_le: "[| Ord(i); Ord(j) |] ==> i le i Un j"
by (rule Un_upper1 [THEN subset_imp_le], auto)

lemma Un_upper2_le: "[| Ord(i); Ord(j) |] ==> j le i Un j"
by (rule Un_upper2 [THEN subset_imp_le], auto)

(*Replacing k by succ(k') yields the similar rule for le!*)
lemma Un_least_lt: "[| i<k;  j<k |] ==> i Un j < k"
apply (rule_tac i = "i" and j = "j" in Ord_linear_le)
apply (auto simp add: Un_commute le_subset_iff subset_Un_iff lt_Ord) 
done

lemma Un_least_lt_iff: "[| Ord(i); Ord(j) |] ==> i Un j < k  <->  i<k & j<k"
apply (safe intro!: Un_least_lt)
apply (rule_tac [2] Un_upper2_le [THEN lt_trans1])
apply (rule Un_upper1_le [THEN lt_trans1], auto) 
done

lemma Un_least_mem_iff:
    "[| Ord(i); Ord(j); Ord(k) |] ==> i Un j : k  <->  i:k & j:k"
apply (insert Un_least_lt_iff [of i j k]) 
apply (simp add: lt_def)
done

(*Replacing k by succ(k') yields the similar rule for le!*)
lemma Int_greatest_lt: "[| i<k;  j<k |] ==> i Int j < k"
apply (rule_tac i = "i" and j = "j" in Ord_linear_le)
apply (auto simp add: Int_commute le_subset_iff subset_Int_iff lt_Ord) 
done

lemma Ord_Un_if:
     "[| Ord(i); Ord(j) |] ==> i \<union> j = (if j<i then i else j)"
by (simp add: not_lt_iff_le le_imp_subset leI
              subset_Un_iff [symmetric]  subset_Un_iff2 [symmetric]) 

lemma succ_Un_distrib:
     "[| Ord(i); Ord(j) |] ==> succ(i \<union> j) = succ(i) \<union> succ(j)"
by (simp add: Ord_Un_if lt_Ord le_Ord2) 

lemma lt_Un_iff:
     "[| Ord(i); Ord(j) |] ==> k < i \<union> j <-> k < i | k < j";
apply (simp add: Ord_Un_if not_lt_iff_le) 
apply (blast intro: leI lt_trans2)+ 
done

lemma le_Un_iff:
     "[| Ord(i); Ord(j) |] ==> k \<le> i \<union> j <-> k \<le> i | k \<le> j";
by (simp add: succ_Un_distrib lt_Un_iff [symmetric]) 

lemma Un_upper1_lt: "[|k < i; Ord(j)|] ==> k < i Un j"
by (simp add: lt_Un_iff lt_Ord2) 

lemma Un_upper2_lt: "[|k < j; Ord(i)|] ==> k < i Un j"
by (simp add: lt_Un_iff lt_Ord2) 

(*See also Transset_iff_Union_succ*)
lemma Ord_Union_succ_eq: "Ord(i) ==> \<Union>(succ(i)) = i"
by (blast intro: Ord_trans)


(*** Results about limits ***)

lemma Ord_Union [intro,simp,TC]: "[| !!i. i:A ==> Ord(i) |] ==> Ord(Union(A))"
apply (rule Ord_is_Transset [THEN Transset_Union_family, THEN OrdI])
apply (blast intro: Ord_contains_Transset)+
done

lemma Ord_UN [intro,simp,TC]:
     "[| !!x. x:A ==> Ord(B(x)) |] ==> Ord(UN x:A. B(x))"
by (rule Ord_Union, blast)

lemma Ord_Inter [intro,simp,TC]:
    "[| !!i. i:A ==> Ord(i) |] ==> Ord(Inter(A))" 
apply (rule Transset_Inter_family [THEN OrdI])
apply (blast intro: Ord_is_Transset) 
apply (simp add: Inter_def) 
apply (blast intro: Ord_contains_Transset) 
done

lemma Ord_INT [intro,simp,TC]:
    "[| !!x. x:A ==> Ord(B(x)) |] ==> Ord(INT x:A. B(x))"
by (rule Ord_Inter, blast) 


(* No < version; consider (UN i:nat.i)=nat *)
lemma UN_least_le:
    "[| Ord(i);  !!x. x:A ==> b(x) le i |] ==> (UN x:A. b(x)) le i"
apply (rule le_imp_subset [THEN UN_least, THEN subset_imp_le])
apply (blast intro: Ord_UN elim: ltE)+
done

lemma UN_succ_least_lt:
    "[| j<i;  !!x. x:A ==> b(x)<j |] ==> (UN x:A. succ(b(x))) < i"
apply (rule ltE, assumption)
apply (rule UN_least_le [THEN lt_trans2])
apply (blast intro: succ_leI)+
done

lemma UN_upper_lt:
     "[| a\<in>A;  i < b(a);  Ord(\<Union>x\<in>A. b(x)) |] ==> i < (\<Union>x\<in>A. b(x))"
by (unfold lt_def, blast) 

lemma UN_upper_le:
     "[| a: A;  i le b(a);  Ord(UN x:A. b(x)) |] ==> i le (UN x:A. b(x))"
apply (frule ltD)
apply (rule le_imp_subset [THEN subset_trans, THEN subset_imp_le])
apply (blast intro: lt_Ord UN_upper)+
done

lemma lt_Union_iff: "\<forall>i\<in>A. Ord(i) ==> (j < \<Union>(A)) <-> (\<exists>i\<in>A. j<i)"
by (auto simp: lt_def Ord_Union)

lemma Union_upper_le:
     "[| j: J;  i\<le>j;  Ord(\<Union>(J)) |] ==> i \<le> \<Union>J"
apply (subst Union_eq_UN)  
apply (rule UN_upper_le, auto)
done

lemma le_implies_UN_le_UN:
    "[| !!x. x:A ==> c(x) le d(x) |] ==> (UN x:A. c(x)) le (UN x:A. d(x))"
apply (rule UN_least_le)
apply (rule_tac [2] UN_upper_le)
apply (blast intro: Ord_UN le_Ord2)+ 
done

lemma Ord_equality: "Ord(i) ==> (UN y:i. succ(y)) = i"
by (blast intro: Ord_trans)

(*Holds for all transitive sets, not just ordinals*)
lemma Ord_Union_subset: "Ord(i) ==> Union(i) <= i"
by (blast intro: Ord_trans)


(*** Limit ordinals -- general properties ***)

lemma Limit_Union_eq: "Limit(i) ==> Union(i) = i"
apply (unfold Limit_def)
apply (fast intro!: ltI elim!: ltE elim: Ord_trans)
done

lemma Limit_is_Ord: "Limit(i) ==> Ord(i)"
apply (unfold Limit_def)
apply (erule conjunct1)
done

lemma Limit_has_0: "Limit(i) ==> 0 < i"
apply (unfold Limit_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma Limit_has_succ: "[| Limit(i);  j<i |] ==> succ(j) < i"
by (unfold Limit_def, blast)

lemma zero_not_Limit [iff]: "~ Limit(0)"
by (simp add: Limit_def)

lemma Limit_has_1: "Limit(i) ==> 1 < i"
by (blast intro: Limit_has_0 Limit_has_succ)

lemma increasing_LimitI: "[| 0<l; \<forall>x\<in>l. \<exists>y\<in>l. x<y |] ==> Limit(l)"
apply (simp add: Limit_def lt_Ord2, clarify)
apply (drule_tac i=y in ltD) 
apply (blast intro: lt_trans1 [OF _ ltI] lt_Ord2)
done

lemma non_succ_LimitI: 
    "[| 0<i;  ALL y. succ(y) ~= i |] ==> Limit(i)"
apply (unfold Limit_def)
apply (safe del: subsetI)
apply (rule_tac [2] not_le_iff_lt [THEN iffD1])
apply (simp_all add: lt_Ord lt_Ord2) 
apply (blast elim: leE lt_asym)
done

lemma succ_LimitE [elim!]: "Limit(succ(i)) ==> P"
apply (rule lt_irrefl)
apply (rule Limit_has_succ, assumption)
apply (erule Limit_is_Ord [THEN Ord_succD, THEN le_refl])
done

lemma not_succ_Limit [simp]: "~ Limit(succ(i))"
by blast

lemma Limit_le_succD: "[| Limit(i);  i le succ(j) |] ==> i le j"
by (blast elim!: leE)


(** Traditional 3-way case analysis on ordinals **)

lemma Ord_cases_disj: "Ord(i) ==> i=0 | (EX j. Ord(j) & i=succ(j)) | Limit(i)"
by (blast intro!: non_succ_LimitI Ord_0_lt)

lemma Ord_cases:
    "[| Ord(i);                  
        i=0                          ==> P;      
        !!j. [| Ord(j); i=succ(j) |] ==> P;      
        Limit(i)                     ==> P       
     |] ==> P"
by (drule Ord_cases_disj, blast)  

lemma trans_induct3:
     "[| Ord(i);                 
         P(0);                   
         !!x. [| Ord(x);  P(x) |] ==> P(succ(x));        
         !!x. [| Limit(x);  ALL y:x. P(y) |] ==> P(x)    
      |] ==> P(i)"
apply (erule trans_induct)
apply (erule Ord_cases, blast+)
done

text{*A set of ordinals is either empty, contains its own union, or its
union is a limit ordinal.*}
lemma Ord_set_cases:
   "\<forall>i\<in>I. Ord(i) ==> I=0 \<or> \<Union>(I) \<in> I \<or> (\<Union>(I) \<notin> I \<and> Limit(\<Union>(I)))"
apply (clarify elim!: not_emptyE) 
apply (cases "\<Union>(I)" rule: Ord_cases) 
   apply (blast intro: Ord_Union)
  apply (blast intro: subst_elem)
 apply auto 
apply (clarify elim!: equalityE succ_subsetE)
apply (simp add: Union_subset_iff)
apply (subgoal_tac "B = succ(j)", blast)
apply (rule le_anti_sym) 
 apply (simp add: le_subset_iff) 
apply (simp add: ltI)
done

text{*If the union of a set of ordinals is a successor, then it is
an element of that set.*}
lemma Ord_Union_eq_succD: "[|\<forall>x\<in>X. Ord(x);  \<Union>X = succ(j)|] ==> succ(j) \<in> X"
by (drule Ord_set_cases, auto)

lemma Limit_Union [rule_format]: "[| I \<noteq> 0;  \<forall>i\<in>I. Limit(i) |] ==> Limit(\<Union>I)"
apply (simp add: Limit_def lt_def)
apply (blast intro!: equalityI)
done

(*special induction rules for the "induct" method*)
lemmas Ord_induct = Ord_induct [consumes 2]
  and Ord_induct_rule = Ord_induct [rule_format, consumes 2]
  and trans_induct = trans_induct [consumes 1]
  and trans_induct_rule = trans_induct [rule_format, consumes 1]
  and trans_induct3 = trans_induct3 [case_names 0 succ limit, consumes 1]
  and trans_induct3_rule = trans_induct3 [rule_format, case_names 0 succ limit, consumes 1]

ML 
{*
val Memrel_def = thm "Memrel_def";
val Transset_def = thm "Transset_def";
val Ord_def = thm "Ord_def";
val lt_def = thm "lt_def";
val Limit_def = thm "Limit_def";

val Transset_iff_Pow = thm "Transset_iff_Pow";
val Transset_iff_Union_succ = thm "Transset_iff_Union_succ";
val Transset_iff_Union_subset = thm "Transset_iff_Union_subset";
val Transset_doubleton_D = thm "Transset_doubleton_D";
val Transset_Pair_D = thm "Transset_Pair_D";
val Transset_includes_domain = thm "Transset_includes_domain";
val Transset_includes_range = thm "Transset_includes_range";
val Transset_0 = thm "Transset_0";
val Transset_Un = thm "Transset_Un";
val Transset_Int = thm "Transset_Int";
val Transset_succ = thm "Transset_succ";
val Transset_Pow = thm "Transset_Pow";
val Transset_Union = thm "Transset_Union";
val Transset_Union_family = thm "Transset_Union_family";
val Transset_Inter_family = thm "Transset_Inter_family";
val OrdI = thm "OrdI";
val Ord_is_Transset = thm "Ord_is_Transset";
val Ord_contains_Transset = thm "Ord_contains_Transset";
val Ord_in_Ord = thm "Ord_in_Ord";
val Ord_succD = thm "Ord_succD";
val Ord_subset_Ord = thm "Ord_subset_Ord";
val OrdmemD = thm "OrdmemD";
val Ord_trans = thm "Ord_trans";
val Ord_succ_subsetI = thm "Ord_succ_subsetI";
val Ord_0 = thm "Ord_0";
val Ord_succ = thm "Ord_succ";
val Ord_1 = thm "Ord_1";
val Ord_succ_iff = thm "Ord_succ_iff";
val Ord_Un = thm "Ord_Un";
val Ord_Int = thm "Ord_Int";
val Ord_Inter = thm "Ord_Inter";
val Ord_INT = thm "Ord_INT";
val ON_class = thm "ON_class";
val ltI = thm "ltI";
val ltE = thm "ltE";
val ltD = thm "ltD";
val not_lt0 = thm "not_lt0";
val lt_Ord = thm "lt_Ord";
val lt_Ord2 = thm "lt_Ord2";
val le_Ord2 = thm "le_Ord2";
val lt0E = thm "lt0E";
val lt_trans = thm "lt_trans";
val lt_not_sym = thm "lt_not_sym";
val lt_asym = thm "lt_asym";
val lt_irrefl = thm "lt_irrefl";
val lt_not_refl = thm "lt_not_refl";
val le_iff = thm "le_iff";
val leI = thm "leI";
val le_eqI = thm "le_eqI";
val le_refl = thm "le_refl";
val le_refl_iff = thm "le_refl_iff";
val leCI = thm "leCI";
val leE = thm "leE";
val le_anti_sym = thm "le_anti_sym";
val le0_iff = thm "le0_iff";
val le0D = thm "le0D";
val Memrel_iff = thm "Memrel_iff";
val MemrelI = thm "MemrelI";
val MemrelE = thm "MemrelE";
val Memrel_type = thm "Memrel_type";
val Memrel_mono = thm "Memrel_mono";
val Memrel_0 = thm "Memrel_0";
val Memrel_1 = thm "Memrel_1";
val wf_Memrel = thm "wf_Memrel";
val trans_Memrel = thm "trans_Memrel";
val Transset_Memrel_iff = thm "Transset_Memrel_iff";
val Transset_induct = thm "Transset_induct";
val Ord_induct = thm "Ord_induct";
val trans_induct = thm "trans_induct";
val Ord_linear = thm "Ord_linear";
val Ord_linear_lt = thm "Ord_linear_lt";
val Ord_linear2 = thm "Ord_linear2";
val Ord_linear_le = thm "Ord_linear_le";
val le_imp_not_lt = thm "le_imp_not_lt";
val not_lt_imp_le = thm "not_lt_imp_le";
val Ord_mem_iff_lt = thm "Ord_mem_iff_lt";
val not_lt_iff_le = thm "not_lt_iff_le";
val not_le_iff_lt = thm "not_le_iff_lt";
val Ord_0_le = thm "Ord_0_le";
val Ord_0_lt = thm "Ord_0_lt";
val Ord_0_lt_iff = thm "Ord_0_lt_iff";
val zero_le_succ_iff = thm "zero_le_succ_iff";
val subset_imp_le = thm "subset_imp_le";
val le_imp_subset = thm "le_imp_subset";
val le_subset_iff = thm "le_subset_iff";
val le_succ_iff = thm "le_succ_iff";
val all_lt_imp_le = thm "all_lt_imp_le";
val lt_trans1 = thm "lt_trans1";
val lt_trans2 = thm "lt_trans2";
val le_trans = thm "le_trans";
val succ_leI = thm "succ_leI";
val succ_leE = thm "succ_leE";
val succ_le_iff = thm "succ_le_iff";
val succ_le_imp_le = thm "succ_le_imp_le";
val lt_subset_trans = thm "lt_subset_trans";
val Un_upper1_le = thm "Un_upper1_le";
val Un_upper2_le = thm "Un_upper2_le";
val Un_least_lt = thm "Un_least_lt";
val Un_least_lt_iff = thm "Un_least_lt_iff";
val Un_least_mem_iff = thm "Un_least_mem_iff";
val Int_greatest_lt = thm "Int_greatest_lt";
val Ord_Union = thm "Ord_Union";
val Ord_UN = thm "Ord_UN";
val UN_least_le = thm "UN_least_le";
val UN_succ_least_lt = thm "UN_succ_least_lt";
val UN_upper_le = thm "UN_upper_le";
val le_implies_UN_le_UN = thm "le_implies_UN_le_UN";
val Ord_equality = thm "Ord_equality";
val Ord_Union_subset = thm "Ord_Union_subset";
val Limit_Union_eq = thm "Limit_Union_eq";
val Limit_is_Ord = thm "Limit_is_Ord";
val Limit_has_0 = thm "Limit_has_0";
val Limit_has_succ = thm "Limit_has_succ";
val non_succ_LimitI = thm "non_succ_LimitI";
val succ_LimitE = thm "succ_LimitE";
val not_succ_Limit = thm "not_succ_Limit";
val Limit_le_succD = thm "Limit_le_succD";
val Ord_cases_disj = thm "Ord_cases_disj";
val Ord_cases = thm "Ord_cases";
val trans_induct3 = thm "trans_induct3";
*}

end
