(*  Title       : Filter.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*) 

header{*Filters and Ultrafilters*}

theory Filter = Zorn:

constdefs

  is_Filter       :: "['a set set,'a set] => bool"
  "is_Filter F S == (F <= Pow(S) & S \<in> F & {} ~: F &
                   (\<forall>u \<in> F. \<forall>v \<in> F. u Int v \<in> F) &
                   (\<forall>u v. u \<in> F & u <= v & v <= S --> v \<in> F))" 

  Filter          :: "'a set => 'a set set set"
  "Filter S == {X. is_Filter X S}"
 
  (* free filter does not contain any finite set *)

  Freefilter      :: "'a set => 'a set set set"
  "Freefilter S == {X. X \<in> Filter S & (\<forall>x \<in> X. ~ finite x)}"

  Ultrafilter     :: "'a set => 'a set set set"
  "Ultrafilter S == {X. X \<in> Filter S & (\<forall>A \<in> Pow(S). A \<in> X | S - A \<in> X)}"

  FreeUltrafilter :: "'a set => 'a set set set"
  "FreeUltrafilter S == {X. X \<in> Ultrafilter S & (\<forall>x \<in> X. ~ finite x)}" 

  (* A locale makes proof of Ultrafilter Theorem more modular *)
locale (open) UFT = 
  fixes frechet      :: "'a set => 'a set set"
    and superfrechet :: "'a set => 'a set set set"
  assumes not_finite_UNIV:  "~finite (UNIV :: 'a set)"
  defines frechet_def:  
		"frechet S == {A. finite (S - A)}"
      and superfrechet_def:
		"superfrechet S == {G.  G \<in> Filter S & frechet S <= G}"


(*------------------------------------------------------------------
      Properties of Filters and Freefilters - 
      rules for intro, destruction etc.
 ------------------------------------------------------------------*)

lemma is_FilterD1: "is_Filter X S ==> X <= Pow(S)"
apply (simp add: is_Filter_def)
done

lemma is_FilterD2: "is_Filter X S ==> X ~= {}"
apply (auto simp add: is_Filter_def)
done

lemma is_FilterD3: "is_Filter X S ==> {} ~: X"
apply (simp add: is_Filter_def)
done

lemma mem_FiltersetI: "is_Filter X S ==> X \<in> Filter S"
apply (simp add: Filter_def)
done

lemma mem_FiltersetD: "X \<in> Filter S ==> is_Filter X S"
apply (simp add: Filter_def)
done

lemma Filter_empty_not_mem: "X \<in> Filter S ==> {} ~: X"
apply (erule mem_FiltersetD [THEN is_FilterD3])
done

lemmas Filter_empty_not_memE = Filter_empty_not_mem [THEN notE, standard]

lemma mem_FiltersetD1: "[| X \<in> Filter S; A \<in> X; B \<in> X |] ==> A Int B \<in> X"
apply (unfold Filter_def is_Filter_def)
apply blast
done

lemma mem_FiltersetD2: "[| X \<in> Filter S; A \<in> X; A <= B; B <= S|] ==> B \<in> X"
apply (unfold Filter_def is_Filter_def)
apply blast
done

lemma mem_FiltersetD3: "[| X \<in> Filter S; A \<in> X |] ==> A \<in> Pow S"
apply (unfold Filter_def is_Filter_def)
apply blast
done

lemma mem_FiltersetD4: "X \<in> Filter S  ==> S \<in> X"
apply (unfold Filter_def is_Filter_def)
apply blast
done

lemma is_FilterI: 
      "[| X <= Pow(S); 
               S \<in> X;  
               X ~= {};  
               {} ~: X;  
               \<forall>u \<in> X. \<forall>v \<in> X. u Int v \<in> X;  
               \<forall>u v. u \<in> X & u<=v & v<=S --> v \<in> X  
            |] ==> is_Filter X S"
apply (unfold is_Filter_def)
apply blast
done

lemma mem_FiltersetI2: "[| X <= Pow(S); 
               S \<in> X;  
               X ~= {};  
               {} ~: X;  
               \<forall>u \<in> X. \<forall>v \<in> X. u Int v \<in> X;  
               \<forall>u v. u \<in> X & u<=v & v<=S --> v \<in> X  
            |] ==> X \<in> Filter S"
by (blast intro: mem_FiltersetI is_FilterI)

lemma is_FilterE_lemma: 
      "is_Filter X S ==> X <= Pow(S) &  
                           S \<in> X &  
                           X ~= {} &  
                           {} ~: X  &  
                           (\<forall>u \<in> X. \<forall>v \<in> X. u Int v \<in> X) &  
                           (\<forall>u v. u \<in> X & u <= v & v<=S --> v \<in> X)"
apply (unfold is_Filter_def)
apply fast
done

lemma memFiltersetE_lemma: 
      "X \<in> Filter S ==> X <= Pow(S) & 
                           S \<in> X &  
                           X ~= {} &  
                           {} ~: X  &  
                           (\<forall>u \<in> X. \<forall>v \<in> X. u Int v \<in> X) &  
                           (\<forall>u v. u \<in> X & u <= v & v<=S --> v \<in> X)"
by (erule mem_FiltersetD [THEN is_FilterE_lemma])

lemma Freefilter_Filter: "X \<in> Freefilter S ==> X \<in> Filter S"
apply (simp add: Filter_def Freefilter_def)
done

lemma mem_Freefilter_not_finite: "X \<in> Freefilter S ==> \<forall>y \<in> X. ~finite(y)"
apply (simp add: Freefilter_def)
done

lemma mem_FreefiltersetD1: "[| X \<in> Freefilter S; x \<in> X |] ==> ~ finite x"
apply (blast dest!: mem_Freefilter_not_finite)
done

lemmas mem_FreefiltersetE1 = mem_FreefiltersetD1 [THEN notE, standard]

lemma mem_FreefiltersetD2: "[| X \<in> Freefilter S; finite x|] ==> x ~: X"
apply (blast dest!: mem_Freefilter_not_finite)
done

lemma mem_FreefiltersetI1: 
      "[| X \<in> Filter S; \<forall>x. ~(x \<in> X & finite x) |] ==> X \<in> Freefilter S"
by (simp add: Freefilter_def)

lemma mem_FreefiltersetI2: 
      "[| X \<in> Filter S; \<forall>x. (x ~: X | ~ finite x) |] ==> X \<in> Freefilter S"
by (simp add: Freefilter_def)

lemma Filter_Int_not_empty: "[| X \<in> Filter S; A \<in> X; B \<in> X |] ==> A Int B ~= {}"
apply (frule_tac A = "A" and B = "B" in mem_FiltersetD1)
apply (auto dest!: Filter_empty_not_mem)
done

lemmas Filter_Int_not_emptyE = Filter_Int_not_empty [THEN notE, standard]

subsection{*Ultrafilters and Free Ultrafilters*}

lemma Ultrafilter_Filter: "X \<in> Ultrafilter S ==> X \<in> Filter S"
apply (simp add: Ultrafilter_def)
done

lemma mem_UltrafiltersetD2: 
      "X \<in> Ultrafilter S ==> \<forall>A \<in> Pow(S). A \<in> X | S - A \<in> X"
by (auto simp add: Ultrafilter_def)

lemma mem_UltrafiltersetD3: 
      "[|X \<in> Ultrafilter S; A <= S; A ~: X |] ==> S - A \<in> X"
by (auto simp add: Ultrafilter_def)

lemma mem_UltrafiltersetD4: 
      "[|X \<in> Ultrafilter S; A <= S; S - A ~: X |] ==> A \<in> X"
by (auto simp add: Ultrafilter_def)

lemma mem_UltrafiltersetI: 
     "[| X \<in> Filter S;  
         \<forall>A \<in> Pow(S). A \<in> X | S - A \<in> X |] ==> X \<in> Ultrafilter S"
by (simp add: Ultrafilter_def)

lemma FreeUltrafilter_Ultrafilter: 
     "X \<in> FreeUltrafilter S ==> X \<in> Ultrafilter S"
by (auto simp add: Ultrafilter_def FreeUltrafilter_def)

lemma mem_FreeUltrafilter_not_finite: 
     "X \<in> FreeUltrafilter S ==> \<forall>y \<in> X. ~finite(y)"
by (simp add: FreeUltrafilter_def)

lemma mem_FreeUltrafiltersetD1: "[| X \<in> FreeUltrafilter S; x \<in> X |] ==> ~ finite x"
apply (blast dest!: mem_FreeUltrafilter_not_finite)
done

lemmas mem_FreeUltrafiltersetE1 = mem_FreeUltrafiltersetD1 [THEN notE, standard]

lemma mem_FreeUltrafiltersetD2: "[| X \<in> FreeUltrafilter S; finite x|] ==> x ~: X"
apply (blast dest!: mem_FreeUltrafilter_not_finite)
done

lemma mem_FreeUltrafiltersetI1: 
      "[| X \<in> Ultrafilter S;  
          \<forall>x. ~(x \<in> X & finite x) |] ==> X \<in> FreeUltrafilter S"
by (simp add: FreeUltrafilter_def)

lemma mem_FreeUltrafiltersetI2: 
      "[| X \<in> Ultrafilter S;  
          \<forall>x. (x ~: X | ~ finite x) |] ==> X \<in> FreeUltrafilter S"
by (simp add: FreeUltrafilter_def)

lemma FreeUltrafilter_iff: 
     "(X \<in> FreeUltrafilter S) = (X \<in> Freefilter S & (\<forall>x \<in> Pow(S). x \<in> X | S - x \<in> X))"
by (auto simp add: FreeUltrafilter_def Freefilter_def Ultrafilter_def)


(*-------------------------------------------------------------------
   A Filter F on S is an ultrafilter iff it is a maximal filter 
   i.e. whenever G is a filter on I and F <= F then F = G
 --------------------------------------------------------------------*)
(*---------------------------------------------------------------------
  lemmas that shows existence of an extension to what was assumed to
  be a maximal filter. Will be used to derive contradiction in proof of
  property of ultrafilter 
 ---------------------------------------------------------------------*)
lemma lemma_set_extend: "[| F ~= {}; A <= S |] ==> \<exists>x. x \<in> {X. X <= S & (\<exists>f \<in> F. A Int f <= X)}"
apply blast
done

lemma lemma_set_not_empty: "a \<in> X ==> X ~= {}"
apply (safe)
done

lemma lemma_empty_Int_subset_Compl: "x Int F <= {} ==> F <= - x"
apply blast
done

lemma mem_Filterset_disjI: 
      "[| F \<in> Filter S; A ~: F; A <= S|]  
           ==> \<forall>B. B ~: F | ~ B <= A"
apply (unfold Filter_def is_Filter_def)
apply blast
done

lemma Ultrafilter_max_Filter: "F \<in> Ultrafilter S ==>  
          (F \<in> Filter S & (\<forall>G \<in> Filter S. F <= G --> F = G))"
apply (auto simp add: Ultrafilter_def)
apply (drule_tac x = "x" in bspec)
apply (erule mem_FiltersetD3 , assumption)
apply (safe)
apply (drule subsetD , assumption)
apply (blast dest!: Filter_Int_not_empty)
done


(*--------------------------------------------------------------------------------
     This is a very long and tedious proof; need to break it into parts.
     Have proof that {X. X <= S & (\<exists>f \<in> F. A Int f <= X)} is a filter as 
     a lemma
--------------------------------------------------------------------------------*)
lemma max_Filter_Ultrafilter: 
      "[| F \<in> Filter S;  
          \<forall>G \<in> Filter S. F <= G --> F = G |] ==> F \<in> Ultrafilter S"
apply (simp add: Ultrafilter_def)
apply (safe)
apply (rule ccontr)
apply (frule mem_FiltersetD [THEN is_FilterD2])
apply (frule_tac x = "{X. X <= S & (\<exists>f \<in> F. A Int f <= X) }" in bspec)
apply (rule mem_FiltersetI2) 
apply (blast intro: elim:); 
apply (simp add: ); 
apply (blast dest: mem_FiltersetD3)
apply (erule lemma_set_extend [THEN exE])
apply (assumption , erule lemma_set_not_empty)
txt{*First we prove @{term "{} \<notin> {X. X \<subseteq> S \<and> (\<exists>f\<in>F. A \<inter> f \<subseteq> X)}"}*}
   apply (clarify ); 
   apply (drule lemma_empty_Int_subset_Compl)
   apply (frule mem_Filterset_disjI) 
   apply assumption; 
   apply (blast intro: elim:); 
   apply (fast dest: mem_FiltersetD3 elim:) 
txt{*Next case: @{term "u \<inter> v"} is an element*}
  apply (intro ballI) 
apply (simp add: ); 
  apply (rule conjI, blast) 
apply (clarify ); 
  apply (rule_tac x = "f Int fa" in bexI)
   apply (fast intro: elim:); 
  apply (blast dest: mem_FiltersetD1 elim:)
 apply force;
apply (blast dest: mem_FiltersetD3 elim:) 
done

lemma Ultrafilter_iff: "(F \<in> Ultrafilter S) = (F \<in> Filter S & (\<forall>G \<in> Filter S. F <= G --> F = G))"
apply (blast intro!: Ultrafilter_max_Filter max_Filter_Ultrafilter)
done


subsection{* A Few Properties of Freefilters*}

lemma lemma_Compl_cancel_eq: "F1 Int F2 = ((F1 Int Y) Int F2) Un ((F2 Int (- Y)) Int F1)"
apply auto
done

lemma finite_IntI1: "finite X ==> finite (X Int Y)"
apply (erule Int_lower1 [THEN finite_subset])
done

lemma finite_IntI2: "finite Y ==> finite (X Int Y)"
apply (erule Int_lower2 [THEN finite_subset])
done

lemma finite_Int_Compl_cancel: "[| finite (F1 Int Y);  
                  finite (F2 Int (- Y))  
               |] ==> finite (F1 Int F2)"
apply (rule_tac Y1 = "Y" in lemma_Compl_cancel_eq [THEN ssubst])
apply (rule finite_UnI)
apply (auto intro!: finite_IntI1 finite_IntI2)
done

lemma Freefilter_lemma_not_finite: "U \<in> Freefilter S  ==>  
          ~ (\<exists>f1 \<in> U. \<exists>f2 \<in> U. finite (f1 Int x)  
                             & finite (f2 Int (- x)))"
apply (safe)
apply (frule_tac A = "f1" and B = "f2" in Freefilter_Filter [THEN mem_FiltersetD1])
apply (drule_tac [3] x = "f1 Int f2" in mem_FreefiltersetD1)
apply (drule_tac [4] finite_Int_Compl_cancel)
apply auto
done

(* the lemmas below follow *)
lemma Freefilter_Compl_not_finite_disjI: "U \<in> Freefilter S ==>  
           \<forall>f \<in> U. ~ finite (f Int x) | ~finite (f Int (- x))"
by (blast dest!: Freefilter_lemma_not_finite bspec)

lemma Freefilter_Compl_not_finite_disjI2: "U \<in> Freefilter S ==> (\<forall>f \<in> U. ~ finite (f Int x)) | (\<forall>f \<in> U. ~finite (f Int (- x)))"
apply (blast dest!: Freefilter_lemma_not_finite bspec)
done

lemma cofinite_Filter: "~ finite (UNIV:: 'a set) ==> {A:: 'a set. finite (- A)} \<in> Filter UNIV"
apply (rule mem_FiltersetI2)
apply (auto simp del: Collect_empty_eq)
apply (erule_tac c = "UNIV" in equalityCE)
apply auto
apply (erule Compl_anti_mono [THEN finite_subset])
apply assumption
done

lemma not_finite_UNIV_disjI: "~finite(UNIV :: 'a set) ==> ~finite (X :: 'a set) | ~finite (- X)" 
apply (drule_tac A1 = "X" in Compl_partition [THEN ssubst])
apply simp
done

lemma not_finite_UNIV_Compl: "[| ~finite(UNIV :: 'a set); finite (X :: 'a set) |] ==>  ~finite (- X)"
apply (drule_tac X = "X" in not_finite_UNIV_disjI)
apply blast
done

lemma mem_cofinite_Filter_not_finite:
     "~ finite (UNIV:: 'a set) 
      ==> \<forall>X \<in> {A:: 'a set. finite (- A)}. ~ finite X"
by (auto dest: not_finite_UNIV_disjI)

lemma cofinite_Freefilter:
    "~ finite (UNIV:: 'a set) ==> {A:: 'a set. finite (- A)} \<in> Freefilter UNIV"
apply (rule mem_FreefiltersetI2)
apply (rule cofinite_Filter , assumption)
apply (blast dest!: mem_cofinite_Filter_not_finite)
done

(*????Set.thy*)
lemma UNIV_diff_Compl [simp]: "UNIV - x = - x"
apply auto
done

lemma FreeUltrafilter_contains_cofinite_set: 
     "[| ~finite(UNIV :: 'a set); (U :: 'a set set): FreeUltrafilter UNIV 
          |] ==> {X. finite(- X)} <= U"
by (auto simp add: Ultrafilter_def FreeUltrafilter_def)

(*--------------------------------------------------------------------
   We prove: 1. Existence of maximal filter i.e. ultrafilter
             2. Freeness property i.e ultrafilter is free
             Use a locale to prove various lemmas and then 
             export main result: The Ultrafilter Theorem
 -------------------------------------------------------------------*)

lemma (in UFT) chain_Un_subset_Pow: 
   "!!(c :: 'a set set set). c \<in> chain (superfrechet S) ==>  Union c <= Pow S"
apply (simp add: chain_def superfrechet_def frechet_def)
apply (blast dest: mem_FiltersetD3 elim:) 
done

lemma (in UFT) mem_chain_psubset_empty: 
          "!!(c :: 'a set set set). c: chain (superfrechet S)  
          ==> !x: c. {} < x"
by (auto simp add: chain_def Filter_def is_Filter_def superfrechet_def frechet_def)

lemma (in UFT) chain_Un_not_empty: "!!(c :: 'a set set set).  
             [| c: chain (superfrechet S); 
                c ~= {} |] 
             ==> Union(c) ~= {}"
apply (drule mem_chain_psubset_empty)
apply (safe)
apply (drule bspec , assumption)
apply (auto dest: Union_upper bspec simp add: psubset_def)
done

lemma (in UFT) Filter_empty_not_mem_Un: 
       "!!(c :: 'a set set set). c \<in> chain (superfrechet S) ==> {} ~: Union(c)"
by (auto simp add: is_Filter_def Filter_def chain_def superfrechet_def)

lemma (in UFT) Filter_Un_Int: "c \<in> chain (superfrechet S)  
          ==> \<forall>u \<in> Union(c). \<forall>v \<in> Union(c). u Int v \<in> Union(c)"
apply (safe)
apply (frule_tac x = "X" and y = "Xa" in chainD)
apply (assumption)+
apply (drule chainD2)
apply (erule disjE)
 apply (rule_tac [2] X = "X" in UnionI)
  apply (rule_tac X = "Xa" in UnionI)
apply (auto intro: mem_FiltersetD1 simp add: superfrechet_def)
done

lemma (in UFT) Filter_Un_subset: "c \<in> chain (superfrechet S)  
          ==> \<forall>u v. u \<in> Union(c) &  
                  (u :: 'a set) <= v & v <= S --> v \<in> Union(c)"
apply (safe)
apply (drule chainD2)
apply (drule subsetD , assumption)
apply (rule UnionI , assumption)
apply (auto intro: mem_FiltersetD2 simp add: superfrechet_def)
done

lemma (in UFT) lemma_mem_chain_Filter:
      "!!(c :: 'a set set set).  
             [| c \<in> chain (superfrechet S); 
                x \<in> c  
             |] ==> x \<in> Filter S"
by (auto simp add: chain_def superfrechet_def)

lemma (in UFT) lemma_mem_chain_frechet_subset: 
     "!!(c :: 'a set set set).  
             [| c \<in> chain (superfrechet S); 
                x \<in> c  
             |] ==> frechet S <= x"
by (auto simp add: chain_def superfrechet_def)

lemma (in UFT) Un_chain_mem_cofinite_Filter_set: "!!(c :: 'a set set set).  
          [| c ~= {};  
             c \<in> chain (superfrechet (UNIV :: 'a set)) 
          |] ==> Union c \<in> superfrechet (UNIV)"
apply (simp (no_asm) add: superfrechet_def frechet_def)
apply (safe)
apply (rule mem_FiltersetI2)
apply (erule chain_Un_subset_Pow)
apply (rule UnionI , assumption)
apply (erule lemma_mem_chain_Filter [THEN mem_FiltersetD4] , assumption)
apply (erule chain_Un_not_empty)
apply (erule_tac [2] Filter_empty_not_mem_Un)
apply (erule_tac [2] Filter_Un_Int)
apply (erule_tac [2] Filter_Un_subset)
apply (subgoal_tac [2] "xa \<in> frechet (UNIV) ")
apply (blast intro: elim:); 
apply (rule UnionI)
apply assumption; 
apply (rule lemma_mem_chain_frechet_subset [THEN subsetD])
apply (auto simp add: frechet_def)
done

lemma (in UFT) max_cofinite_Filter_Ex: "\<exists>U \<in> superfrechet (UNIV).  
                \<forall>G \<in> superfrechet (UNIV). U <= G --> U = G"
apply (rule Zorn_Lemma2)
apply (insert not_finite_UNIV [THEN cofinite_Filter])
apply (safe)
apply (rule_tac Q = "c={}" in excluded_middle [THEN disjE])
apply (rule_tac x = "Union c" in bexI , blast)
apply (rule Un_chain_mem_cofinite_Filter_set);
apply (auto simp add: superfrechet_def frechet_def)
done

lemma (in UFT) max_cofinite_Freefilter_Ex: "\<exists>U \<in> superfrechet UNIV. ( 
                \<forall>G \<in> superfrechet UNIV. U <= G --> U = G)   
                              & (\<forall>x \<in> U. ~finite x)"
apply (insert not_finite_UNIV [THEN UFT.max_cofinite_Filter_Ex]);
apply (safe)
apply (rule_tac x = "U" in bexI)
apply (auto simp add: superfrechet_def frechet_def)
apply (drule_tac c = "- x" in subsetD)
apply (simp (no_asm_simp))
apply (frule_tac A = "x" and B = "- x" in mem_FiltersetD1)
apply (drule_tac [3] Filter_empty_not_mem)
apply (auto ); 
done

text{*There exists a free ultrafilter on any infinite set*}

theorem (in UFT) FreeUltrafilter_ex: "\<exists>U. U \<in> FreeUltrafilter (UNIV :: 'a set)"
apply (simp add: FreeUltrafilter_def)
apply (insert not_finite_UNIV [THEN UFT.max_cofinite_Freefilter_Ex])
apply (simp add: superfrechet_def Ultrafilter_iff frechet_def)
apply (safe)
apply (rule_tac x = "U" in exI)
apply (safe)
apply blast
done

theorems FreeUltrafilter_Ex = UFT.FreeUltrafilter_ex

end
