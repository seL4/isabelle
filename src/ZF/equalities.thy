(*  Title:      ZF/equalities
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

*)

header{*Basic Equalities and Inclusions*}

theory equalities = pair:

text{*These cover union, intersection, converse, domain, range, etc.  Philippe
de Groote proved many of the inclusions.*}

lemma in_mono: "A<=B ==> x:A --> x:B"
by blast

lemma the_eq_0 [simp]: "(THE x. False) = 0"
by (blast intro: the_0)

subsection{*Bounded Quantifiers*}
text {* \medskip 

  The following are not added to the default simpset because
  (a) they duplicate the body and (b) there are no similar rules for @{text Int}.*}

lemma ball_Un: "(\<forall>x \<in> A\<union>B. P(x)) <-> (\<forall>x \<in> A. P(x)) & (\<forall>x \<in> B. P(x))";
  by blast

lemma bex_Un: "(\<exists>x \<in> A\<union>B. P(x)) <-> (\<exists>x \<in> A. P(x)) | (\<exists>x \<in> B. P(x))";
  by blast

lemma ball_UN: "(\<forall>z \<in> (\<Union>x\<in>A. B(x)). P(z)) <-> (\<forall>x\<in>A. \<forall>z \<in> B(x). P(z))"
  by blast

lemma bex_UN: "(\<exists>z \<in> (\<Union>x\<in>A. B(x)). P(z)) <-> (\<exists>x\<in>A. \<exists>z\<in>B(x). P(z))"
  by blast

subsection{*Converse of a Relation*}

lemma converse_iff [simp]: "<a,b>: converse(r) <-> <b,a>:r"
by (unfold converse_def, blast)

lemma converseI [intro!]: "<a,b>:r ==> <b,a>:converse(r)"
by (unfold converse_def, blast)

lemma converseD: "<a,b> : converse(r) ==> <b,a> : r"
by (unfold converse_def, blast)

lemma converseE [elim!]:
    "[| yx : converse(r);   
        !!x y. [| yx=<y,x>;  <x,y>:r |] ==> P |]
     ==> P"
by (unfold converse_def, blast) 

lemma converse_converse: "r<=Sigma(A,B) ==> converse(converse(r)) = r"
by blast

lemma converse_type: "r<=A*B ==> converse(r)<=B*A"
by blast

lemma converse_prod [simp]: "converse(A*B) = B*A"
by blast

lemma converse_empty [simp]: "converse(0) = 0"
by blast

lemma converse_subset_iff:
     "A <= Sigma(X,Y) ==> converse(A) <= converse(B) <-> A <= B"
by blast


subsection{*Finite Set Constructions Using @{term cons}*}

lemma cons_subsetI: "[| a:C; B<=C |] ==> cons(a,B) <= C"
by blast

lemma subset_consI: "B <= cons(a,B)"
by blast

lemma cons_subset_iff [iff]: "cons(a,B)<=C <-> a:C & B<=C"
by blast

(*A safe special case of subset elimination, adding no new variables 
  [| cons(a,B) <= C; [| a : C; B <= C |] ==> R |] ==> R *)
lemmas cons_subsetE = cons_subset_iff [THEN iffD1, THEN conjE, standard]

lemma subset_empty_iff: "A<=0 <-> A=0"
by blast

lemma subset_cons_iff: "C<=cons(a,B) <-> C<=B | (a:C & C-{a} <= B)"
by blast

(* cons_def refers to Upair; reversing the equality LOOPS in rewriting!*)
lemma cons_eq: "{a} Un B = cons(a,B)"
by blast

lemma cons_commute: "cons(a, cons(b, C)) = cons(b, cons(a, C))"
by blast

lemma cons_absorb: "a: B ==> cons(a,B) = B"
by blast

lemma cons_Diff: "a: B ==> cons(a, B-{a}) = B"
by blast

lemma Diff_cons_eq: "cons(a,B) - C = (if a\<in>C then B-C else cons(a,B-C))" 
by auto

lemma equal_singleton [rule_format]: "[| a: C;  \<forall>y\<in>C. y=b |] ==> C = {b}"
by blast

lemma [simp]: "cons(a,cons(a,B)) = cons(a,B)"
by blast

(** singletons **)

lemma singleton_subsetI: "a:C ==> {a} <= C"
by blast

lemma singleton_subsetD: "{a} <= C  ==>  a:C"
by blast


(** succ **)

lemma subset_succI: "i <= succ(i)"
by blast

(*But if j is an ordinal or is transitive, then i:j implies i<=j! 
  See ordinal/Ord_succ_subsetI*)
lemma succ_subsetI: "[| i:j;  i<=j |] ==> succ(i)<=j"
by (unfold succ_def, blast)

lemma succ_subsetE:
    "[| succ(i) <= j;  [| i:j;  i<=j |] ==> P |] ==> P"
by (unfold succ_def, blast) 

lemma succ_subset_iff: "succ(a) <= B <-> (a <= B & a : B)"
by (unfold succ_def, blast)


subsection{*Binary Intersection*}

(** Intersection is the greatest lower bound of two sets **)

lemma Int_subset_iff: "C <= A Int B <-> C <= A & C <= B"
by blast

lemma Int_lower1: "A Int B <= A"
by blast

lemma Int_lower2: "A Int B <= B"
by blast

lemma Int_greatest: "[| C<=A;  C<=B |] ==> C <= A Int B"
by blast

lemma Int_cons: "cons(a,B) Int C <= cons(a, B Int C)"
by blast

lemma Int_absorb [simp]: "A Int A = A"
by blast

lemma Int_left_absorb: "A Int (A Int B) = A Int B"
by blast

lemma Int_commute: "A Int B = B Int A"
by blast

lemma Int_left_commute: "A Int (B Int C) = B Int (A Int C)"
by blast

lemma Int_assoc: "(A Int B) Int C  =  A Int (B Int C)"
by blast

(*Intersection is an AC-operator*)
lemmas Int_ac= Int_assoc Int_left_absorb Int_commute Int_left_commute

lemma Int_absorb1: "B \<subseteq> A ==> A \<inter> B = B"
  by blast

lemma Int_absorb2: "A \<subseteq> B ==> A \<inter> B = A"
  by blast

lemma Int_Un_distrib: "A Int (B Un C) = (A Int B) Un (A Int C)"
by blast

lemma Int_Un_distrib2: "(B Un C) Int A = (B Int A) Un (C Int A)"
by blast

lemma subset_Int_iff: "A<=B <-> A Int B = A"
by (blast elim!: equalityE)

lemma subset_Int_iff2: "A<=B <-> B Int A = A"
by (blast elim!: equalityE)

lemma Int_Diff_eq: "C<=A ==> (A-B) Int C = C-B"
by blast

lemma Int_cons_left:
     "cons(a,A) Int B = (if a : B then cons(a, A Int B) else A Int B)"
by auto

lemma Int_cons_right:
     "A Int cons(a, B) = (if a : A then cons(a, A Int B) else A Int B)"
by auto

lemma cons_Int_distrib: "cons(x, A \<inter> B) = cons(x, A) \<inter> cons(x, B)"
by auto

subsection{*Binary Union*}

(** Union is the least upper bound of two sets *)

lemma Un_subset_iff: "A Un B <= C <-> A <= C & B <= C"
by blast

lemma Un_upper1: "A <= A Un B"
by blast

lemma Un_upper2: "B <= A Un B"
by blast

lemma Un_least: "[| A<=C;  B<=C |] ==> A Un B <= C"
by blast

lemma Un_cons: "cons(a,B) Un C = cons(a, B Un C)"
by blast

lemma Un_absorb [simp]: "A Un A = A"
by blast

lemma Un_left_absorb: "A Un (A Un B) = A Un B"
by blast

lemma Un_commute: "A Un B = B Un A"
by blast

lemma Un_left_commute: "A Un (B Un C) = B Un (A Un C)"
by blast

lemma Un_assoc: "(A Un B) Un C  =  A Un (B Un C)"
by blast

(*Union is an AC-operator*)
lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute

lemma Un_absorb1: "A \<subseteq> B ==> A \<union> B = B"
  by blast

lemma Un_absorb2: "B \<subseteq> A ==> A \<union> B = A"
  by blast

lemma Un_Int_distrib: "(A Int B) Un C  =  (A Un C) Int (B Un C)"
by blast

lemma subset_Un_iff: "A<=B <-> A Un B = B"
by (blast elim!: equalityE)

lemma subset_Un_iff2: "A<=B <-> B Un A = B"
by (blast elim!: equalityE)

lemma Un_empty [iff]: "(A Un B = 0) <-> (A = 0 & B = 0)"
by blast

lemma Un_eq_Union: "A Un B = Union({A, B})"
by blast

subsection{*Set Difference*}

lemma Diff_subset: "A-B <= A"
by blast

lemma Diff_contains: "[| C<=A;  C Int B = 0 |] ==> C <= A-B"
by blast

lemma subset_Diff_cons_iff: "B <= A - cons(c,C)  <->  B<=A-C & c ~: B"
by blast

lemma Diff_cancel: "A - A = 0"
by blast

lemma Diff_triv: "A  Int B = 0 ==> A - B = A"
by blast

lemma empty_Diff [simp]: "0 - A = 0"
by blast

lemma Diff_0 [simp]: "A - 0 = A"
by blast

lemma Diff_eq_0_iff: "A - B = 0 <-> A <= B"
by (blast elim: equalityE)

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
lemma Diff_cons: "A - cons(a,B) = A - B - {a}"
by blast

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
lemma Diff_cons2: "A - cons(a,B) = A - {a} - B"
by blast

lemma Diff_disjoint: "A Int (B-A) = 0"
by blast

lemma Diff_partition: "A<=B ==> A Un (B-A) = B"
by blast

lemma subset_Un_Diff: "A <= B Un (A - B)"
by blast

lemma double_complement: "[| A<=B; B<=C |] ==> B-(C-A) = A"
by blast

lemma double_complement_Un: "(A Un B) - (B-A) = A"
by blast

lemma Un_Int_crazy: 
 "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)"
apply blast
done

lemma Diff_Un: "A - (B Un C) = (A-B) Int (A-C)"
by blast

lemma Diff_Int: "A - (B Int C) = (A-B) Un (A-C)"
by blast

lemma Un_Diff: "(A Un B) - C = (A - C) Un (B - C)"
by blast

lemma Int_Diff: "(A Int B) - C = A Int (B - C)"
by blast

lemma Diff_Int_distrib: "C Int (A-B) = (C Int A) - (C Int B)"
by blast

lemma Diff_Int_distrib2: "(A-B) Int C = (A Int C) - (B Int C)"
by blast

(*Halmos, Naive Set Theory, page 16.*)
lemma Un_Int_assoc_iff: "(A Int B) Un C = A Int (B Un C)  <->  C<=A"
by (blast elim!: equalityE)


subsection{*Big Union and Intersection*}

(** Big Union is the least upper bound of a set  **)

lemma Union_subset_iff: "Union(A) <= C <-> (\<forall>x\<in>A. x <= C)"
by blast

lemma Union_upper: "B:A ==> B <= Union(A)"
by blast

lemma Union_least: "[| !!x. x:A ==> x<=C |] ==> Union(A) <= C"
by blast

lemma Union_cons [simp]: "Union(cons(a,B)) = a Un Union(B)"
by blast

lemma Union_Un_distrib: "Union(A Un B) = Union(A) Un Union(B)"
by blast

lemma Union_Int_subset: "Union(A Int B) <= Union(A) Int Union(B)"
by blast

lemma Union_disjoint: "Union(C) Int A = 0 <-> (\<forall>B\<in>C. B Int A = 0)"
by (blast elim!: equalityE)

lemma Union_empty_iff: "Union(A) = 0 <-> (\<forall>B\<in>A. B=0)"
by blast

lemma Int_Union2: "Union(B) Int A = (UN C:B. C Int A)"
by blast

(** Big Intersection is the greatest lower bound of a nonempty set **)

lemma Inter_subset_iff: "a: A  ==>  C <= Inter(A) <-> (\<forall>x\<in>A. C <= x)"
by blast

lemma Inter_lower: "B:A ==> Inter(A) <= B"
by blast

lemma Inter_greatest: "[| a:A;  !!x. x:A ==> C<=x |] ==> C <= Inter(A)"
by blast

(** Intersection of a family of sets  **)

lemma INT_lower: "x:A ==> (\<Inter>x\<in>A. B(x)) <= B(x)"
by blast

lemma INT_greatest: 
    "[| a:A;  !!x. x:A ==> C<=B(x) |] ==> C <= (\<Inter>x\<in>A. B(x))"
by blast 

lemma Inter_0: "Inter(0) = 0"
by (unfold Inter_def, blast)

lemma Inter_Un_subset:
     "[| z:A; z:B |] ==> Inter(A) Un Inter(B) <= Inter(A Int B)"
by blast

(* A good challenge: Inter is ill-behaved on the empty set *)
lemma Inter_Un_distrib:
     "[| a:A;  b:B |] ==> Inter(A Un B) = Inter(A) Int Inter(B)"
by blast

lemma Union_singleton: "Union({b}) = b"
by blast

lemma Inter_singleton: "Inter({b}) = b"
by blast

lemma Inter_cons [simp]:
     "Inter(cons(a,B)) = (if B=0 then a else a Int Inter(B))"
by force

subsection{*Unions and Intersections of Families*}

lemma subset_UN_iff_eq: "A <= (\<Union>i\<in>I. B(i)) <-> A = (\<Union>i\<in>I. A Int B(i))"
by (blast elim!: equalityE)

lemma UN_subset_iff: "(\<Union>x\<in>A. B(x)) <= C <-> (\<forall>x\<in>A. B(x) <= C)"
by blast

lemma UN_upper: "x:A ==> B(x) <= (\<Union>x\<in>A. B(x))"
by (erule RepFunI [THEN Union_upper])

lemma UN_least: "[| !!x. x:A ==> B(x)<=C |] ==> (\<Union>x\<in>A. B(x)) <= C"
by blast

lemma Union_eq_UN: "Union(A) = (\<Union>x\<in>A. x)"
by blast

lemma Inter_eq_INT: "Inter(A) = (\<Inter>x\<in>A. x)"
by (unfold Inter_def, blast)

lemma UN_0 [simp]: "(\<Union>i\<in>0. A(i)) = 0"
by blast

lemma UN_singleton: "(\<Union>x\<in>A. {x}) = A"
by blast

lemma UN_Un: "(\<Union>i\<in> A Un B. C(i)) = (\<Union>i\<in> A. C(i)) Un (\<Union>i\<in>B. C(i))"
by blast

lemma INT_Un: "(\<Inter>i\<in>I Un J. A(i)) = (if I=0 then \<Inter>j\<in>J. A(j)  
                              else if J=0 then \<Inter>i\<in>I. A(i)  
                              else ((\<Inter>i\<in>I. A(i)) Int  (\<Inter>j\<in>J. A(j))))"
apply simp
apply (blast intro!: equalityI)
done

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B(y)). C(x)) = (\<Union>y\<in>A. \<Union>x\<in> B(y). C(x))"
by blast

(*Halmos, Naive Set Theory, page 35.*)
lemma Int_UN_distrib: "B Int (\<Union>i\<in>I. A(i)) = (\<Union>i\<in>I. B Int A(i))"
by blast

lemma Un_INT_distrib: "i:I ==> B Un (\<Inter>i\<in>I. A(i)) = (\<Inter>i\<in>I. B Un A(i))"
by blast

lemma Int_UN_distrib2:
     "(\<Union>i\<in>I. A(i)) Int (\<Union>j\<in>J. B(j)) = (\<Union>i\<in>I. \<Union>j\<in>J. A(i) Int B(j))"
by blast

lemma Un_INT_distrib2: "[| i:I;  j:J |] ==>  
      (\<Inter>i\<in>I. A(i)) Un (\<Inter>j\<in>J. B(j)) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A(i) Un B(j))"
by blast

lemma UN_constant: "a: A ==> (\<Union>y\<in>A. c) = c"
by blast

lemma INT_constant: "a: A ==> (\<Inter>y\<in>A. c) = c"
by blast

lemma UN_RepFun [simp]: "(\<Union>y\<in> RepFun(A,f). B(y)) = (\<Union>x\<in>A. B(f(x)))"
by blast

lemma INT_RepFun [simp]: "(\<Inter>x\<in>RepFun(A,f). B(x))    = (\<Inter>a\<in>A. B(f(a)))"
by (auto simp add: Inter_def)

lemma INT_Union_eq:
     "0 ~: A ==> (\<Inter>x\<in> Union(A). B(x)) = (\<Inter>y\<in>A. \<Inter>x\<in>y. B(x))"
apply (subgoal_tac "\<forall>x\<in>A. x~=0")
 prefer 2 apply blast
apply (force simp add: Inter_def ball_conj_distrib) 
done

lemma INT_UN_eq:
     "(\<forall>x\<in>A. B(x) ~= 0)  
      ==> (\<Inter>z\<in> (\<Union>x\<in>A. B(x)). C(z)) = (\<Inter>x\<in>A. \<Inter>z\<in> B(x). C(z))"
apply (subst INT_Union_eq, blast)
apply (simp add: Inter_def)
done


(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: 
    Union of a family of unions **)

lemma UN_Un_distrib:
     "(\<Union>i\<in>I. A(i) Un B(i)) = (\<Union>i\<in>I. A(i))  Un  (\<Union>i\<in>I. B(i))"
by blast

lemma INT_Int_distrib:
     "i:I ==> (\<Inter>i\<in>I. A(i) Int B(i)) = (\<Inter>i\<in>I. A(i)) Int (\<Inter>i\<in>I. B(i))"
by blast

lemma UN_Int_subset:
     "(\<Union>z\<in>I Int J. A(z)) <= (\<Union>z\<in>I. A(z)) Int (\<Union>z\<in>J. A(z))"
by blast

(** Devlin, page 12, exercise 5: Complements **)

lemma Diff_UN: "i:I ==> B - (\<Union>i\<in>I. A(i)) = (\<Inter>i\<in>I. B - A(i))"
by blast

lemma Diff_INT: "i:I ==> B - (\<Inter>i\<in>I. A(i)) = (\<Union>i\<in>I. B - A(i))"
by blast

(** Unions and Intersections with General Sum **)

(*Not suitable for rewriting: LOOPS!*)
lemma Sigma_cons1: "Sigma(cons(a,B), C) = ({a}*C(a)) Un Sigma(B,C)"
by blast

(*Not suitable for rewriting: LOOPS!*)
lemma Sigma_cons2: "A * cons(b,B) = A*{b} Un A*B"
by blast

lemma Sigma_succ1: "Sigma(succ(A), B) = ({A}*B(A)) Un Sigma(A,B)"
by blast

lemma Sigma_succ2: "A * succ(B) = A*{B} Un A*B"
by blast

lemma SUM_UN_distrib1:
     "(SUM x:(\<Union>y\<in>A. C(y)). B(x)) = (\<Union>y\<in>A. SUM x:C(y). B(x))"
by blast

lemma SUM_UN_distrib2:
     "(SUM i:I. \<Union>j\<in>J. C(i,j)) = (\<Union>j\<in>J. SUM i:I. C(i,j))"
by blast

lemma SUM_Un_distrib1:
     "(SUM i:I Un J. C(i)) = (SUM i:I. C(i)) Un (SUM j:J. C(j))"
by blast

lemma SUM_Un_distrib2:
     "(SUM i:I. A(i) Un B(i)) = (SUM i:I. A(i)) Un (SUM i:I. B(i))"
by blast

(*First-order version of the above, for rewriting*)
lemma prod_Un_distrib2: "I * (A Un B) = I*A Un I*B"
by (rule SUM_Un_distrib2)

lemma SUM_Int_distrib1:
     "(SUM i:I Int J. C(i)) = (SUM i:I. C(i)) Int (SUM j:J. C(j))"
by blast

lemma SUM_Int_distrib2:
     "(SUM i:I. A(i) Int B(i)) = (SUM i:I. A(i)) Int (SUM i:I. B(i))"
by blast

(*First-order version of the above, for rewriting*)
lemma prod_Int_distrib2: "I * (A Int B) = I*A Int I*B"
by (rule SUM_Int_distrib2)

(*Cf Aczel, Non-Well-Founded Sets, page 115*)
lemma SUM_eq_UN: "(SUM i:I. A(i)) = (\<Union>i\<in>I. {i} * A(i))"
by blast

lemma times_subset_iff:
     "(A'*B' <= A*B) <-> (A' = 0 | B' = 0 | (A'<=A) & (B'<=B))"
by blast

lemma Int_Sigma_eq:
     "(\<Sigma>x \<in> A'. B'(x)) Int (\<Sigma>x \<in> A. B(x)) = (\<Sigma>x \<in> A' Int A. B'(x) Int B(x))"
by blast

(** Domain **)

lemma domain_iff: "a: domain(r) <-> (EX y. <a,y>: r)"
by (unfold domain_def, blast)

lemma domainI [intro]: "<a,b>: r ==> a: domain(r)"
by (unfold domain_def, blast)

lemma domainE [elim!]:
    "[| a : domain(r);  !!y. <a,y>: r ==> P |] ==> P"
by (unfold domain_def, blast)

lemma domain_subset: "domain(Sigma(A,B)) <= A"
by blast

lemma domain_of_prod: "b:B ==> domain(A*B) = A"
by blast

lemma domain_0 [simp]: "domain(0) = 0"
by blast

lemma domain_cons [simp]: "domain(cons(<a,b>,r)) = cons(a, domain(r))"
by blast

lemma domain_Un_eq [simp]: "domain(A Un B) = domain(A) Un domain(B)"
by blast

lemma domain_Int_subset: "domain(A Int B) <= domain(A) Int domain(B)"
by blast

lemma domain_Diff_subset: "domain(A) - domain(B) <= domain(A - B)"
by blast

lemma domain_UN: "domain(\<Union>x\<in>A. B(x)) = (\<Union>x\<in>A. domain(B(x)))"
by blast

lemma domain_Union: "domain(Union(A)) = (\<Union>x\<in>A. domain(x))"
by blast


(** Range **)

lemma rangeI [intro]: "<a,b>: r ==> b : range(r)"
apply (unfold range_def)
apply (erule converseI [THEN domainI])
done

lemma rangeE [elim!]: "[| b : range(r);  !!x. <x,b>: r ==> P |] ==> P"
by (unfold range_def, blast)

lemma range_subset: "range(A*B) <= B"
apply (unfold range_def)
apply (subst converse_prod)
apply (rule domain_subset)
done

lemma range_of_prod: "a:A ==> range(A*B) = B"
by blast

lemma range_0 [simp]: "range(0) = 0"
by blast

lemma range_cons [simp]: "range(cons(<a,b>,r)) = cons(b, range(r))"
by blast

lemma range_Un_eq [simp]: "range(A Un B) = range(A) Un range(B)"
by blast

lemma range_Int_subset: "range(A Int B) <= range(A) Int range(B)"
by blast

lemma range_Diff_subset: "range(A) - range(B) <= range(A - B)"
by blast

lemma domain_converse [simp]: "domain(converse(r)) = range(r)"
by blast

lemma range_converse [simp]: "range(converse(r)) = domain(r)"
by blast


(** Field **)

lemma fieldI1: "<a,b>: r ==> a : field(r)"
by (unfold field_def, blast)

lemma fieldI2: "<a,b>: r ==> b : field(r)"
by (unfold field_def, blast)

lemma fieldCI [intro]: 
    "(~ <c,a>:r ==> <a,b>: r) ==> a : field(r)"
apply (unfold field_def, blast)
done

lemma fieldE [elim!]: 
     "[| a : field(r);   
         !!x. <a,x>: r ==> P;   
         !!x. <x,a>: r ==> P        |] ==> P"
by (unfold field_def, blast)

lemma field_subset: "field(A*B) <= A Un B"
by blast

lemma domain_subset_field: "domain(r) <= field(r)"
apply (unfold field_def)
apply (rule Un_upper1)
done

lemma range_subset_field: "range(r) <= field(r)"
apply (unfold field_def)
apply (rule Un_upper2)
done

lemma domain_times_range: "r <= Sigma(A,B) ==> r <= domain(r)*range(r)"
by blast

lemma field_times_field: "r <= Sigma(A,B) ==> r <= field(r)*field(r)"
by blast

lemma relation_field_times_field: "relation(r) ==> r <= field(r)*field(r)"
by (simp add: relation_def, blast) 

lemma field_of_prod: "field(A*A) = A"
by blast

lemma field_0 [simp]: "field(0) = 0"
by blast

lemma field_cons [simp]: "field(cons(<a,b>,r)) = cons(a, cons(b, field(r)))"
by blast

lemma field_Un_eq [simp]: "field(A Un B) = field(A) Un field(B)"
by blast

lemma field_Int_subset: "field(A Int B) <= field(A) Int field(B)"
by blast

lemma field_Diff_subset: "field(A) - field(B) <= field(A - B)"
by blast

lemma field_converse [simp]: "field(converse(r)) = field(r)"
by blast

(** The Union of a set of relations is a relation -- Lemma for fun_Union **)
lemma rel_Union: "(\<forall>x\<in>S. EX A B. x <= A*B) ==>   
                  Union(S) <= domain(Union(S)) * range(Union(S))"
by blast

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
lemma rel_Un: "[| r <= A*B;  s <= C*D |] ==> (r Un s) <= (A Un C) * (B Un D)"
by blast

lemma domain_Diff_eq: "[| <a,c> : r; c~=b |] ==> domain(r-{<a,b>}) = domain(r)"
by blast

lemma range_Diff_eq: "[| <c,b> : r; c~=a |] ==> range(r-{<a,b>}) = range(r)"
by blast


subsection{*Image of a Set under a Function or Relation*}

lemma image_iff: "b : r``A <-> (\<exists>x\<in>A. <x,b>:r)"
by (unfold image_def, blast)

lemma image_singleton_iff: "b : r``{a} <-> <a,b>:r"
by (rule image_iff [THEN iff_trans], blast)

lemma imageI [intro]: "[| <a,b>: r;  a:A |] ==> b : r``A"
by (unfold image_def, blast)

lemma imageE [elim!]: 
    "[| b: r``A;  !!x.[| <x,b>: r;  x:A |] ==> P |] ==> P"
by (unfold image_def, blast)

lemma image_subset: "r <= A*B ==> r``C <= B"
by blast

lemma image_0 [simp]: "r``0 = 0"
by blast

lemma image_Un [simp]: "r``(A Un B) = (r``A) Un (r``B)"
by blast

lemma image_Int_subset: "r``(A Int B) <= (r``A) Int (r``B)"
by blast

lemma image_Int_square_subset: "(r Int A*A)``B <= (r``B) Int A"
by blast

lemma image_Int_square: "B<=A ==> (r Int A*A)``B = (r``B) Int A"
by blast


(*Image laws for special relations*)
lemma image_0_left [simp]: "0``A = 0"
by blast

lemma image_Un_left: "(r Un s)``A = (r``A) Un (s``A)"
by blast

lemma image_Int_subset_left: "(r Int s)``A <= (r``A) Int (s``A)"
by blast


subsection{*Inverse Image of a Set under a Function or Relation*}

lemma vimage_iff: 
    "a : r-``B <-> (\<exists>y\<in>B. <a,y>:r)"
by (unfold vimage_def image_def converse_def, blast)

lemma vimage_singleton_iff: "a : r-``{b} <-> <a,b>:r"
by (rule vimage_iff [THEN iff_trans], blast)

lemma vimageI [intro]: "[| <a,b>: r;  b:B |] ==> a : r-``B"
by (unfold vimage_def, blast)

lemma vimageE [elim!]: 
    "[| a: r-``B;  !!x.[| <a,x>: r;  x:B |] ==> P |] ==> P"
apply (unfold vimage_def, blast)
done

lemma vimage_subset: "r <= A*B ==> r-``C <= A"
apply (unfold vimage_def)
apply (erule converse_type [THEN image_subset])
done

lemma vimage_0 [simp]: "r-``0 = 0"
by blast

lemma vimage_Un [simp]: "r-``(A Un B) = (r-``A) Un (r-``B)"
by blast

lemma vimage_Int_subset: "r-``(A Int B) <= (r-``A) Int (r-``B)"
by blast

(*NOT suitable for rewriting*)
lemma vimage_eq_UN: "f -``B = (\<Union>y\<in>B. f-``{y})"
by blast

lemma function_vimage_Int:
     "function(f) ==> f-``(A Int B) = (f-``A)  Int  (f-``B)"
by (unfold function_def, blast)

lemma function_vimage_Diff: "function(f) ==> f-``(A-B) = (f-``A) - (f-``B)"
by (unfold function_def, blast)

lemma function_image_vimage: "function(f) ==> f `` (f-`` A) <= A"
by (unfold function_def, blast)

lemma vimage_Int_square_subset: "(r Int A*A)-``B <= (r-``B) Int A"
by blast

lemma vimage_Int_square: "B<=A ==> (r Int A*A)-``B = (r-``B) Int A"
by blast



(*Invese image laws for special relations*)
lemma vimage_0_left [simp]: "0-``A = 0"
by blast

lemma vimage_Un_left: "(r Un s)-``A = (r-``A) Un (s-``A)"
by blast

lemma vimage_Int_subset_left: "(r Int s)-``A <= (r-``A) Int (s-``A)"
by blast


(** Converse **)

lemma converse_Un [simp]: "converse(A Un B) = converse(A) Un converse(B)"
by blast

lemma converse_Int [simp]: "converse(A Int B) = converse(A) Int converse(B)"
by blast

lemma converse_Diff [simp]: "converse(A - B) = converse(A) - converse(B)"
by blast

lemma converse_UN [simp]: "converse(\<Union>x\<in>A. B(x)) = (\<Union>x\<in>A. converse(B(x)))"
by blast

(*Unfolding Inter avoids using excluded middle on A=0*)
lemma converse_INT [simp]:
     "converse(\<Inter>x\<in>A. B(x)) = (\<Inter>x\<in>A. converse(B(x)))"
apply (unfold Inter_def, blast)
done


subsection{*Powerset Operator*}

lemma Pow_0 [simp]: "Pow(0) = {0}"
by blast

lemma Pow_insert: "Pow (cons(a,A)) = Pow(A) Un {cons(a,X) . X: Pow(A)}"
apply (rule equalityI, safe)
apply (erule swap)
apply (rule_tac a = "x-{a}" in RepFun_eqI, auto) 
done

lemma Un_Pow_subset: "Pow(A) Un Pow(B) <= Pow(A Un B)"
by blast

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow(B(x))) <= Pow(\<Union>x\<in>A. B(x))"
by blast

lemma subset_Pow_Union: "A <= Pow(Union(A))"
by blast

lemma Union_Pow_eq [simp]: "Union(Pow(A)) = A"
by blast

lemma Union_Pow_iff: "Union(A) \<in> Pow(B) <-> A \<in> Pow(Pow(B))"
by blast

lemma Pow_Int_eq [simp]: "Pow(A Int B) = Pow(A) Int Pow(B)"
by blast

lemma Pow_INT_eq: "x:A ==> Pow(\<Inter>x\<in>A. B(x)) = (\<Inter>x\<in>A. Pow(B(x)))"
by blast


subsection{*RepFun*}

lemma RepFun_subset: "[| !!x. x:A ==> f(x): B |] ==> {f(x). x:A} <= B"
by blast

lemma RepFun_eq_0_iff [simp]: "{f(x).x:A}=0 <-> A=0"
by blast

lemma RepFun_constant [simp]: "{c. x:A} = (if A=0 then 0 else {c})"
apply auto
apply blast
done

subsection{*Collect*}

lemma Collect_subset: "Collect(A,P) <= A"
by blast

lemma Collect_Un: "Collect(A Un B, P) = Collect(A,P) Un Collect(B,P)"
by blast

lemma Collect_Int: "Collect(A Int B, P) = Collect(A,P) Int Collect(B,P)"
by blast

lemma Collect_Diff: "Collect(A - B, P) = Collect(A,P) - Collect(B,P)"
by blast

lemma Collect_cons: "{x:cons(a,B). P(x)} =  
      (if P(a) then cons(a, {x:B. P(x)}) else {x:B. P(x)})"
by (simp, blast)

lemma Int_Collect_self_eq: "A Int Collect(A,P) = Collect(A,P)"
by blast

lemma Collect_Collect_eq [simp]:
     "Collect(Collect(A,P), Q) = Collect(A, %x. P(x) & Q(x))"
by blast

lemma Collect_Int_Collect_eq:
     "Collect(A,P) Int Collect(A,Q) = Collect(A, %x. P(x) & Q(x))"
by blast

lemma Collect_Union_eq [simp]:
     "Collect(\<Union>x\<in>A. B(x), P) = (\<Union>x\<in>A. Collect(B(x), P))"
by blast

lemma Collect_Int_left: "{x:A. P(x)} Int B = {x : A Int B. P(x)}"
by blast

lemma Collect_Int_right: "A Int {x:B. P(x)} = {x : A Int B. P(x)}"
by blast

lemma Collect_disj_eq: "{x:A. P(x) | Q(x)} = Collect(A, P) Un Collect(A, Q)"
by blast

lemma Collect_conj_eq: "{x:A. P(x) & Q(x)} = Collect(A, P) Int Collect(A, Q)"
by blast

lemmas subset_SIs = subset_refl cons_subsetI subset_consI 
                    Union_least UN_least Un_least 
                    Inter_greatest Int_greatest RepFun_subset
                    Un_upper1 Un_upper2 Int_lower1 Int_lower2

(*First, ML bindings from the old file subset.ML*)
ML
{*
val cons_subsetI = thm "cons_subsetI";
val subset_consI = thm "subset_consI";
val cons_subset_iff = thm "cons_subset_iff";
val cons_subsetE = thm "cons_subsetE";
val subset_empty_iff = thm "subset_empty_iff";
val subset_cons_iff = thm "subset_cons_iff";
val subset_succI = thm "subset_succI";
val succ_subsetI = thm "succ_subsetI";
val succ_subsetE = thm "succ_subsetE";
val succ_subset_iff = thm "succ_subset_iff";
val singleton_subsetI = thm "singleton_subsetI";
val singleton_subsetD = thm "singleton_subsetD";
val Union_subset_iff = thm "Union_subset_iff";
val Union_upper = thm "Union_upper";
val Union_least = thm "Union_least";
val subset_UN_iff_eq = thm "subset_UN_iff_eq";
val UN_subset_iff = thm "UN_subset_iff";
val UN_upper = thm "UN_upper";
val UN_least = thm "UN_least";
val Inter_subset_iff = thm "Inter_subset_iff";
val Inter_lower = thm "Inter_lower";
val Inter_greatest = thm "Inter_greatest";
val INT_lower = thm "INT_lower";
val INT_greatest = thm "INT_greatest";
val Un_subset_iff = thm "Un_subset_iff";
val Un_upper1 = thm "Un_upper1";
val Un_upper2 = thm "Un_upper2";
val Un_least = thm "Un_least";
val Int_subset_iff = thm "Int_subset_iff";
val Int_lower1 = thm "Int_lower1";
val Int_lower2 = thm "Int_lower2";
val Int_greatest = thm "Int_greatest";
val Diff_subset = thm "Diff_subset";
val Diff_contains = thm "Diff_contains";
val subset_Diff_cons_iff = thm "subset_Diff_cons_iff";
val Collect_subset = thm "Collect_subset";
val RepFun_subset = thm "RepFun_subset";

val subset_SIs = thms "subset_SIs";

val subset_cs = claset() 
    delrules [subsetI, subsetCE]
    addSIs subset_SIs
    addIs  [Union_upper, Inter_lower]
    addSEs [cons_subsetE];
*}
(*subset_cs is a claset for subset reasoning*)

ML
{*
val ZF_cs = claset() delrules [equalityI];

val in_mono = thm "in_mono";
val conj_mono = thm "conj_mono";
val disj_mono = thm "disj_mono";
val imp_mono = thm "imp_mono";
val imp_refl = thm "imp_refl";
val ex_mono = thm "ex_mono";
val all_mono = thm "all_mono";

val converse_iff = thm "converse_iff";
val converseI = thm "converseI";
val converseD = thm "converseD";
val converseE = thm "converseE";
val converse_converse = thm "converse_converse";
val converse_type = thm "converse_type";
val converse_prod = thm "converse_prod";
val converse_empty = thm "converse_empty";
val converse_subset_iff = thm "converse_subset_iff";
val domain_iff = thm "domain_iff";
val domainI = thm "domainI";
val domainE = thm "domainE";
val domain_subset = thm "domain_subset";
val rangeI = thm "rangeI";
val rangeE = thm "rangeE";
val range_subset = thm "range_subset";
val fieldI1 = thm "fieldI1";
val fieldI2 = thm "fieldI2";
val fieldCI = thm "fieldCI";
val fieldE = thm "fieldE";
val field_subset = thm "field_subset";
val domain_subset_field = thm "domain_subset_field";
val range_subset_field = thm "range_subset_field";
val domain_times_range = thm "domain_times_range";
val field_times_field = thm "field_times_field";
val image_iff = thm "image_iff";
val image_singleton_iff = thm "image_singleton_iff";
val imageI = thm "imageI";
val imageE = thm "imageE";
val image_subset = thm "image_subset";
val vimage_iff = thm "vimage_iff";
val vimage_singleton_iff = thm "vimage_singleton_iff";
val vimageI = thm "vimageI";
val vimageE = thm "vimageE";
val vimage_subset = thm "vimage_subset";
val rel_Union = thm "rel_Union";
val rel_Un = thm "rel_Un";
val domain_Diff_eq = thm "domain_Diff_eq";
val range_Diff_eq = thm "range_Diff_eq";
val cons_eq = thm "cons_eq";
val cons_commute = thm "cons_commute";
val cons_absorb = thm "cons_absorb";
val cons_Diff = thm "cons_Diff";
val equal_singleton = thm "equal_singleton";
val Int_cons = thm "Int_cons";
val Int_absorb = thm "Int_absorb";
val Int_left_absorb = thm "Int_left_absorb";
val Int_commute = thm "Int_commute";
val Int_left_commute = thm "Int_left_commute";
val Int_assoc = thm "Int_assoc";
val Int_Un_distrib = thm "Int_Un_distrib";
val Int_Un_distrib2 = thm "Int_Un_distrib2";
val subset_Int_iff = thm "subset_Int_iff";
val subset_Int_iff2 = thm "subset_Int_iff2";
val Int_Diff_eq = thm "Int_Diff_eq";
val Int_cons_left = thm "Int_cons_left";
val Int_cons_right = thm "Int_cons_right";
val Un_cons = thm "Un_cons";
val Un_absorb = thm "Un_absorb";
val Un_left_absorb = thm "Un_left_absorb";
val Un_commute = thm "Un_commute";
val Un_left_commute = thm "Un_left_commute";
val Un_assoc = thm "Un_assoc";
val Un_Int_distrib = thm "Un_Int_distrib";
val subset_Un_iff = thm "subset_Un_iff";
val subset_Un_iff2 = thm "subset_Un_iff2";
val Un_empty = thm "Un_empty";
val Un_eq_Union = thm "Un_eq_Union";
val Diff_cancel = thm "Diff_cancel";
val Diff_triv = thm "Diff_triv";
val empty_Diff = thm "empty_Diff";
val Diff_0 = thm "Diff_0";
val Diff_eq_0_iff = thm "Diff_eq_0_iff";
val Diff_cons = thm "Diff_cons";
val Diff_cons2 = thm "Diff_cons2";
val Diff_disjoint = thm "Diff_disjoint";
val Diff_partition = thm "Diff_partition";
val subset_Un_Diff = thm "subset_Un_Diff";
val double_complement = thm "double_complement";
val double_complement_Un = thm "double_complement_Un";
val Un_Int_crazy = thm "Un_Int_crazy";
val Diff_Un = thm "Diff_Un";
val Diff_Int = thm "Diff_Int";
val Un_Diff = thm "Un_Diff";
val Int_Diff = thm "Int_Diff";
val Diff_Int_distrib = thm "Diff_Int_distrib";
val Diff_Int_distrib2 = thm "Diff_Int_distrib2";
val Un_Int_assoc_iff = thm "Un_Int_assoc_iff";
val Union_cons = thm "Union_cons";
val Union_Un_distrib = thm "Union_Un_distrib";
val Union_Int_subset = thm "Union_Int_subset";
val Union_disjoint = thm "Union_disjoint";
val Union_empty_iff = thm "Union_empty_iff";
val Int_Union2 = thm "Int_Union2";
val Inter_0 = thm "Inter_0";
val Inter_Un_subset = thm "Inter_Un_subset";
val Inter_Un_distrib = thm "Inter_Un_distrib";
val Union_singleton = thm "Union_singleton";
val Inter_singleton = thm "Inter_singleton";
val Inter_cons = thm "Inter_cons";
val Union_eq_UN = thm "Union_eq_UN";
val Inter_eq_INT = thm "Inter_eq_INT";
val UN_0 = thm "UN_0";
val UN_singleton = thm "UN_singleton";
val UN_Un = thm "UN_Un";
val INT_Un = thm "INT_Un";
val UN_UN_flatten = thm "UN_UN_flatten";
val Int_UN_distrib = thm "Int_UN_distrib";
val Un_INT_distrib = thm "Un_INT_distrib";
val Int_UN_distrib2 = thm "Int_UN_distrib2";
val Un_INT_distrib2 = thm "Un_INT_distrib2";
val UN_constant = thm "UN_constant";
val INT_constant = thm "INT_constant";
val UN_RepFun = thm "UN_RepFun";
val INT_RepFun = thm "INT_RepFun";
val INT_Union_eq = thm "INT_Union_eq";
val INT_UN_eq = thm "INT_UN_eq";
val UN_Un_distrib = thm "UN_Un_distrib";
val INT_Int_distrib = thm "INT_Int_distrib";
val UN_Int_subset = thm "UN_Int_subset";
val Diff_UN = thm "Diff_UN";
val Diff_INT = thm "Diff_INT";
val Sigma_cons1 = thm "Sigma_cons1";
val Sigma_cons2 = thm "Sigma_cons2";
val Sigma_succ1 = thm "Sigma_succ1";
val Sigma_succ2 = thm "Sigma_succ2";
val SUM_UN_distrib1 = thm "SUM_UN_distrib1";
val SUM_UN_distrib2 = thm "SUM_UN_distrib2";
val SUM_Un_distrib1 = thm "SUM_Un_distrib1";
val SUM_Un_distrib2 = thm "SUM_Un_distrib2";
val prod_Un_distrib2 = thm "prod_Un_distrib2";
val SUM_Int_distrib1 = thm "SUM_Int_distrib1";
val SUM_Int_distrib2 = thm "SUM_Int_distrib2";
val prod_Int_distrib2 = thm "prod_Int_distrib2";
val SUM_eq_UN = thm "SUM_eq_UN";
val domain_of_prod = thm "domain_of_prod";
val domain_0 = thm "domain_0";
val domain_cons = thm "domain_cons";
val domain_Un_eq = thm "domain_Un_eq";
val domain_Int_subset = thm "domain_Int_subset";
val domain_Diff_subset = thm "domain_Diff_subset";
val domain_converse = thm "domain_converse";
val domain_UN = thm "domain_UN";
val domain_Union = thm "domain_Union";
val range_of_prod = thm "range_of_prod";
val range_0 = thm "range_0";
val range_cons = thm "range_cons";
val range_Un_eq = thm "range_Un_eq";
val range_Int_subset = thm "range_Int_subset";
val range_Diff_subset = thm "range_Diff_subset";
val range_converse = thm "range_converse";
val field_of_prod = thm "field_of_prod";
val field_0 = thm "field_0";
val field_cons = thm "field_cons";
val field_Un_eq = thm "field_Un_eq";
val field_Int_subset = thm "field_Int_subset";
val field_Diff_subset = thm "field_Diff_subset";
val field_converse = thm "field_converse";
val image_0 = thm "image_0";
val image_Un = thm "image_Un";
val image_Int_subset = thm "image_Int_subset";
val image_Int_square_subset = thm "image_Int_square_subset";
val image_Int_square = thm "image_Int_square";
val image_0_left = thm "image_0_left";
val image_Un_left = thm "image_Un_left";
val image_Int_subset_left = thm "image_Int_subset_left";
val vimage_0 = thm "vimage_0";
val vimage_Un = thm "vimage_Un";
val vimage_Int_subset = thm "vimage_Int_subset";
val vimage_eq_UN = thm "vimage_eq_UN";
val function_vimage_Int = thm "function_vimage_Int";
val function_vimage_Diff = thm "function_vimage_Diff";
val function_image_vimage = thm "function_image_vimage";
val vimage_Int_square_subset = thm "vimage_Int_square_subset";
val vimage_Int_square = thm "vimage_Int_square";
val vimage_0_left = thm "vimage_0_left";
val vimage_Un_left = thm "vimage_Un_left";
val vimage_Int_subset_left = thm "vimage_Int_subset_left";
val converse_Un = thm "converse_Un";
val converse_Int = thm "converse_Int";
val converse_Diff = thm "converse_Diff";
val converse_UN = thm "converse_UN";
val converse_INT = thm "converse_INT";
val Pow_0 = thm "Pow_0";
val Pow_insert = thm "Pow_insert";
val Un_Pow_subset = thm "Un_Pow_subset";
val UN_Pow_subset = thm "UN_Pow_subset";
val subset_Pow_Union = thm "subset_Pow_Union";
val Union_Pow_eq = thm "Union_Pow_eq";
val Union_Pow_iff = thm "Union_Pow_iff";
val Pow_Int_eq = thm "Pow_Int_eq";
val Pow_INT_eq = thm "Pow_INT_eq";
val RepFun_eq_0_iff = thm "RepFun_eq_0_iff";
val RepFun_constant = thm "RepFun_constant";
val Collect_Un = thm "Collect_Un";
val Collect_Int = thm "Collect_Int";
val Collect_Diff = thm "Collect_Diff";
val Collect_cons = thm "Collect_cons";
val Int_Collect_self_eq = thm "Int_Collect_self_eq";
val Collect_Collect_eq = thm "Collect_Collect_eq";
val Collect_Int_Collect_eq = thm "Collect_Int_Collect_eq";
val Collect_disj_eq = thm "Collect_disj_eq";
val Collect_conj_eq = thm "Collect_conj_eq";

val Int_ac = thms "Int_ac";
val Un_ac = thms "Un_ac";
val Int_absorb1 = thm "Int_absorb1";
val Int_absorb2 = thm "Int_absorb2";
val Un_absorb1 = thm "Un_absorb1";
val Un_absorb2 = thm "Un_absorb2";
*}
 
end

