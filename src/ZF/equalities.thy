(*  Title:      ZF/equalities.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*Basic Equalities and Inclusions*}

theory equalities imports pair begin

text{*These cover union, intersection, converse, domain, range, etc.  Philippe
de Groote proved many of the inclusions.*}

lemma in_mono: "A\<subseteq>B ==> x\<in>A \<longrightarrow> x\<in>B"
by blast

lemma the_eq_0 [simp]: "(THE x. False) = 0"
by (blast intro: the_0)

subsection{*Bounded Quantifiers*}
text {* \medskip

  The following are not added to the default simpset because
  (a) they duplicate the body and (b) there are no similar rules for @{text Int}.*}

lemma ball_Un: "(\<forall>x \<in> A\<union>B. P(x)) \<longleftrightarrow> (\<forall>x \<in> A. P(x)) & (\<forall>x \<in> B. P(x))";
  by blast

lemma bex_Un: "(\<exists>x \<in> A\<union>B. P(x)) \<longleftrightarrow> (\<exists>x \<in> A. P(x)) | (\<exists>x \<in> B. P(x))";
  by blast

lemma ball_UN: "(\<forall>z \<in> (\<Union>x\<in>A. B(x)). P(z)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>z \<in> B(x). P(z))"
  by blast

lemma bex_UN: "(\<exists>z \<in> (\<Union>x\<in>A. B(x)). P(z)) \<longleftrightarrow> (\<exists>x\<in>A. \<exists>z\<in>B(x). P(z))"
  by blast

subsection{*Converse of a Relation*}

lemma converse_iff [simp]: "<a,b>\<in> converse(r) \<longleftrightarrow> <b,a>\<in>r"
by (unfold converse_def, blast)

lemma converseI [intro!]: "<a,b>\<in>r ==> <b,a>\<in>converse(r)"
by (unfold converse_def, blast)

lemma converseD: "<a,b> \<in> converse(r) ==> <b,a> \<in> r"
by (unfold converse_def, blast)

lemma converseE [elim!]:
    "[| yx \<in> converse(r);
        !!x y. [| yx=<y,x>;  <x,y>\<in>r |] ==> P |]
     ==> P"
by (unfold converse_def, blast)

lemma converse_converse: "r\<subseteq>Sigma(A,B) ==> converse(converse(r)) = r"
by blast

lemma converse_type: "r\<subseteq>A*B ==> converse(r)\<subseteq>B*A"
by blast

lemma converse_prod [simp]: "converse(A*B) = B*A"
by blast

lemma converse_empty [simp]: "converse(0) = 0"
by blast

lemma converse_subset_iff:
     "A \<subseteq> Sigma(X,Y) ==> converse(A) \<subseteq> converse(B) \<longleftrightarrow> A \<subseteq> B"
by blast


subsection{*Finite Set Constructions Using @{term cons}*}

lemma cons_subsetI: "[| a\<in>C; B\<subseteq>C |] ==> cons(a,B) \<subseteq> C"
by blast

lemma subset_consI: "B \<subseteq> cons(a,B)"
by blast

lemma cons_subset_iff [iff]: "cons(a,B)\<subseteq>C \<longleftrightarrow> a\<in>C & B\<subseteq>C"
by blast

(*A safe special case of subset elimination, adding no new variables
  [| cons(a,B) \<subseteq> C; [| a \<in> C; B \<subseteq> C |] ==> R |] ==> R *)
lemmas cons_subsetE = cons_subset_iff [THEN iffD1, THEN conjE]

lemma subset_empty_iff: "A\<subseteq>0 \<longleftrightarrow> A=0"
by blast

lemma subset_cons_iff: "C\<subseteq>cons(a,B) \<longleftrightarrow> C\<subseteq>B | (a\<in>C & C-{a} \<subseteq> B)"
by blast

(* cons_def refers to Upair; reversing the equality LOOPS in rewriting!*)
lemma cons_eq: "{a} \<union> B = cons(a,B)"
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

lemma singleton_subsetI: "a\<in>C ==> {a} \<subseteq> C"
by blast

lemma singleton_subsetD: "{a} \<subseteq> C  ==>  a\<in>C"
by blast


(** succ **)

lemma subset_succI: "i \<subseteq> succ(i)"
by blast

(*But if j is an ordinal or is transitive, then @{term"i\<in>j"} implies @{term"i\<subseteq>j"}!
  See @{text"Ord_succ_subsetI}*)
lemma succ_subsetI: "[| i\<in>j;  i\<subseteq>j |] ==> succ(i)\<subseteq>j"
by (unfold succ_def, blast)

lemma succ_subsetE:
    "[| succ(i) \<subseteq> j;  [| i\<in>j;  i\<subseteq>j |] ==> P |] ==> P"
by (unfold succ_def, blast)

lemma succ_subset_iff: "succ(a) \<subseteq> B \<longleftrightarrow> (a \<subseteq> B & a \<in> B)"
by (unfold succ_def, blast)


subsection{*Binary Intersection*}

(** Intersection is the greatest lower bound of two sets **)

lemma Int_subset_iff: "C \<subseteq> A \<inter> B \<longleftrightarrow> C \<subseteq> A & C \<subseteq> B"
by blast

lemma Int_lower1: "A \<inter> B \<subseteq> A"
by blast

lemma Int_lower2: "A \<inter> B \<subseteq> B"
by blast

lemma Int_greatest: "[| C\<subseteq>A;  C\<subseteq>B |] ==> C \<subseteq> A \<inter> B"
by blast

lemma Int_cons: "cons(a,B) \<inter> C \<subseteq> cons(a, B \<inter> C)"
by blast

lemma Int_absorb [simp]: "A \<inter> A = A"
by blast

lemma Int_left_absorb: "A \<inter> (A \<inter> B) = A \<inter> B"
by blast

lemma Int_commute: "A \<inter> B = B \<inter> A"
by blast

lemma Int_left_commute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
by blast

lemma Int_assoc: "(A \<inter> B) \<inter> C  =  A \<inter> (B \<inter> C)"
by blast

(*Intersection is an AC-operator*)
lemmas Int_ac= Int_assoc Int_left_absorb Int_commute Int_left_commute

lemma Int_absorb1: "B \<subseteq> A ==> A \<inter> B = B"
  by blast

lemma Int_absorb2: "A \<subseteq> B ==> A \<inter> B = A"
  by blast

lemma Int_Un_distrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
by blast

lemma Int_Un_distrib2: "(B \<union> C) \<inter> A = (B \<inter> A) \<union> (C \<inter> A)"
by blast

lemma subset_Int_iff: "A\<subseteq>B \<longleftrightarrow> A \<inter> B = A"
by (blast elim!: equalityE)

lemma subset_Int_iff2: "A\<subseteq>B \<longleftrightarrow> B \<inter> A = A"
by (blast elim!: equalityE)

lemma Int_Diff_eq: "C\<subseteq>A ==> (A-B) \<inter> C = C-B"
by blast

lemma Int_cons_left:
     "cons(a,A) \<inter> B = (if a \<in> B then cons(a, A \<inter> B) else A \<inter> B)"
by auto

lemma Int_cons_right:
     "A \<inter> cons(a, B) = (if a \<in> A then cons(a, A \<inter> B) else A \<inter> B)"
by auto

lemma cons_Int_distrib: "cons(x, A \<inter> B) = cons(x, A) \<inter> cons(x, B)"
by auto

subsection{*Binary Union*}

(** Union is the least upper bound of two sets *)

lemma Un_subset_iff: "A \<union> B \<subseteq> C \<longleftrightarrow> A \<subseteq> C & B \<subseteq> C"
by blast

lemma Un_upper1: "A \<subseteq> A \<union> B"
by blast

lemma Un_upper2: "B \<subseteq> A \<union> B"
by blast

lemma Un_least: "[| A\<subseteq>C;  B\<subseteq>C |] ==> A \<union> B \<subseteq> C"
by blast

lemma Un_cons: "cons(a,B) \<union> C = cons(a, B \<union> C)"
by blast

lemma Un_absorb [simp]: "A \<union> A = A"
by blast

lemma Un_left_absorb: "A \<union> (A \<union> B) = A \<union> B"
by blast

lemma Un_commute: "A \<union> B = B \<union> A"
by blast

lemma Un_left_commute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
by blast

lemma Un_assoc: "(A \<union> B) \<union> C  =  A \<union> (B \<union> C)"
by blast

(*Union is an AC-operator*)
lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute

lemma Un_absorb1: "A \<subseteq> B ==> A \<union> B = B"
  by blast

lemma Un_absorb2: "B \<subseteq> A ==> A \<union> B = A"
  by blast

lemma Un_Int_distrib: "(A \<inter> B) \<union> C  =  (A \<union> C) \<inter> (B \<union> C)"
by blast

lemma subset_Un_iff: "A\<subseteq>B \<longleftrightarrow> A \<union> B = B"
by (blast elim!: equalityE)

lemma subset_Un_iff2: "A\<subseteq>B \<longleftrightarrow> B \<union> A = B"
by (blast elim!: equalityE)

lemma Un_empty [iff]: "(A \<union> B = 0) \<longleftrightarrow> (A = 0 & B = 0)"
by blast

lemma Un_eq_Union: "A \<union> B = \<Union>({A, B})"
by blast

subsection{*Set Difference*}

lemma Diff_subset: "A-B \<subseteq> A"
by blast

lemma Diff_contains: "[| C\<subseteq>A;  C \<inter> B = 0 |] ==> C \<subseteq> A-B"
by blast

lemma subset_Diff_cons_iff: "B \<subseteq> A - cons(c,C)  \<longleftrightarrow>  B\<subseteq>A-C & c \<notin> B"
by blast

lemma Diff_cancel: "A - A = 0"
by blast

lemma Diff_triv: "A  \<inter> B = 0 ==> A - B = A"
by blast

lemma empty_Diff [simp]: "0 - A = 0"
by blast

lemma Diff_0 [simp]: "A - 0 = A"
by blast

lemma Diff_eq_0_iff: "A - B = 0 \<longleftrightarrow> A \<subseteq> B"
by (blast elim: equalityE)

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
lemma Diff_cons: "A - cons(a,B) = A - B - {a}"
by blast

(*NOT SUITABLE FOR REWRITING since {a} == cons(a,0)*)
lemma Diff_cons2: "A - cons(a,B) = A - {a} - B"
by blast

lemma Diff_disjoint: "A \<inter> (B-A) = 0"
by blast

lemma Diff_partition: "A\<subseteq>B ==> A \<union> (B-A) = B"
by blast

lemma subset_Un_Diff: "A \<subseteq> B \<union> (A - B)"
by blast

lemma double_complement: "[| A\<subseteq>B; B\<subseteq>C |] ==> B-(C-A) = A"
by blast

lemma double_complement_Un: "(A \<union> B) - (B-A) = A"
by blast

lemma Un_Int_crazy:
 "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
apply blast
done

lemma Diff_Un: "A - (B \<union> C) = (A-B) \<inter> (A-C)"
by blast

lemma Diff_Int: "A - (B \<inter> C) = (A-B) \<union> (A-C)"
by blast

lemma Un_Diff: "(A \<union> B) - C = (A - C) \<union> (B - C)"
by blast

lemma Int_Diff: "(A \<inter> B) - C = A \<inter> (B - C)"
by blast

lemma Diff_Int_distrib: "C \<inter> (A-B) = (C \<inter> A) - (C \<inter> B)"
by blast

lemma Diff_Int_distrib2: "(A-B) \<inter> C = (A \<inter> C) - (B \<inter> C)"
by blast

(*Halmos, Naive Set Theory, page 16.*)
lemma Un_Int_assoc_iff: "(A \<inter> B) \<union> C = A \<inter> (B \<union> C)  \<longleftrightarrow>  C\<subseteq>A"
by (blast elim!: equalityE)


subsection{*Big Union and Intersection*}

(** Big Union is the least upper bound of a set  **)

lemma Union_subset_iff: "\<Union>(A) \<subseteq> C \<longleftrightarrow> (\<forall>x\<in>A. x \<subseteq> C)"
by blast

lemma Union_upper: "B\<in>A ==> B \<subseteq> \<Union>(A)"
by blast

lemma Union_least: "[| !!x. x\<in>A ==> x\<subseteq>C |] ==> \<Union>(A) \<subseteq> C"
by blast

lemma Union_cons [simp]: "\<Union>(cons(a,B)) = a \<union> \<Union>(B)"
by blast

lemma Union_Un_distrib: "\<Union>(A \<union> B) = \<Union>(A) \<union> \<Union>(B)"
by blast

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>(A) \<inter> \<Union>(B)"
by blast

lemma Union_disjoint: "\<Union>(C) \<inter> A = 0 \<longleftrightarrow> (\<forall>B\<in>C. B \<inter> A = 0)"
by (blast elim!: equalityE)

lemma Union_empty_iff: "\<Union>(A) = 0 \<longleftrightarrow> (\<forall>B\<in>A. B=0)"
by blast

lemma Int_Union2: "\<Union>(B) \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
by blast

(** Big Intersection is the greatest lower bound of a nonempty set **)

lemma Inter_subset_iff: "A\<noteq>0  ==>  C \<subseteq> \<Inter>(A) \<longleftrightarrow> (\<forall>x\<in>A. C \<subseteq> x)"
by blast

lemma Inter_lower: "B\<in>A ==> \<Inter>(A) \<subseteq> B"
by blast

lemma Inter_greatest: "[| A\<noteq>0;  !!x. x\<in>A ==> C\<subseteq>x |] ==> C \<subseteq> \<Inter>(A)"
by blast

(** Intersection of a family of sets  **)

lemma INT_lower: "x\<in>A ==> (\<Inter>x\<in>A. B(x)) \<subseteq> B(x)"
by blast

lemma INT_greatest: "[| A\<noteq>0;  !!x. x\<in>A ==> C\<subseteq>B(x) |] ==> C \<subseteq> (\<Inter>x\<in>A. B(x))"
by force

lemma Inter_0 [simp]: "\<Inter>(0) = 0"
by (unfold Inter_def, blast)

lemma Inter_Un_subset:
     "[| z\<in>A; z\<in>B |] ==> \<Inter>(A) \<union> \<Inter>(B) \<subseteq> \<Inter>(A \<inter> B)"
by blast

(* A good challenge: Inter is ill-behaved on the empty set *)
lemma Inter_Un_distrib:
     "[| A\<noteq>0;  B\<noteq>0 |] ==> \<Inter>(A \<union> B) = \<Inter>(A) \<inter> \<Inter>(B)"
by blast

lemma Union_singleton: "\<Union>({b}) = b"
by blast

lemma Inter_singleton: "\<Inter>({b}) = b"
by blast

lemma Inter_cons [simp]:
     "\<Inter>(cons(a,B)) = (if B=0 then a else a \<inter> \<Inter>(B))"
by force

subsection{*Unions and Intersections of Families*}

lemma subset_UN_iff_eq: "A \<subseteq> (\<Union>i\<in>I. B(i)) \<longleftrightarrow> A = (\<Union>i\<in>I. A \<inter> B(i))"
by (blast elim!: equalityE)

lemma UN_subset_iff: "(\<Union>x\<in>A. B(x)) \<subseteq> C \<longleftrightarrow> (\<forall>x\<in>A. B(x) \<subseteq> C)"
by blast

lemma UN_upper: "x\<in>A ==> B(x) \<subseteq> (\<Union>x\<in>A. B(x))"
by (erule RepFunI [THEN Union_upper])

lemma UN_least: "[| !!x. x\<in>A ==> B(x)\<subseteq>C |] ==> (\<Union>x\<in>A. B(x)) \<subseteq> C"
by blast

lemma Union_eq_UN: "\<Union>(A) = (\<Union>x\<in>A. x)"
by blast

lemma Inter_eq_INT: "\<Inter>(A) = (\<Inter>x\<in>A. x)"
by (unfold Inter_def, blast)

lemma UN_0 [simp]: "(\<Union>i\<in>0. A(i)) = 0"
by blast

lemma UN_singleton: "(\<Union>x\<in>A. {x}) = A"
by blast

lemma UN_Un: "(\<Union>i\<in> A \<union> B. C(i)) = (\<Union>i\<in> A. C(i)) \<union> (\<Union>i\<in>B. C(i))"
by blast

lemma INT_Un: "(\<Inter>i\<in>I \<union> J. A(i)) =
               (if I=0 then \<Inter>j\<in>J. A(j)
                       else if J=0 then \<Inter>i\<in>I. A(i)
                       else ((\<Inter>i\<in>I. A(i)) \<inter>  (\<Inter>j\<in>J. A(j))))"
by (simp, blast intro!: equalityI)

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B(y)). C(x)) = (\<Union>y\<in>A. \<Union>x\<in> B(y). C(x))"
by blast

(*Halmos, Naive Set Theory, page 35.*)
lemma Int_UN_distrib: "B \<inter> (\<Union>i\<in>I. A(i)) = (\<Union>i\<in>I. B \<inter> A(i))"
by blast

lemma Un_INT_distrib: "I\<noteq>0 ==> B \<union> (\<Inter>i\<in>I. A(i)) = (\<Inter>i\<in>I. B \<union> A(i))"
by auto

lemma Int_UN_distrib2:
     "(\<Union>i\<in>I. A(i)) \<inter> (\<Union>j\<in>J. B(j)) = (\<Union>i\<in>I. \<Union>j\<in>J. A(i) \<inter> B(j))"
by blast

lemma Un_INT_distrib2: "[| I\<noteq>0;  J\<noteq>0 |] ==>
      (\<Inter>i\<in>I. A(i)) \<union> (\<Inter>j\<in>J. B(j)) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A(i) \<union> B(j))"
by auto

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A=0 then 0 else c)"
by force

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A=0 then 0 else c)"
by force

lemma UN_RepFun [simp]: "(\<Union>y\<in> RepFun(A,f). B(y)) = (\<Union>x\<in>A. B(f(x)))"
by blast

lemma INT_RepFun [simp]: "(\<Inter>x\<in>RepFun(A,f). B(x))    = (\<Inter>a\<in>A. B(f(a)))"
by (auto simp add: Inter_def)

lemma INT_Union_eq:
     "0 \<notin> A ==> (\<Inter>x\<in> \<Union>(A). B(x)) = (\<Inter>y\<in>A. \<Inter>x\<in>y. B(x))"
apply (subgoal_tac "\<forall>x\<in>A. x\<noteq>0")
 prefer 2 apply blast
apply (force simp add: Inter_def ball_conj_distrib)
done

lemma INT_UN_eq:
     "(\<forall>x\<in>A. B(x) \<noteq> 0)
      ==> (\<Inter>z\<in> (\<Union>x\<in>A. B(x)). C(z)) = (\<Inter>x\<in>A. \<Inter>z\<in> B(x). C(z))"
apply (subst INT_Union_eq, blast)
apply (simp add: Inter_def)
done


(** Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5:
    Union of a family of unions **)

lemma UN_Un_distrib:
     "(\<Union>i\<in>I. A(i) \<union> B(i)) = (\<Union>i\<in>I. A(i))  \<union>  (\<Union>i\<in>I. B(i))"
by blast

lemma INT_Int_distrib:
     "I\<noteq>0 ==> (\<Inter>i\<in>I. A(i) \<inter> B(i)) = (\<Inter>i\<in>I. A(i)) \<inter> (\<Inter>i\<in>I. B(i))"
by (blast elim!: not_emptyE)

lemma UN_Int_subset:
     "(\<Union>z\<in>I \<inter> J. A(z)) \<subseteq> (\<Union>z\<in>I. A(z)) \<inter> (\<Union>z\<in>J. A(z))"
by blast

(** Devlin, page 12, exercise 5: Complements **)

lemma Diff_UN: "I\<noteq>0 ==> B - (\<Union>i\<in>I. A(i)) = (\<Inter>i\<in>I. B - A(i))"
by (blast elim!: not_emptyE)

lemma Diff_INT: "I\<noteq>0 ==> B - (\<Inter>i\<in>I. A(i)) = (\<Union>i\<in>I. B - A(i))"
by (blast elim!: not_emptyE)


(** Unions and Intersections with General Sum **)

(*Not suitable for rewriting: LOOPS!*)
lemma Sigma_cons1: "Sigma(cons(a,B), C) = ({a}*C(a)) \<union> Sigma(B,C)"
by blast

(*Not suitable for rewriting: LOOPS!*)
lemma Sigma_cons2: "A * cons(b,B) = A*{b} \<union> A*B"
by blast

lemma Sigma_succ1: "Sigma(succ(A), B) = ({A}*B(A)) \<union> Sigma(A,B)"
by blast

lemma Sigma_succ2: "A * succ(B) = A*{B} \<union> A*B"
by blast

lemma SUM_UN_distrib1:
     "(\<Sigma> x \<in> (\<Union>y\<in>A. C(y)). B(x)) = (\<Union>y\<in>A. \<Sigma> x\<in>C(y). B(x))"
by blast

lemma SUM_UN_distrib2:
     "(\<Sigma> i\<in>I. \<Union>j\<in>J. C(i,j)) = (\<Union>j\<in>J. \<Sigma> i\<in>I. C(i,j))"
by blast

lemma SUM_Un_distrib1:
     "(\<Sigma> i\<in>I \<union> J. C(i)) = (\<Sigma> i\<in>I. C(i)) \<union> (\<Sigma> j\<in>J. C(j))"
by blast

lemma SUM_Un_distrib2:
     "(\<Sigma> i\<in>I. A(i) \<union> B(i)) = (\<Sigma> i\<in>I. A(i)) \<union> (\<Sigma> i\<in>I. B(i))"
by blast

(*First-order version of the above, for rewriting*)
lemma prod_Un_distrib2: "I * (A \<union> B) = I*A \<union> I*B"
by (rule SUM_Un_distrib2)

lemma SUM_Int_distrib1:
     "(\<Sigma> i\<in>I \<inter> J. C(i)) = (\<Sigma> i\<in>I. C(i)) \<inter> (\<Sigma> j\<in>J. C(j))"
by blast

lemma SUM_Int_distrib2:
     "(\<Sigma> i\<in>I. A(i) \<inter> B(i)) = (\<Sigma> i\<in>I. A(i)) \<inter> (\<Sigma> i\<in>I. B(i))"
by blast

(*First-order version of the above, for rewriting*)
lemma prod_Int_distrib2: "I * (A \<inter> B) = I*A \<inter> I*B"
by (rule SUM_Int_distrib2)

(*Cf Aczel, Non-Well-Founded Sets, page 115*)
lemma SUM_eq_UN: "(\<Sigma> i\<in>I. A(i)) = (\<Union>i\<in>I. {i} * A(i))"
by blast

lemma times_subset_iff:
     "(A'*B' \<subseteq> A*B) \<longleftrightarrow> (A' = 0 | B' = 0 | (A'\<subseteq>A) & (B'\<subseteq>B))"
by blast

lemma Int_Sigma_eq:
     "(\<Sigma> x \<in> A'. B'(x)) \<inter> (\<Sigma> x \<in> A. B(x)) = (\<Sigma> x \<in> A' \<inter> A. B'(x) \<inter> B(x))"
by blast

(** Domain **)

lemma domain_iff: "a: domain(r) \<longleftrightarrow> (\<exists>y. <a,y>\<in> r)"
by (unfold domain_def, blast)

lemma domainI [intro]: "<a,b>\<in> r ==> a: domain(r)"
by (unfold domain_def, blast)

lemma domainE [elim!]:
    "[| a \<in> domain(r);  !!y. <a,y>\<in> r ==> P |] ==> P"
by (unfold domain_def, blast)

lemma domain_subset: "domain(Sigma(A,B)) \<subseteq> A"
by blast

lemma domain_of_prod: "b\<in>B ==> domain(A*B) = A"
by blast

lemma domain_0 [simp]: "domain(0) = 0"
by blast

lemma domain_cons [simp]: "domain(cons(<a,b>,r)) = cons(a, domain(r))"
by blast

lemma domain_Un_eq [simp]: "domain(A \<union> B) = domain(A) \<union> domain(B)"
by blast

lemma domain_Int_subset: "domain(A \<inter> B) \<subseteq> domain(A) \<inter> domain(B)"
by blast

lemma domain_Diff_subset: "domain(A) - domain(B) \<subseteq> domain(A - B)"
by blast

lemma domain_UN: "domain(\<Union>x\<in>A. B(x)) = (\<Union>x\<in>A. domain(B(x)))"
by blast

lemma domain_Union: "domain(\<Union>(A)) = (\<Union>x\<in>A. domain(x))"
by blast


(** Range **)

lemma rangeI [intro]: "<a,b>\<in> r ==> b \<in> range(r)"
apply (unfold range_def)
apply (erule converseI [THEN domainI])
done

lemma rangeE [elim!]: "[| b \<in> range(r);  !!x. <x,b>\<in> r ==> P |] ==> P"
by (unfold range_def, blast)

lemma range_subset: "range(A*B) \<subseteq> B"
apply (unfold range_def)
apply (subst converse_prod)
apply (rule domain_subset)
done

lemma range_of_prod: "a\<in>A ==> range(A*B) = B"
by blast

lemma range_0 [simp]: "range(0) = 0"
by blast

lemma range_cons [simp]: "range(cons(<a,b>,r)) = cons(b, range(r))"
by blast

lemma range_Un_eq [simp]: "range(A \<union> B) = range(A) \<union> range(B)"
by blast

lemma range_Int_subset: "range(A \<inter> B) \<subseteq> range(A) \<inter> range(B)"
by blast

lemma range_Diff_subset: "range(A) - range(B) \<subseteq> range(A - B)"
by blast

lemma domain_converse [simp]: "domain(converse(r)) = range(r)"
by blast

lemma range_converse [simp]: "range(converse(r)) = domain(r)"
by blast


(** Field **)

lemma fieldI1: "<a,b>\<in> r ==> a \<in> field(r)"
by (unfold field_def, blast)

lemma fieldI2: "<a,b>\<in> r ==> b \<in> field(r)"
by (unfold field_def, blast)

lemma fieldCI [intro]:
    "(~ <c,a>\<in>r ==> <a,b>\<in> r) ==> a \<in> field(r)"
apply (unfold field_def, blast)
done

lemma fieldE [elim!]:
     "[| a \<in> field(r);
         !!x. <a,x>\<in> r ==> P;
         !!x. <x,a>\<in> r ==> P        |] ==> P"
by (unfold field_def, blast)

lemma field_subset: "field(A*B) \<subseteq> A \<union> B"
by blast

lemma domain_subset_field: "domain(r) \<subseteq> field(r)"
apply (unfold field_def)
apply (rule Un_upper1)
done

lemma range_subset_field: "range(r) \<subseteq> field(r)"
apply (unfold field_def)
apply (rule Un_upper2)
done

lemma domain_times_range: "r \<subseteq> Sigma(A,B) ==> r \<subseteq> domain(r)*range(r)"
by blast

lemma field_times_field: "r \<subseteq> Sigma(A,B) ==> r \<subseteq> field(r)*field(r)"
by blast

lemma relation_field_times_field: "relation(r) ==> r \<subseteq> field(r)*field(r)"
by (simp add: relation_def, blast)

lemma field_of_prod: "field(A*A) = A"
by blast

lemma field_0 [simp]: "field(0) = 0"
by blast

lemma field_cons [simp]: "field(cons(<a,b>,r)) = cons(a, cons(b, field(r)))"
by blast

lemma field_Un_eq [simp]: "field(A \<union> B) = field(A) \<union> field(B)"
by blast

lemma field_Int_subset: "field(A \<inter> B) \<subseteq> field(A) \<inter> field(B)"
by blast

lemma field_Diff_subset: "field(A) - field(B) \<subseteq> field(A - B)"
by blast

lemma field_converse [simp]: "field(converse(r)) = field(r)"
by blast

(** The Union of a set of relations is a relation -- Lemma for fun_Union **)
lemma rel_Union: "(\<forall>x\<in>S. \<exists>A B. x \<subseteq> A*B) ==>
                  \<Union>(S) \<subseteq> domain(\<Union>(S)) * range(\<Union>(S))"
by blast

(** The Union of 2 relations is a relation (Lemma for fun_Un)  **)
lemma rel_Un: "[| r \<subseteq> A*B;  s \<subseteq> C*D |] ==> (r \<union> s) \<subseteq> (A \<union> C) * (B \<union> D)"
by blast

lemma domain_Diff_eq: "[| <a,c> \<in> r; c\<noteq>b |] ==> domain(r-{<a,b>}) = domain(r)"
by blast

lemma range_Diff_eq: "[| <c,b> \<in> r; c\<noteq>a |] ==> range(r-{<a,b>}) = range(r)"
by blast


subsection{*Image of a Set under a Function or Relation*}

lemma image_iff: "b \<in> r``A \<longleftrightarrow> (\<exists>x\<in>A. <x,b>\<in>r)"
by (unfold image_def, blast)

lemma image_singleton_iff: "b \<in> r``{a} \<longleftrightarrow> <a,b>\<in>r"
by (rule image_iff [THEN iff_trans], blast)

lemma imageI [intro]: "[| <a,b>\<in> r;  a\<in>A |] ==> b \<in> r``A"
by (unfold image_def, blast)

lemma imageE [elim!]:
    "[| b: r``A;  !!x.[| <x,b>\<in> r;  x\<in>A |] ==> P |] ==> P"
by (unfold image_def, blast)

lemma image_subset: "r \<subseteq> A*B ==> r``C \<subseteq> B"
by blast

lemma image_0 [simp]: "r``0 = 0"
by blast

lemma image_Un [simp]: "r``(A \<union> B) = (r``A) \<union> (r``B)"
by blast

lemma image_UN: "r `` (\<Union>x\<in>A. B(x)) = (\<Union>x\<in>A. r `` B(x))"
by blast

lemma Collect_image_eq:
     "{z \<in> Sigma(A,B). P(z)} `` C = (\<Union>x \<in> A. {y \<in> B(x). x \<in> C & P(<x,y>)})"
by blast

lemma image_Int_subset: "r``(A \<inter> B) \<subseteq> (r``A) \<inter> (r``B)"
by blast

lemma image_Int_square_subset: "(r \<inter> A*A)``B \<subseteq> (r``B) \<inter> A"
by blast

lemma image_Int_square: "B\<subseteq>A ==> (r \<inter> A*A)``B = (r``B) \<inter> A"
by blast


(*Image laws for special relations*)
lemma image_0_left [simp]: "0``A = 0"
by blast

lemma image_Un_left: "(r \<union> s)``A = (r``A) \<union> (s``A)"
by blast

lemma image_Int_subset_left: "(r \<inter> s)``A \<subseteq> (r``A) \<inter> (s``A)"
by blast


subsection{*Inverse Image of a Set under a Function or Relation*}

lemma vimage_iff:
    "a \<in> r-``B \<longleftrightarrow> (\<exists>y\<in>B. <a,y>\<in>r)"
by (unfold vimage_def image_def converse_def, blast)

lemma vimage_singleton_iff: "a \<in> r-``{b} \<longleftrightarrow> <a,b>\<in>r"
by (rule vimage_iff [THEN iff_trans], blast)

lemma vimageI [intro]: "[| <a,b>\<in> r;  b\<in>B |] ==> a \<in> r-``B"
by (unfold vimage_def, blast)

lemma vimageE [elim!]:
    "[| a: r-``B;  !!x.[| <a,x>\<in> r;  x\<in>B |] ==> P |] ==> P"
apply (unfold vimage_def, blast)
done

lemma vimage_subset: "r \<subseteq> A*B ==> r-``C \<subseteq> A"
apply (unfold vimage_def)
apply (erule converse_type [THEN image_subset])
done

lemma vimage_0 [simp]: "r-``0 = 0"
by blast

lemma vimage_Un [simp]: "r-``(A \<union> B) = (r-``A) \<union> (r-``B)"
by blast

lemma vimage_Int_subset: "r-``(A \<inter> B) \<subseteq> (r-``A) \<inter> (r-``B)"
by blast

(*NOT suitable for rewriting*)
lemma vimage_eq_UN: "f -``B = (\<Union>y\<in>B. f-``{y})"
by blast

lemma function_vimage_Int:
     "function(f) ==> f-``(A \<inter> B) = (f-``A)  \<inter>  (f-``B)"
by (unfold function_def, blast)

lemma function_vimage_Diff: "function(f) ==> f-``(A-B) = (f-``A) - (f-``B)"
by (unfold function_def, blast)

lemma function_image_vimage: "function(f) ==> f `` (f-`` A) \<subseteq> A"
by (unfold function_def, blast)

lemma vimage_Int_square_subset: "(r \<inter> A*A)-``B \<subseteq> (r-``B) \<inter> A"
by blast

lemma vimage_Int_square: "B\<subseteq>A ==> (r \<inter> A*A)-``B = (r-``B) \<inter> A"
by blast



(*Invese image laws for special relations*)
lemma vimage_0_left [simp]: "0-``A = 0"
by blast

lemma vimage_Un_left: "(r \<union> s)-``A = (r-``A) \<union> (s-``A)"
by blast

lemma vimage_Int_subset_left: "(r \<inter> s)-``A \<subseteq> (r-``A) \<inter> (s-``A)"
by blast


(** Converse **)

lemma converse_Un [simp]: "converse(A \<union> B) = converse(A) \<union> converse(B)"
by blast

lemma converse_Int [simp]: "converse(A \<inter> B) = converse(A) \<inter> converse(B)"
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

lemma Pow_insert: "Pow (cons(a,A)) = Pow(A) \<union> {cons(a,X) . X: Pow(A)}"
apply (rule equalityI, safe)
apply (erule swap)
apply (rule_tac a = "x-{a}" in RepFun_eqI, auto)
done

lemma Un_Pow_subset: "Pow(A) \<union> Pow(B) \<subseteq> Pow(A \<union> B)"
by blast

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow(B(x))) \<subseteq> Pow(\<Union>x\<in>A. B(x))"
by blast

lemma subset_Pow_Union: "A \<subseteq> Pow(\<Union>(A))"
by blast

lemma Union_Pow_eq [simp]: "\<Union>(Pow(A)) = A"
by blast

lemma Union_Pow_iff: "\<Union>(A) \<in> Pow(B) \<longleftrightarrow> A \<in> Pow(Pow(B))"
by blast

lemma Pow_Int_eq [simp]: "Pow(A \<inter> B) = Pow(A) \<inter> Pow(B)"
by blast

lemma Pow_INT_eq: "A\<noteq>0 ==> Pow(\<Inter>x\<in>A. B(x)) = (\<Inter>x\<in>A. Pow(B(x)))"
by (blast elim!: not_emptyE)


subsection{*RepFun*}

lemma RepFun_subset: "[| !!x. x\<in>A ==> f(x) \<in> B |] ==> {f(x). x\<in>A} \<subseteq> B"
by blast

lemma RepFun_eq_0_iff [simp]: "{f(x).x\<in>A}=0 \<longleftrightarrow> A=0"
by blast

lemma RepFun_constant [simp]: "{c. x\<in>A} = (if A=0 then 0 else {c})"
by force


subsection{*Collect*}

lemma Collect_subset: "Collect(A,P) \<subseteq> A"
by blast

lemma Collect_Un: "Collect(A \<union> B, P) = Collect(A,P) \<union> Collect(B,P)"
by blast

lemma Collect_Int: "Collect(A \<inter> B, P) = Collect(A,P) \<inter> Collect(B,P)"
by blast

lemma Collect_Diff: "Collect(A - B, P) = Collect(A,P) - Collect(B,P)"
by blast

lemma Collect_cons: "{x\<in>cons(a,B). P(x)} =
      (if P(a) then cons(a, {x\<in>B. P(x)}) else {x\<in>B. P(x)})"
by (simp, blast)

lemma Int_Collect_self_eq: "A \<inter> Collect(A,P) = Collect(A,P)"
by blast

lemma Collect_Collect_eq [simp]:
     "Collect(Collect(A,P), Q) = Collect(A, %x. P(x) & Q(x))"
by blast

lemma Collect_Int_Collect_eq:
     "Collect(A,P) \<inter> Collect(A,Q) = Collect(A, %x. P(x) & Q(x))"
by blast

lemma Collect_Union_eq [simp]:
     "Collect(\<Union>x\<in>A. B(x), P) = (\<Union>x\<in>A. Collect(B(x), P))"
by blast

lemma Collect_Int_left: "{x\<in>A. P(x)} \<inter> B = {x \<in> A \<inter> B. P(x)}"
by blast

lemma Collect_Int_right: "A \<inter> {x\<in>B. P(x)} = {x \<in> A \<inter> B. P(x)}"
by blast

lemma Collect_disj_eq: "{x\<in>A. P(x) | Q(x)} = Collect(A, P) \<union> Collect(A, Q)"
by blast

lemma Collect_conj_eq: "{x\<in>A. P(x) & Q(x)} = Collect(A, P) \<inter> Collect(A, Q)"
by blast

lemmas subset_SIs = subset_refl cons_subsetI subset_consI
                    Union_least UN_least Un_least
                    Inter_greatest Int_greatest RepFun_subset
                    Un_upper1 Un_upper2 Int_lower1 Int_lower2

ML {*
val subset_cs =
  claset_of (@{context}
    delrules [@{thm subsetI}, @{thm subsetCE}]
    addSIs @{thms subset_SIs}
    addIs  [@{thm Union_upper}, @{thm Inter_lower}]
    addSEs [@{thm cons_subsetE}]);

val ZF_cs = claset_of (@{context} delrules [@{thm equalityI}]);
*}

end

