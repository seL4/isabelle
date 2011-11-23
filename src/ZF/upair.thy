(*  Title:      ZF/upair.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge

Observe the order of dependence:
    Upair is defined in terms of Replace
    Un is defined in terms of Upair and Union (similarly for Int)
    cons is defined in terms of Upair and Un
    Ordered pairs and descriptions are defined using cons ("set notation")
*)

header{*Unordered Pairs*}

theory upair imports ZF
uses "Tools/typechk.ML" begin

setup TypeCheck.setup

lemma atomize_ball [symmetric, rulify]:
     "(!!x. x:A ==> P(x)) == Trueprop (ALL x:A. P(x))"
by (simp add: Ball_def atomize_all atomize_imp)


subsection{*Unordered Pairs: constant @{term Upair}*}

lemma Upair_iff [simp]: "c : Upair(a,b) <-> (c=a | c=b)"
by (unfold Upair_def, blast)

lemma UpairI1: "a : Upair(a,b)"
by simp

lemma UpairI2: "b : Upair(a,b)"
by simp

lemma UpairE: "[| a : Upair(b,c);  a=b ==> P;  a=c ==> P |] ==> P"
by (simp, blast)

subsection{*Rules for Binary Union, Defined via @{term Upair}*}

lemma Un_iff [simp]: "c : A Un B <-> (c:A | c:B)"
apply (simp add: Un_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma UnI1: "c : A ==> c : A Un B"
by simp

lemma UnI2: "c : B ==> c : A Un B"
by simp

declare UnI1 [elim?]  UnI2 [elim?]

lemma UnE [elim!]: "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P"
by (simp, blast)

(*Stronger version of the rule above*)
lemma UnE': "[| c : A Un B;  c:A ==> P;  [| c:B;  c~:A |] ==> P |] ==> P"
by (simp, blast)

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI [intro!]: "(c ~: B ==> c : A) ==> c : A Un B"
by (simp, blast)

subsection{*Rules for Binary Intersection, Defined via @{term Upair}*}

lemma Int_iff [simp]: "c : A Int B <-> (c:A & c:B)"
apply (unfold Int_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma IntI [intro!]: "[| c : A;  c : B |] ==> c : A Int B"
by simp

lemma IntD1: "c : A Int B ==> c : A"
by simp

lemma IntD2: "c : A Int B ==> c : B"
by simp

lemma IntE [elim!]: "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P"
by simp


subsection{*Rules for Set Difference, Defined via @{term Upair}*}

lemma Diff_iff [simp]: "c : A-B <-> (c:A & c~:B)"
by (unfold Diff_def, blast)

lemma DiffI [intro!]: "[| c : A;  c ~: B |] ==> c : A - B"
by simp

lemma DiffD1: "c : A - B ==> c : A"
by simp

lemma DiffD2: "c : A - B ==> c ~: B"
by simp

lemma DiffE [elim!]: "[| c : A - B;  [| c:A; c~:B |] ==> P |] ==> P"
by simp


subsection{*Rules for @{term cons}*}

lemma cons_iff [simp]: "a : cons(b,A) <-> (a=b | a:A)"
apply (unfold cons_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

(*risky as a typechecking rule, but solves otherwise unconstrained goals of
the form x : ?A*)
lemma consI1 [simp,TC]: "a : cons(a,B)"
by simp


lemma consI2: "a : B ==> a : cons(b,B)"
by simp

lemma consE [elim!]: "[| a : cons(b,A);  a=b ==> P;  a:A ==> P |] ==> P"
by (simp, blast)

(*Stronger version of the rule above*)
lemma consE':
    "[| a : cons(b,A);  a=b ==> P;  [| a:A;  a~=b |] ==> P |] ==> P"
by (simp, blast)

(*Classical introduction rule*)
lemma consCI [intro!]: "(a~:B ==> a=b) ==> a: cons(b,B)"
by (simp, blast)

lemma cons_not_0 [simp]: "cons(a,B) ~= 0"
by (blast elim: equalityE)

lemmas cons_neq_0 = cons_not_0 [THEN notE]

declare cons_not_0 [THEN not_sym, simp]


subsection{*Singletons*}

lemma singleton_iff: "a : {b} <-> a=b"
by simp

lemma singletonI [intro!]: "a : {a}"
by (rule consI1)

lemmas singletonE = singleton_iff [THEN iffD1, elim_format, elim!]


subsection{*Descriptions*}

lemma the_equality [intro]:
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (THE x. P(x)) = a"
apply (unfold the_def) 
apply (fast dest: subst)
done

(* Only use this if you already know EX!x. P(x) *)
lemma the_equality2: "[| EX! x. P(x);  P(a) |] ==> (THE x. P(x)) = a"
by blast

lemma theI: "EX! x. P(x) ==> P(THE x. P(x))"
apply (erule ex1E)
apply (subst the_equality)
apply (blast+)
done

(*the_cong is no longer necessary: if (ALL y.P(y)<->Q(y)) then 
  (THE x.P(x))  rewrites to  (THE x. Q(x))  *)

(*If it's "undefined", it's zero!*)
lemma the_0: "~ (EX! x. P(x)) ==> (THE x. P(x))=0"
apply (unfold the_def)
apply (blast elim!: ReplaceE)
done

(*Easier to apply than theI: conclusion has only one occurrence of P*)
lemma theI2:
    assumes p1: "~ Q(0) ==> EX! x. P(x)"
        and p2: "!!x. P(x) ==> Q(x)"
    shows "Q(THE x. P(x))"
apply (rule classical)
apply (rule p2)
apply (rule theI)
apply (rule classical)
apply (rule p1)
apply (erule the_0 [THEN subst], assumption)
done

lemma the_eq_trivial [simp]: "(THE x. x = a) = a"
by blast

lemma the_eq_trivial2 [simp]: "(THE x. a = x) = a"
by blast


subsection{*Conditional Terms: @{text "if-then-else"}*}

lemma if_true [simp]: "(if True then a else b) = a"
by (unfold if_def, blast)

lemma if_false [simp]: "(if False then a else b) = b"
by (unfold if_def, blast)

(*Never use with case splitting, or if P is known to be true or false*)
lemma if_cong:
    "[| P<->Q;  Q ==> a=c;  ~Q ==> b=d |]  
     ==> (if P then a else b) = (if Q then c else d)"
by (simp add: if_def cong add: conj_cong)

(*Prevents simplification of x and y: faster and allows the execution
  of functional programs. NOW THE DEFAULT.*)
lemma if_weak_cong: "P<->Q ==> (if P then x else y) = (if Q then x else y)"
by simp

(*Not needed for rewriting, since P would rewrite to True anyway*)
lemma if_P: "P ==> (if P then a else b) = a"
by (unfold if_def, blast)

(*Not needed for rewriting, since P would rewrite to False anyway*)
lemma if_not_P: "~P ==> (if P then a else b) = b"
by (unfold if_def, blast)

lemma split_if [split]:
     "P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))"
by (case_tac Q, simp_all)

(** Rewrite rules for boolean case-splitting: faster than split_if [split]
**)

lemmas split_if_eq1 = split_if [of "%x. x = b"] for b
lemmas split_if_eq2 = split_if [of "%x. a = x"] for x

lemmas split_if_mem1 = split_if [of "%x. x : b"] for b
lemmas split_if_mem2 = split_if [of "%x. a : x"] for x

lemmas split_ifs = split_if_eq1 split_if_eq2 split_if_mem1 split_if_mem2

(*Logically equivalent to split_if_mem2*)
lemma if_iff: "a: (if P then x else y) <-> P & a:x | ~P & a:y"
by simp

lemma if_type [TC]:
    "[| P ==> a: A;  ~P ==> b: A |] ==> (if P then a else b): A"
by simp

(** Splitting IFs in the assumptions **)

lemma split_if_asm: "P(if Q then x else y) <-> (~((Q & ~P(x)) | (~Q & ~P(y))))"
by simp

lemmas if_splits = split_if split_if_asm


subsection{*Consequences of Foundation*}

(*was called mem_anti_sym*)
lemma mem_asym: "[| a:b;  ~P ==> b:a |] ==> P"
apply (rule classical)
apply (rule_tac A1 = "{a,b}" in foundation [THEN disjE])
apply (blast elim!: equalityE)+
done

(*was called mem_anti_refl*)
lemma mem_irrefl: "a:a ==> P"
by (blast intro: mem_asym)

(*mem_irrefl should NOT be added to default databases:
      it would be tried on most goals, making proofs slower!*)

lemma mem_not_refl: "a ~: a"
apply (rule notI)
apply (erule mem_irrefl)
done

(*Good for proving inequalities by rewriting*)
lemma mem_imp_not_eq: "a:A ==> a ~= A"
by (blast elim!: mem_irrefl)

lemma eq_imp_not_mem: "a=A ==> a ~: A"
by (blast intro: elim: mem_irrefl)

subsection{*Rules for Successor*}

lemma succ_iff: "i : succ(j) <-> i=j | i:j"
by (unfold succ_def, blast)

lemma succI1 [simp]: "i : succ(i)"
by (simp add: succ_iff)

lemma succI2: "i : j ==> i : succ(j)"
by (simp add: succ_iff)

lemma succE [elim!]: 
    "[| i : succ(j);  i=j ==> P;  i:j ==> P |] ==> P"
apply (simp add: succ_iff, blast) 
done

(*Classical introduction rule*)
lemma succCI [intro!]: "(i~:j ==> i=j) ==> i: succ(j)"
by (simp add: succ_iff, blast)

lemma succ_not_0 [simp]: "succ(n) ~= 0"
by (blast elim!: equalityE)

lemmas succ_neq_0 = succ_not_0 [THEN notE, elim!]

declare succ_not_0 [THEN not_sym, simp]
declare sym [THEN succ_neq_0, elim!]

(* succ(c) <= B ==> c : B *)
lemmas succ_subsetD = succI1 [THEN [2] subsetD]

(* succ(b) ~= b *)
lemmas succ_neq_self = succI1 [THEN mem_imp_not_eq, THEN not_sym]

lemma succ_inject_iff [simp]: "succ(m) = succ(n) <-> m=n"
by (blast elim: mem_asym elim!: equalityE)

lemmas succ_inject = succ_inject_iff [THEN iffD1, dest!]


subsection{*Miniscoping of the Bounded Universal Quantifier*}

lemma ball_simps1:
     "(ALL x:A. P(x) & Q)   <-> (ALL x:A. P(x)) & (A=0 | Q)"
     "(ALL x:A. P(x) | Q)   <-> ((ALL x:A. P(x)) | Q)"
     "(ALL x:A. P(x) --> Q) <-> ((EX x:A. P(x)) --> Q)"
     "(~(ALL x:A. P(x))) <-> (EX x:A. ~P(x))"
     "(ALL x:0.P(x)) <-> True"
     "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i. P(x))"
     "(ALL x:cons(a,B).P(x)) <-> P(a) & (ALL x:B. P(x))"
     "(ALL x:RepFun(A,f). P(x)) <-> (ALL y:A. P(f(y)))"
     "(ALL x:Union(A).P(x)) <-> (ALL y:A. ALL x:y. P(x))" 
by blast+

lemma ball_simps2:
     "(ALL x:A. P & Q(x))   <-> (A=0 | P) & (ALL x:A. Q(x))"
     "(ALL x:A. P | Q(x))   <-> (P | (ALL x:A. Q(x)))"
     "(ALL x:A. P --> Q(x)) <-> (P --> (ALL x:A. Q(x)))"
by blast+

lemma ball_simps3:
     "(ALL x:Collect(A,Q).P(x)) <-> (ALL x:A. Q(x) --> P(x))"
by blast+

lemmas ball_simps [simp] = ball_simps1 ball_simps2 ball_simps3

lemma ball_conj_distrib:
    "(ALL x:A. P(x) & Q(x)) <-> ((ALL x:A. P(x)) & (ALL x:A. Q(x)))"
by blast


subsection{*Miniscoping of the Bounded Existential Quantifier*}

lemma bex_simps1:
     "(EX x:A. P(x) & Q) <-> ((EX x:A. P(x)) & Q)"
     "(EX x:A. P(x) | Q) <-> (EX x:A. P(x)) | (A~=0 & Q)"
     "(EX x:A. P(x) --> Q) <-> ((ALL x:A. P(x)) --> (A~=0 & Q))"
     "(EX x:0.P(x)) <-> False"
     "(EX x:succ(i).P(x)) <-> P(i) | (EX x:i. P(x))"
     "(EX x:cons(a,B).P(x)) <-> P(a) | (EX x:B. P(x))"
     "(EX x:RepFun(A,f). P(x)) <-> (EX y:A. P(f(y)))"
     "(EX x:Union(A).P(x)) <-> (EX y:A. EX x:y.  P(x))"
     "(~(EX x:A. P(x))) <-> (ALL x:A. ~P(x))"
by blast+

lemma bex_simps2:
     "(EX x:A. P & Q(x)) <-> (P & (EX x:A. Q(x)))"
     "(EX x:A. P | Q(x)) <-> (A~=0 & P) | (EX x:A. Q(x))"
     "(EX x:A. P --> Q(x)) <-> ((A=0 | P) --> (EX x:A. Q(x)))"
by blast+

lemma bex_simps3:
     "(EX x:Collect(A,Q).P(x)) <-> (EX x:A. Q(x) & P(x))"
by blast

lemmas bex_simps [simp] = bex_simps1 bex_simps2 bex_simps3

lemma bex_disj_distrib:
    "(EX x:A. P(x) | Q(x)) <-> ((EX x:A. P(x)) | (EX x:A. Q(x)))"
by blast


(** One-point rule for bounded quantifiers: see HOL/Set.ML **)

lemma bex_triv_one_point1 [simp]: "(EX x:A. x=a) <-> (a:A)"
by blast

lemma bex_triv_one_point2 [simp]: "(EX x:A. a=x) <-> (a:A)"
by blast

lemma bex_one_point1 [simp]: "(EX x:A. x=a & P(x)) <-> (a:A & P(a))"
by blast

lemma bex_one_point2 [simp]: "(EX x:A. a=x & P(x)) <-> (a:A & P(a))"
by blast

lemma ball_one_point1 [simp]: "(ALL x:A. x=a --> P(x)) <-> (a:A --> P(a))"
by blast

lemma ball_one_point2 [simp]: "(ALL x:A. a=x --> P(x)) <-> (a:A --> P(a))"
by blast


subsection{*Miniscoping of the Replacement Operator*}

text{*These cover both @{term Replace} and @{term Collect}*}
lemma Rep_simps [simp]:
     "{x. y:0, R(x,y)} = 0"
     "{x:0. P(x)} = 0"
     "{x:A. Q} = (if Q then A else 0)"
     "RepFun(0,f) = 0"
     "RepFun(succ(i),f) = cons(f(i), RepFun(i,f))"
     "RepFun(cons(a,B),f) = cons(f(a), RepFun(B,f))"
by (simp_all, blast+)


subsection{*Miniscoping of Unions*}

lemma UN_simps1:
     "(UN x:C. cons(a, B(x))) = (if C=0 then 0 else cons(a, UN x:C. B(x)))"
     "(UN x:C. A(x) Un B')   = (if C=0 then 0 else (UN x:C. A(x)) Un B')"
     "(UN x:C. A' Un B(x))   = (if C=0 then 0 else A' Un (UN x:C. B(x)))"
     "(UN x:C. A(x) Int B')  = ((UN x:C. A(x)) Int B')"
     "(UN x:C. A' Int B(x))  = (A' Int (UN x:C. B(x)))"
     "(UN x:C. A(x) - B')    = ((UN x:C. A(x)) - B')"
     "(UN x:C. A' - B(x))    = (if C=0 then 0 else A' - (INT x:C. B(x)))"
apply (simp_all add: Inter_def) 
apply (blast intro!: equalityI )+
done

lemma UN_simps2:
      "(UN x: Union(A). B(x)) = (UN y:A. UN x:y. B(x))"
      "(UN z: (UN x:A. B(x)). C(z)) = (UN  x:A. UN z: B(x). C(z))"
      "(UN x: RepFun(A,f). B(x))     = (UN a:A. B(f(a)))"
by blast+

lemmas UN_simps [simp] = UN_simps1 UN_simps2

text{*Opposite of miniscoping: pull the operator out*}

lemma UN_extend_simps1:
     "(UN x:C. A(x)) Un B   = (if C=0 then B else (UN x:C. A(x) Un B))"
     "((UN x:C. A(x)) Int B) = (UN x:C. A(x) Int B)"
     "((UN x:C. A(x)) - B) = (UN x:C. A(x) - B)"
apply simp_all 
apply blast+
done

lemma UN_extend_simps2:
     "cons(a, UN x:C. B(x)) = (if C=0 then {a} else (UN x:C. cons(a, B(x))))"
     "A Un (UN x:C. B(x))   = (if C=0 then A else (UN x:C. A Un B(x)))"
     "(A Int (UN x:C. B(x))) = (UN x:C. A Int B(x))"
     "A - (INT x:C. B(x))    = (if C=0 then A else (UN x:C. A - B(x)))"
     "(UN y:A. UN x:y. B(x)) = (UN x: Union(A). B(x))"
     "(UN a:A. B(f(a))) = (UN x: RepFun(A,f). B(x))"
apply (simp_all add: Inter_def) 
apply (blast intro!: equalityI)+
done

lemma UN_UN_extend:
     "(UN  x:A. UN z: B(x). C(z)) = (UN z: (UN x:A. B(x)). C(z))"
by blast

lemmas UN_extend_simps = UN_extend_simps1 UN_extend_simps2 UN_UN_extend


subsection{*Miniscoping of Intersections*}

lemma INT_simps1:
     "(INT x:C. A(x) Int B) = (INT x:C. A(x)) Int B"
     "(INT x:C. A(x) - B)   = (INT x:C. A(x)) - B"
     "(INT x:C. A(x) Un B)  = (if C=0 then 0 else (INT x:C. A(x)) Un B)"
by (simp_all add: Inter_def, blast+)

lemma INT_simps2:
     "(INT x:C. A Int B(x)) = A Int (INT x:C. B(x))"
     "(INT x:C. A - B(x))   = (if C=0 then 0 else A - (UN x:C. B(x)))"
     "(INT x:C. cons(a, B(x))) = (if C=0 then 0 else cons(a, INT x:C. B(x)))"
     "(INT x:C. A Un B(x))  = (if C=0 then 0 else A Un (INT x:C. B(x)))"
apply (simp_all add: Inter_def) 
apply (blast intro!: equalityI)+
done

lemmas INT_simps [simp] = INT_simps1 INT_simps2

text{*Opposite of miniscoping: pull the operator out*}


lemma INT_extend_simps1:
     "(INT x:C. A(x)) Int B = (INT x:C. A(x) Int B)"
     "(INT x:C. A(x)) - B = (INT x:C. A(x) - B)"
     "(INT x:C. A(x)) Un B  = (if C=0 then B else (INT x:C. A(x) Un B))"
apply (simp_all add: Inter_def, blast+)
done

lemma INT_extend_simps2:
     "A Int (INT x:C. B(x)) = (INT x:C. A Int B(x))"
     "A - (UN x:C. B(x))   = (if C=0 then A else (INT x:C. A - B(x)))"
     "cons(a, INT x:C. B(x)) = (if C=0 then {a} else (INT x:C. cons(a, B(x))))"
     "A Un (INT x:C. B(x))  = (if C=0 then A else (INT x:C. A Un B(x)))"
apply (simp_all add: Inter_def) 
apply (blast intro!: equalityI)+
done

lemmas INT_extend_simps = INT_extend_simps1 INT_extend_simps2


subsection{*Other simprules*}


(*** Miniscoping: pushing in big Unions, Intersections, quantifiers, etc. ***)

lemma misc_simps [simp]:
     "0 Un A = A"
     "A Un 0 = A"
     "0 Int A = 0"
     "A Int 0 = 0"
     "0 - A = 0"
     "A - 0 = A"
     "Union(0) = 0"
     "Union(cons(b,A)) = b Un Union(A)"
     "Inter({b}) = b"
by blast+

end
