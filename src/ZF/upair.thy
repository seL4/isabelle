(*  Title:      ZF/upair.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge

UNORDERED pairs in Zermelo-Fraenkel Set Theory 

Observe the order of dependence:
    Upair is defined in terms of Replace
    Un is defined in terms of Upair and Union (similarly for Int)
    cons is defined in terms of Upair and Un
    Ordered pairs and descriptions are defined using cons ("set notation")
*)

theory upair = ZF
files "Tools/typechk":

setup TypeCheck.setup
declare atomize_ball [symmetric, rulify]

(*belongs to theory ZF*)
declare bspec [dest?]

(*** Lemmas about power sets  ***)

lemmas Pow_bottom = empty_subsetI [THEN PowI] (* 0 : Pow(B) *)
lemmas Pow_top = subset_refl [THEN PowI] (* A : Pow(A) *)


(*** Unordered pairs - Upair ***)

lemma Upair_iff [simp]: "c : Upair(a,b) <-> (c=a | c=b)"
by (unfold Upair_def, blast)

lemma UpairI1: "a : Upair(a,b)"
by simp

lemma UpairI2: "b : Upair(a,b)"
by simp

lemma UpairE:
    "[| a : Upair(b,c);  a=b ==> P;  a=c ==> P |] ==> P"
apply simp
apply blast 
done

(*** Rules for binary union -- Un -- defined via Upair ***)

lemma Un_iff [simp]: "c : A Un B <-> (c:A | c:B)"
apply (simp add: Un_def)
apply (blast intro: UpairI1 UpairI2 elim: UpairE)
done

lemma UnI1: "c : A ==> c : A Un B"
by simp

lemma UnI2: "c : B ==> c : A Un B"
by simp

(*belongs to theory upair*)
declare UnI1 [elim?]  UnI2 [elim?]

lemma UnE [elim!]: "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P"
apply simp 
apply blast 
done

(*Stronger version of the rule above*)
lemma UnE': "[| c : A Un B;  c:A ==> P;  [| c:B;  c~:A |] ==> P |] ==> P"
apply simp 
apply blast 
done

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI [intro!]: "(c ~: B ==> c : A) ==> c : A Un B"
apply simp
apply blast
done


(*** Rules for small intersection -- Int -- defined via Upair ***)

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


(*** Rules for set difference -- defined via Upair ***)

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


(*** Rules for cons -- defined via Un and Upair ***)

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

lemma consE [elim!]:
    "[| a : cons(b,A);  a=b ==> P;  a:A ==> P |] ==> P"
apply simp 
apply blast 
done

(*Stronger version of the rule above*)
lemma consE':
    "[| a : cons(b,A);  a=b ==> P;  [| a:A;  a~=b |] ==> P |] ==> P"
apply simp 
apply blast 
done

(*Classical introduction rule*)
lemma consCI [intro!]: "(a~:B ==> a=b) ==> a: cons(b,B)"
apply simp
apply blast
done

lemma cons_not_0 [simp]: "cons(a,B) ~= 0"
by (blast elim: equalityE)

lemmas cons_neq_0 = cons_not_0 [THEN notE, standard]

declare cons_not_0 [THEN not_sym, simp]


(*** Singletons - using cons ***)

lemma singleton_iff: "a : {b} <-> a=b"
by simp

lemma singletonI [intro!]: "a : {a}"
by (rule consI1)

lemmas singletonE = singleton_iff [THEN iffD1, elim_format, standard, elim!]


(*** Rules for Descriptions ***)

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

(*** if -- a conditional expression for formulae ***)

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

lemma split_if: "P(if Q then x else y) <-> ((Q --> P(x)) & (~Q --> P(y)))"
(*no case_tac yet!*)
apply (rule_tac P=Q in case_split_thm, simp_all)
done

(** Rewrite rules for boolean case-splitting: faster than 
	addsplits[split_if]
**)

lemmas split_if_eq1 = split_if [of "%x. x = b", standard]
lemmas split_if_eq2 = split_if [of "%x. a = x", standard]

lemmas split_if_mem1 = split_if [of "%x. x : b", standard]
lemmas split_if_mem2 = split_if [of "%x. a : x", standard]

lemmas split_ifs = split_if_eq1 split_if_eq2 split_if_mem1 split_if_mem2

(*Logically equivalent to split_if_mem2*)
lemma if_iff: "a: (if P then x else y) <-> P & a:x | ~P & a:y"
by (simp split add: split_if)

lemma if_type [TC]:
    "[| P ==> a: A;  ~P ==> b: A |] ==> (if P then a else b): A"
by (simp split add: split_if)


(*** Foundation lemmas ***)

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

(*** Rules for succ ***)

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

lemmas succ_neq_0 = succ_not_0 [THEN notE, standard, elim!]

declare succ_not_0 [THEN not_sym, simp]
declare sym [THEN succ_neq_0, elim!]

(* succ(c) <= B ==> c : B *)
lemmas succ_subsetD = succI1 [THEN [2] subsetD]

(* succ(b) ~= b *)
lemmas succ_neq_self = succI1 [THEN mem_imp_not_eq, THEN not_sym, standard]

lemma succ_inject_iff [simp]: "succ(m) = succ(n) <-> m=n"
by (blast elim: mem_asym elim!: equalityE)

lemmas succ_inject = succ_inject_iff [THEN iffD1, standard, dest!]

ML
{*
val Pow_bottom = thm "Pow_bottom";
val Pow_top = thm "Pow_top";
val Upair_iff = thm "Upair_iff";
val UpairI1 = thm "UpairI1";
val UpairI2 = thm "UpairI2";
val UpairE = thm "UpairE";
val Un_iff = thm "Un_iff";
val UnI1 = thm "UnI1";
val UnI2 = thm "UnI2";
val UnE = thm "UnE";
val UnE' = thm "UnE'";
val UnCI = thm "UnCI";
val Int_iff = thm "Int_iff";
val IntI = thm "IntI";
val IntD1 = thm "IntD1";
val IntD2 = thm "IntD2";
val IntE = thm "IntE";
val Diff_iff = thm "Diff_iff";
val DiffI = thm "DiffI";
val DiffD1 = thm "DiffD1";
val DiffD2 = thm "DiffD2";
val DiffE = thm "DiffE";
val cons_iff = thm "cons_iff";
val consI1 = thm "consI1";
val consI2 = thm "consI2";
val consE = thm "consE";
val consE' = thm "consE'";
val consCI = thm "consCI";
val cons_not_0 = thm "cons_not_0";
val cons_neq_0 = thm "cons_neq_0";
val singleton_iff = thm "singleton_iff";
val singletonI = thm "singletonI";
val singletonE = thm "singletonE";
val the_equality = thm "the_equality";
val the_equality2 = thm "the_equality2";
val theI = thm "theI";
val the_0 = thm "the_0";
val theI2 = thm "theI2";
val if_true = thm "if_true";
val if_false = thm "if_false";
val if_cong = thm "if_cong";
val if_weak_cong = thm "if_weak_cong";
val if_P = thm "if_P";
val if_not_P = thm "if_not_P";
val split_if = thm "split_if";
val split_if_eq1 = thm "split_if_eq1";
val split_if_eq2 = thm "split_if_eq2";
val split_if_mem1 = thm "split_if_mem1";
val split_if_mem2 = thm "split_if_mem2";
val if_iff = thm "if_iff";
val if_type = thm "if_type";
val mem_asym = thm "mem_asym";
val mem_irrefl = thm "mem_irrefl";
val mem_not_refl = thm "mem_not_refl";
val mem_imp_not_eq = thm "mem_imp_not_eq";
val succ_iff = thm "succ_iff";
val succI1 = thm "succI1";
val succI2 = thm "succI2";
val succE = thm "succE";
val succCI = thm "succCI";
val succ_not_0 = thm "succ_not_0";
val succ_neq_0 = thm "succ_neq_0";
val succ_subsetD = thm "succ_subsetD";
val succ_neq_self = thm "succ_neq_self";
val succ_inject_iff = thm "succ_inject_iff";
val succ_inject = thm "succ_inject";

val split_ifs = thms "split_ifs";
*}

end
