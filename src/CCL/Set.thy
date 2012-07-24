header {* Extending FOL by a modified version of HOL set theory *}

theory Set
imports "~~/src/FOL/FOL"
begin

declare [[eta_contract]]

typedecl 'a set
arities set :: ("term") "term"

consts
  Collect       :: "['a => o] => 'a set"                    (*comprehension*)
  Compl         :: "('a set) => 'a set"                     (*complement*)
  Int           :: "['a set, 'a set] => 'a set"         (infixl "Int" 70)
  Un            :: "['a set, 'a set] => 'a set"         (infixl "Un" 65)
  Union         :: "(('a set)set) => 'a set"                (*...of a set*)
  Inter         :: "(('a set)set) => 'a set"                (*...of a set*)
  UNION         :: "['a set, 'a => 'b set] => 'b set"       (*general*)
  INTER         :: "['a set, 'a => 'b set] => 'b set"       (*general*)
  Ball          :: "['a set, 'a => o] => o"                 (*bounded quants*)
  Bex           :: "['a set, 'a => o] => o"                 (*bounded quants*)
  mono          :: "['a set => 'b set] => o"                (*monotonicity*)
  mem           :: "['a, 'a set] => o"                  (infixl ":" 50) (*membership*)
  subset        :: "['a set, 'a set] => o"              (infixl "<=" 50)
  singleton     :: "'a => 'a set"                       ("{_}")
  empty         :: "'a set"                             ("{}")

syntax
  "_Coll"       :: "[idt, o] => 'a set"                 ("(1{_./ _})") (*collection*)

  (* Big Intersection / Union *)

  "_INTER"      :: "[idt, 'a set, 'b set] => 'b set"    ("(INT _:_./ _)" [0, 0, 0] 10)
  "_UNION"      :: "[idt, 'a set, 'b set] => 'b set"    ("(UN _:_./ _)" [0, 0, 0] 10)

  (* Bounded Quantifiers *)

  "_Ball"       :: "[idt, 'a set, o] => o"              ("(ALL _:_./ _)" [0, 0, 0] 10)
  "_Bex"        :: "[idt, 'a set, o] => o"              ("(EX _:_./ _)" [0, 0, 0] 10)

translations
  "{x. P}"      == "CONST Collect(%x. P)"
  "INT x:A. B"  == "CONST INTER(A, %x. B)"
  "UN x:A. B"   == "CONST UNION(A, %x. B)"
  "ALL x:A. P"  == "CONST Ball(A, %x. P)"
  "EX x:A. P"   == "CONST Bex(A, %x. P)"

axiomatization where
  mem_Collect_iff: "(a : {x. P(x)}) <-> P(a)" and
  set_extension: "A = B <-> (ALL x. x:A <-> x:B)"

defs
  Ball_def:      "Ball(A, P)  == ALL x. x:A --> P(x)"
  Bex_def:       "Bex(A, P)   == EX x. x:A & P(x)"
  mono_def:      "mono(f)     == (ALL A B. A <= B --> f(A) <= f(B))"
  subset_def:    "A <= B      == ALL x:A. x:B"
  singleton_def: "{a}         == {x. x=a}"
  empty_def:     "{}          == {x. False}"
  Un_def:        "A Un B      == {x. x:A | x:B}"
  Int_def:       "A Int B     == {x. x:A & x:B}"
  Compl_def:     "Compl(A)    == {x. ~x:A}"
  INTER_def:     "INTER(A, B) == {y. ALL x:A. y: B(x)}"
  UNION_def:     "UNION(A, B) == {y. EX x:A. y: B(x)}"
  Inter_def:     "Inter(S)    == (INT x:S. x)"
  Union_def:     "Union(S)    == (UN x:S. x)"


lemma CollectI: "[| P(a) |] ==> a : {x. P(x)}"
  apply (rule mem_Collect_iff [THEN iffD2])
  apply assumption
  done

lemma CollectD: "[| a : {x. P(x)} |] ==> P(a)"
  apply (erule mem_Collect_iff [THEN iffD1])
  done

lemmas CollectE = CollectD [elim_format]

lemma set_ext: "[| !!x. x:A <-> x:B |] ==> A = B"
  apply (rule set_extension [THEN iffD2])
  apply simp
  done


subsection {* Bounded quantifiers *}

lemma ballI: "[| !!x. x:A ==> P(x) |] ==> ALL x:A. P(x)"
  by (simp add: Ball_def)

lemma bspec: "[| ALL x:A. P(x);  x:A |] ==> P(x)"
  by (simp add: Ball_def)

lemma ballE: "[| ALL x:A. P(x);  P(x) ==> Q;  ~ x:A ==> Q |] ==> Q"
  unfolding Ball_def by blast

lemma bexI: "[| P(x);  x:A |] ==> EX x:A. P(x)"
  unfolding Bex_def by blast

lemma bexCI: "[| EX x:A. ~P(x) ==> P(a);  a:A |] ==> EX x:A. P(x)"
  unfolding Bex_def by blast

lemma bexE: "[| EX x:A. P(x);  !!x. [| x:A; P(x) |] ==> Q  |] ==> Q"
  unfolding Bex_def by blast

(*Trival rewrite rule;   (! x:A.P)=P holds only if A is nonempty!*)
lemma ball_rew: "(ALL x:A. True) <-> True"
  by (blast intro: ballI)


subsection {* Congruence rules *}

lemma ball_cong:
  "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==>
    (ALL x:A. P(x)) <-> (ALL x:A'. P'(x))"
  by (blast intro: ballI elim: ballE)

lemma bex_cong:
  "[| A=A';  !!x. x:A' ==> P(x) <-> P'(x) |] ==>
    (EX x:A. P(x)) <-> (EX x:A'. P'(x))"
  by (blast intro: bexI elim: bexE)


subsection {* Rules for subsets *}

lemma subsetI: "(!!x. x:A ==> x:B) ==> A <= B"
  unfolding subset_def by (blast intro: ballI)

(*Rule in Modus Ponens style*)
lemma subsetD: "[| A <= B;  c:A |] ==> c:B"
  unfolding subset_def by (blast elim: ballE)

(*Classical elimination rule*)
lemma subsetCE: "[| A <= B;  ~(c:A) ==> P;  c:B ==> P |] ==> P"
  by (blast dest: subsetD)

lemma subset_refl: "A <= A"
  by (blast intro: subsetI)

lemma subset_trans: "[| A<=B;  B<=C |] ==> A<=C"
  by (blast intro: subsetI dest: subsetD)


subsection {* Rules for equality *}

(*Anti-symmetry of the subset relation*)
lemma subset_antisym: "[| A <= B;  B <= A |] ==> A = B"
  by (blast intro: set_ext dest: subsetD)

lemmas equalityI = subset_antisym

(* Equality rules from ZF set theory -- are they appropriate here? *)
lemma equalityD1: "A = B ==> A<=B"
  and equalityD2: "A = B ==> B<=A"
  by (simp_all add: subset_refl)

lemma equalityE: "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P"
  by (simp add: subset_refl)

lemma equalityCE:
    "[| A = B;  [| c:A; c:B |] ==> P;  [| ~ c:A; ~ c:B |] ==> P |]  ==>  P"
  by (blast elim: equalityE subsetCE)

lemma trivial_set: "{x. x:A} = A"
  by (blast intro: equalityI subsetI CollectI dest: CollectD)


subsection {* Rules for binary union *}

lemma UnI1: "c:A ==> c : A Un B"
  and UnI2: "c:B ==> c : A Un B"
  unfolding Un_def by (blast intro: CollectI)+

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI: "(~c:B ==> c:A) ==> c : A Un B"
  by (blast intro: UnI1 UnI2)

lemma UnE: "[| c : A Un B;  c:A ==> P;  c:B ==> P |] ==> P"
  unfolding Un_def by (blast dest: CollectD)


subsection {* Rules for small intersection *}

lemma IntI: "[| c:A;  c:B |] ==> c : A Int B"
  unfolding Int_def by (blast intro: CollectI)

lemma IntD1: "c : A Int B ==> c:A"
  and IntD2: "c : A Int B ==> c:B"
  unfolding Int_def by (blast dest: CollectD)+

lemma IntE: "[| c : A Int B;  [| c:A; c:B |] ==> P |] ==> P"
  by (blast dest: IntD1 IntD2)


subsection {* Rules for set complement *}

lemma ComplI: "[| c:A ==> False |] ==> c : Compl(A)"
  unfolding Compl_def by (blast intro: CollectI)

(*This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the notional
  turnstile...*)
lemma ComplD: "[| c : Compl(A) |] ==> ~c:A"
  unfolding Compl_def by (blast dest: CollectD)

lemmas ComplE = ComplD [elim_format]


subsection {* Empty sets *}

lemma empty_eq: "{x. False} = {}"
  by (simp add: empty_def)

lemma emptyD: "a : {} ==> P"
  unfolding empty_def by (blast dest: CollectD)

lemmas emptyE = emptyD [elim_format]

lemma not_emptyD:
  assumes "~ A={}"
  shows "EX x. x:A"
proof -
  have "\<not> (EX x. x:A) \<Longrightarrow> A = {}"
    by (rule equalityI) (blast intro!: subsetI elim!: emptyD)+
  with assms show ?thesis by blast
qed


subsection {* Singleton sets *}

lemma singletonI: "a : {a}"
  unfolding singleton_def by (blast intro: CollectI)

lemma singletonD: "b : {a} ==> b=a"
  unfolding singleton_def by (blast dest: CollectD)

lemmas singletonE = singletonD [elim_format]


subsection {* Unions of families *}

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma UN_I: "[| a:A;  b: B(a) |] ==> b: (UN x:A. B(x))"
  unfolding UNION_def by (blast intro: bexI CollectI)

lemma UN_E: "[| b : (UN x:A. B(x));  !!x.[| x:A;  b: B(x) |] ==> R |] ==> R"
  unfolding UNION_def by (blast dest: CollectD elim: bexE)

lemma UN_cong:
  "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==>
    (UN x:A. C(x)) = (UN x:B. D(x))"
  by (simp add: UNION_def cong: bex_cong)


subsection {* Intersections of families *}

lemma INT_I: "(!!x. x:A ==> b: B(x)) ==> b : (INT x:A. B(x))"
  unfolding INTER_def by (blast intro: CollectI ballI)

lemma INT_D: "[| b : (INT x:A. B(x));  a:A |] ==> b: B(a)"
  unfolding INTER_def by (blast dest: CollectD bspec)

(*"Classical" elimination rule -- does not require proving X:C *)
lemma INT_E: "[| b : (INT x:A. B(x));  b: B(a) ==> R;  ~ a:A ==> R |] ==> R"
  unfolding INTER_def by (blast dest: CollectD bspec)

lemma INT_cong:
  "[| A=B;  !!x. x:B ==> C(x) = D(x) |] ==>
    (INT x:A. C(x)) = (INT x:B. D(x))"
  by (simp add: INTER_def cong: ball_cong)


subsection {* Rules for Unions *}

(*The order of the premises presupposes that C is rigid; A may be flexible*)
lemma UnionI: "[| X:C;  A:X |] ==> A : Union(C)"
  unfolding Union_def by (blast intro: UN_I)

lemma UnionE: "[| A : Union(C);  !!X.[| A:X;  X:C |] ==> R |] ==> R"
  unfolding Union_def by (blast elim: UN_E)


subsection {* Rules for Inter *}

lemma InterI: "[| !!X. X:C ==> A:X |] ==> A : Inter(C)"
  unfolding Inter_def by (blast intro: INT_I)

(*A "destruct" rule -- every X in C contains A as an element, but
  A:X can hold when X:C does not!  This rule is analogous to "spec". *)
lemma InterD: "[| A : Inter(C);  X:C |] ==> A:X"
  unfolding Inter_def by (blast dest: INT_D)

(*"Classical" elimination rule -- does not require proving X:C *)
lemma InterE: "[| A : Inter(C);  A:X ==> R;  ~ X:C ==> R |] ==> R"
  unfolding Inter_def by (blast elim: INT_E)


section {* Derived rules involving subsets; Union and Intersection as lattice operations *}

subsection {* Big Union -- least upper bound of a set *}

lemma Union_upper: "B:A ==> B <= Union(A)"
  by (blast intro: subsetI UnionI)

lemma Union_least: "[| !!X. X:A ==> X<=C |] ==> Union(A) <= C"
  by (blast intro: subsetI dest: subsetD elim: UnionE)


subsection {* Big Intersection -- greatest lower bound of a set *}

lemma Inter_lower: "B:A ==> Inter(A) <= B"
  by (blast intro: subsetI dest: InterD)

lemma Inter_greatest: "[| !!X. X:A ==> C<=X |] ==> C <= Inter(A)"
  by (blast intro: subsetI InterI dest: subsetD)


subsection {* Finite Union -- the least upper bound of 2 sets *}

lemma Un_upper1: "A <= A Un B"
  by (blast intro: subsetI UnI1)

lemma Un_upper2: "B <= A Un B"
  by (blast intro: subsetI UnI2)

lemma Un_least: "[| A<=C;  B<=C |] ==> A Un B <= C"
  by (blast intro: subsetI elim: UnE dest: subsetD)


subsection {* Finite Intersection -- the greatest lower bound of 2 sets *}

lemma Int_lower1: "A Int B <= A"
  by (blast intro: subsetI elim: IntE)

lemma Int_lower2: "A Int B <= B"
  by (blast intro: subsetI elim: IntE)

lemma Int_greatest: "[| C<=A;  C<=B |] ==> C <= A Int B"
  by (blast intro: subsetI IntI dest: subsetD)


subsection {* Monotonicity *}

lemma monoI: "[| !!A B. A <= B ==> f(A) <= f(B) |] ==> mono(f)"
  unfolding mono_def by blast

lemma monoD: "[| mono(f);  A <= B |] ==> f(A) <= f(B)"
  unfolding mono_def by blast

lemma mono_Un: "mono(f) ==> f(A) Un f(B) <= f(A Un B)"
  by (blast intro: Un_least dest: monoD intro: Un_upper1 Un_upper2)

lemma mono_Int: "mono(f) ==> f(A Int B) <= f(A) Int f(B)"
  by (blast intro: Int_greatest dest: monoD intro: Int_lower1 Int_lower2)


subsection {* Automated reasoning setup *}

lemmas [intro!] = ballI subsetI InterI INT_I CollectI ComplI IntI UnCI singletonI
  and [intro] = bexI UnionI UN_I
  and [elim!] = bexE UnionE UN_E CollectE ComplE IntE UnE emptyE singletonE
  and [elim] = ballE InterD InterE INT_D INT_E subsetD subsetCE

lemma mem_rews:
  "(a : A Un B)   <->  (a:A | a:B)"
  "(a : A Int B)  <->  (a:A & a:B)"
  "(a : Compl(B)) <->  (~a:B)"
  "(a : {b})      <->  (a=b)"
  "(a : {})       <->   False"
  "(a : {x. P(x)}) <->  P(a)"
  by blast+

lemmas [simp] = trivial_set empty_eq mem_rews
  and [cong] = ball_cong bex_cong INT_cong UN_cong


section {* Equalities involving union, intersection, inclusion, etc. *}

subsection {* Binary Intersection *}

lemma Int_absorb: "A Int A = A"
  by (blast intro: equalityI)

lemma Int_commute: "A Int B  =  B Int A"
  by (blast intro: equalityI)

lemma Int_assoc: "(A Int B) Int C  =  A Int (B Int C)"
  by (blast intro: equalityI)

lemma Int_Un_distrib: "(A Un B) Int C  =  (A Int C) Un (B Int C)"
  by (blast intro: equalityI)

lemma subset_Int_eq: "(A<=B) <-> (A Int B = A)"
  by (blast intro: equalityI elim: equalityE)


subsection {* Binary Union *}

lemma Un_absorb: "A Un A = A"
  by (blast intro: equalityI)

lemma Un_commute: "A Un B  =  B Un A"
  by (blast intro: equalityI)

lemma Un_assoc: "(A Un B) Un C  =  A Un (B Un C)"
  by (blast intro: equalityI)

lemma Un_Int_distrib: "(A Int B) Un C  =  (A Un C) Int (B Un C)"
  by (blast intro: equalityI)

lemma Un_Int_crazy:
    "(A Int B) Un (B Int C) Un (C Int A) = (A Un B) Int (B Un C) Int (C Un A)"
  by (blast intro: equalityI)

lemma subset_Un_eq: "(A<=B) <-> (A Un B = B)"
  by (blast intro: equalityI elim: equalityE)


subsection {* Simple properties of @{text "Compl"} -- complement of a set *}

lemma Compl_disjoint: "A Int Compl(A) = {x. False}"
  by (blast intro: equalityI)

lemma Compl_partition: "A Un Compl(A) = {x. True}"
  by (blast intro: equalityI)

lemma double_complement: "Compl(Compl(A)) = A"
  by (blast intro: equalityI)

lemma Compl_Un: "Compl(A Un B) = Compl(A) Int Compl(B)"
  by (blast intro: equalityI)

lemma Compl_Int: "Compl(A Int B) = Compl(A) Un Compl(B)"
  by (blast intro: equalityI)

lemma Compl_UN: "Compl(UN x:A. B(x)) = (INT x:A. Compl(B(x)))"
  by (blast intro: equalityI)

lemma Compl_INT: "Compl(INT x:A. B(x)) = (UN x:A. Compl(B(x)))"
  by (blast intro: equalityI)

(*Halmos, Naive Set Theory, page 16.*)
lemma Un_Int_assoc_eq: "((A Int B) Un C = A Int (B Un C)) <-> (C<=A)"
  by (blast intro: equalityI elim: equalityE)


subsection {* Big Union and Intersection *}

lemma Union_Un_distrib: "Union(A Un B) = Union(A) Un Union(B)"
  by (blast intro: equalityI)

lemma Union_disjoint:
    "(Union(C) Int A = {x. False}) <-> (ALL B:C. B Int A = {x. False})"
  by (blast intro: equalityI elim: equalityE)

lemma Inter_Un_distrib: "Inter(A Un B) = Inter(A) Int Inter(B)"
  by (blast intro: equalityI)


subsection {* Unions and Intersections of Families *}

lemma UN_eq: "(UN x:A. B(x)) = Union({Y. EX x:A. Y=B(x)})"
  by (blast intro: equalityI)

(*Look: it has an EXISTENTIAL quantifier*)
lemma INT_eq: "(INT x:A. B(x)) = Inter({Y. EX x:A. Y=B(x)})"
  by (blast intro: equalityI)

lemma Int_Union_image: "A Int Union(B) = (UN C:B. A Int C)"
  by (blast intro: equalityI)

lemma Un_Inter_image: "A Un Inter(B) = (INT C:B. A Un C)"
  by (blast intro: equalityI)


section {* Monotonicity of various operations *}

lemma Union_mono: "A<=B ==> Union(A) <= Union(B)"
  by blast

lemma Inter_anti_mono: "[| B<=A |] ==> Inter(A) <= Inter(B)"
  by blast

lemma UN_mono:
  "[| A<=B;  !!x. x:A ==> f(x)<=g(x) |] ==>  
    (UN x:A. f(x)) <= (UN x:B. g(x))"
  by blast

lemma INT_anti_mono:
  "[| B<=A;  !!x. x:A ==> f(x)<=g(x) |] ==>  
    (INT x:A. f(x)) <= (INT x:A. g(x))"
  by blast

lemma Un_mono: "[| A<=C;  B<=D |] ==> A Un B <= C Un D"
  by blast

lemma Int_mono: "[| A<=C;  B<=D |] ==> A Int B <= C Int D"
  by blast

lemma Compl_anti_mono: "[| A<=B |] ==> Compl(B) <= Compl(A)"
  by blast

end
