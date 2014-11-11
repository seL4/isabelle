section {* Extending FOL by a modified version of HOL set theory *}

theory Set
imports "~~/src/FOL/FOL"
begin

declare [[eta_contract]]

typedecl 'a set
instance set :: ("term") "term" ..

consts
  Collect       :: "['a \<Rightarrow> o] \<Rightarrow> 'a set"                    (*comprehension*)
  Compl         :: "('a set) \<Rightarrow> 'a set"                     (*complement*)
  Int           :: "['a set, 'a set] \<Rightarrow> 'a set"         (infixl "Int" 70)
  Un            :: "['a set, 'a set] \<Rightarrow> 'a set"         (infixl "Un" 65)
  Union         :: "(('a set)set) \<Rightarrow> 'a set"                (*...of a set*)
  Inter         :: "(('a set)set) \<Rightarrow> 'a set"                (*...of a set*)
  UNION         :: "['a set, 'a \<Rightarrow> 'b set] \<Rightarrow> 'b set"       (*general*)
  INTER         :: "['a set, 'a \<Rightarrow> 'b set] \<Rightarrow> 'b set"       (*general*)
  Ball          :: "['a set, 'a \<Rightarrow> o] \<Rightarrow> o"                 (*bounded quants*)
  Bex           :: "['a set, 'a \<Rightarrow> o] \<Rightarrow> o"                 (*bounded quants*)
  mono          :: "['a set \<Rightarrow> 'b set] \<Rightarrow> o"                (*monotonicity*)
  mem           :: "['a, 'a set] \<Rightarrow> o"                  (infixl ":" 50) (*membership*)
  subset        :: "['a set, 'a set] \<Rightarrow> o"              (infixl "<=" 50)
  singleton     :: "'a \<Rightarrow> 'a set"                       ("{_}")
  empty         :: "'a set"                             ("{}")

syntax
  "_Coll"       :: "[idt, o] \<Rightarrow> 'a set"                 ("(1{_./ _})") (*collection*)

  (* Big Intersection / Union *)

  "_INTER"      :: "[idt, 'a set, 'b set] \<Rightarrow> 'b set"    ("(INT _:_./ _)" [0, 0, 0] 10)
  "_UNION"      :: "[idt, 'a set, 'b set] \<Rightarrow> 'b set"    ("(UN _:_./ _)" [0, 0, 0] 10)

  (* Bounded Quantifiers *)

  "_Ball"       :: "[idt, 'a set, o] \<Rightarrow> o"              ("(ALL _:_./ _)" [0, 0, 0] 10)
  "_Bex"        :: "[idt, 'a set, o] \<Rightarrow> o"              ("(EX _:_./ _)" [0, 0, 0] 10)

translations
  "{x. P}"      == "CONST Collect(\<lambda>x. P)"
  "INT x:A. B"  == "CONST INTER(A, \<lambda>x. B)"
  "UN x:A. B"   == "CONST UNION(A, \<lambda>x. B)"
  "ALL x:A. P"  == "CONST Ball(A, \<lambda>x. P)"
  "EX x:A. P"   == "CONST Bex(A, \<lambda>x. P)"

axiomatization where
  mem_Collect_iff: "(a : {x. P(x)}) \<longleftrightarrow> P(a)" and
  set_extension: "A = B \<longleftrightarrow> (ALL x. x:A \<longleftrightarrow> x:B)"

defs
  Ball_def:      "Ball(A, P)  == ALL x. x:A \<longrightarrow> P(x)"
  Bex_def:       "Bex(A, P)   == EX x. x:A \<and> P(x)"
  mono_def:      "mono(f)     == (ALL A B. A <= B \<longrightarrow> f(A) <= f(B))"
  subset_def:    "A <= B      == ALL x:A. x:B"
  singleton_def: "{a}         == {x. x=a}"
  empty_def:     "{}          == {x. False}"
  Un_def:        "A Un B      == {x. x:A | x:B}"
  Int_def:       "A Int B     == {x. x:A \<and> x:B}"
  Compl_def:     "Compl(A)    == {x. \<not>x:A}"
  INTER_def:     "INTER(A, B) == {y. ALL x:A. y: B(x)}"
  UNION_def:     "UNION(A, B) == {y. EX x:A. y: B(x)}"
  Inter_def:     "Inter(S)    == (INT x:S. x)"
  Union_def:     "Union(S)    == (UN x:S. x)"


lemma CollectI: "P(a) \<Longrightarrow> a : {x. P(x)}"
  apply (rule mem_Collect_iff [THEN iffD2])
  apply assumption
  done

lemma CollectD: "a : {x. P(x)} \<Longrightarrow> P(a)"
  apply (erule mem_Collect_iff [THEN iffD1])
  done

lemmas CollectE = CollectD [elim_format]

lemma set_ext: "(\<And>x. x:A \<longleftrightarrow> x:B) \<Longrightarrow> A = B"
  apply (rule set_extension [THEN iffD2])
  apply simp
  done


subsection {* Bounded quantifiers *}

lemma ballI: "(\<And>x. x:A \<Longrightarrow> P(x)) \<Longrightarrow> ALL x:A. P(x)"
  by (simp add: Ball_def)

lemma bspec: "\<lbrakk>ALL x:A. P(x); x:A\<rbrakk> \<Longrightarrow> P(x)"
  by (simp add: Ball_def)

lemma ballE: "\<lbrakk>ALL x:A. P(x); P(x) \<Longrightarrow> Q; \<not> x:A \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding Ball_def by blast

lemma bexI: "\<lbrakk>P(x); x:A\<rbrakk> \<Longrightarrow> EX x:A. P(x)"
  unfolding Bex_def by blast

lemma bexCI: "\<lbrakk>EX x:A. \<not>P(x) \<Longrightarrow> P(a); a:A\<rbrakk> \<Longrightarrow> EX x:A. P(x)"
  unfolding Bex_def by blast

lemma bexE: "\<lbrakk>EX x:A. P(x); \<And>x. \<lbrakk>x:A; P(x)\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding Bex_def by blast

(*Trival rewrite rule;   (! x:A.P)=P holds only if A is nonempty!*)
lemma ball_rew: "(ALL x:A. True) \<longleftrightarrow> True"
  by (blast intro: ballI)


subsection {* Congruence rules *}

lemma ball_cong:
  "\<lbrakk>A = A'; \<And>x. x:A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)\<rbrakk> \<Longrightarrow>
    (ALL x:A. P(x)) \<longleftrightarrow> (ALL x:A'. P'(x))"
  by (blast intro: ballI elim: ballE)

lemma bex_cong:
  "\<lbrakk>A = A'; \<And>x. x:A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)\<rbrakk> \<Longrightarrow>
    (EX x:A. P(x)) \<longleftrightarrow> (EX x:A'. P'(x))"
  by (blast intro: bexI elim: bexE)


subsection {* Rules for subsets *}

lemma subsetI: "(\<And>x. x:A \<Longrightarrow> x:B) \<Longrightarrow> A <= B"
  unfolding subset_def by (blast intro: ballI)

(*Rule in Modus Ponens style*)
lemma subsetD: "\<lbrakk>A <= B; c:A\<rbrakk> \<Longrightarrow> c:B"
  unfolding subset_def by (blast elim: ballE)

(*Classical elimination rule*)
lemma subsetCE: "\<lbrakk>A <= B; \<not>(c:A) \<Longrightarrow> P; c:B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (blast dest: subsetD)

lemma subset_refl: "A <= A"
  by (blast intro: subsetI)

lemma subset_trans: "\<lbrakk>A <= B; B <= C\<rbrakk> \<Longrightarrow> A <= C"
  by (blast intro: subsetI dest: subsetD)


subsection {* Rules for equality *}

(*Anti-symmetry of the subset relation*)
lemma subset_antisym: "\<lbrakk>A <= B; B <= A\<rbrakk> \<Longrightarrow> A = B"
  by (blast intro: set_ext dest: subsetD)

lemmas equalityI = subset_antisym

(* Equality rules from ZF set theory -- are they appropriate here? *)
lemma equalityD1: "A = B \<Longrightarrow> A<=B"
  and equalityD2: "A = B \<Longrightarrow> B<=A"
  by (simp_all add: subset_refl)

lemma equalityE: "\<lbrakk>A = B; \<lbrakk>A <= B; B <= A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: subset_refl)

lemma equalityCE: "\<lbrakk>A = B; \<lbrakk>c:A; c:B\<rbrakk> \<Longrightarrow> P; \<lbrakk>\<not> c:A; \<not> c:B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (blast elim: equalityE subsetCE)

lemma trivial_set: "{x. x:A} = A"
  by (blast intro: equalityI subsetI CollectI dest: CollectD)


subsection {* Rules for binary union *}

lemma UnI1: "c:A \<Longrightarrow> c : A Un B"
  and UnI2: "c:B \<Longrightarrow> c : A Un B"
  unfolding Un_def by (blast intro: CollectI)+

(*Classical introduction rule: no commitment to A vs B*)
lemma UnCI: "(\<not>c:B \<Longrightarrow> c:A) \<Longrightarrow> c : A Un B"
  by (blast intro: UnI1 UnI2)

lemma UnE: "\<lbrakk>c : A Un B; c:A \<Longrightarrow> P; c:B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding Un_def by (blast dest: CollectD)


subsection {* Rules for small intersection *}

lemma IntI: "\<lbrakk>c:A; c:B\<rbrakk> \<Longrightarrow> c : A Int B"
  unfolding Int_def by (blast intro: CollectI)

lemma IntD1: "c : A Int B \<Longrightarrow> c:A"
  and IntD2: "c : A Int B \<Longrightarrow> c:B"
  unfolding Int_def by (blast dest: CollectD)+

lemma IntE: "\<lbrakk>c : A Int B; \<lbrakk>c:A; c:B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (blast dest: IntD1 IntD2)


subsection {* Rules for set complement *}

lemma ComplI: "(c:A \<Longrightarrow> False) \<Longrightarrow> c : Compl(A)"
  unfolding Compl_def by (blast intro: CollectI)

(*This form, with negated conclusion, works well with the Classical prover.
  Negated assumptions behave like formulae on the right side of the notional
  turnstile...*)
lemma ComplD: "c : Compl(A) \<Longrightarrow> \<not>c:A"
  unfolding Compl_def by (blast dest: CollectD)

lemmas ComplE = ComplD [elim_format]


subsection {* Empty sets *}

lemma empty_eq: "{x. False} = {}"
  by (simp add: empty_def)

lemma emptyD: "a : {} \<Longrightarrow> P"
  unfolding empty_def by (blast dest: CollectD)

lemmas emptyE = emptyD [elim_format]

lemma not_emptyD:
  assumes "\<not> A={}"
  shows "EX x. x:A"
proof -
  have "\<not> (EX x. x:A) \<Longrightarrow> A = {}"
    by (rule equalityI) (blast intro!: subsetI elim!: emptyD)+
  with assms show ?thesis by blast
qed


subsection {* Singleton sets *}

lemma singletonI: "a : {a}"
  unfolding singleton_def by (blast intro: CollectI)

lemma singletonD: "b : {a} \<Longrightarrow> b=a"
  unfolding singleton_def by (blast dest: CollectD)

lemmas singletonE = singletonD [elim_format]


subsection {* Unions of families *}

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma UN_I: "\<lbrakk>a:A; b: B(a)\<rbrakk> \<Longrightarrow> b: (UN x:A. B(x))"
  unfolding UNION_def by (blast intro: bexI CollectI)

lemma UN_E: "\<lbrakk>b : (UN x:A. B(x)); \<And>x. \<lbrakk>x:A; b: B(x)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding UNION_def by (blast dest: CollectD elim: bexE)

lemma UN_cong: "\<lbrakk>A = B; \<And>x. x:B \<Longrightarrow> C(x) = D(x)\<rbrakk> \<Longrightarrow> (UN x:A. C(x)) = (UN x:B. D(x))"
  by (simp add: UNION_def cong: bex_cong)


subsection {* Intersections of families *}

lemma INT_I: "(\<And>x. x:A \<Longrightarrow> b: B(x)) \<Longrightarrow> b : (INT x:A. B(x))"
  unfolding INTER_def by (blast intro: CollectI ballI)

lemma INT_D: "\<lbrakk>b : (INT x:A. B(x)); a:A\<rbrakk> \<Longrightarrow> b: B(a)"
  unfolding INTER_def by (blast dest: CollectD bspec)

(*"Classical" elimination rule -- does not require proving X:C *)
lemma INT_E: "\<lbrakk>b : (INT x:A. B(x)); b: B(a) \<Longrightarrow> R; \<not> a:A \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding INTER_def by (blast dest: CollectD bspec)

lemma INT_cong: "\<lbrakk>A = B; \<And>x. x:B \<Longrightarrow> C(x) = D(x)\<rbrakk> \<Longrightarrow> (INT x:A. C(x)) = (INT x:B. D(x))"
  by (simp add: INTER_def cong: ball_cong)


subsection {* Rules for Unions *}

(*The order of the premises presupposes that C is rigid; A may be flexible*)
lemma UnionI: "\<lbrakk>X:C; A:X\<rbrakk> \<Longrightarrow> A : Union(C)"
  unfolding Union_def by (blast intro: UN_I)

lemma UnionE: "\<lbrakk>A : Union(C); \<And>X. \<lbrakk> A:X; X:C\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding Union_def by (blast elim: UN_E)


subsection {* Rules for Inter *}

lemma InterI: "(\<And>X. X:C \<Longrightarrow> A:X) \<Longrightarrow> A : Inter(C)"
  unfolding Inter_def by (blast intro: INT_I)

(*A "destruct" rule -- every X in C contains A as an element, but
  A:X can hold when X:C does not!  This rule is analogous to "spec". *)
lemma InterD: "\<lbrakk>A : Inter(C);  X:C\<rbrakk> \<Longrightarrow> A:X"
  unfolding Inter_def by (blast dest: INT_D)

(*"Classical" elimination rule -- does not require proving X:C *)
lemma InterE: "\<lbrakk>A : Inter(C); A:X \<Longrightarrow> R; \<not> X:C \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding Inter_def by (blast elim: INT_E)


section {* Derived rules involving subsets; Union and Intersection as lattice operations *}

subsection {* Big Union -- least upper bound of a set *}

lemma Union_upper: "B:A \<Longrightarrow> B <= Union(A)"
  by (blast intro: subsetI UnionI)

lemma Union_least: "(\<And>X. X:A \<Longrightarrow> X<=C) \<Longrightarrow> Union(A) <= C"
  by (blast intro: subsetI dest: subsetD elim: UnionE)


subsection {* Big Intersection -- greatest lower bound of a set *}

lemma Inter_lower: "B:A \<Longrightarrow> Inter(A) <= B"
  by (blast intro: subsetI dest: InterD)

lemma Inter_greatest: "(\<And>X. X:A \<Longrightarrow> C<=X) \<Longrightarrow> C <= Inter(A)"
  by (blast intro: subsetI InterI dest: subsetD)


subsection {* Finite Union -- the least upper bound of 2 sets *}

lemma Un_upper1: "A <= A Un B"
  by (blast intro: subsetI UnI1)

lemma Un_upper2: "B <= A Un B"
  by (blast intro: subsetI UnI2)

lemma Un_least: "\<lbrakk>A<=C; B<=C\<rbrakk> \<Longrightarrow> A Un B <= C"
  by (blast intro: subsetI elim: UnE dest: subsetD)


subsection {* Finite Intersection -- the greatest lower bound of 2 sets *}

lemma Int_lower1: "A Int B <= A"
  by (blast intro: subsetI elim: IntE)

lemma Int_lower2: "A Int B <= B"
  by (blast intro: subsetI elim: IntE)

lemma Int_greatest: "\<lbrakk>C<=A; C<=B\<rbrakk> \<Longrightarrow> C <= A Int B"
  by (blast intro: subsetI IntI dest: subsetD)


subsection {* Monotonicity *}

lemma monoI: "(\<And>A B. A <= B \<Longrightarrow> f(A) <= f(B)) \<Longrightarrow> mono(f)"
  unfolding mono_def by blast

lemma monoD: "\<lbrakk>mono(f); A <= B\<rbrakk> \<Longrightarrow> f(A) <= f(B)"
  unfolding mono_def by blast

lemma mono_Un: "mono(f) \<Longrightarrow> f(A) Un f(B) <= f(A Un B)"
  by (blast intro: Un_least dest: monoD intro: Un_upper1 Un_upper2)

lemma mono_Int: "mono(f) \<Longrightarrow> f(A Int B) <= f(A) Int f(B)"
  by (blast intro: Int_greatest dest: monoD intro: Int_lower1 Int_lower2)


subsection {* Automated reasoning setup *}

lemmas [intro!] = ballI subsetI InterI INT_I CollectI ComplI IntI UnCI singletonI
  and [intro] = bexI UnionI UN_I
  and [elim!] = bexE UnionE UN_E CollectE ComplE IntE UnE emptyE singletonE
  and [elim] = ballE InterD InterE INT_D INT_E subsetD subsetCE

lemma mem_rews:
  "(a : A Un B)   \<longleftrightarrow>  (a:A | a:B)"
  "(a : A Int B)  \<longleftrightarrow>  (a:A \<and> a:B)"
  "(a : Compl(B)) \<longleftrightarrow>  (\<not>a:B)"
  "(a : {b})      \<longleftrightarrow>  (a=b)"
  "(a : {})       \<longleftrightarrow>   False"
  "(a : {x. P(x)}) \<longleftrightarrow>  P(a)"
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

lemma subset_Int_eq: "(A<=B) \<longleftrightarrow> (A Int B = A)"
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

lemma subset_Un_eq: "(A<=B) \<longleftrightarrow> (A Un B = B)"
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
lemma Un_Int_assoc_eq: "((A Int B) Un C = A Int (B Un C)) \<longleftrightarrow> (C<=A)"
  by (blast intro: equalityI elim: equalityE)


subsection {* Big Union and Intersection *}

lemma Union_Un_distrib: "Union(A Un B) = Union(A) Un Union(B)"
  by (blast intro: equalityI)

lemma Union_disjoint:
    "(Union(C) Int A = {x. False}) \<longleftrightarrow> (ALL B:C. B Int A = {x. False})"
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

lemma Union_mono: "A<=B \<Longrightarrow> Union(A) <= Union(B)"
  by blast

lemma Inter_anti_mono: "B <= A \<Longrightarrow> Inter(A) <= Inter(B)"
  by blast

lemma UN_mono: "\<lbrakk>A <= B; \<And>x. x:A \<Longrightarrow> f(x)<=g(x)\<rbrakk> \<Longrightarrow> (UN x:A. f(x)) <= (UN x:B. g(x))"
  by blast

lemma INT_anti_mono: "\<lbrakk>B <= A; \<And>x. x:A \<Longrightarrow> f(x) <= g(x)\<rbrakk> \<Longrightarrow> (INT x:A. f(x)) <= (INT x:A. g(x))"
  by blast

lemma Un_mono: "\<lbrakk>A <= C; B <= D\<rbrakk> \<Longrightarrow> A Un B <= C Un D"
  by blast

lemma Int_mono: "\<lbrakk>A <= C; B <= D\<rbrakk> \<Longrightarrow> A Int B <= C Int D"
  by blast

lemma Compl_anti_mono: "A <= B \<Longrightarrow> Compl(B) <= Compl(A)"
  by blast

end
