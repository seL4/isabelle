(*  Title:      ZF/ZF_Base.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Base of Zermelo-Fraenkel Set Theory\<close>

theory ZF_Base
imports FOL
begin

subsection \<open>Signature\<close>

declare [[eta_contract = false]]

typedecl i
instance i :: "term" ..

axiomatization mem :: "[i, i] \<Rightarrow> o"  (infixl "\<in>" 50)  \<comment> \<open>membership relation\<close>
  and zero :: "i"  ("0")  \<comment> \<open>the empty set\<close>
  and Pow :: "i \<Rightarrow> i"  \<comment> \<open>power sets\<close>
  and Inf :: "i"  \<comment> \<open>infinite set\<close>
  and Union :: "i \<Rightarrow> i"  ("\<Union>_" [90] 90)
  and PrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"

abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl "\<notin>" 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"


subsection \<open>Bounded Quantifiers\<close>

definition Ball :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Ball(A, P) \<equiv> \<forall>x. x\<in>A \<longrightarrow> P(x)"

definition Bex :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Bex(A, P) \<equiv> \<exists>x. x\<in>A \<and> P(x)"

syntax
  "_Ball" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<forall>_\<in>_./ _)" 10)
  "_Bex" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<exists>_\<in>_./ _)" 10)
translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball(A, \<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex(A, \<lambda>x. P)"


subsection \<open>Variations on Replacement\<close>

(* Derived form of replacement, restricting P to its functional part.
   The resulting set (for functional P) is the same as with
   PrimReplace, but the rules are simpler. *)
definition Replace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"
  where "Replace(A,P) == PrimReplace(A, %x y. (\<exists>!z. P(x,z)) & P(x,y))"

syntax
  "_Replace"  :: "[pttrn, pttrn, i, o] => i"  ("(1{_ ./ _ \<in> _, _})")
translations
  "{y. x\<in>A, Q}" \<rightleftharpoons> "CONST Replace(A, \<lambda>x y. Q)"


(* Functional form of replacement -- analgous to ML's map functional *)

definition RepFun :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "RepFun(A,f) == {y . x\<in>A, y=f(x)}"

syntax
  "_RepFun" :: "[i, pttrn, i] => i"  ("(1{_ ./ _ \<in> _})" [51,0,51])
translations
  "{b. x\<in>A}" \<rightleftharpoons> "CONST RepFun(A, \<lambda>x. b)"


(* Separation and Pairing can be derived from the Replacement
   and Powerset Axioms using the following definitions. *)
definition Collect :: "[i, i \<Rightarrow> o] \<Rightarrow> i"
  where "Collect(A,P) == {y . x\<in>A, x=y & P(x)}"

syntax
  "_Collect" :: "[pttrn, i, o] \<Rightarrow> i"  ("(1{_ \<in> _ ./ _})")
translations
  "{x\<in>A. P}" \<rightleftharpoons> "CONST Collect(A, \<lambda>x. P)"


subsection \<open>General union and intersection\<close>

definition Inter :: "i => i"  ("\<Inter>_" [90] 90)
  where "\<Inter>(A) == { x\<in>\<Union>(A) . \<forall>y\<in>A. x\<in>y}"

syntax
  "_UNION" :: "[pttrn, i, i] => i"  ("(3\<Union>_\<in>_./ _)" 10)
  "_INTER" :: "[pttrn, i, i] => i"  ("(3\<Inter>_\<in>_./ _)" 10)
translations
  "\<Union>x\<in>A. B" == "CONST Union({B. x\<in>A})"
  "\<Inter>x\<in>A. B" == "CONST Inter({B. x\<in>A})"


subsection \<open>Finite sets and binary operations\<close>

(*Unordered pairs (Upair) express binary union/intersection and cons;
  set enumerations translate as {a,...,z} = cons(a,...,cons(z,0)...)*)

definition Upair :: "[i, i] => i"
  where "Upair(a,b) == {y. x\<in>Pow(Pow(0)), (x=0 & y=a) | (x=Pow(0) & y=b)}"

definition Subset :: "[i, i] \<Rightarrow> o"  (infixl "\<subseteq>" 50)  \<comment> \<open>subset relation\<close>
  where subset_def: "A \<subseteq> B \<equiv> \<forall>x\<in>A. x\<in>B"

definition Diff :: "[i, i] \<Rightarrow> i"  (infixl "-" 65)  \<comment> \<open>set difference\<close>
  where "A - B == { x\<in>A . ~(x\<in>B) }"

definition Un :: "[i, i] \<Rightarrow> i"  (infixl "\<union>" 65)  \<comment> \<open>binary union\<close>
  where "A \<union> B == \<Union>(Upair(A,B))"

definition Int :: "[i, i] \<Rightarrow> i"  (infixl "\<inter>" 70)  \<comment> \<open>binary intersection\<close>
  where "A \<inter> B == \<Inter>(Upair(A,B))"

definition cons :: "[i, i] => i"
  where "cons(a,A) == Upair(a,a) \<union> A"

definition succ :: "i => i"
  where "succ(i) == cons(i, i)"

nonterminal "is"
syntax
  "" :: "i \<Rightarrow> is"  ("_")
  "_Enum" :: "[i, is] \<Rightarrow> is"  ("_,/ _")
  "_Finset" :: "is \<Rightarrow> i"  ("{(_)}")
translations
  "{x, xs}" == "CONST cons(x, {xs})"
  "{x}" == "CONST cons(x, 0)"


subsection \<open>Axioms\<close>

(* ZF axioms -- see Suppes p.238
   Axioms for Union, Pow and Replace state existence only,
   uniqueness is derivable using extensionality. *)

axiomatization
where
  extension:     "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A" and
  Union_iff:     "A \<in> \<Union>(C) \<longleftrightarrow> (\<exists>B\<in>C. A\<in>B)" and
  Pow_iff:       "A \<in> Pow(B) \<longleftrightarrow> A \<subseteq> B" and

  (*We may name this set, though it is not uniquely defined.*)
  infinity:      "0 \<in> Inf \<and> (\<forall>y\<in>Inf. succ(y) \<in> Inf)" and

  (*This formulation facilitates case analysis on A.*)
  foundation:    "A = 0 \<or> (\<exists>x\<in>A. \<forall>y\<in>x. y\<notin>A)" and

  (*Schema axiom since predicate P is a higher-order variable*)
  replacement:   "(\<forall>x\<in>A. \<forall>y z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z) \<Longrightarrow>
                         b \<in> PrimReplace(A,P) \<longleftrightarrow> (\<exists>x\<in>A. P(x,b))"


subsection \<open>Definite descriptions -- via Replace over the set "1"\<close>

definition The :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder "THE " 10)
  where the_def: "The(P)    == \<Union>({y . x \<in> {0}, P(y)})"

definition If :: "[o, i, i] \<Rightarrow> i"  ("(if (_)/ then (_)/ else (_))" [10] 10)
  where if_def: "if P then a else b == THE z. P & z=a | ~P & z=b"

abbreviation (input)
  old_if :: "[o, i, i] => i"  ("if '(_,_,_')")
  where "if(P,a,b) == If(P,a,b)"


subsection \<open>Ordered Pairing\<close>

(* this "symmetric" definition works better than {{a}, {a,b}} *)
definition Pair :: "[i, i] => i"
  where "Pair(a,b) == {{a,a}, {a,b}}"

definition fst :: "i \<Rightarrow> i"
  where "fst(p) == THE a. \<exists>b. p = Pair(a, b)"

definition snd :: "i \<Rightarrow> i"
  where "snd(p) == THE b. \<exists>a. p = Pair(a, b)"

definition split :: "[[i, i] \<Rightarrow> 'a, i] \<Rightarrow> 'a::{}"  \<comment> \<open>for pattern-matching\<close>
  where "split(c) == \<lambda>p. c(fst(p), snd(p))"

(* Patterns -- extends pre-defined type "pttrn" used in abstractions *)
nonterminal patterns
syntax
  "_pattern"  :: "patterns => pttrn"         ("\<langle>_\<rangle>")
  ""          :: "pttrn => patterns"         ("_")
  "_patterns" :: "[pttrn, patterns] => patterns"  ("_,/_")
  "_Tuple"    :: "[i, is] => i"              ("\<langle>(_,/ _)\<rangle>")
translations
  "\<langle>x, y, z\<rangle>"   == "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"      == "CONST Pair(x, y)"
  "\<lambda>\<langle>x,y,zs\<rangle>.b" == "CONST split(\<lambda>x \<langle>y,zs\<rangle>.b)"
  "\<lambda>\<langle>x,y\<rangle>.b"    == "CONST split(\<lambda>x y. b)"

definition Sigma :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "Sigma(A,B) == \<Union>x\<in>A. \<Union>y\<in>B(x). {\<langle>x,y\<rangle>}"

abbreviation cart_prod :: "[i, i] => i"  (infixr "\<times>" 80)  \<comment> \<open>Cartesian product\<close>
  where "A \<times> B \<equiv> Sigma(A, \<lambda>_. B)"


subsection \<open>Relations and Functions\<close>

(*converse of relation r, inverse of function*)
definition converse :: "i \<Rightarrow> i"
  where "converse(r) == {z. w\<in>r, \<exists>x y. w=\<langle>x,y\<rangle> \<and> z=\<langle>y,x\<rangle>}"

definition domain :: "i \<Rightarrow> i"
  where "domain(r) == {x. w\<in>r, \<exists>y. w=\<langle>x,y\<rangle>}"

definition range :: "i \<Rightarrow> i"
  where "range(r) == domain(converse(r))"

definition field :: "i \<Rightarrow> i"
  where "field(r) == domain(r) \<union> range(r)"

definition relation :: "i \<Rightarrow> o"  \<comment> \<open>recognizes sets of pairs\<close>
  where "relation(r) == \<forall>z\<in>r. \<exists>x y. z = \<langle>x,y\<rangle>"

definition "function" :: "i \<Rightarrow> o"  \<comment> \<open>recognizes functions; can have non-pairs\<close>
  where "function(r) == \<forall>x y. \<langle>x,y\<rangle> \<in> r \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle> \<in> r \<longrightarrow> y = y')"

definition Image :: "[i, i] \<Rightarrow> i"  (infixl "``" 90)  \<comment> \<open>image\<close>
  where image_def: "r `` A  == {y \<in> range(r). \<exists>x\<in>A. \<langle>x,y\<rangle> \<in> r}"

definition vimage :: "[i, i] \<Rightarrow> i"  (infixl "-``" 90)  \<comment> \<open>inverse image\<close>
  where vimage_def: "r -`` A == converse(r)``A"

(* Restrict the relation r to the domain A *)
definition restrict :: "[i, i] \<Rightarrow> i"
  where "restrict(r,A) == {z \<in> r. \<exists>x\<in>A. \<exists>y. z = \<langle>x,y\<rangle>}"


(* Abstraction, application and Cartesian product of a family of sets *)

definition Lambda :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where lam_def: "Lambda(A,b) == {\<langle>x,b(x)\<rangle>. x\<in>A}"

definition "apply" :: "[i, i] \<Rightarrow> i"  (infixl "`" 90)  \<comment> \<open>function application\<close>
  where "f`a == \<Union>(f``{a})"

definition Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "Pi(A,B) == {f\<in>Pow(Sigma(A,B)). A\<subseteq>domain(f) & function(f)}"

abbreviation function_space :: "[i, i] \<Rightarrow> i"  (infixr "->" 60)  \<comment> \<open>function space\<close>
  where "A -> B \<equiv> Pi(A, \<lambda>_. B)"


(* binder syntax *)

syntax
  "_PROD"     :: "[pttrn, i, i] => i"        ("(3\<Prod>_\<in>_./ _)" 10)
  "_SUM"      :: "[pttrn, i, i] => i"        ("(3\<Sum>_\<in>_./ _)" 10)
  "_lam"      :: "[pttrn, i, i] => i"        ("(3\<lambda>_\<in>_./ _)" 10)
translations
  "\<Prod>x\<in>A. B"   == "CONST Pi(A, \<lambda>x. B)"
  "\<Sum>x\<in>A. B"   == "CONST Sigma(A, \<lambda>x. B)"
  "\<lambda>x\<in>A. f"    == "CONST Lambda(A, \<lambda>x. f)"


subsection \<open>ASCII syntax\<close>

notation (ASCII)
  cart_prod       (infixr "*" 80) and
  Int             (infixl "Int" 70) and
  Un              (infixl "Un" 65) and
  function_space  (infixr "\<rightarrow>" 60) and
  Subset          (infixl "<=" 50) and
  mem             (infixl ":" 50) and
  not_mem         (infixl "~:" 50)

syntax (ASCII)
  "_Ball"     :: "[pttrn, i, o] => o"        ("(3ALL _:_./ _)" 10)
  "_Bex"      :: "[pttrn, i, o] => o"        ("(3EX _:_./ _)" 10)
  "_Collect"  :: "[pttrn, i, o] => i"        ("(1{_: _ ./ _})")
  "_Replace"  :: "[pttrn, pttrn, i, o] => i" ("(1{_ ./ _: _, _})")
  "_RepFun"   :: "[i, pttrn, i] => i"        ("(1{_ ./ _: _})" [51,0,51])
  "_UNION"    :: "[pttrn, i, i] => i"        ("(3UN _:_./ _)" 10)
  "_INTER"    :: "[pttrn, i, i] => i"        ("(3INT _:_./ _)" 10)
  "_PROD"     :: "[pttrn, i, i] => i"        ("(3PROD _:_./ _)" 10)
  "_SUM"      :: "[pttrn, i, i] => i"        ("(3SUM _:_./ _)" 10)
  "_lam"      :: "[pttrn, i, i] => i"        ("(3lam _:_./ _)" 10)
  "_Tuple"    :: "[i, is] => i"              ("<(_,/ _)>")
  "_pattern"  :: "patterns => pttrn"         ("<_>")


subsection \<open>Substitution\<close>

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
lemma subst_elem: "[| b\<in>A;  a=b |] ==> a\<in>A"
by (erule ssubst, assumption)


subsection\<open>Bounded universal quantifier\<close>

lemma ballI [intro!]: "[| !!x. x\<in>A ==> P(x) |] ==> \<forall>x\<in>A. P(x)"
by (simp add: Ball_def)

lemmas strip = impI allI ballI

lemma bspec [dest?]: "[| \<forall>x\<in>A. P(x);  x: A |] ==> P(x)"
by (simp add: Ball_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_ballE [elim]:
    "[| \<forall>x\<in>A. P(x);  x\<notin>A ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: Ball_def, blast)

lemma ballE: "[| \<forall>x\<in>A. P(x);  P(x) ==> Q;  x\<notin>A ==> Q |] ==> Q"
by blast

(*Used in the datatype package*)
lemma rev_bspec: "[| x: A;  \<forall>x\<in>A. P(x) |] ==> P(x)"
by (simp add: Ball_def)

(*Trival rewrite rule;   @{term"(\<forall>x\<in>A.P)<->P"} holds only if A is nonempty!*)
lemma ball_triv [simp]: "(\<forall>x\<in>A. P) <-> ((\<exists>x. x\<in>A) \<longrightarrow> P)"
by (simp add: Ball_def)

(*Congruence rule for rewriting*)
lemma ball_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P(x) <-> P'(x) |] ==> (\<forall>x\<in>A. P(x)) <-> (\<forall>x\<in>A'. P'(x))"
by (simp add: Ball_def)

lemma atomize_ball:
    "(!!x. x \<in> A ==> P(x)) == Trueprop (\<forall>x\<in>A. P(x))"
  by (simp only: Ball_def atomize_all atomize_imp)

lemmas [symmetric, rulify] = atomize_ball
  and [symmetric, defn] = atomize_ball


subsection\<open>Bounded existential quantifier\<close>

lemma bexI [intro]: "[| P(x);  x: A |] ==> \<exists>x\<in>A. P(x)"
by (simp add: Bex_def, blast)

(*The best argument order when there is only one @{term"x\<in>A"}*)
lemma rev_bexI: "[| x\<in>A;  P(x) |] ==> \<exists>x\<in>A. P(x)"
by blast

(*Not of the general form for such rules. The existential quanitifer becomes universal. *)
lemma bexCI: "[| \<forall>x\<in>A. ~P(x) ==> P(a);  a: A |] ==> \<exists>x\<in>A. P(x)"
by blast

lemma bexE [elim!]: "[| \<exists>x\<in>A. P(x);  !!x. [| x\<in>A; P(x) |] ==> Q |] ==> Q"
by (simp add: Bex_def, blast)

(*We do not even have @{term"(\<exists>x\<in>A. True) <-> True"} unless @{term"A" is nonempty!!*)
lemma bex_triv [simp]: "(\<exists>x\<in>A. P) <-> ((\<exists>x. x\<in>A) & P)"
by (simp add: Bex_def)

lemma bex_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P(x) <-> P'(x) |]
     ==> (\<exists>x\<in>A. P(x)) <-> (\<exists>x\<in>A'. P'(x))"
by (simp add: Bex_def cong: conj_cong)



subsection\<open>Rules for subsets\<close>

lemma subsetI [intro!]:
    "(!!x. x\<in>A ==> x\<in>B) ==> A \<subseteq> B"
by (simp add: subset_def)

(*Rule in Modus Ponens style [was called subsetE] *)
lemma subsetD [elim]: "[| A \<subseteq> B;  c\<in>A |] ==> c\<in>B"
apply (unfold subset_def)
apply (erule bspec, assumption)
done

(*Classical elimination rule*)
lemma subsetCE [elim]:
    "[| A \<subseteq> B;  c\<notin>A ==> P;  c\<in>B ==> P |] ==> P"
by (simp add: subset_def, blast)

(*Sometimes useful with premises in this order*)
lemma rev_subsetD: "[| c\<in>A; A<=B |] ==> c\<in>B"
by blast

lemma contra_subsetD: "[| A \<subseteq> B; c \<notin> B |] ==> c \<notin> A"
by blast

lemma rev_contra_subsetD: "[| c \<notin> B;  A \<subseteq> B |] ==> c \<notin> A"
by blast

lemma subset_refl [simp]: "A \<subseteq> A"
by blast

lemma subset_trans: "[| A<=B;  B<=C |] ==> A<=C"
by blast

(*Useful for proving A<=B by rewriting in some cases*)
lemma subset_iff:
     "A<=B <-> (\<forall>x. x\<in>A \<longrightarrow> x\<in>B)"
apply (unfold subset_def Ball_def)
apply (rule iff_refl)
done

text\<open>For calculations\<close>
declare subsetD [trans] rev_subsetD [trans] subset_trans [trans]


subsection\<open>Rules for equality\<close>

(*Anti-symmetry of the subset relation*)
lemma equalityI [intro]: "[| A \<subseteq> B;  B \<subseteq> A |] ==> A = B"
by (rule extension [THEN iffD2], rule conjI)


lemma equality_iffI: "(!!x. x\<in>A <-> x\<in>B) ==> A = B"
by (rule equalityI, blast+)

lemmas equalityD1 = extension [THEN iffD1, THEN conjunct1]
lemmas equalityD2 = extension [THEN iffD1, THEN conjunct2]

lemma equalityE: "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P"
by (blast dest: equalityD1 equalityD2)

lemma equalityCE:
    "[| A = B;  [| c\<in>A; c\<in>B |] ==> P;  [| c\<notin>A; c\<notin>B |] ==> P |]  ==>  P"
by (erule equalityE, blast)

lemma equality_iffD:
  "A = B ==> (!!x. x \<in> A <-> x \<in> B)"
  by auto


subsection\<open>Rules for Replace -- the derived form of replacement\<close>

lemma Replace_iff:
    "b \<in> {y. x\<in>A, P(x,y)}  <->  (\<exists>x\<in>A. P(x,b) & (\<forall>y. P(x,y) \<longrightarrow> y=b))"
apply (unfold Replace_def)
apply (rule replacement [THEN iff_trans], blast+)
done

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
lemma ReplaceI [intro]:
    "[| P(x,b);  x: A;  !!y. P(x,y) ==> y=b |] ==>
     b \<in> {y. x\<in>A, P(x,y)}"
by (rule Replace_iff [THEN iffD2], blast)

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
lemma ReplaceE:
    "[| b \<in> {y. x\<in>A, P(x,y)};
        !!x. [| x: A;  P(x,b);  \<forall>y. P(x,y)\<longrightarrow>y=b |] ==> R
     |] ==> R"
by (rule Replace_iff [THEN iffD1, THEN bexE], simp+)

(*As above but without the (generally useless) 3rd assumption*)
lemma ReplaceE2 [elim!]:
    "[| b \<in> {y. x\<in>A, P(x,y)};
        !!x. [| x: A;  P(x,b) |] ==> R
     |] ==> R"
by (erule ReplaceE, blast)

lemma Replace_cong [cong]:
    "[| A=B;  !!x y. x\<in>B ==> P(x,y) <-> Q(x,y) |] ==>
     Replace(A,P) = Replace(B,Q)"
apply (rule equality_iffI)
apply (simp add: Replace_iff)
done


subsection\<open>Rules for RepFun\<close>

lemma RepFunI: "a \<in> A ==> f(a) \<in> {f(x). x\<in>A}"
by (simp add: RepFun_def Replace_iff, blast)

(*Useful for coinduction proofs*)
lemma RepFun_eqI [intro]: "[| b=f(a);  a \<in> A |] ==> b \<in> {f(x). x\<in>A}"
apply (erule ssubst)
apply (erule RepFunI)
done

lemma RepFunE [elim!]:
    "[| b \<in> {f(x). x\<in>A};
        !!x.[| x\<in>A;  b=f(x) |] ==> P |] ==>
     P"
by (simp add: RepFun_def Replace_iff, blast)

lemma RepFun_cong [cong]:
    "[| A=B;  !!x. x\<in>B ==> f(x)=g(x) |] ==> RepFun(A,f) = RepFun(B,g)"
by (simp add: RepFun_def)

lemma RepFun_iff [simp]: "b \<in> {f(x). x\<in>A} <-> (\<exists>x\<in>A. b=f(x))"
by (unfold Bex_def, blast)

lemma triv_RepFun [simp]: "{x. x\<in>A} = A"
by blast


subsection\<open>Rules for Collect -- forming a subset by separation\<close>

(*Separation is derivable from Replacement*)
lemma separation [simp]: "a \<in> {x\<in>A. P(x)} <-> a\<in>A & P(a)"
by (unfold Collect_def, blast)

lemma CollectI [intro!]: "[| a\<in>A;  P(a) |] ==> a \<in> {x\<in>A. P(x)}"
by simp

lemma CollectE [elim!]: "[| a \<in> {x\<in>A. P(x)};  [| a\<in>A; P(a) |] ==> R |] ==> R"
by simp

lemma CollectD1: "a \<in> {x\<in>A. P(x)} ==> a\<in>A"
by (erule CollectE, assumption)

lemma CollectD2: "a \<in> {x\<in>A. P(x)} ==> P(a)"
by (erule CollectE, assumption)

lemma Collect_cong [cong]:
    "[| A=B;  !!x. x\<in>B ==> P(x) <-> Q(x) |]
     ==> Collect(A, %x. P(x)) = Collect(B, %x. Q(x))"
by (simp add: Collect_def)


subsection\<open>Rules for Unions\<close>

declare Union_iff [simp]

(*The order of the premises presupposes that C is rigid; A may be flexible*)
lemma UnionI [intro]: "[| B: C;  A: B |] ==> A: \<Union>(C)"
by (simp, blast)

lemma UnionE [elim!]: "[| A \<in> \<Union>(C);  !!B.[| A: B;  B: C |] ==> R |] ==> R"
by (simp, blast)


subsection\<open>Rules for Unions of families\<close>
(* @{term"\<Union>x\<in>A. B(x)"} abbreviates @{term"\<Union>({B(x). x\<in>A})"} *)

lemma UN_iff [simp]: "b \<in> (\<Union>x\<in>A. B(x)) <-> (\<exists>x\<in>A. b \<in> B(x))"
by (simp add: Bex_def, blast)

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma UN_I: "[| a: A;  b: B(a) |] ==> b: (\<Union>x\<in>A. B(x))"
by (simp, blast)


lemma UN_E [elim!]:
    "[| b \<in> (\<Union>x\<in>A. B(x));  !!x.[| x: A;  b: B(x) |] ==> R |] ==> R"
by blast

lemma UN_cong:
    "[| A=B;  !!x. x\<in>B ==> C(x)=D(x) |] ==> (\<Union>x\<in>A. C(x)) = (\<Union>x\<in>B. D(x))"
by simp


(*No "Addcongs [UN_cong]" because @{term\<Union>} is a combination of constants*)

(* UN_E appears before UnionE so that it is tried first, to avoid expensive
  calls to hyp_subst_tac.  Cannot include UN_I as it is unsafe: would enlarge
  the search space.*)


subsection\<open>Rules for the empty set\<close>

(*The set @{term"{x\<in>0. False}"} is empty; by foundation it equals 0
  See Suppes, page 21.*)
lemma not_mem_empty [simp]: "a \<notin> 0"
apply (cut_tac foundation)
apply (best dest: equalityD2)
done

lemmas emptyE [elim!] = not_mem_empty [THEN notE]


lemma empty_subsetI [simp]: "0 \<subseteq> A"
by blast

lemma equals0I: "[| !!y. y\<in>A ==> False |] ==> A=0"
by blast

lemma equals0D [dest]: "A=0 ==> a \<notin> A"
by blast

declare sym [THEN equals0D, dest]

lemma not_emptyI: "a\<in>A ==> A \<noteq> 0"
by blast

lemma not_emptyE:  "[| A \<noteq> 0;  !!x. x\<in>A ==> R |] ==> R"
by blast


subsection\<open>Rules for Inter\<close>

(*Not obviously useful for proving InterI, InterD, InterE*)
lemma Inter_iff: "A \<in> \<Inter>(C) <-> (\<forall>x\<in>C. A: x) & C\<noteq>0"
by (simp add: Inter_def Ball_def, blast)

(* Intersection is well-behaved only if the family is non-empty! *)
lemma InterI [intro!]:
    "[| !!x. x: C ==> A: x;  C\<noteq>0 |] ==> A \<in> \<Inter>(C)"
by (simp add: Inter_iff)

(*A "destruct" rule -- every B in C contains A as an element, but
  A\<in>B can hold when B\<in>C does not!  This rule is analogous to "spec". *)
lemma InterD [elim, Pure.elim]: "[| A \<in> \<Inter>(C);  B \<in> C |] ==> A \<in> B"
by (unfold Inter_def, blast)

(*"Classical" elimination rule -- does not require exhibiting @{term"B\<in>C"} *)
lemma InterE [elim]:
    "[| A \<in> \<Inter>(C);  B\<notin>C ==> R;  A\<in>B ==> R |] ==> R"
by (simp add: Inter_def, blast)


subsection\<open>Rules for Intersections of families\<close>

(* @{term"\<Inter>x\<in>A. B(x)"} abbreviates @{term"\<Inter>({B(x). x\<in>A})"} *)

lemma INT_iff: "b \<in> (\<Inter>x\<in>A. B(x)) <-> (\<forall>x\<in>A. b \<in> B(x)) & A\<noteq>0"
by (force simp add: Inter_def)

lemma INT_I: "[| !!x. x: A ==> b: B(x);  A\<noteq>0 |] ==> b: (\<Inter>x\<in>A. B(x))"
by blast

lemma INT_E: "[| b \<in> (\<Inter>x\<in>A. B(x));  a: A |] ==> b \<in> B(a)"
by blast

lemma INT_cong:
    "[| A=B;  !!x. x\<in>B ==> C(x)=D(x) |] ==> (\<Inter>x\<in>A. C(x)) = (\<Inter>x\<in>B. D(x))"
by simp

(*No "Addcongs [INT_cong]" because @{term\<Inter>} is a combination of constants*)


subsection\<open>Rules for Powersets\<close>

lemma PowI: "A \<subseteq> B ==> A \<in> Pow(B)"
by (erule Pow_iff [THEN iffD2])

lemma PowD: "A \<in> Pow(B)  ==>  A<=B"
by (erule Pow_iff [THEN iffD1])

declare Pow_iff [iff]

lemmas Pow_bottom = empty_subsetI [THEN PowI]    \<comment>\<open>@{term"0 \<in> Pow(B)"}\<close>
lemmas Pow_top = subset_refl [THEN PowI]         \<comment>\<open>@{term"A \<in> Pow(A)"}\<close>


subsection\<open>Cantor's Theorem: There is no surjection from a set to its powerset.\<close>

(*The search is undirected.  Allowing redundant introduction rules may
  make it diverge.  Variable b represents ANY map, such as
  (lam x\<in>A.b(x)): A->Pow(A). *)
lemma cantor: "\<exists>S \<in> Pow(A). \<forall>x\<in>A. b(x) \<noteq> S"
by (best elim!: equalityCE del: ReplaceI RepFun_eqI)

end
