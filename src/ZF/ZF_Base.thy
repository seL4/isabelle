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

axiomatization mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<in>\<close> 50)  \<comment> \<open>membership relation\<close>
  and zero :: "i"  (\<open>0\<close>)  \<comment> \<open>the empty set\<close>
  and Pow :: "i \<Rightarrow> i"  \<comment> \<open>power sets\<close>
  and Inf :: "i"  \<comment> \<open>infinite set\<close>
  and Union :: "i \<Rightarrow> i"  (\<open>\<Union>_\<close> [90] 90)
  and PrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"

abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<notin>\<close> 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"


subsection \<open>Bounded Quantifiers\<close>

definition Ball :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Ball(A, P) \<equiv> \<forall>x. x\<in>A \<longrightarrow> P(x)"

definition Bex :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Bex(A, P) \<equiv> \<exists>x. x\<in>A \<and> P(x)"

syntax
  "_Ball" :: "[pttrn, i, o] \<Rightarrow> o"  (\<open>(3\<forall>_\<in>_./ _)\<close> 10)
  "_Bex" :: "[pttrn, i, o] \<Rightarrow> o"  (\<open>(3\<exists>_\<in>_./ _)\<close> 10)
syntax_consts
  "_Ball" \<rightleftharpoons> Ball and
  "_Bex" \<rightleftharpoons> Bex
translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball(A, \<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex(A, \<lambda>x. P)"


subsection \<open>Variations on Replacement\<close>

(* Derived form of replacement, restricting P to its functional part.
   The resulting set (for functional P) is the same as with
   PrimReplace, but the rules are simpler. *)
definition Replace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"
  where "Replace(A,P) \<equiv> PrimReplace(A, \<lambda>x y. (\<exists>!z. P(x,z)) \<and> P(x,y))"

syntax
  "_Replace" :: "[pttrn, pttrn, i, o] \<Rightarrow> i"  (\<open>(1{_ ./ _ \<in> _, _})\<close>)
syntax_consts
  "_Replace" \<rightleftharpoons> Replace
translations
  "{y. x\<in>A, Q}" \<rightleftharpoons> "CONST Replace(A, \<lambda>x y. Q)"


(* Functional form of replacement -- analgous to ML's map functional *)

definition RepFun :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "RepFun(A,f) \<equiv> {y . x\<in>A, y=f(x)}"

syntax
  "_RepFun" :: "[i, pttrn, i] \<Rightarrow> i"  (\<open>(1{_ ./ _ \<in> _})\<close> [51,0,51])
syntax_consts
  "_RepFun" \<rightleftharpoons> RepFun
translations
  "{b. x\<in>A}" \<rightleftharpoons> "CONST RepFun(A, \<lambda>x. b)"

(* Separation and Pairing can be derived from the Replacement
   and Powerset Axioms using the following definitions. *)
definition Collect :: "[i, i \<Rightarrow> o] \<Rightarrow> i"
  where "Collect(A,P) \<equiv> {y . x\<in>A, x=y \<and> P(x)}"

syntax
  "_Collect" :: "[pttrn, i, o] \<Rightarrow> i"  (\<open>(1{_ \<in> _ ./ _})\<close>)
syntax_consts
  "_Collect" \<rightleftharpoons> Collect
translations
  "{x\<in>A. P}" \<rightleftharpoons> "CONST Collect(A, \<lambda>x. P)"


subsection \<open>General union and intersection\<close>

definition Inter :: "i \<Rightarrow> i"  (\<open>\<Inter>_\<close> [90] 90)
  where "\<Inter>(A) \<equiv> { x\<in>\<Union>(A) . \<forall>y\<in>A. x\<in>y}"

syntax
  "_UNION" :: "[pttrn, i, i] \<Rightarrow> i"  (\<open>(3\<Union>_\<in>_./ _)\<close> 10)
  "_INTER" :: "[pttrn, i, i] \<Rightarrow> i"  (\<open>(3\<Inter>_\<in>_./ _)\<close> 10)
syntax_consts
  "_UNION" == Union and
  "_INTER" == Inter
translations
  "\<Union>x\<in>A. B" == "CONST Union({B. x\<in>A})"
  "\<Inter>x\<in>A. B" == "CONST Inter({B. x\<in>A})"


subsection \<open>Finite sets and binary operations\<close>

(*Unordered pairs (Upair) express binary union/intersection and cons;
  set enumerations translate as {a,...,z} = cons(a,...,cons(z,0)...)*)

definition Upair :: "[i, i] \<Rightarrow> i"
  where "Upair(a,b) \<equiv> {y. x\<in>Pow(Pow(0)), (x=0 \<and> y=a) | (x=Pow(0) \<and> y=b)}"

definition Subset :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<subseteq>\<close> 50)  \<comment> \<open>subset relation\<close>
  where subset_def: "A \<subseteq> B \<equiv> \<forall>x\<in>A. x\<in>B"

definition Diff :: "[i, i] \<Rightarrow> i"  (infixl \<open>-\<close> 65)  \<comment> \<open>set difference\<close>
  where "A - B \<equiv> { x\<in>A . \<not>(x\<in>B) }"

definition Un :: "[i, i] \<Rightarrow> i"  (infixl \<open>\<union>\<close> 65)  \<comment> \<open>binary union\<close>
  where "A \<union> B \<equiv> \<Union>(Upair(A,B))"

definition Int :: "[i, i] \<Rightarrow> i"  (infixl \<open>\<inter>\<close> 70)  \<comment> \<open>binary intersection\<close>
  where "A \<inter> B \<equiv> \<Inter>(Upair(A,B))"

definition cons :: "[i, i] \<Rightarrow> i"
  where "cons(a,A) \<equiv> Upair(a,a) \<union> A"

definition succ :: "i \<Rightarrow> i"
  where "succ(i) \<equiv> cons(i, i)"

nonterminal "finset_args"
syntax
  "" :: "i \<Rightarrow> finset_args"  (\<open>_\<close>)
  "_Finset_args" :: "[i, finset_args] \<Rightarrow> finset_args"  (\<open>_,/ _\<close>)
  "_Finset" :: "finset_args \<Rightarrow> i"  (\<open>{(_)}\<close>)
syntax_consts
  "_Finset_args" "_Finset" == cons
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

definition The :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder \<open>THE \<close> 10)
  where the_def: "The(P)    \<equiv> \<Union>({y . x \<in> {0}, P(y)})"

definition If :: "[o, i, i] \<Rightarrow> i"  (\<open>(if (_)/ then (_)/ else (_))\<close> [10] 10)
  where if_def: "if P then a else b \<equiv> THE z. P \<and> z=a | \<not>P \<and> z=b"

abbreviation (input)
  old_if :: "[o, i, i] \<Rightarrow> i"  (\<open>if '(_,_,_')\<close>)
  where "if(P,a,b) \<equiv> If(P,a,b)"


subsection \<open>Ordered Pairing\<close>

(* this "symmetric" definition works better than {{a}, {a,b}} *)
definition Pair :: "[i, i] \<Rightarrow> i"
  where "Pair(a,b) \<equiv> {{a,a}, {a,b}}"

definition fst :: "i \<Rightarrow> i"
  where "fst(p) \<equiv> THE a. \<exists>b. p = Pair(a, b)"

definition snd :: "i \<Rightarrow> i"
  where "snd(p) \<equiv> THE b. \<exists>a. p = Pair(a, b)"

definition split :: "[[i, i] \<Rightarrow> 'a, i] \<Rightarrow> 'a::{}"  \<comment> \<open>for pattern-matching\<close>
  where "split(c) \<equiv> \<lambda>p. c(fst(p), snd(p))"

nonterminal "tuple_args"
syntax
  "" :: "i \<Rightarrow> tuple_args"  (\<open>_\<close>)
  "_Tuple_args" :: "[i, tuple_args] \<Rightarrow> tuple_args"  (\<open>_,/ _\<close>)
  "_Tuple" :: "[i, tuple_args] \<Rightarrow> i"              (\<open>\<langle>(_,/ _)\<rangle>\<close>)
syntax_consts
  "_Tuple_args" "_Tuple" == Pair
translations
  "\<langle>x, y, z\<rangle>"   == "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"      == "CONST Pair(x, y)"

(* Patterns -- extends pre-defined type "pttrn" used in abstractions *)
nonterminal patterns
syntax
  "_pattern"  :: "patterns \<Rightarrow> pttrn"         (\<open>\<langle>_\<rangle>\<close>)
  ""          :: "pttrn \<Rightarrow> patterns"         (\<open>_\<close>)
  "_patterns" :: "[pttrn, patterns] \<Rightarrow> patterns"  (\<open>_,/_\<close>)
syntax_consts
  "_pattern" "_patterns" == split
translations
  "\<lambda>\<langle>x,y,zs\<rangle>.b" == "CONST split(\<lambda>x \<langle>y,zs\<rangle>.b)"
  "\<lambda>\<langle>x,y\<rangle>.b"    == "CONST split(\<lambda>x y. b)"

definition Sigma :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "Sigma(A,B) \<equiv> \<Union>x\<in>A. \<Union>y\<in>B(x). {\<langle>x,y\<rangle>}"

abbreviation cart_prod :: "[i, i] \<Rightarrow> i"  (infixr \<open>\<times>\<close> 80)  \<comment> \<open>Cartesian product\<close>
  where "A \<times> B \<equiv> Sigma(A, \<lambda>_. B)"


subsection \<open>Relations and Functions\<close>

(*converse of relation r, inverse of function*)
definition converse :: "i \<Rightarrow> i"
  where "converse(r) \<equiv> {z. w\<in>r, \<exists>x y. w=\<langle>x,y\<rangle> \<and> z=\<langle>y,x\<rangle>}"

definition domain :: "i \<Rightarrow> i"
  where "domain(r) \<equiv> {x. w\<in>r, \<exists>y. w=\<langle>x,y\<rangle>}"

definition range :: "i \<Rightarrow> i"
  where "range(r) \<equiv> domain(converse(r))"

definition field :: "i \<Rightarrow> i"
  where "field(r) \<equiv> domain(r) \<union> range(r)"

definition relation :: "i \<Rightarrow> o"  \<comment> \<open>recognizes sets of pairs\<close>
  where "relation(r) \<equiv> \<forall>z\<in>r. \<exists>x y. z = \<langle>x,y\<rangle>"

definition "function" :: "i \<Rightarrow> o"  \<comment> \<open>recognizes functions; can have non-pairs\<close>
  where "function(r) \<equiv> \<forall>x y. \<langle>x,y\<rangle> \<in> r \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle> \<in> r \<longrightarrow> y = y')"

definition Image :: "[i, i] \<Rightarrow> i"  (infixl \<open>``\<close> 90)  \<comment> \<open>image\<close>
  where image_def: "r `` A  \<equiv> {y \<in> range(r). \<exists>x\<in>A. \<langle>x,y\<rangle> \<in> r}"

definition vimage :: "[i, i] \<Rightarrow> i"  (infixl \<open>-``\<close> 90)  \<comment> \<open>inverse image\<close>
  where vimage_def: "r -`` A \<equiv> converse(r)``A"

(* Restrict the relation r to the domain A *)
definition restrict :: "[i, i] \<Rightarrow> i"
  where "restrict(r,A) \<equiv> {z \<in> r. \<exists>x\<in>A. \<exists>y. z = \<langle>x,y\<rangle>}"


(* Abstraction, application and Cartesian product of a family of sets *)

definition Lambda :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where lam_def: "Lambda(A,b) \<equiv> {\<langle>x,b(x)\<rangle>. x\<in>A}"

definition "apply" :: "[i, i] \<Rightarrow> i"  (infixl \<open>`\<close> 90)  \<comment> \<open>function application\<close>
  where "f`a \<equiv> \<Union>(f``{a})"

definition Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i"
  where "Pi(A,B) \<equiv> {f\<in>Pow(Sigma(A,B)). A\<subseteq>domain(f) \<and> function(f)}"

abbreviation function_space :: "[i, i] \<Rightarrow> i"  (infixr \<open>\<rightarrow>\<close> 60)  \<comment> \<open>function space\<close>
  where "A \<rightarrow> B \<equiv> Pi(A, \<lambda>_. B)"


(* binder syntax *)

syntax
  "_PROD"     :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3\<Prod>_\<in>_./ _)\<close> 10)
  "_SUM"      :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3\<Sum>_\<in>_./ _)\<close> 10)
  "_lam"      :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3\<lambda>_\<in>_./ _)\<close> 10)
syntax_consts
  "_PROD" == Pi and
  "_SUM" == Sigma and
  "_lam" == Lambda
translations
  "\<Prod>x\<in>A. B"   == "CONST Pi(A, \<lambda>x. B)"
  "\<Sum>x\<in>A. B"   == "CONST Sigma(A, \<lambda>x. B)"
  "\<lambda>x\<in>A. f"    == "CONST Lambda(A, \<lambda>x. f)"


subsection \<open>ASCII syntax\<close>

notation (ASCII)
  cart_prod       (infixr \<open>*\<close> 80) and
  Int             (infixl \<open>Int\<close> 70) and
  Un              (infixl \<open>Un\<close> 65) and
  function_space  (infixr \<open>->\<close> 60) and
  Subset          (infixl \<open><=\<close> 50) and
  mem             (infixl \<open>:\<close> 50) and
  not_mem         (infixl \<open>\<not>:\<close> 50)

syntax (ASCII)
  "_Ball"     :: "[pttrn, i, o] \<Rightarrow> o"        (\<open>(3ALL _:_./ _)\<close> 10)
  "_Bex"      :: "[pttrn, i, o] \<Rightarrow> o"        (\<open>(3EX _:_./ _)\<close> 10)
  "_Collect"  :: "[pttrn, i, o] \<Rightarrow> i"        (\<open>(1{_: _ ./ _})\<close>)
  "_Replace"  :: "[pttrn, pttrn, i, o] \<Rightarrow> i" (\<open>(1{_ ./ _: _, _})\<close>)
  "_RepFun"   :: "[i, pttrn, i] \<Rightarrow> i"        (\<open>(1{_ ./ _: _})\<close> [51,0,51])
  "_UNION"    :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3UN _:_./ _)\<close> 10)
  "_INTER"    :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3INT _:_./ _)\<close> 10)
  "_PROD"     :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3PROD _:_./ _)\<close> 10)
  "_SUM"      :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3SUM _:_./ _)\<close> 10)
  "_lam"      :: "[pttrn, i, i] \<Rightarrow> i"        (\<open>(3lam _:_./ _)\<close> 10)
  "_Tuple"    :: "[i, tuple_args] \<Rightarrow> i"      (\<open><(_,/ _)>\<close>)
  "_pattern"  :: "patterns \<Rightarrow> pttrn"         (\<open><_>\<close>)


subsection \<open>Substitution\<close>

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
lemma subst_elem: "\<lbrakk>b\<in>A;  a=b\<rbrakk> \<Longrightarrow> a\<in>A"
by (erule ssubst, assumption)


subsection\<open>Bounded universal quantifier\<close>

lemma ballI [intro!]: "\<lbrakk>\<And>x. x\<in>A \<Longrightarrow> P(x)\<rbrakk> \<Longrightarrow> \<forall>x\<in>A. P(x)"
by (simp add: Ball_def)

lemmas strip = impI allI ballI

lemma bspec [dest?]: "\<lbrakk>\<forall>x\<in>A. P(x);  x: A\<rbrakk> \<Longrightarrow> P(x)"
by (simp add: Ball_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_ballE [elim]:
    "\<lbrakk>\<forall>x\<in>A. P(x);  x\<notin>A \<Longrightarrow> Q;  P(x) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (simp add: Ball_def, blast)

lemma ballE: "\<lbrakk>\<forall>x\<in>A. P(x);  P(x) \<Longrightarrow> Q;  x\<notin>A \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by blast

(*Used in the datatype package*)
lemma rev_bspec: "\<lbrakk>x: A;  \<forall>x\<in>A. P(x)\<rbrakk> \<Longrightarrow> P(x)"
by (simp add: Ball_def)

(*Trival rewrite rule;   @{term"(\<forall>x\<in>A.P)\<longleftrightarrow>P"} holds only if A is nonempty!*)
lemma ball_triv [simp]: "(\<forall>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x\<in>A) \<longrightarrow> P)"
by (simp add: Ball_def)

(*Congruence rule for rewriting*)
lemma ball_cong [cong]:
    "\<lbrakk>A=A';  \<And>x. x\<in>A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)\<rbrakk> \<Longrightarrow> (\<forall>x\<in>A. P(x)) \<longleftrightarrow> (\<forall>x\<in>A'. P'(x))"
by (simp add: Ball_def)

lemma atomize_ball:
    "(\<And>x. x \<in> A \<Longrightarrow> P(x)) \<equiv> Trueprop (\<forall>x\<in>A. P(x))"
  by (simp only: Ball_def atomize_all atomize_imp)

lemmas [symmetric, rulify] = atomize_ball
  and [symmetric, defn] = atomize_ball


subsection\<open>Bounded existential quantifier\<close>

lemma bexI [intro]: "\<lbrakk>P(x);  x: A\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. P(x)"
by (simp add: Bex_def, blast)

(*The best argument order when there is only one @{term"x\<in>A"}*)
lemma rev_bexI: "\<lbrakk>x\<in>A;  P(x)\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. P(x)"
by blast

(*Not of the general form for such rules. The existential quanitifer becomes universal. *)
lemma bexCI: "\<lbrakk>\<forall>x\<in>A. \<not>P(x) \<Longrightarrow> P(a);  a: A\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. P(x)"
by blast

lemma bexE [elim!]: "\<lbrakk>\<exists>x\<in>A. P(x);  \<And>x. \<lbrakk>x\<in>A; P(x)\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (simp add: Bex_def, blast)

(*We do not even have @{term"(\<exists>x\<in>A. True) \<longleftrightarrow> True"} unless @{term"A" is nonempty\<And>*)
lemma bex_triv [simp]: "(\<exists>x\<in>A. P) \<longleftrightarrow> ((\<exists>x. x\<in>A) \<and> P)"
by (simp add: Bex_def)

lemma bex_cong [cong]:
    "\<lbrakk>A=A';  \<And>x. x\<in>A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)\<rbrakk>
     \<Longrightarrow> (\<exists>x\<in>A. P(x)) \<longleftrightarrow> (\<exists>x\<in>A'. P'(x))"
by (simp add: Bex_def cong: conj_cong)



subsection\<open>Rules for subsets\<close>

lemma subsetI [intro!]:
    "(\<And>x. x\<in>A \<Longrightarrow> x\<in>B) \<Longrightarrow> A \<subseteq> B"
by (simp add: subset_def)

(*Rule in Modus Ponens style [was called subsetE] *)
lemma subsetD [elim]: "\<lbrakk>A \<subseteq> B;  c\<in>A\<rbrakk> \<Longrightarrow> c\<in>B"
  unfolding subset_def
apply (erule bspec, assumption)
done

(*Classical elimination rule*)
lemma subsetCE [elim]:
    "\<lbrakk>A \<subseteq> B;  c\<notin>A \<Longrightarrow> P;  c\<in>B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (simp add: subset_def, blast)

(*Sometimes useful with premises in this order*)
lemma rev_subsetD: "\<lbrakk>c\<in>A; A\<subseteq>B\<rbrakk> \<Longrightarrow> c\<in>B"
by blast

lemma contra_subsetD: "\<lbrakk>A \<subseteq> B; c \<notin> B\<rbrakk> \<Longrightarrow> c \<notin> A"
  by blast

lemma rev_contra_subsetD: "\<lbrakk>c \<notin> B;  A \<subseteq> B\<rbrakk> \<Longrightarrow> c \<notin> A"
  by blast

lemma subset_refl [simp]: "A \<subseteq> A"
  by blast

lemma subset_trans: "\<lbrakk>A\<subseteq>B;  B\<subseteq>C\<rbrakk> \<Longrightarrow> A\<subseteq>C"
  by blast

(*Useful for proving A\<subseteq>B by rewriting in some cases*)
lemma subset_iff:
     "A\<subseteq>B \<longleftrightarrow> (\<forall>x. x\<in>A \<longrightarrow> x\<in>B)"
  by auto

text\<open>For calculations\<close>
declare subsetD [trans] rev_subsetD [trans] subset_trans [trans]


subsection\<open>Rules for equality\<close>

(*Anti-symmetry of the subset relation*)
lemma equalityI [intro]: "\<lbrakk>A \<subseteq> B;  B \<subseteq> A\<rbrakk> \<Longrightarrow> A = B"
  by (rule extension [THEN iffD2], rule conjI)


lemma equality_iffI: "(\<And>x. x\<in>A \<longleftrightarrow> x\<in>B) \<Longrightarrow> A = B"
  by (rule equalityI, blast+)

lemmas equalityD1 = extension [THEN iffD1, THEN conjunct1]
lemmas equalityD2 = extension [THEN iffD1, THEN conjunct2]

lemma equalityE: "\<lbrakk>A = B;  \<lbrakk>A\<subseteq>B; B\<subseteq>A\<rbrakk> \<Longrightarrow> P\<rbrakk>  \<Longrightarrow>  P"
  by (blast dest: equalityD1 equalityD2)

lemma equalityCE:
  "\<lbrakk>A = B;  \<lbrakk>c\<in>A; c\<in>B\<rbrakk> \<Longrightarrow> P;  \<lbrakk>c\<notin>A; c\<notin>B\<rbrakk> \<Longrightarrow> P\<rbrakk>  \<Longrightarrow>  P"
  by (erule equalityE, blast)

lemma equality_iffD:
  "A = B \<Longrightarrow> (\<And>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by auto


subsection\<open>Rules for Replace -- the derived form of replacement\<close>

lemma Replace_iff:
    "b \<in> {y. x\<in>A, P(x,y)}  \<longleftrightarrow>  (\<exists>x\<in>A. P(x,b) \<and> (\<forall>y. P(x,y) \<longrightarrow> y=b))"
  unfolding Replace_def
  by (rule replacement [THEN iff_trans], blast+)

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
lemma ReplaceI [intro]:
    "\<lbrakk>P(x,b);  x: A;  \<And>y. P(x,y) \<Longrightarrow> y=b\<rbrakk> \<Longrightarrow>
     b \<in> {y. x\<in>A, P(x,y)}"
by (rule Replace_iff [THEN iffD2], blast)

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
lemma ReplaceE:
    "\<lbrakk>b \<in> {y. x\<in>A, P(x,y)};
        \<And>x. \<lbrakk>x: A;  P(x,b);  \<forall>y. P(x,y)\<longrightarrow>y=b\<rbrakk> \<Longrightarrow> R
\<rbrakk> \<Longrightarrow> R"
by (rule Replace_iff [THEN iffD1, THEN bexE], simp+)

(*As above but without the (generally useless) 3rd assumption*)
lemma ReplaceE2 [elim!]:
  "\<lbrakk>b \<in> {y. x\<in>A, P(x,y)};
        \<And>x. \<lbrakk>x: A;  P(x,b)\<rbrakk> \<Longrightarrow> R
   \<rbrakk> \<Longrightarrow> R"
  by (erule ReplaceE, blast)

lemma Replace_cong [cong]:
  "\<lbrakk>A=B;  \<And>x y. x\<in>B \<Longrightarrow> P(x,y) \<longleftrightarrow> Q(x,y)\<rbrakk> \<Longrightarrow> Replace(A,P) = Replace(B,Q)"
  apply (rule equality_iffI)
  apply (simp add: Replace_iff)
  done


subsection\<open>Rules for RepFun\<close>

lemma RepFunI: "a \<in> A \<Longrightarrow> f(a) \<in> {f(x). x\<in>A}"
by (simp add: RepFun_def Replace_iff, blast)

(*Useful for coinduction proofs*)
lemma RepFun_eqI [intro]: "\<lbrakk>b=f(a);  a \<in> A\<rbrakk> \<Longrightarrow> b \<in> {f(x). x\<in>A}"
  by (blast intro: RepFunI)

lemma RepFunE [elim!]:
  "\<lbrakk>b \<in> {f(x). x\<in>A};
        \<And>x.\<lbrakk>x\<in>A;  b=f(x)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
     P"
  by (simp add: RepFun_def Replace_iff, blast)

lemma RepFun_cong [cong]:
  "\<lbrakk>A=B;  \<And>x. x\<in>B \<Longrightarrow> f(x)=g(x)\<rbrakk> \<Longrightarrow> RepFun(A,f) = RepFun(B,g)"
  by (simp add: RepFun_def)

lemma RepFun_iff [simp]: "b \<in> {f(x). x\<in>A} \<longleftrightarrow> (\<exists>x\<in>A. b=f(x))"
  by (unfold Bex_def, blast)

lemma triv_RepFun [simp]: "{x. x\<in>A} = A"
  by blast


subsection\<open>Rules for Collect -- forming a subset by separation\<close>

(*Separation is derivable from Replacement*)
lemma separation [simp]: "a \<in> {x\<in>A. P(x)} \<longleftrightarrow> a\<in>A \<and> P(a)"
  by (auto simp: Collect_def)

lemma CollectI [intro!]: "\<lbrakk>a\<in>A;  P(a)\<rbrakk> \<Longrightarrow> a \<in> {x\<in>A. P(x)}"
  by simp

lemma CollectE [elim!]: "\<lbrakk>a \<in> {x\<in>A. P(x)};  \<lbrakk>a\<in>A; P(a)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by simp

lemma CollectD1: "a \<in> {x\<in>A. P(x)} \<Longrightarrow> a\<in>A" and CollectD2: "a \<in> {x\<in>A. P(x)} \<Longrightarrow> P(a)"
  by auto

lemma Collect_cong [cong]:
  "\<lbrakk>A=B;  \<And>x. x\<in>B \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)\<rbrakk>
     \<Longrightarrow> Collect(A, \<lambda>x. P(x)) = Collect(B, \<lambda>x. Q(x))"
  by (simp add: Collect_def)


subsection\<open>Rules for Unions\<close>

declare Union_iff [simp]

(*The order of the premises presupposes that C is rigid; A may be flexible*)
lemma UnionI [intro]: "\<lbrakk>B: C;  A: B\<rbrakk> \<Longrightarrow> A: \<Union>(C)"
  by auto

lemma UnionE [elim!]: "\<lbrakk>A \<in> \<Union>(C);  \<And>B.\<lbrakk>A: B;  B: C\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto


subsection\<open>Rules for Unions of families\<close>
(* @{term"\<Union>x\<in>A. B(x)"} abbreviates @{term"\<Union>({B(x). x\<in>A})"} *)

lemma UN_iff [simp]: "b \<in> (\<Union>x\<in>A. B(x)) \<longleftrightarrow> (\<exists>x\<in>A. b \<in> B(x))"
  by blast

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma UN_I: "\<lbrakk>a: A;  b: B(a)\<rbrakk> \<Longrightarrow> b: (\<Union>x\<in>A. B(x))"
  by force


lemma UN_E [elim!]:
  "\<lbrakk>b \<in> (\<Union>x\<in>A. B(x));  \<And>x.\<lbrakk>x: A;  b: B(x)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by blast

lemma UN_cong:
  "\<lbrakk>A=B;  \<And>x. x\<in>B \<Longrightarrow> C(x)=D(x)\<rbrakk> \<Longrightarrow> (\<Union>x\<in>A. C(x)) = (\<Union>x\<in>B. D(x))"
  by simp


(*No "Addcongs [UN_cong]" because @{term\<Union>} is a combination of constants*)

(* UN_E appears before UnionE so that it is tried first, to avoid expensive
  calls to hyp_subst_tac.  Cannot include UN_I as it is unsafe: would enlarge
  the search space.*)


subsection\<open>Rules for the empty set\<close>

(*The set @{term"{x\<in>0. False}"} is empty; by foundation it equals 0
  See Suppes, page 21.*)
lemma not_mem_empty [simp]: "a \<notin> 0"
  using foundation by (best dest: equalityD2)

lemmas emptyE [elim!] = not_mem_empty [THEN notE]


lemma empty_subsetI [simp]: "0 \<subseteq> A"
  by blast

lemma equals0I: "\<lbrakk>\<And>y. y\<in>A \<Longrightarrow> False\<rbrakk> \<Longrightarrow> A=0"
  by blast

lemma equals0D [dest]: "A=0 \<Longrightarrow> a \<notin> A"
  by blast

declare sym [THEN equals0D, dest]

lemma not_emptyI: "a\<in>A \<Longrightarrow> A \<noteq> 0"
  by blast

lemma not_emptyE:  "\<lbrakk>A \<noteq> 0;  \<And>x. x\<in>A \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by blast


subsection\<open>Rules for Inter\<close>

(*Not obviously useful for proving InterI, InterD, InterE*)
lemma Inter_iff: "A \<in> \<Inter>(C) \<longleftrightarrow> (\<forall>x\<in>C. A: x) \<and> C\<noteq>0"
  by (force simp: Inter_def)

(* Intersection is well-behaved only if the family is non-empty! *)
lemma InterI [intro!]:
  "\<lbrakk>\<And>x. x: C \<Longrightarrow> A: x;  C\<noteq>0\<rbrakk> \<Longrightarrow> A \<in> \<Inter>(C)"
  by (simp add: Inter_iff)

(*A "destruct" rule -- every B in C contains A as an element, but
  A\<in>B can hold when B\<in>C does not!  This rule is analogous to "spec". *)
lemma InterD [elim, Pure.elim]: "\<lbrakk>A \<in> \<Inter>(C);  B \<in> C\<rbrakk> \<Longrightarrow> A \<in> B"
  by (force simp: Inter_def)

(*"Classical" elimination rule -- does not require exhibiting @{term"B\<in>C"} *)
lemma InterE [elim]:
  "\<lbrakk>A \<in> \<Inter>(C);  B\<notin>C \<Longrightarrow> R;  A\<in>B \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp: Inter_def)


subsection\<open>Rules for Intersections of families\<close>

(* @{term"\<Inter>x\<in>A. B(x)"} abbreviates @{term"\<Inter>({B(x). x\<in>A})"} *)

lemma INT_iff: "b \<in> (\<Inter>x\<in>A. B(x)) \<longleftrightarrow> (\<forall>x\<in>A. b \<in> B(x)) \<and> A\<noteq>0"
  by (force simp add: Inter_def)

lemma INT_I: "\<lbrakk>\<And>x. x: A \<Longrightarrow> b: B(x);  A\<noteq>0\<rbrakk> \<Longrightarrow> b: (\<Inter>x\<in>A. B(x))"
  by blast

lemma INT_E: "\<lbrakk>b \<in> (\<Inter>x\<in>A. B(x));  a: A\<rbrakk> \<Longrightarrow> b \<in> B(a)"
  by blast

lemma INT_cong:
  "\<lbrakk>A=B;  \<And>x. x\<in>B \<Longrightarrow> C(x)=D(x)\<rbrakk> \<Longrightarrow> (\<Inter>x\<in>A. C(x)) = (\<Inter>x\<in>B. D(x))"
  by simp

(*No "Addcongs [INT_cong]" because @{term\<Inter>} is a combination of constants*)


subsection\<open>Rules for Powersets\<close>

lemma PowI: "A \<subseteq> B \<Longrightarrow> A \<in> Pow(B)"
  by (erule Pow_iff [THEN iffD2])

lemma PowD: "A \<in> Pow(B)  \<Longrightarrow>  A\<subseteq>B"
  by (erule Pow_iff [THEN iffD1])

declare Pow_iff [iff]

lemmas Pow_bottom = empty_subsetI [THEN PowI]    \<comment> \<open>\<^term>\<open>0 \<in> Pow(B)\<close>\<close>
lemmas Pow_top = subset_refl [THEN PowI]         \<comment> \<open>\<^term>\<open>A \<in> Pow(A)\<close>\<close>


subsection\<open>Cantor's Theorem: There is no surjection from a set to its powerset.\<close>

(*The search is undirected.  Allowing redundant introduction rules may
  make it diverge.  Variable b represents ANY map, such as
  (lam x\<in>A.b(x)): A->Pow(A). *)
lemma cantor: "\<exists>S \<in> Pow(A). \<forall>x\<in>A. b(x) \<noteq> S"
  by (best elim!: equalityCE del: ReplaceI RepFun_eqI)

end
