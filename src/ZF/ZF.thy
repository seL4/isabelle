(*  Title:      ZF/ZF.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header{*Zermelo-Fraenkel Set Theory*}

theory ZF = FOL:

global

typedecl i
arities  i :: "term"

consts

  "0"         :: "i"                  ("0")   --{*the empty set*}
  Pow         :: "i => i"                     --{*power sets*}
  Inf         :: "i"                          --{*infinite set*}

text {*Bounded Quantifiers *}
consts
  Ball   :: "[i, i => o] => o"
  Bex   :: "[i, i => o] => o"

text {*General Union and Intersection *}
consts
  Union :: "i => i"
  Inter :: "i => i"

text {*Variations on Replacement *}
consts
  PrimReplace :: "[i, [i, i] => o] => i"
  Replace     :: "[i, [i, i] => o] => i"
  RepFun      :: "[i, i => i] => i"
  Collect     :: "[i, i => o] => i"


text {*Descriptions *}
consts
  The         :: "(i => o) => i"      (binder "THE " 10)
  If          :: "[o, i, i] => i"     ("(if (_)/ then (_)/ else (_))" [10] 10)

syntax
  old_if      :: "[o, i, i] => i"   ("if '(_,_,_')")

translations
  "if(P,a,b)" => "If(P,a,b)"



text {*Finite Sets *}
consts
  Upair :: "[i, i] => i"
  cons  :: "[i, i] => i"
  succ  :: "i => i"

text {*Ordered Pairing *}
consts
  Pair  :: "[i, i] => i"
  fst   :: "i => i"
  snd   :: "i => i"
  split :: "[[i, i] => 'a, i] => 'a::logic"  --{*for pattern-matching*}

text {*Sigma and Pi Operators *}
consts
  Sigma :: "[i, i => i] => i"
  Pi    :: "[i, i => i] => i"

text {*Relations and Functions *}
consts
  "domain"    :: "i => i"
  range       :: "i => i"
  field       :: "i => i"
  converse    :: "i => i"
  relation    :: "i => o"        --{*recognizes sets of pairs*}
  function    :: "i => o"        --{*recognizes functions; can have non-pairs*}
  Lambda      :: "[i, i => i] => i"
  restrict    :: "[i, i] => i"

text {*Infixes in order of decreasing precedence *}
consts

  "``"        :: "[i, i] => i"    (infixl 90) --{*image*}
  "-``"       :: "[i, i] => i"    (infixl 90) --{*inverse image*}
  "`"         :: "[i, i] => i"    (infixl 90) --{*function application*}
(*"*"         :: "[i, i] => i"    (infixr 80) [virtual] Cartesian product*)
  "Int"       :: "[i, i] => i"    (infixl 70) --{*binary intersection*}
  "Un"        :: "[i, i] => i"    (infixl 65) --{*binary union*}
  "-"         :: "[i, i] => i"    (infixl 65) --{*set difference*}
(*"->"        :: "[i, i] => i"    (infixr 60) [virtual] function spac\<epsilon>*)
  "<="        :: "[i, i] => o"    (infixl 50) --{*subset relation*}
  ":"         :: "[i, i] => o"    (infixl 50) --{*membership relation*}
(*"~:"        :: "[i, i] => o"    (infixl 50) (*negated membership relation*)*)


nonterminals "is" patterns

syntax
  ""          :: "i => is"                   ("_")
  "@Enum"     :: "[i, is] => is"             ("_,/ _")
  "~:"        :: "[i, i] => o"               (infixl 50)
  "@Finset"   :: "is => i"                   ("{(_)}")
  "@Tuple"    :: "[i, is] => i"              ("<(_,/ _)>")
  "@Collect"  :: "[pttrn, i, o] => i"        ("(1{_: _ ./ _})")
  "@Replace"  :: "[pttrn, pttrn, i, o] => i" ("(1{_ ./ _: _, _})")
  "@RepFun"   :: "[i, pttrn, i] => i"        ("(1{_ ./ _: _})" [51,0,51])
  "@INTER"    :: "[pttrn, i, i] => i"        ("(3INT _:_./ _)" 10)
  "@UNION"    :: "[pttrn, i, i] => i"        ("(3UN _:_./ _)" 10)
  "@PROD"     :: "[pttrn, i, i] => i"        ("(3PROD _:_./ _)" 10)
  "@SUM"      :: "[pttrn, i, i] => i"        ("(3SUM _:_./ _)" 10)
  "->"        :: "[i, i] => i"               (infixr 60)
  "*"         :: "[i, i] => i"               (infixr 80)
  "@lam"      :: "[pttrn, i, i] => i"        ("(3lam _:_./ _)" 10)
  "@Ball"     :: "[pttrn, i, o] => o"        ("(3ALL _:_./ _)" 10)
  "@Bex"      :: "[pttrn, i, o] => o"        ("(3EX _:_./ _)" 10)

  (** Patterns -- extends pre-defined type "pttrn" used in abstractions **)

  "@pattern"  :: "patterns => pttrn"         ("<_>")
  ""          :: "pttrn => patterns"         ("_")
  "@patterns" :: "[pttrn, patterns] => patterns"  ("_,/_")

translations
  "x ~: y"      == "~ (x : y)"
  "{x, xs}"     == "cons(x, {xs})"
  "{x}"         == "cons(x, 0)"
  "{x:A. P}"    == "Collect(A, %x. P)"
  "{y. x:A, Q}" == "Replace(A, %x y. Q)"
  "{b. x:A}"    == "RepFun(A, %x. b)"
  "INT x:A. B"  == "Inter({B. x:A})"
  "UN x:A. B"   == "Union({B. x:A})"
  "PROD x:A. B" => "Pi(A, %x. B)"
  "SUM x:A. B"  => "Sigma(A, %x. B)"
  "A -> B"      => "Pi(A, _K(B))"
  "A * B"       => "Sigma(A, _K(B))"
  "lam x:A. f"  == "Lambda(A, %x. f)"
  "ALL x:A. P"  == "Ball(A, %x. P)"
  "EX x:A. P"   == "Bex(A, %x. P)"

  "<x, y, z>"   == "<x, <y, z>>"
  "<x, y>"      == "Pair(x, y)"
  "%<x,y,zs>.b" == "split(%x <y,zs>.b)"
  "%<x,y>.b"    == "split(%x y. b)"


syntax (xsymbols)
  "op *"      :: "[i, i] => i"               (infixr "\<times>" 80)
  "op Int"    :: "[i, i] => i"    	     (infixl "\<inter>" 70)
  "op Un"     :: "[i, i] => i"    	     (infixl "\<union>" 65)
  "op ->"     :: "[i, i] => i"               (infixr "\<rightarrow>" 60)
  "op <="     :: "[i, i] => o"    	     (infixl "\<subseteq>" 50)
  "op :"      :: "[i, i] => o"    	     (infixl "\<in>" 50)
  "op ~:"     :: "[i, i] => o"               (infixl "\<notin>" 50)
  "@Collect"  :: "[pttrn, i, o] => i"        ("(1{_ \<in> _ ./ _})")
  "@Replace"  :: "[pttrn, pttrn, i, o] => i" ("(1{_ ./ _ \<in> _, _})")
  "@RepFun"   :: "[i, pttrn, i] => i"        ("(1{_ ./ _ \<in> _})" [51,0,51])
  "@UNION"    :: "[pttrn, i, i] => i"        ("(3\<Union>_\<in>_./ _)" 10)
  "@INTER"    :: "[pttrn, i, i] => i"        ("(3\<Inter>_\<in>_./ _)" 10)
  Union       :: "i =>i"                     ("\<Union>_" [90] 90)
  Inter       :: "i =>i"                     ("\<Inter>_" [90] 90)
  "@PROD"     :: "[pttrn, i, i] => i"        ("(3\<Pi>_\<in>_./ _)" 10)
  "@SUM"      :: "[pttrn, i, i] => i"        ("(3\<Sigma>_\<in>_./ _)" 10)
  "@lam"      :: "[pttrn, i, i] => i"        ("(3\<lambda>_\<in>_./ _)" 10)
  "@Ball"     :: "[pttrn, i, o] => o"        ("(3\<forall>_\<in>_./ _)" 10)
  "@Bex"      :: "[pttrn, i, o] => o"        ("(3\<exists>_\<in>_./ _)" 10)
  "@Tuple"    :: "[i, is] => i"              ("\<langle>(_,/ _)\<rangle>")
  "@pattern"  :: "patterns => pttrn"         ("\<langle>_\<rangle>")

syntax (HTML output)
  "op *"      :: "[i, i] => i"               (infixr "\<times>" 80)
  "op Int"    :: "[i, i] => i"    	     (infixl "\<inter>" 70)
  "op Un"     :: "[i, i] => i"    	     (infixl "\<union>" 65)
  "op <="     :: "[i, i] => o"    	     (infixl "\<subseteq>" 50)
  "op :"      :: "[i, i] => o"    	     (infixl "\<in>" 50)
  "op ~:"     :: "[i, i] => o"               (infixl "\<notin>" 50)
  "@Collect"  :: "[pttrn, i, o] => i"        ("(1{_ \<in> _ ./ _})")
  "@Replace"  :: "[pttrn, pttrn, i, o] => i" ("(1{_ ./ _ \<in> _, _})")
  "@RepFun"   :: "[i, pttrn, i] => i"        ("(1{_ ./ _ \<in> _})" [51,0,51])
  "@UNION"    :: "[pttrn, i, i] => i"        ("(3\<Union>_\<in>_./ _)" 10)
  "@INTER"    :: "[pttrn, i, i] => i"        ("(3\<Inter>_\<in>_./ _)" 10)
  Union       :: "i =>i"                     ("\<Union>_" [90] 90)
  Inter       :: "i =>i"                     ("\<Inter>_" [90] 90)
  "@PROD"     :: "[pttrn, i, i] => i"        ("(3\<Pi>_\<in>_./ _)" 10)
  "@SUM"      :: "[pttrn, i, i] => i"        ("(3\<Sigma>_\<in>_./ _)" 10)
  "@lam"      :: "[pttrn, i, i] => i"        ("(3\<lambda>_\<in>_./ _)" 10)
  "@Ball"     :: "[pttrn, i, o] => o"        ("(3\<forall>_\<in>_./ _)" 10)
  "@Bex"      :: "[pttrn, i, o] => o"        ("(3\<exists>_\<in>_./ _)" 10)
  "@Tuple"    :: "[i, is] => i"              ("\<langle>(_,/ _)\<rangle>")
  "@pattern"  :: "patterns => pttrn"         ("\<langle>_\<rangle>")


finalconsts
  0 Pow Inf Union PrimReplace 
  "op :"

defs 
(*don't try to use constdefs: the declaration order is tightly constrained*)

  (* Bounded Quantifiers *)
  Ball_def:      "Ball(A, P) == \<forall>x. x\<in>A --> P(x)"
  Bex_def:       "Bex(A, P) == \<exists>x. x\<in>A & P(x)"

  subset_def:    "A <= B == \<forall>x\<in>A. x\<in>B"


local

axioms

  (* ZF axioms -- see Suppes p.238
     Axioms for Union, Pow and Replace state existence only,
     uniqueness is derivable using extensionality. *)

  extension:     "A = B <-> A <= B & B <= A"
  Union_iff:     "A \<in> Union(C) <-> (\<exists>B\<in>C. A\<in>B)"
  Pow_iff:       "A \<in> Pow(B) <-> A <= B"

  (*We may name this set, though it is not uniquely defined.*)
  infinity:      "0\<in>Inf & (\<forall>y\<in>Inf. succ(y): Inf)"

  (*This formulation facilitates case analysis on A.*)
  foundation:    "A=0 | (\<exists>x\<in>A. \<forall>y\<in>x. y~:A)"

  (*Schema axiom since predicate P is a higher-order variable*)
  replacement:   "(\<forall>x\<in>A. \<forall>y z. P(x,y) & P(x,z) --> y=z) ==>
                         b \<in> PrimReplace(A,P) <-> (\<exists>x\<in>A. P(x,b))"

defs

  (* Derived form of replacement, restricting P to its functional part.
     The resulting set (for functional P) is the same as with
     PrimReplace, but the rules are simpler. *)

  Replace_def:  "Replace(A,P) == PrimReplace(A, %x y. (EX!z. P(x,z)) & P(x,y))"

  (* Functional form of replacement -- analgous to ML's map functional *)

  RepFun_def:   "RepFun(A,f) == {y . x\<in>A, y=f(x)}"

  (* Separation and Pairing can be derived from the Replacement
     and Powerset Axioms using the following definitions. *)

  Collect_def:  "Collect(A,P) == {y . x\<in>A, x=y & P(x)}"

  (*Unordered pairs (Upair) express binary union/intersection and cons;
    set enumerations translate as {a,...,z} = cons(a,...,cons(z,0)...)*)

  Upair_def: "Upair(a,b) == {y. x\<in>Pow(Pow(0)), (x=0 & y=a) | (x=Pow(0) & y=b)}"
  cons_def:  "cons(a,A) == Upair(a,a) Un A"
  succ_def:  "succ(i) == cons(i, i)"

  (* Difference, general intersection, binary union and small intersection *)

  Diff_def:      "A - B    == { x\<in>A . ~(x\<in>B) }"
  Inter_def:     "Inter(A) == { x\<in>Union(A) . \<forall>y\<in>A. x\<in>y}"
  Un_def:        "A Un  B  == Union(Upair(A,B))"
  Int_def:      "A Int B  == Inter(Upair(A,B))"

  (* Definite descriptions -- via Replace over the set "1" *)

  the_def:      "The(P)    == Union({y . x \<in> {0}, P(y)})"
  if_def:       "if(P,a,b) == THE z. P & z=a | ~P & z=b"

  (* this "symmetric" definition works better than {{a}, {a,b}} *)
  Pair_def:     "<a,b>  == {{a,a}, {a,b}}"
  fst_def:      "fst(p) == THE a. \<exists>b. p=<a,b>"
  snd_def:      "snd(p) == THE b. \<exists>a. p=<a,b>"
  split_def:    "split(c) == %p. c(fst(p), snd(p))"
  Sigma_def:    "Sigma(A,B) == \<Union>x\<in>A. \<Union>y\<in>B(x). {<x,y>}"

  (* Operations on relations *)

  (*converse of relation r, inverse of function*)
  converse_def: "converse(r) == {z. w\<in>r, \<exists>x y. w=<x,y> & z=<y,x>}"

  domain_def:   "domain(r) == {x. w\<in>r, \<exists>y. w=<x,y>}"
  range_def:    "range(r) == domain(converse(r))"
  field_def:    "field(r) == domain(r) Un range(r)"
  relation_def: "relation(r) == \<forall>z\<in>r. \<exists>x y. z = <x,y>"
  function_def: "function(r) ==
		    \<forall>x y. <x,y>:r --> (\<forall>y'. <x,y'>:r --> y=y')"
  image_def:    "r `` A  == {y : range(r) . \<exists>x\<in>A. <x,y> : r}"
  vimage_def:   "r -`` A == converse(r)``A"

  (* Abstraction, application and Cartesian product of a family of sets *)

  lam_def:      "Lambda(A,b) == {<x,b(x)> . x\<in>A}"
  apply_def:    "f`a == Union(f``{a})"
  Pi_def:       "Pi(A,B)  == {f\<in>Pow(Sigma(A,B)). A<=domain(f) & function(f)}"

  (* Restrict the relation r to the domain A *)
  restrict_def: "restrict(r,A) == {z : r. \<exists>x\<in>A. \<exists>y. z = <x,y>}"

(* Pattern-matching and 'Dependent' type operators *)

print_translation {*
  [("Pi",    dependent_tr' ("@PROD", "op ->")),
   ("Sigma", dependent_tr' ("@SUM", "op *"))];
*}

subsection {* Substitution*}

(*Useful examples:  singletonI RS subst_elem,  subst_elem RSN (2,IntI) *)
lemma subst_elem: "[| b\<in>A;  a=b |] ==> a\<in>A"
by (erule ssubst, assumption)


subsection{*Bounded universal quantifier*}

lemma ballI [intro!]: "[| !!x. x\<in>A ==> P(x) |] ==> \<forall>x\<in>A. P(x)"
by (simp add: Ball_def)

lemma bspec [dest?]: "[| \<forall>x\<in>A. P(x);  x: A |] ==> P(x)"
by (simp add: Ball_def)

(*Instantiates x first: better for automatic theorem proving?*)
lemma rev_ballE [elim]: 
    "[| \<forall>x\<in>A. P(x);  x~:A ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: Ball_def, blast) 

lemma ballE: "[| \<forall>x\<in>A. P(x);  P(x) ==> Q;  x~:A ==> Q |] ==> Q"
by blast

(*Used in the datatype package*)
lemma rev_bspec: "[| x: A;  \<forall>x\<in>A. P(x) |] ==> P(x)"
by (simp add: Ball_def)

(*Trival rewrite rule;   (\<forall>x\<in>A.P)<->P holds only if A is nonempty!*)
lemma ball_triv [simp]: "(\<forall>x\<in>A. P) <-> ((\<exists>x. x\<in>A) --> P)"
by (simp add: Ball_def)

(*Congruence rule for rewriting*)
lemma ball_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P(x) <-> P'(x) |] ==> (\<forall>x\<in>A. P(x)) <-> (\<forall>x\<in>A'. P'(x))"
by (simp add: Ball_def)


subsection{*Bounded existential quantifier*}

lemma bexI [intro]: "[| P(x);  x: A |] ==> \<exists>x\<in>A. P(x)"
by (simp add: Bex_def, blast)

(*The best argument order when there is only one x\<in>A*)
lemma rev_bexI: "[| x\<in>A;  P(x) |] ==> \<exists>x\<in>A. P(x)"
by blast

(*Not of the general form for such rules; ~\<exists>has become ALL~ *)
lemma bexCI: "[| \<forall>x\<in>A. ~P(x) ==> P(a);  a: A |] ==> \<exists>x\<in>A. P(x)"
by blast

lemma bexE [elim!]: "[| \<exists>x\<in>A. P(x);  !!x. [| x\<in>A; P(x) |] ==> Q |] ==> Q"
by (simp add: Bex_def, blast)

(*We do not even have (\<exists>x\<in>A. True) <-> True unless A is nonempty!!*)
lemma bex_triv [simp]: "(\<exists>x\<in>A. P) <-> ((\<exists>x. x\<in>A) & P)"
by (simp add: Bex_def)

lemma bex_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P(x) <-> P'(x) |] 
     ==> (\<exists>x\<in>A. P(x)) <-> (\<exists>x\<in>A'. P'(x))"
by (simp add: Bex_def cong: conj_cong)



subsection{*Rules for subsets*}

lemma subsetI [intro!]:
    "(!!x. x\<in>A ==> x\<in>B) ==> A <= B"
by (simp add: subset_def) 

(*Rule in Modus Ponens style [was called subsetE] *)
lemma subsetD [elim]: "[| A <= B;  c\<in>A |] ==> c\<in>B"
apply (unfold subset_def)
apply (erule bspec, assumption)
done

(*Classical elimination rule*)
lemma subsetCE [elim]:
    "[| A <= B;  c~:A ==> P;  c\<in>B ==> P |] ==> P"
by (simp add: subset_def, blast) 

(*Sometimes useful with premises in this order*)
lemma rev_subsetD: "[| c\<in>A; A<=B |] ==> c\<in>B"
by blast

lemma contra_subsetD: "[| A <= B; c ~: B |] ==> c ~: A"
by blast

lemma rev_contra_subsetD: "[| c ~: B;  A <= B |] ==> c ~: A"
by blast

lemma subset_refl [simp]: "A <= A"
by blast

lemma subset_trans: "[| A<=B;  B<=C |] ==> A<=C"
by blast

(*Useful for proving A<=B by rewriting in some cases*)
lemma subset_iff: 
     "A<=B <-> (\<forall>x. x\<in>A --> x\<in>B)"
apply (unfold subset_def Ball_def)
apply (rule iff_refl)
done


subsection{*Rules for equality*}

(*Anti-symmetry of the subset relation*)
lemma equalityI [intro]: "[| A <= B;  B <= A |] ==> A = B"
by (rule extension [THEN iffD2], rule conjI) 


lemma equality_iffI: "(!!x. x\<in>A <-> x\<in>B) ==> A = B"
by (rule equalityI, blast+)

lemmas equalityD1 = extension [THEN iffD1, THEN conjunct1, standard]
lemmas equalityD2 = extension [THEN iffD1, THEN conjunct2, standard]

lemma equalityE: "[| A = B;  [| A<=B; B<=A |] ==> P |]  ==>  P"
by (blast dest: equalityD1 equalityD2) 

lemma equalityCE:
    "[| A = B;  [| c\<in>A; c\<in>B |] ==> P;  [| c~:A; c~:B |] ==> P |]  ==>  P"
by (erule equalityE, blast) 

(*Lemma for creating induction formulae -- for "pattern matching" on p
  To make the induction hypotheses usable, apply "spec" or "bspec" to
  put universal quantifiers over the free variables in p. 
  Would it be better to do subgoal_tac "\<forall>z. p = f(z) --> R(z)" ??*)
lemma setup_induction: "[| p: A;  !!z. z: A ==> p=z --> R |] ==> R"
by auto 



subsection{*Rules for Replace -- the derived form of replacement*}

lemma Replace_iff: 
    "b : {y. x\<in>A, P(x,y)}  <->  (\<exists>x\<in>A. P(x,b) & (\<forall>y. P(x,y) --> y=b))"
apply (unfold Replace_def)
apply (rule replacement [THEN iff_trans], blast+)
done

(*Introduction; there must be a unique y such that P(x,y), namely y=b. *)
lemma ReplaceI [intro]: 
    "[| P(x,b);  x: A;  !!y. P(x,y) ==> y=b |] ==>  
     b : {y. x\<in>A, P(x,y)}"
by (rule Replace_iff [THEN iffD2], blast) 

(*Elimination; may asssume there is a unique y such that P(x,y), namely y=b. *)
lemma ReplaceE: 
    "[| b : {y. x\<in>A, P(x,y)};   
        !!x. [| x: A;  P(x,b);  \<forall>y. P(x,y)-->y=b |] ==> R  
     |] ==> R"
by (rule Replace_iff [THEN iffD1, THEN bexE], simp+)

(*As above but without the (generally useless) 3rd assumption*)
lemma ReplaceE2 [elim!]: 
    "[| b : {y. x\<in>A, P(x,y)};   
        !!x. [| x: A;  P(x,b) |] ==> R  
     |] ==> R"
by (erule ReplaceE, blast) 

lemma Replace_cong [cong]:
    "[| A=B;  !!x y. x\<in>B ==> P(x,y) <-> Q(x,y) |] ==>  
     Replace(A,P) = Replace(B,Q)"
apply (rule equality_iffI) 
apply (simp add: Replace_iff) 
done


subsection{*Rules for RepFun*}

lemma RepFunI: "a \<in> A ==> f(a) : {f(x). x\<in>A}"
by (simp add: RepFun_def Replace_iff, blast)

(*Useful for coinduction proofs*)
lemma RepFun_eqI [intro]: "[| b=f(a);  a \<in> A |] ==> b : {f(x). x\<in>A}"
apply (erule ssubst)
apply (erule RepFunI)
done

lemma RepFunE [elim!]:
    "[| b : {f(x). x\<in>A};   
        !!x.[| x\<in>A;  b=f(x) |] ==> P |] ==>  
     P"
by (simp add: RepFun_def Replace_iff, blast) 

lemma RepFun_cong [cong]: 
    "[| A=B;  !!x. x\<in>B ==> f(x)=g(x) |] ==> RepFun(A,f) = RepFun(B,g)"
by (simp add: RepFun_def)

lemma RepFun_iff [simp]: "b : {f(x). x\<in>A} <-> (\<exists>x\<in>A. b=f(x))"
by (unfold Bex_def, blast)

lemma triv_RepFun [simp]: "{x. x\<in>A} = A"
by blast


subsection{*Rules for Collect -- forming a subset by separation*}

(*Separation is derivable from Replacement*)
lemma separation [simp]: "a : {x\<in>A. P(x)} <-> a\<in>A & P(a)"
by (unfold Collect_def, blast)

lemma CollectI [intro!]: "[| a\<in>A;  P(a) |] ==> a : {x\<in>A. P(x)}"
by simp

lemma CollectE [elim!]: "[| a : {x\<in>A. P(x)};  [| a\<in>A; P(a) |] ==> R |] ==> R"
by simp

lemma CollectD1: "a : {x\<in>A. P(x)} ==> a\<in>A"
by (erule CollectE, assumption)

lemma CollectD2: "a : {x\<in>A. P(x)} ==> P(a)"
by (erule CollectE, assumption)

lemma Collect_cong [cong]:
    "[| A=B;  !!x. x\<in>B ==> P(x) <-> Q(x) |]  
     ==> Collect(A, %x. P(x)) = Collect(B, %x. Q(x))"
by (simp add: Collect_def)


subsection{*Rules for Unions*}

declare Union_iff [simp]

(*The order of the premises presupposes that C is rigid; A may be flexible*)
lemma UnionI [intro]: "[| B: C;  A: B |] ==> A: Union(C)"
by (simp, blast)

lemma UnionE [elim!]: "[| A \<in> Union(C);  !!B.[| A: B;  B: C |] ==> R |] ==> R"
by (simp, blast)


subsection{*Rules for Unions of families*}
(* \<Union>x\<in>A. B(x) abbreviates Union({B(x). x\<in>A}) *)

lemma UN_iff [simp]: "b : (\<Union>x\<in>A. B(x)) <-> (\<exists>x\<in>A. b \<in> B(x))"
by (simp add: Bex_def, blast)

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma UN_I: "[| a: A;  b: B(a) |] ==> b: (\<Union>x\<in>A. B(x))"
by (simp, blast)


lemma UN_E [elim!]: 
    "[| b : (\<Union>x\<in>A. B(x));  !!x.[| x: A;  b: B(x) |] ==> R |] ==> R"
by blast 

lemma UN_cong: 
    "[| A=B;  !!x. x\<in>B ==> C(x)=D(x) |] ==> (\<Union>x\<in>A. C(x)) = (\<Union>x\<in>B. D(x))"
by simp 


(*No "Addcongs [UN_cong]" because \<Union>is a combination of constants*)

(* UN_E appears before UnionE so that it is tried first, to avoid expensive
  calls to hyp_subst_tac.  Cannot include UN_I as it is unsafe: would enlarge
  the search space.*)


subsection{*Rules for the empty set*}

(*The set {x\<in>0. False} is empty; by foundation it equals 0 
  See Suppes, page 21.*)
lemma not_mem_empty [simp]: "a ~: 0"
apply (cut_tac foundation)
apply (best dest: equalityD2)
done

lemmas emptyE [elim!] = not_mem_empty [THEN notE, standard]


lemma empty_subsetI [simp]: "0 <= A"
by blast 

lemma equals0I: "[| !!y. y\<in>A ==> False |] ==> A=0"
by blast

lemma equals0D [dest]: "A=0 ==> a ~: A"
by blast

declare sym [THEN equals0D, dest]

lemma not_emptyI: "a\<in>A ==> A ~= 0"
by blast

lemma not_emptyE:  "[| A ~= 0;  !!x. x\<in>A ==> R |] ==> R"
by blast


subsection{*Rules for Inter*}

(*Not obviously useful for proving InterI, InterD, InterE*)
lemma Inter_iff: "A \<in> Inter(C) <-> (\<forall>x\<in>C. A: x) & C\<noteq>0"
by (simp add: Inter_def Ball_def, blast)

(* Intersection is well-behaved only if the family is non-empty! *)
lemma InterI [intro!]: 
    "[| !!x. x: C ==> A: x;  C\<noteq>0 |] ==> A \<in> Inter(C)"
by (simp add: Inter_iff)

(*A "destruct" rule -- every B in C contains A as an element, but
  A\<in>B can hold when B\<in>C does not!  This rule is analogous to "spec". *)
lemma InterD [elim]: "[| A \<in> Inter(C);  B \<in> C |] ==> A \<in> B"
by (unfold Inter_def, blast)

(*"Classical" elimination rule -- does not require exhibiting B\<in>C *)
lemma InterE [elim]: 
    "[| A \<in> Inter(C);  B~:C ==> R;  A\<in>B ==> R |] ==> R"
by (simp add: Inter_def, blast) 
  

subsection{*Rules for Intersections of families*}

(* \<Inter>x\<in>A. B(x) abbreviates Inter({B(x). x\<in>A}) *)

lemma INT_iff: "b : (\<Inter>x\<in>A. B(x)) <-> (\<forall>x\<in>A. b \<in> B(x)) & A\<noteq>0"
by (force simp add: Inter_def)

lemma INT_I: "[| !!x. x: A ==> b: B(x);  A\<noteq>0 |] ==> b: (\<Inter>x\<in>A. B(x))"
by blast

lemma INT_E: "[| b : (\<Inter>x\<in>A. B(x));  a: A |] ==> b \<in> B(a)"
by blast

lemma INT_cong:
    "[| A=B;  !!x. x\<in>B ==> C(x)=D(x) |] ==> (\<Inter>x\<in>A. C(x)) = (\<Inter>x\<in>B. D(x))"
by simp

(*No "Addcongs [INT_cong]" because \<Inter>is a combination of constants*)


subsection{*Rules for Powersets*}

lemma PowI: "A <= B ==> A \<in> Pow(B)"
by (erule Pow_iff [THEN iffD2])

lemma PowD: "A \<in> Pow(B)  ==>  A<=B"
by (erule Pow_iff [THEN iffD1])

declare Pow_iff [iff]

lemmas Pow_bottom = empty_subsetI [THEN PowI] (* 0 \<in> Pow(B) *)
lemmas Pow_top = subset_refl [THEN PowI] (* A \<in> Pow(A) *)


subsection{*Cantor's Theorem: There is no surjection from a set to its powerset.*}

(*The search is undirected.  Allowing redundant introduction rules may 
  make it diverge.  Variable b represents ANY map, such as
  (lam x\<in>A.b(x)): A->Pow(A). *)
lemma cantor: "\<exists>S \<in> Pow(A). \<forall>x\<in>A. b(x) ~= S"
by (best elim!: equalityCE del: ReplaceI RepFun_eqI)

ML
{*
val lam_def = thm "lam_def";
val domain_def = thm "domain_def";
val range_def = thm "range_def";
val image_def = thm "image_def";
val vimage_def = thm "vimage_def";
val field_def = thm "field_def";
val Inter_def = thm "Inter_def";
val Ball_def = thm "Ball_def";
val Bex_def = thm "Bex_def";

val ballI = thm "ballI";
val bspec = thm "bspec";
val rev_ballE = thm "rev_ballE";
val ballE = thm "ballE";
val rev_bspec = thm "rev_bspec";
val ball_triv = thm "ball_triv";
val ball_cong = thm "ball_cong";
val bexI = thm "bexI";
val rev_bexI = thm "rev_bexI";
val bexCI = thm "bexCI";
val bexE = thm "bexE";
val bex_triv = thm "bex_triv";
val bex_cong = thm "bex_cong";
val subst_elem = thm "subst_elem";
val subsetI = thm "subsetI";
val subsetD = thm "subsetD";
val subsetCE = thm "subsetCE";
val rev_subsetD = thm "rev_subsetD";
val contra_subsetD = thm "contra_subsetD";
val rev_contra_subsetD = thm "rev_contra_subsetD";
val subset_refl = thm "subset_refl";
val subset_trans = thm "subset_trans";
val subset_iff = thm "subset_iff";
val equalityI = thm "equalityI";
val equality_iffI = thm "equality_iffI";
val equalityD1 = thm "equalityD1";
val equalityD2 = thm "equalityD2";
val equalityE = thm "equalityE";
val equalityCE = thm "equalityCE";
val setup_induction = thm "setup_induction";
val Replace_iff = thm "Replace_iff";
val ReplaceI = thm "ReplaceI";
val ReplaceE = thm "ReplaceE";
val ReplaceE2 = thm "ReplaceE2";
val Replace_cong = thm "Replace_cong";
val RepFunI = thm "RepFunI";
val RepFun_eqI = thm "RepFun_eqI";
val RepFunE = thm "RepFunE";
val RepFun_cong = thm "RepFun_cong";
val RepFun_iff = thm "RepFun_iff";
val triv_RepFun = thm "triv_RepFun";
val separation = thm "separation";
val CollectI = thm "CollectI";
val CollectE = thm "CollectE";
val CollectD1 = thm "CollectD1";
val CollectD2 = thm "CollectD2";
val Collect_cong = thm "Collect_cong";
val UnionI = thm "UnionI";
val UnionE = thm "UnionE";
val UN_iff = thm "UN_iff";
val UN_I = thm "UN_I";
val UN_E = thm "UN_E";
val UN_cong = thm "UN_cong";
val Inter_iff = thm "Inter_iff";
val InterI = thm "InterI";
val InterD = thm "InterD";
val InterE = thm "InterE";
val INT_iff = thm "INT_iff";
val INT_I = thm "INT_I";
val INT_E = thm "INT_E";
val INT_cong = thm "INT_cong";
val PowI = thm "PowI";
val PowD = thm "PowD";
val Pow_bottom = thm "Pow_bottom";
val Pow_top = thm "Pow_top";
val not_mem_empty = thm "not_mem_empty";
val emptyE = thm "emptyE";
val empty_subsetI = thm "empty_subsetI";
val equals0I = thm "equals0I";
val equals0D = thm "equals0D";
val not_emptyI = thm "not_emptyI";
val not_emptyE = thm "not_emptyE";
val cantor = thm "cantor";
*}

(*Functions for ML scripts*)
ML
{*
(*Converts A<=B to x\<in>A ==> x\<in>B*)
fun impOfSubs th = th RSN (2, rev_subsetD);

(*Takes assumptions \<forall>x\<in>A.P(x) and a\<in>A; creates assumption P(a)*)
val ball_tac = dtac bspec THEN' assume_tac
*}

end

