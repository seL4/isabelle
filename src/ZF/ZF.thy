(*  Title:      ZF/ZF.thy
    ID:         $Id$
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge

Zermelo-Fraenkel Set Theory
*)

ZF = FOL + Let + 

types
  i

arities
  i :: term

consts

  "0"         :: i                  ("0")   (*the empty set*)
  Pow         :: i => i                     (*power sets*)
  Inf         :: i                          (*infinite set*)

  (* Bounded Quantifiers *)

  Ball, Bex   :: [i, i => o] => o

  (* General Union and Intersection *)

  Union,Inter :: i => i

  (* Variations on Replacement *)

  PrimReplace :: [i, [i, i] => o] => i
  Replace     :: [i, [i, i] => o] => i
  RepFun      :: [i, i => i] => i
  Collect     :: [i, i => o] => i

  (* Descriptions *)

  The         :: (i => o) => i      (binder "THE " 10)
  if          :: [o, i, i] => i

  (* Finite Sets *)

  Upair, cons :: [i, i] => i
  succ        :: i => i

  (* Ordered Pairing *)

  Pair        :: [i, i] => i
  fst, snd    :: i => i
  split       :: [[i, i] => 'a, i] => 'a::logic  (*for pattern-matching*)

  (* Sigma and Pi Operators *)

  Sigma, Pi   :: [i, i => i] => i

  (* Relations and Functions *)

  domain      :: i => i
  range       :: i => i
  field       :: i => i
  converse    :: i => i
  function    :: i => o         (*is a relation a function?*)
  Lambda      :: [i, i => i] => i
  restrict    :: [i, i] => i

  (* Infixes in order of decreasing precedence *)

  "``"        :: [i, i] => i    (infixl 90) (*image*)
  "-``"       :: [i, i] => i    (infixl 90) (*inverse image*)
  "`"         :: [i, i] => i    (infixl 90) (*function application*)
(*"*"         :: [i, i] => i    (infixr 80) (*Cartesian product*)*)
  "Int"       :: [i, i] => i    (infixl 70) (*binary intersection*)
  "Un"        :: [i, i] => i    (infixl 65) (*binary union*)
  "-"         :: [i, i] => i    (infixl 65) (*set difference*)
(*"->"        :: [i, i] => i    (infixr 60) (*function space*)*)
  "<="        :: [i, i] => o    (infixl 50) (*subset relation*)
  ":"         :: [i, i] => o    (infixl 50) (*membership relation*)
(*"~:"        :: [i, i] => o    (infixl 50) (*negated membership relation*)*)


types
  is
  pttrns

syntax
  ""          :: i => is                   ("_")
  "@Enum"     :: [i, is] => is             ("_,/ _")
  "~:"        :: [i, i] => o               (infixl 50)
  "@Finset"   :: is => i                   ("{(_)}")
  "@Tuple"    :: [i, is] => i              ("<(_,/ _)>")
  "@Collect"  :: [pttrn, i, o] => i        ("(1{_: _ ./ _})")
  "@Replace"  :: [pttrn, pttrn, i, o] => i ("(1{_ ./ _: _, _})")
  "@RepFun"   :: [i, pttrn, i] => i        ("(1{_ ./ _: _})" [51,0,51])
  "@INTER"    :: [pttrn, i, i] => i        ("(3INT _:_./ _)" 10)
  "@UNION"    :: [pttrn, i, i] => i        ("(3UN _:_./ _)" 10)
  "@PROD"     :: [pttrn, i, i] => i        ("(3PROD _:_./ _)" 10)
  "@SUM"      :: [pttrn, i, i] => i        ("(3SUM _:_./ _)" 10)
  "->"        :: [i, i] => i               (infixr 60)
  "*"         :: [i, i] => i               (infixr 80)
  "@lam"      :: [pttrn, i, i] => i        ("(3lam _:_./ _)" 10)
  "@Ball"     :: [pttrn, i, o] => o        ("(3ALL _:_./ _)" 10)
  "@Bex"      :: [pttrn, i, o] => o        ("(3EX _:_./ _)" 10)

  (** Patterns -- extends pre-defined type "pttrn" used in abstractions **)

  "@pttrn"  :: pttrns => pttrn            ("<_>")
  ""        ::  pttrn           => pttrns ("_")
  "@pttrns" :: [pttrn,pttrns]   => pttrns ("_,/_")

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
  "%<x,y>.b"    == "split(%x y.b)"


syntax (symbols)
  "op *"      :: [i, i] => i               (infixr "\\<times>" 80)
  "op Int"    :: [i, i] => i    	   (infixl "\\<inter>" 70)
  "op Un"     :: [i, i] => i    	   (infixl "\\<union>" 65)
  "op ->"     :: [i, i] => i               (infixr "\\<rightarrow>" 60)
  "op <="     :: [i, i] => o    	   (infixl "\\<subseteq>" 50)
  "op :"      :: [i, i] => o    	   (infixl "\\<in>" 50)
  "op ~:"     :: [i, i] => o               (infixl "\\<notin>" 50)
  "@Collect"  :: [pttrn, i, o] => i        ("(1{_\\<in> _ ./ _})")
  "@Replace"  :: [pttrn, pttrn, i, o] => i ("(1{_ ./ _\\<in> _, _})")
  "@RepFun"   :: [i, pttrn, i] => i        ("(1{_ ./ _\\<in> _})" [51,0,51])
  "@INTER"    :: [pttrn, i, i] => i        ("(3\\<Inter> _\\<in>_./ _)" 10)
  "@UNION"    :: [pttrn, i, i] => i        ("(3\\<Union> _\\<in>_./ _)" 10)
  "@PROD"     :: [pttrn, i, i] => i        ("(3\\<Pi> _\\<in>_./ _)" 10)
  "@SUM"      :: [pttrn, i, i] => i        ("(3\\<Sigma> _\\<in>_./ _)" 10)
  "@Ball"     :: [pttrn, i, o] => o        ("(3\\<forall> _\\<in>_./ _)" 10)
  "@Bex"      :: [pttrn, i, o] => o        ("(3\\<exists> _\\<in>_./ _)" 10)
  "@Tuple"    :: [i, is] => i              ("\\<langle>(_,/ _)\\<rangle>")
  "@pttrn"    :: pttrns => pttrn           ("\\<langle>_\\<rangle>")


defs

  (* Bounded Quantifiers *)
  Ball_def      "Ball(A, P) == ALL x. x:A --> P(x)"
  Bex_def       "Bex(A, P) == EX x. x:A & P(x)"

  subset_def    "A <= B == ALL x:A. x:B"
  succ_def      "succ(i) == cons(i, i)"

rules

  (* ZF axioms -- see Suppes p.238
     Axioms for Union, Pow and Replace state existence only,
     uniqueness is derivable using extensionality. *)

  extension     "A = B <-> A <= B & B <= A"
  Union_iff     "A : Union(C) <-> (EX B:C. A:B)"
  Pow_iff       "A : Pow(B) <-> A <= B"

  (*We may name this set, though it is not uniquely defined.*)
  infinity      "0:Inf & (ALL y:Inf. succ(y): Inf)"

  (*This formulation facilitates case analysis on A.*)
  foundation    "A=0 | (EX x:A. ALL y:x. y~:A)"

  (*Schema axiom since predicate P is a higher-order variable*)
  replacement   "(ALL x:A. ALL y z. P(x,y) & P(x,z) --> y=z) ==> 
                         b : PrimReplace(A,P) <-> (EX x:A. P(x,b))"

defs

  (* Derived form of replacement, restricting P to its functional part.
     The resulting set (for functional P) is the same as with
     PrimReplace, but the rules are simpler. *)

  Replace_def   "Replace(A,P) == PrimReplace(A, %x y. (EX!z.P(x,z)) & P(x,y))"

  (* Functional form of replacement -- analgous to ML's map functional *)

  RepFun_def    "RepFun(A,f) == {y . x:A, y=f(x)}"

  (* Separation and Pairing can be derived from the Replacement
     and Powerset Axioms using the following definitions. *)

  Collect_def   "Collect(A,P) == {y . x:A, x=y & P(x)}"

  (*Unordered pairs (Upair) express binary union/intersection and cons;
    set enumerations translate as {a,...,z} = cons(a,...,cons(z,0)...)*)

  Upair_def   "Upair(a,b) == {y. x:Pow(Pow(0)), (x=0 & y=a) | (x=Pow(0) & y=b)}"
  cons_def    "cons(a,A) == Upair(a,a) Un A"

  (* Difference, general intersection, binary union and small intersection *)

  Diff_def      "A - B    == { x:A . ~(x:B) }"
  Inter_def     "Inter(A) == { x:Union(A) . ALL y:A. x:y}"
  Un_def        "A Un  B  == Union(Upair(A,B))"
  Int_def       "A Int B  == Inter(Upair(A,B))"

  (* Definite descriptions -- via Replace over the set "1" *)

  the_def       "The(P)    == Union({y . x:{0}, P(y)})"
  if_def        "if(P,a,b) == THE z. P & z=a | ~P & z=b"

  (* this "symmetric" definition works better than {{a}, {a,b}} *)
  Pair_def      "<a,b>  == {{a,a}, {a,b}}"
  fst_def       "fst(p) == THE a. EX b. p=<a,b>"
  snd_def       "snd(p) == THE b. EX a. p=<a,b>"
  split_def     "split(c,p) == c(fst(p), snd(p))"
  Sigma_def     "Sigma(A,B) == UN x:A. UN y:B(x). {<x,y>}"

  (* Operations on relations *)

  (*converse of relation r, inverse of function*)
  converse_def  "converse(r) == {z. w:r, EX x y. w=<x,y> & z=<y,x>}"

  domain_def    "domain(r) == {x. w:r, EX y. w=<x,y>}"
  range_def     "range(r) == domain(converse(r))"
  field_def     "field(r) == domain(r) Un range(r)"
  function_def  "function(r) == ALL x y. <x,y>:r -->   
                                (ALL y'. <x,y'>:r --> y=y')"
  image_def     "r `` A  == {y : range(r) . EX x:A. <x,y> : r}"
  vimage_def    "r -`` A == converse(r)``A"

  (* Abstraction, application and Cartesian product of a family of sets *)

  lam_def       "Lambda(A,b) == {<x,b(x)> . x:A}"
  apply_def     "f`a == THE y. <a,y> : f"
  Pi_def        "Pi(A,B)  == {f: Pow(Sigma(A,B)). A<=domain(f) & function(f)}"

  (* Restrict the function f to the domain A *)
  restrict_def  "restrict(f,A) == lam x:A.f`x"

end


ML

(* Pattern-matching and 'Dependent' type operators *)

val print_translation = 
  [(*("split", split_tr'),*)
   ("Pi",    dependent_tr' ("@PROD", "op ->")),
   ("Sigma", dependent_tr' ("@SUM", "op *"))];

