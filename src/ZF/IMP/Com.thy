(*  Title:      ZF/IMP/Com.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM

Arithmetic expressions, Boolean expressions, Commands

And their Operational semantics
*)

theory Com = Main:

(** Arithmetic expressions **)
consts  loc  :: i
        aexp :: i

datatype <= "univ(loc Un (nat->nat) Un ((nat*nat) -> nat) )"
  "aexp" = N ("n \<in> nat")
         | X ("x \<in> loc")
         | Op1 ("f \<in> nat -> nat", "a \<in> aexp")
         | Op2 ("f \<in> (nat*nat) -> nat", "a0 \<in> aexp", "a1 \<in> aexp")


(** Evaluation of arithmetic expressions **)
consts  evala    :: "i"
        "-a->"   :: "[i,i] => o"                  (infixl 50)
translations
    "p -a-> n" == "<p,n> \<in> evala"
inductive
  domains "evala" <= "(aexp * (loc -> nat)) * nat"
  intros 
    N:   "[| n \<in> nat;  sigma \<in> loc->nat |] ==> <N(n),sigma> -a-> n"
    X:   "[| x \<in> loc;  sigma \<in> loc->nat |] ==> <X(x),sigma> -a-> sigma`x"
    Op1: "[| <e,sigma> -a-> n; f \<in> nat -> nat |] ==> <Op1(f,e),sigma> -a-> f`n"
    Op2: "[| <e0,sigma> -a-> n0;  <e1,sigma>  -a-> n1; f \<in> (nat*nat) -> nat |] 
          ==> <Op2(f,e0,e1),sigma> -a-> f`<n0,n1>"
  type_intros aexp.intros apply_funtype


(** Boolean expressions **)
consts  bexp :: i

datatype <= "univ(aexp Un ((nat*nat)->bool) )"
  "bexp" = true
         | false
         | ROp  ("f \<in> (nat*nat)->bool", "a0 \<in> aexp", "a1 \<in> aexp")
         | noti ("b \<in> bexp")
         | andi ("b0 \<in> bexp", "b1 \<in> bexp")      (infixl 60)
         | ori  ("b0 \<in> bexp", "b1 \<in> bexp")      (infixl 60)


(** Evaluation of boolean expressions **)
consts evalb    :: "i"
       "-b->"   :: "[i,i] => o"                   (infixl 50)

translations
    "p -b-> b" == "<p,b> \<in> evalb"

inductive
  domains "evalb" <= "(bexp * (loc -> nat)) * bool"
  intros (*avoid clash with ML constructors true, false*)
    tru:   "[| sigma \<in> loc -> nat |] ==> <true,sigma> -b-> 1"
    fls:   "[| sigma \<in> loc -> nat |] ==> <false,sigma> -b-> 0"
    ROp:   "[| <a0,sigma> -a-> n0; <a1,sigma> -a-> n1; f \<in> (nat*nat)->bool |] 
           ==> <ROp(f,a0,a1),sigma> -b-> f`<n0,n1> "
    noti:  "[| <b,sigma> -b-> w |] ==> <noti(b),sigma> -b-> not(w)"
    andi:  "[| <b0,sigma> -b-> w0; <b1,sigma> -b-> w1 |] 
          ==> <b0 andi b1,sigma> -b-> (w0 and w1)"
    ori:   "[| <b0,sigma> -b-> w0; <b1,sigma> -b-> w1 |] 
            ==> <b0 ori b1,sigma> -b-> (w0 or w1)"
  type_intros  bexp.intros 
               apply_funtype and_type or_type bool_1I bool_0I not_type
  type_elims   evala.dom_subset [THEN subsetD, elim_format]


(** Commands **)
consts  com :: i

datatype 
  "com" = skip
        | asgt ("x \<in> loc", "a \<in> aexp")             (infixl 60)
        | semic("c0 \<in> com", "c1 \<in> com")            ("_; _"  [60, 60] 10)
        | while("b \<in> bexp", "c \<in> com")             ("while _ do _"  60)
        | ifc  ("b \<in> bexp", "c0 \<in> com", "c1 \<in> com") ("ifc _ then _ else _" 60)

(*Constructor ";" has low precedence to avoid syntactic ambiguities
  with [| m \<in> nat; x \<in> loc; ... |] ==> ...  It usually will need parentheses.*)

(** Execution of commands **)
consts  evalc    :: "i"
        "-c->"   :: "[i,i] => o"                   (infixl 50)

translations
       "p -c-> s" == "<p,s> \<in> evalc"

inductive
  domains "evalc" <= "(com * (loc -> nat)) * (loc -> nat)"
  intros
    skip:    "[| sigma \<in> loc -> nat |] ==> <skip,sigma> -c-> sigma"

    assign:  "[| m \<in> nat; x \<in> loc; <a,sigma> -a-> m |] 
              ==> <x asgt a,sigma> -c-> sigma(x:=m)"

    semi:    "[| <c0,sigma> -c-> sigma2; <c1,sigma2> -c-> sigma1 |] 
              ==> <c0 ; c1, sigma> -c-> sigma1"

    ifc1:    "[| b \<in> bexp; c1 \<in> com; sigma \<in> loc->nat;   
                 <b,sigma> -b-> 1; <c0,sigma> -c-> sigma1 |] 
              ==> <ifc b then c0 else c1, sigma> -c-> sigma1"

    ifc0:    "[| b \<in> bexp; c0 \<in> com; sigma \<in> loc->nat;   
                 <b,sigma> -b-> 0; <c1,sigma> -c-> sigma1 |] 
               ==> <ifc b then c0 else c1, sigma> -c-> sigma1"

    while0:   "[| c \<in> com; <b, sigma> -b-> 0 |] 
               ==> <while b do c,sigma> -c-> sigma"

    while1:   "[| c \<in> com; <b,sigma> -b-> 1; <c,sigma> -c-> sigma2; 
                  <while b do c, sigma2> -c-> sigma1 |] 
               ==> <while b do c, sigma> -c-> sigma1"

  type_intros  com.intros update_type
  type_elims   evala.dom_subset [THEN subsetD, elim_format]
               evalb.dom_subset [THEN subsetD, elim_format]


(*** type_intros for evala ***)

lemmas evala_1 [simp] = 
       evala.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD1]
lemmas evala_2 [simp] = 
       evala.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD2]
lemmas evala_3 [simp] = 
       evala.dom_subset [THEN subsetD, THEN SigmaD2]


(*** type_intros for evalb ***)

lemmas evalb_1 [simp] = 
       evalb.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD1]
lemmas evalb_2 [simp] = 
       evalb.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD2]
lemmas evalb_3 [simp] = 
       evalb.dom_subset [THEN subsetD, THEN SigmaD2]

(*** type_intros for evalc ***)

lemmas evalc_1 [simp] = 
       evalc.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD1]
lemmas evalc_2 [simp] = 
       evalc.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD2]
lemmas evalc_3 [simp] = 
       evalc.dom_subset [THEN subsetD, THEN SigmaD2]

inductive_cases evala_N_E [elim!]: "<N(n),sigma> -a-> i"
inductive_cases evala_X_E [elim!]: "<X(x),sigma> -a-> i"
inductive_cases evala_Op1_E [elim!]: "<Op1(f,e),sigma> -a-> i"
inductive_cases evala_Op2_E [elim!]: "<Op2(f,a1,a2),sigma>  -a-> i"

end
