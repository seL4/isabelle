(*  Title:      ZF/IMP/Com.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer and Robert Sandner, TU München
*)

header {* Arithmetic expressions, boolean expressions, commands *}

theory Com = Main:


subsection {* Arithmetic expressions *}

consts
  loc :: i
  aexp :: i

datatype \<subseteq> "univ(loc \<union> (nat -> nat) \<union> ((nat \<times> nat) -> nat))"
  aexp = N ("n \<in> nat")
       | X ("x \<in> loc")
       | Op1 ("f \<in> nat -> nat", "a \<in> aexp")
       | Op2 ("f \<in> (nat \<times> nat) -> nat", "a0 \<in> aexp", "a1 \<in> aexp")


consts evala :: i
syntax "_evala" :: "[i, i] => o"    (infixl "-a->" 50)
translations "p -a-> n" == "<p,n> \<in> evala"

inductive
  domains "evala" \<subseteq> "(aexp \<times> (loc -> nat)) \<times> nat"
  intros
    N:   "[| n \<in> nat;  sigma \<in> loc->nat |] ==> <N(n),sigma> -a-> n"
    X:   "[| x \<in> loc;  sigma \<in> loc->nat |] ==> <X(x),sigma> -a-> sigma`x"
    Op1: "[| <e,sigma> -a-> n; f \<in> nat -> nat |] ==> <Op1(f,e),sigma> -a-> f`n"
    Op2: "[| <e0,sigma> -a-> n0;  <e1,sigma>  -a-> n1; f \<in> (nat\<times>nat) -> nat |]
          ==> <Op2(f,e0,e1),sigma> -a-> f`<n0,n1>"
  type_intros aexp.intros apply_funtype


subsection {* Boolean expressions *}

consts bexp :: i

datatype \<subseteq> "univ(aexp \<union> ((nat \<times> nat)->bool))"
  bexp = true
       | false
       | ROp  ("f \<in> (nat \<times> nat)->bool", "a0 \<in> aexp", "a1 \<in> aexp")
       | noti ("b \<in> bexp")
       | andi ("b0 \<in> bexp", "b1 \<in> bexp")      (infixl 60)
       | ori  ("b0 \<in> bexp", "b1 \<in> bexp")      (infixl 60)


consts evalb :: i
syntax "_evalb" :: "[i,i] => o"    (infixl "-b->" 50)
translations "p -b-> b" == "<p,b> \<in> evalb"

inductive
  domains "evalb" \<subseteq> "(bexp \<times> (loc -> nat)) \<times> bool"
  intros
    true:  "[| sigma \<in> loc -> nat |] ==> <true,sigma> -b-> 1"
    false: "[| sigma \<in> loc -> nat |] ==> <false,sigma> -b-> 0"
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


subsection {* Commands *}

consts com :: i
datatype com =
    skip                                  ("\<SKIP>" [])
  | assignment ("x \<in> loc", "a \<in> aexp")       (infixl "\<ASSN>" 60)
  | semicolon ("c0 \<in> com", "c1 \<in> com")       ("_\<SEQ> _"  [60, 60] 10)
  | while ("b \<in> bexp", "c \<in> com")            ("\<WHILE> _ \<DO> _"  60)
  | if ("b \<in> bexp", "c0 \<in> com", "c1 \<in> com")    ("\<IF> _ \<THEN> _ \<ELSE> _" 60)


consts evalc :: i
syntax "_evalc" :: "[i, i] => o"    (infixl "-c->" 50)
translations "p -c-> s" == "<p,s> \<in> evalc"

inductive
  domains "evalc" \<subseteq> "(com \<times> (loc -> nat)) \<times> (loc -> nat)"
  intros
    skip:    "[| sigma \<in> loc -> nat |] ==> <\<SKIP>,sigma> -c-> sigma"

    assign:  "[| m \<in> nat; x \<in> loc; <a,sigma> -a-> m |]
              ==> <x \<ASSN> a,sigma> -c-> sigma(x:=m)"

    semi:    "[| <c0,sigma> -c-> sigma2; <c1,sigma2> -c-> sigma1 |]
              ==> <c0\<SEQ> c1, sigma> -c-> sigma1"

    if1:     "[| b \<in> bexp; c1 \<in> com; sigma \<in> loc->nat;
                 <b,sigma> -b-> 1; <c0,sigma> -c-> sigma1 |]
              ==> <\<IF> b \<THEN> c0 \<ELSE> c1, sigma> -c-> sigma1"

    if0:     "[| b \<in> bexp; c0 \<in> com; sigma \<in> loc->nat;
                 <b,sigma> -b-> 0; <c1,sigma> -c-> sigma1 |]
               ==> <\<IF> b \<THEN> c0 \<ELSE> c1, sigma> -c-> sigma1"

    while0:   "[| c \<in> com; <b, sigma> -b-> 0 |]
               ==> <\<WHILE> b \<DO> c,sigma> -c-> sigma"

    while1:   "[| c \<in> com; <b,sigma> -b-> 1; <c,sigma> -c-> sigma2;
                  <\<WHILE> b \<DO> c, sigma2> -c-> sigma1 |]
               ==> <\<WHILE> b \<DO> c, sigma> -c-> sigma1"

  type_intros  com.intros update_type
  type_elims   evala.dom_subset [THEN subsetD, elim_format]
               evalb.dom_subset [THEN subsetD, elim_format]


subsection {* Misc lemmas *}

lemmas evala_1 [simp] = evala.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD1]
  and evala_2 [simp] = evala.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD2]
  and evala_3 [simp] = evala.dom_subset [THEN subsetD, THEN SigmaD2]

lemmas evalb_1 [simp] = evalb.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD1]
  and evalb_2 [simp] = evalb.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD2]
  and evalb_3 [simp] = evalb.dom_subset [THEN subsetD, THEN SigmaD2]

lemmas evalc_1 [simp] = evalc.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD1]
  and evalc_2 [simp] = evalc.dom_subset [THEN subsetD, THEN SigmaD1, THEN SigmaD2]
  and evalc_3 [simp] = evalc.dom_subset [THEN subsetD, THEN SigmaD2]

inductive_cases
    evala_N_E [elim!]: "<N(n),sigma> -a-> i"
  and evala_X_E [elim!]: "<X(x),sigma> -a-> i"
  and evala_Op1_E [elim!]: "<Op1(f,e),sigma> -a-> i"
  and evala_Op2_E [elim!]: "<Op2(f,a1,a2),sigma>  -a-> i"

end
