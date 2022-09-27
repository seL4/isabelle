(*  Title:      ZF/IMP/Com.thy
    Author:     Heiko Loetzbeyer and Robert Sandner, TU München
*)

section \<open>Arithmetic expressions, boolean expressions, commands\<close>

theory Com imports ZF begin


subsection \<open>Arithmetic expressions\<close>

consts
  loc :: i
  aexp :: i

datatype \<subseteq> "univ(loc \<union> (nat -> nat) \<union> ((nat \<times> nat) -> nat))"
  aexp = N ("n \<in> nat")
       | X ("x \<in> loc")
       | Op1 ("f \<in> nat -> nat", "a \<in> aexp")
       | Op2 ("f \<in> (nat \<times> nat) -> nat", "a0 \<in> aexp", "a1 \<in> aexp")


consts evala :: i

abbreviation
  evala_syntax :: "[i, i] \<Rightarrow> o"    (infixl \<open>-a->\<close> 50)
  where "p -a-> n \<equiv> \<langle>p,n\<rangle> \<in> evala"

inductive
  domains "evala" \<subseteq> "(aexp \<times> (loc -> nat)) \<times> nat"
  intros
    N:   "\<lbrakk>n \<in> nat;  sigma \<in> loc->nat\<rbrakk> \<Longrightarrow> <N(n),sigma> -a-> n"
    X:   "\<lbrakk>x \<in> loc;  sigma \<in> loc->nat\<rbrakk> \<Longrightarrow> <X(x),sigma> -a-> sigma`x"
    Op1: "\<lbrakk>\<langle>e,sigma\<rangle> -a-> n; f \<in> nat -> nat\<rbrakk> \<Longrightarrow> <Op1(f,e),sigma> -a-> f`n"
    Op2: "\<lbrakk>\<langle>e0,sigma\<rangle> -a-> n0;  \<langle>e1,sigma\<rangle>  -a-> n1; f \<in> (nat\<times>nat) -> nat\<rbrakk>
          \<Longrightarrow> <Op2(f,e0,e1),sigma> -a-> f`\<langle>n0,n1\<rangle>"
  type_intros aexp.intros apply_funtype


subsection \<open>Boolean expressions\<close>

consts bexp :: i

datatype \<subseteq> "univ(aexp \<union> ((nat \<times> nat)->bool))"
  bexp = true
       | false
       | ROp  ("f \<in> (nat \<times> nat)->bool", "a0 \<in> aexp", "a1 \<in> aexp")
       | noti ("b \<in> bexp")
       | andi ("b0 \<in> bexp", "b1 \<in> bexp")      (infixl \<open>andi\<close> 60)
       | ori  ("b0 \<in> bexp", "b1 \<in> bexp")      (infixl \<open>ori\<close> 60)


consts evalb :: i

abbreviation
  evalb_syntax :: "[i,i] \<Rightarrow> o"    (infixl \<open>-b->\<close> 50)
  where "p -b-> b \<equiv> \<langle>p,b\<rangle> \<in> evalb"

inductive
  domains "evalb" \<subseteq> "(bexp \<times> (loc -> nat)) \<times> bool"
  intros
    true:  "\<lbrakk>sigma \<in> loc -> nat\<rbrakk> \<Longrightarrow> \<langle>true,sigma\<rangle> -b-> 1"
    false: "\<lbrakk>sigma \<in> loc -> nat\<rbrakk> \<Longrightarrow> \<langle>false,sigma\<rangle> -b-> 0"
    ROp:   "\<lbrakk>\<langle>a0,sigma\<rangle> -a-> n0; \<langle>a1,sigma\<rangle> -a-> n1; f \<in> (nat*nat)->bool\<rbrakk>
           \<Longrightarrow> <ROp(f,a0,a1),sigma> -b-> f`\<langle>n0,n1\<rangle> "
    noti:  "\<lbrakk>\<langle>b,sigma\<rangle> -b-> w\<rbrakk> \<Longrightarrow> <noti(b),sigma> -b-> not(w)"
    andi:  "\<lbrakk>\<langle>b0,sigma\<rangle> -b-> w0; \<langle>b1,sigma\<rangle> -b-> w1\<rbrakk>
          \<Longrightarrow> <b0 andi b1,sigma> -b-> (w0 and w1)"
    ori:   "\<lbrakk>\<langle>b0,sigma\<rangle> -b-> w0; \<langle>b1,sigma\<rangle> -b-> w1\<rbrakk>
            \<Longrightarrow> <b0 ori b1,sigma> -b-> (w0 or w1)"
  type_intros  bexp.intros
               apply_funtype and_type or_type bool_1I bool_0I not_type
  type_elims   evala.dom_subset [THEN subsetD, elim_format]


subsection \<open>Commands\<close>

consts com :: i
datatype com =
    skip                                  (\<open>\<SKIP>\<close> [])
  | assignment ("x \<in> loc", "a \<in> aexp")       (infixl \<open>\<ASSN>\<close> 60)
  | semicolon ("c0 \<in> com", "c1 \<in> com")       (\<open>_\<SEQ> _\<close>  [60, 60] 10)
  | while ("b \<in> bexp", "c \<in> com")            (\<open>\<WHILE> _ \<DO> _\<close>  60)
  | "if" ("b \<in> bexp", "c0 \<in> com", "c1 \<in> com")    (\<open>\<IF> _ \<THEN> _ \<ELSE> _\<close> 60)


consts evalc :: i

abbreviation
  evalc_syntax :: "[i, i] \<Rightarrow> o"    (infixl \<open>-c->\<close> 50)
  where "p -c-> s \<equiv> \<langle>p,s\<rangle> \<in> evalc"

inductive
  domains "evalc" \<subseteq> "(com \<times> (loc -> nat)) \<times> (loc -> nat)"
  intros
    skip:    "\<lbrakk>sigma \<in> loc -> nat\<rbrakk> \<Longrightarrow> <\<SKIP>,sigma> -c-> sigma"

    assign:  "\<lbrakk>m \<in> nat; x \<in> loc; \<langle>a,sigma\<rangle> -a-> m\<rbrakk>
              \<Longrightarrow> <x \<ASSN> a,sigma> -c-> sigma(x:=m)"

    semi:    "\<lbrakk>\<langle>c0,sigma\<rangle> -c-> sigma2; \<langle>c1,sigma2\<rangle> -c-> sigma1\<rbrakk>
              \<Longrightarrow> <c0\<SEQ> c1, sigma> -c-> sigma1"

    if1:     "\<lbrakk>b \<in> bexp; c1 \<in> com; sigma \<in> loc->nat;
                 \<langle>b,sigma\<rangle> -b-> 1; \<langle>c0,sigma\<rangle> -c-> sigma1\<rbrakk>
              \<Longrightarrow> <\<IF> b \<THEN> c0 \<ELSE> c1, sigma> -c-> sigma1"

    if0:     "\<lbrakk>b \<in> bexp; c0 \<in> com; sigma \<in> loc->nat;
                 \<langle>b,sigma\<rangle> -b-> 0; \<langle>c1,sigma\<rangle> -c-> sigma1\<rbrakk>
               \<Longrightarrow> <\<IF> b \<THEN> c0 \<ELSE> c1, sigma> -c-> sigma1"

    while0:   "\<lbrakk>c \<in> com; \<langle>b, sigma\<rangle> -b-> 0\<rbrakk>
               \<Longrightarrow> <\<WHILE> b \<DO> c,sigma> -c-> sigma"

    while1:   "\<lbrakk>c \<in> com; \<langle>b,sigma\<rangle> -b-> 1; \<langle>c,sigma\<rangle> -c-> sigma2;
                  <\<WHILE> b \<DO> c, sigma2> -c-> sigma1\<rbrakk>
               \<Longrightarrow> <\<WHILE> b \<DO> c, sigma> -c-> sigma1"

  type_intros  com.intros update_type
  type_elims   evala.dom_subset [THEN subsetD, elim_format]
               evalb.dom_subset [THEN subsetD, elim_format]


subsection \<open>Misc lemmas\<close>

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
