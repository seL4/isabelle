(*  Title:      ZF/Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section\<open>The Integers as Equivalence Classes Over Pairs of Natural Numbers\<close>

theory Int imports EquivClass ArithSimp begin

definition
  intrel :: i  where
    "intrel \<equiv> {p \<in> (nat*nat)*(nat*nat).
                \<exists>x1 y1 x2 y2. p=<\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>> \<and> x1#+y2 = x2#+y1}"

definition
  int :: i  where
    "int \<equiv> (nat*nat)//intrel"

definition
  int_of :: "i\<Rightarrow>i" \<comment> \<open>coercion from nat to int\<close>  (\<open>(\<open>open_block notation=\<open>prefix $#\<close>\<close>$# _)\<close> [80] 80)
  where "$# m \<equiv> intrel `` {<natify(m), 0>}"

definition
  intify :: "i\<Rightarrow>i" \<comment> \<open>coercion from ANYTHING to int\<close>  where
    "intify(m) \<equiv> if m \<in> int then m else $#0"

definition
  raw_zminus :: "i\<Rightarrow>i"  where
    "raw_zminus(z) \<equiv> \<Union>\<langle>x,y\<rangle>\<in>z. intrel``{\<langle>y,x\<rangle>}"

definition
  zminus :: "i\<Rightarrow>i"  (\<open>(\<open>open_block notation=\<open>prefix $-\<close>\<close>$- _)\<close> [80] 80)
  where "$- z \<equiv> raw_zminus (intify(z))"

definition
  znegative   ::      "i\<Rightarrow>o"  where
    "znegative(z) \<equiv> \<exists>x y. x<y \<and> y\<in>nat \<and> \<langle>x,y\<rangle>\<in>z"

definition
  iszero      ::      "i\<Rightarrow>o"  where
    "iszero(z) \<equiv> z = $# 0"

definition
  raw_nat_of  :: "i\<Rightarrow>i"  where
  "raw_nat_of(z) \<equiv> natify (\<Union>\<langle>x,y\<rangle>\<in>z. x#-y)"

definition
  nat_of  :: "i\<Rightarrow>i"  where
  "nat_of(z) \<equiv> raw_nat_of (intify(z))"

definition
  zmagnitude  ::      "i\<Rightarrow>i"  where
  \<comment> \<open>could be replaced by an absolute value function from int to int?\<close>
    "zmagnitude(z) \<equiv>
     THE m. m\<in>nat \<and> ((\<not> znegative(z) \<and> z = $# m) |
                       (znegative(z) \<and> $- z = $# m))"

definition
  raw_zmult   ::      "[i,i]\<Rightarrow>i"  where
    (*Cannot use UN\<langle>x1,y2\<rangle> here or in zadd because of the form of congruent2.
      Perhaps a "curried" or even polymorphic congruent predicate would be
      better.*)
     "raw_zmult(z1,z2) \<equiv>
       \<Union>p1\<in>z1. \<Union>p2\<in>z2.  split(\<lambda>x1 y1. split(\<lambda>x2 y2.
                   intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1)"

definition
  zmult       ::      "[i,i]\<Rightarrow>i"      (infixl \<open>$*\<close> 70)  where
     "z1 $* z2 \<equiv> raw_zmult (intify(z1),intify(z2))"

definition
  raw_zadd    ::      "[i,i]\<Rightarrow>i"  where
     "raw_zadd (z1, z2) \<equiv>
       \<Union>z1\<in>z1. \<Union>z2\<in>z2. let \<langle>x1,y1\<rangle>=z1; \<langle>x2,y2\<rangle>=z2
                           in intrel``{<x1#+x2, y1#+y2>}"

definition
  zadd        ::      "[i,i]\<Rightarrow>i"      (infixl \<open>$+\<close> 65)  where
     "z1 $+ z2 \<equiv> raw_zadd (intify(z1),intify(z2))"

definition
  zdiff        ::      "[i,i]\<Rightarrow>i"      (infixl \<open>$-\<close> 65)  where
     "z1 $- z2 \<equiv> z1 $+ zminus(z2)"

definition
  zless        ::      "[i,i]\<Rightarrow>o"      (infixl \<open>$<\<close> 50)  where
     "z1 $< z2 \<equiv> znegative(z1 $- z2)"

definition
  zle          ::      "[i,i]\<Rightarrow>o"      (infixl \<open>$\<le>\<close> 50)  where
     "z1 $\<le> z2 \<equiv> z1 $< z2 | intify(z1)=intify(z2)"


declare quotientE [elim!]

subsection\<open>Proving that \<^term>\<open>intrel\<close> is an equivalence relation\<close>

(** Natural deduction for intrel **)

lemma intrel_iff [simp]:
    "<\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>>: intrel \<longleftrightarrow>
     x1\<in>nat \<and> y1\<in>nat \<and> x2\<in>nat \<and> y2\<in>nat \<and> x1#+y2 = x2#+y1"
by (simp add: intrel_def)

lemma intrelI [intro!]:
    "\<lbrakk>x1#+y2 = x2#+y1; x1\<in>nat; y1\<in>nat; x2\<in>nat; y2\<in>nat\<rbrakk>
     \<Longrightarrow> <\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>>: intrel"
by (simp add: intrel_def)

lemma intrelE [elim!]:
  "\<lbrakk>p \<in> intrel;
      \<And>x1 y1 x2 y2. \<lbrakk>p = <\<langle>x1,y1\<rangle>,\<langle>x2,y2\<rangle>>;  x1#+y2 = x2#+y1;
                        x1\<in>nat; y1\<in>nat; x2\<in>nat; y2\<in>nat\<rbrakk> \<Longrightarrow> Q\<rbrakk>
   \<Longrightarrow> Q"
by (simp add: intrel_def, blast)

lemma int_trans_lemma:
     "\<lbrakk>x1 #+ y2 = x2 #+ y1; x2 #+ y3 = x3 #+ y2\<rbrakk> \<Longrightarrow> x1 #+ y3 = x3 #+ y1"
apply (rule sym)
apply (erule add_left_cancel)+
apply (simp_all (no_asm_simp))
done

lemma equiv_intrel: "equiv(nat*nat, intrel)"
apply (simp add: equiv_def refl_def sym_def trans_def)
apply (fast elim!: sym int_trans_lemma)
done

lemma image_intrel_int: "\<lbrakk>m\<in>nat; n\<in>nat\<rbrakk> \<Longrightarrow> intrel `` {\<langle>m,n\<rangle>} \<in> int"
by (simp add: int_def)

declare equiv_intrel [THEN eq_equiv_class_iff, simp]
declare conj_cong [cong]

lemmas eq_intrelD = eq_equiv_class [OF _ equiv_intrel]

(** int_of: the injection from nat to int **)

lemma int_of_type [simp,TC]: "$#m \<in> int"
by (simp add: int_def quotient_def int_of_def, auto)

lemma int_of_eq [iff]: "($# m = $# n) \<longleftrightarrow> natify(m)=natify(n)"
by (simp add: int_of_def)

lemma int_of_inject: "\<lbrakk>$#m = $#n;  m\<in>nat;  n\<in>nat\<rbrakk> \<Longrightarrow> m=n"
by (drule int_of_eq [THEN iffD1], auto)


(** intify: coercion from anything to int **)

lemma intify_in_int [iff,TC]: "intify(x) \<in> int"
by (simp add: intify_def)

lemma intify_ident [simp]: "n \<in> int \<Longrightarrow> intify(n) = n"
by (simp add: intify_def)


subsection\<open>Collapsing rules: to remove \<^term>\<open>intify\<close>
            from arithmetic expressions\<close>

lemma intify_idem [simp]: "intify(intify(x)) = intify(x)"
by simp

lemma int_of_natify [simp]: "$# (natify(m)) = $# m"
by (simp add: int_of_def)

lemma zminus_intify [simp]: "$- (intify(m)) = $- m"
by (simp add: zminus_def)

(** Addition **)

lemma zadd_intify1 [simp]: "intify(x) $+ y = x $+ y"
by (simp add: zadd_def)

lemma zadd_intify2 [simp]: "x $+ intify(y) = x $+ y"
by (simp add: zadd_def)

(** Subtraction **)

lemma zdiff_intify1 [simp]:"intify(x) $- y = x $- y"
by (simp add: zdiff_def)

lemma zdiff_intify2 [simp]:"x $- intify(y) = x $- y"
by (simp add: zdiff_def)

(** Multiplication **)

lemma zmult_intify1 [simp]:"intify(x) $* y = x $* y"
by (simp add: zmult_def)

lemma zmult_intify2 [simp]:"x $* intify(y) = x $* y"
by (simp add: zmult_def)

(** Orderings **)

lemma zless_intify1 [simp]:"intify(x) $< y \<longleftrightarrow> x $< y"
by (simp add: zless_def)

lemma zless_intify2 [simp]:"x $< intify(y) \<longleftrightarrow> x $< y"
by (simp add: zless_def)

lemma zle_intify1 [simp]:"intify(x) $\<le> y \<longleftrightarrow> x $\<le> y"
by (simp add: zle_def)

lemma zle_intify2 [simp]:"x $\<le> intify(y) \<longleftrightarrow> x $\<le> y"
by (simp add: zle_def)


subsection\<open>\<^term>\<open>zminus\<close>: unary negation on \<^term>\<open>int\<close>\<close>

lemma zminus_congruent: "(\<lambda>\<langle>x,y\<rangle>. intrel``{\<langle>y,x\<rangle>}) respects intrel"
by (auto simp add: congruent_def add_ac)

lemma raw_zminus_type: "z \<in> int \<Longrightarrow> raw_zminus(z) \<in> int"
apply (simp add: int_def raw_zminus_def)
apply (typecheck add: UN_equiv_class_type [OF equiv_intrel zminus_congruent])
done

lemma zminus_type [TC,iff]: "$-z \<in> int"
by (simp add: zminus_def raw_zminus_type)

lemma raw_zminus_inject:
     "\<lbrakk>raw_zminus(z) = raw_zminus(w);  z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> z=w"
apply (simp add: int_def raw_zminus_def)
apply (erule UN_equiv_class_inject [OF equiv_intrel zminus_congruent], safe)
apply (auto dest: eq_intrelD simp add: add_ac)
done

lemma zminus_inject_intify [dest!]: "$-z = $-w \<Longrightarrow> intify(z) = intify(w)"
apply (simp add: zminus_def)
apply (blast dest!: raw_zminus_inject)
done

lemma zminus_inject: "\<lbrakk>$-z = $-w;  z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> z=w"
by auto

lemma raw_zminus:
    "\<lbrakk>x\<in>nat;  y\<in>nat\<rbrakk> \<Longrightarrow> raw_zminus(intrel``{\<langle>x,y\<rangle>}) = intrel `` {\<langle>y,x\<rangle>}"
apply (simp add: raw_zminus_def UN_equiv_class [OF equiv_intrel zminus_congruent])
done

lemma zminus:
    "\<lbrakk>x\<in>nat;  y\<in>nat\<rbrakk>
     \<Longrightarrow> $- (intrel``{\<langle>x,y\<rangle>}) = intrel `` {\<langle>y,x\<rangle>}"
by (simp add: zminus_def raw_zminus image_intrel_int)

lemma raw_zminus_zminus: "z \<in> int \<Longrightarrow> raw_zminus (raw_zminus(z)) = z"
by (auto simp add: int_def raw_zminus)

lemma zminus_zminus_intify [simp]: "$- ($- z) = intify(z)"
by (simp add: zminus_def raw_zminus_type raw_zminus_zminus)

lemma zminus_int0 [simp]: "$- ($#0) = $#0"
by (simp add: int_of_def zminus)

lemma zminus_zminus: "z \<in> int \<Longrightarrow> $- ($- z) = z"
by simp


subsection\<open>\<^term>\<open>znegative\<close>: the test for negative integers\<close>

lemma znegative: "\<lbrakk>x\<in>nat; y\<in>nat\<rbrakk> \<Longrightarrow> znegative(intrel``{\<langle>x,y\<rangle>}) \<longleftrightarrow> x<y"
apply (cases "x<y")
apply (auto simp add: znegative_def not_lt_iff_le)
apply (subgoal_tac "y #+ x2 < x #+ y2", force)
apply (rule add_le_lt_mono, auto)
done

(*No natural number is negative!*)
lemma not_znegative_int_of [iff]: "\<not> znegative($# n)"
by (simp add: znegative int_of_def)

lemma znegative_zminus_int_of [simp]: "znegative($- $# succ(n))"
by (simp add: znegative int_of_def zminus natify_succ)

lemma not_znegative_imp_zero: "\<not> znegative($- $# n) \<Longrightarrow> natify(n)=0"
by (simp add: znegative int_of_def zminus Ord_0_lt_iff [THEN iff_sym])


subsection\<open>\<^term>\<open>nat_of\<close>: Coercion of an Integer to a Natural Number\<close>

lemma nat_of_intify [simp]: "nat_of(intify(z)) = nat_of(z)"
by (simp add: nat_of_def)

lemma nat_of_congruent: "(\<lambda>x. (\<lambda>\<langle>x,y\<rangle>. x #- y)(x)) respects intrel"
by (auto simp add: congruent_def split: nat_diff_split)

lemma raw_nat_of:
    "\<lbrakk>x\<in>nat;  y\<in>nat\<rbrakk> \<Longrightarrow> raw_nat_of(intrel``{\<langle>x,y\<rangle>}) = x#-y"
by (simp add: raw_nat_of_def UN_equiv_class [OF equiv_intrel nat_of_congruent])

lemma raw_nat_of_int_of: "raw_nat_of($# n) = natify(n)"
by (simp add: int_of_def raw_nat_of)

lemma nat_of_int_of [simp]: "nat_of($# n) = natify(n)"
by (simp add: raw_nat_of_int_of nat_of_def)

lemma raw_nat_of_type: "raw_nat_of(z) \<in> nat"
by (simp add: raw_nat_of_def)

lemma nat_of_type [iff,TC]: "nat_of(z) \<in> nat"
by (simp add: nat_of_def raw_nat_of_type)

subsection\<open>zmagnitude: magnitide of an integer, as a natural number\<close>

lemma zmagnitude_int_of [simp]: "zmagnitude($# n) = natify(n)"
by (auto simp add: zmagnitude_def int_of_eq)

lemma natify_int_of_eq: "natify(x)=n \<Longrightarrow> $#x = $# n"
apply (drule sym)
apply (simp (no_asm_simp) add: int_of_eq)
done

lemma zmagnitude_zminus_int_of [simp]: "zmagnitude($- $# n) = natify(n)"
apply (simp add: zmagnitude_def)
apply (rule the_equality)
apply (auto dest!: not_znegative_imp_zero natify_int_of_eq
            iff del: int_of_eq, auto)
done

lemma zmagnitude_type [iff,TC]: "zmagnitude(z)\<in>nat"
apply (simp add: zmagnitude_def)
apply (rule theI2, auto)
done

lemma not_zneg_int_of:
     "\<lbrakk>z \<in> int; \<not> znegative(z)\<rbrakk> \<Longrightarrow> \<exists>n\<in>nat. z = $# n"
apply (auto simp add: int_def znegative int_of_def not_lt_iff_le)
apply (rename_tac x y)
apply (rule_tac x="x#-y" in bexI)
apply (auto simp add: add_diff_inverse2)
done

lemma not_zneg_mag [simp]:
     "\<lbrakk>z \<in> int; \<not> znegative(z)\<rbrakk> \<Longrightarrow> $# (zmagnitude(z)) = z"
by (drule not_zneg_int_of, auto)

lemma zneg_int_of:
     "\<lbrakk>znegative(z); z \<in> int\<rbrakk> \<Longrightarrow> \<exists>n\<in>nat. z = $- ($# succ(n))"
by (auto simp add: int_def znegative zminus int_of_def dest!: less_imp_succ_add)

lemma zneg_mag [simp]:
     "\<lbrakk>znegative(z); z \<in> int\<rbrakk> \<Longrightarrow> $# (zmagnitude(z)) = $- z"
by (drule zneg_int_of, auto)

lemma int_cases: "z \<in> int \<Longrightarrow> \<exists>n\<in>nat. z = $# n | z = $- ($# succ(n))"
apply (case_tac "znegative (z) ")
prefer 2 apply (blast dest: not_zneg_mag sym)
apply (blast dest: zneg_int_of)
done

lemma not_zneg_raw_nat_of:
     "\<lbrakk>\<not> znegative(z); z \<in> int\<rbrakk> \<Longrightarrow> $# (raw_nat_of(z)) = z"
apply (drule not_zneg_int_of)
apply (auto simp add: raw_nat_of_type raw_nat_of_int_of)
done

lemma not_zneg_nat_of_intify:
     "\<not> znegative(intify(z)) \<Longrightarrow> $# (nat_of(z)) = intify(z)"
by (simp (no_asm_simp) add: nat_of_def not_zneg_raw_nat_of)

lemma not_zneg_nat_of: "\<lbrakk>\<not> znegative(z); z \<in> int\<rbrakk> \<Longrightarrow> $# (nat_of(z)) = z"
apply (simp (no_asm_simp) add: not_zneg_nat_of_intify)
done

lemma zneg_nat_of [simp]: "znegative(intify(z)) \<Longrightarrow> nat_of(z) = 0"
apply (subgoal_tac "intify(z) \<in> int")
apply (simp add: int_def)
apply (auto simp add: znegative nat_of_def raw_nat_of
            split: nat_diff_split)
done


subsection\<open>\<^term>\<open>zadd\<close>: addition on int\<close>

text\<open>Congruence Property for Addition\<close>
lemma zadd_congruent2:
    "(\<lambda>z1 z2. let \<langle>x1,y1\<rangle>=z1; \<langle>x2,y2\<rangle>=z2
                            in intrel``{<x1#+x2, y1#+y2>})
     respects2 intrel"
apply (simp add: congruent2_def)
(*Proof via congruent2_commuteI seems longer*)
apply safe
apply (simp (no_asm_simp) add: add_assoc Let_def)
(*The rest should be trivial, but rearranging terms is hard
  add_ac does not help rewriting with the assumptions.*)
apply (rule_tac m1 = x1a in add_left_commute [THEN ssubst])
apply (rule_tac m1 = x2a in add_left_commute [THEN ssubst])
apply (simp (no_asm_simp) add: add_assoc [symmetric])
done

lemma raw_zadd_type: "\<lbrakk>z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> raw_zadd(z,w) \<in> int"
apply (simp add: int_def raw_zadd_def)
apply (rule UN_equiv_class_type2 [OF equiv_intrel zadd_congruent2], assumption+)
apply (simp add: Let_def)
done

lemma zadd_type [iff,TC]: "z $+ w \<in> int"
by (simp add: zadd_def raw_zadd_type)

lemma raw_zadd:
  "\<lbrakk>x1\<in>nat; y1\<in>nat;  x2\<in>nat; y2\<in>nat\<rbrakk>
   \<Longrightarrow> raw_zadd (intrel``{\<langle>x1,y1\<rangle>}, intrel``{\<langle>x2,y2\<rangle>}) =
       intrel `` {<x1#+x2, y1#+y2>}"
apply (simp add: raw_zadd_def
             UN_equiv_class2 [OF equiv_intrel equiv_intrel zadd_congruent2])
apply (simp add: Let_def)
done

lemma zadd:
  "\<lbrakk>x1\<in>nat; y1\<in>nat;  x2\<in>nat; y2\<in>nat\<rbrakk>
   \<Longrightarrow> (intrel``{\<langle>x1,y1\<rangle>}) $+ (intrel``{\<langle>x2,y2\<rangle>}) =
       intrel `` {<x1#+x2, y1#+y2>}"
by (simp add: zadd_def raw_zadd image_intrel_int)

lemma raw_zadd_int0: "z \<in> int \<Longrightarrow> raw_zadd ($#0,z) = z"
by (auto simp add: int_def int_of_def raw_zadd)

lemma zadd_int0_intify [simp]: "$#0 $+ z = intify(z)"
by (simp add: zadd_def raw_zadd_int0)

lemma zadd_int0: "z \<in> int \<Longrightarrow> $#0 $+ z = z"
by simp

lemma raw_zminus_zadd_distrib:
     "\<lbrakk>z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> $- raw_zadd(z,w) = raw_zadd($- z, $- w)"
by (auto simp add: zminus raw_zadd int_def)

lemma zminus_zadd_distrib [simp]: "$- (z $+ w) = $- z $+ $- w"
by (simp add: zadd_def raw_zminus_zadd_distrib)

lemma raw_zadd_commute:
     "\<lbrakk>z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> raw_zadd(z,w) = raw_zadd(w,z)"
by (auto simp add: raw_zadd add_ac int_def)

lemma zadd_commute: "z $+ w = w $+ z"
by (simp add: zadd_def raw_zadd_commute)

lemma raw_zadd_assoc:
    "\<lbrakk>z1: int;  z2: int;  z3: int\<rbrakk>
     \<Longrightarrow> raw_zadd (raw_zadd(z1,z2),z3) = raw_zadd(z1,raw_zadd(z2,z3))"
by (auto simp add: int_def raw_zadd add_assoc)

lemma zadd_assoc: "(z1 $+ z2) $+ z3 = z1 $+ (z2 $+ z3)"
by (simp add: zadd_def raw_zadd_type raw_zadd_assoc)

(*For AC rewriting*)
lemma zadd_left_commute: "z1$+(z2$+z3) = z2$+(z1$+z3)"
apply (simp add: zadd_assoc [symmetric])
apply (simp add: zadd_commute)
done

(*Integer addition is an AC operator*)
lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute

lemma int_of_add: "$# (m #+ n) = ($#m) $+ ($#n)"
by (simp add: int_of_def zadd)

lemma int_succ_int_1: "$# succ(m) = $# 1 $+ ($# m)"
by (simp add: int_of_add [symmetric] natify_succ)

lemma int_of_diff:
     "\<lbrakk>m\<in>nat;  n \<le> m\<rbrakk> \<Longrightarrow> $# (m #- n) = ($#m) $- ($#n)"
apply (simp add: int_of_def zdiff_def)
apply (frule lt_nat_in_nat)
apply (simp_all add: zadd zminus add_diff_inverse2)
done

lemma raw_zadd_zminus_inverse: "z \<in> int \<Longrightarrow> raw_zadd (z, $- z) = $#0"
by (auto simp add: int_def int_of_def zminus raw_zadd add_commute)

lemma zadd_zminus_inverse [simp]: "z $+ ($- z) = $#0"
apply (simp add: zadd_def)
apply (subst zminus_intify [symmetric])
apply (rule intify_in_int [THEN raw_zadd_zminus_inverse])
done

lemma zadd_zminus_inverse2 [simp]: "($- z) $+ z = $#0"
by (simp add: zadd_commute zadd_zminus_inverse)

lemma zadd_int0_right_intify [simp]: "z $+ $#0 = intify(z)"
by (rule trans [OF zadd_commute zadd_int0_intify])

lemma zadd_int0_right: "z \<in> int \<Longrightarrow> z $+ $#0 = z"
by simp


subsection\<open>\<^term>\<open>zmult\<close>: Integer Multiplication\<close>

text\<open>Congruence property for multiplication\<close>
lemma zmult_congruent2:
    "(\<lambda>p1 p2. split(\<lambda>x1 y1. split(\<lambda>x2 y2.
                    intrel``{<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}, p2), p1))
     respects2 intrel"
apply (rule equiv_intrel [THEN congruent2_commuteI], auto)
(*Proof that zmult is congruent in one argument*)
apply (rename_tac x y)
apply (frule_tac t = "\<lambda>u. x#*u" in sym [THEN subst_context])
apply (drule_tac t = "\<lambda>u. y#*u" in subst_context)
apply (erule add_left_cancel)+
apply (simp_all add: add_mult_distrib_left)
done


lemma raw_zmult_type: "\<lbrakk>z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> raw_zmult(z,w) \<in> int"
apply (simp add: int_def raw_zmult_def)
apply (rule UN_equiv_class_type2 [OF equiv_intrel zmult_congruent2], assumption+)
apply (simp add: Let_def)
done

lemma zmult_type [iff,TC]: "z $* w \<in> int"
by (simp add: zmult_def raw_zmult_type)

lemma raw_zmult:
     "\<lbrakk>x1\<in>nat; y1\<in>nat;  x2\<in>nat; y2\<in>nat\<rbrakk>
      \<Longrightarrow> raw_zmult(intrel``{\<langle>x1,y1\<rangle>}, intrel``{\<langle>x2,y2\<rangle>}) =
          intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}"
by (simp add: raw_zmult_def
           UN_equiv_class2 [OF equiv_intrel equiv_intrel zmult_congruent2])

lemma zmult:
     "\<lbrakk>x1\<in>nat; y1\<in>nat;  x2\<in>nat; y2\<in>nat\<rbrakk>
      \<Longrightarrow> (intrel``{\<langle>x1,y1\<rangle>}) $* (intrel``{\<langle>x2,y2\<rangle>}) =
          intrel `` {<x1#*x2 #+ y1#*y2, x1#*y2 #+ y1#*x2>}"
by (simp add: zmult_def raw_zmult image_intrel_int)

lemma raw_zmult_int0: "z \<in> int \<Longrightarrow> raw_zmult ($#0,z) = $#0"
by (auto simp add: int_def int_of_def raw_zmult)

lemma zmult_int0 [simp]: "$#0 $* z = $#0"
by (simp add: zmult_def raw_zmult_int0)

lemma raw_zmult_int1: "z \<in> int \<Longrightarrow> raw_zmult ($#1,z) = z"
by (auto simp add: int_def int_of_def raw_zmult)

lemma zmult_int1_intify [simp]: "$#1 $* z = intify(z)"
by (simp add: zmult_def raw_zmult_int1)

lemma zmult_int1: "z \<in> int \<Longrightarrow> $#1 $* z = z"
by simp

lemma raw_zmult_commute:
     "\<lbrakk>z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> raw_zmult(z,w) = raw_zmult(w,z)"
by (auto simp add: int_def raw_zmult add_ac mult_ac)

lemma zmult_commute: "z $* w = w $* z"
by (simp add: zmult_def raw_zmult_commute)

lemma raw_zmult_zminus:
     "\<lbrakk>z \<in> int;  w \<in> int\<rbrakk> \<Longrightarrow> raw_zmult($- z, w) = $- raw_zmult(z, w)"
by (auto simp add: int_def zminus raw_zmult add_ac)

lemma zmult_zminus [simp]: "($- z) $* w = $- (z $* w)"
apply (simp add: zmult_def raw_zmult_zminus)
apply (subst zminus_intify [symmetric], rule raw_zmult_zminus, auto)
done

lemma zmult_zminus_right [simp]: "w $* ($- z) = $- (w $* z)"
by (simp add: zmult_commute [of w])

lemma raw_zmult_assoc:
    "\<lbrakk>z1: int;  z2: int;  z3: int\<rbrakk>
     \<Longrightarrow> raw_zmult (raw_zmult(z1,z2),z3) = raw_zmult(z1,raw_zmult(z2,z3))"
by (auto simp add: int_def raw_zmult add_mult_distrib_left add_ac mult_ac)

lemma zmult_assoc: "(z1 $* z2) $* z3 = z1 $* (z2 $* z3)"
by (simp add: zmult_def raw_zmult_type raw_zmult_assoc)

(*For AC rewriting*)
lemma zmult_left_commute: "z1$*(z2$*z3) = z2$*(z1$*z3)"
apply (simp add: zmult_assoc [symmetric])
apply (simp add: zmult_commute)
done

(*Integer multiplication is an AC operator*)
lemmas zmult_ac = zmult_assoc zmult_commute zmult_left_commute

lemma raw_zadd_zmult_distrib:
    "\<lbrakk>z1: int;  z2: int;  w \<in> int\<rbrakk>
     \<Longrightarrow> raw_zmult(raw_zadd(z1,z2), w) =
         raw_zadd (raw_zmult(z1,w), raw_zmult(z2,w))"
by (auto simp add: int_def raw_zadd raw_zmult add_mult_distrib_left add_ac mult_ac)

lemma zadd_zmult_distrib: "(z1 $+ z2) $* w = (z1 $* w) $+ (z2 $* w)"
by (simp add: zmult_def zadd_def raw_zadd_type raw_zmult_type
              raw_zadd_zmult_distrib)

lemma zadd_zmult_distrib2: "w $* (z1 $+ z2) = (w $* z1) $+ (w $* z2)"
by (simp add: zmult_commute [of w] zadd_zmult_distrib)

lemmas int_typechecks =
  int_of_type zminus_type zmagnitude_type zadd_type zmult_type


(*** Subtraction laws ***)

lemma zdiff_type [iff,TC]: "z $- w \<in> int"
by (simp add: zdiff_def)

lemma zminus_zdiff_eq [simp]: "$- (z $- y) = y $- z"
by (simp add: zdiff_def zadd_commute)

lemma zdiff_zmult_distrib: "(z1 $- z2) $* w = (z1 $* w) $- (z2 $* w)"
apply (simp add: zdiff_def)
apply (subst zadd_zmult_distrib)
apply (simp add: zmult_zminus)
done

lemma zdiff_zmult_distrib2: "w $* (z1 $- z2) = (w $* z1) $- (w $* z2)"
by (simp add: zmult_commute [of w] zdiff_zmult_distrib)

lemma zadd_zdiff_eq: "x $+ (y $- z) = (x $+ y) $- z"
by (simp add: zdiff_def zadd_ac)

lemma zdiff_zadd_eq: "(x $- y) $+ z = (x $+ z) $- y"
by (simp add: zdiff_def zadd_ac)


subsection\<open>The "Less Than" Relation\<close>

(*"Less than" is a linear ordering*)
lemma zless_linear_lemma:
     "\<lbrakk>z \<in> int; w \<in> int\<rbrakk> \<Longrightarrow> z$<w | z=w | w$<z"
apply (simp add: int_def zless_def znegative_def zdiff_def, auto)
apply (simp add: zadd zminus image_iff Bex_def)
apply (rule_tac i = "xb#+ya" and j = "xc #+ y" in Ord_linear_lt)
apply (force dest!: spec simp add: add_ac)+
done

lemma zless_linear: "z$<w | intify(z)=intify(w) | w$<z"
apply (cut_tac z = " intify (z) " and w = " intify (w) " in zless_linear_lemma)
apply auto
done

lemma zless_not_refl [iff]: "\<not> (z$<z)"
by (auto simp add: zless_def znegative_def int_of_def zdiff_def)

lemma neq_iff_zless: "\<lbrakk>x \<in> int; y \<in> int\<rbrakk> \<Longrightarrow> (x \<noteq> y) \<longleftrightarrow> (x $< y | y $< x)"
by (cut_tac z = x and w = y in zless_linear, auto)

lemma zless_imp_intify_neq: "w $< z \<Longrightarrow> intify(w) \<noteq> intify(z)"
apply auto
apply (subgoal_tac "\<not> (intify (w) $< intify (z))")
apply (erule_tac [2] ssubst)
apply (simp (no_asm_use))
apply auto
done

(*This lemma allows direct proofs of other <-properties*)
lemma zless_imp_succ_zadd_lemma:
    "\<lbrakk>w $< z; w \<in> int; z \<in> int\<rbrakk> \<Longrightarrow> (\<exists>n\<in>nat. z = w $+ $#(succ(n)))"
apply (simp add: zless_def znegative_def zdiff_def int_def)
apply (auto dest!: less_imp_succ_add simp add: zadd zminus int_of_def)
apply (rule_tac x = k in bexI)
apply (erule_tac i="succ (v)" for v in add_left_cancel, auto)
done

lemma zless_imp_succ_zadd:
     "w $< z \<Longrightarrow> (\<exists>n\<in>nat. w $+ $#(succ(n)) = intify(z))"
apply (subgoal_tac "intify (w) $< intify (z) ")
apply (drule_tac w = "intify (w) " in zless_imp_succ_zadd_lemma)
apply auto
done

lemma zless_succ_zadd_lemma:
    "w \<in> int \<Longrightarrow> w $< w $+ $# succ(n)"
apply (simp add: zless_def znegative_def zdiff_def int_def)
apply (auto simp add: zadd zminus int_of_def image_iff)
apply (rule_tac x = 0 in exI, auto)
done

lemma zless_succ_zadd: "w $< w $+ $# succ(n)"
by (cut_tac intify_in_int [THEN zless_succ_zadd_lemma], auto)

lemma zless_iff_succ_zadd:
     "w $< z \<longleftrightarrow> (\<exists>n\<in>nat. w $+ $#(succ(n)) = intify(z))"
apply (rule iffI)
apply (erule zless_imp_succ_zadd, auto)
apply (rename_tac "n")
apply (cut_tac w = w and n = n in zless_succ_zadd, auto)
done

lemma zless_int_of [simp]: "\<lbrakk>m\<in>nat; n\<in>nat\<rbrakk> \<Longrightarrow> ($#m $< $#n) \<longleftrightarrow> (m<n)"
apply (simp add: less_iff_succ_add zless_iff_succ_zadd int_of_add [symmetric])
apply (blast intro: sym)
done

lemma zless_trans_lemma:
    "\<lbrakk>x $< y; y $< z; x \<in> int; y \<in> int; z \<in> int\<rbrakk> \<Longrightarrow> x $< z"
apply (simp add: zless_def znegative_def zdiff_def int_def)
apply (auto simp add: zadd zminus image_iff)
apply (rename_tac x1 x2 y1 y2)
apply (rule_tac x = "x1#+x2" in exI)
apply (rule_tac x = "y1#+y2" in exI)
apply (auto simp add: add_lt_mono)
apply (rule sym)
apply hypsubst_thin
apply (erule add_left_cancel)+
apply auto
done

lemma zless_trans [trans]: "\<lbrakk>x $< y; y $< z\<rbrakk> \<Longrightarrow> x $< z"
apply (subgoal_tac "intify (x) $< intify (z) ")
apply (rule_tac [2] y = "intify (y) " in zless_trans_lemma)
apply auto
done

lemma zless_not_sym: "z $< w \<Longrightarrow> \<not> (w $< z)"
by (blast dest: zless_trans)

(* \<lbrakk>z $< w; \<not> P \<Longrightarrow> w $< z\<rbrakk> \<Longrightarrow> P *)
lemmas zless_asym = zless_not_sym [THEN swap]

lemma zless_imp_zle: "z $< w \<Longrightarrow> z $\<le> w"
by (simp add: zle_def)

lemma zle_linear: "z $\<le> w | w $\<le> z"
apply (simp add: zle_def)
apply (cut_tac zless_linear, blast)
done


subsection\<open>Less Than or Equals\<close>

lemma zle_refl: "z $\<le> z"
by (simp add: zle_def)

lemma zle_eq_refl: "x=y \<Longrightarrow> x $\<le> y"
by (simp add: zle_refl)

lemma zle_anti_sym_intify: "\<lbrakk>x $\<le> y; y $\<le> x\<rbrakk> \<Longrightarrow> intify(x) = intify(y)"
apply (simp add: zle_def, auto)
apply (blast dest: zless_trans)
done

lemma zle_anti_sym: "\<lbrakk>x $\<le> y; y $\<le> x; x \<in> int; y \<in> int\<rbrakk> \<Longrightarrow> x=y"
by (drule zle_anti_sym_intify, auto)

lemma zle_trans_lemma:
     "\<lbrakk>x \<in> int; y \<in> int; z \<in> int; x $\<le> y; y $\<le> z\<rbrakk> \<Longrightarrow> x $\<le> z"
apply (simp add: zle_def, auto)
apply (blast intro: zless_trans)
done

lemma zle_trans [trans]: "\<lbrakk>x $\<le> y; y $\<le> z\<rbrakk> \<Longrightarrow> x $\<le> z"
apply (subgoal_tac "intify (x) $\<le> intify (z) ")
apply (rule_tac [2] y = "intify (y) " in zle_trans_lemma)
apply auto
done

lemma zle_zless_trans [trans]: "\<lbrakk>i $\<le> j; j $< k\<rbrakk> \<Longrightarrow> i $< k"
apply (auto simp add: zle_def)
apply (blast intro: zless_trans)
apply (simp add: zless_def zdiff_def zadd_def)
done

lemma zless_zle_trans [trans]: "\<lbrakk>i $< j; j $\<le> k\<rbrakk> \<Longrightarrow> i $< k"
apply (auto simp add: zle_def)
apply (blast intro: zless_trans)
apply (simp add: zless_def zdiff_def zminus_def)
done

lemma not_zless_iff_zle: "\<not> (z $< w) \<longleftrightarrow> (w $\<le> z)"
apply (cut_tac z = z and w = w in zless_linear)
apply (auto dest: zless_trans simp add: zle_def)
apply (auto dest!: zless_imp_intify_neq)
done

lemma not_zle_iff_zless: "\<not> (z $\<le> w) \<longleftrightarrow> (w $< z)"
by (simp add: not_zless_iff_zle [THEN iff_sym])


subsection\<open>More subtraction laws (for \<open>zcompare_rls\<close>)\<close>

lemma zdiff_zdiff_eq: "(x $- y) $- z = x $- (y $+ z)"
by (simp add: zdiff_def zadd_ac)

lemma zdiff_zdiff_eq2: "x $- (y $- z) = (x $+ z) $- y"
by (simp add: zdiff_def zadd_ac)

lemma zdiff_zless_iff: "(x$-y $< z) \<longleftrightarrow> (x $< z $+ y)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zless_zdiff_iff: "(x $< z$-y) \<longleftrightarrow> (x $+ y $< z)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zdiff_eq_iff: "\<lbrakk>x \<in> int; z \<in> int\<rbrakk> \<Longrightarrow> (x$-y = z) \<longleftrightarrow> (x = z $+ y)"
by (auto simp add: zdiff_def zadd_assoc)

lemma eq_zdiff_iff: "\<lbrakk>x \<in> int; z \<in> int\<rbrakk> \<Longrightarrow> (x = z$-y) \<longleftrightarrow> (x $+ y = z)"
by (auto simp add: zdiff_def zadd_assoc)

lemma zdiff_zle_iff_lemma:
     "\<lbrakk>x \<in> int; z \<in> int\<rbrakk> \<Longrightarrow> (x$-y $\<le> z) \<longleftrightarrow> (x $\<le> z $+ y)"
by (auto simp add: zle_def zdiff_eq_iff zdiff_zless_iff)

lemma zdiff_zle_iff: "(x$-y $\<le> z) \<longleftrightarrow> (x $\<le> z $+ y)"
by (cut_tac zdiff_zle_iff_lemma [OF intify_in_int intify_in_int], simp)

lemma zle_zdiff_iff_lemma:
     "\<lbrakk>x \<in> int; z \<in> int\<rbrakk> \<Longrightarrow>(x $\<le> z$-y) \<longleftrightarrow> (x $+ y $\<le> z)"
apply (auto simp add: zle_def zdiff_eq_iff zless_zdiff_iff)
apply (auto simp add: zdiff_def zadd_assoc)
done

lemma zle_zdiff_iff: "(x $\<le> z$-y) \<longleftrightarrow> (x $+ y $\<le> z)"
by (cut_tac zle_zdiff_iff_lemma [ OF intify_in_int intify_in_int], simp)

text\<open>This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.
  Use with \<open>zadd_ac\<close>\<close>
lemmas zcompare_rls =
     zdiff_def [symmetric]
     zadd_zdiff_eq zdiff_zadd_eq zdiff_zdiff_eq zdiff_zdiff_eq2
     zdiff_zless_iff zless_zdiff_iff zdiff_zle_iff zle_zdiff_iff
     zdiff_eq_iff eq_zdiff_iff


subsection\<open>Monotonicity and Cancellation Results for Instantiation
     of the CancelNumerals Simprocs\<close>

lemma zadd_left_cancel:
     "\<lbrakk>w \<in> int; w': int\<rbrakk> \<Longrightarrow> (z $+ w' = z $+ w) \<longleftrightarrow> (w' = w)"
apply safe
apply (drule_tac t = "\<lambda>x. x $+ ($-z) " in subst_context)
apply (simp add: zadd_ac)
done

lemma zadd_left_cancel_intify [simp]:
     "(z $+ w' = z $+ w) \<longleftrightarrow> intify(w') = intify(w)"
apply (rule iff_trans)
apply (rule_tac [2] zadd_left_cancel, auto)
done

lemma zadd_right_cancel:
     "\<lbrakk>w \<in> int; w': int\<rbrakk> \<Longrightarrow> (w' $+ z = w $+ z) \<longleftrightarrow> (w' = w)"
apply safe
apply (drule_tac t = "\<lambda>x. x $+ ($-z) " in subst_context)
apply (simp add: zadd_ac)
done

lemma zadd_right_cancel_intify [simp]:
     "(w' $+ z = w $+ z) \<longleftrightarrow> intify(w') = intify(w)"
apply (rule iff_trans)
apply (rule_tac [2] zadd_right_cancel, auto)
done

lemma zadd_right_cancel_zless [simp]: "(w' $+ z $< w $+ z) \<longleftrightarrow> (w' $< w)"
by (simp add: zdiff_zless_iff [THEN iff_sym] zdiff_def zadd_assoc)

lemma zadd_left_cancel_zless [simp]: "(z $+ w' $< z $+ w) \<longleftrightarrow> (w' $< w)"
by (simp add: zadd_commute [of z] zadd_right_cancel_zless)

lemma zadd_right_cancel_zle [simp]: "(w' $+ z $\<le> w $+ z) \<longleftrightarrow> w' $\<le> w"
by (simp add: zle_def)

lemma zadd_left_cancel_zle [simp]: "(z $+ w' $\<le> z $+ w) \<longleftrightarrow>  w' $\<le> w"
by (simp add: zadd_commute [of z]  zadd_right_cancel_zle)


(*"v $\<le> w \<Longrightarrow> v$+z $\<le> w$+z"*)
lemmas zadd_zless_mono1 = zadd_right_cancel_zless [THEN iffD2]

(*"v $\<le> w \<Longrightarrow> z$+v $\<le> z$+w"*)
lemmas zadd_zless_mono2 = zadd_left_cancel_zless [THEN iffD2]

(*"v $\<le> w \<Longrightarrow> v$+z $\<le> w$+z"*)
lemmas zadd_zle_mono1 = zadd_right_cancel_zle [THEN iffD2]

(*"v $\<le> w \<Longrightarrow> z$+v $\<le> z$+w"*)
lemmas zadd_zle_mono2 = zadd_left_cancel_zle [THEN iffD2]

lemma zadd_zle_mono: "\<lbrakk>w' $\<le> w; z' $\<le> z\<rbrakk> \<Longrightarrow> w' $+ z' $\<le> w $+ z"
by (erule zadd_zle_mono1 [THEN zle_trans], simp)

lemma zadd_zless_mono: "\<lbrakk>w' $< w; z' $\<le> z\<rbrakk> \<Longrightarrow> w' $+ z' $< w $+ z"
by (erule zadd_zless_mono1 [THEN zless_zle_trans], simp)


subsection\<open>Comparison laws\<close>

lemma zminus_zless_zminus [simp]: "($- x $< $- y) \<longleftrightarrow> (y $< x)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zminus_zle_zminus [simp]: "($- x $\<le> $- y) \<longleftrightarrow> (y $\<le> x)"
by (simp add: not_zless_iff_zle [THEN iff_sym])

subsubsection\<open>More inequality lemmas\<close>

lemma equation_zminus: "\<lbrakk>x \<in> int;  y \<in> int\<rbrakk> \<Longrightarrow> (x = $- y) \<longleftrightarrow> (y = $- x)"
by auto

lemma zminus_equation: "\<lbrakk>x \<in> int;  y \<in> int\<rbrakk> \<Longrightarrow> ($- x = y) \<longleftrightarrow> ($- y = x)"
by auto

lemma equation_zminus_intify: "(intify(x) = $- y) \<longleftrightarrow> (intify(y) = $- x)"
apply (cut_tac x = "intify (x) " and y = "intify (y) " in equation_zminus)
apply auto
done

lemma zminus_equation_intify: "($- x = intify(y)) \<longleftrightarrow> ($- y = intify(x))"
apply (cut_tac x = "intify (x) " and y = "intify (y) " in zminus_equation)
apply auto
done


subsubsection\<open>The next several equations are permutative: watch out!\<close>

lemma zless_zminus: "(x $< $- y) \<longleftrightarrow> (y $< $- x)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zminus_zless: "($- x $< y) \<longleftrightarrow> ($- y $< x)"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zle_zminus: "(x $\<le> $- y) \<longleftrightarrow> (y $\<le> $- x)"
by (simp add: not_zless_iff_zle [THEN iff_sym] zminus_zless)

lemma zminus_zle: "($- x $\<le> y) \<longleftrightarrow> ($- y $\<le> x)"
by (simp add: not_zless_iff_zle [THEN iff_sym] zless_zminus)

end
