(*  Title:      IntDef.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

*)

header{*The Integers as Equivalence Classes over Pairs of Natural Numbers*} 

theory IntDef
imports Equiv_Relations Nat
begin

text {* the equivalence relation underlying the integers *}

definition
  intrel :: "((nat \<times> nat) \<times> (nat \<times> nat)) set"
where
  "intrel = {((x, y), (u, v)) | x y u v. x + v = u +y }"

typedef (Integ)
  int = "UNIV//intrel"
  by (auto simp add: quotient_def)

instance int :: zero
  Zero_int_def: "0 \<equiv> Abs_Integ (intrel `` {(0, 0)})" ..

instance int :: one
  One_int_def: "1 \<equiv> Abs_Integ (intrel `` {(1, 0)})" ..

instance int :: plus
  add_int_def: "z + w \<equiv> Abs_Integ
    (\<Union>(x, y) \<in> Rep_Integ z. \<Union>(u, v) \<in> Rep_Integ w.
      intrel `` {(x + u, y + v)})" ..

instance int :: minus
  minus_int_def:
    "- z \<equiv> Abs_Integ (\<Union>(x, y) \<in> Rep_Integ z. intrel `` {(y, x)})"
  diff_int_def:  "z - w \<equiv> z + (-w)" ..

instance int :: times
  mult_int_def: "z * w \<equiv>  Abs_Integ
    (\<Union>(x, y) \<in> Rep_Integ z. \<Union>(u,v ) \<in> Rep_Integ w.
      intrel `` {(x*u + y*v, x*v + y*u)})" ..

instance int :: ord
  le_int_def:
   "z \<le> w \<equiv> \<exists>x y u v. x+v \<le> u+y \<and> (x, y) \<in> Rep_Integ z \<and> (u, v) \<in> Rep_Integ w"
  less_int_def: "z < w \<equiv> z \<le> w \<and> z \<noteq> w" ..

lemmas [code func del] = Zero_int_def One_int_def add_int_def
  minus_int_def mult_int_def le_int_def less_int_def


subsection{*Construction of the Integers*}

lemma intrel_iff [simp]: "(((x,y),(u,v)) \<in> intrel) = (x+v = u+y)"
by (simp add: intrel_def)

lemma equiv_intrel: "equiv UNIV intrel"
by (simp add: intrel_def equiv_def refl_def sym_def trans_def)

text{*Reduces equality of equivalence classes to the @{term intrel} relation:
  @{term "(intrel `` {x} = intrel `` {y}) = ((x,y) \<in> intrel)"} *}
lemmas equiv_intrel_iff [simp] = eq_equiv_class_iff [OF equiv_intrel UNIV_I UNIV_I]

text{*All equivalence classes belong to set of representatives*}
lemma [simp]: "intrel``{(x,y)} \<in> Integ"
by (auto simp add: Integ_def intrel_def quotient_def)

text{*Reduces equality on abstractions to equality on representatives:
  @{prop "\<lbrakk>x \<in> Integ; y \<in> Integ\<rbrakk> \<Longrightarrow> (Abs_Integ x = Abs_Integ y) = (x=y)"} *}
declare Abs_Integ_inject [simp,noatp]  Abs_Integ_inverse [simp,noatp]

text{*Case analysis on the representation of an integer as an equivalence
      class of pairs of naturals.*}
lemma eq_Abs_Integ [case_names Abs_Integ, cases type: int]:
     "(!!x y. z = Abs_Integ(intrel``{(x,y)}) ==> P) ==> P"
apply (rule Abs_Integ_cases [of z]) 
apply (auto simp add: Integ_def quotient_def) 
done


subsection{*Arithmetic Operations*}

lemma minus: "- Abs_Integ(intrel``{(x,y)}) = Abs_Integ(intrel `` {(y,x)})"
proof -
  have "(\<lambda>(x,y). intrel``{(y,x)}) respects intrel"
    by (simp add: congruent_def) 
  thus ?thesis
    by (simp add: minus_int_def UN_equiv_class [OF equiv_intrel])
qed

lemma add:
     "Abs_Integ (intrel``{(x,y)}) + Abs_Integ (intrel``{(u,v)}) =
      Abs_Integ (intrel``{(x+u, y+v)})"
proof -
  have "(\<lambda>z w. (\<lambda>(x,y). (\<lambda>(u,v). intrel `` {(x+u, y+v)}) w) z) 
        respects2 intrel"
    by (simp add: congruent2_def)
  thus ?thesis
    by (simp add: add_int_def UN_UN_split_split_eq
                  UN_equiv_class2 [OF equiv_intrel equiv_intrel])
qed

text{*Congruence property for multiplication*}
lemma mult_congruent2:
     "(%p1 p2. (%(x,y). (%(u,v). intrel``{(x*u + y*v, x*v + y*u)}) p2) p1)
      respects2 intrel"
apply (rule equiv_intrel [THEN congruent2_commuteI])
 apply (force simp add: mult_ac, clarify) 
apply (simp add: congruent_def mult_ac)  
apply (rename_tac u v w x y z)
apply (subgoal_tac "u*y + x*y = w*y + v*y  &  u*z + x*z = w*z + v*z")
apply (simp add: mult_ac)
apply (simp add: add_mult_distrib [symmetric])
done

lemma mult:
     "Abs_Integ((intrel``{(x,y)})) * Abs_Integ((intrel``{(u,v)})) =
      Abs_Integ(intrel `` {(x*u + y*v, x*v + y*u)})"
by (simp add: mult_int_def UN_UN_split_split_eq mult_congruent2
              UN_equiv_class2 [OF equiv_intrel equiv_intrel])

text{*The integers form a @{text comm_ring_1}*}
instance int :: comm_ring_1
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)"
    by (cases i, cases j, cases k) (simp add: add add_assoc)
  show "i + j = j + i" 
    by (cases i, cases j) (simp add: add_ac add)
  show "0 + i = i"
    by (cases i) (simp add: Zero_int_def add)
  show "- i + i = 0"
    by (cases i) (simp add: Zero_int_def minus add)
  show "i - j = i + - j"
    by (simp add: diff_int_def)
  show "(i * j) * k = i * (j * k)"
    by (cases i, cases j, cases k) (simp add: mult ring_simps)
  show "i * j = j * i"
    by (cases i, cases j) (simp add: mult ring_simps)
  show "1 * i = i"
    by (cases i) (simp add: One_int_def mult)
  show "(i + j) * k = i * k + j * k"
    by (cases i, cases j, cases k) (simp add: add mult ring_simps)
  show "0 \<noteq> (1::int)"
    by (simp add: Zero_int_def One_int_def)
qed

lemma int_def: "of_nat m = Abs_Integ (intrel `` {(m, 0)})"
by (induct m, simp_all add: Zero_int_def One_int_def add)


subsection{*The @{text "\<le>"} Ordering*}

lemma le:
  "(Abs_Integ(intrel``{(x,y)}) \<le> Abs_Integ(intrel``{(u,v)})) = (x+v \<le> u+y)"
by (force simp add: le_int_def)

lemma less:
  "(Abs_Integ(intrel``{(x,y)}) < Abs_Integ(intrel``{(u,v)})) = (x+v < u+y)"
by (simp add: less_int_def le order_less_le)

instance int :: linorder
proof
  fix i j k :: int
  show "(i < j) = (i \<le> j \<and> i \<noteq> j)"
    by (simp add: less_int_def)
  show "i \<le> i"
    by (cases i) (simp add: le)
  show "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k"
    by (cases i, cases j, cases k) (simp add: le)
  show "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"
    by (cases i, cases j) (simp add: le)
  show "i \<le> j \<or> j \<le> i"
    by (cases i, cases j) (simp add: le linorder_linear)
qed

instance int :: pordered_cancel_ab_semigroup_add
proof
  fix i j k :: int
  show "i \<le> j \<Longrightarrow> k + i \<le> k + j"
    by (cases i, cases j, cases k) (simp add: le add)
qed

text{*Strict Monotonicity of Multiplication*}

text{*strict, in 1st argument; proof is by induction on k>0*}
lemma zmult_zless_mono2_lemma:
     "(i::int)<j ==> 0<k ==> of_nat k * i < of_nat k * j"
apply (induct "k", simp)
apply (simp add: left_distrib)
apply (case_tac "k=0")
apply (simp_all add: add_strict_mono)
done

lemma zero_le_imp_eq_int: "(0::int) \<le> k ==> \<exists>n. k = of_nat n"
apply (cases k)
apply (auto simp add: le add int_def Zero_int_def)
apply (rule_tac x="x-y" in exI, simp)
done

lemma zero_less_imp_eq_int: "(0::int) < k ==> \<exists>n>0. k = of_nat n"
apply (cases k)
apply (simp add: less int_def Zero_int_def)
apply (rule_tac x="x-y" in exI, simp)
done

lemma zmult_zless_mono2: "[| i<j;  (0::int) < k |] ==> k*i < k*j"
apply (drule zero_less_imp_eq_int)
apply (auto simp add: zmult_zless_mono2_lemma)
done

instance int :: abs
  zabs_def: "\<bar>i\<Colon>int\<bar> \<equiv> if i < 0 then - i else i" ..
instance int :: sgn
  zsgn_def: "sgn(i\<Colon>int) \<equiv> (if i=0 then 0 else if 0<i then 1 else - 1)" ..

instance int :: distrib_lattice
  "inf \<equiv> min"
  "sup \<equiv> max"
  by intro_classes
    (auto simp add: inf_int_def sup_int_def min_max.sup_inf_distrib1)

text{*The integers form an ordered integral domain*}
instance int :: ordered_idom
proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn(i\<Colon>int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

lemma zless_imp_add1_zle: "w<z ==> w + (1::int) \<le> z"
apply (cases w, cases z) 
apply (simp add: less le add One_int_def)
done


subsection{*Magnitude of an Integer, as a Natural Number: @{term nat}*}

definition
  nat :: "int \<Rightarrow> nat"
where
  [code func del]: "nat z = contents (\<Union>(x, y) \<in> Rep_Integ z. {x-y})"

lemma nat: "nat (Abs_Integ (intrel``{(x,y)})) = x-y"
proof -
  have "(\<lambda>(x,y). {x-y}) respects intrel"
    by (simp add: congruent_def) arith
  thus ?thesis
    by (simp add: nat_def UN_equiv_class [OF equiv_intrel])
qed

lemma nat_int [simp]: "nat (of_nat n) = n"
by (simp add: nat int_def)

lemma nat_zero [simp]: "nat 0 = 0"
by (simp add: Zero_int_def nat)

lemma int_nat_eq [simp]: "of_nat (nat z) = (if 0 \<le> z then z else 0)"
by (cases z, simp add: nat le int_def Zero_int_def)

corollary nat_0_le: "0 \<le> z ==> of_nat (nat z) = z"
by simp

lemma nat_le_0 [simp]: "z \<le> 0 ==> nat z = 0"
by (cases z, simp add: nat le Zero_int_def)

lemma nat_le_eq_zle: "0 < w | 0 \<le> z ==> (nat w \<le> nat z) = (w\<le>z)"
apply (cases w, cases z) 
apply (simp add: nat le linorder_not_le [symmetric] Zero_int_def, arith)
done

text{*An alternative condition is @{term "0 \<le> w"} *}
corollary nat_mono_iff: "0 < z ==> (nat w < nat z) = (w < z)"
by (simp add: nat_le_eq_zle linorder_not_le [symmetric]) 

corollary nat_less_eq_zless: "0 \<le> w ==> (nat w < nat z) = (w<z)"
by (simp add: nat_le_eq_zle linorder_not_le [symmetric]) 

lemma zless_nat_conj [simp]: "(nat w < nat z) = (0 < z & w < z)"
apply (cases w, cases z) 
apply (simp add: nat le Zero_int_def linorder_not_le [symmetric], arith)
done

lemma nonneg_eq_int:
  fixes z :: int
  assumes "0 \<le> z" and "\<And>m. z = of_nat m \<Longrightarrow> P"
  shows P
  using assms by (blast dest: nat_0_le sym)

lemma nat_eq_iff: "(nat w = m) = (if 0 \<le> w then w = of_nat m else m=0)"
by (cases w, simp add: nat le int_def Zero_int_def, arith)

corollary nat_eq_iff2: "(m = nat w) = (if 0 \<le> w then w = of_nat m else m=0)"
by (simp only: eq_commute [of m] nat_eq_iff)

lemma nat_less_iff: "0 \<le> w ==> (nat w < m) = (w < of_nat m)"
apply (cases w)
apply (simp add: nat le int_def Zero_int_def linorder_not_le [symmetric], arith)
done

lemma int_eq_iff: "(of_nat m = z) = (m = nat z & 0 \<le> z)"
by (auto simp add: nat_eq_iff2)

lemma zero_less_nat_eq [simp]: "(0 < nat z) = (0 < z)"
by (insert zless_nat_conj [of 0], auto)

lemma nat_add_distrib:
     "[| (0::int) \<le> z;  0 \<le> z' |] ==> nat (z+z') = nat z + nat z'"
by (cases z, cases z', simp add: nat add le Zero_int_def)

lemma nat_diff_distrib:
     "[| (0::int) \<le> z';  z' \<le> z |] ==> nat (z-z') = nat z - nat z'"
by (cases z, cases z', 
    simp add: nat add minus diff_minus le Zero_int_def)

lemma nat_zminus_int [simp]: "nat (- (of_nat n)) = 0"
by (simp add: int_def minus nat Zero_int_def) 

lemma zless_nat_eq_int_zless: "(m < nat z) = (of_nat m < z)"
by (cases z, simp add: nat less int_def, arith)


subsection{*Lemmas about the Function @{term of_nat} and Orderings*}

lemma negative_zless_0: "- (of_nat (Suc n)) < (0 \<Colon> int)"
by (simp add: order_less_le del: of_nat_Suc)

lemma negative_zless [iff]: "- (of_nat (Suc n)) < (of_nat m \<Colon> int)"
by (rule negative_zless_0 [THEN order_less_le_trans], simp)

lemma negative_zle_0: "- of_nat n \<le> (0 \<Colon> int)"
by (simp add: minus_le_iff)

lemma negative_zle [iff]: "- of_nat n \<le> (of_nat m \<Colon> int)"
by (rule order_trans [OF negative_zle_0 of_nat_0_le_iff])

lemma not_zle_0_negative [simp]: "~ (0 \<le> - (of_nat (Suc n) \<Colon> int))"
by (subst le_minus_iff, simp del: of_nat_Suc)

lemma int_zle_neg: "((of_nat n \<Colon> int) \<le> - of_nat m) = (n = 0 & m = 0)"
by (simp add: int_def le minus Zero_int_def)

lemma not_int_zless_negative [simp]: "~ ((of_nat n \<Colon> int) < - of_nat m)"
by (simp add: linorder_not_less)

lemma negative_eq_positive [simp]: "((- of_nat n \<Colon> int) = of_nat m) = (n = 0 & m = 0)"
by (force simp add: order_eq_iff [of "- of_nat n"] int_zle_neg)

lemma zle_iff_zadd: "(w\<Colon>int) \<le> z \<longleftrightarrow> (\<exists>n. z = w + of_nat n)"
proof -
  have "(w \<le> z) = (0 \<le> z - w)"
    by (simp only: le_diff_eq add_0_left)
  also have "\<dots> = (\<exists>n. z - w = of_nat n)"
    by (auto elim: zero_le_imp_eq_int)
  also have "\<dots> = (\<exists>n. z = w + of_nat n)"
    by (simp only: group_simps)
  finally show ?thesis .
qed

lemma zadd_int_left: "of_nat m + (of_nat n + z) = of_nat (m + n) + (z\<Colon>int)"
by simp

lemma int_Suc0_eq_1: "of_nat (Suc 0) = (1\<Colon>int)"
by simp

text{*This version is proved for all ordered rings, not just integers!
      It is proved here because attribute @{text arith_split} is not available
      in theory @{text Ring_and_Field}.
      But is it really better than just rewriting with @{text abs_if}?*}
lemma abs_split [arith_split,noatp]:
     "P(abs(a::'a::ordered_idom)) = ((0 \<le> a --> P a) & (a < 0 --> P(-a)))"
by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)


subsection {* Constants @{term neg} and @{term iszero} *}

definition
  neg  :: "'a\<Colon>ordered_idom \<Rightarrow> bool"
where
  "neg Z \<longleftrightarrow> Z < 0"

definition (*for simplifying equalities*)
  iszero :: "'a\<Colon>semiring_1 \<Rightarrow> bool"
where
  "iszero z \<longleftrightarrow> z = 0"

lemma not_neg_int [simp]: "~ neg (of_nat n)"
by (simp add: neg_def)

lemma neg_zminus_int [simp]: "neg (- (of_nat (Suc n)))"
by (simp add: neg_def neg_less_0_iff_less del: of_nat_Suc)

lemmas neg_eq_less_0 = neg_def

lemma not_neg_eq_ge_0: "(~neg x) = (0 \<le> x)"
by (simp add: neg_def linorder_not_less)


text{*To simplify inequalities when Numeral1 can get simplified to 1*}

lemma not_neg_0: "~ neg 0"
by (simp add: One_int_def neg_def)

lemma not_neg_1: "~ neg 1"
by (simp add: neg_def linorder_not_less zero_le_one)

lemma iszero_0: "iszero 0"
by (simp add: iszero_def)

lemma not_iszero_1: "~ iszero 1"
by (simp add: iszero_def eq_commute)

lemma neg_nat: "neg z ==> nat z = 0"
by (simp add: neg_def order_less_imp_le) 

lemma not_neg_nat: "~ neg z ==> of_nat (nat z) = z"
by (simp add: linorder_not_less neg_def)


subsection{*Embedding of the Integers into any @{text ring_1}: @{term of_int}*}

context ring_1
begin

definition
  of_int :: "int \<Rightarrow> 'a"
where
  "of_int z = contents (\<Union>(i, j) \<in> Rep_Integ z. { of_nat i - of_nat j })"
lemmas [code func del] = of_int_def

lemma of_int: "of_int (Abs_Integ (intrel `` {(i,j)})) = of_nat i - of_nat j"
proof -
  have "(\<lambda>(i,j). { of_nat i - (of_nat j :: 'a) }) respects intrel"
    by (simp add: congruent_def compare_rls of_nat_add [symmetric]
            del: of_nat_add) 
  thus ?thesis
    by (simp add: of_int_def UN_equiv_class [OF equiv_intrel])
qed

lemma of_int_0 [simp]: "of_int 0 = 0"
by (simp add: of_int Zero_int_def)

lemma of_int_1 [simp]: "of_int 1 = 1"
by (simp add: of_int One_int_def)

lemma of_int_add [simp]: "of_int (w+z) = of_int w + of_int z"
by (cases w, cases z, simp add: compare_rls of_int add)

lemma of_int_minus [simp]: "of_int (-z) = - (of_int z)"
by (cases z, simp add: compare_rls of_int minus)

lemma of_int_mult [simp]: "of_int (w*z) = of_int w * of_int z"
apply (cases w, cases z)
apply (simp add: compare_rls of_int left_diff_distrib right_diff_distrib
                 mult add_ac of_nat_mult)
done

text{*Collapse nested embeddings*}
lemma of_int_of_nat_eq [simp]: "of_int (Nat.of_nat n) = of_nat n"
  by (induct n, auto)

end

lemma of_int_diff [simp]: "of_int (w-z) = of_int w - of_int z"
by (simp add: diff_minus)

lemma of_int_le_iff [simp]:
     "(of_int w \<le> (of_int z::'a::ordered_idom)) = (w \<le> z)"
apply (cases w)
apply (cases z)
apply (simp add: compare_rls of_int le diff_int_def add minus
                 of_nat_add [symmetric]   del: of_nat_add)
done

text{*Special cases where either operand is zero*}
lemmas of_int_0_le_iff [simp] = of_int_le_iff [of 0, simplified]
lemmas of_int_le_0_iff [simp] = of_int_le_iff [of _ 0, simplified]

lemma of_int_less_iff [simp]:
     "(of_int w < (of_int z::'a::ordered_idom)) = (w < z)"
by (simp add: linorder_not_le [symmetric])

text{*Special cases where either operand is zero*}
lemmas of_int_0_less_iff [simp] = of_int_less_iff [of 0, simplified]
lemmas of_int_less_0_iff [simp] = of_int_less_iff [of _ 0, simplified]

text{*Class for unital rings with characteristic zero.
 Includes non-ordered rings like the complex numbers.*}
class ring_char_0 = ring_1 + semiring_char_0
begin

lemma of_int_eq_iff [simp]:
   "of_int w = of_int z \<longleftrightarrow> w = z"
apply (cases w, cases z, simp add: of_int)
apply (simp only: diff_eq_eq diff_add_eq eq_diff_eq)
apply (simp only: of_nat_add [symmetric] of_nat_eq_iff)
done

text{*Special cases where either operand is zero*}
lemmas of_int_0_eq_iff [simp] = of_int_eq_iff [of 0, simplified]
lemmas of_int_eq_0_iff [simp] = of_int_eq_iff [of _ 0, simplified]

end

text{*Every @{text ordered_idom} has characteristic zero.*}
instance ordered_idom \<subseteq> ring_char_0 ..

lemma of_int_eq_id [simp]: "of_int = id"
proof
  fix z show "of_int z = id z"
    by (cases z) (simp add: of_int add minus int_def diff_minus)
qed

lemma of_nat_nat: "0 \<le> z \<Longrightarrow> of_nat (nat z) = of_int z"
by (cases z rule: eq_Abs_Integ)
   (simp add: nat le of_int Zero_int_def of_nat_diff)


subsection{*The Set of Integers*}

context ring_1
begin

definition
  Ints  :: "'a set"
where
  "Ints = range of_int"

end

notation (xsymbols)
  Ints  ("\<int>")

context ring_1
begin

lemma Ints_0 [simp]: "0 \<in> \<int>"
apply (simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_0 [symmetric])
done

lemma Ints_1 [simp]: "1 \<in> \<int>"
apply (simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_1 [symmetric])
done

lemma Ints_add [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a + b \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_add [symmetric])
done

lemma Ints_minus [simp]: "a \<in> \<int> \<Longrightarrow> -a \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_minus [symmetric])
done

lemma Ints_mult [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a * b \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_mult [symmetric])
done

lemma Ints_cases [cases set: Ints]:
  assumes "q \<in> \<int>"
  obtains (of_int) z where "q = of_int z"
  unfolding Ints_def
proof -
  from `q \<in> \<int>` have "q \<in> range of_int" unfolding Ints_def .
  then obtain z where "q = of_int z" ..
  then show thesis ..
qed

lemma Ints_induct [case_names of_int, induct set: Ints]:
  "q \<in> \<int> \<Longrightarrow> (\<And>z. P (of_int z)) \<Longrightarrow> P q"
  by (rule Ints_cases) auto

end

lemma Ints_diff [simp]: "a \<in> \<int> \<Longrightarrow> b \<in> \<int> \<Longrightarrow> a-b \<in> \<int>"
apply (auto simp add: Ints_def)
apply (rule range_eqI)
apply (rule of_int_diff [symmetric])
done


subsection {* @{term setsum} and @{term setprod} *}

text {*By Jeremy Avigad*}

lemma of_nat_setsum: "of_nat (setsum f A) = (\<Sum>x\<in>A. of_nat(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto)
  done

lemma of_int_setsum: "of_int (setsum f A) = (\<Sum>x\<in>A. of_int(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto)
  done

lemma of_nat_setprod: "of_nat (setprod f A) = (\<Prod>x\<in>A. of_nat(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto simp add: of_nat_mult)
  done

lemma of_int_setprod: "of_int (setprod f A) = (\<Prod>x\<in>A. of_int(f x))"
  apply (cases "finite A")
  apply (erule finite_induct, auto)
  done

lemma setprod_nonzero_nat:
    "finite A ==> (\<forall>x \<in> A. f x \<noteq> (0::nat)) ==> setprod f A \<noteq> 0"
  by (rule setprod_nonzero, auto)

lemma setprod_zero_eq_nat:
    "finite A ==> (setprod f A = (0::nat)) = (\<exists>x \<in> A. f x = 0)"
  by (rule setprod_zero_eq, auto)

lemma setprod_nonzero_int:
    "finite A ==> (\<forall>x \<in> A. f x \<noteq> (0::int)) ==> setprod f A \<noteq> 0"
  by (rule setprod_nonzero, auto)

lemma setprod_zero_eq_int:
    "finite A ==> (setprod f A = (0::int)) = (\<exists>x \<in> A. f x = 0)"
  by (rule setprod_zero_eq, auto)

lemmas int_setsum = of_nat_setsum [where 'a=int]
lemmas int_setprod = of_nat_setprod [where 'a=int]


subsection {* Further properties *}

text{*Now we replace the case analysis rule by a more conventional one:
whether an integer is negative or not.*}

lemma zless_iff_Suc_zadd:
  "(w \<Colon> int) < z \<longleftrightarrow> (\<exists>n. z = w + of_nat (Suc n))"
apply (cases z, cases w)
apply (auto simp add: less add int_def)
apply (rename_tac a b c d) 
apply (rule_tac x="a+d - Suc(c+b)" in exI) 
apply arith
done

lemma negD: "(x \<Colon> int) < 0 \<Longrightarrow> \<exists>n. x = - (of_nat (Suc n))"
apply (cases x)
apply (auto simp add: le minus Zero_int_def int_def order_less_le)
apply (rule_tac x="y - Suc x" in exI, arith)
done

theorem int_cases [cases type: int, case_names nonneg neg]:
  "[|!! n. (z \<Colon> int) = of_nat n ==> P;  !! n. z =  - (of_nat (Suc n)) ==> P |] ==> P"
apply (cases "z < 0", blast dest!: negD)
apply (simp add: linorder_not_less del: of_nat_Suc)
apply (blast dest: nat_0_le [THEN sym])
done

theorem int_induct [induct type: int, case_names nonneg neg]:
     "[|!! n. P (of_nat n \<Colon> int);  !!n. P (- (of_nat (Suc n))) |] ==> P z"
  by (cases z rule: int_cases) auto

text{*Contributed by Brian Huffman*}
theorem int_diff_cases [case_names diff]:
assumes prem: "!!m n. (z\<Colon>int) = of_nat m - of_nat n ==> P" shows "P"
apply (cases z rule: eq_Abs_Integ)
apply (rule_tac m=x and n=y in prem)
apply (simp add: int_def diff_def minus add)
done


subsection {* Legacy theorems *}

lemmas zminus_zminus = minus_minus [of "?z::int"]
lemmas zminus_0 = minus_zero [where 'a=int]
lemmas zminus_zadd_distrib = minus_add_distrib [of "?z::int" "?w"]
lemmas zadd_commute = add_commute [of "?z::int" "?w"]
lemmas zadd_assoc = add_assoc [of "?z1.0::int" "?z2.0" "?z3.0"]
lemmas zadd_left_commute = add_left_commute [of "?x::int" "?y" "?z"]
lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute
lemmas zmult_ac = OrderedGroup.mult_ac
lemmas zadd_0 = OrderedGroup.add_0_left [of "?z::int"]
lemmas zadd_0_right = OrderedGroup.add_0_left [of "?z::int"]
lemmas zadd_zminus_inverse2 = left_minus [of "?z::int"]
lemmas zmult_zminus = mult_minus_left [of "?z::int" "?w"]
lemmas zmult_commute = mult_commute [of "?z::int" "?w"]
lemmas zmult_assoc = mult_assoc [of "?z1.0::int" "?z2.0" "?z3.0"]
lemmas zadd_zmult_distrib = left_distrib [of "?z1.0::int" "?z2.0" "?w"]
lemmas zadd_zmult_distrib2 = right_distrib [of "?w::int" "?z1.0" "?z2.0"]
lemmas zdiff_zmult_distrib = left_diff_distrib [of "?z1.0::int" "?z2.0" "?w"]
lemmas zdiff_zmult_distrib2 = right_diff_distrib [of "?w::int" "?z1.0" "?z2.0"]

lemmas int_distrib =
  zadd_zmult_distrib zadd_zmult_distrib2
  zdiff_zmult_distrib zdiff_zmult_distrib2

lemmas zmult_1 = mult_1_left [of "?z::int"]
lemmas zmult_1_right = mult_1_right [of "?z::int"]

lemmas zle_refl = order_refl [of "?w::int"]
lemmas zle_trans = order_trans [where 'a=int and x="?i" and y="?j" and z="?k"]
lemmas zle_anti_sym = order_antisym [of "?z::int" "?w"]
lemmas zle_linear = linorder_linear [of "?z::int" "?w"]
lemmas zless_linear = linorder_less_linear [where 'a = int]

lemmas zadd_left_mono = add_left_mono [of "?i::int" "?j" "?k"]
lemmas zadd_strict_right_mono = add_strict_right_mono [of "?i::int" "?j" "?k"]
lemmas zadd_zless_mono = add_less_le_mono [of "?w'::int" "?w" "?z'" "?z"]

lemmas int_0_less_1 = zero_less_one [where 'a=int]
lemmas int_0_neq_1 = zero_neq_one [where 'a=int]

lemmas inj_int = inj_of_nat [where 'a=int]
lemmas int_int_eq = of_nat_eq_iff [where 'a=int]
lemmas zadd_int = of_nat_add [where 'a=int, symmetric]
lemmas int_mult = of_nat_mult [where 'a=int]
lemmas zmult_int = of_nat_mult [where 'a=int, symmetric]
lemmas int_eq_0_conv = of_nat_eq_0_iff [where 'a=int and m="?n"]
lemmas zless_int = of_nat_less_iff [where 'a=int]
lemmas int_less_0_conv = of_nat_less_0_iff [where 'a=int and m="?k"]
lemmas zero_less_int_conv = of_nat_0_less_iff [where 'a=int]
lemmas zle_int = of_nat_le_iff [where 'a=int]
lemmas zero_zle_int = of_nat_0_le_iff [where 'a=int]
lemmas int_le_0_conv = of_nat_le_0_iff [where 'a=int and m="?n"]
lemmas int_0 = of_nat_0 [where 'a=int]
lemmas int_1 = of_nat_1 [where 'a=int]
lemmas int_Suc = of_nat_Suc [where 'a=int]
lemmas abs_int_eq = abs_of_nat [where 'a=int and n="?m"]
lemmas of_int_int_eq = of_int_of_nat_eq [where 'a=int]
lemmas zdiff_int = of_nat_diff [where 'a=int, symmetric]
lemmas zless_le = less_int_def [THEN meta_eq_to_obj_eq]
lemmas int_eq_of_nat = TrueI

abbreviation
  int :: "nat \<Rightarrow> int"
where
  "int \<equiv> of_nat"

end
