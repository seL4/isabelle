(*  Title:      Int.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
                Tobias Nipkow, Florian Haftmann, TU Muenchen
    Copyright   1994  University of Cambridge

*)

header {* The Integers as Equivalence Classes over Pairs of Natural Numbers *} 

theory Int
imports Equiv_Relations Nat Wellfounded
uses
  ("Tools/numeral.ML")
  ("Tools/numeral_syntax.ML")
  "~~/src/Provers/Arith/assoc_fold.ML"
  "~~/src/Provers/Arith/cancel_numerals.ML"
  "~~/src/Provers/Arith/combine_numerals.ML"
  ("Tools/int_arith.ML")
begin

subsection {* The equivalence relation underlying the integers *}

definition intrel :: "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  [code del]: "intrel = {((x, y), (u, v)) | x y u v. x + v = u +y }"

typedef (Integ)
  int = "UNIV//intrel"
  by (auto simp add: quotient_def)

instantiation int :: "{zero, one, plus, minus, uminus, times, ord, abs, sgn}"
begin

definition
  Zero_int_def [code del]: "0 = Abs_Integ (intrel `` {(0, 0)})"

definition
  One_int_def [code del]: "1 = Abs_Integ (intrel `` {(1, 0)})"

definition
  add_int_def [code del]: "z + w = Abs_Integ
    (\<Union>(x, y) \<in> Rep_Integ z. \<Union>(u, v) \<in> Rep_Integ w.
      intrel `` {(x + u, y + v)})"

definition
  minus_int_def [code del]:
    "- z = Abs_Integ (\<Union>(x, y) \<in> Rep_Integ z. intrel `` {(y, x)})"

definition
  diff_int_def [code del]:  "z - w = z + (-w \<Colon> int)"

definition
  mult_int_def [code del]: "z * w = Abs_Integ
    (\<Union>(x, y) \<in> Rep_Integ z. \<Union>(u,v ) \<in> Rep_Integ w.
      intrel `` {(x*u + y*v, x*v + y*u)})"

definition
  le_int_def [code del]:
   "z \<le> w \<longleftrightarrow> (\<exists>x y u v. x+v \<le> u+y \<and> (x, y) \<in> Rep_Integ z \<and> (u, v) \<in> Rep_Integ w)"

definition
  less_int_def [code del]: "(z\<Colon>int) < w \<longleftrightarrow> z \<le> w \<and> z \<noteq> w"

definition
  zabs_def: "\<bar>i\<Colon>int\<bar> = (if i < 0 then - i else i)"

definition
  zsgn_def: "sgn (i\<Colon>int) = (if i=0 then 0 else if 0<i then 1 else - 1)"

instance ..

end


subsection{*Construction of the Integers*}

lemma intrel_iff [simp]: "(((x,y),(u,v)) \<in> intrel) = (x+v = u+y)"
by (simp add: intrel_def)

lemma equiv_intrel: "equiv UNIV intrel"
by (simp add: intrel_def equiv_def refl_on_def sym_def trans_def)

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


subsection {* Arithmetic Operations *}

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
    by (cases i, cases j, cases k) (simp add: mult algebra_simps)
  show "i * j = j * i"
    by (cases i, cases j) (simp add: mult algebra_simps)
  show "1 * i = i"
    by (cases i) (simp add: One_int_def mult)
  show "(i + j) * k = i * k + j * k"
    by (cases i, cases j, cases k) (simp add: add mult algebra_simps)
  show "0 \<noteq> (1::int)"
    by (simp add: Zero_int_def One_int_def)
qed

lemma int_def: "of_nat m = Abs_Integ (intrel `` {(m, 0)})"
by (induct m, simp_all add: Zero_int_def One_int_def add)


subsection {* The @{text "\<le>"} Ordering *}

lemma le:
  "(Abs_Integ(intrel``{(x,y)}) \<le> Abs_Integ(intrel``{(u,v)})) = (x+v \<le> u+y)"
by (force simp add: le_int_def)

lemma less:
  "(Abs_Integ(intrel``{(x,y)}) < Abs_Integ(intrel``{(u,v)})) = (x+v < u+y)"
by (simp add: less_int_def le order_less_le)

instance int :: linorder
proof
  fix i j k :: int
  show antisym: "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"
    by (cases i, cases j) (simp add: le)
  show "(i < j) = (i \<le> j \<and> \<not> j \<le> i)"
    by (auto simp add: less_int_def dest: antisym) 
  show "i \<le> i"
    by (cases i) (simp add: le)
  show "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k"
    by (cases i, cases j, cases k) (simp add: le)
  show "i \<le> j \<or> j \<le> i"
    by (cases i, cases j) (simp add: le linorder_linear)
qed

instantiation int :: distrib_lattice
begin

definition
  "(inf \<Colon> int \<Rightarrow> int \<Rightarrow> int) = min"

definition
  "(sup \<Colon> int \<Rightarrow> int \<Rightarrow> int) = max"

instance
  by intro_classes
    (auto simp add: inf_int_def sup_int_def min_max.sup_inf_distrib1)

end

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

text{*The integers form an ordered integral domain*}
instance int :: ordered_idom
proof
  fix i j k :: int
  show "i < j \<Longrightarrow> 0 < k \<Longrightarrow> k * i < k * j"
    by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)"
    by (simp only: zabs_def)
  show "sgn (i\<Colon>int) = (if i=0 then 0 else if 0<i then 1 else - 1)"
    by (simp only: zsgn_def)
qed

instance int :: lordered_ring
proof  
  fix k :: int
  show "abs k = sup k (- k)"
    by (auto simp add: sup_int_def zabs_def max_def less_minus_self_iff [symmetric])
qed

lemma zless_imp_add1_zle: "w < z \<Longrightarrow> w + (1\<Colon>int) \<le> z"
apply (cases w, cases z) 
apply (simp add: less le add One_int_def)
done

lemma zless_iff_Suc_zadd:
  "(w \<Colon> int) < z \<longleftrightarrow> (\<exists>n. z = w + of_nat (Suc n))"
apply (cases z, cases w)
apply (auto simp add: less add int_def)
apply (rename_tac a b c d) 
apply (rule_tac x="a+d - Suc(c+b)" in exI) 
apply arith
done

lemmas int_distrib =
  left_distrib [of "z1::int" "z2" "w", standard]
  right_distrib [of "w::int" "z1" "z2", standard]
  left_diff_distrib [of "z1::int" "z2" "w", standard]
  right_diff_distrib [of "w::int" "z1" "z2", standard]


subsection {* Embedding of the Integers into any @{text ring_1}: @{text of_int}*}

context ring_1
begin

definition
  of_int :: "int \<Rightarrow> 'a"
where
  [code del]: "of_int z = contents (\<Union>(i, j) \<in> Rep_Integ z. { of_nat i - of_nat j })"

lemma of_int: "of_int (Abs_Integ (intrel `` {(i,j)})) = of_nat i - of_nat j"
proof -
  have "(\<lambda>(i,j). { of_nat i - (of_nat j :: 'a) }) respects intrel"
    by (simp add: congruent_def algebra_simps of_nat_add [symmetric]
            del: of_nat_add) 
  thus ?thesis
    by (simp add: of_int_def UN_equiv_class [OF equiv_intrel])
qed

lemma of_int_0 [simp]: "of_int 0 = 0"
by (simp add: of_int Zero_int_def)

lemma of_int_1 [simp]: "of_int 1 = 1"
by (simp add: of_int One_int_def)

lemma of_int_add [simp]: "of_int (w+z) = of_int w + of_int z"
by (cases w, cases z, simp add: algebra_simps of_int add)

lemma of_int_minus [simp]: "of_int (-z) = - (of_int z)"
by (cases z, simp add: algebra_simps of_int minus)

lemma of_int_diff [simp]: "of_int (w - z) = of_int w - of_int z"
by (simp add: OrderedGroup.diff_minus diff_minus)

lemma of_int_mult [simp]: "of_int (w*z) = of_int w * of_int z"
apply (cases w, cases z)
apply (simp add: algebra_simps of_int mult of_nat_mult)
done

text{*Collapse nested embeddings*}
lemma of_int_of_nat_eq [simp]: "of_int (of_nat n) = of_nat n"
by (induct n) auto

end

context ordered_idom
begin

lemma of_int_le_iff [simp]:
  "of_int w \<le> of_int z \<longleftrightarrow> w \<le> z"
by (cases w, cases z, simp add: of_int le minus algebra_simps of_nat_add [symmetric] del: of_nat_add)

text{*Special cases where either operand is zero*}
lemmas of_int_0_le_iff [simp] = of_int_le_iff [of 0, simplified]
lemmas of_int_le_0_iff [simp] = of_int_le_iff [of _ 0, simplified]

lemma of_int_less_iff [simp]:
  "of_int w < of_int z \<longleftrightarrow> w < z"
  by (simp add: not_le [symmetric] linorder_not_le [symmetric])

text{*Special cases where either operand is zero*}
lemmas of_int_0_less_iff [simp] = of_int_less_iff [of 0, simplified]
lemmas of_int_less_0_iff [simp] = of_int_less_iff [of _ 0, simplified]

end

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
subclass (in ordered_idom) ring_char_0 by intro_locales

lemma of_int_eq_id [simp]: "of_int = id"
proof
  fix z show "of_int z = id z"
    by (cases z) (simp add: of_int add minus int_def diff_minus)
qed


subsection {* Magnitude of an Integer, as a Natural Number: @{text nat} *}

definition
  nat :: "int \<Rightarrow> nat"
where
  [code del]: "nat z = contents (\<Union>(x, y) \<in> Rep_Integ z. {x-y})"

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
apply (simp add: nat le int_def Zero_int_def linorder_not_le[symmetric], arith)
done

lemma nat_0_iff[simp]: "nat(i::int) = 0 \<longleftrightarrow> i\<le>0"
by(simp add: nat_eq_iff) arith

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

context ring_1
begin

lemma of_nat_nat: "0 \<le> z \<Longrightarrow> of_nat (nat z) = of_int z"
  by (cases z rule: eq_Abs_Integ)
   (simp add: nat le of_int Zero_int_def of_nat_diff)

end

text {* For termination proofs: *}
lemma measure_function_int[measure_function]: "is_measure (nat o abs)" ..


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
    by (simp only: algebra_simps)
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

lemma negD: "(x \<Colon> int) < 0 \<Longrightarrow> \<exists>n. x = - (of_nat (Suc n))"
apply (cases x)
apply (auto simp add: le minus Zero_int_def int_def order_less_le)
apply (rule_tac x="y - Suc x" in exI, arith)
done


subsection {* Cases and induction *}

text{*Now we replace the case analysis rule by a more conventional one:
whether an integer is negative or not.*}

theorem int_cases [cases type: int, case_names nonneg neg]:
  "[|!! n. (z \<Colon> int) = of_nat n ==> P;  !! n. z =  - (of_nat (Suc n)) ==> P |] ==> P"
apply (cases "z < 0", blast dest!: negD)
apply (simp add: linorder_not_less del: of_nat_Suc)
apply auto
apply (blast dest: nat_0_le [THEN sym])
done

theorem int_induct [induct type: int, case_names nonneg neg]:
     "[|!! n. P (of_nat n \<Colon> int);  !!n. P (- (of_nat (Suc n))) |] ==> P z"
  by (cases z rule: int_cases) auto

text{*Contributed by Brian Huffman*}
theorem int_diff_cases:
  obtains (diff) m n where "(z\<Colon>int) = of_nat m - of_nat n"
apply (cases z rule: eq_Abs_Integ)
apply (rule_tac m=x and n=y in diff)
apply (simp add: int_def diff_def minus add)
done


subsection {* Binary representation *}

text {*
  This formalization defines binary arithmetic in terms of the integers
  rather than using a datatype. This avoids multiple representations (leading
  zeroes, etc.)  See @{text "ZF/Tools/twos-compl.ML"}, function @{text
  int_of_binary}, for the numerical interpretation.

  The representation expects that @{text "(m mod 2)"} is 0 or 1,
  even if m is negative;
  For instance, @{text "-5 div 2 = -3"} and @{text "-5 mod 2 = 1"}; thus
  @{text "-5 = (-3)*2 + 1"}.
  
  This two's complement binary representation derives from the paper 
  "An Efficient Representation of Arithmetic for Term Rewriting" by
  Dave Cohen and Phil Watson, Rewriting Techniques and Applications,
  Springer LNCS 488 (240-251), 1991.
*}

subsubsection {* The constructors @{term Bit0}, @{term Bit1}, @{term Pls} and @{term Min} *}

definition
  Pls :: int where
  [code del]: "Pls = 0"

definition
  Min :: int where
  [code del]: "Min = - 1"

definition
  Bit0 :: "int \<Rightarrow> int" where
  [code del]: "Bit0 k = k + k"

definition
  Bit1 :: "int \<Rightarrow> int" where
  [code del]: "Bit1 k = 1 + k + k"

class number = -- {* for numeric types: nat, int, real, \dots *}
  fixes number_of :: "int \<Rightarrow> 'a"

use "Tools/numeral.ML"

syntax
  "_Numeral" :: "num_const \<Rightarrow> 'a"    ("_")

use "Tools/numeral_syntax.ML"
setup NumeralSyntax.setup

abbreviation
  "Numeral0 \<equiv> number_of Pls"

abbreviation
  "Numeral1 \<equiv> number_of (Bit1 Pls)"

lemma Let_number_of [simp]: "Let (number_of v) f = f (number_of v)"
  -- {* Unfold all @{text let}s involving constants *}
  unfolding Let_def ..

definition
  succ :: "int \<Rightarrow> int" where
  [code del]: "succ k = k + 1"

definition
  pred :: "int \<Rightarrow> int" where
  [code del]: "pred k = k - 1"

lemmas
  max_number_of [simp] = max_def
    [of "number_of u" "number_of v", standard, simp]
and
  min_number_of [simp] = min_def 
    [of "number_of u" "number_of v", standard, simp]
  -- {* unfolding @{text minx} and @{text max} on numerals *}

lemmas numeral_simps = 
  succ_def pred_def Pls_def Min_def Bit0_def Bit1_def

text {* Removal of leading zeroes *}

lemma Bit0_Pls [simp, code post]:
  "Bit0 Pls = Pls"
  unfolding numeral_simps by simp

lemma Bit1_Min [simp, code post]:
  "Bit1 Min = Min"
  unfolding numeral_simps by simp

lemmas normalize_bin_simps =
  Bit0_Pls Bit1_Min


subsubsection {* Successor and predecessor functions *}

text {* Successor *}

lemma succ_Pls:
  "succ Pls = Bit1 Pls"
  unfolding numeral_simps by simp

lemma succ_Min:
  "succ Min = Pls"
  unfolding numeral_simps by simp

lemma succ_Bit0:
  "succ (Bit0 k) = Bit1 k"
  unfolding numeral_simps by simp

lemma succ_Bit1:
  "succ (Bit1 k) = Bit0 (succ k)"
  unfolding numeral_simps by simp

lemmas succ_bin_simps [simp] =
  succ_Pls succ_Min succ_Bit0 succ_Bit1

text {* Predecessor *}

lemma pred_Pls:
  "pred Pls = Min"
  unfolding numeral_simps by simp

lemma pred_Min:
  "pred Min = Bit0 Min"
  unfolding numeral_simps by simp

lemma pred_Bit0:
  "pred (Bit0 k) = Bit1 (pred k)"
  unfolding numeral_simps by simp 

lemma pred_Bit1:
  "pred (Bit1 k) = Bit0 k"
  unfolding numeral_simps by simp

lemmas pred_bin_simps [simp] =
  pred_Pls pred_Min pred_Bit0 pred_Bit1


subsubsection {* Binary arithmetic *}

text {* Addition *}

lemma add_Pls:
  "Pls + k = k"
  unfolding numeral_simps by simp

lemma add_Min:
  "Min + k = pred k"
  unfolding numeral_simps by simp

lemma add_Bit0_Bit0:
  "(Bit0 k) + (Bit0 l) = Bit0 (k + l)"
  unfolding numeral_simps by simp

lemma add_Bit0_Bit1:
  "(Bit0 k) + (Bit1 l) = Bit1 (k + l)"
  unfolding numeral_simps by simp

lemma add_Bit1_Bit0:
  "(Bit1 k) + (Bit0 l) = Bit1 (k + l)"
  unfolding numeral_simps by simp

lemma add_Bit1_Bit1:
  "(Bit1 k) + (Bit1 l) = Bit0 (k + succ l)"
  unfolding numeral_simps by simp

lemma add_Pls_right:
  "k + Pls = k"
  unfolding numeral_simps by simp

lemma add_Min_right:
  "k + Min = pred k"
  unfolding numeral_simps by simp

lemmas add_bin_simps [simp] =
  add_Pls add_Min add_Pls_right add_Min_right
  add_Bit0_Bit0 add_Bit0_Bit1 add_Bit1_Bit0 add_Bit1_Bit1

text {* Negation *}

lemma minus_Pls:
  "- Pls = Pls"
  unfolding numeral_simps by simp

lemma minus_Min:
  "- Min = Bit1 Pls"
  unfolding numeral_simps by simp

lemma minus_Bit0:
  "- (Bit0 k) = Bit0 (- k)"
  unfolding numeral_simps by simp

lemma minus_Bit1:
  "- (Bit1 k) = Bit1 (pred (- k))"
  unfolding numeral_simps by simp

lemmas minus_bin_simps [simp] =
  minus_Pls minus_Min minus_Bit0 minus_Bit1

text {* Subtraction *}

lemma diff_bin_simps [simp]:
  "k - Pls = k"
  "k - Min = succ k"
  "Pls - (Bit0 l) = Bit0 (Pls - l)"
  "Pls - (Bit1 l) = Bit1 (Min - l)"
  "Min - (Bit0 l) = Bit1 (Min - l)"
  "Min - (Bit1 l) = Bit0 (Min - l)"
  "(Bit0 k) - (Bit0 l) = Bit0 (k - l)"
  "(Bit0 k) - (Bit1 l) = Bit1 (pred k - l)"
  "(Bit1 k) - (Bit0 l) = Bit1 (k - l)"
  "(Bit1 k) - (Bit1 l) = Bit0 (k - l)"
  unfolding numeral_simps by simp_all

text {* Multiplication *}

lemma mult_Pls:
  "Pls * w = Pls"
  unfolding numeral_simps by simp

lemma mult_Min:
  "Min * k = - k"
  unfolding numeral_simps by simp

lemma mult_Bit0:
  "(Bit0 k) * l = Bit0 (k * l)"
  unfolding numeral_simps int_distrib by simp

lemma mult_Bit1:
  "(Bit1 k) * l = (Bit0 (k * l)) + l"
  unfolding numeral_simps int_distrib by simp

lemmas mult_bin_simps [simp] =
  mult_Pls mult_Min mult_Bit0 mult_Bit1


subsubsection {* Binary comparisons *}

text {* Preliminaries *}

lemma even_less_0_iff:
  "a + a < 0 \<longleftrightarrow> a < (0::'a::ordered_idom)"
proof -
  have "a + a < 0 \<longleftrightarrow> (1+1)*a < 0" by (simp add: left_distrib)
  also have "(1+1)*a < 0 \<longleftrightarrow> a < 0"
    by (simp add: mult_less_0_iff zero_less_two 
                  order_less_not_sym [OF zero_less_two])
  finally show ?thesis .
qed

lemma le_imp_0_less: 
  assumes le: "0 \<le> z"
  shows "(0::int) < 1 + z"
proof -
  have "0 \<le> z" by fact
  also have "... < z + 1" by (rule less_add_one) 
  also have "... = 1 + z" by (simp add: add_ac)
  finally show "0 < 1 + z" .
qed

lemma odd_less_0_iff:
  "(1 + z + z < 0) = (z < (0::int))"
proof (cases z rule: int_cases)
  case (nonneg n)
  thus ?thesis by (simp add: linorder_not_less add_assoc add_increasing
                             le_imp_0_less [THEN order_less_imp_le])  
next
  case (neg n)
  thus ?thesis by (simp del: of_nat_Suc of_nat_add of_nat_1
    add: algebra_simps of_nat_1 [where 'a=int, symmetric] of_nat_add [symmetric])
qed

lemma bin_less_0_simps:
  "Pls < 0 \<longleftrightarrow> False"
  "Min < 0 \<longleftrightarrow> True"
  "Bit0 w < 0 \<longleftrightarrow> w < 0"
  "Bit1 w < 0 \<longleftrightarrow> w < 0"
  unfolding numeral_simps
  by (simp_all add: even_less_0_iff odd_less_0_iff)

lemma less_bin_lemma: "k < l \<longleftrightarrow> k - l < (0::int)"
  by simp

lemma le_iff_pred_less: "k \<le> l \<longleftrightarrow> pred k < l"
  unfolding numeral_simps
  proof
    have "k - 1 < k" by simp
    also assume "k \<le> l"
    finally show "k - 1 < l" .
  next
    assume "k - 1 < l"
    hence "(k - 1) + 1 \<le> l" by (rule zless_imp_add1_zle)
    thus "k \<le> l" by simp
  qed

lemma succ_pred: "succ (pred x) = x"
  unfolding numeral_simps by simp

text {* Less-than *}

lemma less_bin_simps [simp]:
  "Pls < Pls \<longleftrightarrow> False"
  "Pls < Min \<longleftrightarrow> False"
  "Pls < Bit0 k \<longleftrightarrow> Pls < k"
  "Pls < Bit1 k \<longleftrightarrow> Pls \<le> k"
  "Min < Pls \<longleftrightarrow> True"
  "Min < Min \<longleftrightarrow> False"
  "Min < Bit0 k \<longleftrightarrow> Min < k"
  "Min < Bit1 k \<longleftrightarrow> Min < k"
  "Bit0 k < Pls \<longleftrightarrow> k < Pls"
  "Bit0 k < Min \<longleftrightarrow> k \<le> Min"
  "Bit1 k < Pls \<longleftrightarrow> k < Pls"
  "Bit1 k < Min \<longleftrightarrow> k < Min"
  "Bit0 k < Bit0 l \<longleftrightarrow> k < l"
  "Bit0 k < Bit1 l \<longleftrightarrow> k \<le> l"
  "Bit1 k < Bit0 l \<longleftrightarrow> k < l"
  "Bit1 k < Bit1 l \<longleftrightarrow> k < l"
  unfolding le_iff_pred_less
    less_bin_lemma [of Pls]
    less_bin_lemma [of Min]
    less_bin_lemma [of "k"]
    less_bin_lemma [of "Bit0 k"]
    less_bin_lemma [of "Bit1 k"]
    less_bin_lemma [of "pred Pls"]
    less_bin_lemma [of "pred k"]
  by (simp_all add: bin_less_0_simps succ_pred)

text {* Less-than-or-equal *}

lemma le_bin_simps [simp]:
  "Pls \<le> Pls \<longleftrightarrow> True"
  "Pls \<le> Min \<longleftrightarrow> False"
  "Pls \<le> Bit0 k \<longleftrightarrow> Pls \<le> k"
  "Pls \<le> Bit1 k \<longleftrightarrow> Pls \<le> k"
  "Min \<le> Pls \<longleftrightarrow> True"
  "Min \<le> Min \<longleftrightarrow> True"
  "Min \<le> Bit0 k \<longleftrightarrow> Min < k"
  "Min \<le> Bit1 k \<longleftrightarrow> Min \<le> k"
  "Bit0 k \<le> Pls \<longleftrightarrow> k \<le> Pls"
  "Bit0 k \<le> Min \<longleftrightarrow> k \<le> Min"
  "Bit1 k \<le> Pls \<longleftrightarrow> k < Pls"
  "Bit1 k \<le> Min \<longleftrightarrow> k \<le> Min"
  "Bit0 k \<le> Bit0 l \<longleftrightarrow> k \<le> l"
  "Bit0 k \<le> Bit1 l \<longleftrightarrow> k \<le> l"
  "Bit1 k \<le> Bit0 l \<longleftrightarrow> k < l"
  "Bit1 k \<le> Bit1 l \<longleftrightarrow> k \<le> l"
  unfolding not_less [symmetric]
  by (simp_all add: not_le)

text {* Equality *}

lemma eq_bin_simps [simp]:
  "Pls = Pls \<longleftrightarrow> True"
  "Pls = Min \<longleftrightarrow> False"
  "Pls = Bit0 l \<longleftrightarrow> Pls = l"
  "Pls = Bit1 l \<longleftrightarrow> False"
  "Min = Pls \<longleftrightarrow> False"
  "Min = Min \<longleftrightarrow> True"
  "Min = Bit0 l \<longleftrightarrow> False"
  "Min = Bit1 l \<longleftrightarrow> Min = l"
  "Bit0 k = Pls \<longleftrightarrow> k = Pls"
  "Bit0 k = Min \<longleftrightarrow> False"
  "Bit1 k = Pls \<longleftrightarrow> False"
  "Bit1 k = Min \<longleftrightarrow> k = Min"
  "Bit0 k = Bit0 l \<longleftrightarrow> k = l"
  "Bit0 k = Bit1 l \<longleftrightarrow> False"
  "Bit1 k = Bit0 l \<longleftrightarrow> False"
  "Bit1 k = Bit1 l \<longleftrightarrow> k = l"
  unfolding order_eq_iff [where 'a=int]
  by (simp_all add: not_less)


subsection {* Converting Numerals to Rings: @{term number_of} *}

class number_ring = number + comm_ring_1 +
  assumes number_of_eq: "number_of k = of_int k"

text {* self-embedding of the integers *}

instantiation int :: number_ring
begin

definition int_number_of_def [code del]:
  "number_of w = (of_int w \<Colon> int)"

instance proof
qed (simp only: int_number_of_def)

end

lemma number_of_is_id:
  "number_of (k::int) = k"
  unfolding int_number_of_def by simp

lemma number_of_succ:
  "number_of (succ k) = (1 + number_of k ::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_pred:
  "number_of (pred w) = (- 1 + number_of w ::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_minus:
  "number_of (uminus w) = (- (number_of w)::'a::number_ring)"
  unfolding number_of_eq by (rule of_int_minus)

lemma number_of_add:
  "number_of (v + w) = (number_of v + number_of w::'a::number_ring)"
  unfolding number_of_eq by (rule of_int_add)

lemma number_of_diff:
  "number_of (v - w) = (number_of v - number_of w::'a::number_ring)"
  unfolding number_of_eq by (rule of_int_diff)

lemma number_of_mult:
  "number_of (v * w) = (number_of v * number_of w::'a::number_ring)"
  unfolding number_of_eq by (rule of_int_mult)

text {*
  The correctness of shifting.
  But it doesn't seem to give a measurable speed-up.
*}

lemma double_number_of_Bit0:
  "(1 + 1) * number_of w = (number_of (Bit0 w) ::'a::number_ring)"
  unfolding number_of_eq numeral_simps left_distrib by simp

text {*
  Converting numerals 0 and 1 to their abstract versions.
*}

lemma numeral_0_eq_0 [simp]:
  "Numeral0 = (0::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma numeral_1_eq_1 [simp]:
  "Numeral1 = (1::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

text {*
  Special-case simplification for small constants.
*}

text{*
  Unary minus for the abstract constant 1. Cannot be inserted
  as a simprule until later: it is @{text number_of_Min} re-oriented!
*}

lemma numeral_m1_eq_minus_1:
  "(-1::'a::number_ring) = - 1"
  unfolding number_of_eq numeral_simps by simp

lemma mult_minus1 [simp]:
  "-1 * z = -(z::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma mult_minus1_right [simp]:
  "z * -1 = -(z::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

(*Negation of a coefficient*)
lemma minus_number_of_mult [simp]:
   "- (number_of w) * z = number_of (uminus w) * (z::'a::number_ring)"
   unfolding number_of_eq by simp

text {* Subtraction *}

lemma diff_number_of_eq:
  "number_of v - number_of w =
    (number_of (v + uminus w)::'a::number_ring)"
  unfolding number_of_eq by simp

lemma number_of_Pls:
  "number_of Pls = (0::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_Min:
  "number_of Min = (- 1::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_Bit0:
  "number_of (Bit0 w) = (0::'a::number_ring) + (number_of w) + (number_of w)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_Bit1:
  "number_of (Bit1 w) = (1::'a::number_ring) + (number_of w) + (number_of w)"
  unfolding number_of_eq numeral_simps by simp


subsubsection {* Equality of Binary Numbers *}

text {* First version by Norbert Voelker *}

definition (*for simplifying equalities*)
  iszero :: "'a\<Colon>semiring_1 \<Rightarrow> bool"
where
  "iszero z \<longleftrightarrow> z = 0"

lemma iszero_0: "iszero 0"
by (simp add: iszero_def)

lemma not_iszero_1: "~ iszero 1"
by (simp add: iszero_def eq_commute)

lemma eq_number_of_eq:
  "((number_of x::'a::number_ring) = number_of y) =
   iszero (number_of (x + uminus y) :: 'a)"
unfolding iszero_def number_of_add number_of_minus
by (simp add: algebra_simps)

lemma iszero_number_of_Pls:
  "iszero ((number_of Pls)::'a::number_ring)"
unfolding iszero_def numeral_0_eq_0 ..

lemma nonzero_number_of_Min:
  "~ iszero ((number_of Min)::'a::number_ring)"
unfolding iszero_def numeral_m1_eq_minus_1 by simp


subsubsection {* Comparisons, for Ordered Rings *}

lemmas double_eq_0_iff = double_zero

lemma odd_nonzero:
  "1 + z + z \<noteq> (0::int)";
proof (cases z rule: int_cases)
  case (nonneg n)
  have le: "0 \<le> z+z" by (simp add: nonneg add_increasing) 
  thus ?thesis using  le_imp_0_less [OF le]
    by (auto simp add: add_assoc) 
next
  case (neg n)
  show ?thesis
  proof
    assume eq: "1 + z + z = 0"
    have "(0::int) < 1 + (of_nat n + of_nat n)"
      by (simp add: le_imp_0_less add_increasing) 
    also have "... = - (1 + z + z)" 
      by (simp add: neg add_assoc [symmetric]) 
    also have "... = 0" by (simp add: eq) 
    finally have "0<0" ..
    thus False by blast
  qed
qed

lemma iszero_number_of_Bit0:
  "iszero (number_of (Bit0 w)::'a) = 
   iszero (number_of w::'a::{ring_char_0,number_ring})"
proof -
  have "(of_int w + of_int w = (0::'a)) \<Longrightarrow> (w = 0)"
  proof -
    assume eq: "of_int w + of_int w = (0::'a)"
    then have "of_int (w + w) = (of_int 0 :: 'a)" by simp
    then have "w + w = 0" by (simp only: of_int_eq_iff)
    then show "w = 0" by (simp only: double_eq_0_iff)
  qed
  thus ?thesis
    by (auto simp add: iszero_def number_of_eq numeral_simps)
qed

lemma iszero_number_of_Bit1:
  "~ iszero (number_of (Bit1 w)::'a::{ring_char_0,number_ring})"
proof -
  have "1 + of_int w + of_int w \<noteq> (0::'a)"
  proof
    assume eq: "1 + of_int w + of_int w = (0::'a)"
    hence "of_int (1 + w + w) = (of_int 0 :: 'a)" by simp 
    hence "1 + w + w = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
  thus ?thesis
    by (auto simp add: iszero_def number_of_eq numeral_simps)
qed

lemmas iszero_simps =
  iszero_0 not_iszero_1
  iszero_number_of_Pls nonzero_number_of_Min
  iszero_number_of_Bit0 iszero_number_of_Bit1
(* iszero_number_of_Pls would never normally be used
   because its lhs simplifies to "iszero 0" *)

subsubsection {* The Less-Than Relation *}

lemma double_less_0_iff:
  "(a + a < 0) = (a < (0::'a::ordered_idom))"
proof -
  have "(a + a < 0) = ((1+1)*a < 0)" by (simp add: left_distrib)
  also have "... = (a < 0)"
    by (simp add: mult_less_0_iff zero_less_two 
                  order_less_not_sym [OF zero_less_two]) 
  finally show ?thesis .
qed

lemma odd_less_0:
  "(1 + z + z < 0) = (z < (0::int))";
proof (cases z rule: int_cases)
  case (nonneg n)
  thus ?thesis by (simp add: linorder_not_less add_assoc add_increasing
                             le_imp_0_less [THEN order_less_imp_le])  
next
  case (neg n)
  thus ?thesis by (simp del: of_nat_Suc of_nat_add of_nat_1
    add: algebra_simps of_nat_1 [where 'a=int, symmetric] of_nat_add [symmetric])
qed

text {* Less-Than or Equals *}

text {* Reduces @{term "a\<le>b"} to @{term "~ (b<a)"} for ALL numerals. *}

lemmas le_number_of_eq_not_less =
  linorder_not_less [of "number_of w" "number_of v", symmetric, 
  standard]


text {* Absolute value (@{term abs}) *}

lemma abs_number_of:
  "abs(number_of x::'a::{ordered_idom,number_ring}) =
   (if number_of x < (0::'a) then -number_of x else number_of x)"
  by (simp add: abs_if)


text {* Re-orientation of the equation nnn=x *}

lemma number_of_reorient:
  "(number_of w = x) = (x = number_of w)"
  by auto


subsubsection {* Simplification of arithmetic operations on integer constants. *}

lemmas arith_extra_simps [standard, simp] =
  number_of_add [symmetric]
  number_of_minus [symmetric]
  numeral_m1_eq_minus_1 [symmetric]
  number_of_mult [symmetric]
  diff_number_of_eq abs_number_of 

text {*
  For making a minimal simpset, one must include these default simprules.
  Also include @{text simp_thms}.
*}

lemmas arith_simps = 
  normalize_bin_simps pred_bin_simps succ_bin_simps
  add_bin_simps minus_bin_simps mult_bin_simps
  abs_zero abs_one arith_extra_simps

text {* Simplification of relational operations *}

lemma less_number_of [simp]:
  "(number_of x::'a::{ordered_idom,number_ring}) < number_of y \<longleftrightarrow> x < y"
  unfolding number_of_eq by (rule of_int_less_iff)

lemma le_number_of [simp]:
  "(number_of x::'a::{ordered_idom,number_ring}) \<le> number_of y \<longleftrightarrow> x \<le> y"
  unfolding number_of_eq by (rule of_int_le_iff)

lemma eq_number_of [simp]:
  "(number_of x::'a::{ring_char_0,number_ring}) = number_of y \<longleftrightarrow> x = y"
  unfolding number_of_eq by (rule of_int_eq_iff)

lemmas rel_simps [simp] = 
  less_number_of less_bin_simps
  le_number_of le_bin_simps
  eq_number_of_eq eq_bin_simps
  iszero_simps


subsubsection {* Simplification of arithmetic when nested to the right. *}

lemma add_number_of_left [simp]:
  "number_of v + (number_of w + z) =
   (number_of(v + w) + z::'a::number_ring)"
  by (simp add: add_assoc [symmetric])

lemma mult_number_of_left [simp]:
  "number_of v * (number_of w * z) =
   (number_of(v * w) * z::'a::number_ring)"
  by (simp add: mult_assoc [symmetric])

lemma add_number_of_diff1:
  "number_of v + (number_of w - c) = 
  number_of(v + w) - (c::'a::number_ring)"
  by (simp add: diff_minus add_number_of_left)

lemma add_number_of_diff2 [simp]:
  "number_of v + (c - number_of w) =
   number_of (v + uminus w) + (c::'a::number_ring)"
by (simp add: algebra_simps diff_number_of_eq [symmetric])




subsection {* The Set of Integers *}

context ring_1
begin

definition Ints  :: "'a set" where
  [code del]: "Ints = range of_int"

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

text {* The premise involving @{term Ints} prevents @{term "a = 1/2"}. *}

lemma Ints_double_eq_0_iff:
  assumes in_Ints: "a \<in> Ints"
  shows "(a + a = 0) = (a = (0::'a::ring_char_0))"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume "a = 0"
    thus "a + a = 0" by simp
  next
    assume eq: "a + a = 0"
    hence "of_int (z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "z + z = 0" by (simp only: of_int_eq_iff)
    hence "z = 0" by (simp only: double_eq_0_iff)
    thus "a = 0" by (simp add: a)
  qed
qed

lemma Ints_odd_nonzero:
  assumes in_Ints: "a \<in> Ints"
  shows "1 + a + a \<noteq> (0::'a::ring_char_0)"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume eq: "1 + a + a = 0"
    hence "of_int (1 + z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "1 + z + z = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
qed 

lemma Ints_number_of:
  "(number_of w :: 'a::number_ring) \<in> Ints"
  unfolding number_of_eq Ints_def by simp

lemma Ints_odd_less_0: 
  assumes in_Ints: "a \<in> Ints"
  shows "(1 + a + a < 0) = (a < (0::'a::ordered_idom))";
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  hence "((1::'a) + a + a < 0) = (of_int (1 + z + z) < (of_int 0 :: 'a))"
    by (simp add: a)
  also have "... = (z < 0)" by (simp only: of_int_less_iff odd_less_0)
  also have "... = (a < 0)" by (simp add: a)
  finally show ?thesis .
qed


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


subsection{*Inequality Reasoning for the Arithmetic Simproc*}

lemma add_numeral_0: "Numeral0 + a = (a::'a::number_ring)"
by simp 

lemma add_numeral_0_right: "a + Numeral0 = (a::'a::number_ring)"
by simp

lemma mult_numeral_1: "Numeral1 * a = (a::'a::number_ring)"
by simp 

lemma mult_numeral_1_right: "a * Numeral1 = (a::'a::number_ring)"
by simp

lemma divide_numeral_1: "a / Numeral1 = (a::'a::{number_ring,field})"
by simp

lemma inverse_numeral_1:
  "inverse Numeral1 = (Numeral1::'a::{number_ring,field})"
by simp

text{*Theorem lists for the cancellation simprocs. The use of binary numerals
for 0 and 1 reduces the number of special cases.*}

lemmas add_0s = add_numeral_0 add_numeral_0_right
lemmas mult_1s = mult_numeral_1 mult_numeral_1_right 
                 mult_minus1 mult_minus1_right


subsection{*Special Arithmetic Rules for Abstract 0 and 1*}

text{*Arithmetic computations are defined for binary literals, which leaves 0
and 1 as special cases. Addition already has rules for 0, but not 1.
Multiplication and unary minus already have rules for both 0 and 1.*}


lemma binop_eq: "[|f x y = g x y; x = x'; y = y'|] ==> f x' y' = g x' y'"
by simp


lemmas add_number_of_eq = number_of_add [symmetric]

text{*Allow 1 on either or both sides*}
lemma one_add_one_is_two: "1 + 1 = (2::'a::number_ring)"
by (simp del: numeral_1_eq_1 add: numeral_1_eq_1 [symmetric] add_number_of_eq)

lemmas add_special =
    one_add_one_is_two
    binop_eq [of "op +", OF add_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op +", OF add_number_of_eq refl numeral_1_eq_1, standard]

text{*Allow 1 on either or both sides (1-1 already simplifies to 0)*}
lemmas diff_special =
    binop_eq [of "op -", OF diff_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op -", OF diff_number_of_eq refl numeral_1_eq_1, standard]

text{*Allow 0 or 1 on either side with a binary numeral on the other*}
lemmas eq_special =
    binop_eq [of "op =", OF eq_number_of_eq numeral_0_eq_0 refl, standard]
    binop_eq [of "op =", OF eq_number_of_eq numeral_1_eq_1 refl, standard]
    binop_eq [of "op =", OF eq_number_of_eq refl numeral_0_eq_0, standard]
    binop_eq [of "op =", OF eq_number_of_eq refl numeral_1_eq_1, standard]

text{*Allow 0 or 1 on either side with a binary numeral on the other*}
lemmas less_special =
  binop_eq [of "op <", OF less_number_of numeral_0_eq_0 refl, standard]
  binop_eq [of "op <", OF less_number_of numeral_1_eq_1 refl, standard]
  binop_eq [of "op <", OF less_number_of refl numeral_0_eq_0, standard]
  binop_eq [of "op <", OF less_number_of refl numeral_1_eq_1, standard]

text{*Allow 0 or 1 on either side with a binary numeral on the other*}
lemmas le_special =
    binop_eq [of "op \<le>", OF le_number_of numeral_0_eq_0 refl, standard]
    binop_eq [of "op \<le>", OF le_number_of numeral_1_eq_1 refl, standard]
    binop_eq [of "op \<le>", OF le_number_of refl numeral_0_eq_0, standard]
    binop_eq [of "op \<le>", OF le_number_of refl numeral_1_eq_1, standard]

lemmas arith_special[simp] = 
       add_special diff_special eq_special less_special le_special


lemma min_max_01: "min (0::int) 1 = 0 & min (1::int) 0 = 0 &
                   max (0::int) 1 = 1 & max (1::int) 0 = 1"
by(simp add:min_def max_def)

lemmas min_max_special[simp] =
 min_max_01
 max_def[of "0::int" "number_of v", standard, simp]
 min_def[of "0::int" "number_of v", standard, simp]
 max_def[of "number_of u" "0::int", standard, simp]
 min_def[of "number_of u" "0::int", standard, simp]
 max_def[of "1::int" "number_of v", standard, simp]
 min_def[of "1::int" "number_of v", standard, simp]
 max_def[of "number_of u" "1::int", standard, simp]
 min_def[of "number_of u" "1::int", standard, simp]

text {* Legacy theorems *}

lemmas zle_int = of_nat_le_iff [where 'a=int]
lemmas int_int_eq = of_nat_eq_iff [where 'a=int]

subsection {* Setting up simplification procedures *}

lemmas int_arith_rules =
  neg_le_iff_le numeral_0_eq_0 numeral_1_eq_1
  minus_zero diff_minus left_minus right_minus
  mult_zero_left mult_zero_right mult_Bit1 mult_1_right
  mult_minus_left mult_minus_right
  minus_add_distrib minus_minus mult_assoc
  of_nat_0 of_nat_1 of_nat_Suc of_nat_add of_nat_mult
  of_int_0 of_int_1 of_int_add of_int_mult

use "Tools/int_arith.ML"
declaration {* K Int_Arith.setup *}


subsection{*Lemmas About Small Numerals*}

lemma of_int_m1 [simp]: "of_int -1 = (-1 :: 'a :: number_ring)"
proof -
  have "(of_int -1 :: 'a) = of_int (- 1)" by simp
  also have "... = - of_int 1" by (simp only: of_int_minus)
  also have "... = -1" by simp
  finally show ?thesis .
qed

lemma abs_minus_one [simp]: "abs (-1) = (1::'a::{ordered_idom,number_ring})"
by (simp add: abs_if)

lemma abs_power_minus_one [simp]:
     "abs(-1 ^ n) = (1::'a::{ordered_idom,number_ring,recpower})"
by (simp add: power_abs)

lemma of_int_number_of_eq [simp]:
     "of_int (number_of v) = (number_of v :: 'a :: number_ring)"
by (simp add: number_of_eq) 

text{*Lemmas for specialist use, NOT as default simprules*}
lemma mult_2: "2 * z = (z+z::'a::number_ring)"
proof -
  have "2*z = (1 + 1)*z" by simp
  also have "... = z+z" by (simp add: left_distrib)
  finally show ?thesis .
qed

lemma mult_2_right: "z * 2 = (z+z::'a::number_ring)"
by (subst mult_commute, rule mult_2)


subsection{*More Inequality Reasoning*}

lemma zless_add1_eq: "(w < z + (1::int)) = (w<z | w=z)"
by arith

lemma add1_zle_eq: "(w + (1::int) \<le> z) = (w<z)"
by arith

lemma zle_diff1_eq [simp]: "(w \<le> z - (1::int)) = (w<z)"
by arith

lemma zle_add1_eq_le [simp]: "(w < z + (1::int)) = (w\<le>z)"
by arith

lemma int_one_le_iff_zero_less: "((1::int) \<le> z) = (0 < z)"
by arith


subsection{*The functions @{term nat} and @{term int}*}

text{*Simplify the terms @{term "int 0"}, @{term "int(Suc 0)"} and
  @{term "w + - z"}*}
declare Zero_int_def [symmetric, simp]
declare One_int_def [symmetric, simp]

lemmas diff_int_def_symmetric = diff_int_def [symmetric, simp]

lemma nat_0: "nat 0 = 0"
by (simp add: nat_eq_iff)

lemma nat_1: "nat 1 = Suc 0"
by (subst nat_eq_iff, simp)

lemma nat_2: "nat 2 = Suc (Suc 0)"
by (subst nat_eq_iff, simp)

lemma one_less_nat_eq [simp]: "(Suc 0 < nat z) = (1 < z)"
apply (insert zless_nat_conj [of 1 z])
apply (auto simp add: nat_1)
done

text{*This simplifies expressions of the form @{term "int n = z"} where
      z is an integer literal.*}
lemmas int_eq_iff_number_of [simp] = int_eq_iff [of _ "number_of v", standard]

lemma split_nat [arith_split]:
  "P(nat(i::int)) = ((\<forall>n. i = of_nat n \<longrightarrow> P n) & (i < 0 \<longrightarrow> P 0))"
  (is "?P = (?L & ?R)")
proof (cases "i < 0")
  case True thus ?thesis by auto
next
  case False
  have "?P = ?L"
  proof
    assume ?P thus ?L using False by clarsimp
  next
    assume ?L thus ?P using False by simp
  qed
  with False show ?thesis by simp
qed

context ring_1
begin

lemma of_int_of_nat [nitpick_const_simp]:
  "of_int k = (if k < 0 then - of_nat (nat (- k)) else of_nat (nat k))"
proof (cases "k < 0")
  case True then have "0 \<le> - k" by simp
  then have "of_nat (nat (- k)) = of_int (- k)" by (rule of_nat_nat)
  with True show ?thesis by simp
next
  case False then show ?thesis by (simp add: not_less of_nat_nat)
qed

end

lemma nat_mult_distrib:
  fixes z z' :: int
  assumes "0 \<le> z"
  shows "nat (z * z') = nat z * nat z'"
proof (cases "0 \<le> z'")
  case False with assms have "z * z' \<le> 0"
    by (simp add: not_le mult_le_0_iff)
  then have "nat (z * z') = 0" by simp
  moreover from False have "nat z' = 0" by simp
  ultimately show ?thesis by simp
next
  case True with assms have ge_0: "z * z' \<ge> 0" by (simp add: zero_le_mult_iff)
  show ?thesis
    by (rule injD [of "of_nat :: nat \<Rightarrow> int", OF inj_of_nat])
      (simp only: of_nat_mult of_nat_nat [OF True]
         of_nat_nat [OF assms] of_nat_nat [OF ge_0], simp)
qed

lemma nat_mult_distrib_neg: "z \<le> (0::int) ==> nat(z*z') = nat(-z) * nat(-z')"
apply (rule trans)
apply (rule_tac [2] nat_mult_distrib, auto)
done

lemma nat_abs_mult_distrib: "nat (abs (w * z)) = nat (abs w) * nat (abs z)"
apply (cases "z=0 | w=0")
apply (auto simp add: abs_if nat_mult_distrib [symmetric] 
                      nat_mult_distrib_neg [symmetric] mult_less_0_iff)
done


subsection "Induction principles for int"

text{*Well-founded segments of the integers*}

definition
  int_ge_less_than  ::  "int => (int * int) set"
where
  "int_ge_less_than d = {(z',z). d \<le> z' & z' < z}"

theorem wf_int_ge_less_than: "wf (int_ge_less_than d)"
proof -
  have "int_ge_less_than d \<subseteq> measure (%z. nat (z-d))"
    by (auto simp add: int_ge_less_than_def)
  thus ?thesis 
    by (rule wf_subset [OF wf_measure]) 
qed

text{*This variant looks odd, but is typical of the relations suggested
by RankFinder.*}

definition
  int_ge_less_than2 ::  "int => (int * int) set"
where
  "int_ge_less_than2 d = {(z',z). d \<le> z & z' < z}"

theorem wf_int_ge_less_than2: "wf (int_ge_less_than2 d)"
proof -
  have "int_ge_less_than2 d \<subseteq> measure (%z. nat (1+z-d))" 
    by (auto simp add: int_ge_less_than2_def)
  thus ?thesis 
    by (rule wf_subset [OF wf_measure]) 
qed

abbreviation
  int :: "nat \<Rightarrow> int"
where
  "int \<equiv> of_nat"

(* `set:int': dummy construction *)
theorem int_ge_induct [case_names base step, induct set: int]:
  fixes i :: int
  assumes ge: "k \<le> i" and
    base: "P k" and
    step: "\<And>i. k \<le> i \<Longrightarrow> P i \<Longrightarrow> P (i + 1)"
  shows "P i"
proof -
  { fix n have "\<And>i::int. n = nat(i-k) \<Longrightarrow> k \<le> i \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      then have "n = nat((i - 1) - k)" by arith
      moreover
      have ki1: "k \<le> i - 1" using Suc.prems by arith
      ultimately
      have "P(i - 1)" by(rule Suc.hyps)
      from step[OF ki1 this] show ?case by simp
    qed
  }
  with ge show ?thesis by fast
qed

(* `set:int': dummy construction *)
theorem int_gr_induct [case_names base step, induct set: int]:
  assumes gr: "k < (i::int)" and
        base: "P(k+1)" and
        step: "\<And>i. \<lbrakk>k < i; P i\<rbrakk> \<Longrightarrow> P(i+1)"
  shows "P i"
apply(rule int_ge_induct[of "k + 1"])
  using gr apply arith
 apply(rule base)
apply (rule step, simp+)
done

theorem int_le_induct[consumes 1,case_names base step]:
  assumes le: "i \<le> (k::int)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>i \<le> k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
proof -
  { fix n have "\<And>i::int. n = nat(k-i) \<Longrightarrow> i \<le> k \<Longrightarrow> P i"
    proof (induct n)
      case 0
      hence "i = k" by arith
      thus "P i" using base by simp
    next
      case (Suc n)
      hence "n = nat(k - (i+1))" by arith
      moreover
      have ki1: "i + 1 \<le> k" using Suc.prems by arith
      ultimately
      have "P(i+1)" by(rule Suc.hyps)
      from step[OF ki1 this] show ?case by simp
    qed
  }
  with le show ?thesis by fast
qed

theorem int_less_induct [consumes 1,case_names base step]:
  assumes less: "(i::int) < k" and
        base: "P(k - 1)" and
        step: "\<And>i. \<lbrakk>i < k; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
apply(rule int_le_induct[of _ "k - 1"])
  using less apply arith
 apply(rule base)
apply (rule step, simp+)
done

subsection{*Intermediate value theorems*}

lemma int_val_lemma:
     "(\<forall>i<n::nat. abs(f(i+1) - f i) \<le> 1) -->  
      f 0 \<le> k --> k \<le> f n --> (\<exists>i \<le> n. f i = (k::int))"
unfolding One_nat_def
apply (induct n, simp)
apply (intro strip)
apply (erule impE, simp)
apply (erule_tac x = n in allE, simp)
apply (case_tac "k = f (Suc n)")
apply force
apply (erule impE)
 apply (simp add: abs_if split add: split_if_asm)
apply (blast intro: le_SucI)
done

lemmas nat0_intermed_int_val = int_val_lemma [rule_format (no_asm)]

lemma nat_intermed_int_val:
     "[| \<forall>i. m \<le> i & i < n --> abs(f(i + 1::nat) - f i) \<le> 1; m < n;  
         f m \<le> k; k \<le> f n |] ==> ? i. m \<le> i & i \<le> n & f i = (k::int)"
apply (cut_tac n = "n-m" and f = "%i. f (i+m) " and k = k 
       in int_val_lemma)
unfolding One_nat_def
apply simp
apply (erule exE)
apply (rule_tac x = "i+m" in exI, arith)
done


subsection{*Products and 1, by T. M. Rasmussen*}

lemma zabs_less_one_iff [simp]: "(\<bar>z\<bar> < 1) = (z = (0::int))"
by arith

lemma abs_zmult_eq_1: "(\<bar>m * n\<bar> = 1) ==> \<bar>m\<bar> = (1::int)"
apply (cases "\<bar>n\<bar>=1") 
apply (simp add: abs_mult) 
apply (rule ccontr) 
apply (auto simp add: linorder_neq_iff abs_mult) 
apply (subgoal_tac "2 \<le> \<bar>m\<bar> & 2 \<le> \<bar>n\<bar>")
 prefer 2 apply arith 
apply (subgoal_tac "2*2 \<le> \<bar>m\<bar> * \<bar>n\<bar>", simp) 
apply (rule mult_mono, auto) 
done

lemma pos_zmult_eq_1_iff_lemma: "(m * n = 1) ==> m = (1::int) | m = -1"
by (insert abs_zmult_eq_1 [of m n], arith)

lemma pos_zmult_eq_1_iff: "0 < (m::int) ==> (m * n = 1) = (m = 1 & n = 1)"
apply (auto dest: pos_zmult_eq_1_iff_lemma) 
apply (simp add: mult_commute [of m]) 
apply (frule pos_zmult_eq_1_iff_lemma, auto) 
done

lemma zmult_eq_1_iff: "(m*n = (1::int)) = ((m = 1 & n = 1) | (m = -1 & n = -1))"
apply (rule iffI) 
 apply (frule pos_zmult_eq_1_iff_lemma)
 apply (simp add: mult_commute [of m]) 
 apply (frule pos_zmult_eq_1_iff_lemma, auto) 
done

(* Could be simplified but Presburger only becomes available too late *)
lemma infinite_UNIV_int: "~finite(UNIV::int set)"
proof
  assume "finite(UNIV::int set)"
  moreover have "~(EX i::int. 2*i = 1)"
    by (auto simp: pos_zmult_eq_1_iff)
  ultimately show False using finite_UNIV_inj_surj[of "%n::int. n+n"]
    by (simp add:inj_on_def surj_def) (blast intro:sym)
qed


subsection {* Integer Powers *} 

instantiation int :: recpower
begin

primrec power_int where
  "p ^ 0 = (1\<Colon>int)"
  | "p ^ (Suc n) = (p\<Colon>int) * (p ^ n)"

instance proof
  fix z :: int
  fix n :: nat
  show "z ^ 0 = 1" by simp
  show "z ^ Suc n = z * (z ^ n)" by simp
qed

declare power_int.simps [simp del]

end

lemma zpower_zadd_distrib: "x ^ (y + z) = ((x ^ y) * (x ^ z)::int)"
  by (rule Power.power_add)

lemma zpower_zpower: "(x ^ y) ^ z = (x ^ (y * z)::int)"
  by (rule Power.power_mult [symmetric])

lemma zero_less_zpower_abs_iff [simp]:
  "(0 < abs x ^ n) \<longleftrightarrow> (x \<noteq> (0::int) | n = 0)"
  by (induct n) (auto simp add: zero_less_mult_iff)

lemma zero_le_zpower_abs [simp]: "(0::int) \<le> abs x ^ n"
  by (induct n) (auto simp add: zero_le_mult_iff)

lemma of_int_power:
  "of_int (z ^ n) = (of_int z ^ n :: 'a::{recpower, ring_1})"
  by (induct n) simp_all

lemma int_power: "int (m^n) = (int m) ^ n"
  by (rule of_nat_power)

lemmas zpower_int = int_power [symmetric]


subsection {* Further theorems on numerals *}

subsubsection{*Special Simplification for Constants*}

text{*These distributive laws move literals inside sums and differences.*}

lemmas left_distrib_number_of [simp] =
  left_distrib [of _ _ "number_of v", standard]

lemmas right_distrib_number_of [simp] =
  right_distrib [of "number_of v", standard]

lemmas left_diff_distrib_number_of [simp] =
  left_diff_distrib [of _ _ "number_of v", standard]

lemmas right_diff_distrib_number_of [simp] =
  right_diff_distrib [of "number_of v", standard]

text{*These are actually for fields, like real: but where else to put them?*}

lemmas zero_less_divide_iff_number_of [simp, noatp] =
  zero_less_divide_iff [of "number_of w", standard]

lemmas divide_less_0_iff_number_of [simp, noatp] =
  divide_less_0_iff [of "number_of w", standard]

lemmas zero_le_divide_iff_number_of [simp, noatp] =
  zero_le_divide_iff [of "number_of w", standard]

lemmas divide_le_0_iff_number_of [simp, noatp] =
  divide_le_0_iff [of "number_of w", standard]


text {*Replaces @{text "inverse #nn"} by @{text "1/#nn"}.  It looks
  strange, but then other simprocs simplify the quotient.*}

lemmas inverse_eq_divide_number_of [simp] =
  inverse_eq_divide [of "number_of w", standard]

text {*These laws simplify inequalities, moving unary minus from a term
into the literal.*}

lemmas less_minus_iff_number_of [simp, noatp] =
  less_minus_iff [of "number_of v", standard]

lemmas le_minus_iff_number_of [simp, noatp] =
  le_minus_iff [of "number_of v", standard]

lemmas equation_minus_iff_number_of [simp, noatp] =
  equation_minus_iff [of "number_of v", standard]

lemmas minus_less_iff_number_of [simp, noatp] =
  minus_less_iff [of _ "number_of v", standard]

lemmas minus_le_iff_number_of [simp, noatp] =
  minus_le_iff [of _ "number_of v", standard]

lemmas minus_equation_iff_number_of [simp, noatp] =
  minus_equation_iff [of _ "number_of v", standard]


text{*To Simplify Inequalities Where One Side is the Constant 1*}

lemma less_minus_iff_1 [simp,noatp]:
  fixes b::"'b::{ordered_idom,number_ring}"
  shows "(1 < - b) = (b < -1)"
by auto

lemma le_minus_iff_1 [simp,noatp]:
  fixes b::"'b::{ordered_idom,number_ring}"
  shows "(1 \<le> - b) = (b \<le> -1)"
by auto

lemma equation_minus_iff_1 [simp,noatp]:
  fixes b::"'b::number_ring"
  shows "(1 = - b) = (b = -1)"
by (subst equation_minus_iff, auto)

lemma minus_less_iff_1 [simp,noatp]:
  fixes a::"'b::{ordered_idom,number_ring}"
  shows "(- a < 1) = (-1 < a)"
by auto

lemma minus_le_iff_1 [simp,noatp]:
  fixes a::"'b::{ordered_idom,number_ring}"
  shows "(- a \<le> 1) = (-1 \<le> a)"
by auto

lemma minus_equation_iff_1 [simp,noatp]:
  fixes a::"'b::number_ring"
  shows "(- a = 1) = (a = -1)"
by (subst minus_equation_iff, auto)


text {*Cancellation of constant factors in comparisons (@{text "<"} and @{text "\<le>"}) *}

lemmas mult_less_cancel_left_number_of [simp, noatp] =
  mult_less_cancel_left [of "number_of v", standard]

lemmas mult_less_cancel_right_number_of [simp, noatp] =
  mult_less_cancel_right [of _ "number_of v", standard]

lemmas mult_le_cancel_left_number_of [simp, noatp] =
  mult_le_cancel_left [of "number_of v", standard]

lemmas mult_le_cancel_right_number_of [simp, noatp] =
  mult_le_cancel_right [of _ "number_of v", standard]


text {*Multiplying out constant divisors in comparisons (@{text "<"}, @{text "\<le>"} and @{text "="}) *}

lemmas le_divide_eq_number_of1 [simp] = le_divide_eq [of _ _ "number_of w", standard]
lemmas divide_le_eq_number_of1 [simp] = divide_le_eq [of _ "number_of w", standard]
lemmas less_divide_eq_number_of1 [simp] = less_divide_eq [of _ _ "number_of w", standard]
lemmas divide_less_eq_number_of1 [simp] = divide_less_eq [of _ "number_of w", standard]
lemmas eq_divide_eq_number_of1 [simp] = eq_divide_eq [of _ _ "number_of w", standard]
lemmas divide_eq_eq_number_of1 [simp] = divide_eq_eq [of _ "number_of w", standard]


subsubsection{*Optional Simplification Rules Involving Constants*}

text{*Simplify quotients that are compared with a literal constant.*}

lemmas le_divide_eq_number_of = le_divide_eq [of "number_of w", standard]
lemmas divide_le_eq_number_of = divide_le_eq [of _ _ "number_of w", standard]
lemmas less_divide_eq_number_of = less_divide_eq [of "number_of w", standard]
lemmas divide_less_eq_number_of = divide_less_eq [of _ _ "number_of w", standard]
lemmas eq_divide_eq_number_of = eq_divide_eq [of "number_of w", standard]
lemmas divide_eq_eq_number_of = divide_eq_eq [of _ _ "number_of w", standard]


text{*Not good as automatic simprules because they cause case splits.*}
lemmas divide_const_simps =
  le_divide_eq_number_of divide_le_eq_number_of less_divide_eq_number_of
  divide_less_eq_number_of eq_divide_eq_number_of divide_eq_eq_number_of
  le_divide_eq_1 divide_le_eq_1 less_divide_eq_1 divide_less_eq_1

text{*Division By @{text "-1"}*}

lemma divide_minus1 [simp]:
     "x/-1 = -(x::'a::{field,division_by_zero,number_ring})"
by simp

lemma minus1_divide [simp]:
     "-1 / (x::'a::{field,division_by_zero,number_ring}) = - (1/x)"
by (simp add: divide_inverse inverse_minus_eq)

lemma half_gt_zero_iff:
     "(0 < r/2) = (0 < (r::'a::{ordered_field,division_by_zero,number_ring}))"
by auto

lemmas half_gt_zero [simp] = half_gt_zero_iff [THEN iffD2, standard]


subsection {* Configuration of the code generator *}

code_datatype Pls Min Bit0 Bit1 "number_of \<Colon> int \<Rightarrow> int"

lemmas pred_succ_numeral_code [code] =
  pred_bin_simps succ_bin_simps

lemmas plus_numeral_code [code] =
  add_bin_simps
  arith_extra_simps(1) [where 'a = int]

lemmas minus_numeral_code [code] =
  minus_bin_simps
  arith_extra_simps(2) [where 'a = int]
  arith_extra_simps(5) [where 'a = int]

lemmas times_numeral_code [code] =
  mult_bin_simps
  arith_extra_simps(4) [where 'a = int]

instantiation int :: eq
begin

definition [code del]: "eq_class.eq k l \<longleftrightarrow> k - l = (0\<Colon>int)"

instance by default (simp add: eq_int_def)

end

lemma eq_number_of_int_code [code]:
  "eq_class.eq (number_of k \<Colon> int) (number_of l) \<longleftrightarrow> eq_class.eq k l"
  unfolding eq_int_def number_of_is_id ..

lemma eq_int_code [code]:
  "eq_class.eq Int.Pls Int.Pls \<longleftrightarrow> True"
  "eq_class.eq Int.Pls Int.Min \<longleftrightarrow> False"
  "eq_class.eq Int.Pls (Int.Bit0 k2) \<longleftrightarrow> eq_class.eq Int.Pls k2"
  "eq_class.eq Int.Pls (Int.Bit1 k2) \<longleftrightarrow> False"
  "eq_class.eq Int.Min Int.Pls \<longleftrightarrow> False"
  "eq_class.eq Int.Min Int.Min \<longleftrightarrow> True"
  "eq_class.eq Int.Min (Int.Bit0 k2) \<longleftrightarrow> False"
  "eq_class.eq Int.Min (Int.Bit1 k2) \<longleftrightarrow> eq_class.eq Int.Min k2"
  "eq_class.eq (Int.Bit0 k1) Int.Pls \<longleftrightarrow> eq_class.eq k1 Int.Pls"
  "eq_class.eq (Int.Bit1 k1) Int.Pls \<longleftrightarrow> False"
  "eq_class.eq (Int.Bit0 k1) Int.Min \<longleftrightarrow> False"
  "eq_class.eq (Int.Bit1 k1) Int.Min \<longleftrightarrow> eq_class.eq k1 Int.Min"
  "eq_class.eq (Int.Bit0 k1) (Int.Bit0 k2) \<longleftrightarrow> eq_class.eq k1 k2"
  "eq_class.eq (Int.Bit0 k1) (Int.Bit1 k2) \<longleftrightarrow> False"
  "eq_class.eq (Int.Bit1 k1) (Int.Bit0 k2) \<longleftrightarrow> False"
  "eq_class.eq (Int.Bit1 k1) (Int.Bit1 k2) \<longleftrightarrow> eq_class.eq k1 k2"
  unfolding eq_equals by simp_all

lemma eq_int_refl [code nbe]:
  "eq_class.eq (k::int) k \<longleftrightarrow> True"
  by (rule HOL.eq_refl)

lemma less_eq_number_of_int_code [code]:
  "(number_of k \<Colon> int) \<le> number_of l \<longleftrightarrow> k \<le> l"
  unfolding number_of_is_id ..

lemma less_eq_int_code [code]:
  "Int.Pls \<le> Int.Pls \<longleftrightarrow> True"
  "Int.Pls \<le> Int.Min \<longleftrightarrow> False"
  "Int.Pls \<le> Int.Bit0 k \<longleftrightarrow> Int.Pls \<le> k"
  "Int.Pls \<le> Int.Bit1 k \<longleftrightarrow> Int.Pls \<le> k"
  "Int.Min \<le> Int.Pls \<longleftrightarrow> True"
  "Int.Min \<le> Int.Min \<longleftrightarrow> True"
  "Int.Min \<le> Int.Bit0 k \<longleftrightarrow> Int.Min < k"
  "Int.Min \<le> Int.Bit1 k \<longleftrightarrow> Int.Min \<le> k"
  "Int.Bit0 k \<le> Int.Pls \<longleftrightarrow> k \<le> Int.Pls"
  "Int.Bit1 k \<le> Int.Pls \<longleftrightarrow> k < Int.Pls"
  "Int.Bit0 k \<le> Int.Min \<longleftrightarrow> k \<le> Int.Min"
  "Int.Bit1 k \<le> Int.Min \<longleftrightarrow> k \<le> Int.Min"
  "Int.Bit0 k1 \<le> Int.Bit0 k2 \<longleftrightarrow> k1 \<le> k2"
  "Int.Bit0 k1 \<le> Int.Bit1 k2 \<longleftrightarrow> k1 \<le> k2"
  "Int.Bit1 k1 \<le> Int.Bit0 k2 \<longleftrightarrow> k1 < k2"
  "Int.Bit1 k1 \<le> Int.Bit1 k2 \<longleftrightarrow> k1 \<le> k2"
  by simp_all

lemma less_number_of_int_code [code]:
  "(number_of k \<Colon> int) < number_of l \<longleftrightarrow> k < l"
  unfolding number_of_is_id ..

lemma less_int_code [code]:
  "Int.Pls < Int.Pls \<longleftrightarrow> False"
  "Int.Pls < Int.Min \<longleftrightarrow> False"
  "Int.Pls < Int.Bit0 k \<longleftrightarrow> Int.Pls < k"
  "Int.Pls < Int.Bit1 k \<longleftrightarrow> Int.Pls \<le> k"
  "Int.Min < Int.Pls \<longleftrightarrow> True"
  "Int.Min < Int.Min \<longleftrightarrow> False"
  "Int.Min < Int.Bit0 k \<longleftrightarrow> Int.Min < k"
  "Int.Min < Int.Bit1 k \<longleftrightarrow> Int.Min < k"
  "Int.Bit0 k < Int.Pls \<longleftrightarrow> k < Int.Pls"
  "Int.Bit1 k < Int.Pls \<longleftrightarrow> k < Int.Pls"
  "Int.Bit0 k < Int.Min \<longleftrightarrow> k \<le> Int.Min"
  "Int.Bit1 k < Int.Min \<longleftrightarrow> k < Int.Min"
  "Int.Bit0 k1 < Int.Bit0 k2 \<longleftrightarrow> k1 < k2"
  "Int.Bit0 k1 < Int.Bit1 k2 \<longleftrightarrow> k1 \<le> k2"
  "Int.Bit1 k1 < Int.Bit0 k2 \<longleftrightarrow> k1 < k2"
  "Int.Bit1 k1 < Int.Bit1 k2 \<longleftrightarrow> k1 < k2"
  by simp_all

definition
  nat_aux :: "int \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_aux i n = nat i + n"

lemma [code]:
  "nat_aux i n = (if i \<le> 0 then n else nat_aux (i - 1) (Suc n))"  -- {* tail recursive *}
  by (auto simp add: nat_aux_def nat_eq_iff linorder_not_le order_less_imp_le
    dest: zless_imp_add1_zle)

lemma [code]: "nat i = nat_aux i 0"
  by (simp add: nat_aux_def)

hide (open) const nat_aux

lemma zero_is_num_zero [code, code inline, symmetric, code post]:
  "(0\<Colon>int) = Numeral0" 
  by simp

lemma one_is_num_one [code, code inline, symmetric, code post]:
  "(1\<Colon>int) = Numeral1" 
  by simp

code_modulename SML
  Int Integer

code_modulename OCaml
  Int Integer

code_modulename Haskell
  Int Integer

types_code
  "int" ("int")
attach (term_of) {*
val term_of_int = HOLogic.mk_number HOLogic.intT;
*}
attach (test) {*
fun gen_int i =
  let val j = one_of [~1, 1] * random_range 0 i
  in (j, fn () => term_of_int j) end;
*}

setup {*
let

fun strip_number_of (@{term "Int.number_of :: int => int"} $ t) = t
  | strip_number_of t = t;

fun numeral_codegen thy defs dep module b t gr =
  let val i = HOLogic.dest_numeral (strip_number_of t)
  in
    SOME (Codegen.str (string_of_int i),
      snd (Codegen.invoke_tycodegen thy defs dep module false HOLogic.intT gr))
  end handle TERM _ => NONE;

in

Codegen.add_codegen "numeral_codegen" numeral_codegen

end
*}

consts_code
  "number_of :: int \<Rightarrow> int"    ("(_)")
  "0 :: int"                   ("0")
  "1 :: int"                   ("1")
  "uminus :: int => int"       ("~")
  "op + :: int => int => int"  ("(_ +/ _)")
  "op * :: int => int => int"  ("(_ */ _)")
  "op \<le> :: int => int => bool" ("(_ <=/ _)")
  "op < :: int => int => bool" ("(_ </ _)")

quickcheck_params [default_type = int]

hide (open) const Pls Min Bit0 Bit1 succ pred


subsection {* Legacy theorems *}

lemmas zminus_zminus = minus_minus [of "z::int", standard]
lemmas zminus_0 = minus_zero [where 'a=int]
lemmas zminus_zadd_distrib = minus_add_distrib [of "z::int" "w", standard]
lemmas zadd_commute = add_commute [of "z::int" "w", standard]
lemmas zadd_assoc = add_assoc [of "z1::int" "z2" "z3", standard]
lemmas zadd_left_commute = add_left_commute [of "x::int" "y" "z", standard]
lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute
lemmas zmult_ac = OrderedGroup.mult_ac
lemmas zadd_0 = OrderedGroup.add_0_left [of "z::int", standard]
lemmas zadd_0_right = OrderedGroup.add_0_left [of "z::int", standard]
lemmas zadd_zminus_inverse2 = left_minus [of "z::int", standard]
lemmas zmult_zminus = mult_minus_left [of "z::int" "w", standard]
lemmas zmult_commute = mult_commute [of "z::int" "w", standard]
lemmas zmult_assoc = mult_assoc [of "z1::int" "z2" "z3", standard]
lemmas zadd_zmult_distrib = left_distrib [of "z1::int" "z2" "w", standard]
lemmas zadd_zmult_distrib2 = right_distrib [of "w::int" "z1" "z2", standard]
lemmas zdiff_zmult_distrib = left_diff_distrib [of "z1::int" "z2" "w", standard]
lemmas zdiff_zmult_distrib2 = right_diff_distrib [of "w::int" "z1" "z2", standard]

lemmas zmult_1 = mult_1_left [of "z::int", standard]
lemmas zmult_1_right = mult_1_right [of "z::int", standard]

lemmas zle_refl = order_refl [of "w::int", standard]
lemmas zle_trans = order_trans [where 'a=int and x="i" and y="j" and z="k", standard]
lemmas zle_anti_sym = order_antisym [of "z::int" "w", standard]
lemmas zle_linear = linorder_linear [of "z::int" "w", standard]
lemmas zless_linear = linorder_less_linear [where 'a = int]

lemmas zadd_left_mono = add_left_mono [of "i::int" "j" "k", standard]
lemmas zadd_strict_right_mono = add_strict_right_mono [of "i::int" "j" "k", standard]
lemmas zadd_zless_mono = add_less_le_mono [of "w'::int" "w" "z'" "z", standard]

lemmas int_0_less_1 = zero_less_one [where 'a=int]
lemmas int_0_neq_1 = zero_neq_one [where 'a=int]

lemmas inj_int = inj_of_nat [where 'a=int]
lemmas zadd_int = of_nat_add [where 'a=int, symmetric]
lemmas int_mult = of_nat_mult [where 'a=int]
lemmas zmult_int = of_nat_mult [where 'a=int, symmetric]
lemmas int_eq_0_conv = of_nat_eq_0_iff [where 'a=int and m="n", standard]
lemmas zless_int = of_nat_less_iff [where 'a=int]
lemmas int_less_0_conv = of_nat_less_0_iff [where 'a=int and m="k", standard]
lemmas zero_less_int_conv = of_nat_0_less_iff [where 'a=int]
lemmas zero_zle_int = of_nat_0_le_iff [where 'a=int]
lemmas int_le_0_conv = of_nat_le_0_iff [where 'a=int and m="n", standard]
lemmas int_0 = of_nat_0 [where 'a=int]
lemmas int_1 = of_nat_1 [where 'a=int]
lemmas int_Suc = of_nat_Suc [where 'a=int]
lemmas abs_int_eq = abs_of_nat [where 'a=int and n="m", standard]
lemmas of_int_int_eq = of_int_of_nat_eq [where 'a=int]
lemmas zdiff_int = of_nat_diff [where 'a=int, symmetric]
lemmas zless_le = less_int_def
lemmas int_eq_of_nat = TrueI

end
