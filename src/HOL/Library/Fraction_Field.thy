(*  Title:      Fraction_Field.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header{* A formalization of the fraction field of any integral domain 
         A generalization of Rational.thy from int to any integral domain *}

theory Fraction_Field
imports Main (* Equiv_Relations Plain *)
begin

subsection {* General fractions construction *}

subsubsection {* Construction of the type of fractions *}

definition fractrel :: "(('a::idom * 'a ) * ('a * 'a)) set" where
  "fractrel == {(x, y). snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x}"

lemma fractrel_iff [simp]:
  "(x, y) \<in> fractrel \<longleftrightarrow> snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x"
  by (simp add: fractrel_def)

lemma refl_fractrel: "refl_on {x. snd x \<noteq> 0} fractrel"
  by (auto simp add: refl_on_def fractrel_def)

lemma sym_fractrel: "sym fractrel"
  by (simp add: fractrel_def sym_def)

lemma trans_fractrel: "trans fractrel"
proof (rule transI, unfold split_paired_all)
  fix a b a' b' a'' b'' :: 'a
  assume A: "((a, b), (a', b')) \<in> fractrel"
  assume B: "((a', b'), (a'', b'')) \<in> fractrel"
  have "b' * (a * b'') = b'' * (a * b')" by (simp add: mult_ac)
  also from A have "a * b' = a' * b" by auto
  also have "b'' * (a' * b) = b * (a' * b'')" by (simp add: mult_ac)
  also from B have "a' * b'' = a'' * b'" by auto
  also have "b * (a'' * b') = b' * (a'' * b)" by (simp add: mult_ac)
  finally have "b' * (a * b'') = b' * (a'' * b)" .
  moreover from B have "b' \<noteq> 0" by auto
  ultimately have "a * b'' = a'' * b" by simp
  with A B show "((a, b), (a'', b'')) \<in> fractrel" by auto
qed
  
lemma equiv_fractrel: "equiv {x. snd x \<noteq> 0} fractrel"
  by (rule equiv.intro [OF refl_fractrel sym_fractrel trans_fractrel])

lemmas UN_fractrel = UN_equiv_class [OF equiv_fractrel]
lemmas UN_fractrel2 = UN_equiv_class2 [OF equiv_fractrel equiv_fractrel]

lemma equiv_fractrel_iff [iff]: 
  assumes "snd x \<noteq> 0" and "snd y \<noteq> 0"
  shows "fractrel `` {x} = fractrel `` {y} \<longleftrightarrow> (x, y) \<in> fractrel"
  by (rule eq_equiv_class_iff, rule equiv_fractrel) (auto simp add: assms)

typedef 'a fract = "{(x::'a\<times>'a). snd x \<noteq> (0::'a::idom)} // fractrel"
proof
  have "(0::'a, 1::'a) \<in> {x. snd x \<noteq> 0}" by simp
  then show "fractrel `` {(0::'a, 1)} \<in> {x. snd x \<noteq> 0} // fractrel" by (rule quotientI)
qed

lemma fractrel_in_fract [simp]: "snd x \<noteq> 0 \<Longrightarrow> fractrel `` {x} \<in> fract"
  by (simp add: fract_def quotientI)

declare Abs_fract_inject [simp] Abs_fract_inverse [simp]


subsubsection {* Representation and basic operations *}

definition
  Fract :: "'a::idom \<Rightarrow> 'a \<Rightarrow> 'a fract" where
  [code del]: "Fract a b = Abs_fract (fractrel `` {if b = 0 then (0, 1) else (a, b)})"

code_datatype Fract

lemma Fract_cases [case_names Fract, cases type: fract]:
  assumes "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> C"
  shows C
  using assms by (cases q) (clarsimp simp add: Fract_def fract_def quotient_def)

lemma Fract_induct [case_names Fract, induct type: fract]:
  assumes "\<And>a b. b \<noteq> 0 \<Longrightarrow> P (Fract a b)"
  shows "P q"
  using assms by (cases q) simp

lemma eq_fract:
  shows "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  and "\<And>a. Fract a 0 = Fract 0 1"
  and "\<And>a c. Fract 0 a = Fract 0 c"
  by (simp_all add: Fract_def)

instantiation fract :: (idom) "{comm_ring_1, power}"
begin

definition
  Zero_fract_def [code, code unfold]: "0 = Fract 0 1"

definition
  One_fract_def [code, code unfold]: "1 = Fract 1 1"

definition
  add_fract_def [code del]:
  "q + r = Abs_fract (\<Union>x \<in> Rep_fract q. \<Union>y \<in> Rep_fract r.
    fractrel `` {(fst x * snd y + fst y * snd x, snd x * snd y)})"

lemma add_fract [simp]:
  assumes "b \<noteq> (0::'a::idom)" and "d \<noteq> 0"
  shows "Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
proof -
  have "(\<lambda>x y. fractrel``{(fst x * snd y + fst y * snd x, snd x * snd y :: 'a)})
    respects2 fractrel"
  apply (rule equiv_fractrel [THEN congruent2_commuteI]) apply (auto simp add: algebra_simps)
  unfolding mult_assoc[symmetric] .
  with assms show ?thesis by (simp add: Fract_def add_fract_def UN_fractrel2)
qed

definition
  minus_fract_def [code del]:
  "- q = Abs_fract (\<Union>x \<in> Rep_fract q. fractrel `` {(- fst x, snd x)})"

lemma minus_fract [simp, code]: "- Fract a b = Fract (- a) (b::'a::idom)"
proof -
  have "(\<lambda>x. fractrel `` {(- fst x, snd x :: 'a)}) respects fractrel"
    by (simp add: congruent_def)
  then show ?thesis by (simp add: Fract_def minus_fract_def UN_fractrel)
qed

lemma minus_fract_cancel [simp]: "Fract (- a) (- b) = Fract a b"
  by (cases "b = 0") (simp_all add: eq_fract)

definition
  diff_fract_def [code del]: "q - r = q + - (r::'a fract)"

lemma diff_fract [simp]:
  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  using assms by (simp add: diff_fract_def diff_minus)

definition
  mult_fract_def [code del]:
  "q * r = Abs_fract (\<Union>x \<in> Rep_fract q. \<Union>y \<in> Rep_fract r.
    fractrel``{(fst x * fst y, snd x * snd y)})"

lemma mult_fract [simp]: "Fract (a::'a::idom) b * Fract c d = Fract (a * c) (b * d)"
proof -
  have "(\<lambda>x y. fractrel `` {(fst x * fst y, snd x * snd y :: 'a)}) respects2 fractrel"
    apply (rule equiv_fractrel [THEN congruent2_commuteI]) apply (auto simp add: algebra_simps)
    unfolding mult_assoc[symmetric] .
  then show ?thesis by (simp add: Fract_def mult_fract_def UN_fractrel2)
qed

lemma mult_fract_cancel:
  assumes "c \<noteq> 0"
  shows "Fract (c * a) (c * b) = Fract a b"
proof -
  from assms have "Fract c c = Fract 1 1" by (simp add: Fract_def)
  then show ?thesis by (simp add: mult_fract [symmetric])
qed

instance proof
  fix q r s :: "'a fract" show "(q * r) * s = q * (r * s)" 
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
next
  fix q r :: "'a fract" show "q * r = r * q"
    by (cases q, cases r) (simp add: eq_fract algebra_simps)
next
  fix q :: "'a fract" show "1 * q = q"
    by (cases q) (simp add: One_fract_def eq_fract)
next
  fix q r s :: "'a fract" show "(q + r) + s = q + (r + s)"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
next
  fix q r :: "'a fract" show "q + r = r + q"
    by (cases q, cases r) (simp add: eq_fract algebra_simps)
next
  fix q :: "'a fract" show "0 + q = q"
    by (cases q) (simp add: Zero_fract_def eq_fract)
next
  fix q :: "'a fract" show "- q + q = 0"
    by (cases q) (simp add: Zero_fract_def eq_fract)
next
  fix q r :: "'a fract" show "q - r = q + - r"
    by (cases q, cases r) (simp add: eq_fract)
next
  fix q r s :: "'a fract" show "(q + r) * s = q * s + r * s"
    by (cases q, cases r, cases s) (simp add: eq_fract algebra_simps)
next
  show "(0::'a fract) \<noteq> 1" by (simp add: Zero_fract_def One_fract_def eq_fract)
qed

end

lemma of_nat_fract: "of_nat k = Fract (of_nat k) 1"
  by (induct k) (simp_all add: Zero_fract_def One_fract_def)

lemma Fract_of_nat_eq: "Fract (of_nat k) 1 = of_nat k"
  by (rule of_nat_fract [symmetric])

lemma fract_collapse [code post]:
  "Fract 0 k = 0"
  "Fract 1 1 = 1"
  "Fract k 0 = 0"
  by (cases "k = 0")
    (simp_all add: Zero_fract_def One_fract_def eq_fract Fract_def)

lemma fract_expand [code unfold]:
  "0 = Fract 0 1"
  "1 = Fract 1 1"
  by (simp_all add: fract_collapse)

lemma Fract_cases_nonzero [case_names Fract 0]:
  assumes Fract: "\<And>a b. q = Fract a b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> C"
  assumes 0: "q = 0 \<Longrightarrow> C"
  shows C
proof (cases "q = 0")
  case True then show C using 0 by auto
next
  case False
  then obtain a b where "q = Fract a b" and "b \<noteq> 0" by (cases q) auto
  moreover with False have "0 \<noteq> Fract a b" by simp
  with `b \<noteq> 0` have "a \<noteq> 0" by (simp add: Zero_fract_def eq_fract)
  with Fract `q = Fract a b` `b \<noteq> 0` show C by auto
qed
  


subsubsection {* The field of rational numbers *}

context idom
begin
subclass ring_no_zero_divisors ..
thm mult_eq_0_iff
end

instantiation fract :: (idom) "{field, division_by_zero}"
begin

definition
  inverse_fract_def [code del]:
  "inverse q = Abs_fract (\<Union>x \<in> Rep_fract q.
     fractrel `` {if fst x = 0 then (0, 1) else (snd x, fst x)})"


lemma inverse_fract [simp]: "inverse (Fract a b) = Fract (b::'a::idom) a"
proof -
  have stupid: "\<And>x. (0::'a) = x \<longleftrightarrow> x = 0" by auto
  have "(\<lambda>x. fractrel `` {if fst x = 0 then (0, 1) else (snd x, fst x :: 'a)}) respects fractrel"
    by (auto simp add: congruent_def stupid algebra_simps)
  then show ?thesis by (simp add: Fract_def inverse_fract_def UN_fractrel)
qed

definition
  divide_fract_def [code del]: "q / r = q * inverse (r:: 'a fract)"

lemma divide_fract [simp]: "Fract a b / Fract c d = Fract (a * d) (b * c)"
  by (simp add: divide_fract_def)

instance proof
  show "inverse 0 = (0:: 'a fract)" by (simp add: fract_expand)
    (simp add: fract_collapse)
next
  fix q :: "'a fract"
  assume "q \<noteq> 0"
  then show "inverse q * q = 1" apply (cases q rule: Fract_cases_nonzero)
    by (simp_all add: mult_fract  inverse_fract fract_expand eq_fract mult_commute)
next
  fix q r :: "'a fract"
  show "q / r = q * inverse r" by (simp add: divide_fract_def)
qed

end


end