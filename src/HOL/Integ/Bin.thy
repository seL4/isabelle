(*  Title:	HOL/Integ/Bin.thy
    ID:         $Id$
    Authors:	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright	1994  University of Cambridge

Ported from ZF to HOL by David Spelt.
*)

header{*Arithmetic on Binary Integers*}

theory Bin = IntDef + Numeral:

axclass number_ring \<subseteq> number, comm_ring_1
  number_of_Pls: "number_of bin.Pls = 0"
  number_of_Min: "number_of bin.Min = - 1"
  number_of_BIT: "number_of(w BIT x) = (if x then 1 else 0) +
	                               (number_of w) + (number_of w)"
subsection{*Converting Numerals to Rings: @{term number_of}*}

lemmas number_of = number_of_Pls number_of_Min number_of_BIT

lemma number_of_NCons [simp]:
     "number_of(NCons w b) = (number_of(w BIT b)::'a::number_ring)"
by (induct_tac "w", simp_all add: number_of)

lemma number_of_succ: "number_of(bin_succ w) = (1 + number_of w ::'a::number_ring)"
apply (induct_tac "w")
apply (simp_all add: number_of add_ac)
done

lemma number_of_pred: "number_of(bin_pred w) = (- 1 + number_of w ::'a::number_ring)"
apply (induct_tac "w")
apply (simp_all add: number_of add_assoc [symmetric]) 
apply (simp add: add_ac)
done

lemma number_of_minus: "number_of(bin_minus w) = (- (number_of w)::'a::number_ring)"
apply (induct_tac "w")
apply (simp_all del: bin_pred_Pls bin_pred_Min bin_pred_BIT 
            add: number_of number_of_succ number_of_pred add_assoc)
done

text{*This proof is complicated by the mutual recursion*}
lemma number_of_add [rule_format]:
     "\<forall>w. number_of(bin_add v w) = (number_of v + number_of w::'a::number_ring)"
apply (induct_tac "v")
apply (simp add: number_of)
apply (simp add: number_of number_of_pred)
apply (rule allI)
apply (induct_tac "w")
apply (simp_all add: number_of bin_add_BIT_BIT number_of_succ number_of_pred add_ac)
apply (simp add: add_left_commute [of "1::'a::number_ring"]) 
done

lemma number_of_mult:
     "number_of(bin_mult v w) = (number_of v * number_of w::'a::number_ring)"
apply (induct_tac "v", simp add: number_of) 
apply (simp add: number_of number_of_minus) 
apply (simp add: number_of number_of_add left_distrib add_ac)
done

text{*The correctness of shifting.  But it doesn't seem to give a measurable
  speed-up.*}
lemma double_number_of_BIT:
     "(1+1) * number_of w = (number_of (w BIT False) ::'a::number_ring)"
apply (induct_tac "w")
apply (simp_all add: number_of number_of_add left_distrib add_ac)
done


text{*Converting numerals 0 and 1 to their abstract versions*}
lemma numeral_0_eq_0 [simp]: "Numeral0 = (0::'a::number_ring)"
by (simp add: number_of) 

lemma numeral_1_eq_1 [simp]: "Numeral1 = (1::'a::number_ring)"
by (simp add: number_of) 

text{*Special-case simplification for small constants*}

text{*Unary minus for the abstract constant 1. Cannot be inserted
  as a simprule until later: it is @{text number_of_Min} re-oriented!*}
lemma numeral_m1_eq_minus_1: "(-1::'a::number_ring) = - 1"
by (simp add: number_of)

lemma mult_minus1 [simp]: "-1 * z = -(z::'a::number_ring)"
by (simp add: numeral_m1_eq_minus_1)

lemma mult_minus1_right [simp]: "z * -1 = -(z::'a::number_ring)"
by (simp add: numeral_m1_eq_minus_1)

(*Negation of a coefficient*)
lemma minus_number_of_mult [simp]:
     "- (number_of w) * z = number_of(bin_minus w) * (z::'a::number_ring)"
by (simp add: number_of_minus)

text{*Subtraction*}
lemma diff_number_of_eq:
     "number_of v - number_of w =
      (number_of(bin_add v (bin_minus w))::'a::number_ring)"
by (simp add: diff_minus number_of_add number_of_minus)


subsection{*Equality of Binary Numbers*}

text{*First version by Norbert Voelker*}

lemma eq_number_of_eq:
  "((number_of x::'a::number_ring) = number_of y) =
   iszero (number_of (bin_add x (bin_minus y)) :: 'a)"
by (simp add: iszero_def compare_rls number_of_add number_of_minus)

lemma iszero_number_of_Pls: "iszero ((number_of bin.Pls)::'a::number_ring)"
by (simp add: iszero_def numeral_0_eq_0)

lemma nonzero_number_of_Min: "~ iszero ((number_of bin.Min)::'a::number_ring)"
by (simp add: iszero_def numeral_m1_eq_minus_1 eq_commute)


subsection{*Comparisons, for Ordered Rings*}

lemma double_eq_0_iff: "(a + a = 0) = (a = (0::'a::ordered_idom))"
proof -
  have "a + a = (1+1)*a" by (simp add: left_distrib)
  with zero_less_two [where 'a = 'a]
  show ?thesis by force
qed

lemma le_imp_0_less: 
  assumes le: "0 \<le> z" shows "(0::int) < 1 + z"
proof -
  have "0 \<le> z" .
  also have "... < z + 1" by (rule less_add_one) 
  also have "... = 1 + z" by (simp add: add_ac)
  finally show "0 < 1 + z" .
qed

lemma odd_nonzero: "1 + z + z \<noteq> (0::int)";
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
    have "0 < 1 + (int n + int n)"
      by (simp add: le_imp_0_less add_increasing) 
    also have "... = - (1 + z + z)"
      by (simp add: neg add_assoc [symmetric], simp add: add_commute) 
    also have "... = 0" by (simp add: eq) 
    finally have "0<0" ..
    thus False by blast
  qed
qed


text{*The premise involving @{term Ints} prevents @{term "a = 1/2"}.*}
lemma Ints_odd_nonzero: "a \<in> Ints ==> 1 + a + a \<noteq> (0::'a::ordered_idom)"
proof (unfold Ints_def) 
  assume "a \<in> range of_int"
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume eq: "1 + a + a = 0"
    hence "of_int (1 + z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "1 + z + z = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
qed 

lemma Ints_number_of: "(number_of w :: 'a::number_ring) \<in> Ints"
by (induct_tac "w", simp_all add: number_of)

lemma iszero_number_of_BIT:
     "iszero (number_of (w BIT x)::'a) = 
      (~x & iszero (number_of w::'a::{ordered_idom,number_ring}))"
by (simp add: iszero_def compare_rls zero_reorient double_eq_0_iff 
              number_of Ints_odd_nonzero [OF Ints_number_of])

lemma iszero_number_of_0:
     "iszero (number_of (w BIT False) :: 'a::{ordered_idom,number_ring}) = 
      iszero (number_of w :: 'a)"
by (simp only: iszero_number_of_BIT simp_thms)

lemma iszero_number_of_1:
     "~ iszero (number_of (w BIT True)::'a::{ordered_idom,number_ring})"
by (simp only: iszero_number_of_BIT simp_thms)



subsection{*The Less-Than Relation*}

lemma less_number_of_eq_neg:
    "((number_of x::'a::{ordered_idom,number_ring}) < number_of y)
     = neg (number_of (bin_add x (bin_minus y)) :: 'a)"
apply (subst less_iff_diff_less_0) 
apply (simp add: neg_def diff_minus number_of_add number_of_minus)
done

text{*If @{term Numeral0} is rewritten to 0 then this rule can't be applied:
  @{term Numeral0} IS @{term "number_of Pls"} *}
lemma not_neg_number_of_Pls:
     "~ neg (number_of bin.Pls ::'a::{ordered_idom,number_ring})"
by (simp add: neg_def numeral_0_eq_0)

lemma neg_number_of_Min:
     "neg (number_of bin.Min ::'a::{ordered_idom,number_ring})"
by (simp add: neg_def zero_less_one numeral_m1_eq_minus_1)

lemma double_less_0_iff: "(a + a < 0) = (a < (0::'a::ordered_idom))"
proof -
  have "(a + a < 0) = ((1+1)*a < 0)" by (simp add: left_distrib)
  also have "... = (a < 0)"
    by (simp add: mult_less_0_iff zero_less_two 
                  order_less_not_sym [OF zero_less_two]) 
  finally show ?thesis .
qed

lemma odd_less_0: "(1 + z + z < 0) = (z < (0::int))";
proof (cases z rule: int_cases)
  case (nonneg n)
  thus ?thesis by (simp add: linorder_not_less add_assoc add_increasing
                             le_imp_0_less [THEN order_less_imp_le])  
next
  case (neg n)
  thus ?thesis by (simp del: int_Suc
			add: int_Suc0_eq_1 [symmetric] zadd_int compare_rls)
qed

text{*The premise involving @{term Ints} prevents @{term "a = 1/2"}.*}
lemma Ints_odd_less_0: 
     "a \<in> Ints ==> (1 + a + a < 0) = (a < (0::'a::ordered_idom))";
proof (unfold Ints_def) 
  assume "a \<in> range of_int"
  then obtain z where a: "a = of_int z" ..
  hence "((1::'a) + a + a < 0) = (of_int (1 + z + z) < (of_int 0 :: 'a))"
    by (simp add: a)
  also have "... = (z < 0)" by (simp only: of_int_less_iff odd_less_0)
  also have "... = (a < 0)" by (simp add: a)
  finally show ?thesis .
qed

lemma neg_number_of_BIT:
     "neg (number_of (w BIT x)::'a) = 
      neg (number_of w :: 'a::{ordered_idom,number_ring})"
by (simp add: number_of neg_def double_less_0_iff
              Ints_odd_less_0 [OF Ints_number_of])


text{*Less-Than or Equals*}

text{*Reduces @{term "a\<le>b"} to @{term "~ (b<a)"} for ALL numerals*}
lemmas le_number_of_eq_not_less =
       linorder_not_less [of "number_of w" "number_of v", symmetric, 
                          standard]

lemma le_number_of_eq:
    "((number_of x::'a::{ordered_idom,number_ring}) \<le> number_of y)
     = (~ (neg (number_of (bin_add y (bin_minus x)) :: 'a)))"
by (simp add: le_number_of_eq_not_less less_number_of_eq_neg)


text{*Absolute value (@{term abs})*}

lemma abs_number_of:
     "abs(number_of x::'a::{ordered_idom,number_ring}) =
      (if number_of x < (0::'a) then -number_of x else number_of x)"
by (simp add: abs_if)


text{*Re-orientation of the equation nnn=x*}
lemma number_of_reorient: "(number_of w = x) = (x = number_of w)"
by auto


(*Delete the original rewrites, with their clumsy conditional expressions*)
declare bin_succ_BIT [simp del] bin_pred_BIT [simp del]
        bin_minus_BIT [simp del]

declare bin_add_BIT [simp del] bin_mult_BIT [simp del]
declare NCons_Pls [simp del] NCons_Min [simp del]

(*Hide the binary representation of integer constants*)
declare number_of_Pls [simp del] number_of_Min [simp del]
        number_of_BIT [simp del]



(*Simplification of arithmetic operations on integer constants.
  Note that bin_pred_Pls, etc. were added to the simpset by primrec.*)

lemmas NCons_simps = NCons_Pls_0 NCons_Pls_1 NCons_Min_0 NCons_Min_1 NCons_BIT

lemmas bin_arith_extra_simps = 
       number_of_add [symmetric]
       number_of_minus [symmetric] numeral_m1_eq_minus_1 [symmetric]
       number_of_mult [symmetric]
       bin_succ_1 bin_succ_0
       bin_pred_1 bin_pred_0
       bin_minus_1 bin_minus_0
       bin_add_Pls_right bin_add_Min_right
       bin_add_BIT_0 bin_add_BIT_10 bin_add_BIT_11
       diff_number_of_eq abs_number_of abs_zero abs_one
       bin_mult_1 bin_mult_0 NCons_simps

(*For making a minimal simpset, one must include these default simprules
  of thy.  Also include simp_thms, or at least (~False)=True*)
lemmas bin_arith_simps = 
       bin_pred_Pls bin_pred_Min
       bin_succ_Pls bin_succ_Min
       bin_add_Pls bin_add_Min
       bin_minus_Pls bin_minus_Min
       bin_mult_Pls bin_mult_Min bin_arith_extra_simps

(*Simplification of relational operations*)
lemmas bin_rel_simps = 
       eq_number_of_eq iszero_number_of_Pls nonzero_number_of_Min
       iszero_number_of_0 iszero_number_of_1
       less_number_of_eq_neg
       not_neg_number_of_Pls not_neg_0 not_neg_1 not_iszero_1
       neg_number_of_Min neg_number_of_BIT
       le_number_of_eq

declare bin_arith_extra_simps [simp]
declare bin_rel_simps [simp]


subsection{*Simplification of arithmetic when nested to the right*}

lemma add_number_of_left [simp]:
     "number_of v + (number_of w + z) =
      (number_of(bin_add v w) + z::'a::number_ring)"
by (simp add: add_assoc [symmetric])

lemma mult_number_of_left [simp]:
    "number_of v * (number_of w * z) =
     (number_of(bin_mult v w) * z::'a::number_ring)"
by (simp add: mult_assoc [symmetric])

lemma add_number_of_diff1:
    "number_of v + (number_of w - c) = 
     number_of(bin_add v w) - (c::'a::number_ring)"
by (simp add: diff_minus add_number_of_left)

lemma add_number_of_diff2 [simp]: "number_of v + (c - number_of w) =
     number_of (bin_add v (bin_minus w)) + (c::'a::number_ring)"
apply (subst diff_number_of_eq [symmetric])
apply (simp only: compare_rls)
done

end
