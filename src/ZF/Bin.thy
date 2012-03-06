(*  Title:      ZF/Bin.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

   The sign Pls stands for an infinite string of leading 0's.
   The sign Min stands for an infinite string of leading 1's.

A number can have multiple representations, namely leading 0's with sign
Pls and leading 1's with sign Min.  See twos-compl.ML/int_of_binary for
the numerical interpretation.

The representation expects that (m mod 2) is 0 or 1, even if m is negative;
For instance, ~5 div 2 = ~3 and ~5 mod 2 = 1; thus ~5 = (~3)*2 + 1
*)

header{*Arithmetic on Binary Integers*}

theory Bin
imports Int_ZF Datatype_ZF
uses ("Tools/numeral_syntax.ML")
begin

consts  bin :: i
datatype
  "bin" = Pls
        | Min
        | Bit ("w: bin", "b: bool")     (infixl "BIT" 90)

consts
  integ_of  :: "i=>i"
  NCons     :: "[i,i]=>i"
  bin_succ  :: "i=>i"
  bin_pred  :: "i=>i"
  bin_minus :: "i=>i"
  bin_adder :: "i=>i"
  bin_mult  :: "[i,i]=>i"

primrec
  integ_of_Pls:  "integ_of (Pls)     = $# 0"
  integ_of_Min:  "integ_of (Min)     = $-($#1)"
  integ_of_BIT:  "integ_of (w BIT b) = $#b $+ integ_of(w) $+ integ_of(w)"

    (** recall that cond(1,b,c)=b and cond(0,b,c)=0 **)

primrec (*NCons adds a bit, suppressing leading 0s and 1s*)
  NCons_Pls: "NCons (Pls,b)     = cond(b,Pls BIT b,Pls)"
  NCons_Min: "NCons (Min,b)     = cond(b,Min,Min BIT b)"
  NCons_BIT: "NCons (w BIT c,b) = w BIT c BIT b"

primrec (*successor.  If a BIT, can change a 0 to a 1 without recursion.*)
  bin_succ_Pls:  "bin_succ (Pls)     = Pls BIT 1"
  bin_succ_Min:  "bin_succ (Min)     = Pls"
  bin_succ_BIT:  "bin_succ (w BIT b) = cond(b, bin_succ(w) BIT 0, NCons(w,1))"

primrec (*predecessor*)
  bin_pred_Pls:  "bin_pred (Pls)     = Min"
  bin_pred_Min:  "bin_pred (Min)     = Min BIT 0"
  bin_pred_BIT:  "bin_pred (w BIT b) = cond(b, NCons(w,0), bin_pred(w) BIT 1)"

primrec (*unary negation*)
  bin_minus_Pls:
    "bin_minus (Pls)       = Pls"
  bin_minus_Min:
    "bin_minus (Min)       = Pls BIT 1"
  bin_minus_BIT:
    "bin_minus (w BIT b) = cond(b, bin_pred(NCons(bin_minus(w),0)),
                                bin_minus(w) BIT 0)"

primrec (*sum*)
  bin_adder_Pls:
    "bin_adder (Pls)     = (\<lambda>w\<in>bin. w)"
  bin_adder_Min:
    "bin_adder (Min)     = (\<lambda>w\<in>bin. bin_pred(w))"
  bin_adder_BIT:
    "bin_adder (v BIT x) =
       (\<lambda>w\<in>bin.
         bin_case (v BIT x, bin_pred(v BIT x),
                   %w y. NCons(bin_adder (v) ` cond(x and y, bin_succ(w), w),
                               x xor y),
                   w))"

(*The bin_case above replaces the following mutually recursive function:
primrec
  "adding (v,x,Pls)     = v BIT x"
  "adding (v,x,Min)     = bin_pred(v BIT x)"
  "adding (v,x,w BIT y) = NCons(bin_adder (v, cond(x and y, bin_succ(w), w)),
                                x xor y)"
*)

definition
  bin_add   :: "[i,i]=>i"  where
    "bin_add(v,w) == bin_adder(v)`w"


primrec
  bin_mult_Pls:
    "bin_mult (Pls,w)     = Pls"
  bin_mult_Min:
    "bin_mult (Min,w)     = bin_minus(w)"
  bin_mult_BIT:
    "bin_mult (v BIT b,w) = cond(b, bin_add(NCons(bin_mult(v,w),0),w),
                                 NCons(bin_mult(v,w),0))"

syntax
  "_Int"    :: "xnum_token => i"        ("_")

use "Tools/numeral_syntax.ML"
setup Numeral_Syntax.setup


declare bin.intros [simp,TC]

lemma NCons_Pls_0: "NCons(Pls,0) = Pls"
by simp

lemma NCons_Pls_1: "NCons(Pls,1) = Pls BIT 1"
by simp

lemma NCons_Min_0: "NCons(Min,0) = Min BIT 0"
by simp

lemma NCons_Min_1: "NCons(Min,1) = Min"
by simp

lemma NCons_BIT: "NCons(w BIT x,b) = w BIT x BIT b"
by (simp add: bin.case_eqns)

lemmas NCons_simps [simp] =
    NCons_Pls_0 NCons_Pls_1 NCons_Min_0 NCons_Min_1 NCons_BIT



(** Type checking **)

lemma integ_of_type [TC]: "w: bin ==> integ_of(w) \<in> int"
apply (induct_tac "w")
apply (simp_all add: bool_into_nat)
done

lemma NCons_type [TC]: "[| w: bin; b: bool |] ==> NCons(w,b) \<in> bin"
by (induct_tac "w", auto)

lemma bin_succ_type [TC]: "w: bin ==> bin_succ(w) \<in> bin"
by (induct_tac "w", auto)

lemma bin_pred_type [TC]: "w: bin ==> bin_pred(w) \<in> bin"
by (induct_tac "w", auto)

lemma bin_minus_type [TC]: "w: bin ==> bin_minus(w) \<in> bin"
by (induct_tac "w", auto)

(*This proof is complicated by the mutual recursion*)
lemma bin_add_type [rule_format,TC]:
     "v: bin ==> \<forall>w\<in>bin. bin_add(v,w) \<in> bin"
apply (unfold bin_add_def)
apply (induct_tac "v")
apply (rule_tac [3] ballI)
apply (rename_tac [3] "w'")
apply (induct_tac [3] "w'")
apply (simp_all add: NCons_type)
done

lemma bin_mult_type [TC]: "[| v: bin; w: bin |] ==> bin_mult(v,w) \<in> bin"
by (induct_tac "v", auto)


subsubsection{*The Carry and Borrow Functions,
            @{term bin_succ} and @{term bin_pred}*}

(*NCons preserves the integer value of its argument*)
lemma integ_of_NCons [simp]:
     "[| w: bin; b: bool |] ==> integ_of(NCons(w,b)) = integ_of(w BIT b)"
apply (erule bin.cases)
apply (auto elim!: boolE)
done

lemma integ_of_succ [simp]:
     "w: bin ==> integ_of(bin_succ(w)) = $#1 $+ integ_of(w)"
apply (erule bin.induct)
apply (auto simp add: zadd_ac elim!: boolE)
done

lemma integ_of_pred [simp]:
     "w: bin ==> integ_of(bin_pred(w)) = $- ($#1) $+ integ_of(w)"
apply (erule bin.induct)
apply (auto simp add: zadd_ac elim!: boolE)
done


subsubsection{*@{term bin_minus}: Unary Negation of Binary Integers*}

lemma integ_of_minus: "w: bin ==> integ_of(bin_minus(w)) = $- integ_of(w)"
apply (erule bin.induct)
apply (auto simp add: zadd_ac zminus_zadd_distrib  elim!: boolE)
done


subsubsection{*@{term bin_add}: Binary Addition*}

lemma bin_add_Pls [simp]: "w: bin ==> bin_add(Pls,w) = w"
by (unfold bin_add_def, simp)

lemma bin_add_Pls_right: "w: bin ==> bin_add(w,Pls) = w"
apply (unfold bin_add_def)
apply (erule bin.induct, auto)
done

lemma bin_add_Min [simp]: "w: bin ==> bin_add(Min,w) = bin_pred(w)"
by (unfold bin_add_def, simp)

lemma bin_add_Min_right: "w: bin ==> bin_add(w,Min) = bin_pred(w)"
apply (unfold bin_add_def)
apply (erule bin.induct, auto)
done

lemma bin_add_BIT_Pls [simp]: "bin_add(v BIT x,Pls) = v BIT x"
by (unfold bin_add_def, simp)

lemma bin_add_BIT_Min [simp]: "bin_add(v BIT x,Min) = bin_pred(v BIT x)"
by (unfold bin_add_def, simp)

lemma bin_add_BIT_BIT [simp]:
     "[| w: bin;  y: bool |]
      ==> bin_add(v BIT x, w BIT y) =
          NCons(bin_add(v, cond(x and y, bin_succ(w), w)), x xor y)"
by (unfold bin_add_def, simp)

lemma integ_of_add [rule_format]:
     "v: bin ==>
          \<forall>w\<in>bin. integ_of(bin_add(v,w)) = integ_of(v) $+ integ_of(w)"
apply (erule bin.induct, simp, simp)
apply (rule ballI)
apply (induct_tac "wa")
apply (auto simp add: zadd_ac elim!: boolE)
done

(*Subtraction*)
lemma diff_integ_of_eq:
     "[| v: bin;  w: bin |]
      ==> integ_of(v) $- integ_of(w) = integ_of(bin_add (v, bin_minus(w)))"
apply (unfold zdiff_def)
apply (simp add: integ_of_add integ_of_minus)
done


subsubsection{*@{term bin_mult}: Binary Multiplication*}

lemma integ_of_mult:
     "[| v: bin;  w: bin |]
      ==> integ_of(bin_mult(v,w)) = integ_of(v) $* integ_of(w)"
apply (induct_tac "v", simp)
apply (simp add: integ_of_minus)
apply (auto simp add: zadd_ac integ_of_add zadd_zmult_distrib  elim!: boolE)
done


subsection{*Computations*}

(** extra rules for bin_succ, bin_pred **)

lemma bin_succ_1: "bin_succ(w BIT 1) = bin_succ(w) BIT 0"
by simp

lemma bin_succ_0: "bin_succ(w BIT 0) = NCons(w,1)"
by simp

lemma bin_pred_1: "bin_pred(w BIT 1) = NCons(w,0)"
by simp

lemma bin_pred_0: "bin_pred(w BIT 0) = bin_pred(w) BIT 1"
by simp

(** extra rules for bin_minus **)

lemma bin_minus_1: "bin_minus(w BIT 1) = bin_pred(NCons(bin_minus(w), 0))"
by simp

lemma bin_minus_0: "bin_minus(w BIT 0) = bin_minus(w) BIT 0"
by simp

(** extra rules for bin_add **)

lemma bin_add_BIT_11: "w: bin ==> bin_add(v BIT 1, w BIT 1) =
                     NCons(bin_add(v, bin_succ(w)), 0)"
by simp

lemma bin_add_BIT_10: "w: bin ==> bin_add(v BIT 1, w BIT 0) =
                     NCons(bin_add(v,w), 1)"
by simp

lemma bin_add_BIT_0: "[| w: bin;  y: bool |]
      ==> bin_add(v BIT 0, w BIT y) = NCons(bin_add(v,w), y)"
by simp

(** extra rules for bin_mult **)

lemma bin_mult_1: "bin_mult(v BIT 1, w) = bin_add(NCons(bin_mult(v,w),0), w)"
by simp

lemma bin_mult_0: "bin_mult(v BIT 0, w) = NCons(bin_mult(v,w),0)"
by simp


(** Simplification rules with integer constants **)

lemma int_of_0: "$#0 = #0"
by simp

lemma int_of_succ: "$# succ(n) = #1 $+ $#n"
by (simp add: int_of_add [symmetric] natify_succ)

lemma zminus_0 [simp]: "$- #0 = #0"
by simp

lemma zadd_0_intify [simp]: "#0 $+ z = intify(z)"
by simp

lemma zadd_0_right_intify [simp]: "z $+ #0 = intify(z)"
by simp

lemma zmult_1_intify [simp]: "#1 $* z = intify(z)"
by simp

lemma zmult_1_right_intify [simp]: "z $* #1 = intify(z)"
by (subst zmult_commute, simp)

lemma zmult_0 [simp]: "#0 $* z = #0"
by simp

lemma zmult_0_right [simp]: "z $* #0 = #0"
by (subst zmult_commute, simp)

lemma zmult_minus1 [simp]: "#-1 $* z = $-z"
by (simp add: zcompare_rls)

lemma zmult_minus1_right [simp]: "z $* #-1 = $-z"
apply (subst zmult_commute)
apply (rule zmult_minus1)
done


subsection{*Simplification Rules for Comparison of Binary Numbers*}
text{*Thanks to Norbert Voelker*}

(** Equals (=) **)

lemma eq_integ_of_eq:
     "[| v: bin;  w: bin |]
      ==> ((integ_of(v)) = integ_of(w)) <->
          iszero (integ_of (bin_add (v, bin_minus(w))))"
apply (unfold iszero_def)
apply (simp add: zcompare_rls integ_of_add integ_of_minus)
done

lemma iszero_integ_of_Pls: "iszero (integ_of(Pls))"
by (unfold iszero_def, simp)


lemma nonzero_integ_of_Min: "~ iszero (integ_of(Min))"
apply (unfold iszero_def)
apply (simp add: zminus_equation)
done

lemma iszero_integ_of_BIT:
     "[| w: bin; x: bool |]
      ==> iszero (integ_of (w BIT x)) <-> (x=0 & iszero (integ_of(w)))"
apply (unfold iszero_def, simp)
apply (subgoal_tac "integ_of (w) \<in> int")
apply typecheck
apply (drule int_cases)
apply (safe elim!: boolE)
apply (simp_all (asm_lr) add: zcompare_rls zminus_zadd_distrib [symmetric]
                     int_of_add [symmetric])
done

lemma iszero_integ_of_0:
     "w: bin ==> iszero (integ_of (w BIT 0)) <-> iszero (integ_of(w))"
by (simp only: iszero_integ_of_BIT, blast)

lemma iszero_integ_of_1: "w: bin ==> ~ iszero (integ_of (w BIT 1))"
by (simp only: iszero_integ_of_BIT, blast)



(** Less-than (<) **)

lemma less_integ_of_eq_neg:
     "[| v: bin;  w: bin |]
      ==> integ_of(v) $< integ_of(w)
          <-> znegative (integ_of (bin_add (v, bin_minus(w))))"
apply (unfold zless_def zdiff_def)
apply (simp add: integ_of_minus integ_of_add)
done

lemma not_neg_integ_of_Pls: "~ znegative (integ_of(Pls))"
by simp

lemma neg_integ_of_Min: "znegative (integ_of(Min))"
by simp

lemma neg_integ_of_BIT:
     "[| w: bin; x: bool |]
      ==> znegative (integ_of (w BIT x)) <-> znegative (integ_of(w))"
apply simp
apply (subgoal_tac "integ_of (w) \<in> int")
apply typecheck
apply (drule int_cases)
apply (auto elim!: boolE simp add: int_of_add [symmetric]  zcompare_rls)
apply (simp_all add: zminus_zadd_distrib [symmetric] zdiff_def
                     int_of_add [symmetric])
apply (subgoal_tac "$#1 $- $# succ (succ (n #+ n)) = $- $# succ (n #+ n) ")
 apply (simp add: zdiff_def)
apply (simp add: equation_zminus int_of_diff [symmetric])
done

(** Less-than-or-equals (<=) **)

lemma le_integ_of_eq_not_less:
     "(integ_of(x) $<= (integ_of(w))) <-> ~ (integ_of(w) $< (integ_of(x)))"
by (simp add: not_zless_iff_zle [THEN iff_sym])


(*Delete the original rewrites, with their clumsy conditional expressions*)
declare bin_succ_BIT [simp del]
        bin_pred_BIT [simp del]
        bin_minus_BIT [simp del]
        NCons_Pls [simp del]
        NCons_Min [simp del]
        bin_adder_BIT [simp del]
        bin_mult_BIT [simp del]

(*Hide the binary representation of integer constants*)
declare integ_of_Pls [simp del] integ_of_Min [simp del] integ_of_BIT [simp del]


lemmas bin_arith_extra_simps =
     integ_of_add [symmetric]
     integ_of_minus [symmetric]
     integ_of_mult [symmetric]
     bin_succ_1 bin_succ_0
     bin_pred_1 bin_pred_0
     bin_minus_1 bin_minus_0
     bin_add_Pls_right bin_add_Min_right
     bin_add_BIT_0 bin_add_BIT_10 bin_add_BIT_11
     diff_integ_of_eq
     bin_mult_1 bin_mult_0 NCons_simps


(*For making a minimal simpset, one must include these default simprules
  of thy.  Also include simp_thms, or at least (~False)=True*)
lemmas bin_arith_simps =
     bin_pred_Pls bin_pred_Min
     bin_succ_Pls bin_succ_Min
     bin_add_Pls bin_add_Min
     bin_minus_Pls bin_minus_Min
     bin_mult_Pls bin_mult_Min
     bin_arith_extra_simps

(*Simplification of relational operations*)
lemmas bin_rel_simps =
     eq_integ_of_eq iszero_integ_of_Pls nonzero_integ_of_Min
     iszero_integ_of_0 iszero_integ_of_1
     less_integ_of_eq_neg
     not_neg_integ_of_Pls neg_integ_of_Min neg_integ_of_BIT
     le_integ_of_eq_not_less

declare bin_arith_simps [simp]
declare bin_rel_simps [simp]


(** Simplification of arithmetic when nested to the right **)

lemma add_integ_of_left [simp]:
     "[| v: bin;  w: bin |]
      ==> integ_of(v) $+ (integ_of(w) $+ z) = (integ_of(bin_add(v,w)) $+ z)"
by (simp add: zadd_assoc [symmetric])

lemma mult_integ_of_left [simp]:
     "[| v: bin;  w: bin |]
      ==> integ_of(v) $* (integ_of(w) $* z) = (integ_of(bin_mult(v,w)) $* z)"
by (simp add: zmult_assoc [symmetric])

lemma add_integ_of_diff1 [simp]:
    "[| v: bin;  w: bin |]
      ==> integ_of(v) $+ (integ_of(w) $- c) = integ_of(bin_add(v,w)) $- (c)"
apply (unfold zdiff_def)
apply (rule add_integ_of_left, auto)
done

lemma add_integ_of_diff2 [simp]:
     "[| v: bin;  w: bin |]
      ==> integ_of(v) $+ (c $- integ_of(w)) =
          integ_of (bin_add (v, bin_minus(w))) $+ (c)"
apply (subst diff_integ_of_eq [symmetric])
apply (simp_all add: zdiff_def zadd_ac)
done


(** More for integer constants **)

declare int_of_0 [simp] int_of_succ [simp]

lemma zdiff0 [simp]: "#0 $- x = $-x"
by (simp add: zdiff_def)

lemma zdiff0_right [simp]: "x $- #0 = intify(x)"
by (simp add: zdiff_def)

lemma zdiff_self [simp]: "x $- x = #0"
by (simp add: zdiff_def)

lemma znegative_iff_zless_0: "k: int ==> znegative(k) <-> k $< #0"
by (simp add: zless_def)

lemma zero_zless_imp_znegative_zminus: "[|#0 $< k; k: int|] ==> znegative($-k)"
by (simp add: zless_def)

lemma zero_zle_int_of [simp]: "#0 $<= $# n"
by (simp add: not_zless_iff_zle [THEN iff_sym] znegative_iff_zless_0 [THEN iff_sym])

lemma nat_of_0 [simp]: "nat_of(#0) = 0"
by (simp only: natify_0 int_of_0 [symmetric] nat_of_int_of)

lemma nat_le_int0_lemma: "[| z $<= $#0; z: int |] ==> nat_of(z) = 0"
by (auto simp add: znegative_iff_zless_0 [THEN iff_sym] zle_def zneg_nat_of)

lemma nat_le_int0: "z $<= $#0 ==> nat_of(z) = 0"
apply (subgoal_tac "nat_of (intify (z)) = 0")
apply (rule_tac [2] nat_le_int0_lemma, auto)
done

lemma int_of_eq_0_imp_natify_eq_0: "$# n = #0 ==> natify(n) = 0"
by (rule not_znegative_imp_zero, auto)

lemma nat_of_zminus_int_of: "nat_of($- $# n) = 0"
by (simp add: nat_of_def int_of_def raw_nat_of zminus image_intrel_int)

lemma int_of_nat_of: "#0 $<= z ==> $# nat_of(z) = intify(z)"
apply (rule not_zneg_nat_of_intify)
apply (simp add: znegative_iff_zless_0 not_zless_iff_zle)
done

declare int_of_nat_of [simp] nat_of_zminus_int_of [simp]

lemma int_of_nat_of_if: "$# nat_of(z) = (if #0 $<= z then intify(z) else #0)"
by (simp add: int_of_nat_of znegative_iff_zless_0 not_zle_iff_zless)

lemma zless_nat_iff_int_zless: "[| m: nat; z: int |] ==> (m < nat_of(z)) <-> ($#m $< z)"
apply (case_tac "znegative (z) ")
apply (erule_tac [2] not_zneg_nat_of [THEN subst])
apply (auto dest: zless_trans dest!: zero_zle_int_of [THEN zle_zless_trans]
            simp add: znegative_iff_zless_0)
done


(** nat_of and zless **)

(*An alternative condition is  @{term"$#0 \<subseteq> w"}  *)
lemma zless_nat_conj_lemma: "$#0 $< z ==> (nat_of(w) < nat_of(z)) <-> (w $< z)"
apply (rule iff_trans)
apply (rule zless_int_of [THEN iff_sym])
apply (auto simp add: int_of_nat_of_if simp del: zless_int_of)
apply (auto elim: zless_asym simp add: not_zle_iff_zless)
apply (blast intro: zless_zle_trans)
done

lemma zless_nat_conj: "(nat_of(w) < nat_of(z)) <-> ($#0 $< z & w $< z)"
apply (case_tac "$#0 $< z")
apply (auto simp add: zless_nat_conj_lemma nat_le_int0 not_zless_iff_zle)
done

(*This simprule cannot be added unless we can find a way to make eq_integ_of_eq
  unconditional!
  [The condition "True" is a hack to prevent looping.
    Conditional rewrite rules are tried after unconditional ones, so a rule
    like eq_nat_number_of will be tried first to eliminate #mm=#nn.]
  lemma integ_of_reorient [simp]:
       "True ==> (integ_of(w) = x) <-> (x = integ_of(w))"
  by auto
*)

lemma integ_of_minus_reorient [simp]:
     "(integ_of(w) = $- x) <-> ($- x = integ_of(w))"
by auto

lemma integ_of_add_reorient [simp]:
     "(integ_of(w) = x $+ y) <-> (x $+ y = integ_of(w))"
by auto

lemma integ_of_diff_reorient [simp]:
     "(integ_of(w) = x $- y) <-> (x $- y = integ_of(w))"
by auto

lemma integ_of_mult_reorient [simp]:
     "(integ_of(w) = x $* y) <-> (x $* y = integ_of(w))"
by auto

end
