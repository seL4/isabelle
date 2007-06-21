(*  Title:      HOL/Arith_Tools.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Setup of arithmetic tools *}

theory Arith_Tools
imports Groebner_Basis Dense_Linear_Order SetInterval
uses
  "~~/src/Provers/Arith/cancel_numeral_factor.ML"
  "~~/src/Provers/Arith/extract_common_term.ML"
  "int_factor_simprocs.ML"
  "nat_simprocs.ML"
  "Tools/Presburger/cooper_data.ML"
  "Tools/Presburger/generated_cooper.ML"
  ("Tools/Presburger/cooper.ML")
  ("Tools/Presburger/presburger.ML") 
begin

subsection {* Simprocs for the Naturals *}

setup nat_simprocs_setup

subsubsection{*For simplifying @{term "Suc m - K"} and  @{term "K - Suc m"}*}

text{*Where K above is a literal*}

lemma Suc_diff_eq_diff_pred: "Numeral0 < n ==> Suc m - n = m - (n - Numeral1)"
by (simp add: numeral_0_eq_0 numeral_1_eq_1 split add: nat_diff_split)

text {*Now just instantiating @{text n} to @{text "number_of v"} does
  the right simplification, but with some redundant inequality
  tests.*}
lemma neg_number_of_pred_iff_0:
  "neg (number_of (Numeral.pred v)::int) = (number_of v = (0::nat))"
apply (subgoal_tac "neg (number_of (Numeral.pred v)) = (number_of v < Suc 0) ")
apply (simp only: less_Suc_eq_le le_0_eq)
apply (subst less_number_of_Suc, simp)
done

text{*No longer required as a simprule because of the @{text inverse_fold}
   simproc*}
lemma Suc_diff_number_of:
     "neg (number_of (uminus v)::int) ==>
      Suc m - (number_of v) = m - (number_of (Numeral.pred v))"
apply (subst Suc_diff_eq_diff_pred)
apply simp
apply (simp del: nat_numeral_1_eq_1)
apply (auto simp only: diff_nat_number_of less_0_number_of [symmetric]
                        neg_number_of_pred_iff_0)
done

lemma diff_Suc_eq_diff_pred: "m - Suc n = (m - 1) - n"
by (simp add: numerals split add: nat_diff_split)


subsubsection{*For @{term nat_case} and @{term nat_rec}*}

lemma nat_case_number_of [simp]:
     "nat_case a f (number_of v) =
        (let pv = number_of (Numeral.pred v) in
         if neg pv then a else f (nat pv))"
by (simp split add: nat.split add: Let_def neg_number_of_pred_iff_0)

lemma nat_case_add_eq_if [simp]:
     "nat_case a f ((number_of v) + n) =
       (let pv = number_of (Numeral.pred v) in
         if neg pv then nat_case a f n else f (nat pv + n))"
apply (subst add_eq_if)
apply (simp split add: nat.split
            del: nat_numeral_1_eq_1
            add: numeral_1_eq_Suc_0 [symmetric] Let_def
                 neg_imp_number_of_eq_0 neg_number_of_pred_iff_0)
done

lemma nat_rec_number_of [simp]:
     "nat_rec a f (number_of v) =
        (let pv = number_of (Numeral.pred v) in
         if neg pv then a else f (nat pv) (nat_rec a f (nat pv)))"
apply (case_tac " (number_of v) ::nat")
apply (simp_all (no_asm_simp) add: Let_def neg_number_of_pred_iff_0)
apply (simp split add: split_if_asm)
done

lemma nat_rec_add_eq_if [simp]:
     "nat_rec a f (number_of v + n) =
        (let pv = number_of (Numeral.pred v) in
         if neg pv then nat_rec a f n
                   else f (nat pv + n) (nat_rec a f (nat pv + n)))"
apply (subst add_eq_if)
apply (simp split add: nat.split
            del: nat_numeral_1_eq_1
            add: numeral_1_eq_Suc_0 [symmetric] Let_def neg_imp_number_of_eq_0
                 neg_number_of_pred_iff_0)
done


subsubsection{*Various Other Lemmas*}

text {*Evens and Odds, for Mutilated Chess Board*}

text{*Lemmas for specialist use, NOT as default simprules*}
lemma nat_mult_2: "2 * z = (z+z::nat)"
proof -
  have "2*z = (1 + 1)*z" by simp
  also have "... = z+z" by (simp add: left_distrib)
  finally show ?thesis .
qed

lemma nat_mult_2_right: "z * 2 = (z+z::nat)"
by (subst mult_commute, rule nat_mult_2)

text{*Case analysis on @{term "n<2"}*}
lemma less_2_cases: "(n::nat) < 2 ==> n = 0 | n = Suc 0"
by arith

lemma div2_Suc_Suc [simp]: "Suc(Suc m) div 2 = Suc (m div 2)"
by arith

lemma add_self_div_2 [simp]: "(m + m) div 2 = (m::nat)"
by (simp add: nat_mult_2 [symmetric])

lemma mod2_Suc_Suc [simp]: "Suc(Suc(m)) mod 2 = m mod 2"
apply (subgoal_tac "m mod 2 < 2")
apply (erule less_2_cases [THEN disjE])
apply (simp_all (no_asm_simp) add: Let_def mod_Suc nat_1)
done

lemma mod2_gr_0 [simp]: "!!m::nat. (0 < m mod 2) = (m mod 2 = 1)"
apply (subgoal_tac "m mod 2 < 2")
apply (force simp del: mod_less_divisor, simp)
done

text{*Removal of Small Numerals: 0, 1 and (in additive positions) 2*}

lemma add_2_eq_Suc [simp]: "2 + n = Suc (Suc n)"
by simp

lemma add_2_eq_Suc' [simp]: "n + 2 = Suc (Suc n)"
by simp

text{*Can be used to eliminate long strings of Sucs, but not by default*}
lemma Suc3_eq_add_3: "Suc (Suc (Suc n)) = 3 + n"
by simp


text{*These lemmas collapse some needless occurrences of Suc:
    at least three Sucs, since two and fewer are rewritten back to Suc again!
    We already have some rules to simplify operands smaller than 3.*}

lemma div_Suc_eq_div_add3 [simp]: "m div (Suc (Suc (Suc n))) = m div (3+n)"
by (simp add: Suc3_eq_add_3)

lemma mod_Suc_eq_mod_add3 [simp]: "m mod (Suc (Suc (Suc n))) = m mod (3+n)"
by (simp add: Suc3_eq_add_3)

lemma Suc_div_eq_add3_div: "(Suc (Suc (Suc m))) div n = (3+m) div n"
by (simp add: Suc3_eq_add_3)

lemma Suc_mod_eq_add3_mod: "(Suc (Suc (Suc m))) mod n = (3+m) mod n"
by (simp add: Suc3_eq_add_3)

lemmas Suc_div_eq_add3_div_number_of =
    Suc_div_eq_add3_div [of _ "number_of v", standard]
declare Suc_div_eq_add3_div_number_of [simp]

lemmas Suc_mod_eq_add3_mod_number_of =
    Suc_mod_eq_add3_mod [of _ "number_of v", standard]
declare Suc_mod_eq_add3_mod_number_of [simp]


subsubsection{*Special Simplification for Constants*}

text{*These belong here, late in the development of HOL, to prevent their
interfering with proofs of abstract properties of instances of the function
@{term number_of}*}

text{*These distributive laws move literals inside sums and differences.*}
lemmas left_distrib_number_of = left_distrib [of _ _ "number_of v", standard]
declare left_distrib_number_of [simp]

lemmas right_distrib_number_of = right_distrib [of "number_of v", standard]
declare right_distrib_number_of [simp]


lemmas left_diff_distrib_number_of =
    left_diff_distrib [of _ _ "number_of v", standard]
declare left_diff_distrib_number_of [simp]

lemmas right_diff_distrib_number_of =
    right_diff_distrib [of "number_of v", standard]
declare right_diff_distrib_number_of [simp]


text{*These are actually for fields, like real: but where else to put them?*}
lemmas zero_less_divide_iff_number_of =
    zero_less_divide_iff [of "number_of w", standard]
declare zero_less_divide_iff_number_of [simp]

lemmas divide_less_0_iff_number_of =
    divide_less_0_iff [of "number_of w", standard]
declare divide_less_0_iff_number_of [simp]

lemmas zero_le_divide_iff_number_of =
    zero_le_divide_iff [of "number_of w", standard]
declare zero_le_divide_iff_number_of [simp]

lemmas divide_le_0_iff_number_of =
    divide_le_0_iff [of "number_of w", standard]
declare divide_le_0_iff_number_of [simp]


(****
IF times_divide_eq_right and times_divide_eq_left are removed as simprules,
then these special-case declarations may be useful.

text{*These simprules move numerals into numerators and denominators.*}
lemma times_recip_eq_right [simp]: "a * (1/c) = a / (c::'a::field)"
by (simp add: times_divide_eq)

lemma times_recip_eq_left [simp]: "(1/c) * a = a / (c::'a::field)"
by (simp add: times_divide_eq)

lemmas times_divide_eq_right_number_of =
    times_divide_eq_right [of "number_of w", standard]
declare times_divide_eq_right_number_of [simp]

lemmas times_divide_eq_right_number_of =
    times_divide_eq_right [of _ _ "number_of w", standard]
declare times_divide_eq_right_number_of [simp]

lemmas times_divide_eq_left_number_of =
    times_divide_eq_left [of _ "number_of w", standard]
declare times_divide_eq_left_number_of [simp]

lemmas times_divide_eq_left_number_of =
    times_divide_eq_left [of _ _ "number_of w", standard]
declare times_divide_eq_left_number_of [simp]

****)

text {*Replaces @{text "inverse #nn"} by @{text "1/#nn"}.  It looks
  strange, but then other simprocs simplify the quotient.*}

lemmas inverse_eq_divide_number_of =
    inverse_eq_divide [of "number_of w", standard]
declare inverse_eq_divide_number_of [simp]


text {*These laws simplify inequalities, moving unary minus from a term
into the literal.*}
lemmas less_minus_iff_number_of =
    less_minus_iff [of "number_of v", standard]
declare less_minus_iff_number_of [simp]

lemmas le_minus_iff_number_of =
    le_minus_iff [of "number_of v", standard]
declare le_minus_iff_number_of [simp]

lemmas equation_minus_iff_number_of =
    equation_minus_iff [of "number_of v", standard]
declare equation_minus_iff_number_of [simp]


lemmas minus_less_iff_number_of =
    minus_less_iff [of _ "number_of v", standard]
declare minus_less_iff_number_of [simp]

lemmas minus_le_iff_number_of =
    minus_le_iff [of _ "number_of v", standard]
declare minus_le_iff_number_of [simp]

lemmas minus_equation_iff_number_of =
    minus_equation_iff [of _ "number_of v", standard]
declare minus_equation_iff_number_of [simp]


text{*To Simplify Inequalities Where One Side is the Constant 1*}

lemma less_minus_iff_1 [simp]:
  fixes b::"'b::{ordered_idom,number_ring}"
  shows "(1 < - b) = (b < -1)"
by auto

lemma le_minus_iff_1 [simp]:
  fixes b::"'b::{ordered_idom,number_ring}"
  shows "(1 \<le> - b) = (b \<le> -1)"
by auto

lemma equation_minus_iff_1 [simp]:
  fixes b::"'b::number_ring"
  shows "(1 = - b) = (b = -1)"
by (subst equation_minus_iff, auto)

lemma minus_less_iff_1 [simp]:
  fixes a::"'b::{ordered_idom,number_ring}"
  shows "(- a < 1) = (-1 < a)"
by auto

lemma minus_le_iff_1 [simp]:
  fixes a::"'b::{ordered_idom,number_ring}"
  shows "(- a \<le> 1) = (-1 \<le> a)"
by auto

lemma minus_equation_iff_1 [simp]:
  fixes a::"'b::number_ring"
  shows "(- a = 1) = (a = -1)"
by (subst minus_equation_iff, auto)


text {*Cancellation of constant factors in comparisons (@{text "<"} and @{text "\<le>"}) *}

lemmas mult_less_cancel_left_number_of =
    mult_less_cancel_left [of "number_of v", standard]
declare mult_less_cancel_left_number_of [simp]

lemmas mult_less_cancel_right_number_of =
    mult_less_cancel_right [of _ "number_of v", standard]
declare mult_less_cancel_right_number_of [simp]

lemmas mult_le_cancel_left_number_of =
    mult_le_cancel_left [of "number_of v", standard]
declare mult_le_cancel_left_number_of [simp]

lemmas mult_le_cancel_right_number_of =
    mult_le_cancel_right [of _ "number_of v", standard]
declare mult_le_cancel_right_number_of [simp]


text {*Multiplying out constant divisors in comparisons (@{text "<"}, @{text "\<le>"} and @{text "="}) *}

lemmas le_divide_eq_number_of = le_divide_eq [of _ _ "number_of w", standard]
declare le_divide_eq_number_of [simp]

lemmas divide_le_eq_number_of = divide_le_eq [of _ "number_of w", standard]
declare divide_le_eq_number_of [simp]

lemmas less_divide_eq_number_of = less_divide_eq [of _ _ "number_of w", standard]
declare less_divide_eq_number_of [simp]

lemmas divide_less_eq_number_of = divide_less_eq [of _ "number_of w", standard]
declare divide_less_eq_number_of [simp]

lemmas eq_divide_eq_number_of = eq_divide_eq [of _ _ "number_of w", standard]
declare eq_divide_eq_number_of [simp]

lemmas divide_eq_eq_number_of = divide_eq_eq [of _ "number_of w", standard]
declare divide_eq_eq_number_of [simp]



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

lemmas half_gt_zero = half_gt_zero_iff [THEN iffD2, standard]
declare half_gt_zero [simp]

(* The following lemma should appear in Divides.thy, but there the proof
   doesn't work. *)

lemma nat_dvd_not_less:
  "[| 0 < m; m < n |] ==> \<not> n dvd (m::nat)"
  by (unfold dvd_def) auto

ML {*
val divide_minus1 = @{thm divide_minus1};
val minus1_divide = @{thm minus1_divide};
*}


subsection{* Groebner Bases for fields *}

interpretation class_fieldgb:
  fieldgb["op +" "op *" "op ^" "0::'a::{field,recpower,number_ring}" "1" "op -" "uminus" "op /" "inverse"] apply (unfold_locales) by (simp_all add: divide_inverse)

lemma divide_Numeral1: "(x::'a::{field,number_ring}) / Numeral1 = x" by simp
lemma divide_Numeral0: "(x::'a::{field,number_ring, division_by_zero}) / Numeral0 = 0"
  by simp
lemma mult_frac_frac: "((x::'a::{field,division_by_zero}) / y) * (z / w) = (x*z) / (y*w)"
  by simp
lemma mult_frac_num: "((x::'a::{field, division_by_zero}) / y) * z  = (x*z) / y"
  by simp
lemma mult_num_frac: "((x::'a::{field, division_by_zero}) / y) * z  = (x*z) / y"
  by simp

lemma Numeral1_eq1_nat: "(1::nat) = Numeral1" by simp

lemma add_frac_num: "y\<noteq> 0 \<Longrightarrow> (x::'a::{field, division_by_zero}) / y + z = (x + z*y) / y"
  by (simp add: add_divide_distrib)
lemma add_num_frac: "y\<noteq> 0 \<Longrightarrow> z + (x::'a::{field, division_by_zero}) / y = (x + z*y) / y"
  by (simp add: add_divide_distrib)

declaration{*
let
 val zr = @{cpat "0"}
 val zT = ctyp_of_term zr
 val geq = @{cpat "op ="}
 val eqT = Thm.dest_ctyp (ctyp_of_term geq) |> hd
 val add_frac_eq = mk_meta_eq @{thm "add_frac_eq"}
 val add_frac_num = mk_meta_eq @{thm "add_frac_num"}
 val add_num_frac = mk_meta_eq @{thm "add_num_frac"}

 fun prove_nz ctxt =
  let val ss = local_simpset_of ctxt
  in fn T => fn t =>
    let
      val z = instantiate_cterm ([(zT,T)],[]) zr
      val eq = instantiate_cterm ([(eqT,T)],[]) geq
      val th = Simplifier.rewrite (ss addsimps simp_thms)
           (Thm.capply @{cterm "Trueprop"} (Thm.capply @{cterm "Not"}
                  (Thm.capply (Thm.capply eq t) z)))
    in equal_elim (symmetric th) TrueI
    end
  end

 fun proc ctxt phi ss ct =
  let
    val ((x,y),(w,z)) =
         (Thm.dest_binop #> (fn (a,b) => (Thm.dest_binop a, Thm.dest_binop b))) ct
    val _ = map (HOLogic.dest_number o term_of) [x,y,z,w]
    val T = ctyp_of_term x
    val [y_nz, z_nz] = map (prove_nz ctxt T) [y, z]
    val th = instantiate' [SOME T] (map SOME [y,z,x,w]) add_frac_eq
  in SOME (implies_elim (implies_elim th y_nz) z_nz)
  end
  handle CTERM _ => NONE | TERM _ => NONE | THM _ => NONE

 fun proc2 ctxt phi ss ct =
  let
    val (l,r) = Thm.dest_binop ct
    val T = ctyp_of_term l
  in (case (term_of l, term_of r) of
      (Const(@{const_name "HOL.divide"},_)$_$_, _) =>
        let val (x,y) = Thm.dest_binop l val z = r
            val _ = map (HOLogic.dest_number o term_of) [x,y,z]
            val ynz = prove_nz ctxt T y
        in SOME (implies_elim (instantiate' [SOME T] (map SOME [y,x,z]) add_frac_num) ynz)
        end
     | (_, Const (@{const_name "HOL.divide"},_)$_$_) =>
        let val (x,y) = Thm.dest_binop r val z = l
            val _ = map (HOLogic.dest_number o term_of) [x,y,z]
            val ynz = prove_nz ctxt T y
        in SOME (implies_elim (instantiate' [SOME T] (map SOME [y,z,x]) add_num_frac) ynz)
        end
     | _ => NONE)
  end
  handle CTERM _ => NONE | TERM _ => NONE | THM _ => NONE

 fun is_number (Const(@{const_name "HOL.divide"},_)$a$b) = is_number a andalso is_number b
   | is_number t = can HOLogic.dest_number t

 val is_number = is_number o term_of

 fun proc3 phi ss ct =
  (case term_of ct of
    Const(@{const_name "Orderings.less"},_)$(Const(@{const_name "HOL.divide"},_)$_$_)$_ =>
      let
        val ((a,b),c) = Thm.dest_binop ct |>> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = ctyp_of_term c
        val th = instantiate' [SOME T] (map SOME [a,b,c]) @{thm "divide_less_eq"}
      in SOME (mk_meta_eq th) end
  | Const(@{const_name "Orderings.less_eq"},_)$(Const(@{const_name "HOL.divide"},_)$_$_)$_ =>
      let
        val ((a,b),c) = Thm.dest_binop ct |>> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = ctyp_of_term c
        val th = instantiate' [SOME T] (map SOME [a,b,c]) @{thm "divide_le_eq"}
      in SOME (mk_meta_eq th) end
  | Const("op =",_)$(Const(@{const_name "HOL.divide"},_)$_$_)$_ =>
      let
        val ((a,b),c) = Thm.dest_binop ct |>> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = ctyp_of_term c
        val th = instantiate' [SOME T] (map SOME [a,b,c]) @{thm "divide_eq_eq"}
      in SOME (mk_meta_eq th) end
  | Const(@{const_name "Orderings.less"},_)$_$(Const(@{const_name "HOL.divide"},_)$_$_) =>
    let
      val (a,(b,c)) = Thm.dest_binop ct ||> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = ctyp_of_term c
        val th = instantiate' [SOME T] (map SOME [a,b,c]) @{thm "less_divide_eq"}
      in SOME (mk_meta_eq th) end
  | Const(@{const_name "Orderings.less_eq"},_)$_$(Const(@{const_name "HOL.divide"},_)$_$_) =>
    let
      val (a,(b,c)) = Thm.dest_binop ct ||> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = ctyp_of_term c
        val th = instantiate' [SOME T] (map SOME [a,b,c]) @{thm "le_divide_eq"}
      in SOME (mk_meta_eq th) end
  | Const("op =",_)$_$(Const(@{const_name "HOL.divide"},_)$_$_) =>
    let
      val (a,(b,c)) = Thm.dest_binop ct ||> Thm.dest_binop
        val _ = map is_number [a,b,c]
        val T = ctyp_of_term c
        val th = instantiate' [SOME T] (map SOME [a,b,c]) @{thm "eq_divide_eq"}
      in SOME (mk_meta_eq th) end
  | _ => NONE)
  handle TERM _ => NONE | CTERM _ => NONE | THM _ => NONE

fun add_frac_frac_simproc ctxt =
       make_simproc {lhss = [@{cpat "(?x::?'a::field)/?y + (?w::?'a::field)/?z"}],
                     name = "add_frac_frac_simproc",
                     proc = proc ctxt, identifier = []}

fun add_frac_num_simproc ctxt =
       make_simproc {lhss = [@{cpat "(?x::?'a::field)/?y + ?z"}, @{cpat "?z + (?x::?'a::field)/?y"}],
                     name = "add_frac_num_simproc",
                     proc = proc2 ctxt, identifier = []}

val ord_frac_simproc =
  make_simproc
    {lhss = [@{cpat "(?a::(?'a::{field, ord}))/?b < ?c"},
             @{cpat "(?a::(?'a::{field, ord}))/?b \<le> ?c"},
             @{cpat "?c < (?a::(?'a::{field, ord}))/?b"},
             @{cpat "?c \<le> (?a::(?'a::{field, ord}))/?b"},
             @{cpat "?c = ((?a::(?'a::{field, ord}))/?b)"},
             @{cpat "((?a::(?'a::{field, ord}))/ ?b) = ?c"}],
             name = "ord_frac_simproc", proc = proc3, identifier = []}

val nat_arith = map thm ["add_nat_number_of", "diff_nat_number_of",
               "mult_nat_number_of", "eq_nat_number_of", "less_nat_number_of"]

val comp_arith = (map thm ["Let_def", "if_False", "if_True", "add_0",
                 "add_Suc", "add_number_of_left", "mult_number_of_left",
                 "Suc_eq_add_numeral_1"])@
                 (map (fn s => thm s RS sym) ["numeral_1_eq_1", "numeral_0_eq_0"])
                 @ arith_simps@ nat_arith @ rel_simps
val ths = [@{thm "mult_numeral_1"}, @{thm "mult_numeral_1_right"},
           @{thm "divide_Numeral1"},
           @{thm "Ring_and_Field.divide_zero"}, @{thm "divide_Numeral0"},
           @{thm "divide_divide_eq_left"}, @{thm "mult_frac_frac"},
           @{thm "mult_num_frac"}, @{thm "mult_frac_num"},
           @{thm "mult_frac_frac"}, @{thm "times_divide_eq_right"},
           @{thm "times_divide_eq_left"}, @{thm "divide_divide_eq_right"},
           @{thm "diff_def"}, @{thm "minus_divide_left"},
           @{thm "Numeral1_eq1_nat"}, @{thm "add_divide_distrib"} RS sym]

local
open Conv
in
fun comp_conv ctxt = (Simplifier.rewrite
(HOL_basic_ss addsimps @{thms "Groebner_Basis.comp_arith"}
              addsimps ths addsimps comp_arith addsimps simp_thms
              addsimprocs field_cancel_numeral_factors
               addsimprocs [add_frac_frac_simproc ctxt, add_frac_num_simproc ctxt,
                            ord_frac_simproc]
                addcongs [@{thm "if_weak_cong"}]))
then_conv (Simplifier.rewrite (HOL_basic_ss addsimps
  [@{thm numeral_1_eq_1},@{thm numeral_0_eq_0}] @ @{thms numerals(1-2)}))
end

fun numeral_is_const ct =
  case term_of ct of
   Const (@{const_name "HOL.divide"},_) $ a $ b =>
     numeral_is_const (Thm.dest_arg1 ct) andalso numeral_is_const (Thm.dest_arg ct)
 | Const (@{const_name "HOL.uminus"},_)$t => numeral_is_const (Thm.dest_arg ct)
 | t => can HOLogic.dest_number t

fun dest_const ct = case term_of ct of
   Const (@{const_name "HOL.divide"},_) $ a $ b=>
    Rat.rat_of_quotient (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
 | t => Rat.rat_of_int (snd (HOLogic.dest_number t))

fun mk_const phi cT x =
 let val (a, b) = Rat.quotient_of_rat x
 in if b = 1 then Normalizer.mk_cnumber cT a
    else Thm.capply
         (Thm.capply (Drule.cterm_rule (instantiate' [SOME cT] []) @{cpat "op /"})
                     (Normalizer.mk_cnumber cT a))
         (Normalizer.mk_cnumber cT b)
  end

in
 NormalizerData.funs @{thm class_fieldgb.axioms}
   {is_const = K numeral_is_const,
    dest_const = K dest_const,
    mk_const = mk_const,
    conv = K comp_conv}
end

*}


subsection {* Ferrante and Rackoff algorithm over ordered fields *}

lemma neg_prod_lt:"(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x < 0) == (x > 0))"
proof-
  assume H: "c < 0"
  have "c*x < 0 = (0/c < x)" by (simp only: neg_divide_less_eq[OF H] ring_eq_simps)
  also have "\<dots> = (0 < x)" by simp
  finally show  "(c*x < 0) == (x > 0)" by simp
qed

lemma pos_prod_lt:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x < 0) == (x < 0))"
proof-
  assume H: "c > 0"
  hence "c*x < 0 = (0/c > x)" by (simp only: pos_less_divide_eq[OF H] ring_eq_simps)
  also have "\<dots> = (0 > x)" by simp
  finally show  "(c*x < 0) == (x < 0)" by simp
qed

lemma neg_prod_sum_lt: "(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x + t< 0) == (x > (- 1/c)*t))"
proof-
  assume H: "c < 0"
  have "c*x + t< 0 = (c*x < -t)" by (subst less_iff_diff_less_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c < x)" by (simp only: neg_divide_less_eq[OF H] ring_eq_simps)
  also have "\<dots> = ((- 1/c)*t < x)" by simp
  finally show  "(c*x + t < 0) == (x > (- 1/c)*t)" by simp
qed

lemma pos_prod_sum_lt:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x + t < 0) == (x < (- 1/c)*t))"
proof-
  assume H: "c > 0"
  have "c*x + t< 0 = (c*x < -t)"  by (subst less_iff_diff_less_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c > x)" by (simp only: pos_less_divide_eq[OF H] ring_eq_simps)
  also have "\<dots> = ((- 1/c)*t > x)" by simp
  finally show  "(c*x + t < 0) == (x < (- 1/c)*t)" by simp
qed

lemma sum_lt:"((x::'a::pordered_ab_group_add) + t < 0) == (x < - t)"
  using less_diff_eq[where a= x and b=t and c=0] by simp

lemma neg_prod_le:"(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x <= 0) == (x >= 0))"
proof-
  assume H: "c < 0"
  have "c*x <= 0 = (0/c <= x)" by (simp only: neg_divide_le_eq[OF H] ring_eq_simps)
  also have "\<dots> = (0 <= x)" by simp
  finally show  "(c*x <= 0) == (x >= 0)" by simp
qed

lemma pos_prod_le:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x <= 0) == (x <= 0))"
proof-
  assume H: "c > 0"
  hence "c*x <= 0 = (0/c >= x)" by (simp only: pos_le_divide_eq[OF H] ring_eq_simps)
  also have "\<dots> = (0 >= x)" by simp
  finally show  "(c*x <= 0) == (x <= 0)" by simp
qed

lemma neg_prod_sum_le: "(c\<Colon>'a\<Colon>ordered_field) < 0 \<Longrightarrow> ((c*x + t <= 0) == (x >= (- 1/c)*t))"
proof-
  assume H: "c < 0"
  have "c*x + t <= 0 = (c*x <= -t)"  by (subst le_iff_diff_le_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c <= x)" by (simp only: neg_divide_le_eq[OF H] ring_eq_simps)
  also have "\<dots> = ((- 1/c)*t <= x)" by simp
  finally show  "(c*x + t <= 0) == (x >= (- 1/c)*t)" by simp
qed

lemma pos_prod_sum_le:"(c\<Colon>'a\<Colon>ordered_field) > 0 \<Longrightarrow> ((c*x + t <= 0) == (x <= (- 1/c)*t))"
proof-
  assume H: "c > 0"
  have "c*x + t <= 0 = (c*x <= -t)" by (subst le_iff_diff_le_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (-t/c >= x)" by (simp only: pos_le_divide_eq[OF H] ring_eq_simps)
  also have "\<dots> = ((- 1/c)*t >= x)" by simp
  finally show  "(c*x + t <= 0) == (x <= (- 1/c)*t)" by simp
qed

lemma sum_le:"((x::'a::pordered_ab_group_add) + t <= 0) == (x <= - t)"
  using le_diff_eq[where a= x and b=t and c=0] by simp

lemma nz_prod_eq:"(c\<Colon>'a\<Colon>ordered_field) \<noteq> 0 \<Longrightarrow> ((c*x = 0) == (x = 0))" by simp
lemma nz_prod_sum_eq: "(c\<Colon>'a\<Colon>ordered_field) \<noteq> 0 \<Longrightarrow> ((c*x + t = 0) == (x = (- 1/c)*t))"
proof-
  assume H: "c \<noteq> 0"
  have "c*x + t = 0 = (c*x = -t)" by (subst eq_iff_diff_eq_0 [of "c*x" "-t"], simp)
  also have "\<dots> = (x = -t/c)" by (simp only: nonzero_eq_divide_eq[OF H] ring_eq_simps)
  finally show  "(c*x + t = 0) == (x = (- 1/c)*t)" by simp
qed
lemma sum_eq:"((x::'a::pordered_ab_group_add) + t = 0) == (x = - t)"
  using eq_diff_eq[where a= x and b=t and c=0] by simp


interpretation class_ordered_field_dense_linear_order: dense_linear_order
 ["op <=" "op <"
   "\<lambda> x y. 1/2 * ((x::'a::{ordered_field,recpower,number_ring}) + y)"]
proof (unfold_locales,
  simp_all only: ordered_field_no_ub ordered_field_no_lb,
    auto simp add: linorder_not_le)
  fix x y::'a assume lt: "x < y"
  from  less_half_sum[OF lt] show "x < (x + y) /2" by simp
next
  fix x y::'a assume lt: "x < y"
  from  gt_half_sum[OF lt] show "(x + y) /2 < y" by simp
qed

declaration{*
let
fun earlier [] x y = false
        | earlier (h::t) x y =
    if h aconvc y then false else if h aconvc x then true else earlier t x y;

fun dest_frac ct = case term_of ct of
   Const (@{const_name "HOL.divide"},_) $ a $ b=>
    Rat.rat_of_quotient (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
 | t => Rat.rat_of_int (snd (HOLogic.dest_number t))

fun mk_frac phi cT x =
 let val (a, b) = Rat.quotient_of_rat x
 in if b = 1 then Normalizer.mk_cnumber cT a
    else Thm.capply
         (Thm.capply (Drule.cterm_rule (instantiate' [SOME cT] []) @{cpat "op /"})
                     (Normalizer.mk_cnumber cT a))
         (Normalizer.mk_cnumber cT b)
 end

fun whatis x ct = case term_of ct of
  Const(@{const_name "HOL.plus"}, _)$(Const(@{const_name "HOL.times"},_)$_$y)$_ =>
     if y aconv term_of x then ("c*x+t",[(funpow 2 Thm.dest_arg1) ct, Thm.dest_arg ct])
     else ("Nox",[])
| Const(@{const_name "HOL.plus"}, _)$y$_ =>
     if y aconv term_of x then ("x+t",[Thm.dest_arg ct])
     else ("Nox",[])
| Const(@{const_name "HOL.times"}, _)$_$y =>
     if y aconv term_of x then ("c*x",[Thm.dest_arg1 ct])
     else ("Nox",[])
| t => if t aconv term_of x then ("x",[]) else ("Nox",[]);

fun xnormalize_conv ctxt [] ct = reflexive ct
| xnormalize_conv ctxt (vs as (x::_)) ct =
   case term_of ct of
   Const(@{const_name "Orderings.less"},_)$_$Const(@{const_name "HOL.zero"},_) =>
    (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val cr = dest_frac c
        val clt = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME (ctyp_of_term x)] (map SOME [c,x,t])
             (if neg then @{thm neg_prod_sum_lt} else @{thm pos_prod_sum_lt})) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = ctyp_of_term x
        val th = instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_lt"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val cr = dest_frac c
        val clt = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME (ctyp_of_term x)] (map SOME [c,x])
             (if neg then @{thm neg_prod_lt} else @{thm pos_prod_lt})) cth
        val rth = th
      in rth end
    | _ => reflexive ct)


|  Const(@{const_name "Orderings.less_eq"},_)$_$Const(@{const_name "HOL.zero"},_) =>
   (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val clt = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat "op <"}
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME T] (map SOME [c,x,t])
             (if neg then @{thm neg_prod_sum_le} else @{thm pos_prod_sum_le})) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = ctyp_of_term x
        val th = instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_le"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val clt = Drule.cterm_rule (instantiate' [SOME T] []) @{cpat "op <"}
        val cz = Thm.dest_arg ct
        val neg = cr </ Rat.zero
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
               (Thm.capply @{cterm "Trueprop"}
                  (if neg then Thm.capply (Thm.capply clt c) cz
                    else Thm.capply (Thm.capply clt cz) c))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim (instantiate' [SOME (ctyp_of_term x)] (map SOME [c,x])
             (if neg then @{thm neg_prod_le} else @{thm pos_prod_le})) cth
        val rth = th
      in rth end
    | _ => reflexive ct)

|  Const("op =",_)$_$Const(@{const_name "HOL.zero"},_) =>
   (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val ceq = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
            (Thm.capply @{cterm "Trueprop"}
             (Thm.capply @{cterm "Not"} (Thm.capply (Thm.capply ceq c) cz)))
        val cth = equal_elim (symmetric cthp) TrueI
        val th = implies_elim
                 (instantiate' [SOME T] (map SOME [c,x,t]) @{thm nz_prod_sum_eq}) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = ctyp_of_term x
        val th = instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_eq"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Normalizer.semiring_normalize_ord_conv ctxt (earlier vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val T = ctyp_of_term x
        val cr = dest_frac c
        val ceq = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val cthp = Simplifier.rewrite (local_simpset_of ctxt)
            (Thm.capply @{cterm "Trueprop"}
             (Thm.capply @{cterm "Not"} (Thm.capply (Thm.capply ceq c) cz)))
        val cth = equal_elim (symmetric cthp) TrueI
        val rth = implies_elim
                 (instantiate' [SOME T] (map SOME [c,x]) @{thm nz_prod_eq}) cth
      in rth end
    | _ => reflexive ct);

local
  val less_iff_diff_less_0 = mk_meta_eq @{thm "less_iff_diff_less_0"}
  val le_iff_diff_le_0 = mk_meta_eq @{thm "le_iff_diff_le_0"}
  val eq_iff_diff_eq_0 = mk_meta_eq @{thm "eq_iff_diff_eq_0"}
in
fun field_isolate_conv phi ctxt vs ct = case term_of ct of
  Const(@{const_name "Orderings.less"},_)$a$b =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = ctyp_of_term ca
       val th = instantiate' [SOME T] [SOME ca, SOME cb] less_iff_diff_less_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Normalizer.semiring_normalize_ord_conv @{context} (earlier vs)))) th
       val rth = transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end
| Const(@{const_name "Orderings.less_eq"},_)$a$b =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = ctyp_of_term ca
       val th = instantiate' [SOME T] [SOME ca, SOME cb] le_iff_diff_le_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Normalizer.semiring_normalize_ord_conv @{context} (earlier vs)))) th
       val rth = transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end

| Const("op =",_)$a$b =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = ctyp_of_term ca
       val th = instantiate' [SOME T] [SOME ca, SOME cb] eq_iff_diff_eq_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Normalizer.semiring_normalize_ord_conv @{context} (earlier vs)))) th
       val rth = transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end
| @{term "Not"} $(Const("op =",_)$a$b) => Conv.arg_conv (field_isolate_conv phi ctxt vs) ct
| _ => reflexive ct
end;

fun classfield_whatis phi =
 let
  fun h x t =
   case term_of t of
     Const("op =", _)$y$z => if term_of x aconv y then Ferrante_Rackoff_Data.Eq
                            else Ferrante_Rackoff_Data.Nox
   | @{term "Not"}$(Const("op =", _)$y$z) => if term_of x aconv y then Ferrante_Rackoff_Data.NEq
                            else Ferrante_Rackoff_Data.Nox
   | Const(@{const_name "Orderings.less"},_)$y$z =>
       if term_of x aconv y then Ferrante_Rackoff_Data.Lt
        else if term_of x aconv z then Ferrante_Rackoff_Data.Gt
        else Ferrante_Rackoff_Data.Nox
   | Const (@{const_name "Orderings.less_eq"},_)$y$z =>
         if term_of x aconv y then Ferrante_Rackoff_Data.Le
         else if term_of x aconv z then Ferrante_Rackoff_Data.Ge
         else Ferrante_Rackoff_Data.Nox
   | _ => Ferrante_Rackoff_Data.Nox
 in h end;
fun class_field_ss phi =
   HOL_basic_ss addsimps ([@{thm "linorder_not_less"}, @{thm "linorder_not_le"}])
   addsplits [@{thm "abs_split"},@{thm "split_max"}, @{thm "split_min"}]

in
Ferrante_Rackoff_Data.funs @{thm "class_ordered_field_dense_linear_order.ferrack_axiom"}
  {isolate_conv = field_isolate_conv, whatis = classfield_whatis, simpset = class_field_ss}
end
*}


subsection {* Decision Procedure for Presburger Arithmetic *}

setup CooperData.setup

subsection{* The @{text "-\<infinity>"} and @{text "+\<infinity>"} Properties *}

lemma minf:
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x<z. P x = P' x; \<exists>z.\<forall>x<z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x<z. (P x \<and> Q x) = (P' x \<and> Q' x)"
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x<z. P x = P' x; \<exists>z.\<forall>x<z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x<z. (P x \<or> Q x) = (P' x \<or> Q' x)"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x = t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<noteq> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x < t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<le> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x > t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<ge> t) = False"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,times})<z. (d dvd x + s) = (d dvd x + s)"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,times})<z. (\<not> d dvd x + s) = (\<not> d dvd x + s)"
  "\<exists>z.\<forall>x<z. F = F"
  by ((erule exE, erule exE,rule_tac x="min z za" in exI,simp)+, (rule_tac x="t" in exI,fastsimp)+) simp_all

lemma pinf:
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x>z. P x = P' x; \<exists>z.\<forall>x>z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x>z. (P x \<and> Q x) = (P' x \<and> Q' x)"
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x>z. P x = P' x; \<exists>z.\<forall>x>z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x>z. (P x \<or> Q x) = (P' x \<or> Q' x)"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x = t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<noteq> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x < t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<le> t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x > t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<ge> t) = True"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,times})>z. (d dvd x + s) = (d dvd x + s)"
  "\<exists>z.\<forall>(x::'a::{linorder,plus,times})>z. (\<not> d dvd x + s) = (\<not> d dvd x + s)"
  "\<exists>z.\<forall>x>z. F = F"
  by ((erule exE, erule exE,rule_tac x="max z za" in exI,simp)+,(rule_tac x="t" in exI,fastsimp)+) simp_all

lemma inf_period:
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<and> Q x) = (P (x - k*D) \<and> Q (x - k*D))"
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<or> Q x) = (P (x - k*D) \<or> Q (x - k*D))"
  "(d::'a::{comm_ring}) dvd D \<Longrightarrow> \<forall>x k. (d dvd x + t) = (d dvd (x - k*D) + t)"
  "(d::'a::{comm_ring}) dvd D \<Longrightarrow> \<forall>x k. (\<not>d dvd x + t) = (\<not>d dvd (x - k*D) + t)"
  "\<forall>x k. F = F"
by simp_all
  (clarsimp simp add: dvd_def, rule iffI, clarsimp,rule_tac x = "kb - ka*k" in exI,
    simp add: ring_eq_simps, clarsimp,rule_tac x = "kb + ka*k" in exI,simp add: ring_eq_simps)+

section{* The A and B sets *}
lemma bset:
  "\<lbrakk>\<forall>x.(\<forall>j \<in> {1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> P x \<longrightarrow> P(x - D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> Q x \<longrightarrow> Q(x - D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j) \<longrightarrow> (P x \<and> Q x) \<longrightarrow> (P(x - D) \<and> Q (x - D))"
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> P x \<longrightarrow> P(x - D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> Q x \<longrightarrow> Q(x - D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (P x \<or> Q x) \<longrightarrow> (P(x - D) \<or> Q (x - D))"
  "\<lbrakk>D>0; t - 1\<in> B\<rbrakk> \<Longrightarrow> (\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x = t) \<longrightarrow> (x - D = t))"
  "\<lbrakk>D>0 ; t \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x - D \<noteq> t))"
  "D>0 \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x < t) \<longrightarrow> (x - D < t))"
  "D>0 \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x - D \<le> t))"
  "\<lbrakk>D>0 ; t \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x > t) \<longrightarrow> (x - D > t))"
  "\<lbrakk>D>0 ; t - 1 \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x - D \<ge> t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x - D) + t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not> d dvd (x - D) + t))"
  "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j) \<longrightarrow> F \<longrightarrow> F"
proof (blast, blast)
  assume dp: "D > 0" and tB: "t - 1\<in> B"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x = t) \<longrightarrow> (x - D = t))" 
    apply (rule allI, rule impI,erule ballE[where x="1"],erule ballE[where x="t - 1"])
    using dp tB by simp_all
next
  assume dp: "D > 0" and tB: "t \<in> B"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x - D \<noteq> t))" 
    apply (rule allI, rule impI,erule ballE[where x="D"],erule ballE[where x="t"])
    using dp tB by simp_all
next
  assume dp: "D > 0" thus "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x < t) \<longrightarrow> (x - D < t))" by arith
next
  assume dp: "D > 0" thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x - D \<le> t)" by arith
next
  assume dp: "D > 0" and tB:"t \<in> B"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j" and g: "x > t" and ng: "\<not> (x - D) > t"
    hence "x -t \<le> D" and "1 \<le> x - t" by simp+
      hence "\<exists>j \<in> {1 .. D}. x - t = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = t + j" by (simp add: ring_eq_simps)
      with nob tB have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x > t) \<longrightarrow> (x - D > t)" by blast
next
  assume dp: "D > 0" and tB:"t - 1\<in> B"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j" and g: "x \<ge> t" and ng: "\<not> (x - D) \<ge> t"
    hence "x - (t - 1) \<le> D" and "1 \<le> x - (t - 1)" by simp+
      hence "\<exists>j \<in> {1 .. D}. x - (t - 1) = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = (t - 1) + j" by (simp add: ring_eq_simps)
      with nob tB have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x - D \<ge> t)" by blast
next
  assume d: "d dvd D"
  {fix x assume H: "d dvd x + t" with d have "d dvd (x - D) + t"
      by (clarsimp simp add: dvd_def,rule_tac x= "ka - k" in exI,simp add: ring_eq_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x - D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not>d dvd (x - D) + t"
      by (clarsimp simp add: dvd_def,erule_tac x= "ka + k" in allE,simp add: ring_eq_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x - D) + t)" by auto
qed blast

lemma aset:
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> P x \<longrightarrow> P(x + D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> Q x \<longrightarrow> Q(x + D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j) \<longrightarrow> (P x \<and> Q x) \<longrightarrow> (P(x + D) \<and> Q (x + D))"
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> P x \<longrightarrow> P(x + D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> Q x \<longrightarrow> Q(x + D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (P x \<or> Q x) \<longrightarrow> (P(x + D) \<or> Q (x + D))"
  "\<lbrakk>D>0; t + 1\<in> A\<rbrakk> \<Longrightarrow> (\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x = t) \<longrightarrow> (x + D = t))"
  "\<lbrakk>D>0 ; t \<in> A\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x + D \<noteq> t))"
  "\<lbrakk>D>0; t\<in> A\<rbrakk> \<Longrightarrow>(\<forall>(x::int). (\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x < t) \<longrightarrow> (x + D < t))"
  "\<lbrakk>D>0; t + 1 \<in> A\<rbrakk> \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x + D \<le> t))"
  "D>0 \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x > t) \<longrightarrow> (x + D > t))"
  "D>0 \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x + D \<ge> t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not> d dvd (x + D) + t))"
  "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j) \<longrightarrow> F \<longrightarrow> F"
proof (blast, blast)
  assume dp: "D > 0" and tA: "t + 1 \<in> A"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x = t) \<longrightarrow> (x + D = t))" 
    apply (rule allI, rule impI,erule ballE[where x="1"],erule ballE[where x="t + 1"])
    using dp tA by simp_all
next
  assume dp: "D > 0" and tA: "t \<in> A"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x + D \<noteq> t))" 
    apply (rule allI, rule impI,erule ballE[where x="D"],erule ballE[where x="t"])
    using dp tA by simp_all
next
  assume dp: "D > 0" thus "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x > t) \<longrightarrow> (x + D > t))" by arith
next
  assume dp: "D > 0" thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x + D \<ge> t)" by arith
next
  assume dp: "D > 0" and tA:"t \<in> A"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j" and g: "x < t" and ng: "\<not> (x + D) < t"
    hence "t - x \<le> D" and "1 \<le> t - x" by simp+
      hence "\<exists>j \<in> {1 .. D}. t - x = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = t - j" by (auto simp add: ring_eq_simps) 
      with nob tA have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x < t) \<longrightarrow> (x + D < t)" by blast
next
  assume dp: "D > 0" and tA:"t + 1\<in> A"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j" and g: "x \<le> t" and ng: "\<not> (x + D) \<le> t"
    hence "(t + 1) - x \<le> D" and "1 \<le> (t + 1) - x" by (simp_all add: ring_eq_simps)
      hence "\<exists>j \<in> {1 .. D}. (t + 1) - x = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = (t + 1) - j" by (auto simp add: ring_eq_simps)
      with nob tA have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x + D \<le> t)" by blast
next
  assume d: "d dvd D"
  {fix x assume H: "d dvd x + t" with d have "d dvd (x + D) + t"
      by (clarsimp simp add: dvd_def,rule_tac x= "ka + k" in exI,simp add: ring_eq_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not>d dvd (x + D) + t"
      by (clarsimp simp add: dvd_def,erule_tac x= "ka - k" in allE,simp add: ring_eq_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x + D) + t)" by auto
qed blast

subsection{* Cooper's Theorem @{text "-\<infinity>"} and @{text "+\<infinity>"} Version *}

subsubsection{* First some trivial facts about periodic sets or predicates *}
lemma periodic_finite_ex:
  assumes dpos: "(0::int) < d" and modd: "ALL x k. P x = P(x - k*d)"
  shows "(EX x. P x) = (EX j : {1..d}. P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x - (x div d)*d" by(simp add:zmod_zdiv_equality mult_ac eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by simp
  show ?RHS
  proof (cases)
    assume "x mod d = 0"
    hence "P 0" using P Pmod by simp
    moreover have "P 0 = P(0 - (-1)*d)" using modd by blast
    ultimately have "P d" by simp
    moreover have "d : {1..d}" using dpos by(simp add:atLeastAtMost_iff)
    ultimately show ?RHS ..
  next
    assume not0: "x mod d \<noteq> 0"
    have "P(x mod d)" using dpos P Pmod by(simp add:pos_mod_sign pos_mod_bound)
    moreover have "x mod d : {1..d}"
    proof -
      from dpos have "0 \<le> x mod d" by(rule pos_mod_sign)
      moreover from dpos have "x mod d < d" by(rule pos_mod_bound)
      ultimately show ?thesis using not0 by(simp add:atLeastAtMost_iff)
    qed
    ultimately show ?RHS ..
  qed
qed auto

subsubsection{* The @{text "-\<infinity>"} Version*}

lemma decr_lemma: "0 < (d::int) \<Longrightarrow> x - (abs(x-z)+1) * d < z"
by(induct rule: int_gr_induct,simp_all add:int_distrib)

lemma incr_lemma: "0 < (d::int) \<Longrightarrow> z < x + (abs(x-z)+1) * d"
by(induct rule: int_gr_induct, simp_all add:int_distrib)

theorem int_induct[case_names base step1 step2]:
  assumes 
  base: "P(k::int)" and step1: "\<And>i. \<lbrakk>k \<le> i; P i\<rbrakk> \<Longrightarrow> P(i+1)" and
  step2: "\<And>i. \<lbrakk>k \<ge> i; P i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
proof -
  have "i \<le> k \<or> i\<ge> k" by arith
  thus ?thesis using prems int_ge_induct[where P="P" and k="k" and i="i"] int_le_induct[where P="P" and k="k" and i="i"] by blast
qed

lemma decr_mult_lemma:
  assumes dpos: "(0::int) < d" and minus: "\<forall>x. P x \<longrightarrow> P(x - d)" and knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x - k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x - i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x - (i + 1) * d)" using minus[THEN spec, of "x - i * d"]
      by (simp add:int_distrib OrderedGroup.diff_diff_eq[symmetric])
    ultimately have "P x \<longrightarrow> P(x - (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma  minusinfinity:
  assumes dpos: "0 < d" and
    P1eqP1: "ALL x k. P1 x = P1(x - k*d)" and ePeqP1: "EX z::int. ALL x. x < z \<longrightarrow> (P x = P1 x)"
  shows "(EX x. P1 x) \<longrightarrow> (EX x. P x)"
proof
  assume eP1: "EX x. P1 x"
  then obtain x where P1: "P1 x" ..
  from ePeqP1 obtain z where P1eqP: "ALL x. x < z \<longrightarrow> (P x = P1 x)" ..
  let ?w = "x - (abs(x-z)+1) * d"
  from dpos have w: "?w < z" by(rule decr_lemma)
  have "P1 x = P1 ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "EX x. P x" ..
qed

lemma cpmi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x< z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> B. x \<noteq> b+j) --> P (x) --> P (x - D)"
  and pd: "\<forall> x k. P' x = P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists> j\<in> {1..D} . P' j) | (\<exists> j \<in> {1..D}.\<exists> b\<in> B. P (b+j)))" 
         (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using minusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>B. P (b + j))" and P: "P y"
     hence "~(EX (j::int) : {1..D}. EX (b::int) : B. y = b+j)" by auto
     with nb P  have "P (y - D)" by auto }
   hence "ALL x.~(EX (j::int) : {1..D}. EX (b::int) : B. P(b+j)) --> P (x) --> P (x - D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x - D)" by auto
   from p1 obtain z where z: "ALL x. x < z --> (P x = P' x)" by blast
   let ?y = "x - (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y < z" using decr_lemma[OF dp] by simp   
   from z[rule_format, OF yz] decr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

subsubsection {* The @{text "+\<infinity>"} Version*}

lemma  plusinfinity:
  assumes dpos: "(0::int) < d" and
    P1eqP1: "\<forall>x k. P' x = P'(x - k*d)" and ePeqP1: "\<exists> z. \<forall> x>z. P x = P' x"
  shows "(\<exists> x. P' x) \<longrightarrow> (\<exists> x. P x)"
proof
  assume eP1: "EX x. P' x"
  then obtain x where P1: "P' x" ..
  from ePeqP1 obtain z where P1eqP: "\<forall>x>z. P x = P' x" ..
  let ?w' = "x + (abs(x-z)+1) * d"
  let ?w = "x - (-(abs(x-z) + 1))*d"
  have ww'[simp]: "?w = ?w'" by (simp add: ring_eq_simps)
  from dpos have w: "?w > z" by(simp only: ww' incr_lemma)
  hence "P' x = P' ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "EX x. P x" ..
qed

lemma incr_mult_lemma:
  assumes dpos: "(0::int) < d" and plus: "ALL x::int. P x \<longrightarrow> P(x + d)" and knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x + k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x + i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x + (i + 1) * d)" using plus[THEN spec, of "x + i * d"]
      by (simp add:int_distrib zadd_ac)
    ultimately have "P x \<longrightarrow> P(x + (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma cppi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x> z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> A. x \<noteq> b - j) --> P (x) --> P (x + D)"
  and pd: "\<forall> x k. P' x= P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists> j\<in> {1..D} . P' j) | (\<exists> j \<in> {1..D}.\<exists> b\<in> A. P (b - j)))" (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using plusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>A. P (b - j))" and P: "P y"
     hence "~(EX (j::int) : {1..D}. EX (b::int) : A. y = b - j)" by auto
     with nb P  have "P (y + D)" by auto }
   hence "ALL x.~(EX (j::int) : {1..D}. EX (b::int) : A. P(b-j)) --> P (x) --> P (x + D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x + D)" by auto
   from p1 obtain z where z: "ALL x. x > z --> (P x = P' x)" by blast
   let ?y = "x + (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y > z" using incr_lemma[OF dp] by simp
   from z[rule_format, OF yz] incr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

lemma simp_from_to: "{i..j::int} = (if j < i then {} else insert i {i+1..j})"
apply(simp add:atLeastAtMost_def atLeast_def atMost_def)
apply(fastsimp)
done

theorem unity_coeff_ex: "(\<exists>(x::'a::{semiring_0}). P (l * x)) \<equiv> (\<exists>x. l dvd (x + 0) \<and> P x)"
  apply (rule eq_reflection[symmetric])
  apply (rule iffI)
  defer
  apply (erule exE)
  apply (rule_tac x = "l * x" in exI)
  apply (simp add: dvd_def)
  apply (rule_tac x="x" in exI, simp)
  apply (erule exE)
  apply (erule conjE)
  apply (erule dvdE)
  apply (rule_tac x = k in exI)
  apply simp
  done

lemma zdvd_mono: assumes not0: "(k::int) \<noteq> 0"
shows "((m::int) dvd t) \<equiv> (k*m dvd k*t)" 
  using not0 by (simp add: dvd_def)

lemma uminus_dvd_conv: "(d dvd (t::int)) \<equiv> (-d dvd t)" "(d dvd (t::int)) \<equiv> (d dvd -t)"
  by simp_all
text {* \bigskip Theorems for transforming predicates on nat to predicates on @{text int}*}
lemma all_nat: "(\<forall>x::nat. P x) = (\<forall>x::int. 0 <= x \<longrightarrow> P (nat x))"
  by (simp split add: split_nat)

lemma ex_nat: "(\<exists>x::nat. P x) = (\<exists>x::int. 0 <= x \<and> P (nat x))"
  apply (auto split add: split_nat)
  apply (rule_tac x="int x" in exI, simp)
  apply (rule_tac x = "nat x" in exI,erule_tac x = "nat x" in allE, simp)
  done

lemma zdiff_int_split: "P (int (x - y)) =
  ((y \<le> x \<longrightarrow> P (int x - int y)) \<and> (x < y \<longrightarrow> P 0))"
  by (case_tac "y \<le> x", simp_all add: zdiff_int)

lemma number_of1: "(0::int) <= number_of n \<Longrightarrow> (0::int) <= number_of (n BIT b)" by simp
lemma number_of2: "(0::int) <= Numeral0" by simp
lemma Suc_plus1: "Suc n = n + 1" by simp

text {*
  \medskip Specific instances of congruence rules, to prevent
  simplifier from looping. *}

theorem imp_le_cong: "(0 <= x \<Longrightarrow> P = P') \<Longrightarrow> (0 <= (x::int) \<longrightarrow> P) = (0 <= x \<longrightarrow> P')" by simp

theorem conj_le_cong: "(0 <= x \<Longrightarrow> P = P') \<Longrightarrow> (0 <= (x::int) \<and> P) = (0 <= x \<and> P')" 
  by (simp cong: conj_cong)
lemma int_eq_number_of_eq:
  "(((number_of v)::int) = (number_of w)) = iszero ((number_of (v + (uminus w)))::int)"
  by simp

lemma mod_eq0_dvd_iff[presburger]: "(m::nat) mod n = 0 \<longleftrightarrow> n dvd m"
unfolding dvd_eq_mod_eq_0[symmetric] ..

lemma zmod_eq0_zdvd_iff[presburger]: "(m::int) mod n = 0 \<longleftrightarrow> n dvd m"
unfolding zdvd_iff_zmod_eq_0[symmetric] ..
declare mod_1[presburger]
declare mod_0[presburger]
declare zmod_1[presburger]
declare zmod_zero[presburger]
declare zmod_self[presburger]
declare mod_self[presburger]
declare DIVISION_BY_ZERO_MOD[presburger]
declare nat_mod_div_trivial[presburger]
declare div_mod_equality2[presburger]
declare div_mod_equality[presburger]
declare mod_div_equality2[presburger]
declare mod_div_equality[presburger]
declare mod_mult_self1[presburger]
declare mod_mult_self2[presburger]
declare zdiv_zmod_equality2[presburger]
declare zdiv_zmod_equality[presburger]
declare mod2_Suc_Suc[presburger]
lemma [presburger]: "(a::int) div 0 = 0" and [presburger]: "a mod 0 = a"
using IntDiv.DIVISION_BY_ZERO by blast+

use "Tools/Presburger/cooper.ML"
oracle linzqe_oracle ("term") = Coopereif.cooper_oracle

use "Tools/Presburger/presburger.ML"

setup {* 
  arith_tactic_add 
    (mk_arith_tactic "presburger" (fn i => fn st =>
       (warning "Trying Presburger arithmetic ...";   
    Presburger.cooper_tac true [] [] ((ProofContext.init o theory_of_thm) st) i st)))
  (* FIXME!!!!!!! get the right context!!*)	
*}

method_setup presburger = {*
let
 fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()
 fun simple_keyword k = Scan.lift (Args.$$$ k) >> K ()
 val addN = "add"
 val delN = "del"
 val elimN = "elim"
 val any_keyword = keyword addN || keyword delN || simple_keyword elimN
 val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
in
  fn src => Method.syntax 
   ((Scan.optional (simple_keyword elimN >> K false) true) -- 
    (Scan.optional (keyword addN |-- thms) []) -- 
    (Scan.optional (keyword delN |-- thms) [])) src 
  #> (fn (((elim, add_ths), del_ths),ctxt) => 
         Method.SIMPLE_METHOD' (Presburger.cooper_tac elim add_ths del_ths ctxt))
end
*} "Cooper's algorithm for Presburger arithmetic"

lemma [presburger]: "m mod 2 = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod 2 = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod (Suc (Suc 0)) = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod (Suc (Suc 0)) = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger]: "m mod 2 = (1::int) \<longleftrightarrow> \<not> 2 dvd m " by presburger


subsection {* Code generator setup *}

text {*
  Presburger arithmetic is convenient to prove some
  of the following code lemmas on integer numerals:
*}

lemma eq_Pls_Pls:
  "Numeral.Pls = Numeral.Pls \<longleftrightarrow> True" by presburger

lemma eq_Pls_Min:
  "Numeral.Pls = Numeral.Min \<longleftrightarrow> False"
  unfolding Pls_def Numeral.Min_def by presburger

lemma eq_Pls_Bit0:
  "Numeral.Pls = Numeral.Bit k bit.B0 \<longleftrightarrow> Numeral.Pls = k"
  unfolding Pls_def Bit_def bit.cases by presburger

lemma eq_Pls_Bit1:
  "Numeral.Pls = Numeral.Bit k bit.B1 \<longleftrightarrow> False"
  unfolding Pls_def Bit_def bit.cases by presburger

lemma eq_Min_Pls:
  "Numeral.Min = Numeral.Pls \<longleftrightarrow> False"
  unfolding Pls_def Numeral.Min_def by presburger

lemma eq_Min_Min:
  "Numeral.Min = Numeral.Min \<longleftrightarrow> True" by presburger

lemma eq_Min_Bit0:
  "Numeral.Min = Numeral.Bit k bit.B0 \<longleftrightarrow> False"
  unfolding Numeral.Min_def Bit_def bit.cases by presburger

lemma eq_Min_Bit1:
  "Numeral.Min = Numeral.Bit k bit.B1 \<longleftrightarrow> Numeral.Min = k"
  unfolding Numeral.Min_def Bit_def bit.cases by presburger

lemma eq_Bit0_Pls:
  "Numeral.Bit k bit.B0 = Numeral.Pls \<longleftrightarrow> Numeral.Pls = k"
  unfolding Pls_def Bit_def bit.cases by presburger

lemma eq_Bit1_Pls:
  "Numeral.Bit k bit.B1 = Numeral.Pls \<longleftrightarrow> False"
  unfolding Pls_def Bit_def bit.cases  by presburger

lemma eq_Bit0_Min:
  "Numeral.Bit k bit.B0 = Numeral.Min \<longleftrightarrow> False"
  unfolding Numeral.Min_def Bit_def bit.cases  by presburger

lemma eq_Bit1_Min:
  "(Numeral.Bit k bit.B1) = Numeral.Min \<longleftrightarrow> Numeral.Min = k"
  unfolding Numeral.Min_def Bit_def bit.cases  by presburger

lemma eq_Bit_Bit:
  "Numeral.Bit k1 v1 = Numeral.Bit k2 v2 \<longleftrightarrow>
    v1 = v2 \<and> k1 = k2" 
  unfolding Bit_def
  apply (cases v1)
  apply (cases v2)
  apply auto
  apply presburger
  apply (cases v2)
  apply auto
  apply presburger
  apply (cases v2)
  apply auto
  done

lemma eq_number_of:
  "(number_of k \<Colon> int) = number_of l \<longleftrightarrow> k = l" 
  unfolding number_of_is_id ..


lemma less_eq_Pls_Pls:
  "Numeral.Pls \<le> Numeral.Pls \<longleftrightarrow> True" by rule+

lemma less_eq_Pls_Min:
  "Numeral.Pls \<le> Numeral.Min \<longleftrightarrow> False"
  unfolding Pls_def Numeral.Min_def by presburger

lemma less_eq_Pls_Bit:
  "Numeral.Pls \<le> Numeral.Bit k v \<longleftrightarrow> Numeral.Pls \<le> k"
  unfolding Pls_def Bit_def by (cases v) auto

lemma less_eq_Min_Pls:
  "Numeral.Min \<le> Numeral.Pls \<longleftrightarrow> True"
  unfolding Pls_def Numeral.Min_def by presburger

lemma less_eq_Min_Min:
  "Numeral.Min \<le> Numeral.Min \<longleftrightarrow> True" by rule+

lemma less_eq_Min_Bit0:
  "Numeral.Min \<le> Numeral.Bit k bit.B0 \<longleftrightarrow> Numeral.Min < k"
  unfolding Numeral.Min_def Bit_def by auto

lemma less_eq_Min_Bit1:
  "Numeral.Min \<le> Numeral.Bit k bit.B1 \<longleftrightarrow> Numeral.Min \<le> k"
  unfolding Numeral.Min_def Bit_def by auto

lemma less_eq_Bit0_Pls:
  "Numeral.Bit k bit.B0 \<le> Numeral.Pls \<longleftrightarrow> k \<le> Numeral.Pls"
  unfolding Pls_def Bit_def by simp

lemma less_eq_Bit1_Pls:
  "Numeral.Bit k bit.B1 \<le> Numeral.Pls \<longleftrightarrow> k < Numeral.Pls"
  unfolding Pls_def Bit_def by auto

lemma less_eq_Bit_Min:
  "Numeral.Bit k v \<le> Numeral.Min \<longleftrightarrow> k \<le> Numeral.Min"
  unfolding Numeral.Min_def Bit_def by (cases v) auto

lemma less_eq_Bit0_Bit:
  "Numeral.Bit k1 bit.B0 \<le> Numeral.Bit k2 v \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit_def bit.cases by (cases v) auto

lemma less_eq_Bit_Bit1:
  "Numeral.Bit k1 v \<le> Numeral.Bit k2 bit.B1 \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit_def bit.cases by (cases v) auto

lemma less_eq_Bit1_Bit0:
  "Numeral.Bit k1 bit.B1 \<le> Numeral.Bit k2 bit.B0 \<longleftrightarrow> k1 < k2"
  unfolding Bit_def by (auto split: bit.split)

lemma less_eq_number_of:
  "(number_of k \<Colon> int) \<le> number_of l \<longleftrightarrow> k \<le> l"
  unfolding number_of_is_id ..


lemma less_Pls_Pls:
  "Numeral.Pls < Numeral.Pls \<longleftrightarrow> False" by simp 

lemma less_Pls_Min:
  "Numeral.Pls < Numeral.Min \<longleftrightarrow> False"
  unfolding Pls_def Numeral.Min_def  by presburger 

lemma less_Pls_Bit0:
  "Numeral.Pls < Numeral.Bit k bit.B0 \<longleftrightarrow> Numeral.Pls < k"
  unfolding Pls_def Bit_def by auto

lemma less_Pls_Bit1:
  "Numeral.Pls < Numeral.Bit k bit.B1 \<longleftrightarrow> Numeral.Pls \<le> k"
  unfolding Pls_def Bit_def by auto

lemma less_Min_Pls:
  "Numeral.Min < Numeral.Pls \<longleftrightarrow> True"
  unfolding Pls_def Numeral.Min_def by presburger 

lemma less_Min_Min:
  "Numeral.Min < Numeral.Min \<longleftrightarrow> False"  by simp

lemma less_Min_Bit:
  "Numeral.Min < Numeral.Bit k v \<longleftrightarrow> Numeral.Min < k"
  unfolding Numeral.Min_def Bit_def by (auto split: bit.split)

lemma less_Bit_Pls:
  "Numeral.Bit k v < Numeral.Pls \<longleftrightarrow> k < Numeral.Pls"
  unfolding Pls_def Bit_def by (auto split: bit.split)

lemma less_Bit0_Min:
  "Numeral.Bit k bit.B0 < Numeral.Min \<longleftrightarrow> k \<le> Numeral.Min"
  unfolding Numeral.Min_def Bit_def by auto

lemma less_Bit1_Min:
  "Numeral.Bit k bit.B1 < Numeral.Min \<longleftrightarrow> k < Numeral.Min"
  unfolding Numeral.Min_def Bit_def by auto

lemma less_Bit_Bit0:
  "Numeral.Bit k1 v < Numeral.Bit k2 bit.B0 \<longleftrightarrow> k1 < k2"
  unfolding Bit_def by (auto split: bit.split)

lemma less_Bit1_Bit:
  "Numeral.Bit k1 bit.B1 < Numeral.Bit k2 v \<longleftrightarrow> k1 < k2"
  unfolding Bit_def by (auto split: bit.split)

lemma less_Bit0_Bit1:
  "Numeral.Bit k1 bit.B0 < Numeral.Bit k2 bit.B1 \<longleftrightarrow> k1 \<le> k2"
  unfolding Bit_def bit.cases  by arith

lemma less_number_of:
  "(number_of k \<Colon> int) < number_of l \<longleftrightarrow> k < l"
  unfolding number_of_is_id ..

lemmas pred_succ_numeral_code [code func] =
  arith_simps(5-12)

lemmas plus_numeral_code [code func] =
  arith_simps(13-17)
  arith_simps(26-27)
  arith_extra_simps(1) [where 'a = int]

lemmas minus_numeral_code [code func] =
  arith_simps(18-21)
  arith_extra_simps(2) [where 'a = int]
  arith_extra_simps(5) [where 'a = int]

lemmas times_numeral_code [code func] =
  arith_simps(22-25)
  arith_extra_simps(4) [where 'a = int]

lemmas eq_numeral_code [code func] =
  eq_Pls_Pls eq_Pls_Min eq_Pls_Bit0 eq_Pls_Bit1
  eq_Min_Pls eq_Min_Min eq_Min_Bit0 eq_Min_Bit1
  eq_Bit0_Pls eq_Bit1_Pls eq_Bit0_Min eq_Bit1_Min eq_Bit_Bit
  eq_number_of

lemmas less_eq_numeral_code [code func] = less_eq_Pls_Pls less_eq_Pls_Min less_eq_Pls_Bit
  less_eq_Min_Pls less_eq_Min_Min less_eq_Min_Bit0 less_eq_Min_Bit1
  less_eq_Bit0_Pls less_eq_Bit1_Pls less_eq_Bit_Min less_eq_Bit0_Bit less_eq_Bit_Bit1 less_eq_Bit1_Bit0
  less_eq_number_of

lemmas less_numeral_code [code func] = less_Pls_Pls less_Pls_Min less_Pls_Bit0
  less_Pls_Bit1 less_Min_Pls less_Min_Min less_Min_Bit less_Bit_Pls
  less_Bit0_Min less_Bit1_Min less_Bit_Bit0 less_Bit1_Bit less_Bit0_Bit1
  less_number_of

end
