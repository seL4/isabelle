(*
  Title:     The algebraic hierarchy of rings
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* The algebraic hierarchy of rings as axiomatic classes *}

theory Ring = Group

section {* The Algebraic Hierarchy of Rings *}

subsection {* Basic Definitions *}

record 'a ring = "'a group" +
  zero :: 'a ("\<zero>\<index>")
  add :: "['a, 'a] => 'a" (infixl "\<oplus>\<index>" 65)
  a_inv :: "'a => 'a" ("\<ominus>\<index> _" [81] 80)

locale cring = abelian_monoid R +
  assumes a_abelian_group: "abelian_group (| carrier = carrier R,
      mult = add R, one = zero R, m_inv = a_inv R |)"
    and m_inv_def: "[| EX y. y \<in> carrier R & x \<otimes> y = \<one>; x \<in> carrier R |]
      ==> inv x = (THE y. y \<in> carrier R & x \<otimes> y = \<one>)"
    and l_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"

ML {*
  thm "cring.l_distr"
*}

(*
locale cring = struct R +
  assumes a_group: "abelian_group (| carrier = carrier R,
      mult = add R, one = zero R, m_inv = a_inv R |)"
    and m_monoid: "abelian_monoid (| carrier = carrier R - {zero R},
      mult = mult R, one = one R |)"
    and l_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"

locale field = struct R +
  assumes a_group: "abelian_group (| carrier = carrier R,
      mult = add R, one = zero R, m_inv = a_inv R |)"
    and m_group: "monoid (| carrier = carrier R - {zero R},
      mult = mult R, one = one R |)"
    and l_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
*)
(*
  a_assoc:      "(a + b) + c = a + (b + c)"
  l_zero:       "0 + a = a"
  l_neg:        "(-a) + a = 0"
  a_comm:       "a + b = b + a"

  m_assoc:      "(a * b) * c = a * (b * c)"
  l_one:        "1 * a = a"

  l_distr:      "(a + b) * c = a * c + b * c"

  m_comm:       "a * b = b * a"

  -- {* Definition of derived operations *}

  minus_def:    "a - b = a + (-b)"
  inverse_def:  "inverse a = (if a dvd 1 then THE x. a*x = 1 else 0)"
  divide_def:   "a / b = a * inverse b"
  power_def:    "a ^ n = nat_rec 1 (%u b. b * a) n"
*)
subsection {* Basic Facts *}

lemma (in cring) a_magma [simp, intro]:
  "magma (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  using a_abelian_group by (simp only: abelian_group_def)

lemma (in cring) a_l_one [simp, intro]:
  "l_one (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  using a_abelian_group by (simp only: abelian_group_def)

lemma (in cring) a_abelian_group_parts [simp, intro]:
  "semigroup_axioms (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  "group_axioms (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  "abelian_semigroup_axioms (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  using a_abelian_group by (simp_all only: abelian_group_def)

lemma (in cring) a_semigroup:
  "semigroup (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: semigroup_def)

lemma (in cring) a_group:
  "group (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: group_def)

lemma (in cring) a_abelian_semigroup:
  "abelian_semigroup (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: abelian_semigroup_def)

lemma (in cring) a_abelian_group:
  "abelian_group (| carrier = carrier R,
     mult = add R, one = zero R, m_inv = a_inv R |)"
  by (simp add: abelian_group_def)

lemma (in cring) a_assoc:
  "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
  ==> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  using semigroup.m_assoc [OF a_semigroup]
  by simp

lemma (in cring) l_zero:
  "x \<in> carrier R ==> \<zero> \<oplus> x = x"
  using l_one.l_one [OF a_l_one]
  by simp

lemma (in cring) l_neg:
  "x \<in> carrier R ==> (\<ominus> x) \<oplus> x = \<zero>"
  using group.l_inv [OF a_group]
  by simp

lemma (in cring) a_comm:
  "[| x \<in> carrier R; y \<in> carrier R |]
  ==> x \<oplus> y = y \<oplus> x"
  using abelian_semigroup.m_comm [OF a_abelian_semigroup]
  by simp




qed

  l_zero:       "0 + a = a"
  l_neg:        "(-a) + a = 0"
  a_comm:       "a + b = b + a"

  m_assoc:      "(a * b) * c = a * (b * c)"
  l_one:        "1 * a = a"

  l_distr:      "(a + b) * c = a * c + b * c"

  m_comm:       "a * b = b * a"
text {* Normaliser for Commutative Rings *}

use "order.ML"

method_setup ring =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (full_simp_tac ring_ss)) *}
  {* computes distributive normal form in rings *}

subsection {* Rings and the summation operator *}

(* Basic facts --- move to HOL!!! *)

lemma natsum_0 [simp]: "setsum f {..(0::nat)} = (f 0::'a::plus_ac0)"
by simp

lemma natsum_Suc [simp]:
  "setsum f {..Suc n} = (f (Suc n) + setsum f {..n}::'a::plus_ac0)"
by (simp add: atMost_Suc)

lemma natsum_Suc2:
  "setsum f {..Suc n} = (setsum (%i. f (Suc i)) {..n} + f 0::'a::plus_ac0)"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by (simp add: assoc) 
qed

lemma natsum_cong [cong]:
  "!!k. [| j = k; !!i::nat. i <= k ==> f i = (g i::'a::plus_ac0) |] ==>
        setsum f {..j} = setsum g {..k}"
by (induct j) auto

lemma natsum_zero [simp]: "setsum (%i. 0) {..n::nat} = (0::'a::plus_ac0)"
by (induct n) simp_all

lemma natsum_add [simp]:
  "!!f::nat=>'a::plus_ac0.
   setsum (%i. f i + g i) {..n::nat} = setsum f {..n} + setsum g {..n}"
by (induct n) (simp_all add: plus_ac0)

(* Facts specific to rings *)

instance ring < plus_ac0
proof
  fix x y z
  show "(x::'a::ring) + y = y + x" by (rule a_comm)
  show "((x::'a::ring) + y) + z = x + (y + z)" by (rule a_assoc)
  show "0 + (x::'a::ring) = x" by (rule l_zero)
qed

ML {*
  local
    val lhss = 
        [read_cterm (sign_of (the_context ()))
                    ("?t + ?u::'a::ring", TVar (("'z", 0), [])),
	 read_cterm (sign_of (the_context ()))
                    ("?t - ?u::'a::ring", TVar (("'z", 0), [])),
	 read_cterm (sign_of (the_context ()))
                    ("?t * ?u::'a::ring", TVar (("'z", 0), [])),
	 read_cterm (sign_of (the_context ()))
                    ("- ?t::'a::ring", TVar (("'z", 0), []))
	];
    fun proc sg _ t = 
      let val rew = Tactic.prove sg [] []
            (HOLogic.mk_Trueprop
              (HOLogic.mk_eq (t, Var (("x", Term.maxidx_of_term t + 1), fastype_of t))))
                (fn _ => simp_tac ring_ss 1)
            |> mk_meta_eq;
          val (t', u) = Logic.dest_equals (Thm.prop_of rew);
      in if t' aconv u 
        then None
        else Some rew 
    end;
  in
    val ring_simproc = mk_simproc "ring" lhss proc;
  end;
*}

ML_setup {* Addsimprocs [ring_simproc] *}

lemma natsum_ldistr:
  "!!a::'a::ring. setsum f {..n::nat} * a = setsum (%i. f i * a) {..n}"
by (induct n) simp_all

lemma natsum_rdistr:
  "!!a::'a::ring. a * setsum f {..n::nat} = setsum (%i. a * f i) {..n}"
by (induct n) simp_all

subsection {* Integral Domains *}

declare one_not_zero [simp]

lemma zero_not_one [simp]:
  "0 ~= (1::'a::domain)" 
by (rule not_sym) simp

lemma integral_iff: (* not by default a simp rule! *)
  "(a * b = (0::'a::domain)) = (a = 0 | b = 0)"
proof
  assume "a * b = 0" then show "a = 0 | b = 0" by (simp add: integral)
next
  assume "a = 0 | b = 0" then show "a * b = 0" by auto
qed

(*
lemma "(a::'a::ring) - (a - b) = b" apply simp
 simproc seems to fail on this example (fixed with new term order)
*)
(*
lemma bug: "(b::'a::ring) - (b - a) = a" by simp
   simproc for rings cannot prove "(a::'a::ring) - (a - b) = b" 
*)
lemma m_lcancel:
  assumes prem: "(a::'a::domain) ~= 0" shows conc: "(a * b = a * c) = (b = c)"
proof
  assume eq: "a * b = a * c"
  then have "a * (b - c) = 0" by simp
  then have "a = 0 | (b - c) = 0" by (simp only: integral_iff)
  with prem have "b - c = 0" by auto 
  then have "b = b - (b - c)" by simp 
  also have "b - (b - c) = c" by simp
  finally show "b = c" .
next
  assume "b = c" then show "a * b = a * c" by simp
qed

lemma m_rcancel:
  "(a::'a::domain) ~= 0 ==> (b * a = c * a) = (b = c)"
by (simp add: m_lcancel)

end
