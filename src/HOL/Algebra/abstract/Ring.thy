(*
  Title:     The algebraic hierarchy of rings as axiomatic classes
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* The algebraic hierarchy of rings as axiomatic classes *}

theory Ring = Main
files ("order.ML"):

section {* Constants *}

text {* Most constants are already declared by HOL. *}

consts
  assoc         :: "['a::times, 'a] => bool"              (infixl 50)
  irred         :: "'a::{zero, one, times} => bool"
  prime         :: "'a::{zero, one, times} => bool"

section {* Axioms *}

subsection {* Ring axioms *}

axclass ring < zero, one, plus, minus, times, inverse, power

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

defs
  assoc_def:    "a assoc b == a dvd b & b dvd a"
  irred_def:    "irred a == a ~= 0 & ~ a dvd 1
                          & (ALL d. d dvd a --> d dvd 1 | a dvd d)"
  prime_def:    "prime p == p ~= 0 & ~ p dvd 1
                          & (ALL a b. p dvd (a*b) --> p dvd a | p dvd b)"

subsection {* Integral domains *}

axclass
  "domain" < ring

  one_not_zero: "1 ~= 0"
  integral:     "a * b = 0 ==> a = 0 | b = 0"

subsection {* Factorial domains *}

axclass
  factorial < "domain"

(*
  Proper definition using divisor chain condition currently not supported.
  factorial_divisor:    "wf {(a, b). a dvd b & ~ (b dvd a)}"
*)
  factorial_divisor:	"True"
  factorial_prime:      "irred a ==> prime a"

subsection {* Euclidean domains *}

(*
axclass
  euclidean < "domain"

  euclidean_ax:  "b ~= 0 ==> Ex (% (q, r, e_size::('a::ringS)=>nat).
                   a = b * q + r & e_size r < e_size b)"

  Nothing has been proved about Euclidean domains, yet.
  Design question:
    Fix quo, rem and e_size as constants that are axiomatised with
    euclidean_ax?
    - advantage: more pragmatic and easier to use
    - disadvantage: for every type, one definition of quo and rem will
        be fixed, users may want to use differing ones;
        also, it seems not possible to prove that fields are euclidean
        domains, because that would require generic (type-independent)
        definitions of quo and rem.
*)

subsection {* Fields *}

axclass
  field < ring

  field_one_not_zero:    "1 ~= 0"
                (* Avoid a common superclass as the first thing we will
                   prove about fields is that they are domains. *)
  field_ax:        "a ~= 0 ==> a dvd 1"

section {* Basic facts *}

subsection {* Normaliser for rings *}

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
