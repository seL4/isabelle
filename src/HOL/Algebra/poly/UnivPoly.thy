(*
  Title:     Univariate Polynomials
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* Univariate Polynomials *}

theory UnivPoly = Abstract:

(* already proved in Finite_Set.thy

lemma setsum_cong:
  "[| A = B; !!i. i : B ==> f i = g i |] ==> setsum f A = setsum g B"
proof -
  assume prems: "A = B" "!!i. i : B ==> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. [| A = B; !!i. i : B ==> f i = g i |] ==>
      setsum f A = setsum g B"
    proof induct
      case empty thus ?case by simp
    next
      case insert thus ?case by simp
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by (simp add: setsum_def)
  qed
qed
*)

(* Instruct simplifier to simplify assumptions introduced by congs.
   This makes setsum_cong more convenient to use, because assumptions
   like i:{m..n} get simplified (to m <= i & i <= n). *)

ML_setup {* 

Addcongs [thm "setsum_cong"];
Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_full_simp_tac; thy)) *}

section {* Definition of type up *}

constdefs
  bound  :: "[nat, nat => 'a::zero] => bool"
  "bound n f == (ALL i. n < i --> f i = 0)"

lemma boundI [intro!]: "[| !! m. n < m ==> f m = 0 |] ==> bound n f"
proof (unfold bound_def)
qed fast

lemma boundE [elim?]: "[| bound n f; (!! m. n < m ==> f m = 0) ==> P |] ==> P"
proof (unfold bound_def)
qed fast

lemma boundD [dest]: "[| bound n f; n < m |] ==> f m = 0"
proof (unfold bound_def)
qed fast

lemma bound_below:
  assumes bound: "bound m f" and nonzero: "f n ~= 0" shows "n <= m"
proof (rule classical)
  assume "~ ?thesis"
  then have "m < n" by arith
  with bound have "f n = 0" ..
  with nonzero show ?thesis by contradiction
qed

typedef (UP)
  ('a) up = "{f :: nat => 'a::zero. EX n. bound n f}"
by (rule+)   (* Question: what does trace_rule show??? *)

section {* Constants *}

consts
  coeff  :: "['a up, nat] => ('a::zero)"
  monom  :: "['a::zero, nat] => 'a up"              ("(3_*X^/_)" [71, 71] 70)
  "*s"   :: "['a::{zero, times}, 'a up] => 'a up"   (infixl 70)

defs
  coeff_def: "coeff p n == Rep_UP p n"
  monom_def: "monom a n == Abs_UP (%i. if i=n then a else 0)"
  smult_def: "a *s p == Abs_UP (%i. a * Rep_UP p i)"

lemma coeff_bound_ex: "EX n. bound n (coeff p)"
proof -
  have "(%n. coeff p n) : UP" by (simp add: coeff_def Rep_UP)
  then obtain n where "bound n (coeff p)" by (unfold UP_def) fast
  then show ?thesis ..
qed
  
lemma bound_coeff_obtain:
  assumes prem: "(!!n. bound n (coeff p) ==> P)" shows "P"
proof -
  have "(%n. coeff p n) : UP" by (simp add: coeff_def Rep_UP)
  then obtain n where "bound n (coeff p)" by (unfold UP_def) fast
  with prem show P .
qed

text {* Ring operations *}

instance up :: (zero) zero ..
instance up :: (one) one ..
instance up :: (plus) plus ..
instance up :: (minus) minus ..
instance up :: (times) times ..
instance up :: (inverse) inverse ..
instance up :: (power) power ..

defs
  up_add_def:	"p + q == Abs_UP (%n. Rep_UP p n + Rep_UP q n)"
  up_mult_def:  "p * q == Abs_UP (%n::nat. setsum
		     (%i. Rep_UP p i * Rep_UP q (n-i)) {..n})"
  up_zero_def:  "0 == monom 0 0"
  up_one_def:   "1 == monom 1 0"
  up_uminus_def:"- p == (- 1) *s p"
                (* easier to use than "Abs_UP (%i. - Rep_UP p i)" *)
                (* note: - 1 is different from -1; latter is of class number *)

  up_minus_def:   "(a::'a::{plus, minus} up) - b == a + (-b)"
  up_inverse_def: "inverse (a::'a::{zero, one, times, inverse} up) == 
                     (if a dvd 1 then THE x. a*x = 1 else 0)"
  up_divide_def:  "(a::'a::{times, inverse} up) / b == a * inverse b"
  up_power_def:   "(a::'a::{one, times, power} up) ^ n ==
                     nat_rec 1 (%u b. b * a) n"

subsection {* Effect of operations on coefficients *}

lemma coeff_monom [simp]: "coeff (monom a m) n = (if m=n then a else 0)"
proof -
  have "(%n. if n = m then a else 0) : UP"
    using UP_def by force
  from this show ?thesis
    by (simp add: coeff_def monom_def Abs_UP_inverse Rep_UP)
qed

lemma coeff_zero [simp]: "coeff 0 n = 0"
proof (unfold up_zero_def)
qed simp

lemma coeff_one [simp]: "coeff 1 n = (if n=0 then 1 else 0)"
proof (unfold up_one_def)
qed simp

lemma coeff_smult [simp]: "coeff (a *s p) n = (a::'a::ring) * coeff p n"
proof -
  have "!!f. f : UP ==> (%n. a * f n) : UP"
    by (unfold UP_def) (force simp add: ring_simps)
      (* this force step is slow *)
  then show ?thesis
    by (simp add: coeff_def smult_def Abs_UP_inverse Rep_UP)
qed

lemma coeff_add [simp]: "coeff (p+q) n = (coeff p n + coeff q n::'a::ring)"
proof -
  {
    fix f g
    assume fup: "(f::nat=>'a::ring) : UP" and gup: "(g::nat=>'a::ring) : UP"
    have "(%i. f i + g i) : UP"
    proof -
      from fup obtain n where boundn: "bound n f"
	by (unfold UP_def) fast
      from gup obtain m where boundm: "bound m g"
	by (unfold UP_def) fast
      have "bound (max n m) (%i. (f i + g i))"
      proof
	fix i
	assume "max n m < i"
	with boundn and boundm show "f i + g i = 0"
          by (fastsimp simp add: ring_simps)
      qed
      then show "(%i. (f i + g i)) : UP"
	by (unfold UP_def) fast
    qed
  }
  then show ?thesis
    by (simp add: coeff_def up_add_def Abs_UP_inverse Rep_UP)
qed

lemma coeff_mult [simp]:
  "coeff (p * q) n = (setsum (%i. coeff p i * coeff q (n-i)) {..n}::'a::ring)"
proof -
  {
    fix f g
    assume fup: "(f::nat=>'a::ring) : UP" and gup: "(g::nat=>'a::ring) : UP"
    have "(%n. setsum (%i. f i * g (n-i)) {..n}) : UP"
    proof -
      from fup obtain n where "bound n f"
	by (unfold UP_def) fast
      from gup obtain m where "bound m g"
	by (unfold UP_def) fast
      have "bound (n + m) (%n. setsum (%i. f i * g (n-i)) {..n})"
      proof
	fix k
	assume bound: "n + m < k"
	{
	  fix i
	  have "f i * g (k-i) = 0"
	  proof cases
	    assume "n < i"
	    show ?thesis by (auto! simp add: ring_simps)
	  next
	    assume "~ (n < i)"
	    with bound have "m < k-i" by arith
	    then show ?thesis by (auto! simp add: ring_simps)
	  qed
	}
	then show "setsum (%i. f i * g (k-i)) {..k} = 0"
	  by (simp add: ring_simps)
      qed
      then show "(%n. setsum (%i. f i * g (n-i)) {..n}) : UP"
	by (unfold UP_def) fast
    qed
  }
  then show ?thesis
    by (simp add: coeff_def up_mult_def Abs_UP_inverse Rep_UP)
qed

lemma coeff_uminus [simp]: "coeff (-p) n = (-coeff p n::'a::ring)"
by (unfold up_uminus_def) (simp add: ring_simps)

(* Other lemmas *)

lemma up_eqI: assumes prem: "(!! n. coeff p n = coeff q n)" shows "p = q"
proof -
  have "p = Abs_UP (%u. Rep_UP p u)" by (simp add: Rep_UP_inverse)
  also from prem have "... = Abs_UP (Rep_UP q)" by (simp only: coeff_def)
  also have "... = q" by (simp add: Rep_UP_inverse)
  finally show ?thesis .
qed

(* ML_setup {* Addsimprocs [ring_simproc] *} *)

instance up :: (ring) ring
proof
  fix p q r :: "'a::ring up"
  fix n
  show "(p + q) + r = p + (q + r)"
    by (rule up_eqI) simp
  show "0 + p = p"
    by (rule up_eqI) simp
  show "(-p) + p = 0"
    by (rule up_eqI) simp
  show "p + q = q + p"
    by (rule up_eqI) simp
  show "(p * q) * r = p * (q * r)"
  proof (rule up_eqI)
    fix n 
    {
      fix k and a b c :: "nat=>'a::ring"
      have "k <= n ==> 
	setsum (%j. setsum (%i. a i * b (j-i)) {..j} * c (n-j)) {..k} = 
	setsum (%j. a j * setsum  (%i. b i * c (n-j-i)) {..k-j}) {..k}"
	(is "_ ==> ?eq k")
      proof (induct k)
	case 0 show ?case by simp
      next
	case (Suc k)
	then have "k <= n" by arith
	then have "?eq k" by (rule Suc)
	then show ?case
	  by (simp add: Suc_diff_le natsum_ldistr)
      qed
    }
    then show "coeff ((p * q) * r) n = coeff (p * (q * r)) n"
      by simp
  qed
  show "1 * p = p"
  proof (rule up_eqI)
    fix n
    show "coeff (1 * p) n = coeff p n"
    proof (cases n)
      case 0 then show ?thesis by simp
    next
      case Suc then show ?thesis by (simp del: natsum_Suc add: natsum_Suc2)
    qed
  qed
  show "(p + q) * r = p * r + q * r"
    by (rule up_eqI) simp
  show "p * q = q * p"
  proof (rule up_eqI)
    fix n 
    {
      fix k
      fix a b :: "nat=>'a::ring"
      have "k <= n ==> 
	setsum (%i. a i * b (n-i)) {..k} =
	setsum (%i. a (k-i) * b (i+n-k)) {..k}"
	(is "_ ==> ?eq k")
      proof (induct k)
	case 0 show ?case by simp
      next
	case (Suc k) then show ?case by (subst natsum_Suc2) simp
      qed
    }
    then show "coeff (p * q) n = coeff (q * p) n"
      by simp
  qed

  show "p - q = p + (-q)"
    by (simp add: up_minus_def)
  show "inverse p = (if p dvd 1 then THE x. p*x = 1 else 0)"
    by (simp add: up_inverse_def)
  show "p / q = p * inverse q"
    by (simp add: up_divide_def)
  show "p ^ n = nat_rec 1 (%u b. b * p) n"
    by (simp add: up_power_def)
  qed

(* Further properties of monom *)

lemma monom_zero [simp]:
  "monom 0 n = 0"
  by (simp add: monom_def up_zero_def)

lemma monom_mult_is_smult:
  "monom (a::'a::ring) 0 * p = a *s p"
proof (rule up_eqI)
  fix k
  show "coeff (monom a 0 * p) k = coeff (a *s p) k"
  proof (cases k)
    case 0 then show ?thesis by simp
  next
    case Suc then show ?thesis by simp
  qed
qed

lemma monom_add [simp]:
  "monom (a + b) n = monom (a::'a::ring) n + monom b n"
by (rule up_eqI) simp

lemma monom_mult_smult:
  "monom (a * b) n = a *s monom (b::'a::ring) n"
by (rule up_eqI) simp

lemma monom_uminus [simp]:
  "monom (-a) n = - monom (a::'a::ring) n"
by (rule up_eqI) simp

lemma monom_one [simp]:
  "monom 1 0 = 1"
by (simp add: up_one_def)

lemma monom_inj:
  "(monom a n = monom b n) = (a = b)"
proof
  assume "monom a n = monom b n"
  then have "coeff (monom a n) n = coeff (monom b n) n" by simp
  then show "a = b" by simp
next
  assume "a = b" then show "monom a n = monom b n" by simp
qed

(* Properties of *s:
   Polynomials form a module *)

lemma smult_l_distr:
  "(a + b::'a::ring) *s p = a *s p + b *s p"
by (rule up_eqI) simp

lemma smult_r_distr:
  "(a::'a::ring) *s (p + q) = a *s p + a *s q"
by (rule up_eqI) simp

lemma smult_assoc1:
  "(a * b::'a::ring) *s p = a *s (b *s p)"
by (rule up_eqI) simp

lemma smult_one [simp]:
  "(1::'a::ring) *s p = p"
by (rule up_eqI) simp

(* Polynomials form an algebra *)

ML_setup {* Delsimprocs [ring_simproc] *}

lemma smult_assoc2:
  "(a *s p) * q = (a::'a::ring) *s (p * q)"
by (rule up_eqI) (simp add: natsum_rdistr m_assoc)
(* Simproc fails. *)

ML_setup {* Addsimprocs [ring_simproc] *}

(* the following can be derived from the above ones,
   for generality reasons, it is therefore done *)

lemma smult_l_null [simp]:
  "(0::'a::ring) *s p = 0"
proof -
  fix a
  have "0 *s p = (0 *s p + a *s p) + - (a *s p)" by simp
  also have "... = (0 + a) *s p + - (a *s p)" by (simp only: smult_l_distr)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma smult_r_null [simp]:
  "(a::'a::ring) *s 0 = 0";
proof -
  fix p
  have "a *s 0 = (a *s 0 + a *s p) + - (a *s p)" by simp
  also have "... = a *s (0 + p) + - (a *s p)" by (simp only: smult_r_distr)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma smult_l_minus:
  "(-a::'a::ring) *s p = - (a *s p)"
proof -
  have "(-a) *s p = (-a *s p + a *s p) + -(a *s p)" by simp 
  also have "... = (-a + a) *s p + -(a *s p)" by (simp only: smult_l_distr)
  also have "... = -(a *s p)" by simp
  finally show ?thesis .
qed

lemma smult_r_minus:
  "(a::'a::ring) *s (-p) = - (a *s p)"
proof -
  have "a *s (-p) = (a *s -p + a *s p) + -(a *s p)" by simp
  also have "... = a *s (-p + p) + -(a *s p)" by (simp only: smult_r_distr)
  also have "... = -(a *s p)" by simp
  finally show ?thesis .
qed

section {* The degree function *}

constdefs
  deg :: "('a::zero) up => nat"
  "deg p == LEAST n. bound n (coeff p)"

lemma deg_aboveI:
  "(!!m. n < m ==> coeff p m = 0) ==> deg p <= n"
by (unfold deg_def) (fast intro: Least_le)

lemma deg_aboveD:
  assumes prem: "deg p < m" shows "coeff p m = 0"
proof -
  obtain n where "bound n (coeff p)" by (rule bound_coeff_obtain)
  then have "bound (deg p) (coeff p)" by (unfold deg_def, rule LeastI)
  then show "coeff p m = 0" by (rule boundD)
qed

lemma deg_belowI:
  assumes prem: "n ~= 0 ==> coeff p n ~= 0" shows "n <= deg p"
(* logically, this is a slightly stronger version of deg_aboveD *)
proof (cases "n=0")
  case True then show ?thesis by simp
next
  case False then have "coeff p n ~= 0" by (rule prem)
  then have "~ deg p < n" by (fast dest: deg_aboveD)
  then show ?thesis by arith
qed

lemma lcoeff_nonzero_deg:
  assumes deg: "deg p ~= 0" shows "coeff p (deg p) ~= 0"
proof -
  obtain m where "deg p <= m" and m_coeff: "coeff p m ~= 0"
  proof -
    have minus: "!!(n::nat) m. n ~= 0 ==> (n - Suc 0 < m) = (n <= m)"
      by arith (* make public?, why does proof not work with "1" *)
    from deg have "deg p - 1 < (LEAST n. bound n (coeff p))"
      by (unfold deg_def) arith
    then have "~ bound (deg p - 1) (coeff p)" by (rule not_less_Least)
    then have "EX m. deg p - 1 < m & coeff p m ~= 0"
      by (unfold bound_def) fast
    then have "EX m. deg p <= m & coeff p m ~= 0" by (simp add: deg minus)
    then show ?thesis by auto 
  qed
  with deg_belowI have "deg p = m" by fastsimp
  with m_coeff show ?thesis by simp
qed

lemma lcoeff_nonzero_nonzero:
  assumes deg: "deg p = 0" and nonzero: "p ~= 0" shows "coeff p 0 ~= 0"
proof -
  have "EX m. coeff p m ~= 0"
  proof (rule classical)
    assume "~ ?thesis"
    then have "p = 0" by (auto intro: up_eqI)
    with nonzero show ?thesis by contradiction
  qed
  then obtain m where coeff: "coeff p m ~= 0" ..
  then have "m <= deg p" by (rule deg_belowI)
  then have "m = 0" by (simp add: deg)
  with coeff show ?thesis by simp
qed

lemma lcoeff_nonzero:
  "p ~= 0 ==> coeff p (deg p) ~= 0"
proof (cases "deg p = 0")
  case True
  assume "p ~= 0"
  with True show ?thesis by (simp add: lcoeff_nonzero_nonzero)
next
  case False
  assume "p ~= 0"
  with False show ?thesis by (simp add: lcoeff_nonzero_deg)
qed

lemma deg_eqI:
  "[| !!m. n < m ==> coeff p m = 0;
      !!n. n ~= 0 ==> coeff p n ~= 0|] ==> deg p = n"
by (fast intro: le_anti_sym deg_aboveI deg_belowI)

(* Degree and polynomial operations *)

lemma deg_add [simp]:
  "deg ((p::'a::ring up) + q) <= max (deg p) (deg q)"
proof (cases "deg p <= deg q")
  case True show ?thesis by (rule deg_aboveI) (simp add: True deg_aboveD) 
next
  case False show ?thesis by (rule deg_aboveI) (simp add: False deg_aboveD)
qed

lemma deg_monom_ring:
  "deg (monom a n::'a::ring up) <= n"
by (rule deg_aboveI) simp

lemma deg_monom [simp]:
  "a ~= 0 ==> deg (monom a n::'a::ring up) = n"
by (fastsimp intro: le_anti_sym deg_aboveI deg_belowI)

lemma deg_const [simp]:
  "deg (monom (a::'a::ring) 0) = 0"
proof (rule le_anti_sym)
  show "deg (monom a 0) <= 0" by (rule deg_aboveI) simp
next
  show "0 <= deg (monom a 0)" by (rule deg_belowI) simp
qed

lemma deg_zero [simp]:
  "deg 0 = 0"
proof (rule le_anti_sym)
  show "deg 0 <= 0" by (rule deg_aboveI) simp
next
  show "0 <= deg 0" by (rule deg_belowI) simp
qed

lemma deg_one [simp]:
  "deg 1 = 0"
proof (rule le_anti_sym)
  show "deg 1 <= 0" by (rule deg_aboveI) simp
next
  show "0 <= deg 1" by (rule deg_belowI) simp
qed

lemma uminus_monom:
  "!!a::'a::ring. (-a = 0) = (a = 0)"
proof
  fix a::"'a::ring"
  assume "a = 0"
  then show "-a = 0" by simp
next
  fix a::"'a::ring"
  assume "- a = 0"
  then have "-(- a) = 0" by simp
  then show "a = 0" by simp
qed

lemma deg_uminus [simp]:
  "deg (-p::('a::ring) up) = deg p"
proof (rule le_anti_sym)
  show "deg (- p) <= deg p" by (simp add: deg_aboveI deg_aboveD)
next
  show "deg p <= deg (- p)" 
  by (simp add: deg_belowI lcoeff_nonzero_deg uminus_monom)
qed

lemma deg_smult_ring:
  "deg ((a::'a::ring) *s p) <= (if a = 0 then 0 else deg p)"
proof (cases "a = 0")
qed (simp add: deg_aboveI deg_aboveD)+

lemma deg_smult [simp]:
  "deg ((a::'a::domain) *s p) = (if a = 0 then 0 else deg p)"
proof (rule le_anti_sym)
  show "deg (a *s p) <= (if a = 0 then 0 else deg p)" by (rule deg_smult_ring)
next
  show "(if a = 0 then 0 else deg p) <= deg (a *s p)"
  proof (cases "a = 0")
  qed (simp, simp add: deg_belowI lcoeff_nonzero_deg integral_iff)
qed

lemma deg_mult_ring:
  "deg (p * q::'a::ring up) <= deg p + deg q"
proof (rule deg_aboveI)
  fix m
  assume boundm: "deg p + deg q < m"
  {
    fix k i
    assume boundk: "deg p + deg q < k"
    then have "coeff p i * coeff q (k - i) = 0"
    proof (cases "deg p < i")
      case True then show ?thesis by (simp add: deg_aboveD)
    next
      case False with boundk have "deg q < k - i" by arith
      then show ?thesis by (simp add: deg_aboveD)
    qed
  }
      (* This is similar to bound_mult_zero and deg_above_mult_zero in the old
         proofs. *)
  with boundm show "coeff (p * q) m = 0" by simp
qed

lemma deg_mult [simp]:
  "[| (p::'a::domain up) ~= 0; q ~= 0|] ==> deg (p * q) = deg p + deg q"
proof (rule le_anti_sym)
  show "deg (p * q) <= deg p + deg q" by (rule deg_mult_ring)
next
  let ?s = "(%i. coeff p i * coeff q (deg p + deg q - i))"
  assume nz: "p ~= 0" "q ~= 0"
  have less_add_diff: "!!(k::nat) n m. k < n ==> m < n + m - k" by arith
  show "deg p + deg q <= deg (p * q)"
  proof (rule deg_belowI, simp)
    have "setsum ?s {.. deg p + deg q}
      = setsum ?s ({.. deg p(} Un {deg p .. deg p + deg q})"
      by (simp only: ivl_disj_un_one)
    also have "... = setsum ?s {deg p .. deg p + deg q}"
      by (simp add: setsum_Un_disjoint ivl_disj_int_one
        setsum_0 deg_aboveD less_add_diff)
    also have "... = setsum ?s ({deg p} Un {)deg p .. deg p + deg q})"
      by (simp only: ivl_disj_un_singleton)
    also have "... = coeff p (deg p) * coeff q (deg q)" 
      by (simp add: setsum_Un_disjoint ivl_disj_int_singleton 
        setsum_0 deg_aboveD)
    finally have "setsum ?s {.. deg p + deg q} 
      = coeff p (deg p) * coeff q (deg q)" .
    with nz show "setsum ?s {.. deg p + deg q} ~= 0"
      by (simp add: integral_iff lcoeff_nonzero)
    qed
  qed

lemma coeff_natsum:
  "((coeff (setsum p A) k)::'a::ring) = 
   setsum (%i. coeff (p i) k) A"
proof (cases "finite A")
  case True then show ?thesis by induct auto
next
  case False then show ?thesis by (simp add: setsum_def)
qed
(* Instance of a more general result!!! *)

(*
lemma coeff_natsum:
  "((coeff (setsum p {..n::nat}) k)::'a::ring) = 
   setsum (%i. coeff (p i) k) {..n}"
by (induct n) auto
*)

lemma up_repr:
  "setsum (%i. monom (coeff p i) i) {..deg (p::'a::ring up)} = p"
proof (rule up_eqI)
  let ?s = "(%i. monom (coeff p i) i)"
  fix k
  show "coeff (setsum ?s {..deg p}) k = coeff p k"
  proof (cases "k <= deg p")
    case True
    hence "coeff (setsum ?s {..deg p}) k = 
          coeff (setsum ?s ({..k} Un {)k..deg p})) k"
      by (simp only: ivl_disj_un_one)
    also from True
    have "... = coeff (setsum ?s {..k}) k"
      by (simp add: setsum_Un_disjoint ivl_disj_int_one order_less_imp_not_eq2
        setsum_0 coeff_natsum )
    also
    have "... = coeff (setsum ?s ({..k(} Un {k})) k"
      by (simp only: ivl_disj_un_singleton)
    also have "... = coeff p k"
      by (simp add: setsum_Un_disjoint ivl_disj_int_singleton 
        setsum_0 coeff_natsum deg_aboveD)
    finally show ?thesis .
  next
    case False
    hence "coeff (setsum ?s {..deg p}) k = 
          coeff (setsum ?s ({..deg p(} Un {deg p})) k"
      by (simp only: ivl_disj_un_singleton)
    also from False have "... = coeff p k"
      by (simp add: setsum_Un_disjoint ivl_disj_int_singleton 
        setsum_0 coeff_natsum deg_aboveD)
    finally show ?thesis .
  qed
qed

lemma up_repr_le:
  "deg (p::'a::ring up) <= n ==> setsum (%i. monom (coeff p i) i) {..n} = p"
proof -
  let ?s = "(%i. monom (coeff p i) i)"
  assume "deg p <= n"
  then have "setsum ?s {..n} = setsum ?s ({..deg p} Un {)deg p..n})"
    by (simp only: ivl_disj_un_one)
  also have "... = setsum ?s {..deg p}"
    by (simp add: setsum_Un_disjoint ivl_disj_int_one
      setsum_0 deg_aboveD)
  also have "... = p" by (rule up_repr)
  finally show ?thesis .
qed

instance up :: ("domain") "domain"
proof
  show "1 ~= (0::'a up)"
  proof (* notI is applied here *)
    assume "1 = (0::'a up)"
    hence "coeff 1 0 = (coeff 0 0::'a)" by simp
    hence "1 = (0::'a)" by simp
    with one_not_zero show "False" by contradiction
  qed
next
  fix p q :: "'a::domain up"
  assume pq: "p * q = 0"
  show "p = 0 | q = 0"
  proof (rule classical)
    assume c: "~ (p = 0 | q = 0)"
    then have "deg p + deg q = deg (p * q)" by simp
    also from pq have "... = 0" by simp
    finally have "deg p + deg q = 0" .
    then have f1: "deg p = 0 & deg q = 0" by simp
    from f1 have "p = setsum (%i. (monom (coeff p i) i)) {..0}"
      by (simp only: up_repr_le)
    also have "... = monom (coeff p 0) 0" by simp
    finally have p: "p = monom (coeff p 0) 0" .
    from f1 have "q = setsum (%i. (monom (coeff q i) i)) {..0}"
      by (simp only: up_repr_le)
    also have "... = monom (coeff q 0) 0" by simp
    finally have q: "q = monom (coeff q 0) 0" .
    have "coeff p 0 * coeff q 0 = coeff (p * q) 0" by simp
    also from pq have "... = 0" by simp
    finally have "coeff p 0 * coeff q 0 = 0" .
    then have "coeff p 0 = 0 | coeff q 0 = 0" by (simp only: integral_iff)
    with p q show "p = 0 | q = 0" by fastsimp
  qed
qed

lemma monom_inj_zero:
  "(monom a n = 0) = (a = 0)"
proof -
  have "(monom a n = 0) = (monom a n = monom 0 n)" by simp
  also have "... = (a = 0)" by (simp add: monom_inj del: monom_zero)
  finally show ?thesis .
qed

lemma smult_integral:
  "(a::'a::domain) *s p = 0 ==> a = 0 | p = 0"
by (simp add: monom_mult_is_smult [THEN sym] integral_iff monom_inj_zero) fast

end