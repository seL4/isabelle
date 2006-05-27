(*  ID:         $Id$
    Author:     Bernhard Haeupler

Proving equalities in commutative rings done "right" in Isabelle/HOL.
*)

header {* Proving equalities in commutative rings *}

theory Commutative_Ring
imports Main
uses ("comm_ring.ML")
begin

text {* Syntax of multivariate polynomials (pol) and polynomial expressions. *}

datatype 'a pol =
    Pc 'a
  | Pinj nat "'a pol"
  | PX "'a pol" nat "'a pol"

datatype 'a polex =
  Pol "'a pol"
  | Add "'a polex" "'a polex"
  | Sub "'a polex" "'a polex"
  | Mul "'a polex" "'a polex"
  | Pow "'a polex" nat
  | Neg "'a polex"

text {* Interpretation functions for the shadow syntax. *}

consts
  Ipol :: "'a::{comm_ring,recpower} list \<Rightarrow> 'a pol \<Rightarrow> 'a"
  Ipolex :: "'a::{comm_ring,recpower} list \<Rightarrow> 'a polex \<Rightarrow> 'a"

primrec
  "Ipol l (Pc c) = c"
  "Ipol l (Pinj i P) = Ipol (drop i l) P"
  "Ipol l (PX P x Q) = Ipol l P * (hd l)^x + Ipol (drop 1 l) Q"

primrec
  "Ipolex l (Pol P) = Ipol l P"
  "Ipolex l (Add P Q) = Ipolex l P + Ipolex l Q"
  "Ipolex l (Sub P Q) = Ipolex l P - Ipolex l Q"
  "Ipolex l (Mul P Q) = Ipolex l P * Ipolex l Q"
  "Ipolex l (Pow p n) = Ipolex l p ^ n"
  "Ipolex l (Neg P) = - Ipolex l P"

text {* Create polynomial normalized polynomials given normalized inputs. *}

definition
  mkPinj :: "nat \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
  "mkPinj x P = (case P of
    Pc c \<Rightarrow> Pc c |
    Pinj y P \<Rightarrow> Pinj (x + y) P |
    PX p1 y p2 \<Rightarrow> Pinj x P)"

definition
  mkPX :: "'a::{comm_ring,recpower} pol \<Rightarrow> nat \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
  "mkPX P i Q = (case P of
    Pc c \<Rightarrow> (if (c = 0) then (mkPinj 1 Q) else (PX P i Q)) |
    Pinj j R \<Rightarrow> PX P i Q |
    PX P2 i2 Q2 \<Rightarrow> (if (Q2 = (Pc 0)) then (PX P2 (i+i2) Q) else (PX P i Q)) )"

text {* Defining the basic ring operations on normalized polynomials *}

consts
  add :: "'a::{comm_ring,recpower} pol \<times> 'a pol \<Rightarrow> 'a pol"
  mul :: "'a::{comm_ring,recpower} pol \<times> 'a pol \<Rightarrow> 'a pol"
  neg :: "'a::{comm_ring,recpower} pol \<Rightarrow> 'a pol"
  sqr :: "'a::{comm_ring,recpower} pol \<Rightarrow> 'a pol"
  pow :: "'a::{comm_ring,recpower} pol \<times> nat \<Rightarrow> 'a pol"

text {* Addition *}
recdef add "measure (\<lambda>(x, y). size x + size y)"
  "add (Pc a, Pc b) = Pc (a + b)"
  "add (Pc c, Pinj i P) = Pinj i (add (P, Pc c))"
  "add (Pinj i P, Pc c) = Pinj i (add (P, Pc c))"
  "add (Pc c, PX P i Q) = PX P i (add (Q, Pc c))"
  "add (PX P i Q, Pc c) = PX P i (add (Q, Pc c))"
  "add (Pinj x P, Pinj y Q) =
  (if x=y then mkPinj x (add (P, Q))
   else (if x>y then mkPinj y (add (Pinj (x-y) P, Q))
         else mkPinj x (add (Pinj (y-x) Q, P)) ))"
  "add (Pinj x P, PX Q y R) =
  (if x=0 then add(P, PX Q y R)
   else (if x=1 then PX Q y (add (R, P))
         else PX Q y (add (R, Pinj (x - 1) P))))"
  "add (PX P x R, Pinj y Q) =
  (if y=0 then add(PX P x R, Q)
   else (if y=1 then PX P x (add (R, Q))
         else PX P x (add (R, Pinj (y - 1) Q))))"
  "add (PX P1 x P2, PX Q1 y Q2) =
  (if x=y then mkPX (add (P1, Q1)) x (add (P2, Q2))
  else (if x>y then mkPX (add (PX P1 (x-y) (Pc 0), Q1)) y (add (P2,Q2))
        else mkPX (add (PX Q1 (y-x) (Pc 0), P1)) x (add (P2,Q2)) ))"

text {* Multiplication *}
recdef mul "measure (\<lambda>(x, y). size x + size y)"
  "mul (Pc a, Pc b) = Pc (a*b)"
  "mul (Pc c, Pinj i P) = (if c=0 then Pc 0 else mkPinj i (mul (P, Pc c)))"
  "mul (Pinj i P, Pc c) = (if c=0 then Pc 0 else mkPinj i (mul (P, Pc c)))"
  "mul (Pc c, PX P i Q) =
  (if c=0 then Pc 0 else mkPX (mul (P, Pc c)) i (mul (Q, Pc c)))"
  "mul (PX P i Q, Pc c) =
  (if c=0 then Pc 0 else mkPX (mul (P, Pc c)) i (mul (Q, Pc c)))"
  "mul (Pinj x P, Pinj y Q) =
  (if x=y then mkPinj x (mul (P, Q))
   else (if x>y then mkPinj y (mul (Pinj (x-y) P, Q))
         else mkPinj x (mul (Pinj (y-x) Q, P)) ))"
  "mul (Pinj x P, PX Q y R) =
  (if x=0 then mul(P, PX Q y R)
   else (if x=1 then mkPX (mul (Pinj x P, Q)) y (mul (R, P))
         else mkPX (mul (Pinj x P, Q)) y (mul (R, Pinj (x - 1) P))))"
  "mul (PX P x R, Pinj y Q) =
  (if y=0 then mul(PX P x R, Q)
   else (if y=1 then mkPX (mul (Pinj y Q, P)) x (mul (R, Q))
         else mkPX (mul (Pinj y Q, P)) x (mul (R, Pinj (y - 1) Q))))"
  "mul (PX P1 x P2, PX Q1 y Q2) =
  add (mkPX (mul (P1, Q1)) (x+y) (mul (P2, Q2)),
  add (mkPX (mul (P1, mkPinj 1 Q2)) x (Pc 0), mkPX (mul (Q1, mkPinj 1 P2)) y (Pc 0)) )"
(hints simp add: mkPinj_def split: pol.split)

text {* Negation*}
primrec
  "neg (Pc c) = Pc (-c)"
  "neg (Pinj i P) = Pinj i (neg P)"
  "neg (PX P x Q) = PX (neg P) x (neg Q)"

text {* Substraction *}
definition
  sub :: "'a::{comm_ring,recpower} pol \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
  "sub p q = add (p, neg q)"

text {* Square for Fast Exponentation *}
primrec
  "sqr (Pc c) = Pc (c * c)"
  "sqr (Pinj i P) = mkPinj i (sqr P)"
  "sqr (PX A x B) = add (mkPX (sqr A) (x + x) (sqr B),
    mkPX (mul (mul (Pc (1 + 1), A), mkPinj 1 B)) x (Pc 0))"

text {* Fast Exponentation *}
lemma pow_wf:"odd n \<Longrightarrow> (n::nat) div 2 < n" by (cases n) auto
recdef pow "measure (\<lambda>(x, y). y)"
  "pow (p, 0) = Pc 1"
  "pow (p, n) = (if even n then (pow (sqr p, n div 2)) else mul (p, pow (sqr p, n div 2)))"
(hints simp add: pow_wf)

lemma pow_if:
  "pow (p,n) =
   (if n = 0 then Pc 1 else if even n then pow (sqr p, n div 2)
    else mul (p, pow (sqr p, n div 2)))"
  by (cases n) simp_all

(*
lemma number_of_nat_B0: "(number_of (w BIT bit.B0) ::nat) = 2* (number_of w)"
by simp

lemma number_of_nat_even: "even (number_of (w BIT bit.B0)::nat)"
by simp

lemma pow_even : "pow (p, number_of(w BIT bit.B0)) = pow (sqr p, number_of w)"
  ( is "pow(?p,?n) = pow (_,?n2)")
proof-
  have "even ?n" by simp
  hence "pow (p, ?n) = pow (sqr p, ?n div 2)"
    apply simp
    apply (cases "IntDef.neg (number_of w)")
    apply simp
    done
*)

text {* Normalization of polynomial expressions *}

consts norm :: "'a::{comm_ring,recpower} polex \<Rightarrow> 'a pol"
primrec
  "norm (Pol P) = P"
  "norm (Add P Q) = add (norm P, norm Q)"
  "norm (Sub p q) = sub (norm p) (norm q)"
  "norm (Mul P Q) = mul (norm P, norm Q)"
  "norm (Pow p n) = pow (norm p, n)"
  "norm (Neg P) = neg (norm P)"

text {* mkPinj preserve semantics *}
lemma mkPinj_ci: "Ipol l (mkPinj a B) = Ipol l (Pinj a B)"
  by (induct B) (auto simp add: mkPinj_def ring_eq_simps)

text {* mkPX preserves semantics *}
lemma mkPX_ci: "Ipol l (mkPX A b C) = Ipol l (PX A b C)"
  by (cases A) (auto simp add: mkPX_def mkPinj_ci power_add ring_eq_simps)

text {* Correctness theorems for the implemented operations *}

text {* Negation *}
lemma neg_ci: "\<And>l. Ipol l (neg P) = -(Ipol l P)"
  by (induct P) auto

text {* Addition *}
lemma add_ci: "\<And>l. Ipol l (add (P, Q)) = Ipol l P + Ipol l Q"
proof (induct P Q rule: add.induct)
  case (6 x P y Q)
  show ?case
  proof (rule linorder_cases)
    assume "x < y"
    with 6 show ?case by (simp add: mkPinj_ci ring_eq_simps)
  next
    assume "x = y"
    with 6 show ?case by (simp add: mkPinj_ci)
  next
    assume "x > y"
    with 6 show ?case by (simp add: mkPinj_ci ring_eq_simps)
  qed
next
  case (7 x P Q y R)
  have "x = 0 \<or> x = 1 \<or> x > 1" by arith
  moreover
  { assume "x = 0" with 7 have ?case by simp }
  moreover
  { assume "x = 1" with 7 have ?case by (simp add: ring_eq_simps) }
  moreover
  { assume "x > 1" from 7 have ?case by (cases x) simp_all }
  ultimately show ?case by blast
next
  case (8 P x R y Q)
  have "y = 0 \<or> y = 1 \<or> y > 1" by arith
  moreover
  { assume "y = 0" with 8 have ?case by simp }
  moreover
  { assume "y = 1" with 8 have ?case by simp }
  moreover
  { assume "y > 1" with 8 have ?case by simp }
  ultimately show ?case by blast
next
  case (9 P1 x P2 Q1 y Q2)
  show ?case
  proof (rule linorder_cases)
    assume a: "x < y" hence "EX d. d + x = y" by arith
    with 9 a show ?case by (auto simp add: mkPX_ci power_add ring_eq_simps)
  next
    assume a: "y < x" hence "EX d. d + y = x" by arith
    with 9 a show ?case by (auto simp add: power_add mkPX_ci ring_eq_simps)
  next
    assume "x = y"
    with 9 show ?case by (simp add: mkPX_ci ring_eq_simps)
  qed
qed (auto simp add: ring_eq_simps)

text {* Multiplication *}
lemma mul_ci: "\<And>l. Ipol l (mul (P, Q)) = Ipol l P * Ipol l Q"
  by (induct P Q rule: mul.induct)
    (simp_all add: mkPX_ci mkPinj_ci ring_eq_simps add_ci power_add)

text {* Substraction *}
lemma sub_ci: "Ipol l (sub p q) = Ipol l p - Ipol l q"
  by (simp add: add_ci neg_ci sub_def)

text {* Square *}
lemma sqr_ci:"\<And>ls. Ipol ls (sqr p) = Ipol ls p * Ipol ls p"
  by (induct p) (simp_all add: add_ci mkPinj_ci mkPX_ci mul_ci ring_eq_simps power_add)


text {* Power *}
lemma even_pow:"even n \<Longrightarrow> pow (p, n) = pow (sqr p, n div 2)" by (induct n) simp_all

lemma pow_ci: "\<And>p. Ipol ls (pow (p, n)) = (Ipol ls p) ^ n"
proof (induct n rule: nat_less_induct)
  case (1 k)
  have two:"2 = Suc (Suc 0)" by simp
  show ?case
  proof (cases k)
    case (Suc l)
    show ?thesis
    proof cases
      assume EL: "even l"
      have "Suc l div 2 = l div 2"
        by (simp add: nat_number even_nat_plus_one_div_two [OF EL])
      moreover
      from Suc have "l < k" by simp
      with 1 have "\<forall>p. Ipol ls (pow (p, l)) = Ipol ls p ^ l" by simp
      moreover
      note Suc EL even_nat_plus_one_div_two [OF EL]
      ultimately show ?thesis by (auto simp add: mul_ci power_Suc even_pow)
    next
      assume OL: "odd l"
      with prems have "\<lbrakk>\<forall>m<Suc l. \<forall>p. Ipol ls (pow (p, m)) = Ipol ls p ^ m; k = Suc l; odd l\<rbrakk> \<Longrightarrow> \<forall>p. Ipol ls (sqr p) ^ (Suc l div 2) = Ipol ls p ^ Suc l"
      proof(cases l)
        case (Suc w)
        from prems have EW: "even w" by simp
        from two have two_times:"(2 * (w div 2))= w"
          by (simp only: even_nat_div_two_times_two[OF EW])
        have A: "\<And>p. (Ipol ls p * Ipol ls p) = (Ipol ls p) ^ (Suc (Suc 0))"
          by (simp add: power_Suc)
        from A two [symmetric] have "ALL p.(Ipol ls p * Ipol ls p) = (Ipol ls p) ^ 2"
          by simp
        with prems show ?thesis
          by (auto simp add: power_mult[symmetric, of _ 2 _] two_times mul_ci sqr_ci)
      qed simp
      with prems show ?thesis by simp
    qed
  next
    case 0
    then show ?thesis by simp
  qed
qed

text {* Normalization preserves semantics  *}
lemma norm_ci:"Ipolex l Pe = Ipol l (norm Pe)"
  by (induct Pe) (simp_all add: add_ci sub_ci mul_ci neg_ci pow_ci)

text {* Reflection lemma: Key to the (incomplete) decision procedure *}
lemma norm_eq:
  assumes eq: "norm P1  = norm P2"
  shows "Ipolex l P1 = Ipolex l P2"
proof -
  from eq have "Ipol l (norm P1) = Ipol l (norm P2)" by simp
  thus ?thesis by (simp only: norm_ci)
qed


use "comm_ring.ML"
setup CommRing.setup

end
