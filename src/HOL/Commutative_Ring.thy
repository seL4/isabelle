(*  ID:         $Id$
    Author:     Bernhard Haeupler

Proving equalities in commutative rings done "right" in Isabelle/HOL.
*)

header {* Proving equalities in commutative rings *}

theory Commutative_Ring
imports List
uses ("Tools/comm_ring.ML")
begin

  (* Syntax of multivariate polynomials (pol) and polynomial expressions*)
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

  (* Interpretation functions for the shadow syntax *)
consts
  Ipol :: "('a::{comm_ring,recpower}) list \<Rightarrow> 'a pol \<Rightarrow> 'a"
  Ipolex :: "('a::{comm_ring,recpower}) list \<Rightarrow> 'a polex \<Rightarrow> 'a"

primrec
  "Ipol l (Pc c) = c"
  "Ipol l (Pinj i P) = Ipol (drop i l) P"
  "Ipol l (PX P x Q) = (Ipol l P)*((hd l)^x) + (Ipol (drop 1 l) Q)"

primrec
  "Ipolex l (Pol P) = Ipol l P"
  "Ipolex l (Add P Q) = (Ipolex l P) + (Ipolex l Q)"
  "Ipolex l (Sub P Q) = (Ipolex l P) - (Ipolex l Q)"
  "Ipolex l (Mul P Q) = (Ipolex l P) * (Ipolex l Q)"
  "Ipolex l (Pow p n) = (Ipolex l p) ^ n"
  "Ipolex l (Neg P) = -(Ipolex l P)"

  (* Create polynomial normalized polynomials given normalized inputs *)
constdefs mkPinj :: "nat \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
  mkPinj_def: "mkPinj x P \<equiv> (case P of
  (Pc c) \<Rightarrow> (Pc c) |
  (Pinj y P) \<Rightarrow> Pinj (x+y) P |
  (PX p1 y p2) \<Rightarrow> Pinj x P )"

constdefs mkPX :: "('a::{comm_ring,recpower}) pol \<Rightarrow> nat \<Rightarrow> 'a pol \<Rightarrow> 'a pol"
  mkPX_def: "mkPX P i Q == (case P of
  (Pc c) \<Rightarrow> (if (c = 0) then (mkPinj 1 Q) else (PX P i Q)) |
  (Pinj j R) \<Rightarrow> (PX P i Q) |
  (PX P2 i2 Q2) \<Rightarrow> (if (Q2 = (Pc 0)) then (PX P2 (i+i2) Q) else (PX P i Q)) )"

  (* Defining the basic ring operations on normalized polynomials *)
consts
add :: "(('a::{comm_ring,recpower}) pol) \<times> ('a pol) \<Rightarrow> 'a pol"
mul :: "(('a::{comm_ring,recpower}) pol) \<times> ('a pol) \<Rightarrow> 'a pol"
neg :: "('a::{comm_ring,recpower}) pol \<Rightarrow> 'a pol"
sqr :: "('a::{comm_ring,recpower}) pol  \<Rightarrow> 'a pol"
pow :: "('a::{comm_ring,recpower}) pol \<times> nat \<Rightarrow> 'a pol"


  (* Addition *)
recdef add "measure (\<lambda>(x, y). size x + size y)"
  "add (Pc a, Pc b) = Pc (a+b)"
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

  (* Multiplication *)
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

  (* Negation*)
primrec
  "neg (Pc c) = (Pc (-c))"
  "neg (Pinj i P) = Pinj i (neg P)"
  "neg (PX P x Q) = PX (neg P) x (neg Q)"

  (* Substraction*)
constdefs sub :: "(('a::{comm_ring,recpower}) pol) \<Rightarrow> ('a pol) \<Rightarrow> 'a pol"
  "sub p q \<equiv> add (p,neg q)"

  (* Square for Fast Exponentation *)
primrec
  "sqr (Pc c) = Pc (c*c)"
  "sqr (Pinj i P) = mkPinj i (sqr P)"
  "sqr (PX A x B) = add (mkPX (sqr A) (x+x) (sqr B), mkPX (mul (mul (Pc (1+1), A), mkPinj 1 B)) x (Pc 0))"

  (* Fast Exponentation *)
lemma pow_wf:"odd n \<longrightarrow> (n::nat) div 2 < n" by(cases n, auto)
recdef pow "measure (\<lambda>(x, y). y)"
  "pow (p, 0) = Pc 1"
  "pow (p, n) = (if even n then (pow (sqr p, n div 2)) else mul (p, pow (sqr p, n div 2)))"
(hints simp add: pow_wf)

lemma pow_if: "pow (p,n) = (if n=0 then Pc 1 else (if even n then (pow (sqr p, n div 2)) else mul (p, pow (sqr p, n div 2))))"
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
  (* Normalization of polynomial expressions *)

consts norm :: "('a::{comm_ring,recpower}) polex \<Rightarrow> 'a pol"
primrec
  "norm (Pol P) = P"
  "norm (Add P Q) = add (norm P, norm Q)"
  "norm (Sub p q) = sub (norm p) (norm q)"
  "norm (Mul P Q) = mul (norm P, norm Q)"
  "norm (Pow p n) = pow (norm p, n)"
  "norm (Neg P) = neg (norm P)"

  (* mkPinj preserve semantics *)
lemma mkPinj_ci: "ALL a l. Ipol l (mkPinj a B) = Ipol l (Pinj a B)"
  by(induct B, auto simp add: mkPinj_def ring_eq_simps)

  (* mkPX preserves semantics *)
lemma mkPX_ci: "ALL b l. Ipol l (mkPX A b C) = Ipol l (PX A b C)"
  by(case_tac A, auto simp add: mkPX_def mkPinj_ci power_add ring_eq_simps)

  (* Correctness theorems for the implemented operations *)
  (* Negation *)
lemma neg_ci: "ALL l. Ipol l (neg P) = -(Ipol l P)"
  by(induct P, auto)

  (* Addition *)
lemma add_ci: "ALL l. Ipol l (add (P, Q)) = Ipol l P + Ipol l Q"
proof(induct P Q rule: add.induct)
  case (6 x P y Q)
  have "x < y \<or> x = y \<or> x > y" by arith
  moreover
  { assume "x<y" hence "EX d. d+x=y" by arith
    then obtain d where "d+x=y"..
    with prems have ?case by (auto simp add: mkPinj_ci ring_eq_simps) }
  moreover
  { assume "x=y" with prems have ?case by (auto simp add: mkPinj_ci)}
  moreover
  { assume "x>y" hence "EX d. d+y=x" by arith
    then obtain d where "d+y=x"..
    with prems have ?case by (auto simp add: mkPinj_ci ring_eq_simps) }
  ultimately show ?case by blast
next
  case (7 x P Q y R)
  have "x=0 \<or> (x = 1) \<or> (x > 1)" by arith
  moreover
  { assume "x=0" with prems have ?case by auto }
  moreover
  { assume "x=1" with prems have ?case by (auto simp add: ring_eq_simps) }
  moreover
  { assume "x > 1" from prems have ?case by(cases x, auto) }
  ultimately show ?case by blast
next
  case (8 P x R y Q)
  have "(y = 0) \<or> (y = 1) \<or> (y > 1)" by arith
  moreover
  {assume "y=0" with prems have ?case by simp}
  moreover
  {assume "y=1" with prems have ?case by simp}
  moreover
  {assume "y>1" hence "EX d. d+1=y" by arith
    then obtain d where "d+1=y" ..
    with prems have ?case by auto }
  ultimately show ?case by blast
next
  case (9 P1 x P2 Q1 y Q2)
  have "y < x \<or> x = y \<or> x < y" by arith
  moreover
  {assume "y < x" hence "EX d. d+y=x" by arith
    then obtain d where "d+y=x"..
    with prems have ?case by (auto simp add: power_add mkPX_ci ring_eq_simps) }
  moreover
  {assume "x=y" with prems have ?case by(auto simp add: mkPX_ci ring_eq_simps) }
  moreover
  {assume "x<y" hence "EX d. d+x=y" by arith
    then obtain d where "d+x=y" ..
    with prems have ?case by (auto simp add: mkPX_ci power_add ring_eq_simps) }
  ultimately show ?case by blast
qed (auto simp add: ring_eq_simps)

    (* Multiplication *)
lemma mul_ci: "ALL l. Ipol l (mul (P, Q)) = Ipol l P * Ipol l Q"
  by (induct P Q rule: mul.induct, auto simp add: mkPX_ci mkPinj_ci ring_eq_simps add_ci power_add)

  (* Substraction *)
lemma sub_ci: "\<forall> l. Ipol l (sub p q) = (Ipol l p) - (Ipol l q)"
  by (auto simp add: add_ci neg_ci sub_def)

  (* Square *)
lemma sqr_ci:"ALL ls. Ipol ls (sqr p) = Ipol ls p * Ipol ls p"
by(induct p, auto simp add: add_ci mkPinj_ci mkPX_ci mul_ci ring_eq_simps power_add)


  (* Power *)
lemma even_pow:"even n \<longrightarrow> pow (p, n) = pow (sqr p, n div 2)" by(induct n,auto)
lemma pow_ci: "ALL p. Ipol ls (pow (p, n)) = (Ipol ls p) ^ n"
proof(induct n rule: nat_less_induct)
  case (1 k)
  have two:"2=Suc( Suc 0)" by simp
  from prems show ?case
  proof(cases k)
    case (Suc l)
    hence KL:"k=Suc l" by simp
    have "even l \<or> odd l" by (simp)
    moreover
    {assume EL:"even l"
      have "Suc l div 2 = l div 2" by (simp add: nat_number even_nat_plus_one_div_two[OF EL])
      moreover
      from KL have"l<k" by simp
      with prems have "ALL p. Ipol ls (pow (p, l)) = Ipol ls p ^ l" by simp
      moreover
      note prems even_nat_plus_one_div_two[OF EL]
      ultimately have ?thesis by (simp add: mul_ci power_Suc even_pow) }
    moreover
    {assume OL:"odd l"
      with prems have "\<lbrakk>\<forall>m<Suc l. \<forall>p. Ipol ls (pow (p, m)) = Ipol ls p ^ m; k = Suc l; odd l\<rbrakk> \<Longrightarrow> \<forall>p. Ipol ls (sqr p) ^ (Suc l div 2) = Ipol ls p ^ Suc l"
      proof(cases l)
        case (Suc w)
        from prems have EW:"even w" by simp
        from two have two_times:"(2 * (w div 2))= w" by (simp only: even_nat_div_two_times_two[OF EW])
        have A:"ALL p. (Ipol ls p * Ipol ls p) = (Ipol ls p) ^ (Suc (Suc 0))" by (simp add: power_Suc)
        from A two[symmetric] have "ALL p.(Ipol ls p * Ipol ls p) = (Ipol ls p) ^ 2" by simp
        with prems show ?thesis by (auto simp add: power_mult[symmetric, of _ 2 _] two_times mul_ci sqr_ci)
      qed(simp)
      with prems have ?thesis by simp }
    ultimately show ?thesis by blast
  qed(simp)
qed

  (* Normalization preserves semantics  *)
lemma norm_ci:"Ipolex l Pe = Ipol l (norm Pe)"
  by(induct Pe, simp_all add: add_ci sub_ci mul_ci neg_ci pow_ci)

(* Reflection lemma: Key to the (incomplete) decision procedure *)
lemma norm_eq:
  assumes A:"norm P1  = norm P2"
  shows "Ipolex l P1 = Ipolex l P2"
proof -
  from A have "Ipol l (norm P1) = Ipol l (norm P2)" by simp
  thus ?thesis by(simp only: norm_ci)
qed


    (* Code generation *)
(*
Does not work, since no generic ring operations implementation is there
generate_code ("ring.ML") test = "norm"*)

use "Tools/comm_ring.ML"
setup "CommRing.setup"

end
