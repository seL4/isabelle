(*  Title:      HOL/Groebner_Basis.thy
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Semiring normalization and Groebner Bases *}
theory Groebner_Basis
imports NatBin
uses
  "Tools/Groebner_Basis/misc.ML"
  "Tools/Groebner_Basis/normalizer_data.ML"
  ("Tools/Groebner_Basis/normalizer.ML")
  ("Tools/Groebner_Basis/groebner.ML")
begin


subsection {* Semiring normalization *}

setup NormalizerData.setup


locale gb_semiring =
  fixes add mul pwr r0 r1
  assumes add_a:"(add x (add y z) = add (add x y) z)"
    and add_c: "add x y = add y x" and add_0:"add r0 x = x"
    and mul_a:"mul x (mul y z) = mul (mul x y) z" and mul_c:"mul x y = mul y x"
    and mul_1:"mul r1 x = x" and  mul_0:"mul r0 x = r0"
    and mul_d:"mul x (add y z) = add (mul x y) (mul x z)"
    and pwr_0:"pwr x 0 = r1" and pwr_Suc:"pwr x (Suc n) = mul x (pwr x n)"
begin

lemma mul_pwr:"mul (pwr x p) (pwr x q) = pwr x (p + q)"
proof (induct p)
  case 0
  then show ?case by (auto simp add: pwr_0 mul_1)
next
  case Suc
  from this [symmetric] show ?case
    by (auto simp add: pwr_Suc mul_1 mul_a)
qed

lemma pwr_mul: "pwr (mul x y) q = mul (pwr x q) (pwr y q)"
proof (induct q arbitrary: x y, auto simp add:pwr_0 pwr_Suc mul_1)
  fix q x y
  assume "\<And>x y. pwr (mul x y) q = mul (pwr x q) (pwr y q)"
  have "mul (mul x y) (mul (pwr x q) (pwr y q)) = mul x (mul y (mul (pwr x q) (pwr y q)))"
    by (simp add: mul_a)
  also have "\<dots> = (mul (mul y (mul (pwr y q) (pwr x q))) x)" by (simp add: mul_c)
  also have "\<dots> = (mul (mul y (pwr y q)) (mul (pwr x q) x))" by (simp add: mul_a)
  finally show "mul (mul x y) (mul (pwr x q) (pwr y q)) =
    mul (mul x (pwr x q)) (mul y (pwr y q))" by (simp add: mul_c)
qed

lemma pwr_pwr: "pwr (pwr x p) q = pwr x (p * q)"
proof (induct p arbitrary: q)
  case 0
  show ?case using pwr_Suc mul_1 pwr_0 by (induct q) auto
next
  case Suc
  thus ?case by (auto simp add: mul_pwr [symmetric] pwr_mul pwr_Suc)
qed


subsubsection {* Declaring the abstract theory *}

lemma semiring_ops:
  includes meta_term_syntax
  shows "TERM (add x y)" and "TERM (mul x y)" and "TERM (pwr x n)"
    and "TERM r0" and "TERM r1"
  by rule+

lemma semiring_rules:
  "add (mul a m) (mul b m) = mul (add a b) m"
  "add (mul a m) m = mul (add a r1) m"
  "add m (mul a m) = mul (add a r1) m"
  "add m m = mul (add r1 r1) m"
  "add r0 a = a"
  "add a r0 = a"
  "mul a b = mul b a"
  "mul (add a b) c = add (mul a c) (mul b c)"
  "mul r0 a = r0"
  "mul a r0 = r0"
  "mul r1 a = a"
  "mul a r1 = a"
  "mul (mul lx ly) (mul rx ry) = mul (mul lx rx) (mul ly ry)"
  "mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry))"
  "mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry)"
  "mul (mul lx ly) rx = mul (mul lx rx) ly"
  "mul (mul lx ly) rx = mul lx (mul ly rx)"
  "mul lx (mul rx ry) = mul (mul lx rx) ry"
  "mul lx (mul rx ry) = mul rx (mul lx ry)"
  "add (add a b) (add c d) = add (add a c) (add b d)"
  "add (add a b) c = add a (add b c)"
  "add a (add c d) = add c (add a d)"
  "add (add a b) c = add (add a c) b"
  "add a c = add c a"
  "add a (add c d) = add (add a c) d"
  "mul (pwr x p) (pwr x q) = pwr x (p + q)"
  "mul x (pwr x q) = pwr x (Suc q)"
  "mul (pwr x q) x = pwr x (Suc q)"
  "mul x x = pwr x 2"
  "pwr (mul x y) q = mul (pwr x q) (pwr y q)"
  "pwr (pwr x p) q = pwr x (p * q)"
  "pwr x 0 = r1"
  "pwr x 1 = x"
  "mul x (add y z) = add (mul x y) (mul x z)"
  "pwr x (Suc q) = mul x (pwr x q)"
  "pwr x (2*n) = mul (pwr x n) (pwr x n)"
  "pwr x (Suc (2*n)) = mul x (mul (pwr x n) (pwr x n))"
proof -
  show "add (mul a m) (mul b m) = mul (add a b) m" using mul_d mul_c by simp
next show"add (mul a m) m = mul (add a r1) m" using mul_d mul_c mul_1 by simp
next show "add m (mul a m) = mul (add a r1) m" using mul_c mul_d mul_1 add_c by simp
next show "add m m = mul (add r1 r1) m" using mul_c mul_d mul_1 by simp
next show "add r0 a = a" using add_0 by simp
next show "add a r0 = a" using add_0 add_c by simp
next show "mul a b = mul b a" using mul_c by simp
next show "mul (add a b) c = add (mul a c) (mul b c)" using mul_c mul_d by simp
next show "mul r0 a = r0" using mul_0 by simp
next show "mul a r0 = r0" using mul_0 mul_c by simp
next show "mul r1 a = a" using mul_1 by simp
next show "mul a r1 = a" using mul_1 mul_c by simp
next show "mul (mul lx ly) (mul rx ry) = mul (mul lx rx) (mul ly ry)"
    using mul_c mul_a by simp
next show "mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry))"
    using mul_a by simp
next
  have "mul (mul lx ly) (mul rx ry) = mul (mul rx ry) (mul lx ly)" by (rule mul_c)
  also have "\<dots> = mul rx (mul ry (mul lx ly))" using mul_a by simp
  finally
  show "mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry)"
    using mul_c by simp
next show "mul (mul lx ly) rx = mul (mul lx rx) ly" using mul_c mul_a by simp
next
  show "mul (mul lx ly) rx = mul lx (mul ly rx)" by (simp add: mul_a)
next show "mul lx (mul rx ry) = mul (mul lx rx) ry" by (simp add: mul_a )
next show "mul lx (mul rx ry) = mul rx (mul lx ry)" by (simp add: mul_a,simp add: mul_c)
next show "add (add a b) (add c d) = add (add a c) (add b d)"
    using add_c add_a by simp
next show "add (add a b) c = add a (add b c)" using add_a by simp
next show "add a (add c d) = add c (add a d)"
    apply (simp add: add_a) by (simp only: add_c)
next show "add (add a b) c = add (add a c) b" using add_a add_c by simp
next show "add a c = add c a" by (rule add_c)
next show "add a (add c d) = add (add a c) d" using add_a by simp
next show "mul (pwr x p) (pwr x q) = pwr x (p + q)" by (rule mul_pwr)
next show "mul x (pwr x q) = pwr x (Suc q)" using pwr_Suc by simp
next show "mul (pwr x q) x = pwr x (Suc q)" using pwr_Suc mul_c by simp
next show "mul x x = pwr x 2" by (simp add: nat_number pwr_Suc pwr_0 mul_1 mul_c)
next show "pwr (mul x y) q = mul (pwr x q) (pwr y q)" by (rule pwr_mul)
next show "pwr (pwr x p) q = pwr x (p * q)" by (rule pwr_pwr)
next show "pwr x 0 = r1" using pwr_0 .
next show "pwr x 1 = x" by (simp add: nat_number pwr_Suc pwr_0 mul_1 mul_c)
next show "mul x (add y z) = add (mul x y) (mul x z)" using mul_d by simp
next show "pwr x (Suc q) = mul x (pwr x q)" using pwr_Suc by simp
next show "pwr x (2 * n) = mul (pwr x n) (pwr x n)" by (simp add: nat_number mul_pwr)
next show "pwr x (Suc (2 * n)) = mul x (mul (pwr x n) (pwr x n))"
    by (simp add: nat_number pwr_Suc mul_pwr)
qed


lemma "axioms" [normalizer
    semiring ops: semiring_ops
    semiring rules: semiring_rules]:
  "gb_semiring add mul pwr r0 r1" by fact

end

interpretation class_semiring: gb_semiring
    ["op +" "op *" "op ^" "0::'a::{comm_semiring_1, recpower}" "1"]
  by unfold_locales (auto simp add: ring_simps power_Suc)

lemmas nat_arith =
  add_nat_number_of diff_nat_number_of mult_nat_number_of eq_nat_number_of less_nat_number_of

lemma not_iszero_Numeral1: "\<not> iszero (Numeral1::'a::number_ring)"
  by (simp add: numeral_1_eq_1)
lemmas comp_arith = Let_def arith_simps nat_arith rel_simps if_False
  if_True add_0 add_Suc add_number_of_left mult_number_of_left
  numeral_1_eq_1[symmetric] Suc_eq_add_numeral_1
  numeral_0_eq_0[symmetric] numerals[symmetric] not_iszero_1
  iszero_number_of_1 iszero_number_of_0 nonzero_number_of_Min
  iszero_number_of_Pls iszero_0 not_iszero_Numeral1

lemmas semiring_norm = comp_arith

ML {*
local

open Conv;

fun numeral_is_const ct =
  can HOLogic.dest_number (Thm.term_of ct);

fun int_of_rat x =
  (case Rat.quotient_of_rat x of (i, 1) => i
  | _ => error "int_of_rat: bad int");

val numeral_conv =
  Simplifier.rewrite (HOL_basic_ss addsimps @{thms semiring_norm}) then_conv
  Simplifier.rewrite (HOL_basic_ss addsimps
    (@{thms numeral_1_eq_1} @ @{thms numeral_0_eq_0} @ @{thms numerals(1-2)}));

in

fun normalizer_funs key =
  NormalizerData.funs key
   {is_const = fn phi => numeral_is_const,
    dest_const = fn phi => fn ct =>
      Rat.rat_of_int (snd
        (HOLogic.dest_number (Thm.term_of ct)
          handle TERM _ => error "ring_dest_const")),
    mk_const = fn phi => fn cT => fn x => Numeral.mk_cnumber cT (int_of_rat x),
    conv = fn phi => K numeral_conv}

end
*}

declaration {* normalizer_funs @{thm class_semiring.axioms} *}


locale gb_ring = gb_semiring +
  fixes sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and neg :: "'a \<Rightarrow> 'a"
  assumes neg_mul: "neg x = mul (neg r1) x"
    and sub_add: "sub x y = add x (neg y)"
begin

lemma ring_ops:
  includes meta_term_syntax
  shows "TERM (sub x y)" and "TERM (neg x)" .

lemmas ring_rules = neg_mul sub_add

lemma "axioms" [normalizer
  semiring ops: semiring_ops
  semiring rules: semiring_rules
  ring ops: ring_ops
  ring rules: ring_rules]:
  "gb_ring add mul pwr r0 r1 sub neg" by fact

end


interpretation class_ring: gb_ring ["op +" "op *" "op ^"
    "0::'a::{comm_semiring_1,recpower,number_ring}" 1 "op -" "uminus"]
  by unfold_locales simp_all


declaration {* normalizer_funs @{thm class_ring.axioms} *}

use "Tools/Groebner_Basis/normalizer.ML"

method_setup sring_norm = {*
  Method.ctxt_args (fn ctxt => Method.SIMPLE_METHOD' (Normalizer.semiring_normalize_tac ctxt))
*} "semiring normalizer"


locale gb_field = gb_ring +
  fixes divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and inverse:: "'a \<Rightarrow> 'a"
  assumes divide: "divide x y = mul x (inverse y)"
     and inverse: "inverse x = divide r1 x"
begin

lemma "axioms" [normalizer
  semiring ops: semiring_ops
  semiring rules: semiring_rules
  ring ops: ring_ops
  ring rules: ring_rules]:
  "gb_field add mul pwr r0 r1 sub neg divide inverse" by fact

end


subsection {* Groebner Bases *}

locale semiringb = gb_semiring +
  assumes add_cancel: "add (x::'a) y = add x z \<longleftrightarrow> y = z"
  and add_mul_solve: "add (mul w y) (mul x z) =
    add (mul w z) (mul x y) \<longleftrightarrow> w = x \<or> y = z"
begin

lemma noteq_reduce: "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> add (mul a c) (mul b d) \<noteq> add (mul a d) (mul b c)"
proof-
  have "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> \<not> (a = b \<or> c = d)" by simp
  also have "\<dots> \<longleftrightarrow> add (mul a c) (mul b d) \<noteq> add (mul a d) (mul b c)"
    using add_mul_solve by blast
  finally show "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> add (mul a c) (mul b d) \<noteq> add (mul a d) (mul b c)"
    by simp
qed

lemma add_scale_eq_noteq: "\<lbrakk>r \<noteq> r0 ; (a = b) \<and> ~(c = d)\<rbrakk>
  \<Longrightarrow> add a (mul r c) \<noteq> add b (mul r d)"
proof(clarify)
  assume nz: "r\<noteq> r0" and cnd: "c\<noteq>d"
    and eq: "add b (mul r c) = add b (mul r d)"
  hence "mul r c = mul r d" using cnd add_cancel by simp
  hence "add (mul r0 d) (mul r c) = add (mul r0 c) (mul r d)"
    using mul_0 add_cancel by simp
  thus "False" using add_mul_solve nz cnd by simp
qed

declare "axioms" [normalizer del]

lemma "axioms" [normalizer
  semiring ops: semiring_ops
  semiring rules: semiring_rules
  idom rules: noteq_reduce add_scale_eq_noteq]:
  "semiringb add mul pwr r0 r1" by fact

end

locale ringb = semiringb + gb_ring
begin

declare "axioms" [normalizer del]

lemma "axioms" [normalizer
  semiring ops: semiring_ops
  semiring rules: semiring_rules
  ring ops: ring_ops
  ring rules: ring_rules
  idom rules: noteq_reduce add_scale_eq_noteq]:
  "ringb add mul pwr r0 r1 sub neg" by fact

end

lemma no_zero_divirors_neq0:
  assumes az: "(a::'a::no_zero_divisors) \<noteq> 0"
    and ab: "a*b = 0" shows "b = 0"
proof -
  { assume bz: "b \<noteq> 0"
    from no_zero_divisors [OF az bz] ab have False by blast }
  thus "b = 0" by blast
qed

interpretation class_ringb: ringb
  ["op +" "op *" "op ^" "0::'a::{idom,recpower,number_ring}" "1" "op -" "uminus"]
proof(unfold_locales, simp add: ring_simps power_Suc, auto)
  fix w x y z ::"'a::{idom,recpower,number_ring}"
  assume p: "w * y + x * z = w * z + x * y" and ynz: "y \<noteq> z"
  hence ynz': "y - z \<noteq> 0" by simp
  from p have "w * y + x* z - w*z - x*y = 0" by simp
  hence "w* (y - z) - x * (y - z) = 0" by (simp add: ring_simps)
  hence "(y - z) * (w - x) = 0" by (simp add: ring_simps)
  with  no_zero_divirors_neq0 [OF ynz']
  have "w - x = 0" by blast
  thus "w = x"  by simp
qed


declaration {* normalizer_funs @{thm class_ringb.axioms} *}

interpretation natgb: semiringb
  ["op +" "op *" "op ^" "0::nat" "1"]
proof (unfold_locales, simp add: ring_simps power_Suc)
  fix w x y z ::"nat"
  { assume p: "w * y + x * z = w * z + x * y" and ynz: "y \<noteq> z"
    hence "y < z \<or> y > z" by arith
    moreover {
      assume lt:"y <z" hence "\<exists>k. z = y + k \<and> k > 0" by (rule_tac x="z - y" in exI, auto)
      then obtain k where kp: "k>0" and yz:"z = y + k" by blast
      from p have "(w * y + x *y) + x*k = (w * y + x*y) + w*k" by (simp add: yz ring_simps)
      hence "x*k = w*k" by simp
      hence "w = x" using kp by (simp add: mult_cancel2) }
    moreover {
      assume lt: "y >z" hence "\<exists>k. y = z + k \<and> k>0" by (rule_tac x="y - z" in exI, auto)
      then obtain k where kp: "k>0" and yz:"y = z + k" by blast
      from p have "(w * z + x *z) + w*k = (w * z + x*z) + x*k" by (simp add: yz ring_simps)
      hence "w*k = x*k" by simp
      hence "w = x" using kp by (simp add: mult_cancel2)}
    ultimately have "w=x" by blast }
  thus "(w * y + x * z = w * z + x * y) = (w = x \<or> y = z)" by auto
qed

declaration {* normalizer_funs @{thm natgb.axioms} *}

locale fieldgb = ringb + gb_field
begin

declare "axioms" [normalizer del]

lemma "axioms" [normalizer
  semiring ops: semiring_ops
  semiring rules: semiring_rules
  ring ops: ring_ops
  ring rules: ring_rules
  idom rules: noteq_reduce add_scale_eq_noteq]:
  "fieldgb add mul pwr r0 r1 sub neg divide inverse" by unfold_locales
end


lemmas bool_simps = simp_thms(1-34)
lemma dnf:
    "(P & (Q | R)) = ((P&Q) | (P&R))" "((Q | R) & P) = ((Q&P) | (R&P))"
    "(P \<and> Q) = (Q \<and> P)" "(P \<or> Q) = (Q \<or> P)"
  by blast+

lemmas weak_dnf_simps = dnf bool_simps

lemma nnf_simps:
    "(\<not>(P \<and> Q)) = (\<not>P \<or> \<not>Q)" "(\<not>(P \<or> Q)) = (\<not>P \<and> \<not>Q)" "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
    "(P = Q) = ((P \<and> Q) \<or> (\<not>P \<and> \<not> Q))" "(\<not> \<not>(P)) = P"
  by blast+

lemma PFalse:
    "P \<equiv> False \<Longrightarrow> \<not> P"
    "\<not> P \<Longrightarrow> (P \<equiv> False)"
  by auto

use "Tools/Groebner_Basis/groebner.ML"

method_setup algebra =
{*
let
 fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()
 val addN = "add"
 val delN = "del"
 val any_keyword = keyword addN || keyword delN
 val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
in
fn src => Method.syntax 
    ((Scan.optional (keyword addN |-- thms) []) -- 
    (Scan.optional (keyword delN |-- thms) [])) src 
 #> (fn ((add_ths, del_ths), ctxt) => 
       Method.SIMPLE_METHOD' (Groebner.ring_tac add_ths del_ths ctxt))
end
*} "solve polynomial equations over (semi)rings using Groebner bases"

end
