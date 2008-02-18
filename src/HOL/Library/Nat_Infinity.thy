(*  Title:      HOL/Library/Nat_Infinity.thy
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen
*)

header {* Natural numbers with infinity *}

theory Nat_Infinity
imports ATP_Linkup
begin

subsection "Definitions"

text {*
  We extend the standard natural numbers by a special value indicating
  infinity.  This includes extending the ordering relations @{term "op
  <"} and @{term "op \<le>"}.
*}

datatype inat = Fin nat | Infty

notation (xsymbols)
  Infty  ("\<infinity>")

notation (HTML output)
  Infty  ("\<infinity>")

definition
  iSuc :: "inat => inat" where
  "iSuc i = (case i of Fin n => Fin (Suc n) | \<infinity> => \<infinity>)"

instantiation inat :: "{ord, zero}"
begin

definition
  Zero_inat_def: "0 == Fin 0"

definition
  iless_def: "m < n ==
    case m of Fin m1 => (case n of Fin n1 => m1 < n1 | \<infinity> => True)
    | \<infinity>  => False"

definition
  ile_def: "m \<le> n ==
    case n of Fin n1 => (case m of Fin m1 => m1 \<le> n1 | \<infinity> => False)
    | \<infinity>  => True"

instance ..

end

lemmas inat_defs = Zero_inat_def iSuc_def iless_def ile_def
lemmas inat_splits = inat.split inat.split_asm

text {*
  Below is a not quite complete set of theorems.  Use the method
  @{text "(simp add: inat_defs split:inat_splits, arith?)"} to prove
  new theorems or solve arithmetic subgoals involving @{typ inat} on
  the fly.
*}

subsection "Constructors"

lemma Fin_0: "Fin 0 = 0"
by (simp add: inat_defs split:inat_splits)

lemma Infty_ne_i0 [simp]: "\<infinity> \<noteq> 0"
by (simp add: inat_defs split:inat_splits)

lemma i0_ne_Infty [simp]: "0 \<noteq> \<infinity>"
by (simp add: inat_defs split:inat_splits)

lemma iSuc_Fin [simp]: "iSuc (Fin n) = Fin (Suc n)"
by (simp add: inat_defs split:inat_splits)

lemma iSuc_Infty [simp]: "iSuc \<infinity> = \<infinity>"
by (simp add: inat_defs split:inat_splits)

lemma iSuc_ne_0 [simp]: "iSuc n \<noteq> 0"
by (simp add: inat_defs split:inat_splits)

lemma iSuc_inject [simp]: "(iSuc x = iSuc y) = (x = y)"
by (simp add: inat_defs split:inat_splits)


subsection "Ordering relations"

instance inat :: linorder
proof
  fix x :: inat
  show "x \<le> x"
    by (simp add: inat_defs split: inat_splits)
next
  fix x y :: inat
  assume "x \<le> y" and "y \<le> x" thus "x = y"
    by (simp add: inat_defs split: inat_splits)
next
  fix x y z :: inat
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    by (simp add: inat_defs split: inat_splits)
next
  fix x y :: inat
  show "(x < y) = (x \<le> y \<and> x \<noteq> y)"
    by (simp add: inat_defs order_less_le split: inat_splits)
next
  fix x y :: inat
  show "x \<le> y \<or> y \<le> x"
    by (simp add: inat_defs linorder_linear split: inat_splits)
qed

lemma Infty_ilessE [elim!]: "\<infinity> < Fin m ==> R"
by (simp add: inat_defs split:inat_splits)

lemma iless_linear: "m < n \<or> m = n \<or> n < (m::inat)"
by (rule linorder_less_linear)

lemma iless_not_refl: "\<not> n < (n::inat)"
by (rule order_less_irrefl)

lemma iless_trans: "i < j ==> j < k ==> i < (k::inat)"
by (rule order_less_trans)

lemma iless_not_sym: "n < m ==> \<not> m < (n::inat)"
by (rule order_less_not_sym)

lemma Fin_iless_mono [simp]: "(Fin n < Fin m) = (n < m)"
by (simp add: inat_defs split:inat_splits)

lemma Fin_iless_Infty [simp]: "Fin n < \<infinity>"
by (simp add: inat_defs split:inat_splits)

lemma Infty_eq [simp]: "(n < \<infinity>) = (n \<noteq> \<infinity>)"
by (simp add: inat_defs split:inat_splits)

lemma i0_eq [simp]: "((0::inat) < n) = (n \<noteq> 0)"
by (fastsimp simp: inat_defs split:inat_splits)

lemma i0_iless_iSuc [simp]: "0 < iSuc n"
by (simp add: inat_defs split:inat_splits)

lemma not_ilessi0 [simp]: "\<not> n < (0::inat)"
by (simp add: inat_defs split:inat_splits)

lemma Fin_iless: "n < Fin m ==> \<exists>k. n = Fin k"
by (simp add: inat_defs split:inat_splits)

lemma iSuc_mono [simp]: "(iSuc n < iSuc m) = (n < m)"
by (simp add: inat_defs split:inat_splits)



lemma ile_def2: "(m \<le> n) = (m < n \<or> m = (n::inat))"
by (rule order_le_less)

lemma ile_refl [simp]: "n \<le> (n::inat)"
by (rule order_refl)

lemma ile_trans: "i \<le> j ==> j \<le> k ==> i \<le> (k::inat)"
by (rule order_trans)

lemma ile_iless_trans: "i \<le> j ==> j < k ==> i < (k::inat)"
by (rule order_le_less_trans)

lemma iless_ile_trans: "i < j ==> j \<le> k ==> i < (k::inat)"
by (rule order_less_le_trans)

lemma Infty_ub [simp]: "n \<le> \<infinity>"
by (simp add: inat_defs split:inat_splits)

lemma i0_lb [simp]: "(0::inat) \<le> n"
by (simp add: inat_defs split:inat_splits)

lemma Infty_ileE [elim!]: "\<infinity> \<le> Fin m ==> R"
by (simp add: inat_defs split:inat_splits)

lemma Fin_ile_mono [simp]: "(Fin n \<le> Fin m) = (n \<le> m)"
by (simp add: inat_defs split:inat_splits)

lemma ilessI1: "n \<le> m ==> n \<noteq> m ==> n < (m::inat)"
by (rule order_le_neq_trans)

lemma ileI1: "m < n ==> iSuc m \<le> n"
by (simp add: inat_defs split:inat_splits)

lemma Suc_ile_eq: "(Fin (Suc m) \<le> n) = (Fin m < n)"
by (simp add: inat_defs split:inat_splits, arith)

lemma iSuc_ile_mono [simp]: "(iSuc n \<le> iSuc m) = (n \<le> m)"
by (simp add: inat_defs split:inat_splits)

lemma iless_Suc_eq [simp]: "(Fin m < iSuc n) = (Fin m \<le> n)"
by (simp add: inat_defs split:inat_splits, arith)

lemma not_iSuc_ilei0 [simp]: "\<not> iSuc n \<le> 0"
by (simp add: inat_defs split:inat_splits)

lemma ile_iSuc [simp]: "n \<le> iSuc n"
by (simp add: inat_defs split:inat_splits)

lemma Fin_ile: "n \<le> Fin m ==> \<exists>k. n = Fin k"
by (simp add: inat_defs split:inat_splits)

lemma chain_incr: "\<forall>i. \<exists>j. Y i < Y j ==> \<exists>j. Fin k < Y j"
apply (induct_tac k)
 apply (simp (no_asm) only: Fin_0)
 apply (fast intro: ile_iless_trans [OF i0_lb])
apply (erule exE)
apply (drule spec)
apply (erule exE)
apply (drule ileI1)
apply (rule iSuc_Fin [THEN subst])
apply (rule exI)
apply (erule (1) ile_iless_trans)
done


subsection "Well-ordering"

lemma less_FinE:
  "[| n < Fin m; !!k. n = Fin k ==> k < m ==> P |] ==> P"
by (induct n) auto

lemma less_InftyE:
  "[| n < Infty; !!k. n = Fin k ==> P |] ==> P"
by (induct n) auto

lemma inat_less_induct:
  assumes prem: "!!n. \<forall>m::inat. m < n --> P m ==> P n" shows "P n"
proof -
  have P_Fin: "!!k. P (Fin k)"
    apply (rule nat_less_induct)
    apply (rule prem, clarify)
    apply (erule less_FinE, simp)
    done
  show ?thesis
  proof (induct n)
    fix nat
    show "P (Fin nat)" by (rule P_Fin)
  next
    show "P Infty"
      apply (rule prem, clarify)
      apply (erule less_InftyE)
      apply (simp add: P_Fin)
      done
  qed
qed

instance inat :: wellorder
proof
  show "wf {(x::inat, y::inat). x < y}"
  proof (rule wfUNIVI)
    fix P and x :: inat
    assume "\<forall>x::inat. (\<forall>y. (y, x) \<in> {(x, y). x < y} \<longrightarrow> P y) \<longrightarrow> P x"
    hence 1: "!!x::inat. ALL y. y < x --> P y ==> P x" by fast
    thus "P x" by (rule inat_less_induct)
  qed
qed

end
