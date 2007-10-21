(*  Title:      HOL/Nat.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Lawrence C Paulson and Markus Wenzel

Type "nat" is a linear order, and a datatype; arithmetic operators + -
and * (for div, mod and dvd, see theory Divides).
*)

header {* Natural numbers *}

theory Nat
imports Wellfounded_Recursion Ring_and_Field
uses
  "~~/src/Tools/rat.ML"
  "~~/src/Provers/Arith/cancel_sums.ML"
  ("arith_data.ML")
  "~~/src/Provers/Arith/fast_lin_arith.ML"
  ("Tools/lin_arith.ML")
  ("Tools/function_package/size.ML")
begin

subsection {* Type @{text ind} *}

typedecl ind

axiomatization
  Zero_Rep :: ind and
  Suc_Rep :: "ind => ind"
where
  -- {* the axiom of infinity in 2 parts *}
  inj_Suc_Rep:          "inj Suc_Rep" and
  Suc_Rep_not_Zero_Rep: "Suc_Rep x \<noteq> Zero_Rep"


subsection {* Type nat *}

text {* Type definition *}

inductive_set Nat :: "ind set"
where
    Zero_RepI: "Zero_Rep : Nat"
  | Suc_RepI: "i : Nat ==> Suc_Rep i : Nat"

global

typedef (open Nat)
  nat = Nat
proof
  show "Zero_Rep : Nat" by (rule Nat.Zero_RepI)
qed

consts
  Suc :: "nat => nat"

local

instance nat :: zero
  Zero_nat_def: "0 == Abs_Nat Zero_Rep" ..
lemmas [code func del] = Zero_nat_def

defs
  Suc_def:      "Suc == (%n. Abs_Nat (Suc_Rep (Rep_Nat n)))"

theorem nat_induct: "P 0 ==> (!!n. P n ==> P (Suc n)) ==> P n"
  apply (unfold Zero_nat_def Suc_def)
  apply (rule Rep_Nat_inverse [THEN subst]) -- {* types force good instantiation *}
  apply (erule Rep_Nat [THEN Nat.induct])
  apply (iprover elim: Abs_Nat_inverse [THEN subst])
  done

lemma Suc_not_Zero [iff]: "Suc m \<noteq> 0"
  by (simp add: Zero_nat_def Suc_def Abs_Nat_inject Rep_Nat Suc_RepI Zero_RepI
                Suc_Rep_not_Zero_Rep)

lemma Zero_not_Suc [iff]: "0 \<noteq> Suc m"
  by (rule not_sym, rule Suc_not_Zero not_sym)

lemma inj_Suc[simp]: "inj_on Suc N"
  by (simp add: Suc_def inj_on_def Abs_Nat_inject Rep_Nat Suc_RepI
                inj_Suc_Rep [THEN inj_eq] Rep_Nat_inject)

lemma Suc_Suc_eq [iff]: "(Suc m = Suc n) = (m = n)"
  by (rule inj_Suc [THEN inj_eq])

rep_datatype nat
  distinct  Suc_not_Zero Zero_not_Suc
  inject    Suc_Suc_eq
  induction nat_induct

declare nat.induct [case_names 0 Suc, induct type: nat]
declare nat.exhaust [case_names 0 Suc, cases type: nat]

lemmas nat_rec_0 = nat.recs(1)
  and nat_rec_Suc = nat.recs(2)

lemmas nat_case_0 = nat.cases(1)
  and nat_case_Suc = nat.cases(2)


text {* Injectiveness and distinctness lemmas *}

lemma Suc_neq_Zero: "Suc m = 0 ==> R"
  by (rule notE, rule Suc_not_Zero)

lemma Zero_neq_Suc: "0 = Suc m ==> R"
  by (rule Suc_neq_Zero, erule sym)

lemma Suc_inject: "Suc x = Suc y ==> x = y"
  by (rule inj_Suc [THEN injD])

lemma nat_not_singleton: "(\<forall>x. x = (0::nat)) = False"
  by auto

lemma n_not_Suc_n: "n \<noteq> Suc n"
  by (induct n) simp_all

lemma Suc_n_not_n: "Suc t \<noteq> t"
  by (rule not_sym, rule n_not_Suc_n)


text {* A special form of induction for reasoning
  about @{term "m < n"} and @{term "m - n"} *}

theorem diff_induct: "(!!x. P x 0) ==> (!!y. P 0 (Suc y)) ==>
    (!!x y. P x y ==> P (Suc x) (Suc y)) ==> P m n"
  apply (rule_tac x = m in spec)
  apply (induct n)
  prefer 2
  apply (rule allI)
  apply (induct_tac x, iprover+)
  done


subsection {* Arithmetic operators *}

instance nat :: "{one, plus, minus, times}"
  One_nat_def [simp]: "1 == Suc 0" ..

primrec
  add_0:    "0 + n = n"
  add_Suc:  "Suc m + n = Suc (m + n)"

primrec
  diff_0:   "m - 0 = m"
  diff_Suc: "m - Suc n = (case m - n of 0 => 0 | Suc k => k)"

primrec
  mult_0:   "0 * n = 0"
  mult_Suc: "Suc m * n = n + (m * n)"


subsection {* Orders on @{typ nat} *}

definition
  pred_nat :: "(nat * nat) set" where
  "pred_nat = {(m, n). n = Suc m}"

instance nat :: ord
  less_def: "m < n == (m, n) : pred_nat^+"
  le_def:   "m \<le> (n::nat) == ~ (n < m)" ..

lemmas [code func del] = less_def le_def

lemma wf_pred_nat: "wf pred_nat"
  apply (unfold wf_def pred_nat_def, clarify)
  apply (induct_tac x, blast+)
  done

lemma wf_less: "wf {(x, y::nat). x < y}"
  apply (unfold less_def)
  apply (rule wf_pred_nat [THEN wf_trancl, THEN wf_subset], blast)
  done

lemma less_eq: "((m, n) : pred_nat^+) = (m < n)"
  apply (unfold less_def)
  apply (rule refl)
  done

subsubsection {* Introduction properties *}

lemma less_trans: "i < j ==> j < k ==> i < (k::nat)"
  apply (unfold less_def)
  apply (rule trans_trancl [THEN transD], assumption+)
  done

lemma lessI [iff]: "n < Suc n"
  apply (unfold less_def pred_nat_def)
  apply (simp add: r_into_trancl)
  done

lemma less_SucI: "i < j ==> i < Suc j"
  apply (rule less_trans, assumption)
  apply (rule lessI)
  done

lemma zero_less_Suc [iff]: "0 < Suc n"
  apply (induct n)
  apply (rule lessI)
  apply (erule less_trans)
  apply (rule lessI)
  done

subsubsection {* Elimination properties *}

lemma less_not_sym: "n < m ==> ~ m < (n::nat)"
  apply (unfold less_def)
  apply (blast intro: wf_pred_nat wf_trancl [THEN wf_asym])
  done

lemma less_asym:
  assumes h1: "(n::nat) < m" and h2: "~ P ==> m < n" shows P
  apply (rule contrapos_np)
  apply (rule less_not_sym)
  apply (rule h1)
  apply (erule h2)
  done

lemma less_not_refl: "~ n < (n::nat)"
  apply (unfold less_def)
  apply (rule wf_pred_nat [THEN wf_trancl, THEN wf_not_refl])
  done

lemma less_irrefl [elim!]: "(n::nat) < n ==> R"
  by (rule notE, rule less_not_refl)

lemma less_not_refl2: "n < m ==> m \<noteq> (n::nat)" by blast

lemma less_not_refl3: "(s::nat) < t ==> s \<noteq> t"
  by (rule not_sym, rule less_not_refl2)

lemma lessE:
  assumes major: "i < k"
  and p1: "k = Suc i ==> P" and p2: "!!j. i < j ==> k = Suc j ==> P"
  shows P
  apply (rule major [unfolded less_def pred_nat_def, THEN tranclE], simp_all)
  apply (erule p1)
  apply (rule p2)
  apply (simp add: less_def pred_nat_def, assumption)
  done

lemma not_less0 [iff]: "~ n < (0::nat)"
  by (blast elim: lessE)

lemma less_zeroE: "(n::nat) < 0 ==> R"
  by (rule notE, rule not_less0)

lemma less_SucE: assumes major: "m < Suc n"
  and less: "m < n ==> P" and eq: "m = n ==> P" shows P
  apply (rule major [THEN lessE])
  apply (rule eq, blast)
  apply (rule less, blast)
  done

lemma less_Suc_eq: "(m < Suc n) = (m < n | m = n)"
  by (blast elim!: less_SucE intro: less_trans)

lemma less_one [iff,noatp]: "(n < (1::nat)) = (n = 0)"
  by (simp add: less_Suc_eq)

lemma less_Suc0 [iff]: "(n < Suc 0) = (n = 0)"
  by (simp add: less_Suc_eq)

lemma Suc_mono: "m < n ==> Suc m < Suc n"
  by (induct n) (fast elim: less_trans lessE)+

text {* "Less than" is a linear ordering *}
lemma less_linear: "m < n | m = n | n < (m::nat)"
  apply (induct m)
  apply (induct n)
  apply (rule refl [THEN disjI1, THEN disjI2])
  apply (rule zero_less_Suc [THEN disjI1])
  apply (blast intro: Suc_mono less_SucI elim: lessE)
  done

text {* "Less than" is antisymmetric, sort of *}
lemma less_antisym: "\<lbrakk> \<not> n < m; n < Suc m \<rbrakk> \<Longrightarrow> m = n"
  apply(simp only:less_Suc_eq)
  apply blast
  done

lemma nat_neq_iff: "((m::nat) \<noteq> n) = (m < n | n < m)"
  using less_linear by blast

lemma nat_less_cases: assumes major: "(m::nat) < n ==> P n m"
  and eqCase: "m = n ==> P n m" and lessCase: "n<m ==> P n m"
  shows "P n m"
  apply (rule less_linear [THEN disjE])
  apply (erule_tac [2] disjE)
  apply (erule lessCase)
  apply (erule sym [THEN eqCase])
  apply (erule major)
  done


subsubsection {* Inductive (?) properties *}

lemma Suc_lessI: "m < n ==> Suc m \<noteq> n ==> Suc m < n"
  apply (simp add: nat_neq_iff)
  apply (blast elim!: less_irrefl less_SucE elim: less_asym)
  done

lemma Suc_lessD: "Suc m < n ==> m < n"
  apply (induct n)
  apply (fast intro!: lessI [THEN less_SucI] elim: less_trans lessE)+
  done

lemma Suc_lessE: assumes major: "Suc i < k"
  and minor: "!!j. i < j ==> k = Suc j ==> P" shows P
  apply (rule major [THEN lessE])
  apply (erule lessI [THEN minor])
  apply (erule Suc_lessD [THEN minor], assumption)
  done

lemma Suc_less_SucD: "Suc m < Suc n ==> m < n"
  by (blast elim: lessE dest: Suc_lessD)

lemma Suc_less_eq [iff, code]: "(Suc m < Suc n) = (m < n)"
  apply (rule iffI)
  apply (erule Suc_less_SucD)
  apply (erule Suc_mono)
  done

lemma less_trans_Suc:
  assumes le: "i < j" shows "j < k ==> Suc i < k"
  apply (induct k, simp_all)
  apply (insert le)
  apply (simp add: less_Suc_eq)
  apply (blast dest: Suc_lessD)
  done

lemma [code]: "((n::nat) < 0) = False" by simp
lemma [code]: "(0 < Suc n) = True" by simp

text {* Can be used with @{text less_Suc_eq} to get @{term "n = m | n < m"} *}
lemma not_less_eq: "(~ m < n) = (n < Suc m)"
  by (induct m n rule: diff_induct) simp_all

text {* Complete induction, aka course-of-values induction *}
lemma nat_less_induct:
  assumes prem: "!!n. \<forall>m::nat. m < n --> P m ==> P n" shows "P n"
  apply (induct n rule: wf_induct [OF wf_pred_nat [THEN wf_trancl]])
  apply (rule prem)
  apply (unfold less_def, assumption)
  done

lemmas less_induct = nat_less_induct [rule_format, case_names less]


text {* Properties of "less than or equal" *}

text {* Was @{text le_eq_less_Suc}, but this orientation is more useful *}
lemma less_Suc_eq_le: "(m < Suc n) = (m \<le> n)"
  unfolding le_def by (rule not_less_eq [symmetric])

lemma le_imp_less_Suc: "m \<le> n ==> m < Suc n"
  by (rule less_Suc_eq_le [THEN iffD2])

lemma le0 [iff]: "(0::nat) \<le> n"
  unfolding le_def by (rule not_less0)

lemma Suc_n_not_le_n: "~ Suc n \<le> n"
  by (simp add: le_def)

lemma le_0_eq [iff]: "((i::nat) \<le> 0) = (i = 0)"
  by (induct i) (simp_all add: le_def)

lemma le_Suc_eq: "(m \<le> Suc n) = (m \<le> n | m = Suc n)"
  by (simp del: less_Suc_eq_le add: less_Suc_eq_le [symmetric] less_Suc_eq)

lemma le_SucE: "m \<le> Suc n ==> (m \<le> n ==> R) ==> (m = Suc n ==> R) ==> R"
  by (drule le_Suc_eq [THEN iffD1], iprover+)

lemma Suc_leI: "m < n ==> Suc(m) \<le> n"
  apply (simp add: le_def less_Suc_eq)
  apply (blast elim!: less_irrefl less_asym)
  done -- {* formerly called lessD *}

lemma Suc_leD: "Suc(m) \<le> n ==> m \<le> n"
  by (simp add: le_def less_Suc_eq)

text {* Stronger version of @{text Suc_leD} *}
lemma Suc_le_lessD: "Suc m \<le> n ==> m < n"
  apply (simp add: le_def less_Suc_eq)
  using less_linear
  apply blast
  done

lemma Suc_le_eq: "(Suc m \<le> n) = (m < n)"
  by (blast intro: Suc_leI Suc_le_lessD)

lemma le_SucI: "m \<le> n ==> m \<le> Suc n"
  by (unfold le_def) (blast dest: Suc_lessD)

lemma less_imp_le: "m < n ==> m \<le> (n::nat)"
  by (unfold le_def) (blast elim: less_asym)

text {* For instance, @{text "(Suc m < Suc n) = (Suc m \<le> n) = (m < n)"} *}
lemmas le_simps = less_imp_le less_Suc_eq_le Suc_le_eq


text {* Equivalence of @{term "m \<le> n"} and @{term "m < n | m = n"} *}

lemma le_imp_less_or_eq: "m \<le> n ==> m < n | m = (n::nat)"
  unfolding le_def
  using less_linear
  by (blast elim: less_irrefl less_asym)

lemma less_or_eq_imp_le: "m < n | m = n ==> m \<le> (n::nat)"
  unfolding le_def
  using less_linear
  by (blast elim!: less_irrefl elim: less_asym)

lemma le_eq_less_or_eq: "(m \<le> (n::nat)) = (m < n | m=n)"
  by (iprover intro: less_or_eq_imp_le le_imp_less_or_eq)

text {* Useful with @{text blast}. *}
lemma eq_imp_le: "(m::nat) = n ==> m \<le> n"
  by (rule less_or_eq_imp_le) (rule disjI2)

lemma le_refl: "n \<le> (n::nat)"
  by (simp add: le_eq_less_or_eq)

lemma le_less_trans: "[| i \<le> j; j < k |] ==> i < (k::nat)"
  by (blast dest!: le_imp_less_or_eq intro: less_trans)

lemma less_le_trans: "[| i < j; j \<le> k |] ==> i < (k::nat)"
  by (blast dest!: le_imp_less_or_eq intro: less_trans)

lemma le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::nat)"
  by (blast dest!: le_imp_less_or_eq intro: less_or_eq_imp_le less_trans)

lemma le_anti_sym: "[| m \<le> n; n \<le> m |] ==> m = (n::nat)"
  by (blast dest!: le_imp_less_or_eq elim!: less_irrefl elim: less_asym)

lemma Suc_le_mono [iff]: "(Suc n \<le> Suc m) = (n \<le> m)"
  by (simp add: le_simps)

text {* Axiom @{text order_less_le} of class @{text order}: *}
lemma nat_less_le: "((m::nat) < n) = (m \<le> n & m \<noteq> n)"
  by (simp add: le_def nat_neq_iff) (blast elim!: less_asym)

lemma le_neq_implies_less: "(m::nat) \<le> n ==> m \<noteq> n ==> m < n"
  by (rule iffD2, rule nat_less_le, rule conjI)

text {* Axiom @{text linorder_linear} of class @{text linorder}: *}
lemma nat_le_linear: "(m::nat) \<le> n | n \<le> m"
  apply (simp add: le_eq_less_or_eq)
  using less_linear by blast

text {* Type @{typ nat} is a wellfounded linear order *}

instance nat :: wellorder
  by intro_classes
    (assumption |
      rule le_refl le_trans le_anti_sym nat_less_le nat_le_linear wf_less)+

lemmas linorder_neqE_nat = linorder_neqE [where 'a = nat]

lemma not_less_less_Suc_eq: "~ n < m ==> (n < Suc m) = (n = m)"
  by (blast elim!: less_SucE)

text {*
  Rewrite @{term "n < Suc m"} to @{term "n = m"}
  if @{term "~ n < m"} or @{term "m \<le> n"} hold.
  Not suitable as default simprules because they often lead to looping
*}
lemma le_less_Suc_eq: "m \<le> n ==> (n < Suc m) = (n = m)"
  by (rule not_less_less_Suc_eq, rule leD)

lemmas not_less_simps = not_less_less_Suc_eq le_less_Suc_eq


text {*
  Re-orientation of the equations @{text "0 = x"} and @{text "1 = x"}.
  No longer added as simprules (they loop)
  but via @{text reorient_simproc} in Bin
*}

text {* Polymorphic, not just for @{typ nat} *}
lemma zero_reorient: "(0 = x) = (x = 0)"
  by auto

lemma one_reorient: "(1 = x) = (x = 1)"
  by auto

text {* These two rules ease the use of primitive recursion.
NOTE USE OF @{text "=="} *}
lemma def_nat_rec_0: "(!!n. f n == nat_rec c h n) ==> f 0 = c"
  by simp

lemma def_nat_rec_Suc: "(!!n. f n == nat_rec c h n) ==> f (Suc n) = h n (f n)"
  by simp

lemma not0_implies_Suc: "n \<noteq> 0 ==> \<exists>m. n = Suc m"
  by (cases n) simp_all

lemma gr_implies_not0: fixes n :: nat shows "m<n ==> n \<noteq> 0"
  by (cases n) simp_all

lemma neq0_conv: fixes n :: nat shows "(n \<noteq> 0) = (0 < n)"
  by (cases n) simp_all

text {* This theorem is useful with @{text blast} *}
lemma gr0I: "((n::nat) = 0 ==> False) ==> 0 < n"
  by (rule iffD1, rule neq0_conv, iprover)

lemma gr0_conv_Suc: "(0 < n) = (\<exists>m. n = Suc m)"
  by (fast intro: not0_implies_Suc)

lemma not_gr0 [iff,noatp]: "!!n::nat. (~ (0 < n)) = (n = 0)"
using neq0_conv by blast

lemma Suc_le_D: "(Suc n \<le> m') ==> (? m. m' = Suc m)"
  by (induct m') simp_all

text {* Useful in certain inductive arguments *}
lemma less_Suc_eq_0_disj: "(m < Suc n) = (m = 0 | (\<exists>j. m = Suc j & j < n))"
  by (cases m) simp_all

lemma nat_induct2: "[|P 0; P (Suc 0); !!k. P k ==> P (Suc (Suc k))|] ==> P n"
  apply (rule nat_less_induct)
  apply (case_tac n)
  apply (case_tac [2] nat)
  apply (blast intro: less_trans)+
  done


subsection {* @{text LEAST} theorems for type @{typ nat}*}

lemma Least_Suc:
     "[| P n; ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P(Suc m))"
  apply (case_tac "n", auto)
  apply (frule LeastI)
  apply (drule_tac P = "%x. P (Suc x) " in LeastI)
  apply (subgoal_tac " (LEAST x. P x) \<le> Suc (LEAST x. P (Suc x))")
  apply (erule_tac [2] Least_le)
  apply (case_tac "LEAST x. P x", auto)
  apply (drule_tac P = "%x. P (Suc x) " in Least_le)
  apply (blast intro: order_antisym)
  done

lemma Least_Suc2:
     "[|P n; Q m; ~P 0; !k. P (Suc k) = Q k|] ==> Least P = Suc (Least Q)"
  by (erule (1) Least_Suc [THEN ssubst], simp)


subsection {* @{term min} and @{term max} *}

lemma mono_Suc: "mono Suc"
  by (rule monoI) simp

lemma min_0L [simp]: "min 0 n = (0::nat)"
  by (rule min_leastL) simp

lemma min_0R [simp]: "min n 0 = (0::nat)"
  by (rule min_leastR) simp

lemma min_Suc_Suc [simp]: "min (Suc m) (Suc n) = Suc (min m n)"
  by (simp add: mono_Suc min_of_mono)

lemma min_Suc1:
   "min (Suc n) m = (case m of 0 => 0 | Suc m' => Suc(min n m'))"
  by (simp split: nat.split)

lemma min_Suc2:
   "min m (Suc n) = (case m of 0 => 0 | Suc m' => Suc(min m' n))"
  by (simp split: nat.split)

lemma max_0L [simp]: "max 0 n = (n::nat)"
  by (rule max_leastL) simp

lemma max_0R [simp]: "max n 0 = (n::nat)"
  by (rule max_leastR) simp

lemma max_Suc_Suc [simp]: "max (Suc m) (Suc n) = Suc(max m n)"
  by (simp add: mono_Suc max_of_mono)

lemma max_Suc1:
   "max (Suc n) m = (case m of 0 => Suc n | Suc m' => Suc(max n m'))"
  by (simp split: nat.split)

lemma max_Suc2:
   "max m (Suc n) = (case m of 0 => Suc n | Suc m' => Suc(max m' n))"
  by (simp split: nat.split)


subsection {* Basic rewrite rules for the arithmetic operators *}

text {* Difference *}

lemma diff_0_eq_0 [simp, code]: "0 - n = (0::nat)"
  by (induct n) simp_all

lemma diff_Suc_Suc [simp, code]: "Suc(m) - Suc(n) = m - n"
  by (induct n) simp_all


text {*
  Could be (and is, below) generalized in various ways
  However, none of the generalizations are currently in the simpset,
  and I dread to think what happens if I put them in
*}
lemma Suc_pred [simp]: "0 \<noteq> n ==> Suc (n - Suc 0) = n"
by (simp split add: nat.split)

declare diff_Suc [simp del, code del]


subsection {* Addition *}

lemma add_0_right [simp]: "m + 0 = (m::nat)"
  by (induct m) simp_all

lemma add_Suc_right [simp]: "m + Suc n = Suc (m + n)"
  by (induct m) simp_all

lemma add_Suc_shift [code]: "Suc m + n = m + Suc n"
  by simp


text {* Associative law for addition *}
lemma nat_add_assoc: "(m + n) + k = m + ((n + k)::nat)"
  by (induct m) simp_all

text {* Commutative law for addition *}
lemma nat_add_commute: "m + n = n + (m::nat)"
  by (induct m) simp_all

lemma nat_add_left_commute: "x + (y + z) = y + ((x + z)::nat)"
  apply (rule mk_left_commute [of "op +"])
  apply (rule nat_add_assoc)
  apply (rule nat_add_commute)
  done

lemma nat_add_left_cancel [simp]: "(k + m = k + n) = (m = (n::nat))"
  by (induct k) simp_all

lemma nat_add_right_cancel [simp]: "(m + k = n + k) = (m=(n::nat))"
  by (induct k) simp_all

lemma nat_add_left_cancel_le [simp]: "(k + m \<le> k + n) = (m\<le>(n::nat))"
  by (induct k) simp_all

lemma nat_add_left_cancel_less [simp]: "(k + m < k + n) = (m<(n::nat))"
  by (induct k) simp_all

text {* Reasoning about @{text "m + 0 = 0"}, etc. *}

lemma add_is_0 [iff]: fixes m :: nat shows "(m + n = 0) = (m = 0 & n = 0)"
  by (cases m) simp_all

lemma add_is_1: "(m+n= Suc 0) = (m= Suc 0 & n=0 | m=0 & n= Suc 0)"
  by (cases m) simp_all

lemma one_is_add: "(Suc 0 = m + n) = (m = Suc 0 & n = 0 | m = 0 & n = Suc 0)"
  by (rule trans, rule eq_commute, rule add_is_1)

lemma add_gr_0 [iff]: "!!m::nat. (m + n \<noteq> 0) = (m\<noteq>0 | n\<noteq>0)"
by simp

lemma add_eq_self_zero: "!!m::nat. m + n = m ==> n = 0"
  apply (drule add_0_right [THEN ssubst])
  apply (simp add: nat_add_assoc del: add_0_right)
  done

lemma inj_on_add_nat[simp]: "inj_on (%n::nat. n+k) N"
  apply (induct k)
   apply simp
  apply(drule comp_inj_on[OF _ inj_Suc])
  apply (simp add:o_def)
  done


subsection {* Multiplication *}

text {* right annihilation in product *}
lemma mult_0_right [simp]: "(m::nat) * 0 = 0"
  by (induct m) simp_all

text {* right successor law for multiplication *}
lemma mult_Suc_right [simp]: "m * Suc n = m + (m * n)"
  by (induct m) (simp_all add: nat_add_left_commute)

text {* Commutative law for multiplication *}
lemma nat_mult_commute: "m * n = n * (m::nat)"
  by (induct m) simp_all

text {* addition distributes over multiplication *}
lemma add_mult_distrib: "(m + n) * k = (m * k) + ((n * k)::nat)"
  by (induct m) (simp_all add: nat_add_assoc nat_add_left_commute)

lemma add_mult_distrib2: "k * (m + n) = (k * m) + ((k * n)::nat)"
  by (induct m) (simp_all add: nat_add_assoc)

text {* Associative law for multiplication *}
lemma nat_mult_assoc: "(m * n) * k = m * ((n * k)::nat)"
  by (induct m) (simp_all add: add_mult_distrib)


text{*The naturals form a @{text comm_semiring_1_cancel}*}
instance nat :: comm_semiring_1_cancel
proof
  fix i j k :: nat
  show "(i + j) + k = i + (j + k)" by (rule nat_add_assoc)
  show "i + j = j + i" by (rule nat_add_commute)
  show "0 + i = i" by simp
  show "(i * j) * k = i * (j * k)" by (rule nat_mult_assoc)
  show "i * j = j * i" by (rule nat_mult_commute)
  show "1 * i = i" by simp
  show "(i + j) * k = i * k + j * k" by (simp add: add_mult_distrib)
  show "0 \<noteq> (1::nat)" by simp
  assume "k+i = k+j" thus "i=j" by simp
qed

lemma mult_is_0 [simp]: "((m::nat) * n = 0) = (m=0 | n=0)"
  apply (induct m)
   apply (induct_tac [2] n)
    apply simp_all
  done


subsection {* Monotonicity of Addition *}

text {* strict, in 1st argument *}
lemma add_less_mono1: "i < j ==> i + k < j + (k::nat)"
  by (induct k) simp_all

text {* strict, in both arguments *}
lemma add_less_mono: "[|i < j; k < l|] ==> i + k < j + (l::nat)"
  apply (rule add_less_mono1 [THEN less_trans], assumption+)
  apply (induct j, simp_all)
  done

text {* Deleted @{text less_natE}; use @{text "less_imp_Suc_add RS exE"} *}
lemma less_imp_Suc_add: "m < n ==> (\<exists>k. n = Suc (m + k))"
  apply (induct n)
  apply (simp_all add: order_le_less)
  apply (blast elim!: less_SucE
               intro!: add_0_right [symmetric] add_Suc_right [symmetric])
  done

text {* strict, in 1st argument; proof is by induction on @{text "k > 0"} *}
lemma mult_less_mono2: "(i::nat) < j ==> 0<k ==> k * i < k * j"
apply(auto simp: gr0_conv_Suc)
apply (induct_tac m)
apply (simp_all add: add_less_mono)
done


text{*The naturals form an ordered @{text comm_semiring_1_cancel}*}
instance nat :: ordered_semidom
proof
  fix i j k :: nat
  show "0 < (1::nat)" by simp
  show "i \<le> j ==> k + i \<le> k + j" by simp
  show "i < j ==> 0 < k ==> k * i < k * j" by (simp add: mult_less_mono2)
qed

lemma nat_mult_1: "(1::nat) * n = n"
  by simp

lemma nat_mult_1_right: "n * (1::nat) = n"
  by simp


subsection {* Additional theorems about "less than" *}

text{*An induction rule for estabilishing binary relations*}
lemma less_Suc_induct:
  assumes less:  "i < j"
     and  step:  "!!i. P i (Suc i)"
     and  trans: "!!i j k. P i j ==> P j k ==> P i k"
  shows "P i j"
proof -
  from less obtain k where j: "j = Suc(i+k)" by (auto dest: less_imp_Suc_add)
  have "P i (Suc (i + k))"
  proof (induct k)
    case 0
    show ?case by (simp add: step)
  next
    case (Suc k)
    thus ?case by (auto intro: assms)
  qed
  thus "P i j" by (simp add: j)
qed

text {* The method of infinite descent, frequently used in number theory.
Provided by Roelof Oosterhuis.
$P(n)$ is true for all $n\in\mathbb{N}$ if
\begin{itemize}
  \item case ``0'': given $n=0$ prove $P(n)$,
  \item case ``smaller'': given $n>0$ and $\neg P(n)$ prove there exists
        a smaller integer $m$ such that $\neg P(m)$.
\end{itemize} *}

lemma infinite_descent0[case_names 0 smaller]: 
  "\<lbrakk> P 0; !!n. n>0 \<Longrightarrow> \<not> P n \<Longrightarrow> (\<exists>m::nat. m < n \<and> \<not>P m) \<rbrakk> \<Longrightarrow> P n"
by (induct n rule: less_induct, case_tac "n>0", auto)

text{* A compact version without explicit base case: *}
lemma infinite_descent:
  "\<lbrakk> !!n::nat. \<not> P n \<Longrightarrow>  \<exists>m<n. \<not>  P m \<rbrakk> \<Longrightarrow>  P n"
by (induct n rule: less_induct, auto)


text {* Infinite descent using a mapping to $\mathbb{N}$:
$P(x)$ is true for all $x\in D$ if there exists a $V: D \to \mathbb{N}$ and
\begin{itemize}
\item case ``0'': given $V(x)=0$ prove $P(x)$,
\item case ``smaller'': given $V(x)>0$ and $\neg P(x)$ prove there exists a $y \in D$ such that $V(y)<V(x)$ and $~\neg P(y)$.
\end{itemize}
NB: the proof also shows how to use the previous lemma. *}
corollary infinite_descent0_measure[case_names 0 smaller]:
assumes 0: "!!x. V x = (0::nat) \<Longrightarrow> P x"
and     1: "!!x. V x > 0 \<Longrightarrow> \<not>P x \<Longrightarrow> (\<exists>y. V y < V x \<and> \<not>P y)"
shows "P x"
proof -
  obtain n where "n = V x" by auto
  moreover have "!!x. V x = n \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent0)
    case 0 -- "i.e. $V(x) = 0$"
    with 0 show "P x" by auto
  next -- "now $n>0$ and $P(x)$ does not hold for some $x$ with $V(x)=n$"
    case (smaller n)
    then obtain x where vxn: "V x = n " and "V x > 0 \<and> \<not> P x" by auto
    with 1 obtain y where "V y < V x \<and> \<not> P y" by auto
    with vxn obtain m where "m = V y \<and> m<n \<and> \<not> P y" by auto
    thus ?case by auto
  qed
  ultimately show "P x" by auto
qed

text{* Again, without explicit base case: *}
lemma infinite_descent_measure:
assumes "!!x. \<not> P x \<Longrightarrow> \<exists>y. (V::'a\<Rightarrow>nat) y < V x \<and> \<not> P y" shows "P x"
proof -
  from assms obtain n where "n = V x" by auto
  moreover have "!!x. V x = n \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent, auto)
    fix x assume "\<not> P x"
    with assms show "\<exists>m < V x. \<exists>y. V y = m \<and> \<not> P y" by auto
  qed
  ultimately show "P x" by auto
qed



text {* A [clumsy] way of lifting @{text "<"}
  monotonicity to @{text "\<le>"} monotonicity *}
lemma less_mono_imp_le_mono:
  "\<lbrakk> !!i j::nat. i < j \<Longrightarrow> f i < f j; i \<le> j \<rbrakk> \<Longrightarrow> f i \<le> ((f j)::nat)"
by (simp add: order_le_less) (blast)


text {* non-strict, in 1st argument *}
lemma add_le_mono1: "i \<le> j ==> i + k \<le> j + (k::nat)"
by (rule add_right_mono)

text {* non-strict, in both arguments *}
lemma add_le_mono: "[| i \<le> j;  k \<le> l |] ==> i + k \<le> j + (l::nat)"
by (rule add_mono)

lemma le_add2: "n \<le> ((m + n)::nat)"
by (insert add_right_mono [of 0 m n], simp)

lemma le_add1: "n \<le> ((n + m)::nat)"
by (simp add: add_commute, rule le_add2)

lemma less_add_Suc1: "i < Suc (i + m)"
by (rule le_less_trans, rule le_add1, rule lessI)

lemma less_add_Suc2: "i < Suc (m + i)"
by (rule le_less_trans, rule le_add2, rule lessI)

lemma less_iff_Suc_add: "(m < n) = (\<exists>k. n = Suc (m + k))"
by (iprover intro!: less_add_Suc1 less_imp_Suc_add)

lemma trans_le_add1: "(i::nat) \<le> j ==> i \<le> j + m"
by (rule le_trans, assumption, rule le_add1)

lemma trans_le_add2: "(i::nat) \<le> j ==> i \<le> m + j"
by (rule le_trans, assumption, rule le_add2)

lemma trans_less_add1: "(i::nat) < j ==> i < j + m"
by (rule less_le_trans, assumption, rule le_add1)

lemma trans_less_add2: "(i::nat) < j ==> i < m + j"
by (rule less_le_trans, assumption, rule le_add2)

lemma add_lessD1: "i + j < (k::nat) ==> i < k"
apply (rule le_less_trans [of _ "i+j"])
apply (simp_all add: le_add1)
done

lemma not_add_less1 [iff]: "~ (i + j < (i::nat))"
apply (rule notI)
apply (erule add_lessD1 [THEN less_irrefl])
done

lemma not_add_less2 [iff]: "~ (j + i < (i::nat))"
by (simp add: add_commute not_add_less1)

lemma add_leD1: "m + k \<le> n ==> m \<le> (n::nat)"
apply (rule order_trans [of _ "m+k"])
apply (simp_all add: le_add1)
done

lemma add_leD2: "m + k \<le> n ==> k \<le> (n::nat)"
apply (simp add: add_commute)
apply (erule add_leD1)
done

lemma add_leE: "(m::nat) + k \<le> n ==> (m \<le> n ==> k \<le> n ==> R) ==> R"
by (blast dest: add_leD1 add_leD2)

text {* needs @{text "!!k"} for @{text add_ac} to work *}
lemma less_add_eq_less: "!!k::nat. k < l ==> m + l = k + n ==> m < n"
by (force simp del: add_Suc_right
    simp add: less_iff_Suc_add add_Suc_right [symmetric] add_ac)


subsection {* Difference *}

lemma diff_self_eq_0 [simp]: "(m::nat) - m = 0"
by (induct m) simp_all

text {* Addition is the inverse of subtraction:
  if @{term "n \<le> m"} then @{term "n + (m - n) = m"}. *}
lemma add_diff_inverse: "~  m < n ==> n + (m - n) = (m::nat)"
by (induct m n rule: diff_induct) simp_all

lemma le_add_diff_inverse [simp]: "n \<le> m ==> n + (m - n) = (m::nat)"
by (simp add: add_diff_inverse linorder_not_less)

lemma le_add_diff_inverse2 [simp]: "n \<le> m ==> (m - n) + n = (m::nat)"
by (simp add: le_add_diff_inverse add_commute)


subsection {* More results about difference *}

lemma Suc_diff_le: "n \<le> m ==> Suc m - n = Suc (m - n)"
by (induct m n rule: diff_induct) simp_all

lemma diff_less_Suc: "m - n < Suc m"
apply (induct m n rule: diff_induct)
apply (erule_tac [3] less_SucE)
apply (simp_all add: less_Suc_eq)
done

lemma diff_le_self [simp]: "m - n \<le> (m::nat)"
by (induct m n rule: diff_induct) (simp_all add: le_SucI)

lemma less_imp_diff_less: "(j::nat) < k ==> j - n < k"
by (rule le_less_trans, rule diff_le_self)

lemma diff_diff_left: "(i::nat) - j - k = i - (j + k)"
by (induct i j rule: diff_induct) simp_all

lemma Suc_diff_diff [simp]: "(Suc m - n) - Suc k = m - n - k"
by (simp add: diff_diff_left)

lemma diff_Suc_less [simp]: "0<n ==> n - Suc i < n"
by (cases n) (auto simp add: le_simps)

text {* This and the next few suggested by Florian Kammueller *}
lemma diff_commute: "(i::nat) - j - k = i - k - j"
by (simp add: diff_diff_left add_commute)

lemma diff_add_assoc: "k \<le> (j::nat) ==> (i + j) - k = i + (j - k)"
by (induct j k rule: diff_induct) simp_all

lemma diff_add_assoc2: "k \<le> (j::nat) ==> (j + i) - k = (j - k) + i"
by (simp add: add_commute diff_add_assoc)

lemma diff_add_inverse: "(n + m) - n = (m::nat)"
by (induct n) simp_all

lemma diff_add_inverse2: "(m + n) - n = (m::nat)"
by (simp add: diff_add_assoc)

lemma le_imp_diff_is_add: "i \<le> (j::nat) ==> (j - i = k) = (j = k + i)"
by (auto simp add: diff_add_inverse2)

lemma diff_is_0_eq [simp]: "((m::nat) - n = 0) = (m \<le> n)"
by (induct m n rule: diff_induct) simp_all

lemma diff_is_0_eq' [simp]: "m \<le> n ==> (m::nat) - n = 0"
by (rule iffD2, rule diff_is_0_eq)

lemma zero_less_diff [simp]: "(0 < n - (m::nat)) = (m < n)"
by (induct m n rule: diff_induct) simp_all

lemma less_imp_add_positive:
  assumes "i < j"
  shows "\<exists>k::nat. 0 < k & i + k = j"
proof
  from assms show "0 < j - i & i + (j - i) = j"
    by (simp add: order_less_imp_le)
qed

lemma diff_cancel: "(k + m) - (k + n) = m - (n::nat)"
by (induct k) simp_all

lemma diff_cancel2: "(m + k) - (n + k) = m - (n::nat)"
by (simp add: diff_cancel add_commute)

lemma diff_add_0: "n - (n + m) = (0::nat)"
by (induct n) simp_all


text {* Difference distributes over multiplication *}

lemma diff_mult_distrib: "((m::nat) - n) * k = (m * k) - (n * k)"
by (induct m n rule: diff_induct) (simp_all add: diff_cancel)

lemma diff_mult_distrib2: "k * ((m::nat) - n) = (k * m) - (k * n)"
by (simp add: diff_mult_distrib mult_commute [of k])
  -- {* NOT added as rewrites, since sometimes they are used from right-to-left *}

lemmas nat_distrib =
  add_mult_distrib add_mult_distrib2 diff_mult_distrib diff_mult_distrib2


subsection {* Monotonicity of Multiplication *}

lemma mult_le_mono1: "i \<le> (j::nat) ==> i * k \<le> j * k"
by (simp add: mult_right_mono)

lemma mult_le_mono2: "i \<le> (j::nat) ==> k * i \<le> k * j"
by (simp add: mult_left_mono)

text {* @{text "\<le>"} monotonicity, BOTH arguments *}
lemma mult_le_mono: "i \<le> (j::nat) ==> k \<le> l ==> i * k \<le> j * l"
by (simp add: mult_mono)

lemma mult_less_mono1: "(i::nat) < j ==> 0 < k ==> i * k < j * k"
by (simp add: mult_strict_right_mono)

text{*Differs from the standard @{text zero_less_mult_iff} in that
      there are no negative numbers.*}
lemma nat_0_less_mult_iff [simp]: "(0 < (m::nat) * n) = (0 < m & 0 < n)"
  apply (induct m)
   apply simp
  apply (case_tac n)
   apply simp_all
  done

lemma one_le_mult_iff [simp]: "(Suc 0 \<le> m * n) = (1 \<le> m & 1 \<le> n)"
  apply (induct m)
   apply simp
  apply (case_tac n)
   apply simp_all
  done

lemma mult_eq_1_iff [simp]: "(m * n = Suc 0) = (m = 1 & n = 1)"
  apply (induct m)
   apply simp
  apply (induct n)
   apply auto
  done

lemma one_eq_mult_iff [simp,noatp]: "(Suc 0 = m * n) = (m = 1 & n = 1)"
  apply (rule trans)
  apply (rule_tac [2] mult_eq_1_iff, fastsimp)
  done

lemma mult_less_cancel2 [simp]: "((m::nat) * k < n * k) = (0 < k & m < n)"
  apply (safe intro!: mult_less_mono1)
  apply (case_tac k, auto)
  apply (simp del: le_0_eq add: linorder_not_le [symmetric])
  apply (blast intro: mult_le_mono1)
  done

lemma mult_less_cancel1 [simp]: "(k * (m::nat) < k * n) = (0 < k & m < n)"
by (simp add: mult_commute [of k])

lemma mult_le_cancel1 [simp]: "(k * (m::nat) \<le> k * n) = (0 < k --> m \<le> n)"
by (simp add: linorder_not_less [symmetric], auto)

lemma mult_le_cancel2 [simp]: "((m::nat) * k \<le> n * k) = (0 < k --> m \<le> n)"
by (simp add: linorder_not_less [symmetric], auto)

lemma mult_cancel2 [simp]: "(m * k = n * k) = (m = n | (k = (0::nat)))"
apply (cut_tac less_linear, safe, auto simp add: neq0_conv)
apply (drule mult_less_mono1, assumption, simp)+
done

lemma mult_cancel1 [simp]: "(k * m = k * n) = (m = n | (k = (0::nat)))"
by (simp add: mult_commute [of k])

lemma Suc_mult_less_cancel1: "(Suc k * m < Suc k * n) = (m < n)"
by (subst mult_less_cancel1) simp

lemma Suc_mult_le_cancel1: "(Suc k * m \<le> Suc k * n) = (m \<le> n)"
by (subst mult_le_cancel1) simp

lemma Suc_mult_cancel1: "(Suc k * m = Suc k * n) = (m = n)"
by (subst mult_cancel1) simp

text {* Lemma for @{text gcd} *}
lemma mult_eq_self_implies_10: "(m::nat) = m * n ==> n = 1 | m = 0"
  apply (drule sym)
  apply (rule disjCI)
  apply (rule nat_less_cases, erule_tac [2] _)
  apply (fastsimp elim!: less_SucE)
  apply (auto simp add: neq0_conv dest: mult_less_mono2)
  done


subsection {* size of a datatype value *}

class size = type +
  fixes size :: "'a \<Rightarrow> nat"

use "Tools/function_package/size.ML"

setup Size.setup

lemma nat_size [simp, code func]: "size (n\<Colon>nat) = n"
  by (induct n) simp_all

lemma size_bool [code func]:
  "size (b\<Colon>bool) = 0" by (cases b) auto

declare "*.size" [noatp]


subsection {* Code generator setup *}

lemma one_is_Suc_zero [code inline]: "1 = Suc 0"
by simp

instance nat :: eq ..

lemma [code func]:
    "(0\<Colon>nat) = 0 \<longleftrightarrow> True"
    "Suc n = Suc m \<longleftrightarrow> n = m"
    "Suc n = 0 \<longleftrightarrow> False"
    "0 = Suc m \<longleftrightarrow> False"
by auto

lemma [code func]:
    "(0\<Colon>nat) \<le> m \<longleftrightarrow> True"
    "Suc (n\<Colon>nat) \<le> m \<longleftrightarrow> n < m"
    "(n\<Colon>nat) < 0 \<longleftrightarrow> False"
    "(n\<Colon>nat) < Suc m \<longleftrightarrow> n \<le> m"
  using Suc_le_eq less_Suc_eq_le by simp_all


subsection{*Embedding of the Naturals into any
  @{text semiring_1}: @{term of_nat}*}

context semiring_1
begin

definition
  of_nat_def: "of_nat = nat_rec 0 (\<lambda>_. (op +) 1)"

end

subsection {* Further Arithmetic Facts Concerning the Natural Numbers *}

lemma subst_equals:
  assumes 1: "t = s" and 2: "u = t"
  shows "u = s"
  using 2 1 by (rule trans)


use "arith_data.ML"
declaration {* K arith_data_setup *}

use "Tools/lin_arith.ML"
declaration {* K LinArith.setup *}


text{*The following proofs may rely on the arithmetic proof procedures.*}

lemma le_iff_add: "(m::nat) \<le> n = (\<exists>k. n = m + k)"
by (auto simp: le_eq_less_or_eq dest: less_imp_Suc_add)

lemma pred_nat_trancl_eq_le: "((m, n) : pred_nat^*) = (m \<le> n)"
by (simp add: less_eq reflcl_trancl [symmetric] del: reflcl_trancl, arith)

lemma nat_diff_split:
  "P(a - b::nat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
    -- {* elimination of @{text -} on @{text nat} *}
by (cases "a<b" rule: case_split) (auto simp add: diff_is_0_eq [THEN iffD2])

lemma nat_diff_split_asm:
    "P(a - b::nat) = (~ (a < b & ~ P 0 | (EX d. a = b + d & ~ P d)))"
    -- {* elimination of @{text -} on @{text nat} in assumptions *}
by (simp split: nat_diff_split)

lemmas [arith_split] = nat_diff_split split_min split_max


lemma le_square: "m \<le> m * (m::nat)"
by (induct m) auto

lemma le_cube: "(m::nat) \<le> m * (m * m)"
by (induct m) auto


text{*Subtraction laws, mostly by Clemens Ballarin*}

lemma diff_less_mono: "[| a < (b::nat); c \<le> a |] ==> a-c < b-c"
by arith

lemma less_diff_conv: "(i < j-k) = (i+k < (j::nat))"
by arith

lemma le_diff_conv: "(j-k \<le> (i::nat)) = (j \<le> i+k)"
by arith

lemma le_diff_conv2: "k \<le> j ==> (i \<le> j-k) = (i+k \<le> (j::nat))"
by arith

lemma diff_diff_cancel [simp]: "i \<le> (n::nat) ==> n - (n - i) = i"
by arith

lemma le_add_diff: "k \<le> (n::nat) ==> m \<le> n + m - k"
by arith

(*Replaces the previous diff_less and le_diff_less, which had the stronger
  second premise n\<le>m*)
lemma diff_less[simp]: "!!m::nat. [| 0<n; 0<m |] ==> m - n < m"
by arith


(** Simplification of relational expressions involving subtraction **)

lemma diff_diff_eq: "[| k \<le> m;  k \<le> (n::nat) |] ==> ((m-k) - (n-k)) = (m-n)"
by (simp split add: nat_diff_split)

lemma eq_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k = n-k) = (m=n)"
by (auto split add: nat_diff_split)

lemma less_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k < n-k) = (m<n)"
by (auto split add: nat_diff_split)

lemma le_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k \<le> n-k) = (m\<le>n)"
by (auto split add: nat_diff_split)


text{*(Anti)Monotonicity of subtraction -- by Stephan Merz*}

(* Monotonicity of subtraction in first argument *)
lemma diff_le_mono: "m \<le> (n::nat) ==> (m-l) \<le> (n-l)"
by (simp split add: nat_diff_split)

lemma diff_le_mono2: "m \<le> (n::nat) ==> (l-n) \<le> (l-m)"
by (simp split add: nat_diff_split)

lemma diff_less_mono2: "[| m < (n::nat); m<l |] ==> (l-n) < (l-m)"
by (simp split add: nat_diff_split)

lemma diffs0_imp_equal: "!!m::nat. [| m-n = 0; n-m = 0 |] ==>  m=n"
by (simp split add: nat_diff_split)

text{*Lemmas for ex/Factorization*}

lemma one_less_mult: "[| Suc 0 < n; Suc 0 < m |] ==> Suc 0 < m*n"
by (cases m) auto

lemma n_less_m_mult_n: "[| Suc 0 < n; Suc 0 < m |] ==> n<m*n"
by (cases m) auto

lemma n_less_n_mult_m: "[| Suc 0 < n; Suc 0 < m |] ==> n<n*m"
by (cases m) auto

text {* Specialized induction principles that work "backwards": *}

lemma inc_induct[consumes 1, case_names base step]:
  assumes less: "i <= j"
  assumes base: "P j"
  assumes step: "!!i. [| i < j; P (Suc i) |] ==> P i"
  shows "P i"
  using less
proof (induct d=="j - i" arbitrary: i)
  case (0 i)
  hence "i = j" by simp
  with base show ?case by simp
next
  case (Suc d i)
  hence "i < j" "P (Suc i)"
    by simp_all
  thus "P i" by (rule step)
qed

lemma strict_inc_induct[consumes 1, case_names base step]:
  assumes less: "i < j"
  assumes base: "!!i. j = Suc i ==> P i"
  assumes step: "!!i. [| i < j; P (Suc i) |] ==> P i"
  shows "P i"
  using less
proof (induct d=="j - i - 1" arbitrary: i)
  case (0 i)
  with `i < j` have "j = Suc i" by simp
  with base show ?case by simp
next
  case (Suc d i)
  hence "i < j" "P (Suc i)"
    by simp_all
  thus "P i" by (rule step)
qed

lemma zero_induct_lemma: "P k ==> (!!n. P (Suc n) ==> P n) ==> P (k - i)"
  using inc_induct[of "k - i" k P, simplified] by blast

lemma zero_induct: "P k ==> (!!n. P (Suc n) ==> P n) ==> P 0"
  using inc_induct[of 0 k P] by blast

text{*Rewriting to pull differences out*}

lemma diff_diff_right [simp]: "k\<le>j --> i - (j - k) = i + (k::nat) - j"
by arith

lemma diff_Suc_diff_eq1 [simp]: "k \<le> j ==> m - Suc (j - k) = m + k - Suc j"
by arith

lemma diff_Suc_diff_eq2 [simp]: "k \<le> j ==> Suc (j - k) - m = Suc j - (k + m)"
by arith

(*The others are
      i - j - k = i - (j + k),
      k \<le> j ==> j - k + i = j + i - k,
      k \<le> j ==> i + (j - k) = i + j - k *)
lemmas add_diff_assoc = diff_add_assoc [symmetric]
lemmas add_diff_assoc2 = diff_add_assoc2[symmetric]
declare diff_diff_left [simp]  add_diff_assoc [simp]  add_diff_assoc2[simp]

text{*At present we prove no analogue of @{text not_less_Least} or @{text
Least_Suc}, since there appears to be no need.*}


subsection{*Embedding of the Naturals into any
  @{text semiring_1}: @{term of_nat}*}

context semiring_1
begin

lemma of_nat_simps [simp, code]:
  shows of_nat_0:   "of_nat 0 = 0"
    and of_nat_Suc: "of_nat (Suc m) = 1 + of_nat m"
  unfolding of_nat_def by simp_all

end

lemma of_nat_id [simp]: "(of_nat n \<Colon> nat) = n"
by (induct n) auto

lemma of_nat_1 [simp]: "of_nat 1 = 1"
by simp

lemma of_nat_add [simp]: "of_nat (m + n) = of_nat m + of_nat n"
by (induct m) (simp_all add: add_ac)

lemma of_nat_mult: "of_nat (m*n) = of_nat m * of_nat n"
by (induct m) (simp_all add: add_ac left_distrib)

lemma zero_le_imp_of_nat: "0 \<le> (of_nat m::'a::ordered_semidom)"
  apply (induct m, simp_all)
  apply (erule order_trans)
  apply (rule ord_le_eq_trans [OF _ add_commute])
  apply (rule less_add_one [THEN order_less_imp_le])
  done

lemma less_imp_of_nat_less:
    "m < n ==> of_nat m < (of_nat n::'a::ordered_semidom)"
  apply (induct m n rule: diff_induct, simp_all)
  apply (insert add_less_le_mono [OF zero_less_one zero_le_imp_of_nat], force)
  done

lemma of_nat_less_imp_less:
    "of_nat m < (of_nat n::'a::ordered_semidom) ==> m < n"
  apply (induct m n rule: diff_induct, simp_all)
  apply (insert zero_le_imp_of_nat)
  apply (force simp add: linorder_not_less [symmetric])
  done

lemma of_nat_less_iff [simp]:
    "(of_nat m < (of_nat n::'a::ordered_semidom)) = (m<n)"
by (blast intro: of_nat_less_imp_less less_imp_of_nat_less)

text{*Special cases where either operand is zero*}

lemma of_nat_0_less_iff [simp]: "((0::'a::ordered_semidom) < of_nat n) = (0 < n)"
by (rule of_nat_less_iff [of 0, simplified])

lemma of_nat_less_0_iff [simp]: "\<not> of_nat m < (0::'a::ordered_semidom)"
by (rule of_nat_less_iff [of _ 0, simplified])

lemma of_nat_le_iff [simp]:
    "(of_nat m \<le> (of_nat n::'a::ordered_semidom)) = (m \<le> n)"
by (simp add: linorder_not_less [symmetric])

text{*Special cases where either operand is zero*}
lemma of_nat_0_le_iff [simp]: "(0::'a::ordered_semidom) \<le> of_nat n"
by (rule of_nat_le_iff [of 0, simplified])
lemma of_nat_le_0_iff [simp,noatp]: "(of_nat m \<le> (0::'a::ordered_semidom)) = (m = 0)"
by (rule of_nat_le_iff [of _ 0, simplified])

text{*Class for unital semirings with characteristic zero.
 Includes non-ordered rings like the complex numbers.*}

class semiring_char_0 = semiring_1 +
  assumes of_nat_eq_iff [simp]:
    "of_nat m = of_nat n \<longleftrightarrow> m = n"

text{*Every @{text ordered_semidom} has characteristic zero.*}
instance ordered_semidom < semiring_char_0
by intro_classes (simp add: order_eq_iff)

text{*Special cases where either operand is zero*}
lemma of_nat_0_eq_iff [simp,noatp]: "((0::'a::semiring_char_0) = of_nat n) = (0 = n)"
by (rule of_nat_eq_iff [of 0, simplified])
lemma of_nat_eq_0_iff [simp,noatp]: "(of_nat m = (0::'a::semiring_char_0)) = (m = 0)"
by (rule of_nat_eq_iff [of _ 0, simplified])

lemma inj_of_nat: "inj (of_nat :: nat \<Rightarrow> 'a::semiring_char_0)"
by (simp add: inj_on_def)

lemma of_nat_diff:
    "n \<le> m ==> of_nat (m - n) = of_nat m - (of_nat n :: 'a::ring_1)"
by (simp del: of_nat_add
    add: compare_rls of_nat_add [symmetric] split add: nat_diff_split)

lemma abs_of_nat [simp]: "\<bar>of_nat n::'a::ordered_idom\<bar> = of_nat n"
by (rule of_nat_0_le_iff [THEN abs_of_nonneg])


subsection {*The Set of Natural Numbers*}

definition
  Nats  :: "'a::semiring_1 set"
where
  "Nats = range of_nat"

notation (xsymbols)
  Nats  ("\<nat>")

lemma of_nat_in_Nats [simp]: "of_nat n \<in> Nats"
by (simp add: Nats_def)

lemma Nats_0 [simp]: "0 \<in> Nats"
apply (simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_0 [symmetric])
done

lemma Nats_1 [simp]: "1 \<in> Nats"
apply (simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_1 [symmetric])
done

lemma Nats_add [simp]: "[|a \<in> Nats; b \<in> Nats|] ==> a+b \<in> Nats"
apply (auto simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_add [symmetric])
done

lemma Nats_mult [simp]: "[|a \<in> Nats; b \<in> Nats|] ==> a*b \<in> Nats"
apply (auto simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_mult [symmetric])
done

lemma of_nat_eq_id [simp]: "of_nat = (id :: nat => nat)"
by (auto simp add: expand_fun_eq)


text {* the lattice order on @{typ nat} *}

instance nat :: distrib_lattice
  "inf \<equiv> min"
  "sup \<equiv> max"
  by intro_classes
    (simp_all add: inf_nat_def sup_nat_def)


subsection {* legacy bindings *}

ML
{*
val pred_nat_trancl_eq_le = thm "pred_nat_trancl_eq_le";
val nat_diff_split = thm "nat_diff_split";
val nat_diff_split_asm = thm "nat_diff_split_asm";
val le_square = thm "le_square";
val le_cube = thm "le_cube";
val diff_less_mono = thm "diff_less_mono";
val less_diff_conv = thm "less_diff_conv";
val le_diff_conv = thm "le_diff_conv";
val le_diff_conv2 = thm "le_diff_conv2";
val diff_diff_cancel = thm "diff_diff_cancel";
val le_add_diff = thm "le_add_diff";
val diff_less = thm "diff_less";
val diff_diff_eq = thm "diff_diff_eq";
val eq_diff_iff = thm "eq_diff_iff";
val less_diff_iff = thm "less_diff_iff";
val le_diff_iff = thm "le_diff_iff";
val diff_le_mono = thm "diff_le_mono";
val diff_le_mono2 = thm "diff_le_mono2";
val diff_less_mono2 = thm "diff_less_mono2";
val diffs0_imp_equal = thm "diffs0_imp_equal";
val one_less_mult = thm "one_less_mult";
val n_less_m_mult_n = thm "n_less_m_mult_n";
val n_less_n_mult_m = thm "n_less_n_mult_m";
val diff_diff_right = thm "diff_diff_right";
val diff_Suc_diff_eq1 = thm "diff_Suc_diff_eq1";
val diff_Suc_diff_eq2 = thm "diff_Suc_diff_eq2";
*}

end
