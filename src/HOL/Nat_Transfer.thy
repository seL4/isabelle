(* Authors: Jeremy Avigad and Amine Chaieb *)

section \<open>Generic transfer machinery;  specific transfer from nats to ints and back.\<close>

theory Nat_Transfer
imports Int Divides
begin

subsection \<open>Generic transfer machinery\<close>

definition transfer_morphism:: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool"
  where "transfer_morphism f A \<longleftrightarrow> True"

lemma transfer_morphismI[intro]: "transfer_morphism f A"
  by (simp add: transfer_morphism_def)

ML_file "Tools/legacy_transfer.ML"


subsection \<open>Set up transfer from nat to int\<close>

text \<open>set up transfer direction\<close>

lemma transfer_morphism_nat_int [no_atp]:
  "transfer_morphism nat (op <= (0::int))" ..

declare transfer_morphism_nat_int [transfer add
  mode: manual
  return: nat_0_le
  labels: nat_int
]

text \<open>basic functions and relations\<close>

lemma transfer_nat_int_numerals [no_atp, transfer key: transfer_morphism_nat_int]:
    "(0::nat) = nat 0"
    "(1::nat) = nat 1"
    "(2::nat) = nat 2"
    "(3::nat) = nat 3"
  by auto

definition
  tsub :: "int \<Rightarrow> int \<Rightarrow> int"
where
  "tsub x y = (if x >= y then x - y else 0)"

lemma tsub_eq: "x >= y \<Longrightarrow> tsub x y = x - y"
  by (simp add: tsub_def)

lemma transfer_nat_int_functions [no_atp, transfer key: transfer_morphism_nat_int]:
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) + (nat y) = nat (x + y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) * (nat y) = nat (x * y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) - (nat y) = nat (tsub x y)"
    "(x::int) >= 0 \<Longrightarrow> (nat x)^n = nat (x^n)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) div (nat y) = nat (x div y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) mod (nat y) = nat (x mod y)"
  by (auto simp add: eq_nat_nat_iff nat_mult_distrib
      nat_power_eq tsub_def nat_div_distrib nat_mod_distrib)

lemma transfer_nat_int_function_closures [no_atp, transfer key: transfer_morphism_nat_int]:
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x + y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x * y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> tsub x y >= 0"
    "(x::int) >= 0 \<Longrightarrow> x^n >= 0"
    "(0::int) >= 0"
    "(1::int) >= 0"
    "(2::int) >= 0"
    "(3::int) >= 0"
    "int z >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x div y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x mod y >= 0"
            apply (auto simp add: zero_le_mult_iff tsub_def pos_imp_zdiv_nonneg_iff)
   apply (cases "y = 0")
    apply (auto simp add: pos_imp_zdiv_nonneg_iff)
  apply (cases "y = 0")
   apply auto
  done

lemma transfer_nat_int_relations [no_atp, transfer key: transfer_morphism_nat_int]:
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) = nat y) = (x = y)"
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) < nat y) = (x < y)"
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) <= nat y) = (x <= y)"
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) dvd nat y) = (x dvd y)"
  by (auto simp add: zdvd_int)


text \<open>first-order quantifiers\<close>

lemma all_nat: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x\<ge>0. P (nat x))"
  by (simp split: split_nat)

lemma ex_nat: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. 0 \<le> x \<and> P (nat x))"
proof
  assume "\<exists>x. P x"
  then obtain x where "P x" ..
  then have "int x \<ge> 0 \<and> P (nat (int x))" by simp
  then show "\<exists>x\<ge>0. P (nat x)" ..
next
  assume "\<exists>x\<ge>0. P (nat x)"
  then show "\<exists>x. P x" by auto
qed

lemma transfer_nat_int_quantifiers [no_atp, transfer key: transfer_morphism_nat_int]:
    "(ALL (x::nat). P x) = (ALL (x::int). x >= 0 \<longrightarrow> P (nat x))"
    "(EX (x::nat). P x) = (EX (x::int). x >= 0 & P (nat x))"
  by (rule all_nat, rule ex_nat)

(* should we restrict these? *)
lemma all_cong: "(\<And>x. Q x \<Longrightarrow> P x = P' x) \<Longrightarrow>
    (ALL x. Q x \<longrightarrow> P x) = (ALL x. Q x \<longrightarrow> P' x)"
  by auto

lemma ex_cong: "(\<And>x. Q x \<Longrightarrow> P x = P' x) \<Longrightarrow>
    (EX x. Q x \<and> P x) = (EX x. Q x \<and> P' x)"
  by auto

declare transfer_morphism_nat_int [transfer add
  cong: all_cong ex_cong]


text \<open>if\<close>

lemma nat_if_cong [transfer key: transfer_morphism_nat_int]:
  "(if P then (nat x) else (nat y)) = nat (if P then x else y)"
  by auto


text \<open>operations with sets\<close>

definition
  nat_set :: "int set \<Rightarrow> bool"
where
  "nat_set S = (ALL x:S. x >= 0)"

lemma transfer_nat_int_set_functions [no_atp]:
    "card A = card (int ` A)"
    "{} = nat ` ({}::int set)"
    "A Un B = nat ` (int ` A Un int ` B)"
    "A Int B = nat ` (int ` A Int int ` B)"
    "{x. P x} = nat ` {x. x >= 0 & P(nat x)}"
  apply (rule card_image [symmetric])
  apply (auto simp add: inj_on_def image_def)
  apply (rule_tac x = "int x" in bexI)
  apply auto
  apply (rule_tac x = "int x" in bexI)
  apply auto
  apply (rule_tac x = "int x" in bexI)
  apply auto
  apply (rule_tac x = "int x" in exI)
  apply auto
done

lemma transfer_nat_int_set_function_closures [no_atp]:
    "nat_set {}"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Un B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Int B)"
    "nat_set {x. x >= 0 & P x}"
    "nat_set (int ` C)"
    "nat_set A \<Longrightarrow> x : A \<Longrightarrow> x >= 0" (* does it hurt to turn this on? *)
  unfolding nat_set_def apply auto
done

lemma transfer_nat_int_set_relations [no_atp]:
    "(finite A) = (finite (int ` A))"
    "(x : A) = (int x : int ` A)"
    "(A = B) = (int ` A = int ` B)"
    "(A < B) = (int ` A < int ` B)"
    "(A <= B) = (int ` A <= int ` B)"
  apply (rule iffI)
  apply (erule finite_imageI)
  apply (erule finite_imageD)
  apply (auto simp add: image_def set_eq_iff inj_on_def)
  apply (drule_tac x = "int x" in spec, auto)
  apply (drule_tac x = "int x" in spec, auto)
  apply (drule_tac x = "int x" in spec, auto)
done

lemma transfer_nat_int_set_return_embed [no_atp]: "nat_set A \<Longrightarrow>
    (int ` nat ` A = A)"
  by (auto simp add: nat_set_def image_def)

lemma transfer_nat_int_set_cong [no_atp]: "(!!x. x >= 0 \<Longrightarrow> P x = P' x) \<Longrightarrow>
    {(x::int). x >= 0 & P x} = {x. x >= 0 & P' x}"
  by auto

declare transfer_morphism_nat_int [transfer add
  return: transfer_nat_int_set_functions
    transfer_nat_int_set_function_closures
    transfer_nat_int_set_relations
    transfer_nat_int_set_return_embed
  cong: transfer_nat_int_set_cong
]


text \<open>sum and prod\<close>

(* this handles the case where the *domain* of f is nat *)
lemma transfer_nat_int_sum_prod [no_atp]:
    "sum f A = sum (%x. f (nat x)) (int ` A)"
    "prod f A = prod (%x. f (nat x)) (int ` A)"
  apply (subst sum.reindex)
  apply (unfold inj_on_def, auto)
  apply (subst prod.reindex)
  apply (unfold inj_on_def o_def, auto)
done

(* this handles the case where the *range* of f is nat *)
lemma transfer_nat_int_sum_prod2 [no_atp]:
    "sum f A = nat(sum (%x. int (f x)) A)"
    "prod f A = nat(prod (%x. int (f x)) A)"
  apply (simp only: int_sum [symmetric] nat_int)
  apply (simp only: int_prod [symmetric] nat_int)
  done

lemma transfer_nat_int_sum_prod_closure [no_atp]:
    "nat_set A \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x >= (0::int)) \<Longrightarrow> sum f A >= 0"
    "nat_set A \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x >= (0::int)) \<Longrightarrow> prod f A >= 0"
  unfolding nat_set_def
  apply (rule sum_nonneg)
  apply auto
  apply (rule prod_nonneg)
  apply auto
done

(* this version doesn't work, even with nat_set A \<Longrightarrow>
      x : A \<Longrightarrow> x >= 0 turned on. Why not?

  also: what does =simp=> do?

lemma transfer_nat_int_sum_prod_closure:
    "(!!x. x : A  ==> f x >= (0::int)) \<Longrightarrow> sum f A >= 0"
    "(!!x. x : A  ==> f x >= (0::int)) \<Longrightarrow> prod f A >= 0"
  unfolding nat_set_def simp_implies_def
  apply (rule sum_nonneg)
  apply auto
  apply (rule prod_nonneg)
  apply auto
done
*)

(* Making A = B in this lemma doesn't work. Why not?
   Also, why aren't sum.cong and prod.cong enough,
   with the previously mentioned rule turned on? *)

lemma transfer_nat_int_sum_prod_cong [no_atp]:
    "A = B \<Longrightarrow> nat_set B \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x = g x) \<Longrightarrow>
      sum f A = sum g B"
    "A = B \<Longrightarrow> nat_set B \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x = g x) \<Longrightarrow>
      prod f A = prod g B"
  unfolding nat_set_def
  apply (subst sum.cong, assumption)
  apply auto [2]
  apply (subst prod.cong, assumption, auto)
done

declare transfer_morphism_nat_int [transfer add
  return: transfer_nat_int_sum_prod transfer_nat_int_sum_prod2
    transfer_nat_int_sum_prod_closure
  cong: transfer_nat_int_sum_prod_cong]


subsection \<open>Set up transfer from int to nat\<close>

text \<open>set up transfer direction\<close>

lemma transfer_morphism_int_nat [no_atp]: "transfer_morphism int (\<lambda>n. True)" ..

declare transfer_morphism_int_nat [transfer add
  mode: manual
  return: nat_int
  labels: int_nat
]


text \<open>basic functions and relations\<close>

definition
  is_nat :: "int \<Rightarrow> bool"
where
  "is_nat x = (x >= 0)"

lemma transfer_int_nat_numerals [no_atp]:
    "0 = int 0"
    "1 = int 1"
    "2 = int 2"
    "3 = int 3"
  by auto

lemma transfer_int_nat_functions [no_atp]:
    "(int x) + (int y) = int (x + y)"
    "(int x) * (int y) = int (x * y)"
    "tsub (int x) (int y) = int (x - y)"
    "(int x)^n = int (x^n)"
    "(int x) div (int y) = int (x div y)"
    "(int x) mod (int y) = int (x mod y)"
  by (auto simp add: zdiv_int zmod_int tsub_def)

lemma transfer_int_nat_function_closures [no_atp]:
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x + y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x * y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (tsub x y)"
    "is_nat x \<Longrightarrow> is_nat (x^n)"
    "is_nat 0"
    "is_nat 1"
    "is_nat 2"
    "is_nat 3"
    "is_nat (int z)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x div y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x mod y)"
  by (simp_all only: is_nat_def transfer_nat_int_function_closures)

lemma transfer_int_nat_relations [no_atp]:
    "(int x = int y) = (x = y)"
    "(int x < int y) = (x < y)"
    "(int x <= int y) = (x <= y)"
    "(int x dvd int y) = (x dvd y)"
  by (auto simp add: zdvd_int)

declare transfer_morphism_int_nat [transfer add return:
  transfer_int_nat_numerals
  transfer_int_nat_functions
  transfer_int_nat_function_closures
  transfer_int_nat_relations
]


text \<open>first-order quantifiers\<close>

lemma transfer_int_nat_quantifiers [no_atp]:
    "(ALL (x::int) >= 0. P x) = (ALL (x::nat). P (int x))"
    "(EX (x::int) >= 0. P x) = (EX (x::nat). P (int x))"
  apply (subst all_nat)
  apply auto [1]
  apply (subst ex_nat)
  apply auto
done

declare transfer_morphism_int_nat [transfer add
  return: transfer_int_nat_quantifiers]


text \<open>if\<close>

lemma int_if_cong: "(if P then (int x) else (int y)) =
    int (if P then x else y)"
  by auto

declare transfer_morphism_int_nat [transfer add return: int_if_cong]



text \<open>operations with sets\<close>

lemma transfer_int_nat_set_functions [no_atp]:
    "nat_set A \<Longrightarrow> card A = card (nat ` A)"
    "{} = int ` ({}::nat set)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> A Un B = int ` (nat ` A Un nat ` B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> A Int B = int ` (nat ` A Int nat ` B)"
    "{x. x >= 0 & P x} = int ` {x. P(int x)}"
       (* need all variants of these! *)
  by (simp_all only: is_nat_def transfer_nat_int_set_functions
          transfer_nat_int_set_function_closures
          transfer_nat_int_set_return_embed nat_0_le
          cong: transfer_nat_int_set_cong)

lemma transfer_int_nat_set_function_closures [no_atp]:
    "nat_set {}"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Un B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Int B)"
    "nat_set {x. x >= 0 & P x}"
    "nat_set (int ` C)"
    "nat_set A \<Longrightarrow> x : A \<Longrightarrow> is_nat x"
  by (simp_all only: transfer_nat_int_set_function_closures is_nat_def)

lemma transfer_int_nat_set_relations [no_atp]:
    "nat_set A \<Longrightarrow> finite A = finite (nat ` A)"
    "is_nat x \<Longrightarrow> nat_set A \<Longrightarrow> (x : A) = (nat x : nat ` A)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> (A = B) = (nat ` A = nat ` B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> (A < B) = (nat ` A < nat ` B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> (A <= B) = (nat ` A <= nat ` B)"
  by (simp_all only: is_nat_def transfer_nat_int_set_relations
    transfer_nat_int_set_return_embed nat_0_le)

lemma transfer_int_nat_set_return_embed [no_atp]: "nat ` int ` A = A"
  by (simp only: transfer_nat_int_set_relations
    transfer_nat_int_set_function_closures
    transfer_nat_int_set_return_embed nat_0_le)

lemma transfer_int_nat_set_cong [no_atp]: "(!!x. P x = P' x) \<Longrightarrow>
    {(x::nat). P x} = {x. P' x}"
  by auto

declare transfer_morphism_int_nat [transfer add
  return: transfer_int_nat_set_functions
    transfer_int_nat_set_function_closures
    transfer_int_nat_set_relations
    transfer_int_nat_set_return_embed
  cong: transfer_int_nat_set_cong
]


text \<open>sum and prod\<close>

(* this handles the case where the *domain* of f is int *)
lemma transfer_int_nat_sum_prod [no_atp]:
    "nat_set A \<Longrightarrow> sum f A = sum (%x. f (int x)) (nat ` A)"
    "nat_set A \<Longrightarrow> prod f A = prod (%x. f (int x)) (nat ` A)"
  apply (subst sum.reindex)
  apply (unfold inj_on_def nat_set_def, auto simp add: eq_nat_nat_iff)
  apply (subst prod.reindex)
  apply (unfold inj_on_def nat_set_def o_def, auto simp add: eq_nat_nat_iff
            cong: prod.cong)
done

(* this handles the case where the *range* of f is int *)
lemma transfer_int_nat_sum_prod2 [no_atp]:
    "(!!x. x:A \<Longrightarrow> is_nat (f x)) \<Longrightarrow> sum f A = int(sum (%x. nat (f x)) A)"
    "(!!x. x:A \<Longrightarrow> is_nat (f x)) \<Longrightarrow>
      prod f A = int(prod (%x. nat (f x)) A)"
  unfolding is_nat_def
  by (subst int_sum) auto

declare transfer_morphism_int_nat [transfer add
  return: transfer_int_nat_sum_prod transfer_int_nat_sum_prod2
  cong: sum.cong prod.cong]

declare transfer_morphism_int_nat [transfer add return: even_int_iff]

end
