(*  Title:      HOL/Library/NatTransfer.thy
    Authors:    Jeremy Avigad and Amine Chaieb

    Sets up transfer from nats to ints and
    back.
*)


header {* NatTransfer *}

theory NatTransfer
imports Main Parity
uses ("Tools/transfer_data.ML")
begin

subsection {* A transfer Method between isomorphic domains*}

definition TransferMorphism:: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> bool"
  where "TransferMorphism a B = True"

use "Tools/transfer_data.ML"

setup TransferData.setup


subsection {* Set up transfer from nat to int *}

(* set up transfer direction *)

lemma TransferMorphism_nat_int: "TransferMorphism nat (op <= (0::int))"
  by (simp add: TransferMorphism_def)

declare TransferMorphism_nat_int[transfer
  add mode: manual
  return: nat_0_le
  labels: natint
]

(* basic functions and relations *)

lemma transfer_nat_int_numerals:
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


lemma transfer_nat_int_functions:
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) + (nat y) = nat (x + y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) * (nat y) = nat (x * y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) - (nat y) = nat (tsub x y)"
    "(x::int) >= 0 \<Longrightarrow> (nat x)^n = nat (x^n)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) div (nat y) = nat (x div y)"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> (nat x) mod (nat y) = nat (x mod y)"
  by (auto simp add: eq_nat_nat_iff nat_mult_distrib
      nat_power_eq nat_div_distrib nat_mod_distrib tsub_def)

lemma transfer_nat_int_function_closures:
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x + y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x * y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> tsub x y >= 0"
    "(x::int) >= 0 \<Longrightarrow> x^n >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x div y >= 0"
    "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> x mod y >= 0"
    "(0::int) >= 0"
    "(1::int) >= 0"
    "(2::int) >= 0"
    "(3::int) >= 0"
    "int z >= 0"
  apply (auto simp add: zero_le_mult_iff tsub_def)
  apply (case_tac "y = 0")
  apply auto
  apply (subst pos_imp_zdiv_nonneg_iff, auto)
  apply (case_tac "y = 0")
  apply force
  apply (rule pos_mod_sign)
  apply arith
done

lemma transfer_nat_int_relations:
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) = nat y) = (x = y)"
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) < nat y) = (x < y)"
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) <= nat y) = (x <= y)"
    "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow>
      (nat (x::int) dvd nat y) = (x dvd y)"
  by (auto simp add: zdvd_int even_nat_def)

declare TransferMorphism_nat_int[transfer add return:
  transfer_nat_int_numerals
  transfer_nat_int_functions
  transfer_nat_int_function_closures
  transfer_nat_int_relations
]


(* first-order quantifiers *)

lemma transfer_nat_int_quantifiers:
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

declare TransferMorphism_nat_int[transfer add
  return: transfer_nat_int_quantifiers
  cong: all_cong ex_cong]


(* if *)

lemma nat_if_cong: "(if P then (nat x) else (nat y)) =
    nat (if P then x else y)"
  by auto

declare TransferMorphism_nat_int [transfer add return: nat_if_cong]


(* operations with sets *)

definition
  nat_set :: "int set \<Rightarrow> bool"
where
  "nat_set S = (ALL x:S. x >= 0)"

lemma transfer_nat_int_set_functions:
    "card A = card (int ` A)"
    "{} = nat ` ({}::int set)"
    "A Un B = nat ` (int ` A Un int ` B)"
    "A Int B = nat ` (int ` A Int int ` B)"
    "{x. P x} = nat ` {x. x >= 0 & P(nat x)}"
    "{..n} = nat ` {0..int n}"
    "{m..n} = nat ` {int m..int n}"  (* need all variants of these! *)
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
  apply (rule_tac x = "int x" in bexI)
  apply auto
  apply (rule_tac x = "int x" in bexI)
  apply auto
done

lemma transfer_nat_int_set_function_closures:
    "nat_set {}"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Un B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Int B)"
    "x >= 0 \<Longrightarrow> nat_set {x..y}"
    "nat_set {x. x >= 0 & P x}"
    "nat_set (int ` C)"
    "nat_set A \<Longrightarrow> x : A \<Longrightarrow> x >= 0" (* does it hurt to turn this on? *)
  unfolding nat_set_def apply auto
done

lemma transfer_nat_int_set_relations:
    "(finite A) = (finite (int ` A))"
    "(x : A) = (int x : int ` A)"
    "(A = B) = (int ` A = int ` B)"
    "(A < B) = (int ` A < int ` B)"
    "(A <= B) = (int ` A <= int ` B)"

  apply (rule iffI)
  apply (erule finite_imageI)
  apply (erule finite_imageD)
  apply (auto simp add: image_def expand_set_eq inj_on_def)
  apply (drule_tac x = "int x" in spec, auto)
  apply (drule_tac x = "int x" in spec, auto)
  apply (drule_tac x = "int x" in spec, auto)
done

lemma transfer_nat_int_set_return_embed: "nat_set A \<Longrightarrow>
    (int ` nat ` A = A)"
  by (auto simp add: nat_set_def image_def)

lemma transfer_nat_int_set_cong: "(!!x. x >= 0 \<Longrightarrow> P x = P' x) \<Longrightarrow>
    {(x::int). x >= 0 & P x} = {x. x >= 0 & P' x}"
  by auto

declare TransferMorphism_nat_int[transfer add
  return: transfer_nat_int_set_functions
    transfer_nat_int_set_function_closures
    transfer_nat_int_set_relations
    transfer_nat_int_set_return_embed
  cong: transfer_nat_int_set_cong
]


(* setsum and setprod *)

(* this handles the case where the *domain* of f is nat *)
lemma transfer_nat_int_sum_prod:
    "setsum f A = setsum (%x. f (nat x)) (int ` A)"
    "setprod f A = setprod (%x. f (nat x)) (int ` A)"
  apply (subst setsum_reindex)
  apply (unfold inj_on_def, auto)
  apply (subst setprod_reindex)
  apply (unfold inj_on_def o_def, auto)
done

(* this handles the case where the *range* of f is nat *)
lemma transfer_nat_int_sum_prod2:
    "setsum f A = nat(setsum (%x. int (f x)) A)"
    "setprod f A = nat(setprod (%x. int (f x)) A)"
  apply (subst int_setsum [symmetric])
  apply auto
  apply (subst int_setprod [symmetric])
  apply auto
done

lemma transfer_nat_int_sum_prod_closure:
    "nat_set A \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x >= (0::int)) \<Longrightarrow> setsum f A >= 0"
    "nat_set A \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x >= (0::int)) \<Longrightarrow> setprod f A >= 0"
  unfolding nat_set_def
  apply (rule setsum_nonneg)
  apply auto
  apply (rule setprod_nonneg)
  apply auto
done

(* this version doesn't work, even with nat_set A \<Longrightarrow>
      x : A \<Longrightarrow> x >= 0 turned on. Why not?

  also: what does =simp=> do?

lemma transfer_nat_int_sum_prod_closure:
    "(!!x. x : A  ==> f x >= (0::int)) \<Longrightarrow> setsum f A >= 0"
    "(!!x. x : A  ==> f x >= (0::int)) \<Longrightarrow> setprod f A >= 0"
  unfolding nat_set_def simp_implies_def
  apply (rule setsum_nonneg)
  apply auto
  apply (rule setprod_nonneg)
  apply auto
done
*)

(* Making A = B in this lemma doesn't work. Why not?
   Also, why aren't setsum_cong and setprod_cong enough,
   with the previously mentioned rule turned on? *)

lemma transfer_nat_int_sum_prod_cong:
    "A = B \<Longrightarrow> nat_set B \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x = g x) \<Longrightarrow>
      setsum f A = setsum g B"
    "A = B \<Longrightarrow> nat_set B \<Longrightarrow> (!!x. x >= 0 \<Longrightarrow> f x = g x) \<Longrightarrow>
      setprod f A = setprod g B"
  unfolding nat_set_def
  apply (subst setsum_cong, assumption)
  apply auto [2]
  apply (subst setprod_cong, assumption, auto)
done

declare TransferMorphism_nat_int[transfer add
  return: transfer_nat_int_sum_prod transfer_nat_int_sum_prod2
    transfer_nat_int_sum_prod_closure
  cong: transfer_nat_int_sum_prod_cong]

(* lists *)

definition
  embed_list :: "nat list \<Rightarrow> int list"
where
  "embed_list l = map int l";

definition
  nat_list :: "int list \<Rightarrow> bool"
where
  "nat_list l = nat_set (set l)";

definition
  return_list :: "int list \<Rightarrow> nat list"
where
  "return_list l = map nat l";

thm nat_0_le;

lemma transfer_nat_int_list_return_embed: "nat_list l \<longrightarrow>
    embed_list (return_list l) = l";
  unfolding embed_list_def return_list_def nat_list_def nat_set_def
  apply (induct l);
  apply auto;
done;

lemma transfer_nat_int_list_functions:
  "l @ m = return_list (embed_list l @ embed_list m)"
  "[] = return_list []";
  unfolding return_list_def embed_list_def;
  apply auto;
  apply (induct l, auto);
  apply (induct m, auto);
done;

(*
lemma transfer_nat_int_fold1: "fold f l x =
    fold (%x. f (nat x)) (embed_list l) x";
*)




subsection {* Set up transfer from int to nat *}

(* set up transfer direction *)

lemma TransferMorphism_int_nat: "TransferMorphism int (UNIV :: nat set)"
  by (simp add: TransferMorphism_def)

declare TransferMorphism_int_nat[transfer add
  mode: manual
(*  labels: int-nat *)
  return: nat_int
]


(* basic functions and relations *)

definition
  is_nat :: "int \<Rightarrow> bool"
where
  "is_nat x = (x >= 0)"

lemma transfer_int_nat_numerals:
    "0 = int 0"
    "1 = int 1"
    "2 = int 2"
    "3 = int 3"
  by auto

lemma transfer_int_nat_functions:
    "(int x) + (int y) = int (x + y)"
    "(int x) * (int y) = int (x * y)"
    "tsub (int x) (int y) = int (x - y)"
    "(int x)^n = int (x^n)"
    "(int x) div (int y) = int (x div y)"
    "(int x) mod (int y) = int (x mod y)"
  by (auto simp add: int_mult tsub_def int_power zdiv_int zmod_int)

lemma transfer_int_nat_function_closures:
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x + y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x * y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (tsub x y)"
    "is_nat x \<Longrightarrow> is_nat (x^n)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x div y)"
    "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> is_nat (x mod y)"
    "is_nat 0"
    "is_nat 1"
    "is_nat 2"
    "is_nat 3"
    "is_nat (int z)"
  by (simp_all only: is_nat_def transfer_nat_int_function_closures)

lemma transfer_int_nat_relations:
    "(int x = int y) = (x = y)"
    "(int x < int y) = (x < y)"
    "(int x <= int y) = (x <= y)"
    "(int x dvd int y) = (x dvd y)"
    "(even (int x)) = (even x)"
  by (auto simp add: zdvd_int even_nat_def)

lemma UNIV_apply:
  "UNIV x = True"
  by (simp add: top_set_eq [symmetric] top_fun_eq top_bool_eq)

declare TransferMorphism_int_nat[transfer add return:
  transfer_int_nat_numerals
  transfer_int_nat_functions
  transfer_int_nat_function_closures
  transfer_int_nat_relations
  UNIV_apply
]


(* first-order quantifiers *)

lemma transfer_int_nat_quantifiers:
    "(ALL (x::int) >= 0. P x) = (ALL (x::nat). P (int x))"
    "(EX (x::int) >= 0. P x) = (EX (x::nat). P (int x))"
  apply (subst all_nat)
  apply auto [1]
  apply (subst ex_nat)
  apply auto
done

declare TransferMorphism_int_nat[transfer add
  return: transfer_int_nat_quantifiers]


(* if *)

lemma int_if_cong: "(if P then (int x) else (int y)) =
    int (if P then x else y)"
  by auto

declare TransferMorphism_int_nat [transfer add return: int_if_cong]



(* operations with sets *)

lemma transfer_int_nat_set_functions:
    "nat_set A \<Longrightarrow> card A = card (nat ` A)"
    "{} = int ` ({}::nat set)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> A Un B = int ` (nat ` A Un nat ` B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> A Int B = int ` (nat ` A Int nat ` B)"
    "{x. x >= 0 & P x} = int ` {x. P(int x)}"
    "is_nat m \<Longrightarrow> is_nat n \<Longrightarrow> {m..n} = int ` {nat m..nat n}"
       (* need all variants of these! *)
  by (simp_all only: is_nat_def transfer_nat_int_set_functions
          transfer_nat_int_set_function_closures
          transfer_nat_int_set_return_embed nat_0_le
          cong: transfer_nat_int_set_cong)

lemma transfer_int_nat_set_function_closures:
    "nat_set {}"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Un B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> nat_set (A Int B)"
    "is_nat x \<Longrightarrow> nat_set {x..y}"
    "nat_set {x. x >= 0 & P x}"
    "nat_set (int ` C)"
    "nat_set A \<Longrightarrow> x : A \<Longrightarrow> is_nat x"
  by (simp_all only: transfer_nat_int_set_function_closures is_nat_def)

lemma transfer_int_nat_set_relations:
    "nat_set A \<Longrightarrow> finite A = finite (nat ` A)"
    "is_nat x \<Longrightarrow> nat_set A \<Longrightarrow> (x : A) = (nat x : nat ` A)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> (A = B) = (nat ` A = nat ` B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> (A < B) = (nat ` A < nat ` B)"
    "nat_set A \<Longrightarrow> nat_set B \<Longrightarrow> (A <= B) = (nat ` A <= nat ` B)"
  by (simp_all only: is_nat_def transfer_nat_int_set_relations
    transfer_nat_int_set_return_embed nat_0_le)

lemma transfer_int_nat_set_return_embed: "nat ` int ` A = A"
  by (simp only: transfer_nat_int_set_relations
    transfer_nat_int_set_function_closures
    transfer_nat_int_set_return_embed nat_0_le)

lemma transfer_int_nat_set_cong: "(!!x. P x = P' x) \<Longrightarrow>
    {(x::nat). P x} = {x. P' x}"
  by auto

declare TransferMorphism_int_nat[transfer add
  return: transfer_int_nat_set_functions
    transfer_int_nat_set_function_closures
    transfer_int_nat_set_relations
    transfer_int_nat_set_return_embed
  cong: transfer_int_nat_set_cong
]


(* setsum and setprod *)

(* this handles the case where the *domain* of f is int *)
lemma transfer_int_nat_sum_prod:
    "nat_set A \<Longrightarrow> setsum f A = setsum (%x. f (int x)) (nat ` A)"
    "nat_set A \<Longrightarrow> setprod f A = setprod (%x. f (int x)) (nat ` A)"
  apply (subst setsum_reindex)
  apply (unfold inj_on_def nat_set_def, auto simp add: eq_nat_nat_iff)
  apply (subst setprod_reindex)
  apply (unfold inj_on_def nat_set_def o_def, auto simp add: eq_nat_nat_iff
            cong: setprod_cong)
done

(* this handles the case where the *range* of f is int *)
lemma transfer_int_nat_sum_prod2:
    "(!!x. x:A \<Longrightarrow> is_nat (f x)) \<Longrightarrow> setsum f A = int(setsum (%x. nat (f x)) A)"
    "(!!x. x:A \<Longrightarrow> is_nat (f x)) \<Longrightarrow>
      setprod f A = int(setprod (%x. nat (f x)) A)"
  unfolding is_nat_def
  apply (subst int_setsum, auto)
  apply (subst int_setprod, auto simp add: cong: setprod_cong)
done

declare TransferMorphism_int_nat[transfer add
  return: transfer_int_nat_sum_prod transfer_int_nat_sum_prod2
  cong: setsum_cong setprod_cong]


subsection {* Test it out *}

(* nat to int *)

lemma ex1: "(x::nat) + y = y + x"
  by auto

thm ex1 [transferred]

lemma ex2: "(a::nat) div b * b + a mod b = a"
  by (rule mod_div_equality)

thm ex2 [transferred]

lemma ex3: "ALL (x::nat). ALL y. EX z. z >= x + y"
  by auto

thm ex3 [transferred natint]

lemma ex4: "(x::nat) >= y \<Longrightarrow> (x - y) + y = x"
  by auto

thm ex4 [transferred]

lemma ex5: "(2::nat) * (SUM i <= n. i) = n * (n + 1)"
  by (induct n rule: nat_induct, auto)

thm ex5 [transferred]

theorem ex6: "0 <= (n::int) \<Longrightarrow> 2 * \<Sum>{0..n} = n * (n + 1)"
  by (rule ex5 [transferred])

thm ex6 [transferred]

thm ex5 [transferred, transferred]

end
