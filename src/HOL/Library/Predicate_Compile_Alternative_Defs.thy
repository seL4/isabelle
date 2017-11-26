(*  Title:      HOL/Library/Predicate_Compile_Alternative_Defs.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

theory Predicate_Compile_Alternative_Defs
  imports Main
begin

section \<open>Common constants\<close>

declare HOL.if_bool_eq_disj[code_pred_inline]

declare bool_diff_def[code_pred_inline]
declare inf_bool_def[abs_def, code_pred_inline]
declare less_bool_def[abs_def, code_pred_inline]
declare le_bool_def[abs_def, code_pred_inline]

lemma min_bool_eq [code_pred_inline]: "(min :: bool => bool => bool) == (op \<and>)"
by (rule eq_reflection) (auto simp add: fun_eq_iff min_def)

lemma [code_pred_inline]: 
  "((A::bool) \<noteq> (B::bool)) = ((A \<and> \<not> B) \<or> (B \<and> \<not> A))"
by fast

setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name Let}]\<close>

section \<open>Pairs\<close>

setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name fst}, @{const_name snd}, @{const_name case_prod}]\<close>

section \<open>Filters\<close>

(*TODO: shouldn't this be done by typedef? *)
setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name Abs_filter}, @{const_name Rep_filter}]\<close>

section \<open>Bounded quantifiers\<close>

declare Ball_def[code_pred_inline]
declare Bex_def[code_pred_inline]

section \<open>Operations on Predicates\<close>

lemma Diff[code_pred_inline]:
  "(A - B) = (%x. A x \<and> \<not> B x)"
  by (simp add: fun_eq_iff)

lemma subset_eq[code_pred_inline]:
  "(P :: 'a \<Rightarrow> bool) < (Q :: 'a \<Rightarrow> bool) \<equiv> ((\<exists>x. Q x \<and> (\<not> P x)) \<and> (\<forall>x. P x \<longrightarrow> Q x))"
  by (rule eq_reflection) (auto simp add: less_fun_def le_fun_def)

lemma set_equality[code_pred_inline]:
  "A = B \<longleftrightarrow> (\<forall>x. A x \<longrightarrow> B x) \<and> (\<forall>x. B x \<longrightarrow> A x)"
  by (auto simp add: fun_eq_iff)

section \<open>Setup for Numerals\<close>

setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name numeral}]\<close>
setup \<open>Predicate_Compile_Data.keep_functions [@{const_name numeral}]\<close>
setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name Char}]\<close>
setup \<open>Predicate_Compile_Data.keep_functions [@{const_name Char}]\<close>

setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name divide}, @{const_name modulo}, @{const_name times}]\<close>

section \<open>Arithmetic operations\<close>

subsection \<open>Arithmetic on naturals and integers\<close>

definition plus_eq_nat :: "nat => nat => nat => bool"
where
  "plus_eq_nat x y z = (x + y = z)"

definition minus_eq_nat :: "nat => nat => nat => bool"
where
  "minus_eq_nat x y z = (x - y = z)"

definition plus_eq_int :: "int => int => int => bool"
where
  "plus_eq_int x y z = (x + y = z)"

definition minus_eq_int :: "int => int => int => bool"
where
  "minus_eq_int x y z = (x - y = z)"

definition subtract
where
  [code_unfold]: "subtract x y = y - x"

setup \<open>
let
  val Fun = Predicate_Compile_Aux.Fun
  val Input = Predicate_Compile_Aux.Input
  val Output = Predicate_Compile_Aux.Output
  val Bool = Predicate_Compile_Aux.Bool
  val iio = Fun (Input, Fun (Input, Fun (Output, Bool)))
  val ioi = Fun (Input, Fun (Output, Fun (Input, Bool)))
  val oii = Fun (Output, Fun (Input, Fun (Input, Bool)))
  val ooi = Fun (Output, Fun (Output, Fun (Input, Bool)))
  val plus_nat = Core_Data.functional_compilation @{const_name plus} iio
  val minus_nat = Core_Data.functional_compilation @{const_name "minus"} iio
  fun subtract_nat compfuns (_ : typ) =
    let
      val T = Predicate_Compile_Aux.mk_monadT compfuns @{typ nat}
    in
      absdummy @{typ nat} (absdummy @{typ nat}
        (Const (@{const_name "If"}, @{typ bool} --> T --> T --> T) $
          (@{term "op > :: nat => nat => bool"} $ Bound 1 $ Bound 0) $
          Predicate_Compile_Aux.mk_empty compfuns @{typ nat} $
          Predicate_Compile_Aux.mk_single compfuns
          (@{term "op - :: nat => nat => nat"} $ Bound 0 $ Bound 1)))
    end
  fun enumerate_addups_nat compfuns (_ : typ) =
    absdummy @{typ nat} (Predicate_Compile_Aux.mk_iterate_upto compfuns @{typ "nat * nat"}
    (absdummy @{typ natural} (@{term "Pair :: nat => nat => nat * nat"} $
      (@{term "nat_of_natural"} $ Bound 0) $
      (@{term "op - :: nat => nat => nat"} $ Bound 1 $ (@{term "nat_of_natural"} $ Bound 0))),
      @{term "0 :: natural"}, @{term "natural_of_nat"} $ Bound 0))
  fun enumerate_nats compfuns  (_ : typ) =
    let
      val (single_const, _) = strip_comb (Predicate_Compile_Aux.mk_single compfuns @{term "0 :: nat"})
      val T = Predicate_Compile_Aux.mk_monadT compfuns @{typ nat}
    in
      absdummy @{typ nat} (absdummy @{typ nat}
        (Const (@{const_name If}, @{typ bool} --> T --> T --> T) $
          (@{term "op = :: nat => nat => bool"} $ Bound 0 $ @{term "0::nat"}) $
          (Predicate_Compile_Aux.mk_iterate_upto compfuns @{typ nat} (@{term "nat_of_natural"},
            @{term "0::natural"}, @{term "natural_of_nat"} $ Bound 1)) $
            (single_const $ (@{term "op + :: nat => nat => nat"} $ Bound 1 $ Bound 0))))
    end
in
  Core_Data.force_modes_and_compilations @{const_name plus_eq_nat}
    [(iio, (plus_nat, false)), (oii, (subtract_nat, false)), (ioi, (subtract_nat, false)),
     (ooi, (enumerate_addups_nat, false))]
  #> Predicate_Compile_Fun.add_function_predicate_translation
       (@{term "plus :: nat => nat => nat"}, @{term "plus_eq_nat"})
  #> Core_Data.force_modes_and_compilations @{const_name minus_eq_nat}
       [(iio, (minus_nat, false)), (oii, (enumerate_nats, false))]
  #> Predicate_Compile_Fun.add_function_predicate_translation
      (@{term "minus :: nat => nat => nat"}, @{term "minus_eq_nat"})
  #> Core_Data.force_modes_and_functions @{const_name plus_eq_int}
    [(iio, (@{const_name plus}, false)), (ioi, (@{const_name subtract}, false)),
     (oii, (@{const_name subtract}, false))]
  #> Predicate_Compile_Fun.add_function_predicate_translation
       (@{term "plus :: int => int => int"}, @{term "plus_eq_int"})
  #> Core_Data.force_modes_and_functions @{const_name minus_eq_int}
    [(iio, (@{const_name minus}, false)), (oii, (@{const_name plus}, false)),
     (ioi, (@{const_name minus}, false))]
  #> Predicate_Compile_Fun.add_function_predicate_translation
      (@{term "minus :: int => int => int"}, @{term "minus_eq_int"})
end
\<close>

subsection \<open>Inductive definitions for ordering on naturals\<close>

inductive less_nat
where
  "less_nat 0 (Suc y)"
| "less_nat x y ==> less_nat (Suc x) (Suc y)"

lemma less_nat[code_pred_inline]:
  "x < y = less_nat x y"
apply (rule iffI)
apply (induct x arbitrary: y)
apply (case_tac y) apply (auto intro: less_nat.intros)
apply (case_tac y)
apply (auto intro: less_nat.intros)
apply (induct rule: less_nat.induct)
apply auto
done

inductive less_eq_nat
where
  "less_eq_nat 0 y"
| "less_eq_nat x y ==> less_eq_nat (Suc x) (Suc y)"

lemma [code_pred_inline]:
"x <= y = less_eq_nat x y"
apply (rule iffI)
apply (induct x arbitrary: y)
apply (auto intro: less_eq_nat.intros)
apply (case_tac y) apply (auto intro: less_eq_nat.intros)
apply (induct rule: less_eq_nat.induct)
apply auto done

section \<open>Alternative list definitions\<close>

subsection \<open>Alternative rules for \<open>length\<close>\<close>

definition size_list' :: "'a list => nat"
where "size_list' = size"

lemma size_list'_simps:
  "size_list' [] = 0"
  "size_list' (x # xs) = Suc (size_list' xs)"
by (auto simp add: size_list'_def)

declare size_list'_simps[code_pred_def]
declare size_list'_def[symmetric, code_pred_inline]


subsection \<open>Alternative rules for \<open>list_all2\<close>\<close>

lemma list_all2_NilI [code_pred_intro]: "list_all2 P [] []"
by auto

lemma list_all2_ConsI [code_pred_intro]: "list_all2 P xs ys ==> P x y ==> list_all2 P (x#xs) (y#ys)"
by auto

code_pred [skip_proof] list_all2
proof -
  case list_all2
  from this show thesis
    apply -
    apply (case_tac xb)
    apply (case_tac xc)
    apply auto
    apply (case_tac xc)
    apply auto
    done
qed

subsection \<open>Alternative rules for membership in lists\<close>

declare in_set_member[code_pred_inline]

lemma member_intros [code_pred_intro]:
  "List.member (x#xs) x"
  "List.member xs x \<Longrightarrow> List.member (y#xs) x"
by(simp_all add: List.member_def)

code_pred List.member
  by(auto simp add: List.member_def elim: list.set_cases)

code_identifier constant member_i_i
   \<rightharpoonup> (SML) "List.member_i_i"
  and (OCaml) "List.member_i_i"
  and (Haskell) "List.member_i_i"
  and (Scala) "List.member_i_i"

code_identifier constant member_i_o
   \<rightharpoonup> (SML) "List.member_i_o"
  and (OCaml) "List.member_i_o"
  and (Haskell) "List.member_i_o"
  and (Scala) "List.member_i_o"

section \<open>Setup for String.literal\<close>

setup \<open>Predicate_Compile_Data.ignore_consts [@{const_name "STR"}]\<close>

section \<open>Simplification rules for optimisation\<close>

lemma [code_pred_simp]: "\<not> False == True"
by auto

lemma [code_pred_simp]: "\<not> True == False"
by auto

lemma less_nat_k_0 [code_pred_simp]: "less_nat k 0 == False"
unfolding less_nat[symmetric] by auto

end
