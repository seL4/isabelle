theory Predicate_Compile_Alternative_Defs
imports Main
begin

section {* Common constants *}

declare HOL.if_bool_eq_disj[code_pred_inline]

declare bool_diff_def[code_pred_inline]
declare inf_bool_def_raw[code_pred_inline]
declare less_bool_def_raw[code_pred_inline]
declare le_bool_def_raw[code_pred_inline]

lemma min_bool_eq [code_pred_inline]: "(min :: bool => bool => bool) == (op &)"
by (rule eq_reflection) (auto simp add: fun_eq_iff min_def le_bool_def)

lemma [code_pred_inline]: 
  "((A::bool) ~= (B::bool)) = ((A & ~ B) | (B & ~ A))"
by fast

setup {* Predicate_Compile_Data.ignore_consts [@{const_name Let}] *}

section {* Pairs *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name fst}, @{const_name snd}, @{const_name prod_case}] *}

section {* Bounded quantifiers *}

declare Ball_def[code_pred_inline]
declare Bex_def[code_pred_inline]

section {* Set operations *}

declare Collect_def[code_pred_inline]
declare mem_def[code_pred_inline]

declare eq_reflection[OF empty_def, code_pred_inline]
declare insert_code[code_pred_def]

declare subset_iff[code_pred_inline]

declare Int_def[code_pred_inline]
declare eq_reflection[OF Un_def, code_pred_inline]
declare eq_reflection[OF UNION_eq, code_pred_inline]

lemma Diff[code_pred_inline]:
  "(A - B) = (%x. A x \<and> \<not> B x)"
by (auto simp add: mem_def)

lemma subset_eq[code_pred_inline]:
  "(P :: 'a => bool) < (Q :: 'a => bool) == ((\<exists>x. Q x \<and> (\<not> P x)) \<and> (\<forall> x. P x --> Q x))"
by (rule eq_reflection) (fastforce simp add: mem_def)

lemma set_equality[code_pred_inline]:
  "(A = B) = ((\<forall>x. A x \<longrightarrow> B x) \<and> (\<forall>x. B x \<longrightarrow> A x))"
by (fastforce simp add: mem_def)

section {* Setup for Numerals *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name number_of}] *}
setup {* Predicate_Compile_Data.keep_functions [@{const_name number_of}] *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name div}, @{const_name mod}, @{const_name times}] *}

section {* Arithmetic operations *}

subsection {* Arithmetic on naturals and integers *}

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

setup {*
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
      val T = Predicate_Compile_Aux.mk_predT compfuns @{typ nat}
    in
      absdummy @{typ nat} (absdummy @{typ nat}
        (Const (@{const_name "If"}, @{typ bool} --> T --> T --> T) $
          (@{term "op > :: nat => nat => bool"} $ Bound 1 $ Bound 0) $
          Predicate_Compile_Aux.mk_bot compfuns @{typ nat} $
          Predicate_Compile_Aux.mk_single compfuns
          (@{term "op - :: nat => nat => nat"} $ Bound 0 $ Bound 1)))
    end
  fun enumerate_addups_nat compfuns (_ : typ) =
    absdummy @{typ nat} (Predicate_Compile_Aux.mk_iterate_upto compfuns @{typ "nat * nat"}
    (absdummy @{typ code_numeral} (@{term "Pair :: nat => nat => nat * nat"} $
      (@{term "Code_Numeral.nat_of"} $ Bound 0) $
      (@{term "op - :: nat => nat => nat"} $ Bound 1 $ (@{term "Code_Numeral.nat_of"} $ Bound 0))),
      @{term "0 :: code_numeral"}, @{term "Code_Numeral.of_nat"} $ Bound 0))
  fun enumerate_nats compfuns  (_ : typ) =
    let
      val (single_const, _) = strip_comb (Predicate_Compile_Aux.mk_single compfuns @{term "0 :: nat"})
      val T = Predicate_Compile_Aux.mk_predT compfuns @{typ nat}
    in
      absdummy @{typ nat} (absdummy @{typ nat}
        (Const (@{const_name If}, @{typ bool} --> T --> T --> T) $
          (@{term "op = :: nat => nat => bool"} $ Bound 0 $ @{term "0::nat"}) $
          (Predicate_Compile_Aux.mk_iterate_upto compfuns @{typ nat} (@{term "Code_Numeral.nat_of"},
            @{term "0::code_numeral"}, @{term "Code_Numeral.of_nat"} $ Bound 1)) $
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
*}

subsection {* Inductive definitions for ordering on naturals *}

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

section {* Alternative list definitions *}

subsection {* Alternative rules for length *}

definition size_list :: "'a list => nat"
where "size_list = size"

lemma size_list_simps:
  "size_list [] = 0"
  "size_list (x # xs) = Suc (size_list xs)"
by (auto simp add: size_list_def)

declare size_list_simps[code_pred_def]
declare size_list_def[symmetric, code_pred_inline]

subsection {* Alternative rules for set *}

lemma set_ConsI1 [code_pred_intro]:
  "set (x # xs) x"
unfolding mem_def[symmetric, of _ x]
by auto

lemma set_ConsI2 [code_pred_intro]:
  "set xs x ==> set (x' # xs) x" 
unfolding mem_def[symmetric, of _ x]
by auto

code_pred [skip_proof] set
proof -
  case set
  from this show thesis
    apply (case_tac xb)
    apply auto
    unfolding mem_def[symmetric, of _ xc]
    apply auto
    unfolding mem_def
    apply fastforce
    done
qed

subsection {* Alternative rules for list_all2 *}

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
    apply fastforce
    done
qed

section {* Setup for String.literal *}

setup {* Predicate_Compile_Data.ignore_consts [@{const_name "STR"}] *}

section {* Simplification rules for optimisation *}

lemma [code_pred_simp]: "\<not> False == True"
by auto

lemma [code_pred_simp]: "\<not> True == False"
by auto

lemma less_nat_k_0 [code_pred_simp]: "less_nat k 0 == False"
unfolding less_nat[symmetric] by auto


end