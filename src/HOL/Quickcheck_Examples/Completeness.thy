(*  Title:      HOL/Quickcheck_Examples/Completeness.thy
    Author:     Lukas Bulwahn
    Copyright   2012 TU Muenchen
*)

header {* Proving completeness of exhaustive generators *}

theory Completeness
imports Main
begin

subsection {* Preliminaries *}

primrec is_some
where
  "is_some (Some t) = True"
| "is_some None = False"

setup {* Exhaustive_Generators.setup_exhaustive_datatype_interpretation *} 

subsection {* Defining the size of values *}

hide_const size

class size =
  fixes size :: "'a => nat"

instantiation int :: size
begin

definition size_int :: "int => nat"
where
  "size_int n = nat (abs n)"

instance ..

end

instantiation code_numeral :: size
begin

definition size_code_numeral :: "code_numeral => nat"
where
  "size_code_numeral = Code_Numeral.nat_of"

instance ..

end

instantiation nat :: size
begin

definition size_nat :: "nat => nat"
where
  "size_nat n = n"

instance ..

end

instantiation list :: (size) size
begin

primrec size_list :: "'a list => nat"
where
  "size [] = 1"
| "size (x # xs) = max (size x) (size xs) + 1"

instance ..

end

subsection {* Completeness *}

class complete = exhaustive + size +
assumes
   complete: "(\<exists> v. size v \<le> n \<and> is_some (f v)) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"

lemma complete_imp1:
  "size (v :: 'a :: complete) \<le> n \<Longrightarrow> is_some (f v) \<Longrightarrow> is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"
by (metis complete)

lemma complete_imp2:
  assumes "is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"
  obtains v where "size (v :: 'a :: complete) \<le> n" "is_some (f v)"
using assms by (metis complete)

subsubsection {* Instance Proofs *}

declare exhaustive'.simps [simp del]

lemma complete_exhaustive':
  "(\<exists> i. j <= i & i <= k & is_some (f i)) \<longleftrightarrow> is_some (Quickcheck_Exhaustive.exhaustive' f k j)"
proof (induct rule: Quickcheck_Exhaustive.exhaustive'.induct[of _ f k j])
  case (1 f d i)
  show ?case
  proof (cases "f i")
    case None
    from this 1 show ?thesis
    unfolding exhaustive'.simps[of _ _ i] Quickcheck_Exhaustive.orelse_def
    apply auto
    apply (metis is_some.simps(2) order_le_neq_trans zless_imp_add1_zle)
    apply (metis add1_zle_eq less_int_def)
    done
  next
    case Some
    from this show ?thesis
    unfolding exhaustive'.simps[of _ _ i] Quickcheck_Exhaustive.orelse_def by auto
  qed
qed

lemma int_of_nat:
  "Code_Numeral.int_of (Code_Numeral.of_nat n) = int n"
unfolding int_of_def by simp

instance int :: complete
proof
  fix n f
  show "(\<exists>v. size (v :: int) \<le> n \<and> is_some (f v)) = is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"
    unfolding exhaustive_int_def complete_exhaustive'[symmetric]
    apply auto apply (rule_tac x="v" in exI)
    unfolding size_int_def by (metis int_of_nat abs_le_iff minus_le_iff nat_le_iff)+
qed

declare exhaustive_code_numeral'.simps[simp del]

lemma complete_code_numeral':
  "(\<exists>n. j \<le> n \<and> n \<le> k \<and> is_some (f n)) =
    is_some (Quickcheck_Exhaustive.exhaustive_code_numeral' f k j)"
proof (induct rule: exhaustive_code_numeral'.induct[of _ f k j])
  case (1 f k j)
  show "(\<exists>n\<ge>j. n \<le> k \<and> is_some (f n)) = is_some (Quickcheck_Exhaustive.exhaustive_code_numeral' f k j)"
  unfolding exhaustive_code_numeral'.simps[of f k j] Quickcheck_Exhaustive.orelse_def
  apply auto
  apply (auto split: option.split)
  apply (insert 1[symmetric])
  apply simp
  apply (metis is_some.simps(2) less_eq_code_numeral_def not_less_eq_eq order_antisym)
  apply simp
  apply (split option.split_asm)
  defer apply fastforce
  apply simp by (metis Suc_leD)
qed

instance code_numeral :: complete
proof
  fix n f
  show "(\<exists>v. size (v :: code_numeral) \<le> n \<and> is_some (f v)) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"
  unfolding exhaustive_code_numeral_def complete_code_numeral'[symmetric]
  by (auto simp add: size_code_numeral_def)
qed  

instance nat :: complete
proof
  fix n f
  show "(\<exists>v. size (v :: nat) \<le> n \<and> is_some (f v)) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"
    unfolding exhaustive_nat_def complete[of n "%x. f (Code_Numeral.nat_of x)", symmetric]
    apply auto
    apply (rule_tac x="Code_Numeral.of_nat v" in exI)
    apply (auto simp add: size_code_numeral_def size_nat_def) done
qed

instance list :: (complete) complete
proof
  fix n f
  show "(\<exists> v. size (v :: 'a list) \<le> n \<and> is_some (f (v :: 'a list))) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat n))"
  proof (induct n arbitrary: f)
    case 0
    { fix v have "size (v :: 'a list) > 0" by (induct v) auto }
    from this show ?case by (simp add: list.exhaustive_list.simps)
  next
    case (Suc n)
    show ?case
    proof
      assume "\<exists>v. Completeness.size_class.size v \<le> Suc n \<and> is_some (f v)"
      from this guess v .. note v = this
      show "is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat (Suc n)))"
      proof (cases "v")
      case Nil
        from this v show ?thesis
          unfolding list.exhaustive_list.simps[of _ "Code_Numeral.of_nat (Suc n)"] Quickcheck_Exhaustive.orelse_def
          by (auto split: option.split)
      next 
      case (Cons v' vs')
        from Cons v have size_v': "Completeness.size_class.size v' \<le> n"
          and "Completeness.size_class.size vs' \<le> n" by auto
        from Suc v Cons this have "is_some (exhaustive_class.exhaustive (\<lambda>xs. f (v' # xs)) (Code_Numeral.of_nat n))"
          by metis
        from complete_imp1[OF size_v', of "%x. (exhaustive_class.exhaustive (\<lambda>xs. f (x # xs)) (Code_Numeral.of_nat n))", OF this]
        show ?thesis
          unfolding list.exhaustive_list.simps[of _ "Code_Numeral.of_nat (Suc n)"] Quickcheck_Exhaustive.orelse_def
          by (auto split: option.split)
      qed
    next
      assume is_some: "is_some (exhaustive_class.exhaustive f (Code_Numeral.of_nat (Suc n)))"
      show "\<exists>v. size v \<le> Suc n \<and> is_some (f v)"
      proof (cases "f []")
        case Some
        from this show ?thesis
        by (metis Suc_eq_plus1 is_some.simps(1) le_add2 size_list.simps(1))
      next
        case None
        from this is_some have
          "is_some (exhaustive_class.exhaustive (\<lambda>x. exhaustive_class.exhaustive (\<lambda>xs. f (x # xs)) (Code_Numeral.of_nat n)) (Code_Numeral.of_nat n))"
          unfolding list.exhaustive_list.simps[of _ "Code_Numeral.of_nat (Suc n)"] Quickcheck_Exhaustive.orelse_def
          by simp
        from complete_imp2[OF this] guess v' . note v = this
        from Suc[of "%xs. f (v' # xs)"] this(2) obtain vs' where "size vs' \<le> n" "is_some (f (v' # vs'))"
          by metis
        note vs' = this
        from this v have "size (v' # vs') \<le> Suc n" by auto
        from this vs' v show ?thesis by metis
      qed
    qed
  qed
qed

end
