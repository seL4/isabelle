(*  Title:      HOL/Quickcheck_Examples/Completeness.thy
    Author:     Lukas Bulwahn
    Copyright   2012 TU Muenchen
*)

section {* Proving completeness of exhaustive generators *}

theory Completeness
imports Main
begin

subsection {* Preliminaries *}

primrec is_some
where
  "is_some (Some t) = True"
| "is_some None = False"

lemma is_some_is_not_None:
  "is_some x \<longleftrightarrow> x \<noteq> None"
  by (cases x) simp_all

setup Exhaustive_Generators.setup_exhaustive_datatype_interpretation

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

instantiation natural :: size
begin

definition size_natural :: "natural => nat"
where
  "size_natural = nat_of_natural"

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
   complete: "(\<exists> v. size v \<le> n \<and> is_some (f v)) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (natural_of_nat n))"

lemma complete_imp1:
  "size (v :: 'a :: complete) \<le> n \<Longrightarrow> is_some (f v) \<Longrightarrow> is_some (exhaustive_class.exhaustive f (natural_of_nat n))"
by (metis complete)

lemma complete_imp2:
  assumes "is_some (exhaustive_class.exhaustive f (natural_of_nat n))"
  obtains v where "size (v :: 'a :: complete) \<le> n" "is_some (f v)"
using assms by (metis complete)

subsubsection {* Instance Proofs *}

declare exhaustive_int'.simps [simp del]

lemma complete_exhaustive':
  "(\<exists> i. j <= i & i <= k & is_some (f i)) \<longleftrightarrow> is_some (Quickcheck_Exhaustive.exhaustive_int' f k j)"
proof (induct rule: Quickcheck_Exhaustive.exhaustive_int'.induct[of _ f k j])
  case (1 f d i)
  show ?case
  proof (cases "f i")
    case None
    from this 1 show ?thesis
    unfolding exhaustive_int'.simps[of _ _ i] Quickcheck_Exhaustive.orelse_def
    apply (auto simp add: add1_zle_eq dest: less_imp_le)
    apply auto
    done
  next
    case Some
    from this show ?thesis
    unfolding exhaustive_int'.simps[of _ _ i] Quickcheck_Exhaustive.orelse_def by auto
  qed
qed

instance int :: complete
proof
  fix n f
  show "(\<exists>v. size (v :: int) \<le> n \<and> is_some (f v)) = is_some (exhaustive_class.exhaustive f (natural_of_nat n))"
    unfolding exhaustive_int_def complete_exhaustive'[symmetric]
    apply auto apply (rule_tac x="v" in exI)
    unfolding size_int_def by (metis abs_le_iff minus_le_iff nat_le_iff)+
qed

declare exhaustive_natural'.simps[simp del]

lemma complete_natural':
  "(\<exists>n. j \<le> n \<and> n \<le> k \<and> is_some (f n)) =
    is_some (Quickcheck_Exhaustive.exhaustive_natural' f k j)"
proof (induct rule: exhaustive_natural'.induct[of _ f k j])
  case (1 f k j)
  show "(\<exists>n\<ge>j. n \<le> k \<and> is_some (f n)) = is_some (Quickcheck_Exhaustive.exhaustive_natural' f k j)"
  unfolding exhaustive_natural'.simps [of f k j] Quickcheck_Exhaustive.orelse_def
  apply (auto split: option.split)
  apply (auto simp add: less_eq_natural_def less_natural_def 1 [symmetric] dest: Suc_leD)
  apply (metis is_some.simps(2) natural_eqI not_less_eq_eq order_antisym)
  done
qed

instance natural :: complete
proof
  fix n f
  show "(\<exists>v. size (v :: natural) \<le> n \<and> is_some (f v)) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (natural_of_nat n))"
  unfolding exhaustive_natural_def complete_natural' [symmetric]
    by (auto simp add: size_natural_def less_eq_natural_def)
qed  

instance nat :: complete
proof
  fix n f
  show "(\<exists>v. size (v :: nat) \<le> n \<and> is_some (f v)) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (natural_of_nat n))"
    unfolding exhaustive_nat_def complete[of n "%x. f (nat_of_natural x)", symmetric]
    apply auto
    apply (rule_tac x="natural_of_nat v" in exI)
    apply (auto simp add: size_natural_def size_nat_def) done
qed

instance list :: (complete) complete
proof
  fix n f
  show "(\<exists> v. size (v :: 'a list) \<le> n \<and> is_some (f (v :: 'a list))) \<longleftrightarrow> is_some (exhaustive_class.exhaustive f (natural_of_nat n))"
  proof (induct n arbitrary: f)
    case 0
    { fix v have "size (v :: 'a list) > 0" by (induct v) auto }
    from this show ?case by (simp add: list.exhaustive_list.simps)
  next
    case (Suc n)
    show ?case
    proof
      assume "\<exists>v. Completeness.size_class.size v \<le> Suc n \<and> is_some (f v)"
      then obtain v where v: "size v \<le> Suc n" "is_some (f v)" by blast
      show "is_some (exhaustive_class.exhaustive f (natural_of_nat (Suc n)))"
      proof (cases "v")
      case Nil
        from this v show ?thesis
          unfolding list.exhaustive_list.simps[of _ "natural_of_nat (Suc n)"] Quickcheck_Exhaustive.orelse_def
          by (auto split: option.split simp add: less_natural_def)
      next 
      case (Cons v' vs')
        from Cons v have size_v': "Completeness.size_class.size v' \<le> n"
          and "Completeness.size_class.size vs' \<le> n" by auto
        from Suc v Cons this have "is_some (exhaustive_class.exhaustive (\<lambda>xs. f (v' # xs)) (natural_of_nat n))"
          by metis
        from complete_imp1[OF size_v', of "%x. (exhaustive_class.exhaustive (\<lambda>xs. f (x # xs)) (natural_of_nat n))", OF this]
        show ?thesis
          unfolding list.exhaustive_list.simps[of _ "natural_of_nat (Suc n)"] Quickcheck_Exhaustive.orelse_def
          by (auto split: option.split simp add: less_natural_def)
      qed
    next
      assume is_some: "is_some (exhaustive_class.exhaustive f (natural_of_nat (Suc n)))"
      show "\<exists>v. size v \<le> Suc n \<and> is_some (f v)"
      proof (cases "f []")
        case Some
        then show ?thesis
        by (metis Suc_eq_plus1 is_some.simps(1) le_add2 size_list.simps(1))
      next
        case None
        with is_some have
          "is_some (exhaustive_class.exhaustive (\<lambda>x. exhaustive_class.exhaustive (\<lambda>xs. f (x # xs)) (natural_of_nat n)) (natural_of_nat n))"
          unfolding list.exhaustive_list.simps[of _ "natural_of_nat (Suc n)"] Quickcheck_Exhaustive.orelse_def
          by (simp add: less_natural_def)
        then obtain v' where
            v: "size v' \<le> n"
              "is_some (exhaustive_class.exhaustive (\<lambda>xs. f (v' # xs)) (natural_of_nat n))"
          by (rule complete_imp2)
        with Suc[of "%xs. f (v' # xs)"]
        obtain vs' where vs': "size vs' \<le> n" "is_some (f (v' # vs'))"
          by metis
        with v have "size (v' # vs') \<le> Suc n" by auto
        with vs' v show ?thesis by metis
      qed
    qed
  qed
qed

end

