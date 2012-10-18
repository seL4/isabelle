(*  Title:      HOL/Metis_Examples/Sets.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring typed set theory.
*)

header {* Metis Example Featuring Typed Set Theory *}

theory Sets
imports Main
begin

declare [[metis_new_skolemizer]]

lemma "EX x X. ALL y. EX z Z. (~P(y,y) | P(x,x) | ~S(z,x)) &
               (S(x,y) | ~S(y,z) | Q(Z,Z))  &
               (Q(X,y) | ~Q(y,Z) | S(X,X))"
by metis

lemma "P(n::nat) ==> ~P(0) ==> n ~= 0"
by metis

sledgehammer_params [isar_proofs, isar_shrinkage = 1]

(*multiple versions of this example*)
lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>1 \<union> x\<^isub>2" by (metis Un_commute Un_upper2)
  have F2a: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>2 \<longrightarrow> x\<^isub>2 = x\<^isub>2 \<union> x\<^isub>1" by (metis Un_commute subset_Un_eq)
  have F2: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>2 \<and> x\<^isub>2 \<subseteq> x\<^isub>1 \<longrightarrow> x\<^isub>1 = x\<^isub>2" by (metis F2a subset_Un_eq)
  { assume "\<not> Z \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
  moreover
  { assume AA1: "Y \<union> Z \<noteq> X"
    { assume "\<not> Y \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis F1) }
    moreover
    { assume AAA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
      { assume "\<not> Z \<subseteq> X"
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
      moreover
      { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
        hence "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z" by (metis Un_subset_iff)
        hence "Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> Y \<union> Z" by (metis F2)
        hence "\<exists>x\<^isub>1\<Colon>'a set. Y \<subseteq> x\<^isub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^isub>1 \<union> Z" by (metis F1)
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
      ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AAA1) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AA1) }
  moreover
  { assume "\<exists>x\<^isub>1\<Colon>'a set. (Z \<subseteq> x\<^isub>1 \<and> Y \<subseteq> x\<^isub>1) \<and> \<not> X \<subseteq> x\<^isub>1"
    { assume "\<not> Y \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis F1) }
    moreover
    { assume AAA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
      { assume "\<not> Z \<subseteq> X"
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
      moreover
      { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
        hence "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z" by (metis Un_subset_iff)
        hence "Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> Y \<union> Z" by (metis F2)
        hence "\<exists>x\<^isub>1\<Colon>'a set. Y \<subseteq> x\<^isub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^isub>1 \<union> Z" by (metis F1)
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
      ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AAA1) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by blast }
  moreover
  { assume "\<not> Y \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis F1) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by metis
qed

sledgehammer_params [isar_proofs, isar_shrinkage = 2]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>2 \<and> x\<^isub>2 \<subseteq> x\<^isub>1 \<longrightarrow> x\<^isub>1 = x\<^isub>2" by (metis Un_commute subset_Un_eq)
  { assume AA1: "\<exists>x\<^isub>1\<Colon>'a set. (Z \<subseteq> x\<^isub>1 \<and> Y \<subseteq> x\<^isub>1) \<and> \<not> X \<subseteq> x\<^isub>1"
    { assume AAA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
      { assume "\<not> Z \<subseteq> X"
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
      moreover
      { assume "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z"
        hence "\<exists>x\<^isub>1\<Colon>'a set. Y \<subseteq> x\<^isub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^isub>1 \<union> Z" by (metis F1 Un_commute Un_upper2)
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
      ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AAA1 Un_subset_iff) }
    moreover
    { assume "\<not> Y \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_commute Un_upper2) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AA1 Un_subset_iff) }
  moreover
  { assume "\<not> Z \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
  moreover
  { assume "\<not> Y \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_commute Un_upper2) }
  moreover
  { assume AA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
    { assume "\<not> Z \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
    moreover
    { assume "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z"
      hence "\<exists>x\<^isub>1\<Colon>'a set. Y \<subseteq> x\<^isub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^isub>1 \<union> Z" by (metis F1 Un_commute Un_upper2)
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AA1 Un_subset_iff) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by metis
qed

sledgehammer_params [isar_proofs, isar_shrinkage = 3]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1a: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>2 \<longrightarrow> x\<^isub>2 = x\<^isub>2 \<union> x\<^isub>1" by (metis Un_commute subset_Un_eq)
  have F1: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>2 \<and> x\<^isub>2 \<subseteq> x\<^isub>1 \<longrightarrow> x\<^isub>1 = x\<^isub>2" by (metis F1a subset_Un_eq)
  { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis F1 Un_commute Un_subset_iff Un_upper2) }
  moreover
  { assume AA1: "\<exists>x\<^isub>1\<Colon>'a set. (Z \<subseteq> x\<^isub>1 \<and> Y \<subseteq> x\<^isub>1) \<and> \<not> X \<subseteq> x\<^isub>1"
    { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis F1 Un_commute Un_subset_iff Un_upper2) }
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AA1 Un_commute Un_subset_iff Un_upper2) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_commute Un_upper2)
qed

sledgehammer_params [isar_proofs, isar_shrinkage = 4]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1: "\<forall>(x\<^isub>2\<Colon>'b set) x\<^isub>1\<Colon>'b set. x\<^isub>1 \<subseteq> x\<^isub>2 \<and> x\<^isub>2 \<subseteq> x\<^isub>1 \<longrightarrow> x\<^isub>1 = x\<^isub>2" by (metis Un_commute subset_Un_eq)
  { assume "\<not> Y \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_commute Un_upper2) }
  moreover
  { assume AA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
    { assume "\<exists>x\<^isub>1\<Colon>'a set. Y \<subseteq> x\<^isub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^isub>1 \<union> Z"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_upper2) }
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis AA1 F1 Un_commute Un_subset_iff Un_upper2) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V\<Colon>'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (metis Un_subset_iff Un_upper2)
qed

sledgehammer_params [isar_proofs, isar_shrinkage = 1]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
by (metis Un_least Un_upper1 Un_upper2 set_eq_subset)

lemma "(X = Y \<inter> Z) = (X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
by (metis Int_greatest Int_lower1 Int_lower2 subset_antisym)

lemma fixedpoint: "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
by metis

lemma (* fixedpoint: *) "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
proof -
  assume "\<exists>!x\<Colon>'a. f (g x) = x"
  thus "\<exists>!y\<Colon>'b. g (f y) = y" by metis
qed

lemma (* singleton_example_2: *)
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by (metis Set.subsetI Union_upper insertCI set_eq_subset)

lemma (* singleton_example_2: *)
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by (metis Set.subsetI Union_upper insert_iff set_eq_subset)

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
proof -
  assume "\<forall>x \<in> S. \<Union>S \<subseteq> x"
  hence "\<forall>x\<^isub>1. x\<^isub>1 \<subseteq> \<Union>S \<and> x\<^isub>1 \<in> S \<longrightarrow> x\<^isub>1 = \<Union>S" by (metis set_eq_subset)
  hence "\<forall>x\<^isub>1. x\<^isub>1 \<in> S \<longrightarrow> x\<^isub>1 = \<Union>S" by (metis Union_upper)
  hence "\<forall>x\<^isub>1\<Colon>('a set) set. \<Union>S \<in> x\<^isub>1 \<longrightarrow> S \<subseteq> x\<^isub>1" by (metis subsetI)
  hence "\<forall>x\<^isub>1\<Colon>('a set) set. S \<subseteq> insert (\<Union>S) x\<^isub>1" by (metis insert_iff)
  thus "\<exists>z. S \<subseteq> {z}" by metis
qed

text {*
  From W. W. Bledsoe and Guohui Feng, SET-VAR. JAR 11 (3), 1993, pages
  293-314.
*}

(* Notes: (1) The numbering doesn't completely agree with the paper.
   (2) We must rename set variables to avoid type clashes. *)
lemma "\<exists>B. (\<forall>x \<in> B. x \<le> (0::int))"
      "D \<in> F \<Longrightarrow> \<exists>G. \<forall>A \<in> G. \<exists>B \<in> F. A \<subseteq> B"
      "P a \<Longrightarrow> \<exists>A. (\<forall>x \<in> A. P x) \<and> (\<exists>y. y \<in> A)"
      "a < b \<and> b < (c::int) \<Longrightarrow> \<exists>B. a \<notin> B \<and> b \<in> B \<and> c \<notin> B"
      "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
      "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
      "\<exists>A. a \<notin> A"
      "(\<forall>C. (0, 0) \<in> C \<and> (\<forall>x y. (x, y) \<in> C \<longrightarrow> (Suc x, Suc y) \<in> C) \<longrightarrow> (n, m) \<in> C) \<and> Q n \<longrightarrow> Q m"
       apply (metis all_not_in_conv)
      apply (metis all_not_in_conv)
     apply (metis mem_Collect_eq)
    apply (metis less_le singleton_iff)
   apply (metis mem_Collect_eq)
  apply (metis mem_Collect_eq)
 apply (metis all_not_in_conv)
by (metis pair_in_Id_conv)

end
