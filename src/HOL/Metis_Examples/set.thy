(*  Title:      HOL/Metis_Examples/set.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method.
*)

theory set
imports Main
begin

lemma "EX x X. ALL y. EX z Z. (~P(y,y) | P(x,x) | ~S(z,x)) &
               (S(x,y) | ~S(y,z) | Q(Z,Z))  &
               (Q(X,y) | ~Q(y,Z) | S(X,X))" 
by metis
(*??But metis can't prove the single-step version...*)



lemma "P(n::nat) ==> ~P(0) ==> n ~= 0"
by metis

declare [[sledgehammer_modulus = 1]]


(*multiple versions of this example*)
lemma (*equal_union: *)
   "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof (neg_clausify)
fix x
assume 0: "Y \<subseteq> X \<or> X = Y \<union> Z"
assume 1: "Z \<subseteq> X \<or> X = Y \<union> Z"
assume 2: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Y \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 3: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Z \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 4: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> \<not> X \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 5: "\<And>V. ((\<not> Y \<subseteq> V \<or> \<not> Z \<subseteq> V) \<or> X \<subseteq> V) \<or> X = Y \<union> Z"
have 6: "sup Y Z = X \<or> Y \<subseteq> X"
  by (metis 0)
have 7: "sup Y Z = X \<or> Z \<subseteq> X"
  by (metis 1)
have 8: "\<And>X3. sup Y Z = X \<or> X \<subseteq> X3 \<or> \<not> Y \<subseteq> X3 \<or> \<not> Z \<subseteq> X3"
  by (metis 5)
have 9: "Y \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 2)
have 10: "Z \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 3)
have 11: "sup Y Z \<noteq> X \<or> \<not> X \<subseteq> x \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 4)
have 12: "Z \<subseteq> X"
  by (metis Un_upper2 7)
have 13: "\<And>X3. sup Y Z = X \<or> X \<subseteq> sup X3 Z \<or> \<not> Y \<subseteq> sup X3 Z"
  by (metis 8 Un_upper2)
have 14: "Y \<subseteq> X"
  by (metis Un_upper1 6)
have 15: "Z \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X"
  by (metis 10 12)
have 16: "Y \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X"
  by (metis 9 12)
have 17: "sup Y Z \<noteq> X \<or> \<not> X \<subseteq> x \<or> \<not> Y \<subseteq> X"
  by (metis 11 12)
have 18: "sup Y Z \<noteq> X \<or> \<not> X \<subseteq> x"
  by (metis 17 14)
have 19: "Z \<subseteq> x \<or> sup Y Z \<noteq> X"
  by (metis 15 14)
have 20: "Y \<subseteq> x \<or> sup Y Z \<noteq> X"
  by (metis 16 14)
have 21: "sup Y Z = X \<or> X \<subseteq> sup Y Z"
  by (metis 13 Un_upper1)
have 22: "sup Y Z = X \<or> \<not> sup Y Z \<subseteq> X"
  by (metis equalityI 21)
have 23: "sup Y Z = X \<or> \<not> Z \<subseteq> X \<or> \<not> Y \<subseteq> X"
  by (metis 22 Un_least)
have 24: "sup Y Z = X \<or> \<not> Y \<subseteq> X"
  by (metis 23 12)
have 25: "sup Y Z = X"
  by (metis 24 14)
have 26: "\<And>X3. X \<subseteq> X3 \<or> \<not> Z \<subseteq> X3 \<or> \<not> Y \<subseteq> X3"
  by (metis Un_least 25)
have 27: "Y \<subseteq> x"
  by (metis 20 25)
have 28: "Z \<subseteq> x"
  by (metis 19 25)
have 29: "\<not> X \<subseteq> x"
  by (metis 18 25)
have 30: "X \<subseteq> x \<or> \<not> Y \<subseteq> x"
  by (metis 26 28)
have 31: "X \<subseteq> x"
  by (metis 30 27)
show "False"
  by (metis 31 29)
qed

declare [[sledgehammer_modulus = 2]]

lemma (*equal_union: *)
   "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof (neg_clausify)
fix x
assume 0: "Y \<subseteq> X \<or> X = Y \<union> Z"
assume 1: "Z \<subseteq> X \<or> X = Y \<union> Z"
assume 2: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Y \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 3: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Z \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 4: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> \<not> X \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 5: "\<And>V. ((\<not> Y \<subseteq> V \<or> \<not> Z \<subseteq> V) \<or> X \<subseteq> V) \<or> X = Y \<union> Z"
have 6: "sup Y Z = X \<or> Y \<subseteq> X"
  by (metis 0)
have 7: "Y \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 2)
have 8: "sup Y Z \<noteq> X \<or> \<not> X \<subseteq> x \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 4)
have 9: "\<And>X3. sup Y Z = X \<or> X \<subseteq> sup X3 Z \<or> \<not> Y \<subseteq> sup X3 Z"
  by (metis 5 Un_upper2)
have 10: "Z \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X"
  by (metis 3 Un_upper2)
have 11: "sup Y Z \<noteq> X \<or> \<not> X \<subseteq> x \<or> \<not> Y \<subseteq> X"
  by (metis 8 Un_upper2)
have 12: "Z \<subseteq> x \<or> sup Y Z \<noteq> X"
  by (metis 10 Un_upper1)
have 13: "sup Y Z = X \<or> X \<subseteq> sup Y Z"
  by (metis 9 Un_upper1)
have 14: "sup Y Z = X \<or> \<not> Z \<subseteq> X \<or> \<not> Y \<subseteq> X"
  by (metis equalityI 13 Un_least)
have 15: "sup Y Z = X"
  by (metis 14 1 6)
have 16: "Y \<subseteq> x"
  by (metis 7 Un_upper2 Un_upper1 15)
have 17: "\<not> X \<subseteq> x"
  by (metis 11 Un_upper1 15)
have 18: "X \<subseteq> x"
  by (metis Un_least 15 12 15 16)
show "False"
  by (metis 18 17)
qed

declare [[sledgehammer_modulus = 3]]

lemma (*equal_union: *)
   "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof (neg_clausify)
fix x
assume 0: "Y \<subseteq> X \<or> X = Y \<union> Z"
assume 1: "Z \<subseteq> X \<or> X = Y \<union> Z"
assume 2: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Y \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 3: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Z \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 4: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> \<not> X \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 5: "\<And>V. ((\<not> Y \<subseteq> V \<or> \<not> Z \<subseteq> V) \<or> X \<subseteq> V) \<or> X = Y \<union> Z"
have 6: "Z \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 3)
have 7: "\<And>X3. sup Y Z = X \<or> X \<subseteq> sup X3 Z \<or> \<not> Y \<subseteq> sup X3 Z"
  by (metis 5 Un_upper2)
have 8: "Y \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X"
  by (metis 2 Un_upper2)
have 9: "Z \<subseteq> x \<or> sup Y Z \<noteq> X"
  by (metis 6 Un_upper2 Un_upper1)
have 10: "sup Y Z = X \<or> \<not> sup Y Z \<subseteq> X"
  by (metis equalityI 7 Un_upper1)
have 11: "sup Y Z = X"
  by (metis 10 Un_least 1 0)
have 12: "Z \<subseteq> x"
  by (metis 9 11)
have 13: "X \<subseteq> x"
  by (metis Un_least 11 12 8 Un_upper1 11)
show "False"
  by (metis 13 4 Un_upper2 Un_upper1 11)
qed

(*Example included in TPHOLs paper*)

declare [[sledgehammer_modulus = 4]]

lemma (*equal_union: *)
   "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof (neg_clausify)
fix x
assume 0: "Y \<subseteq> X \<or> X = Y \<union> Z"
assume 1: "Z \<subseteq> X \<or> X = Y \<union> Z"
assume 2: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Y \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 3: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> Z \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 4: "(\<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X \<or> \<not> X \<subseteq> x) \<or> X \<noteq> Y \<union> Z"
assume 5: "\<And>V. ((\<not> Y \<subseteq> V \<or> \<not> Z \<subseteq> V) \<or> X \<subseteq> V) \<or> X = Y \<union> Z"
have 6: "sup Y Z \<noteq> X \<or> \<not> X \<subseteq> x \<or> \<not> Y \<subseteq> X \<or> \<not> Z \<subseteq> X"
  by (metis 4)
have 7: "Z \<subseteq> x \<or> sup Y Z \<noteq> X \<or> \<not> Y \<subseteq> X"
  by (metis 3 Un_upper2)
have 8: "Z \<subseteq> x \<or> sup Y Z \<noteq> X"
  by (metis 7 Un_upper1)
have 9: "sup Y Z = X \<or> \<not> Z \<subseteq> X \<or> \<not> Y \<subseteq> X"
  by (metis equalityI 5 Un_upper2 Un_upper1 Un_least)
have 10: "Y \<subseteq> x"
  by (metis 2 Un_upper2 1 Un_upper1 0 9 Un_upper2 1 Un_upper1 0)
have 11: "X \<subseteq> x"
  by (metis Un_least 9 Un_upper2 1 Un_upper1 0 8 9 Un_upper2 1 Un_upper1 0 10)
show "False"
  by (metis 11 6 Un_upper2 1 Un_upper1 0 9 Un_upper2 1 Un_upper1 0)
qed 

declare [[ atp_problem_prefix = "set__equal_union" ]]
lemma (*equal_union: *)
   "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" 
(*One shot proof: hand-reduced. Metis can't do the full proof any more.*)
by (metis Un_least Un_upper1 Un_upper2 set_eq_subset)


declare [[ atp_problem_prefix = "set__equal_inter" ]]
lemma "(X = Y \<inter> Z) =
    (X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
by (metis Int_greatest Int_lower1 Int_lower2 set_eq_subset)

declare [[ atp_problem_prefix = "set__fixedpoint" ]]
lemma fixedpoint:
    "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
by metis

lemma (*fixedpoint:*)
    "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
proof (neg_clausify)
fix x xa
assume 0: "f (g x) = x"
assume 1: "\<And>y. y = x \<or> f (g y) \<noteq> y"
assume 2: "\<And>x. g (f (xa x)) = xa x \<or> g (f x) \<noteq> x"
assume 3: "\<And>x. g (f x) \<noteq> x \<or> xa x \<noteq> x"
have 4: "\<And>X1. g (f X1) \<noteq> X1 \<or> g x \<noteq> X1"
  by (metis 3 1 2)
show "False"
  by (metis 4 0)
qed

declare [[ atp_problem_prefix = "set__singleton_example" ]]
lemma (*singleton_example_2:*)
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by (metis Set.subsetI Union_upper insertCI set_eq_subset)
  --{*found by SPASS*}

lemma (*singleton_example_2:*)
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by (metis Set.subsetI Union_upper insert_iff set_eq_subset)

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
proof (neg_clausify)
assume 0: "\<And>x. \<not> S \<subseteq> {x}"
assume 1: "\<And>x. x \<notin> S \<or> \<Union>S \<subseteq> x"
have 2: "\<And>X3. X3 = \<Union>S \<or> \<not> X3 \<subseteq> \<Union>S \<or> X3 \<notin> S"
  by (metis set_eq_subset 1)
have 3: "\<And>X3. S \<subseteq> insert (\<Union>S) X3"
  by (metis insert_iff Set.subsetI Union_upper 2 Set.subsetI)
show "False"
  by (metis 3 0)
qed



text {*
  From W. W. Bledsoe and Guohui Feng, SET-VAR. JAR 11 (3), 1993, pages
  293-314.
*}

declare [[ atp_problem_prefix = "set__Bledsoe_Fung" ]]
(*Notes: 1, the numbering doesn't completely agree with the paper. 
2, we must rename set variables to avoid type clashes.*)
lemma "\<exists>B. (\<forall>x \<in> B. x \<le> (0::int))"
      "D \<in> F \<Longrightarrow> \<exists>G. \<forall>A \<in> G. \<exists>B \<in> F. A \<subseteq> B"
      "P a \<Longrightarrow> \<exists>A. (\<forall>x \<in> A. P x) \<and> (\<exists>y. y \<in> A)"
      "a < b \<and> b < (c::int) \<Longrightarrow> \<exists>B. a \<notin> B \<and> b \<in> B \<and> c \<notin> B"
      "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
      "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
      "\<exists>A. a \<notin> A"
      "(\<forall>C. (0, 0) \<in> C \<and> (\<forall>x y. (x, y) \<in> C \<longrightarrow> (Suc x, Suc y) \<in> C) \<longrightarrow> (n, m) \<in> C) \<and> Q n \<longrightarrow> Q m" 
apply (metis atMost_iff)
apply (metis emptyE)
apply (metis insert_iff singletonE)
apply (metis insertCI singletonE zless_le)
apply (metis Collect_def Collect_mem_eq)
apply (metis Collect_def Collect_mem_eq)
apply (metis DiffE)
apply (metis pair_in_Id_conv) 
done

end
