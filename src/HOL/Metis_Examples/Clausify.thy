(*  Title:      HOL/Metis_Examples/Clausify.thy
    Author:     Jasmin Blanchette, TU Muenchen

Testing Metis's clausifier.
*)

theory Clausify
imports Complex_Main
begin

(* FIXME: shouldn't need this *)
declare [[unify_search_bound = 100]]
declare [[unify_trace_bound = 100]]

text {* Definitional CNF for facts *}

declare [[meson_max_clauses = 10]]

axiomatization q :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
qax: "\<exists>b. \<forall>a. (q b a \<and> q 0 0 \<and> q 1 a \<and> q a 1) \<or> (q 0 1 \<and> q 1 0 \<and> q a b \<and> q 1 1)"

declare [[metis_new_skolemizer = false]]

lemma "\<exists>b. \<forall>a. (q b a \<or> q a b)"
by (metis qax)

lemma "\<exists>b. \<forall>a. (q b a \<or> q a b)"
by (metisFT qax)

lemma "\<exists>b. \<forall>a. (q b a \<and> q 0 0 \<and> q 1 a \<and> q a 1) \<or> (q 0 1 \<and> q 1 0 \<and> q a b \<and> q 1 1)"
by (metis qax)

lemma "\<exists>b. \<forall>a. (q b a \<and> q 0 0 \<and> q 1 a \<and> q a 1) \<or> (q 0 1 \<and> q 1 0 \<and> q a b \<and> q 1 1)"
by (metisFT qax)

declare [[metis_new_skolemizer]]

lemma "\<exists>b. \<forall>a. (q b a \<or> q a b)"
by (metis qax)

lemma "\<exists>b. \<forall>a. (q b a \<or> q a b)"
by (metisFT qax)

lemma "\<exists>b. \<forall>a. (q b a \<and> q 0 0 \<and> q 1 a \<and> q a 1) \<or> (q 0 1 \<and> q 1 0 \<and> q a b \<and> q 1 1)"
by (metis qax)

lemma "\<exists>b. \<forall>a. (q b a \<and> q 0 0 \<and> q 1 a \<and> q a 1) \<or> (q 0 1 \<and> q 1 0 \<and> q a b \<and> q 1 1)"
by (metisFT qax)

declare [[meson_max_clauses = 60]]

axiomatization r :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
rax: "(r 0 0 \<and> r 0 1 \<and> r 0 2 \<and> r 0 3) \<or>
      (r 1 0 \<and> r 1 1 \<and> r 1 2 \<and> r 1 3) \<or>
      (r 2 0 \<and> r 2 1 \<and> r 2 2 \<and> r 2 3) \<or>
      (r 3 0 \<and> r 3 1 \<and> r 3 2 \<and> r 3 3)"

declare [[metis_new_skolemizer = false]]

lemma "r 0 0 \<or> r 1 1 \<or> r 2 2 \<or> r 3 3"
by (metis rax)

lemma "r 0 0 \<or> r 1 1 \<or> r 2 2 \<or> r 3 3"
by (metisFT rax)

declare [[metis_new_skolemizer]]

lemma "r 0 0 \<or> r 1 1 \<or> r 2 2 \<or> r 3 3"
by (metis rax)

lemma "r 0 0 \<or> r 1 1 \<or> r 2 2 \<or> r 3 3"
by (metisFT rax)

lemma "(r 0 0 \<and> r 0 1 \<and> r 0 2 \<and> r 0 3) \<or>
       (r 1 0 \<and> r 1 1 \<and> r 1 2 \<and> r 1 3) \<or>
       (r 2 0 \<and> r 2 1 \<and> r 2 2 \<and> r 2 3) \<or>
       (r 3 0 \<and> r 3 1 \<and> r 3 2 \<and> r 3 3)"
by (metis rax)

lemma "(r 0 0 \<and> r 0 1 \<and> r 0 2 \<and> r 0 3) \<or>
       (r 1 0 \<and> r 1 1 \<and> r 1 2 \<and> r 1 3) \<or>
       (r 2 0 \<and> r 2 1 \<and> r 2 2 \<and> r 2 3) \<or>
       (r 3 0 \<and> r 3 1 \<and> r 3 2 \<and> r 3 3)"
by (metisFT rax)

text {* Definitional CNF for goal *}

axiomatization p :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
pax: "\<exists>b. \<forall>a. (p b a \<and> p 0 0 \<and> p 1 a) \<or> (p 0 1 \<and> p 1 0 \<and> p a b)"

declare [[metis_new_skolemizer = false]]

lemma "\<exists>b. \<forall>a. \<exists>x. (p b a \<or> x) \<and> (p 0 0 \<or> x) \<and> (p 1 a \<or> x) \<and>
                   (p 0 1 \<or> \<not> x) \<and> (p 1 0 \<or> \<not> x) \<and> (p a b \<or> \<not> x)"
by (metis pax)

lemma "\<exists>b. \<forall>a. \<exists>x. (p b a \<or> x) \<and> (p 0 0 \<or> x) \<and> (p 1 a \<or> x) \<and>
                   (p 0 1 \<or> \<not> x) \<and> (p 1 0 \<or> \<not> x) \<and> (p a b \<or> \<not> x)"
by (metisFT pax)

declare [[metis_new_skolemizer]]

lemma "\<exists>b. \<forall>a. \<exists>x. (p b a \<or> x) \<and> (p 0 0 \<or> x) \<and> (p 1 a \<or> x) \<and>
                   (p 0 1 \<or> \<not> x) \<and> (p 1 0 \<or> \<not> x) \<and> (p a b \<or> \<not> x)"
by (metis pax)

lemma "\<exists>b. \<forall>a. \<exists>x. (p b a \<or> x) \<and> (p 0 0 \<or> x) \<and> (p 1 a \<or> x) \<and>
                   (p 0 1 \<or> \<not> x) \<and> (p 1 0 \<or> \<not> x) \<and> (p a b \<or> \<not> x)"
by (metisFT pax)

text {* New Skolemizer *}

declare [[metis_new_skolemizer]]

lemma
  fixes x :: real
  assumes fn_le: "!!n. f n \<le> x" and 1: "f ----> lim f"
  shows "lim f \<le> x"
by (metis 1 LIMSEQ_le_const2 fn_le)

definition
  bounded :: "'a::metric_space set \<Rightarrow> bool" where
  "bounded S \<longleftrightarrow> (\<exists>x eee. \<forall>y\<in>S. dist x y \<le> eee)"

lemma "bounded T \<Longrightarrow> S \<subseteq> T ==> bounded S"
by (metis bounded_def subset_eq)

lemma
  assumes a: "Quotient R Abs Rep"
  shows "symp R"
using a unfolding Quotient_def using sympI
by metisFT

lemma
  "(\<exists>x \<in> set xs. P x) \<longleftrightarrow>
   (\<exists>ys x zs. xs = ys @ x # zs \<and> P x \<and> (\<forall>z \<in> set zs. \<not> P z))"
by (metis split_list_last_prop [where P = P] in_set_conv_decomp)

lemma ex_tl: "EX ys. tl ys = xs"
using tl.simps(2) by fast

lemma "(\<exists>ys\<Colon>nat list. tl ys = xs) \<and> (\<exists>bs\<Colon>int list. tl bs = as)"
by (metis ex_tl)

end
