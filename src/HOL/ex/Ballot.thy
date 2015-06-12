(*   Title: HOL/ex/Ballot.thy
     Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
*)

section {* Bertrand's Ballot Theorem *}

theory Ballot
imports
  Complex_Main
  "~~/src/HOL/Library/FuncSet"
begin

subsection {* Preliminaries *}

subsubsection {* Dedicated Simplification Setup *}

declare One_nat_def[simp del]
declare add_2_eq_Suc'[simp del]
declare atLeastAtMost_iff[simp del]
declare fun_upd_apply[simp del]

lemma [simp]: "1 \<le> n \<Longrightarrow> n : {1..(n :: nat)}"
by (auto simp add: atLeastAtMost_iff)

lemma [simp]: "(n :: nat) + 2 \<notin> {1..n + 1}"
by (auto simp add: atLeastAtMost_iff)

subsubsection {* Additions to @{theory Set} Theory *}

lemma ex1_iff_singleton: "(EX! x. x : S) \<longleftrightarrow> (EX x. S = {x})"
proof
  assume "EX! x. x : S"
  from this show "EX x. S = {x}"
    by (metis Un_empty_left Un_insert_left insertI1 insert_absorb subsetI subset_antisym)
next
  assume "EX x. S = {x}"
  thus "EX! x. x : S" by (metis (full_types) singleton_iff)
qed

subsubsection {* Additions to @{theory Finite_Set} Theory *}

lemma card_singleton[simp]: "card {x} = 1"
  by simp

lemma finite_bij_subset_implies_equal_sets:
  assumes "finite T" "\<exists>f. bij_betw f S T" "S <= T"
  shows "S = T"
using assms by (metis (lifting) bij_betw_def bij_betw_inv endo_inj_surj)

lemma singleton_iff_card_one: "(EX x. S = {x}) \<longleftrightarrow> card S = 1"
proof
  assume "EX x. S = {x}"
  then show "card S = 1" by auto
next
  assume c: "card S = 1"
  from this have s: "S \<noteq> {}" by (metis card_empty zero_neq_one)
  from this obtain a where a: "a \<in> S" by auto
  from this s obtain T where S: "S = insert a T" and a: "a \<notin> T"
    by (metis Set.set_insert)
  from c S a have "card T = 0"
    by (metis One_nat_def card_infinite card_insert_disjoint old.nat.inject)
  from this c S have "T = {}" by (metis (full_types) card_eq_0_iff finite_insert zero_neq_one)
  from this S show "EX x. S = {x}" by auto
qed

subsubsection {* Additions to @{theory Nat} Theory *}

lemma square_diff_square_factored_nat:
  shows "(x::nat) * x - y * y = (x + y) * (x - y)"
proof (cases "(x::nat) \<ge> y")
  case True
  from this show ?thesis by (simp add: algebra_simps diff_mult_distrib2)
next
  case False
  from this show ?thesis by (auto intro: mult_le_mono)
qed

subsubsection {* Additions to @{theory FuncSet} Theory *}

lemma extensional_constant_function_is_unique:
  assumes c: "c : T"
  shows "EX! f. f : S \<rightarrow>\<^sub>E T & (\<forall>x \<in> S. f x = c)"
proof
  def f == "(%x. if x \<in> S then c else undefined)"
  from c show "f : S \<rightarrow>\<^sub>E T & (\<forall>x \<in> S. f x = c)" unfolding f_def by auto
next
  fix f
  assume "f : S \<rightarrow>\<^sub>E T & (\<forall>x \<in> S. f x = c)"
  from this show "f = (%x. if x \<in> S then c else undefined)" by (metis PiE_E)
qed

lemma PiE_insert_restricted_eq:
  assumes a: "x \<notin> S"
  shows "{f : insert x S \<rightarrow>\<^sub>E T. P f} = (\<lambda>(y, g). g(x:=y)) ` (SIGMA y:T. {f : S \<rightarrow>\<^sub>E T. P (f(x := y))})"
proof -
  {
    fix f
    assume "f : {f : insert x S \<rightarrow>\<^sub>E T. P f}"
    from this a have "f :(\<lambda>(y, g). g(x:=y)) ` (SIGMA y:T. {f : S \<rightarrow>\<^sub>E T. P (f(x := y))})"
    by (auto intro!: image_eqI[where x="(f x, f(x:=undefined))"])
      (metis PiE_E fun_upd_other insertCI, metis (full_types) PiE_E fun_upd_in_PiE)
  } moreover
  {
    fix f
    assume "f :(\<lambda>(y, g). g(x:=y)) ` (SIGMA y:T. {f : S \<rightarrow>\<^sub>E T. P (f(x := y))})"
    from this have "f : {f : insert x S \<rightarrow>\<^sub>E T. P f}"
      by (auto elim!: PiE_fun_upd split: prod.split)
  }
  ultimately show ?thesis
    by (intro set_eqI iffI) assumption+
qed

lemma card_extensional_funcset_insert:
  assumes "x \<notin> S" "finite S" "finite T"
  shows "card {f : insert x S \<rightarrow>\<^sub>E T. P f} = (\<Sum>y\<in>T. card {f : S \<rightarrow>\<^sub>E T. P (f(x:=y))})"
proof -
  from `finite S` `finite T` have finite_funcset: "finite (S \<rightarrow>\<^sub>E T)" by (rule finite_PiE)
  have finite: "\<forall>y\<in>T. finite {f : S \<rightarrow>\<^sub>E T. P (f(x:=y))}"
    by (auto intro: finite_subset[OF _ finite_funcset])
  from `x \<notin> S`have inj: "inj_on (%(y, g). g(x:=y)) (UNIV \<times> (S \<rightarrow>\<^sub>E T))"
  unfolding inj_on_def
  by auto (metis fun_upd_same, metis PiE_E fun_upd_idem_iff fun_upd_upd fun_upd_same)
  from `x \<notin> S` have "card {f : insert x S \<rightarrow>\<^sub>E T. P f} =
    card ((\<lambda>(y, g). g(x:=y)) ` (SIGMA y:T. {f : S \<rightarrow>\<^sub>E T. P (f(x := y))}))"
    by (subst PiE_insert_restricted_eq) auto
  also from subset_inj_on[OF inj, of "SIGMA y:T. {f : S \<rightarrow>\<^sub>E T. P (f(x := y))}"]
  have "\<dots> = card (SIGMA y:T. {f : S \<rightarrow>\<^sub>E T. P (f(x := y))})" by (subst card_image) auto
  also from `finite T` finite have "\<dots> = (\<Sum>y\<in>T. card {f : S \<rightarrow>\<^sub>E T. P (f(x := y))})"
    by (simp only: card_SigmaI)
  finally show ?thesis .
qed

subsubsection {* Additions to @{theory Binomial} Theory *}

lemma Suc_times_binomial_add:
  "Suc a * (Suc (a + b) choose Suc a) = Suc b * (Suc (a + b) choose a)"
proof -
  have minus: "Suc (a + b) - a = Suc b" "Suc (a + b) - (Suc a) = b" by auto
  from fact_fact_dvd_fact[of "Suc a" "b"] have "fact (Suc a) * fact b dvd (fact (Suc a + b) :: nat)"
    by fast
  from this have dvd1: "Suc a * fact a * fact b dvd fact (Suc (a + b))"  
    by (simp only: fact_Suc add_Suc[symmetric] of_nat_id)
  have dvd2: "fact a * (Suc b * fact b) dvd fact (Suc (a + b))"
    by (metis add_Suc_right fact_Suc fact_fact_dvd_fact of_nat_id)
  have "Suc a * (Suc (a + b) choose Suc a) = Suc a * (fact (Suc (a + b)) div (fact (Suc a) * fact b))"
    by (simp only: binomial_altdef_nat minus(2))
  also have "... = Suc a * fact (Suc (a + b)) div (Suc a * (fact a * fact b))"
   unfolding fact_Suc[of a] div_mult_swap[OF dvd1] of_nat_id by (simp only: algebra_simps)
  also have "... = Suc b * fact (Suc (a + b)) div (Suc b * (fact a * fact b))"
    by (simp only: div_mult_mult1)
  also have "... = Suc b * (fact (Suc (a + b)) div (fact a * fact (Suc b)))"
    unfolding fact_Suc[of b] div_mult_swap[OF dvd2] of_nat_id by (simp only: algebra_simps)
  also have "... = Suc b * (Suc (a + b) choose a)"
    by (simp only: binomial_altdef_nat minus(1))
  finally show ?thesis .
qed

subsection {* Formalization of Problem Statement *}

subsubsection {* Basic Definitions *}

datatype vote = A | B

definition
  "all_countings a b = card {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = A} = a
    & card {x : {1 .. a + b}. f x = B} = b}"

definition
  "valid_countings a b =
    card {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = A} = a
    & card {x : {1 .. a + b}. f x = B} = b
    & (\<forall>m \<in> {1 .. a + b }. card {x \<in> {1..m}. f x = A} > card {x \<in> {1..m}. f x = B})}"

subsubsection {* Equivalence of Alternative Definitions *}

lemma definition_rewrite_generic:
  assumes "case vote of A \<Rightarrow> count = a | B \<Rightarrow> count = b"
  shows "{f \<in> {1..a + b} \<rightarrow>\<^sub>E {A, B}. card {x \<in> {1..a + b}. f x = A} = a \<and> card {x \<in> {1..a + b}. f x = B} = b \<and> P f}
   = {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = vote} = count \<and> P f}"
proof -
  let ?other_vote = "case vote of A \<Rightarrow> B | B \<Rightarrow> A"
  let ?other_count = "case vote of A \<Rightarrow> b | B \<Rightarrow> a" 
  {
    fix f
    assume "card {x : {1 .. a + b}. f x = vote} = count"
    from this have c: "card ({1 .. a + b} - {x : {1 .. a + b}. f x = vote}) = a + b - count"
      by (subst card_Diff_subset) auto
    have "{1 .. a + b} - {x : {1 .. a + b}. f x = vote} = {x : {1 .. a + b}. f x ~= vote}" by auto
    from this c have not_A:" card {x : {1 .. a + b}. f x ~= vote} = a + b - count" by auto
    have "!x. (f x ~= vote) = (f x = ?other_vote)"
      by (cases vote, auto) (case_tac "f x", auto)+
    from this not_A assms have "card {x : {1 .. a + b}. f x = ?other_vote} = ?other_count"
      by auto (cases vote, auto)
  }
  from this have "{f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}.
    card {x : {1 .. a + b}. f x = vote} = count & card {x : {1 .. a + b}. f x = ?other_vote} = ?other_count & P f} =
    {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = vote} = count & P f}"
    by auto
  from this assms show ?thesis by (cases vote) auto
qed

lemma all_countings_def':
  "all_countings a b = card {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = A} = a}"
unfolding all_countings_def definition_rewrite_generic[of a a _ A "\<lambda>_. True", simplified] ..

lemma all_countings_def'':
  "all_countings a b = card {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = B} = b}"
unfolding all_countings_def definition_rewrite_generic[of b _ b B  "\<lambda>_. True", simplified] ..

lemma valid_countings_def':
  "valid_countings a b =
    card {f : {1 .. a + b} \<rightarrow>\<^sub>E {A, B}. card {x : {1 .. a + b}. f x = A} = a
    & (\<forall>m \<in> {1 .. a + b }. card {x \<in> {1..m}. f x = A} > card {x \<in> {1..m}. f x = B})}"
unfolding valid_countings_def definition_rewrite_generic[of a a _ A, simplified] ..

subsubsection {* Cardinality of Sets of Functions *}

lemma one_extensional_constant_function:
  assumes "c : T"
  shows "card {f : S \<rightarrow>\<^sub>E T. (\<forall>x \<in> S. f x = c)} = 1"
using assms
  by (auto simp only: singleton_iff_card_one[symmetric] ex1_iff_singleton[symmetric] mem_Collect_eq
    elim!: extensional_constant_function_is_unique)

lemma card_filtered_set_eq_card_set_implies_forall:
  assumes f: "finite S"
  assumes c: "card {x : S. P x} = card S"
  shows "\<forall>x \<in> S. P x"
proof -
  from f c have "\<exists>f. bij_betw f {x : S. P x} S"
    by (metis Collect_mem_eq finite_Collect_conjI finite_same_card_bij)
  from f this have eq: "{x : S. P x} = S"
    by (metis (mono_tags) finite_bij_subset_implies_equal_sets Collect_mem_eq Collect_mono)
  from this show ?thesis by auto
qed

lemma card_filtered_set_from_n_eq_n_implies_forall:
  shows "(card {x : {1..n}. P x} = n) = (\<forall>x \<in> {1..n}. P x)"
proof
  assume "card {x : {1..n}. P x} = n"
  from this show "\<forall>x \<in> {1..n}. P x"
    by (metis card_atLeastAtMost card_filtered_set_eq_card_set_implies_forall
     diff_Suc_1 finite_atLeastAtMost)
next
  assume "\<forall>x \<in> {1..n}. P x"
  from this have "{x : {1..n}. P x} = {1..n}" by auto
  from this show "card {x : {1..n}. P x} = n" by simp
qed

subsubsection {* Cardinality of the Inverse Image of an Updated Function *}

lemma fun_upd_not_in_Domain:
  assumes "x' \<notin> S"
  shows "card {x : S. (f(x' := y)) x = c} = card {x : S. f x = c}"
using assms by (auto simp add: fun_upd_apply) metis

lemma card_fun_upd_noteq_constant:
  assumes "x' \<notin> S" "c \<noteq> d"
  shows "card {x : insert x' S. (f(x' := d)) x = c} = card {x : S. f x = c}"
using assms by (auto simp add: fun_upd_apply) metis

lemma card_fun_upd_eq_constant:
  assumes "x' \<notin> S" "finite S"
  shows "card {x : insert x' S. (f(x' := c)) x = c} = card {x : S. f x = c} + 1"
proof -
  from `x' \<notin> S` have "{x : insert x' S. (f(x' := c)) x = c} = insert x' {x \<in> S. f x = c}"
    by (auto simp add: fun_upd_same fun_upd_other fun_upd_apply)
  from `x' \<notin> S` `finite S` this show ?thesis by force
qed

subsubsection {* Relevant Specializations *}

lemma atLeastAtMost_plus2_conv: "{1..(n :: nat) + 2} = insert (n + 2) {1..n + 1}" 
by (auto simp add: atLeastAtMost_iff)

lemma card_fun_upd_noteq_constant_plus2:
  assumes "v' \<noteq> v"
  shows "card {x\<in>{1..(a :: nat) + b + 2}. (f(a + b + 2 := v')) x = v} =
    card {x \<in> {1..a + b + 1}. f x = v}"
using assms unfolding atLeastAtMost_plus2_conv by (subst card_fun_upd_noteq_constant) auto

lemma card_fun_upd_eq_constant_plus2:
  shows "card {x\<in>{1..(a :: nat) + b + 2}. (f(a + b + 2 := v)) x = v} = card {x\<in>{1..a + b + 1}. f x = v} + 1"
unfolding atLeastAtMost_plus2_conv by (subst card_fun_upd_eq_constant) auto

lemmas card_fun_upd_simps = card_fun_upd_noteq_constant_plus2 card_fun_upd_eq_constant_plus2

lemma split_into_sum:
  "card {f : {1 .. (n :: nat) + 2} \<rightarrow>\<^sub>E {A, B}. P f} =
   card {f : {1 .. n + 1} \<rightarrow>\<^sub>E {A, B}. P (f(n + 2 := A))} +
   card {f : {1 .. n + 1} \<rightarrow>\<^sub>E {A, B}. P (f(n + 2 := B))}"
by (auto simp add: atLeastAtMost_plus2_conv card_extensional_funcset_insert)

subsection {* Facts About @{term all_countings} *}

subsubsection {* Simple Non-Recursive Cases *}

lemma all_countings_a_0:
  "all_countings a 0 = 1"
unfolding all_countings_def'
by (simp add: card_filtered_set_from_n_eq_n_implies_forall one_extensional_constant_function)

lemma all_countings_0_b:
  "all_countings 0 b = 1"
unfolding all_countings_def''
by (simp add: card_filtered_set_from_n_eq_n_implies_forall one_extensional_constant_function)

subsubsection {* Recursive Case *}

lemma all_countings_Suc_Suc:
  "all_countings (a + 1) (b + 1) = all_countings a (b + 1) + all_countings (a + 1) b"
proof -
  let ?intermed = "%y. card {f : {1..a + b + 1} \<rightarrow>\<^sub>E {A, B}. card {x : {1..a + b + 2}.
    (f(a + b + 2 := y)) x = A} = a + 1 \<and> card {x : {1..a + b + 2}. (f(a + b + 2 := y)) x = B} = b + 1}"
  have "all_countings (a + 1) (b + 1) = card {f : {1..a + b + 2} \<rightarrow>\<^sub>E {A, B}.
          card {x : {1..a + b + 2}. f x = A} = a + 1 \<and> card {x : {1..a + b + 2}. f x = B} = b + 1}"
    unfolding all_countings_def[of "a+1" "b+1"] by (simp add: algebra_simps One_nat_def add_2_eq_Suc')
  also have "\<dots> = ?intermed A + ?intermed B" unfolding split_into_sum ..
  also have "\<dots> = all_countings a (b + 1) + all_countings (a + 1) b"
    by (simp add: card_fun_upd_simps all_countings_def) (simp add: algebra_simps)
  finally show ?thesis .
qed

subsubsection {* Executable Definition *}

declare all_countings_def [code del]
declare all_countings_a_0 [code]
declare all_countings_0_b [code]
declare all_countings_Suc_Suc [unfolded One_nat_def, simplified, code]

value "all_countings 1 0"
value "all_countings 0 1"
value "all_countings 1 1"
value "all_countings 2 1"
value "all_countings 1 2"
value "all_countings 2 4"
value "all_countings 4 2"

subsubsection {* Relation to Binomial Function *}

lemma all_countings:
  "all_countings a b = (a + b) choose a"
proof (induct a arbitrary: b)
  case 0
  show ?case by (simp add: all_countings_0_b)
next
  case (Suc a)
  note Suc_hyps = Suc.hyps
  show ?case
  proof (induct b)
    case 0
    show ?case by (simp add: all_countings_a_0)
  next
    case (Suc b)
    from Suc_hyps Suc.hyps show ?case
      by (metis Suc_eq_plus1 Suc_funpow add_Suc_shift binomial_Suc_Suc funpow_swap1
          all_countings_Suc_Suc)
  qed
qed

subsection {* Facts About @{term valid_countings} *}

subsubsection {* Non-Recursive Cases *}

lemma valid_countings_a_0:
  "valid_countings a 0 = 1"
proof -
  {
    fix f
    {
      assume "card {x : {1..a}. f x = A} = a"
      from this have a: "\<forall>x \<in> {1..a}. f x = A"
        by (intro card_filtered_set_eq_card_set_implies_forall) auto
      {
        fix i m
        assume e: "1 <= i"  "i <= m" "m <= a"
        from a e have "{x : {1..m}. f x = A} = {1 .. m}" by (auto simp add: atLeastAtMost_iff)
        from this have "card {x : {1..m}. f x = A} = m" by auto
        from a e this have "card {x : {1..m}. f x = A} = m \<and> card {x : {1..m}. f x = B} = 0"
          by (auto simp add: atLeastAtMost_iff)
      }
      from this have "(\<forall>m \<in> {1..a}. card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A}) = True"
        by (auto simp del: card_0_eq simp add: atLeastAtMost_iff)
    }
    from this have "((card {x : {1..a}. f x = A} = a) &
      (\<forall>m \<in> {1..a}. card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A})) =
      (card {x : {1..a}. f x = A} = a)" by blast
  } note redundant_disjunct = this
  show ?thesis
    unfolding valid_countings_def'
    by (auto simp add: redundant_disjunct all_countings_a_0[unfolded all_countings_def', simplified])
qed

lemma valid_countings_eq_zero:
  assumes "a \<le> b" "0 < b"
  shows "valid_countings a b = 0"
proof -
  from assms have is_empty: "{f \<in> {1..a + b} \<rightarrow>\<^sub>E {A, B}. 
    card {x \<in> {1..a + b}. f x = A} = a \<and>
    card {x \<in> {1..a + b}. f x = B} = b \<and>
    (\<forall>m \<in> {1..a + b}. card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A})} = {}"
  by auto (intro bexI[of _ "a + b"], auto)
  show ?thesis
    unfolding valid_countings_def by (metis card_empty is_empty)
qed

subsubsection {* Recursive Cases *}

lemma valid_countings_Suc_Suc_recursive:
  assumes "b < a"
  shows "valid_countings (a + 1) (b + 1) = valid_countings a (b + 1) + valid_countings (a + 1) b"
proof -
  let ?intermed = "%y. card {f : {1..a + b + 1} \<rightarrow>\<^sub>E {A, B}. card {x : {1..a + b + 2}.
    (f(a + b + 2 := y)) x = A} = a + 1 \<and> card {x : {1..a + b + 2}. (f(a + b + 2 := y)) x = B} = b + 1
    \<and> (\<forall>m \<in> {1..a + b + 2}. card {x : {1..m}. (f(a + b + 2 := y)) x = B} < card {x : {1 .. m}. (f(a + b + 2 := y)) x = A})}"
  {
    fix f
    let ?a = "%c. card {x \<in> {1.. a + b + 1}. f x = A} = c"
    let ?b = "%c. card {x \<in> {1.. a + b + 1}. f x = B} = c"
    let ?c = "%c. (\<forall>m\<in>{1.. a + b + 2}. card {x \<in> {1..m}. (f(a + b + 2 := c)) x = B}
        < card {x \<in> {1..m}. (f(a + b + 2 := c)) x = A})"
    let ?d = "(\<forall>m\<in>{1.. a + b + 1}. card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A})"
    {
      fix c
      have "(\<forall>m\<in>{1.. a + b + 1}. card {x \<in> {1..m}. (f(a + b + 2 := c)) x = B}
        < card {x \<in> {1..m}. (f(a + b + 2 := c)) x = A}) = ?d"
      proof (rule iffI, auto)
        fix m
        assume 1: "\<forall>m\<in>{1..a + b + 1}.
          card {x \<in> {1..m}. (f(a + b + 2 := c)) x = B} < card {x \<in> {1..m}. (f(a + b + 2 := c)) x = A}"
        assume 2: "m \<in> {1..a + b + 1}"
        from 2 have 3: "a + b + 2 \<notin> {1..m}" by (simp add: atLeastAtMost_iff)
        from 1 2 have "card {x \<in> {1..m}. (f(a + b + 2 := c)) x = B} < card {x \<in> {1..m}. (f(a + b + 2 := c)) x = A}"
          by auto
        from this show "card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A}"
          by (simp add: fun_upd_not_in_Domain[OF 3])
      next
        fix m
        assume 1: "\<forall>m\<in>{1..a + b + 1}. card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A}"
        assume 2: "m \<in> {1..a + b + 1}"
        from 2 have 3: "a + b + 2 \<notin> {1..m}" by (simp add: atLeastAtMost_iff)
        from 1 2 have "card {x \<in> {1..m}. f x = B} < card {x \<in> {1..m}. f x = A}" by auto
        from this show
          "card {x \<in> {1..m}. (f(a + b + 2 := c)) x = B} < card {x \<in> {1..m}. (f(a + b + 2 := c)) x = A}"
          by (simp add: fun_upd_not_in_Domain[OF 3])
      qed
    } note common = this
    {
      assume cardinalities: "?a a" "?b (b + 1)"
      have "?c A = ?d"
        unfolding atLeastAtMost_plus2_conv
        by (simp add: cardinalities card_fun_upd_simps `b < a` common)
    } moreover
    {
      assume cardinalities: "?a (a + 1)" "?b b"
      have "?c B = ?d"
        unfolding atLeastAtMost_plus2_conv
        by (simp add: cardinalities card_fun_upd_simps `b < a` common)
    } 
    ultimately have "(?a a & ?b (b + 1) & ?c A) = (?a a & ?b (b + 1) & ?d)"
      "(?a (a + 1) & ?b b & ?c B) = (?a (a + 1) & ?b b & ?d)" by blast+
  } note eq_inner = this  
  have "valid_countings (a + 1) (b + 1) = card {f : {1..a + b + 2} \<rightarrow>\<^sub>E {A, B}.
    card {x : {1..a + b + 2}. f x = A} = a + 1 \<and> card {x : {1..a + b + 2}. f x = B} = b + 1 \<and>
    (\<forall>m \<in> {1..a + b + 2}. card {x : {1..m}. f x = B} < card {x : {1..m}. f x = A})}"
    unfolding valid_countings_def[of "a + 1" "b + 1"]
    by (simp add: algebra_simps One_nat_def add_2_eq_Suc')
  also have "\<dots> = ?intermed A + ?intermed B" unfolding split_into_sum .. 
  also have "\<dots> = valid_countings a (b + 1) + valid_countings (a + 1) b"
    by (simp add: card_fun_upd_simps eq_inner valid_countings_def) (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma valid_countings_Suc_Suc:
  "valid_countings (a + 1) (b + 1) =
    (if a \<le> b then 0 else valid_countings a (b + 1) + valid_countings (a + 1) b)"
by (auto simp add: valid_countings_eq_zero valid_countings_Suc_Suc_recursive)

lemma valid_countings_0_Suc: "valid_countings 0 (Suc b) = 0"
by (simp add: valid_countings_eq_zero)

subsubsection {* Executable Definition *}

declare valid_countings_def [code del]
declare valid_countings_a_0 [code]
declare valid_countings_0_Suc [code]       
declare valid_countings_Suc_Suc [unfolded One_nat_def, simplified, code]

value "valid_countings 1 0"
value "valid_countings 0 1"
value "valid_countings 1 1"
value "valid_countings 2 1"
value "valid_countings 1 2"
value "valid_countings 2 4"
value "valid_countings 4 2"

subsubsection {* Relation to Binomial Function *}

lemma valid_countings:
  "(a + b) * valid_countings a b = (a - b) * ((a + b) choose a)"
proof (induct a arbitrary: b rule: nat.induct[unfolded Suc_eq_plus1])
  case 1
  have "b = 0 | (EX b'. b = b' + 1)" by (cases b) simp+
  from this show ?case
    by (auto simp : valid_countings_eq_zero valid_countings_a_0)
next
  case (2 a)
  note a_hyp = "2.hyps"
  show ?case
  proof (induct b rule: nat.induct[unfolded Suc_eq_plus1])
    case 1
    show ?case by (simp add: valid_countings_a_0)
  next
    case (2 b)
    note b_hyp = "2.hyps"
    show ?case
    proof(cases "a <= b")
      case True
      from this show ?thesis
        unfolding valid_countings_Suc_Suc if_True by (simp add: algebra_simps)
    next
      case False
      from this have "b < a" by simp
      have makes_plus_2: "a + 1 + (b + 1) = a + b + 2"
        by (metis Suc_eq_plus1 add_Suc add_Suc_right one_add_one)
      from b_hyp have b_hyp: "(a + b + 1) * valid_countings (a + 1) b = (a + 1 - b) * (a + b + 1 choose (a + 1))"
        by (simp add: algebra_simps)
      from a_hyp[of "b + 1"] have a_hyp: "(a + b + 1) * valid_countings a (b + 1) = (a - (b + 1)) * (a + (b + 1) choose a)"
        by (simp add: algebra_simps)
      have "a - b \<le> a * a - b * b" by (simp add: square_diff_square_factored_nat)
      from this `b < a` have "a + b * b \<le> b + a * a" by auto      
      moreover from `\<not> a \<le> b` have "b * b \<le> a + a * b" by (meson linear mult_le_mono1 trans_le_add2)
      moreover have "1 + b + a * b \<le> a * a"
      proof -
         from `b < a` have "1 + b + a * b \<le> a + a * b" by simp
         also have "\<dots> \<le> a * (b + 1)" by (simp add: algebra_simps)
         also from `b < a` have "\<dots> \<le> a * a" by simp
         finally show ?thesis .
      qed
      moreover note `b < a`
      ultimately have rearrange: "(a + 1) * (a - (b + 1)) + (a + 1 - b) * (b + 1) = (a - b) * (a + b + 1)"
        by (simp add: algebra_simps)
      have rewrite1: "\<And>(A :: nat) B C D E F. A * B * ((C * D) + (E * F)) = A * ((C * (B * D)) + (E * (B * F)))"
        by (simp add: algebra_simps)
      have rewrite2: "\<And>(A :: nat) B C D E F. A * (B * (C * D) + E * (F * D)) = (C * B + E * F) * (A * D)"
        by (simp only: algebra_simps)
      have "(a + b + 2) * (a + 1) * (a + b + 1) * valid_countings (a + 1) (b + 1) =
        (a + b + 2) * (a + 1) * ((a + b + 1) * valid_countings a (b + 1) + (a + b + 1) * valid_countings (a + 1) b)"
        unfolding valid_countings_Suc_Suc_recursive[OF `b < a`] by (simp only: algebra_simps)
      also have "... = (a + b + 2) * ((a - (b + 1)) * ((a + 1) * (a + b + 1 choose a)) + (a + 1 - b) * ((a + 1) * (a + b + 1 choose (a + 1))))"
        unfolding b_hyp a_hyp rewrite1 by (simp only: add.assoc)
      also have "... = ((a + 1) * (a - (b + 1)) + (a + 1 - b) * (b + 1)) * ((a + b + 2) * (a + 1 + b choose a))"
        unfolding Suc_times_binomial_add[simplified Suc_eq_plus1] rewrite2 by (simp only: algebra_simps)
      also have "... = (a - b) * (a + b + 1) * ((a + 1 + b + 1) * (a + 1 + b choose a))"
        by (simp add: rearrange)
      also have "... = (a - b) * (a + b + 1) * (((a + 1 + b + 1) choose (a + 1)) * (a + 1))"
        by (subst Suc_times_binomial_eq[simplified Suc_eq_plus1, where k = "a" and n = "a + 1 + b"]) auto
      also have "... = (a - b) * (a + 1) * (a + b + 1) * (a + 1 + (b + 1) choose (a + 1))"
        by (auto simp add: add.assoc)
      finally show ?thesis by (simp add: makes_plus_2)
    qed
  qed
qed

subsection {* Relation Between @{term valid_countings} and @{term all_countings} *}

lemma main_nat: "(a + b) * valid_countings a b = (a - b) * all_countings a b"
  unfolding valid_countings all_countings ..

lemma main_real:
  assumes "b < a"
  shows "valid_countings a b = (a - b) / (a + b) * all_countings a b"
using assms
proof -
  from main_nat[of a b] `b < a` have
    "(real a + real b) * real (valid_countings a b) = (real a - real b) * real (all_countings a b)"
    by (simp only: real_of_nat_add[symmetric] real_of_nat_mult[symmetric]) auto
  from this `b < a` show ?thesis
    by (subst mult_left_cancel[of "real a + real b", symmetric]) auto
qed

lemma
  "valid_countings a b = (if a \<le> b then (if b = 0 then 1 else 0) else (a - b) / (a + b) * all_countings a b)"
proof (cases "a \<le> b")
  case False
    from this show ?thesis by (simp add: main_real)
next
  case True
    from this show ?thesis
      by (auto simp add: valid_countings_a_0 all_countings_a_0 valid_countings_eq_zero)
qed

end
