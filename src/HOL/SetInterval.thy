(*  Title:      HOL/SetInterval.thy
    Author:     Tobias Nipkow and Clemens Ballarin
                Additions by Jeremy Avigad in March 2004
    Copyright   2000  TU Muenchen

lessThan, greaterThan, atLeast, atMost and two-sided intervals
*)

header {* Set intervals *}

theory SetInterval
imports Int
begin

context ord
begin
definition
  lessThan    :: "'a => 'a set"	("(1{..<_})") where
  "{..<u} == {x. x < u}"

definition
  atMost      :: "'a => 'a set"	("(1{.._})") where
  "{..u} == {x. x \<le> u}"

definition
  greaterThan :: "'a => 'a set"	("(1{_<..})") where
  "{l<..} == {x. l<x}"

definition
  atLeast     :: "'a => 'a set"	("(1{_..})") where
  "{l..} == {x. l\<le>x}"

definition
  greaterThanLessThan :: "'a => 'a => 'a set"  ("(1{_<..<_})") where
  "{l<..<u} == {l<..} Int {..<u}"

definition
  atLeastLessThan :: "'a => 'a => 'a set"      ("(1{_..<_})") where
  "{l..<u} == {l..} Int {..<u}"

definition
  greaterThanAtMost :: "'a => 'a => 'a set"    ("(1{_<.._})") where
  "{l<..u} == {l<..} Int {..u}"

definition
  atLeastAtMost :: "'a => 'a => 'a set"        ("(1{_.._})") where
  "{l..u} == {l..} Int {..u}"

end


text{* A note of warning when using @{term"{..<n}"} on type @{typ
nat}: it is equivalent to @{term"{0::nat..<n}"} but some lemmas involving
@{term"{m..<n}"} may not exist in @{term"{..<n}"}-form as well. *}

syntax
  "@UNION_le"   :: "'a => 'a => 'b set => 'b set"       ("(3UN _<=_./ _)" 10)
  "@UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3UN _<_./ _)" 10)
  "@INTER_le"   :: "'a => 'a => 'b set => 'b set"       ("(3INT _<=_./ _)" 10)
  "@INTER_less" :: "'a => 'a => 'b set => 'b set"       ("(3INT _<_./ _)" 10)

syntax (xsymbols)
  "@UNION_le"   :: "'a => 'a => 'b set => 'b set"       ("(3\<Union> _\<le>_./ _)" 10)
  "@UNION_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Union> _<_./ _)" 10)
  "@INTER_le"   :: "'a => 'a => 'b set => 'b set"       ("(3\<Inter> _\<le>_./ _)" 10)
  "@INTER_less" :: "'a => 'a => 'b set => 'b set"       ("(3\<Inter> _<_./ _)" 10)

syntax (latex output)
  "@UNION_le"   :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Union>(00_ \<le> _)/ _)" 10)
  "@UNION_less" :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Union>(00_ < _)/ _)" 10)
  "@INTER_le"   :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Inter>(00_ \<le> _)/ _)" 10)
  "@INTER_less" :: "'a \<Rightarrow> 'a => 'b set => 'b set"       ("(3\<Inter>(00_ < _)/ _)" 10)

translations
  "UN i<=n. A"  == "UN i:{..n}. A"
  "UN i<n. A"   == "UN i:{..<n}. A"
  "INT i<=n. A" == "INT i:{..n}. A"
  "INT i<n. A"  == "INT i:{..<n}. A"


subsection {* Various equivalences *}

lemma (in ord) lessThan_iff [iff]: "(i: lessThan k) = (i<k)"
by (simp add: lessThan_def)

lemma Compl_lessThan [simp]:
    "!!k:: 'a::linorder. -lessThan k = atLeast k"
apply (auto simp add: lessThan_def atLeast_def)
done

lemma single_Diff_lessThan [simp]: "!!k:: 'a::order. {k} - lessThan k = {k}"
by auto

lemma (in ord) greaterThan_iff [iff]: "(i: greaterThan k) = (k<i)"
by (simp add: greaterThan_def)

lemma Compl_greaterThan [simp]:
    "!!k:: 'a::linorder. -greaterThan k = atMost k"
  by (auto simp add: greaterThan_def atMost_def)

lemma Compl_atMost [simp]: "!!k:: 'a::linorder. -atMost k = greaterThan k"
apply (subst Compl_greaterThan [symmetric])
apply (rule double_complement)
done

lemma (in ord) atLeast_iff [iff]: "(i: atLeast k) = (k<=i)"
by (simp add: atLeast_def)

lemma Compl_atLeast [simp]:
    "!!k:: 'a::linorder. -atLeast k = lessThan k"
  by (auto simp add: lessThan_def atLeast_def)

lemma (in ord) atMost_iff [iff]: "(i: atMost k) = (i<=k)"
by (simp add: atMost_def)

lemma atMost_Int_atLeast: "!!n:: 'a::order. atMost n Int atLeast n = {n}"
by (blast intro: order_antisym)


subsection {* Logical Equivalences for Set Inclusion and Equality *}

lemma atLeast_subset_iff [iff]:
     "(atLeast x \<subseteq> atLeast y) = (y \<le> (x::'a::order))"
by (blast intro: order_trans)

lemma atLeast_eq_iff [iff]:
     "(atLeast x = atLeast y) = (x = (y::'a::linorder))"
by (blast intro: order_antisym order_trans)

lemma greaterThan_subset_iff [iff]:
     "(greaterThan x \<subseteq> greaterThan y) = (y \<le> (x::'a::linorder))"
apply (auto simp add: greaterThan_def)
 apply (subst linorder_not_less [symmetric], blast)
done

lemma greaterThan_eq_iff [iff]:
     "(greaterThan x = greaterThan y) = (x = (y::'a::linorder))"
apply (rule iffI)
 apply (erule equalityE)
 apply simp_all
done

lemma atMost_subset_iff [iff]: "(atMost x \<subseteq> atMost y) = (x \<le> (y::'a::order))"
by (blast intro: order_trans)

lemma atMost_eq_iff [iff]: "(atMost x = atMost y) = (x = (y::'a::linorder))"
by (blast intro: order_antisym order_trans)

lemma lessThan_subset_iff [iff]:
     "(lessThan x \<subseteq> lessThan y) = (x \<le> (y::'a::linorder))"
apply (auto simp add: lessThan_def)
 apply (subst linorder_not_less [symmetric], blast)
done

lemma lessThan_eq_iff [iff]:
     "(lessThan x = lessThan y) = (x = (y::'a::linorder))"
apply (rule iffI)
 apply (erule equalityE)
 apply simp_all
done


subsection {*Two-sided intervals*}

context ord
begin

lemma greaterThanLessThan_iff [simp,noatp]:
  "(i : {l<..<u}) = (l < i & i < u)"
by (simp add: greaterThanLessThan_def)

lemma atLeastLessThan_iff [simp,noatp]:
  "(i : {l..<u}) = (l <= i & i < u)"
by (simp add: atLeastLessThan_def)

lemma greaterThanAtMost_iff [simp,noatp]:
  "(i : {l<..u}) = (l < i & i <= u)"
by (simp add: greaterThanAtMost_def)

lemma atLeastAtMost_iff [simp,noatp]:
  "(i : {l..u}) = (l <= i & i <= u)"
by (simp add: atLeastAtMost_def)

text {* The above four lemmas could be declared as iffs.
  If we do so, a call to blast in Hyperreal/Star.ML, lemma @{text STAR_Int}
  seems to take forever (more than one hour). *}
end

subsubsection{* Emptyness and singletons *}

context order
begin

lemma atLeastAtMost_empty [simp]: "n < m ==> {m..n} = {}";
by (auto simp add: atLeastAtMost_def atMost_def atLeast_def)

lemma atLeastLessThan_empty[simp]: "n \<le> m ==> {m..<n} = {}"
by (auto simp add: atLeastLessThan_def)

lemma greaterThanAtMost_empty[simp]:"l \<le> k ==> {k<..l} = {}"
by(auto simp:greaterThanAtMost_def greaterThan_def atMost_def)

lemma greaterThanLessThan_empty[simp]:"l \<le> k ==> {k<..<l} = {}"
by(auto simp:greaterThanLessThan_def greaterThan_def lessThan_def)

lemma atLeastAtMost_singleton [simp]: "{a..a} = {a}"
by (auto simp add: atLeastAtMost_def atMost_def atLeast_def)

end

subsection {* Intervals of natural numbers *}

subsubsection {* The Constant @{term lessThan} *}

lemma lessThan_0 [simp]: "lessThan (0::nat) = {}"
by (simp add: lessThan_def)

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
by (simp add: lessThan_def less_Suc_eq, blast)

lemma lessThan_Suc_atMost: "lessThan (Suc k) = atMost k"
by (simp add: lessThan_def atMost_def less_Suc_eq_le)

lemma UN_lessThan_UNIV: "(UN m::nat. lessThan m) = UNIV"
by blast

subsubsection {* The Constant @{term greaterThan} *}

lemma greaterThan_0 [simp]: "greaterThan 0 = range Suc"
apply (simp add: greaterThan_def)
apply (blast dest: gr0_conv_Suc [THEN iffD1])
done

lemma greaterThan_Suc: "greaterThan (Suc k) = greaterThan k - {Suc k}"
apply (simp add: greaterThan_def)
apply (auto elim: linorder_neqE)
done

lemma INT_greaterThan_UNIV: "(INT m::nat. greaterThan m) = {}"
by blast

subsubsection {* The Constant @{term atLeast} *}

lemma atLeast_0 [simp]: "atLeast (0::nat) = UNIV"
by (unfold atLeast_def UNIV_def, simp)

lemma atLeast_Suc: "atLeast (Suc k) = atLeast k - {k}"
apply (simp add: atLeast_def)
apply (simp add: Suc_le_eq)
apply (simp add: order_le_less, blast)
done

lemma atLeast_Suc_greaterThan: "atLeast (Suc k) = greaterThan k"
  by (auto simp add: greaterThan_def atLeast_def less_Suc_eq_le)

lemma UN_atLeast_UNIV: "(UN m::nat. atLeast m) = UNIV"
by blast

subsubsection {* The Constant @{term atMost} *}

lemma atMost_0 [simp]: "atMost (0::nat) = {0}"
by (simp add: atMost_def)

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
apply (simp add: atMost_def)
apply (simp add: less_Suc_eq order_le_less, blast)
done

lemma UN_atMost_UNIV: "(UN m::nat. atMost m) = UNIV"
by blast

subsubsection {* The Constant @{term atLeastLessThan} *}

text{*The orientation of the following 2 rules is tricky. The lhs is
defined in terms of the rhs.  Hence the chosen orientation makes sense
in this theory --- the reverse orientation complicates proofs (eg
nontermination). But outside, when the definition of the lhs is rarely
used, the opposite orientation seems preferable because it reduces a
specific concept to a more general one. *}

lemma atLeast0LessThan: "{0::nat..<n} = {..<n}"
by(simp add:lessThan_def atLeastLessThan_def)

lemma atLeast0AtMost: "{0..n::nat} = {..n}"
by(simp add:atMost_def atLeastAtMost_def)

declare atLeast0LessThan[symmetric, code unfold]
        atLeast0AtMost[symmetric, code unfold]

lemma atLeastLessThan0: "{m..<0::nat} = {}"
by (simp add: atLeastLessThan_def)

subsubsection {* Intervals of nats with @{term Suc} *}

text{*Not a simprule because the RHS is too messy.*}
lemma atLeastLessThanSuc:
    "{m..<Suc n} = (if m \<le> n then insert n {m..<n} else {})"
by (auto simp add: atLeastLessThan_def)

lemma atLeastLessThan_singleton [simp]: "{m..<Suc m} = {m}"
by (auto simp add: atLeastLessThan_def)
(*
lemma atLeast_sum_LessThan [simp]: "{m + k..<k::nat} = {}"
by (induct k, simp_all add: atLeastLessThanSuc)

lemma atLeastSucLessThan [simp]: "{Suc n..<n} = {}"
by (auto simp add: atLeastLessThan_def)
*)
lemma atLeastLessThanSuc_atLeastAtMost: "{l..<Suc u} = {l..u}"
  by (simp add: lessThan_Suc_atMost atLeastAtMost_def atLeastLessThan_def)

lemma atLeastSucAtMost_greaterThanAtMost: "{Suc l..u} = {l<..u}"
  by (simp add: atLeast_Suc_greaterThan atLeastAtMost_def
    greaterThanAtMost_def)

lemma atLeastSucLessThan_greaterThanLessThan: "{Suc l..<u} = {l<..<u}"
  by (simp add: atLeast_Suc_greaterThan atLeastLessThan_def
    greaterThanLessThan_def)

lemma atLeastAtMostSuc_conv: "m \<le> Suc n \<Longrightarrow> {m..Suc n} = insert (Suc n) {m..n}"
by (auto simp add: atLeastAtMost_def)

subsubsection {* Image *}

lemma image_add_atLeastAtMost:
  "(%n::nat. n+k) ` {i..j} = {i+k..j+k}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" by auto
next
  show "?B \<subseteq> ?A"
  proof
    fix n assume a: "n : ?B"
    hence "n - k : {i..j}" by auto
    moreover have "n = (n - k) + k" using a by auto
    ultimately show "n : ?A" by blast
  qed
qed

lemma image_add_atLeastLessThan:
  "(%n::nat. n+k) ` {i..<j} = {i+k..<j+k}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" by auto
next
  show "?B \<subseteq> ?A"
  proof
    fix n assume a: "n : ?B"
    hence "n - k : {i..<j}" by auto
    moreover have "n = (n - k) + k" using a by auto
    ultimately show "n : ?A" by blast
  qed
qed

corollary image_Suc_atLeastAtMost[simp]:
  "Suc ` {i..j} = {Suc i..Suc j}"
using image_add_atLeastAtMost[where k="Suc 0"] by simp

corollary image_Suc_atLeastLessThan[simp]:
  "Suc ` {i..<j} = {Suc i..<Suc j}"
using image_add_atLeastLessThan[where k="Suc 0"] by simp

lemma image_add_int_atLeastLessThan:
    "(%x. x + (l::int)) ` {0..<u-l} = {l..<u}"
  apply (auto simp add: image_def)
  apply (rule_tac x = "x - l" in bexI)
  apply auto
  done


subsubsection {* Finiteness *}

lemma finite_lessThan [iff]: fixes k :: nat shows "finite {..<k}"
  by (induct k) (simp_all add: lessThan_Suc)

lemma finite_atMost [iff]: fixes k :: nat shows "finite {..k}"
  by (induct k) (simp_all add: atMost_Suc)

lemma finite_greaterThanLessThan [iff]:
  fixes l :: nat shows "finite {l<..<u}"
by (simp add: greaterThanLessThan_def)

lemma finite_atLeastLessThan [iff]:
  fixes l :: nat shows "finite {l..<u}"
by (simp add: atLeastLessThan_def)

lemma finite_greaterThanAtMost [iff]:
  fixes l :: nat shows "finite {l<..u}"
by (simp add: greaterThanAtMost_def)

lemma finite_atLeastAtMost [iff]:
  fixes l :: nat shows "finite {l..u}"
by (simp add: atLeastAtMost_def)

text {* A bounded set of natural numbers is finite. *}
lemma bounded_nat_set_is_finite:
  "(ALL i:N. i < (n::nat)) ==> finite N"
apply (rule finite_subset)
 apply (rule_tac [2] finite_lessThan, auto)
done

text {* A set of natural numbers is finite iff it is bounded. *}
lemma finite_nat_set_iff_bounded:
  "finite(N::nat set) = (EX m. ALL n:N. n<m)" (is "?F = ?B")
proof
  assume f:?F  show ?B
    using Max_ge[OF `?F`, simplified less_Suc_eq_le[symmetric]] by blast
next
  assume ?B show ?F using `?B` by(blast intro:bounded_nat_set_is_finite)
qed

lemma finite_nat_set_iff_bounded_le:
  "finite(N::nat set) = (EX m. ALL n:N. n<=m)"
apply(simp add:finite_nat_set_iff_bounded)
apply(blast dest:less_imp_le_nat le_imp_less_Suc)
done

lemma finite_less_ub:
     "!!f::nat=>nat. (!!n. n \<le> f n) ==> finite {n. f n \<le> u}"
by (rule_tac B="{..u}" in finite_subset, auto intro: order_trans)

text{* Any subset of an interval of natural numbers the size of the
subset is exactly that interval. *}

lemma subset_card_intvl_is_intvl:
  "A <= {k..<k+card A} \<Longrightarrow> A = {k..<k+card A}" (is "PROP ?P")
proof cases
  assume "finite A"
  thus "PROP ?P"
  proof(induct A rule:finite_linorder_induct)
    case empty thus ?case by auto
  next
    case (insert A b)
    moreover hence "b ~: A" by auto
    moreover have "A <= {k..<k+card A}" and "b = k+card A"
      using `b ~: A` insert by fastsimp+
    ultimately show ?case by auto
  qed
next
  assume "~finite A" thus "PROP ?P" by simp
qed


subsubsection {* Cardinality *}

lemma card_lessThan [simp]: "card {..<u} = u"
  by (induct u, simp_all add: lessThan_Suc)

lemma card_atMost [simp]: "card {..u} = Suc u"
  by (simp add: lessThan_Suc_atMost [THEN sym])

lemma card_atLeastLessThan [simp]: "card {l..<u} = u - l"
  apply (subgoal_tac "card {l..<u} = card {..<u-l}")
  apply (erule ssubst, rule card_lessThan)
  apply (subgoal_tac "(%x. x + l) ` {..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule card_image)
  apply (simp add: inj_on_def)
  apply (auto simp add: image_def atLeastLessThan_def lessThan_def)
  apply (rule_tac x = "x - l" in exI)
  apply arith
  done

lemma card_atLeastAtMost [simp]: "card {l..u} = Suc u - l"
  by (subst atLeastLessThanSuc_atLeastAtMost [THEN sym], simp)

lemma card_greaterThanAtMost [simp]: "card {l<..u} = u - l"
  by (subst atLeastSucAtMost_greaterThanAtMost [THEN sym], simp)

lemma card_greaterThanLessThan [simp]: "card {l<..<u} = u - Suc l"
  by (subst atLeastSucLessThan_greaterThanLessThan [THEN sym], simp)

lemma ex_bij_betw_nat_finite:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h {0..<card M} M"
apply(drule finite_imp_nat_seg_image_inj_on)
apply(auto simp:atLeast0LessThan[symmetric] lessThan_def[symmetric] card_image bij_betw_def)
done

lemma ex_bij_betw_finite_nat:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h M {0..<card M}"
by (blast dest: ex_bij_betw_nat_finite bij_betw_inv)

lemma finite_same_card_bij:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> card A = card B \<Longrightarrow> EX h. bij_betw h A B"
apply(drule ex_bij_betw_finite_nat)
apply(drule ex_bij_betw_nat_finite)
apply(auto intro!:bij_betw_trans)
done

lemma ex_bij_betw_nat_finite_1:
  "finite M \<Longrightarrow> \<exists>h. bij_betw h {1 .. card M} M"
by (rule finite_same_card_bij) auto


subsection {* Intervals of integers *}

lemma atLeastLessThanPlusOne_atLeastAtMost_int: "{l..<u+1} = {l..(u::int)}"
  by (auto simp add: atLeastAtMost_def atLeastLessThan_def)

lemma atLeastPlusOneAtMost_greaterThanAtMost_int: "{l+1..u} = {l<..(u::int)}"
  by (auto simp add: atLeastAtMost_def greaterThanAtMost_def)

lemma atLeastPlusOneLessThan_greaterThanLessThan_int:
    "{l+1..<u} = {l<..<u::int}"
  by (auto simp add: atLeastLessThan_def greaterThanLessThan_def)

subsubsection {* Finiteness *}

lemma image_atLeastZeroLessThan_int: "0 \<le> u ==>
    {(0::int)..<u} = int ` {..<nat u}"
  apply (unfold image_def lessThan_def)
  apply auto
  apply (rule_tac x = "nat x" in exI)
  apply (auto simp add: zless_nat_conj zless_nat_eq_int_zless [THEN sym])
  done

lemma finite_atLeastZeroLessThan_int: "finite {(0::int)..<u}"
  apply (case_tac "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_int, assumption)
  apply (rule finite_imageI)
  apply auto
  done

lemma finite_atLeastLessThan_int [iff]: "finite {l..<u::int}"
  apply (subgoal_tac "(%x. x + l) ` {0..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule finite_imageI)
  apply (rule finite_atLeastZeroLessThan_int)
  apply (rule image_add_int_atLeastLessThan)
  done

lemma finite_atLeastAtMost_int [iff]: "finite {l..(u::int)}"
  by (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym], simp)

lemma finite_greaterThanAtMost_int [iff]: "finite {l<..(u::int)}"
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma finite_greaterThanLessThan_int [iff]: "finite {l<..<u::int}"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)


subsubsection {* Cardinality *}

lemma card_atLeastZeroLessThan_int: "card {(0::int)..<u} = nat u"
  apply (case_tac "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_int, assumption)
  apply (subst card_image)
  apply (auto simp add: inj_on_def)
  done

lemma card_atLeastLessThan_int [simp]: "card {l..<u} = nat (u - l)"
  apply (subgoal_tac "card {l..<u} = card {0..<u-l}")
  apply (erule ssubst, rule card_atLeastZeroLessThan_int)
  apply (subgoal_tac "(%x. x + l) ` {0..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule card_image)
  apply (simp add: inj_on_def)
  apply (rule image_add_int_atLeastLessThan)
  done

lemma card_atLeastAtMost_int [simp]: "card {l..u} = nat (u - l + 1)"
apply (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym])
apply (auto simp add: algebra_simps)
done

lemma card_greaterThanAtMost_int [simp]: "card {l<..u} = nat (u - l)"
by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma card_greaterThanLessThan_int [simp]: "card {l<..<u} = nat (u - (l + 1))"
by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)

lemma finite_M_bounded_by_nat: "finite {k. P k \<and> k < (i::nat)}"
proof -
  have "{k. P k \<and> k < i} \<subseteq> {..<i}" by auto
  with finite_lessThan[of "i"] show ?thesis by (simp add: finite_subset)
qed

lemma card_less:
assumes zero_in_M: "0 \<in> M"
shows "card {k \<in> M. k < Suc i} \<noteq> 0"
proof -
  from zero_in_M have "{k \<in> M. k < Suc i} \<noteq> {}" by auto
  with finite_M_bounded_by_nat show ?thesis by (auto simp add: card_eq_0_iff)
qed

lemma card_less_Suc2: "0 \<notin> M \<Longrightarrow> card {k. Suc k \<in> M \<and> k < i} = card {k \<in> M. k < Suc i}"
apply (rule card_bij_eq [of "Suc" _ _ "\<lambda>x. x - Suc 0"])
apply simp
apply fastsimp
apply auto
apply (rule inj_on_diff_nat)
apply auto
apply (case_tac x)
apply auto
apply (case_tac xa)
apply auto
apply (case_tac xa)
apply auto
done

lemma card_less_Suc:
  assumes zero_in_M: "0 \<in> M"
    shows "Suc (card {k. Suc k \<in> M \<and> k < i}) = card {k \<in> M. k < Suc i}"
proof -
  from assms have a: "0 \<in> {k \<in> M. k < Suc i}" by simp
  hence c: "{k \<in> M. k < Suc i} = insert 0 ({k \<in> M. k < Suc i} - {0})"
    by (auto simp only: insert_Diff)
  have b: "{k \<in> M. k < Suc i} - {0} = {k \<in> M - {0}. k < Suc i}"  by auto
  from finite_M_bounded_by_nat[of "\<lambda>x. x \<in> M" "Suc i"] have "Suc (card {k. Suc k \<in> M \<and> k < i}) = card (insert 0 ({k \<in> M. k < Suc i} - {0}))"
    apply (subst card_insert)
    apply simp_all
    apply (subst b)
    apply (subst card_less_Suc2[symmetric])
    apply simp_all
    done
  with c show ?thesis by simp
qed


subsection {*Lemmas useful with the summation operator setsum*}

text {* For examples, see Algebra/poly/UnivPoly2.thy *}

subsubsection {* Disjoint Unions *}

text {* Singletons and open intervals *}

lemma ivl_disj_un_singleton:
  "{l::'a::linorder} Un {l<..} = {l..}"
  "{..<u} Un {u::'a::linorder} = {..u}"
  "(l::'a::linorder) < u ==> {l} Un {l<..<u} = {l..<u}"
  "(l::'a::linorder) < u ==> {l<..<u} Un {u} = {l<..u}"
  "(l::'a::linorder) <= u ==> {l} Un {l<..u} = {l..u}"
  "(l::'a::linorder) <= u ==> {l..<u} Un {u} = {l..u}"
by auto

text {* One- and two-sided intervals *}

lemma ivl_disj_un_one:
  "(l::'a::linorder) < u ==> {..l} Un {l<..<u} = {..<u}"
  "(l::'a::linorder) <= u ==> {..<l} Un {l..<u} = {..<u}"
  "(l::'a::linorder) <= u ==> {..l} Un {l<..u} = {..u}"
  "(l::'a::linorder) <= u ==> {..<l} Un {l..u} = {..u}"
  "(l::'a::linorder) <= u ==> {l<..u} Un {u<..} = {l<..}"
  "(l::'a::linorder) < u ==> {l<..<u} Un {u..} = {l<..}"
  "(l::'a::linorder) <= u ==> {l..u} Un {u<..} = {l..}"
  "(l::'a::linorder) <= u ==> {l..<u} Un {u..} = {l..}"
by auto

text {* Two- and two-sided intervals *}

lemma ivl_disj_un_two:
  "[| (l::'a::linorder) < m; m <= u |] ==> {l<..<m} Un {m..<u} = {l<..<u}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {l<..m} Un {m<..<u} = {l<..<u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..<m} Un {m..<u} = {l..<u}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {l..m} Un {m<..<u} = {l..<u}"
  "[| (l::'a::linorder) < m; m <= u |] ==> {l<..<m} Un {m..u} = {l<..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l<..m} Un {m<..u} = {l<..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..<m} Un {m..u} = {l..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..m} Un {m<..u} = {l..u}"
by auto

lemmas ivl_disj_un = ivl_disj_un_singleton ivl_disj_un_one ivl_disj_un_two

subsubsection {* Disjoint Intersections *}

text {* Singletons and open intervals *}

lemma ivl_disj_int_singleton:
  "{l::'a::order} Int {l<..} = {}"
  "{..<u} Int {u} = {}"
  "{l} Int {l<..<u} = {}"
  "{l<..<u} Int {u} = {}"
  "{l} Int {l<..u} = {}"
  "{l..<u} Int {u} = {}"
  by simp+

text {* One- and two-sided intervals *}

lemma ivl_disj_int_one:
  "{..l::'a::order} Int {l<..<u} = {}"
  "{..<l} Int {l..<u} = {}"
  "{..l} Int {l<..u} = {}"
  "{..<l} Int {l..u} = {}"
  "{l<..u} Int {u<..} = {}"
  "{l<..<u} Int {u..} = {}"
  "{l..u} Int {u<..} = {}"
  "{l..<u} Int {u..} = {}"
  by auto

text {* Two- and two-sided intervals *}

lemma ivl_disj_int_two:
  "{l::'a::order<..<m} Int {m..<u} = {}"
  "{l<..m} Int {m<..<u} = {}"
  "{l..<m} Int {m..<u} = {}"
  "{l..m} Int {m<..<u} = {}"
  "{l<..<m} Int {m..u} = {}"
  "{l<..m} Int {m<..u} = {}"
  "{l..<m} Int {m..u} = {}"
  "{l..m} Int {m<..u} = {}"
  by auto

lemmas ivl_disj_int = ivl_disj_int_singleton ivl_disj_int_one ivl_disj_int_two

subsubsection {* Some Differences *}

lemma ivl_diff[simp]:
 "i \<le> n \<Longrightarrow> {i..<m} - {i..<n} = {n..<(m::'a::linorder)}"
by(auto)


subsubsection {* Some Subset Conditions *}

lemma ivl_subset [simp,noatp]:
 "({i..<j} \<subseteq> {m..<n}) = (j \<le> i | m \<le> i & j \<le> (n::'a::linorder))"
apply(auto simp:linorder_not_le)
apply(rule ccontr)
apply(insert linorder_le_less_linear[of i n])
apply(clarsimp simp:linorder_not_le)
apply(fastsimp)
done


subsection {* Summation indexed over intervals *}

syntax
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _<_./ _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _<=_./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_<_./ _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_\<le>_./ _)" [0,0,10] 10)
syntax (HTML output)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_<_./ _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_\<le>_./ _)" [0,0,10] 10)
syntax (latex_sum output)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ = _\<^raw:}^{>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ = _\<^raw:}^{<>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_upt_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ < _\<^raw:}$> _)" [0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ \<le> _\<^raw:}$> _)" [0,0,10] 10)

translations
  "\<Sum>x=a..b. t" == "CONST setsum (%x. t) {a..b}"
  "\<Sum>x=a..<b. t" == "CONST setsum (%x. t) {a..<b}"
  "\<Sum>i\<le>n. t" == "CONST setsum (\<lambda>i. t) {..n}"
  "\<Sum>i<n. t" == "CONST setsum (\<lambda>i. t) {..<n}"

text{* The above introduces some pretty alternative syntaxes for
summation over intervals:
\begin{center}
\begin{tabular}{lll}
Old & New & \LaTeX\\
@{term[source]"\<Sum>x\<in>{a..b}. e"} & @{term"\<Sum>x=a..b. e"} & @{term[mode=latex_sum]"\<Sum>x=a..b. e"}\\
@{term[source]"\<Sum>x\<in>{a..<b}. e"} & @{term"\<Sum>x=a..<b. e"} & @{term[mode=latex_sum]"\<Sum>x=a..<b. e"}\\
@{term[source]"\<Sum>x\<in>{..b}. e"} & @{term"\<Sum>x\<le>b. e"} & @{term[mode=latex_sum]"\<Sum>x\<le>b. e"}\\
@{term[source]"\<Sum>x\<in>{..<b}. e"} & @{term"\<Sum>x<b. e"} & @{term[mode=latex_sum]"\<Sum>x<b. e"}
\end{tabular}
\end{center}
The left column shows the term before introduction of the new syntax,
the middle column shows the new (default) syntax, and the right column
shows a special syntax. The latter is only meaningful for latex output
and has to be activated explicitly by setting the print mode to
@{text latex_sum} (e.g.\ via @{text "mode = latex_sum"} in
antiquotations). It is not the default \LaTeX\ output because it only
works well with italic-style formulae, not tt-style.

Note that for uniformity on @{typ nat} it is better to use
@{term"\<Sum>x::nat=0..<n. e"} rather than @{text"\<Sum>x<n. e"}: @{text setsum} may
not provide all lemmas available for @{term"{m..<n}"} also in the
special form for @{term"{..<n}"}. *}

text{* This congruence rule should be used for sums over intervals as
the standard theorem @{text[source]setsum_cong} does not work well
with the simplifier who adds the unsimplified premise @{term"x:B"} to
the context. *}

lemma setsum_ivl_cong:
 "\<lbrakk>a = c; b = d; !!x. \<lbrakk> c \<le> x; x < d \<rbrakk> \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow>
 setsum f {a..<b} = setsum g {c..<d}"
by(rule setsum_cong, simp_all)

(* FIXME why are the following simp rules but the corresponding eqns
on intervals are not? *)

lemma setsum_atMost_Suc[simp]: "(\<Sum>i \<le> Suc n. f i) = (\<Sum>i \<le> n. f i) + f(Suc n)"
by (simp add:atMost_Suc add_ac)

lemma setsum_lessThan_Suc[simp]: "(\<Sum>i < Suc n. f i) = (\<Sum>i < n. f i) + f n"
by (simp add:lessThan_Suc add_ac)

lemma setsum_cl_ivl_Suc[simp]:
  "setsum f {m..Suc n} = (if Suc n < m then 0 else setsum f {m..n} + f(Suc n))"
by (auto simp:add_ac atLeastAtMostSuc_conv)

lemma setsum_op_ivl_Suc[simp]:
  "setsum f {m..<Suc n} = (if n < m then 0 else setsum f {m..<n} + f(n))"
by (auto simp:add_ac atLeastLessThanSuc)
(*
lemma setsum_cl_ivl_add_one_nat: "(n::nat) <= m + 1 ==>
    (\<Sum>i=n..m+1. f i) = (\<Sum>i=n..m. f i) + f(m + 1)"
by (auto simp:add_ac atLeastAtMostSuc_conv)
*)

lemma setsum_head:
  fixes n :: nat
  assumes mn: "m <= n" 
  shows "(\<Sum>x\<in>{m..n}. P x) = P m + (\<Sum>x\<in>{m<..n}. P x)" (is "?lhs = ?rhs")
proof -
  from mn
  have "{m..n} = {m} \<union> {m<..n}"
    by (auto intro: ivl_disj_un_singleton)
  hence "?lhs = (\<Sum>x\<in>{m} \<union> {m<..n}. P x)"
    by (simp add: atLeast0LessThan)
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed

lemma setsum_head_Suc:
  "m \<le> n \<Longrightarrow> setsum f {m..n} = f m + setsum f {Suc m..n}"
by (simp add: setsum_head atLeastSucAtMost_greaterThanAtMost)

lemma setsum_head_upt_Suc:
  "m < n \<Longrightarrow> setsum f {m..<n} = f m + setsum f {Suc m..<n}"
apply(insert setsum_head_Suc[of m "n - Suc 0" f])
apply (simp add: atLeastLessThanSuc_atLeastAtMost[symmetric] algebra_simps)
done

lemma setsum_ub_add_nat: assumes "(m::nat) \<le> n + 1"
  shows "setsum f {m..n + p} = setsum f {m..n} + setsum f {n + 1..n + p}"
proof-
  have "{m .. n+p} = {m..n} \<union> {n+1..n+p}" using `m \<le> n+1` by auto
  thus ?thesis by (auto simp: ivl_disj_int setsum_Un_disjoint
    atLeastSucAtMost_greaterThanAtMost)
qed

lemma setsum_add_nat_ivl: "\<lbrakk> m \<le> n; n \<le> p \<rbrakk> \<Longrightarrow>
  setsum f {m..<n} + setsum f {n..<p} = setsum f {m..<p::nat}"
by (simp add:setsum_Un_disjoint[symmetric] ivl_disj_int ivl_disj_un)

lemma setsum_diff_nat_ivl:
fixes f :: "nat \<Rightarrow> 'a::ab_group_add"
shows "\<lbrakk> m \<le> n; n \<le> p \<rbrakk> \<Longrightarrow>
  setsum f {m..<p} - setsum f {m..<n} = setsum f {n..<p}"
using setsum_add_nat_ivl [of m n p f,symmetric]
apply (simp add: add_ac)
done


subsection{* Shifting bounds *}

lemma setsum_shift_bounds_nat_ivl:
  "setsum f {m+k..<n+k} = setsum (%i. f(i + k)){m..<n::nat}"
by (induct "n", auto simp:atLeastLessThanSuc)

lemma setsum_shift_bounds_cl_nat_ivl:
  "setsum f {m+k..n+k} = setsum (%i. f(i + k)){m..n::nat}"
apply (insert setsum_reindex[OF inj_on_add_nat, where h=f and B = "{m..n}"])
apply (simp add:image_add_atLeastAtMost o_def)
done

corollary setsum_shift_bounds_cl_Suc_ivl:
  "setsum f {Suc m..Suc n} = setsum (%i. f(Suc i)){m..n}"
by (simp add:setsum_shift_bounds_cl_nat_ivl[where k="Suc 0", simplified])

corollary setsum_shift_bounds_Suc_ivl:
  "setsum f {Suc m..<Suc n} = setsum (%i. f(Suc i)){m..<n}"
by (simp add:setsum_shift_bounds_nat_ivl[where k="Suc 0", simplified])

lemma setsum_shift_lb_Suc0_0:
  "f(0::nat) = (0::nat) \<Longrightarrow> setsum f {Suc 0..k} = setsum f {0..k}"
by(simp add:setsum_head_Suc)

lemma setsum_shift_lb_Suc0_0_upt:
  "f(0::nat) = 0 \<Longrightarrow> setsum f {Suc 0..<k} = setsum f {0..<k}"
apply(cases k)apply simp
apply(simp add:setsum_head_upt_Suc)
done

subsection {* The formula for geometric sums *}

lemma geometric_sum:
  "x ~= 1 ==> (\<Sum>i=0..<n. x ^ i) =
  (x ^ n - 1) / (x - 1::'a::{field})"
by (induct "n") (simp_all add:field_simps power_Suc)

subsection {* The formula for arithmetic sums *}

lemma gauss_sum:
  "((1::'a::comm_semiring_1) + 1)*(\<Sum>i\<in>{1..n}. of_nat i) =
   of_nat n*((of_nat n)+1)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: algebra_simps)
qed

theorem arith_series_general:
  "((1::'a::comm_semiring_1) + 1) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
proof cases
  assume ngt1: "n > 1"
  let ?I = "\<lambda>i. of_nat i" and ?n = "of_nat n"
  have
    "(\<Sum>i\<in>{..<n}. a+?I i*d) =
     ((\<Sum>i\<in>{..<n}. a) + (\<Sum>i\<in>{..<n}. ?I i*d))"
    by (rule setsum_addf)
  also from ngt1 have "\<dots> = ?n*a + (\<Sum>i\<in>{..<n}. ?I i*d)" by simp
  also from ngt1 have "\<dots> = (?n*a + d*(\<Sum>i\<in>{1..<n}. ?I i))"
    unfolding One_nat_def
    by (simp add: setsum_right_distrib atLeast0LessThan[symmetric] setsum_shift_lb_Suc0_0_upt mult_ac)
  also have "(1+1)*\<dots> = (1+1)*?n*a + d*(1+1)*(\<Sum>i\<in>{1..<n}. ?I i)"
    by (simp add: left_distrib right_distrib)
  also from ngt1 have "{1..<n} = {1..n - 1}"
    by (cases n) (auto simp: atLeastLessThanSuc_atLeastAtMost)
  also from ngt1
  have "(1+1)*?n*a + d*(1+1)*(\<Sum>i\<in>{1..n - 1}. ?I i) = ((1+1)*?n*a + d*?I (n - 1)*?I n)"
    by (simp only: mult_ac gauss_sum [of "n - 1"], unfold One_nat_def)
       (simp add:  mult_ac trans [OF add_commute of_nat_Suc [symmetric]])
  finally show ?thesis by (simp add: algebra_simps)
next
  assume "\<not>(n > 1)"
  hence "n = 1 \<or> n = 0" by auto
  thus ?thesis by (auto simp: algebra_simps)
qed

lemma arith_series_nat:
  "Suc (Suc 0) * (\<Sum>i\<in>{..<n}. a+i*d) = n * (a + (a+(n - 1)*d))"
proof -
  have
    "((1::nat) + 1) * (\<Sum>i\<in>{..<n::nat}. a + of_nat(i)*d) =
    of_nat(n) * (a + (a + of_nat(n - 1)*d))"
    by (rule arith_series_general)
  thus ?thesis
    unfolding One_nat_def by (auto simp add: of_nat_id)
qed

lemma arith_series_int:
  "(2::int) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
  of_nat n * (a + (a + of_nat(n - 1)*d))"
proof -
  have
    "((1::int) + 1) * (\<Sum>i\<in>{..<n}. a + of_nat i * d) =
    of_nat(n) * (a + (a + of_nat(n - 1)*d))"
    by (rule arith_series_general)
  thus ?thesis by simp
qed

lemma sum_diff_distrib:
  fixes P::"nat\<Rightarrow>nat"
  shows
  "\<forall>x. Q x \<le> P x  \<Longrightarrow>
  (\<Sum>x<n. P x) - (\<Sum>x<n. Q x) = (\<Sum>x<n. P x - Q x)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)

  let ?lhs = "(\<Sum>x<n. P x) - (\<Sum>x<n. Q x)"
  let ?rhs = "\<Sum>x<n. P x - Q x"

  from Suc have "?lhs = ?rhs" by simp
  moreover
  from Suc have "?lhs + P n - Q n = ?rhs + (P n - Q n)" by simp
  moreover
  from Suc have
    "(\<Sum>x<n. P x) + P n - ((\<Sum>x<n. Q x) + Q n) = ?rhs + (P n - Q n)"
    by (subst diff_diff_left[symmetric],
        subst diff_add_assoc2)
       (auto simp: diff_add_assoc2 intro: setsum_mono)
  ultimately
  show ?case by simp
qed

subsection {* Products indexed over intervals *}

syntax
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _<_./ _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(PROD _<=_./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_<_./ _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_\<le>_./ _)" [0,0,10] 10)
syntax (HTML output)
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_<_./ _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Prod>_\<le>_./ _)" [0,0,10] 10)
syntax (latex_prod output)
  "_from_to_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ = _\<^raw:}^{>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_from_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ = _\<^raw:}^{<>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_upt_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ < _\<^raw:}$> _)" [0,0,10] 10)
  "_upto_setprod" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\prod_{>_ \<le> _\<^raw:}$> _)" [0,0,10] 10)

translations
  "\<Prod>x=a..b. t" == "CONST setprod (%x. t) {a..b}"
  "\<Prod>x=a..<b. t" == "CONST setprod (%x. t) {a..<b}"
  "\<Prod>i\<le>n. t" == "CONST setprod (\<lambda>i. t) {..n}"
  "\<Prod>i<n. t" == "CONST setprod (\<lambda>i. t) {..<n}"

end
