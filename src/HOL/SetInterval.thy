(*  Title:      HOL/SetInterval.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Clemens Ballarin
                Additions by Jeremy Avigad in March 2004
    Copyright   2000  TU Muenchen

lessThan, greaterThan, atLeast, atMost and two-sided intervals
*)

header {* Set intervals *}

theory SetInterval
imports IntArith
begin

constdefs
  lessThan    :: "('a::ord) => 'a set"	("(1{..<_})")
  "{..<u} == {x. x<u}"

  atMost      :: "('a::ord) => 'a set"	("(1{.._})")
  "{..u} == {x. x<=u}"

  greaterThan :: "('a::ord) => 'a set"	("(1{_<..})")
  "{l<..} == {x. l<x}"

  atLeast     :: "('a::ord) => 'a set"	("(1{_..})")
  "{l..} == {x. l<=x}"

  greaterThanLessThan :: "['a::ord, 'a] => 'a set"  ("(1{_<..<_})")
  "{l<..<u} == {l<..} Int {..<u}"

  atLeastLessThan :: "['a::ord, 'a] => 'a set"      ("(1{_..<_})")
  "{l..<u} == {l..} Int {..<u}"

  greaterThanAtMost :: "['a::ord, 'a] => 'a set"    ("(1{_<.._})")
  "{l<..u} == {l<..} Int {..u}"

  atLeastAtMost :: "['a::ord, 'a] => 'a set"        ("(1{_.._})")
  "{l..u} == {l..} Int {..u}"

(* Old syntax, will disappear! *)
syntax
  "_lessThan"    :: "('a::ord) => 'a set"	("(1{.._'(})")
  "_greaterThan" :: "('a::ord) => 'a set"	("(1{')_..})")
  "_greaterThanLessThan" :: "['a::ord, 'a] => 'a set"  ("(1{')_.._'(})")
  "_atLeastLessThan" :: "['a::ord, 'a] => 'a set"      ("(1{_.._'(})")
  "_greaterThanAtMost" :: "['a::ord, 'a] => 'a set"    ("(1{')_.._})")
translations
  "{..m(}" => "{..<m}"
  "{)m..}" => "{m<..}"
  "{)m..n(}" => "{m<..<n}"
  "{m..n(}" => "{m..<n}"
  "{)m..n}" => "{m<..n}"


text{* A note of warning when using @{term"{..<n}"} on type @{typ
nat}: it is equivalent to @{term"{0::nat..<n}"} but some lemmas involving
@{term"{m..<n}"} may not exist in @{term"{..<n}"}-form as well. *}

syntax
  "@UNION_le"   :: "nat => nat => 'b set => 'b set"       ("(3UN _<=_./ _)" 10)
  "@UNION_less" :: "nat => nat => 'b set => 'b set"       ("(3UN _<_./ _)" 10)
  "@INTER_le"   :: "nat => nat => 'b set => 'b set"       ("(3INT _<=_./ _)" 10)
  "@INTER_less" :: "nat => nat => 'b set => 'b set"       ("(3INT _<_./ _)" 10)

syntax (input)
  "@UNION_le"   :: "nat => nat => 'b set => 'b set"       ("(3\<Union> _\<le>_./ _)" 10)
  "@UNION_less" :: "nat => nat => 'b set => 'b set"       ("(3\<Union> _<_./ _)" 10)
  "@INTER_le"   :: "nat => nat => 'b set => 'b set"       ("(3\<Inter> _\<le>_./ _)" 10)
  "@INTER_less" :: "nat => nat => 'b set => 'b set"       ("(3\<Inter> _<_./ _)" 10)

syntax (xsymbols)
  "@UNION_le"   :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Union>(00\<^bsub>_ \<le> _\<^esub>)/ _)" 10)
  "@UNION_less" :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Union>(00\<^bsub>_ < _\<^esub>)/ _)" 10)
  "@INTER_le"   :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Inter>(00\<^bsub>_ \<le> _\<^esub>)/ _)" 10)
  "@INTER_less" :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Inter>(00\<^bsub>_ < _\<^esub>)/ _)" 10)

translations
  "UN i<=n. A"  == "UN i:{..n}. A"
  "UN i<n. A"   == "UN i:{..<n}. A"
  "INT i<=n. A" == "INT i:{..n}. A"
  "INT i<n. A"  == "INT i:{..<n}. A"


subsection {* Various equivalences *}

lemma lessThan_iff [iff]: "(i: lessThan k) = (i<k)"
by (simp add: lessThan_def)

lemma Compl_lessThan [simp]:
    "!!k:: 'a::linorder. -lessThan k = atLeast k"
apply (auto simp add: lessThan_def atLeast_def)
done

lemma single_Diff_lessThan [simp]: "!!k:: 'a::order. {k} - lessThan k = {k}"
by auto

lemma greaterThan_iff [iff]: "(i: greaterThan k) = (k<i)"
by (simp add: greaterThan_def)

lemma Compl_greaterThan [simp]:
    "!!k:: 'a::linorder. -greaterThan k = atMost k"
apply (simp add: greaterThan_def atMost_def le_def, auto)
done

lemma Compl_atMost [simp]: "!!k:: 'a::linorder. -atMost k = greaterThan k"
apply (subst Compl_greaterThan [symmetric])
apply (rule double_complement)
done

lemma atLeast_iff [iff]: "(i: atLeast k) = (k<=i)"
by (simp add: atLeast_def)

lemma Compl_atLeast [simp]:
    "!!k:: 'a::linorder. -atLeast k = lessThan k"
apply (simp add: lessThan_def atLeast_def le_def, auto)
done

lemma atMost_iff [iff]: "(i: atMost k) = (i<=k)"
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
 apply (simp_all add: greaterThan_subset_iff)
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
 apply (simp_all add: lessThan_subset_iff)
done


subsection {*Two-sided intervals*}

lemma greaterThanLessThan_iff [simp]:
  "(i : {l<..<u}) = (l < i & i < u)"
by (simp add: greaterThanLessThan_def)

lemma atLeastLessThan_iff [simp]:
  "(i : {l..<u}) = (l <= i & i < u)"
by (simp add: atLeastLessThan_def)

lemma greaterThanAtMost_iff [simp]:
  "(i : {l<..u}) = (l < i & i <= u)"
by (simp add: greaterThanAtMost_def)

lemma atLeastAtMost_iff [simp]:
  "(i : {l..u}) = (l <= i & i <= u)"
by (simp add: atLeastAtMost_def)

text {* The above four lemmas could be declared as iffs.
  If we do so, a call to blast in Hyperreal/Star.ML, lemma @{text STAR_Int}
  seems to take forever (more than one hour). *}

subsubsection{* Emptyness and singletons *}

lemma atLeastAtMost_empty [simp]: "n < m ==> {m::'a::order..n} = {}";
  by (auto simp add: atLeastAtMost_def atMost_def atLeast_def);

lemma atLeastLessThan_empty[simp]: "n \<le> m ==> {m..<n::'a::order} = {}"
by (auto simp add: atLeastLessThan_def)

lemma atLeastAtMost_singleton [simp]: "{a::'a::order..a} = {a}";
  by (auto simp add: atLeastAtMost_def atMost_def atLeast_def);

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

text{*But not a simprule because some concepts are better left in terms
  of @{term atLeastLessThan}*}
lemma atLeast0LessThan: "{0::nat..<n} = {..<n}"
by(simp add:lessThan_def atLeastLessThan_def)

lemma atLeastLessThan0 [simp]: "{m..<0::nat} = {}"
by (simp add: atLeastLessThan_def)

subsubsection {* Intervals of nats with @{term Suc} *}

text{*Not a simprule because the RHS is too messy.*}
lemma atLeastLessThanSuc:
    "{m..<Suc n} = (if m \<le> n then insert n {m..<n} else {})"
by (auto simp add: atLeastLessThan_def)

lemma atLeastLessThan_singleton [simp]: "{m..<Suc m} = {m}"
by (auto simp add: atLeastLessThan_def)

lemma atLeast_sum_LessThan [simp]: "{m + k..<k::nat} = {}"
by (induct k, simp_all add: atLeastLessThanSuc)

lemma atLeastSucLessThan [simp]: "{Suc n..<n} = {}"
by (auto simp add: atLeastLessThan_def)

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

lemma bounded_nat_set_is_finite:
    "(ALL i:N. i < (n::nat)) ==> finite N"
  -- {* A bounded set of natural numbers is finite. *}
  apply (rule finite_subset)
   apply (rule_tac [2] finite_lessThan, auto)
  done

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
  apply arith
  apply (rule_tac x = "x - l" in exI)
  apply arith
  done

lemma card_atLeastAtMost [simp]: "card {l..u} = Suc u - l"
  by (subst atLeastLessThanSuc_atLeastAtMost [THEN sym], simp)

lemma card_greaterThanAtMost [simp]: "card {l<..u} = u - l"
  by (subst atLeastSucAtMost_greaterThanAtMost [THEN sym], simp)

lemma card_greaterThanLessThan [simp]: "card {l<..<u} = u - Suc l"
  by (subst atLeastSucLessThan_greaterThanLessThan [THEN sym], simp)

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

lemma image_atLeastLessThan_int_shift:
    "(%x. x + (l::int)) ` {0..<u-l} = {l..<u}"
  apply (auto simp add: image_def atLeastLessThan_iff)
  apply (rule_tac x = "x - l" in bexI)
  apply auto
  done

lemma finite_atLeastLessThan_int [iff]: "finite {l..<u::int}"
  apply (subgoal_tac "(%x. x + l) ` {0..<u-l} = {l..<u}")
  apply (erule subst)
  apply (rule finite_imageI)
  apply (rule finite_atLeastZeroLessThan_int)
  apply (rule image_atLeastLessThan_int_shift)
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
  apply (rule image_atLeastLessThan_int_shift)
  done

lemma card_atLeastAtMost_int [simp]: "card {l..u} = nat (u - l + 1)"
  apply (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym])
  apply (auto simp add: compare_rls)
  done

lemma card_greaterThanAtMost_int [simp]: "card {l<..u} = nat (u - l)"
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma card_greaterThanLessThan_int [simp]: "card {l<..<u} = nat (u - (l + 1))"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)


subsection {*Lemmas useful with the summation operator setsum*}

text {* For examples, see Algebra/poly/UnivPoly.thy *}

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

lemma ivl_subset[simp]:
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
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(SUM _<_./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_<_./ _)" [0,0,10] 10)
syntax (HTML output)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _.._./ _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_ = _..<_./ _)" [0,0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("(3\<Sum>_<_./ _)" [0,0,10] 10)
syntax (latex_sum output)
  "_from_to_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ = _\<^raw:}^{>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_from_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ = _\<^raw:}^{<>_\<^raw:}$> _)" [0,0,0,10] 10)
  "_upto_setsum" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
 ("(3\<^raw:$\sum_{>_ < _\<^raw:}$> _)" [0,0,10] 10)

translations
  "\<Sum>x=a..b. t" == "setsum (%x. t) {a..b}"
  "\<Sum>x=a..<b. t" == "setsum (%x. t) {a..<b}"
  "\<Sum>i<n. t" == "setsum (\<lambda>i. t) {..<n}"

text{* The above introduces some pretty alternative syntaxes for
summation over intervals:
\begin{center}
\begin{tabular}{lll}
Old & New & \LaTeX\\
@{term[source]"\<Sum>x\<in>{a..b}. e"} & @{term"\<Sum>x=a..b. e"} & @{term[mode=latex_sum]"\<Sum>x=a..b. e"}\\
@{term[source]"\<Sum>x\<in>{a..<b}. e"} & @{term"\<Sum>x=a..<b. e"} & @{term[mode=latex_sum]"\<Sum>x=a..<b. e"}\\
@{term[source]"\<Sum>x\<in>{..<b}. e"} & @{term"\<Sum>x<b. e"} & @{term[mode=latex_sum]"\<Sum>x<b. e"}
\end{tabular}
\end{center}
The left column shows the term before introduction of the new syntax,
the middle column shows the new (default) syntax, and the right column
shows a special syntax. The latter is only meaningful for latex output
and has to be activated explicitly by setting the print mode to
\texttt{latex\_sum} (e.g.\ via \texttt{mode=latex\_sum} in
antiquotations). It is not the default \LaTeX\ output because it only
works well with italic-style formulae, not tt-style.

Note that for uniformity on @{typ nat} it is better to use
@{term"\<Sum>x::nat=0..<n. e"} rather than @{text"\<Sum>x<n. e"}: @{text setsum} may
not provide all lemmas available for @{term"{m..<n}"} also in the
special form for @{term"{..<n}"}. *}

(* FIXME change the simplifier's treatment of congruence rules?? *)

text{* This congruence rule should be used for sums over intervals as
the standard theorem @{text[source]setsum_cong} does not work well
with the simplifier who adds the unsimplified premise @{term"x:B"} to
the context. *}

lemma setsum_ivl_cong:
 "\<lbrakk>a = c; b = d; !!x. \<lbrakk> c \<le> x; x < d \<rbrakk> \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow>
 setsum f {a..<b} = setsum g {c..<d}"
by(rule setsum_cong, simp_all)

lemma setsum_cl_ivl_add_one_nat: "(n::nat) <= m + 1 ==>
    (\<Sum>i=n..m+1. f i) = (\<Sum>i=n..m. f i) + f(m + 1)"
by (auto simp:add_ac atLeastAtMostSuc_conv)

(* FIXME delete
lemma Summation_Suc[simp]: "(\<Sum>i < Suc n. b i) = b n + (\<Sum>i < n. b i)"
by (simp add:lessThan_Suc)
*)

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

lemma setsum_shift_bounds_nat_ivl:
  "setsum f {m+k..<n+k} = setsum (%i. f(i + k)){m..<n::nat}"
by (induct "n", auto simp:atLeastLessThanSuc)


ML
{*
val Compl_atLeast = thm "Compl_atLeast";
val Compl_atMost = thm "Compl_atMost";
val Compl_greaterThan = thm "Compl_greaterThan";
val Compl_lessThan = thm "Compl_lessThan";
val INT_greaterThan_UNIV = thm "INT_greaterThan_UNIV";
val UN_atLeast_UNIV = thm "UN_atLeast_UNIV";
val UN_atMost_UNIV = thm "UN_atMost_UNIV";
val UN_lessThan_UNIV = thm "UN_lessThan_UNIV";
val atLeastAtMost_def = thm "atLeastAtMost_def";
val atLeastAtMost_iff = thm "atLeastAtMost_iff";
val atLeastLessThan_def  = thm "atLeastLessThan_def";
val atLeastLessThan_iff = thm "atLeastLessThan_iff";
val atLeast_0 = thm "atLeast_0";
val atLeast_Suc = thm "atLeast_Suc";
val atLeast_def      = thm "atLeast_def";
val atLeast_iff = thm "atLeast_iff";
val atMost_0 = thm "atMost_0";
val atMost_Int_atLeast = thm "atMost_Int_atLeast";
val atMost_Suc = thm "atMost_Suc";
val atMost_def       = thm "atMost_def";
val atMost_iff = thm "atMost_iff";
val greaterThanAtMost_def  = thm "greaterThanAtMost_def";
val greaterThanAtMost_iff = thm "greaterThanAtMost_iff";
val greaterThanLessThan_def  = thm "greaterThanLessThan_def";
val greaterThanLessThan_iff = thm "greaterThanLessThan_iff";
val greaterThan_0 = thm "greaterThan_0";
val greaterThan_Suc = thm "greaterThan_Suc";
val greaterThan_def  = thm "greaterThan_def";
val greaterThan_iff = thm "greaterThan_iff";
val ivl_disj_int = thms "ivl_disj_int";
val ivl_disj_int_one = thms "ivl_disj_int_one";
val ivl_disj_int_singleton = thms "ivl_disj_int_singleton";
val ivl_disj_int_two = thms "ivl_disj_int_two";
val ivl_disj_un = thms "ivl_disj_un";
val ivl_disj_un_one = thms "ivl_disj_un_one";
val ivl_disj_un_singleton = thms "ivl_disj_un_singleton";
val ivl_disj_un_two = thms "ivl_disj_un_two";
val lessThan_0 = thm "lessThan_0";
val lessThan_Suc = thm "lessThan_Suc";
val lessThan_Suc_atMost = thm "lessThan_Suc_atMost";
val lessThan_def     = thm "lessThan_def";
val lessThan_iff = thm "lessThan_iff";
val single_Diff_lessThan = thm "single_Diff_lessThan";

val bounded_nat_set_is_finite = thm "bounded_nat_set_is_finite";
val finite_atMost = thm "finite_atMost";
val finite_lessThan = thm "finite_lessThan";
*}

end
