(*  Title:      HOL/SetInterval.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Clemens Ballarin
                Additions by Jeremy Avigad in March 2004
    Copyright   2000  TU Muenchen

lessThan, greaterThan, atLeast, atMost and two-sided intervals
*)

header {* Set intervals *}

theory SetInterval = IntArith:

constdefs
  lessThan    :: "('a::ord) => 'a set"	("(1{.._'(})")
  "{..u(} == {x. x<u}"

  atMost      :: "('a::ord) => 'a set"	("(1{.._})")
  "{..u} == {x. x<=u}"

  greaterThan :: "('a::ord) => 'a set"	("(1{')_..})")
  "{)l..} == {x. l<x}"

  atLeast     :: "('a::ord) => 'a set"	("(1{_..})")
  "{l..} == {x. l<=x}"

  greaterThanLessThan :: "['a::ord, 'a] => 'a set"  ("(1{')_.._'(})")
  "{)l..u(} == {)l..} Int {..u(}"

  atLeastLessThan :: "['a::ord, 'a] => 'a set"      ("(1{_.._'(})")
  "{l..u(} == {l..} Int {..u(}"

  greaterThanAtMost :: "['a::ord, 'a] => 'a set"    ("(1{')_.._})")
  "{)l..u} == {)l..} Int {..u}"

  atLeastAtMost :: "['a::ord, 'a] => 'a set"        ("(1{_.._})")
  "{l..u} == {l..} Int {..u}"

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
  "@UNION_le"   :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Union>\<^bsub>_ \<le> _\<^esub>/ _)" 10)
  "@UNION_less" :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Union>\<^bsub>_ < _\<^esub>/ _)" 10)
  "@INTER_le"   :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Inter>\<^bsub>_ \<le> _\<^esub>/ _)" 10)
  "@INTER_less" :: "nat \<Rightarrow> nat => 'b set => 'b set"       ("(3\<Inter>\<^bsub>_ < _\<^esub>/ _)" 10)

translations
  "UN i<=n. A"  == "UN i:{..n}. A"
  "UN i<n. A"   == "UN i:{..n(}. A"
  "INT i<=n. A" == "INT i:{..n}. A"
  "INT i<n. A"  == "INT i:{..n(}. A"


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
 apply (simp add: greaterThan_subset_iff order_antisym, simp) 
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
 apply (simp add: lessThan_subset_iff order_antisym, simp) 
done


subsection {*Two-sided intervals*}

text {* @{text greaterThanLessThan} *}

lemma greaterThanLessThan_iff [simp]:
  "(i : {)l..u(}) = (l < i & i < u)"
by (simp add: greaterThanLessThan_def)

text {* @{text atLeastLessThan} *}

lemma atLeastLessThan_iff [simp]:
  "(i : {l..u(}) = (l <= i & i < u)"
by (simp add: atLeastLessThan_def)

text {* @{text greaterThanAtMost} *}

lemma greaterThanAtMost_iff [simp]:
  "(i : {)l..u}) = (l < i & i <= u)"
by (simp add: greaterThanAtMost_def)

text {* @{text atLeastAtMost} *}

lemma atLeastAtMost_iff [simp]:
  "(i : {l..u}) = (l <= i & i <= u)"
by (simp add: atLeastAtMost_def)

text {* The above four lemmas could be declared as iffs.
  If we do so, a call to blast in Hyperreal/Star.ML, lemma @{text STAR_Int}
  seems to take forever (more than one hour). *}


subsection {* Intervals of natural numbers *}

lemma lessThan_0 [simp]: "lessThan (0::nat) = {}"
by (simp add: lessThan_def)

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
by (simp add: lessThan_def less_Suc_eq, blast)

lemma lessThan_Suc_atMost: "lessThan (Suc k) = atMost k"
by (simp add: lessThan_def atMost_def less_Suc_eq_le)

lemma UN_lessThan_UNIV: "(UN m::nat. lessThan m) = UNIV"
by blast

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

lemma atMost_0 [simp]: "atMost (0::nat) = {0}"
by (simp add: atMost_def)

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
apply (simp add: atMost_def)
apply (simp add: less_Suc_eq order_le_less, blast)
done

lemma UN_atMost_UNIV: "(UN m::nat. atMost m) = UNIV"
by blast

text {* Intervals of nats with @{text Suc} *}

lemma atLeastLessThanSuc_atLeastAtMost: "{l..Suc u(} = {l..u}"
  by (simp add: lessThan_Suc_atMost atLeastAtMost_def atLeastLessThan_def)

lemma atLeastSucAtMost_greaterThanAtMost: "{Suc l..u} = {)l..u}"  
  by (simp add: atLeast_Suc_greaterThan atLeastAtMost_def 
    greaterThanAtMost_def)

lemma atLeastSucLessThan_greaterThanLessThan: "{Suc l..u(} = {)l..u(}"  
  by (simp add: atLeast_Suc_greaterThan atLeastLessThan_def 
    greaterThanLessThan_def)

subsubsection {* Finiteness *}

lemma finite_lessThan [iff]: fixes k :: nat shows "finite {..k(}"
  by (induct k) (simp_all add: lessThan_Suc)

lemma finite_atMost [iff]: fixes k :: nat shows "finite {..k}"
  by (induct k) (simp_all add: atMost_Suc)

lemma finite_greaterThanLessThan [iff]:
  fixes l :: nat shows "finite {)l..u(}"
by (simp add: greaterThanLessThan_def)

lemma finite_atLeastLessThan [iff]:
  fixes l :: nat shows "finite {l..u(}"
by (simp add: atLeastLessThan_def)

lemma finite_greaterThanAtMost [iff]:
  fixes l :: nat shows "finite {)l..u}"
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

lemma card_lessThan [simp]: "card {..u(} = u"
  by (induct_tac u, simp_all add: lessThan_Suc)

lemma card_atMost [simp]: "card {..u} = Suc u"
  by (simp add: lessThan_Suc_atMost [THEN sym])

lemma card_atLeastLessThan [simp]: "card {l..u(} = u - l"
  apply (subgoal_tac "card {l..u(} = card {..u-l(}")
  apply (erule ssubst, rule card_lessThan)
  apply (subgoal_tac "(%x. x + l) ` {..u-l(} = {l..u(}")
  apply (erule subst)
  apply (rule card_image)
  apply (rule finite_lessThan)
  apply (simp add: inj_on_def)
  apply (auto simp add: image_def atLeastLessThan_def lessThan_def)
  apply arith
  apply (rule_tac x = "x - l" in exI)
  apply arith
  done

lemma card_atLeastAtMost [simp]: "card {l..u} = Suc u - l"
  by (subst atLeastLessThanSuc_atLeastAtMost [THEN sym], simp)

lemma card_greaterThanAtMost [simp]: "card {)l..u} = u - l" 
  by (subst atLeastSucAtMost_greaterThanAtMost [THEN sym], simp)

lemma card_greaterThanLessThan [simp]: "card {)l..u(} = u - Suc l"
  by (subst atLeastSucLessThan_greaterThanLessThan [THEN sym], simp)

subsection {* Intervals of integers *}

lemma atLeastLessThanPlusOne_atLeastAtMost_int: "{l..u+1(} = {l..(u::int)}"
  by (auto simp add: atLeastAtMost_def atLeastLessThan_def)

lemma atLeastPlusOneAtMost_greaterThanAtMost_int: "{l+1..u} = {)l..(u::int)}"  
  by (auto simp add: atLeastAtMost_def greaterThanAtMost_def)

lemma atLeastPlusOneLessThan_greaterThanLessThan_int: 
    "{l+1..u(} = {)l..(u::int)(}"  
  by (auto simp add: atLeastLessThan_def greaterThanLessThan_def)

subsubsection {* Finiteness *}

lemma image_atLeastZeroLessThan_int: "0 \<le> u ==> 
    {(0::int)..u(} = int ` {..nat u(}"
  apply (unfold image_def lessThan_def)
  apply auto
  apply (rule_tac x = "nat x" in exI)
  apply (auto simp add: zless_nat_conj zless_nat_eq_int_zless [THEN sym])
  done

lemma finite_atLeastZeroLessThan_int: "finite {(0::int)..u(}"
  apply (case_tac "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_int, assumption)
  apply (rule finite_imageI)
  apply auto
  apply (subgoal_tac "{0..u(} = {}")
  apply auto
  done

lemma image_atLeastLessThan_int_shift: 
    "(%x. x + (l::int)) ` {0..u-l(} = {l..u(}"
  apply (auto simp add: image_def atLeastLessThan_iff)
  apply (rule_tac x = "x - l" in bexI)
  apply auto
  done

lemma finite_atLeastLessThan_int [iff]: "finite {l..(u::int)(}"
  apply (subgoal_tac "(%x. x + l) ` {0..u-l(} = {l..u(}")
  apply (erule subst)
  apply (rule finite_imageI)
  apply (rule finite_atLeastZeroLessThan_int)
  apply (rule image_atLeastLessThan_int_shift)
  done

lemma finite_atLeastAtMost_int [iff]: "finite {l..(u::int)}" 
  by (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym], simp)

lemma finite_greaterThanAtMost_int [iff]: "finite {)l..(u::int)}" 
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma finite_greaterThanLessThan_int [iff]: "finite {)l..(u::int)(}" 
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)

subsubsection {* Cardinality *}

lemma card_atLeastZeroLessThan_int: "card {(0::int)..u(} = nat u"
  apply (case_tac "0 \<le> u")
  apply (subst image_atLeastZeroLessThan_int, assumption)
  apply (subst card_image)
  apply (auto simp add: inj_on_def)
  done

lemma card_atLeastLessThan_int [simp]: "card {l..u(} = nat (u - l)"
  apply (subgoal_tac "card {l..u(} = card {0..u-l(}")
  apply (erule ssubst, rule card_atLeastZeroLessThan_int)
  apply (subgoal_tac "(%x. x + l) ` {0..u-l(} = {l..u(}")
  apply (erule subst)
  apply (rule card_image)
  apply (rule finite_atLeastZeroLessThan_int)
  apply (simp add: inj_on_def)
  apply (rule image_atLeastLessThan_int_shift)
  done

lemma card_atLeastAtMost_int [simp]: "card {l..u} = nat (u - l + 1)"
  apply (subst atLeastLessThanPlusOne_atLeastAtMost_int [THEN sym])
  apply (auto simp add: compare_rls)
  done

lemma card_greaterThanAtMost_int [simp]: "card {)l..u} = nat (u - l)" 
  by (subst atLeastPlusOneAtMost_greaterThanAtMost_int [THEN sym], simp)

lemma card_greaterThanLessThan_int [simp]: "card {)l..u(} = nat (u - (l + 1))"
  by (subst atLeastPlusOneLessThan_greaterThanLessThan_int [THEN sym], simp)


subsection {*Lemmas useful with the summation operator setsum*}

text {* For examples, see Algebra/poly/UnivPoly.thy *}

subsubsection {* Disjoint Unions *}

text {* Singletons and open intervals *}

lemma ivl_disj_un_singleton:
  "{l::'a::linorder} Un {)l..} = {l..}"
  "{..u(} Un {u::'a::linorder} = {..u}"
  "(l::'a::linorder) < u ==> {l} Un {)l..u(} = {l..u(}"
  "(l::'a::linorder) < u ==> {)l..u(} Un {u} = {)l..u}"
  "(l::'a::linorder) <= u ==> {l} Un {)l..u} = {l..u}"
  "(l::'a::linorder) <= u ==> {l..u(} Un {u} = {l..u}"
by auto

text {* One- and two-sided intervals *}

lemma ivl_disj_un_one:
  "(l::'a::linorder) < u ==> {..l} Un {)l..u(} = {..u(}"
  "(l::'a::linorder) <= u ==> {..l(} Un {l..u(} = {..u(}"
  "(l::'a::linorder) <= u ==> {..l} Un {)l..u} = {..u}"
  "(l::'a::linorder) <= u ==> {..l(} Un {l..u} = {..u}"
  "(l::'a::linorder) <= u ==> {)l..u} Un {)u..} = {)l..}"
  "(l::'a::linorder) < u ==> {)l..u(} Un {u..} = {)l..}"
  "(l::'a::linorder) <= u ==> {l..u} Un {)u..} = {l..}"
  "(l::'a::linorder) <= u ==> {l..u(} Un {u..} = {l..}"
by auto

text {* Two- and two-sided intervals *}

lemma ivl_disj_un_two:
  "[| (l::'a::linorder) < m; m <= u |] ==> {)l..m(} Un {m..u(} = {)l..u(}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {)l..m} Un {)m..u(} = {)l..u(}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..m(} Un {m..u(} = {l..u(}"
  "[| (l::'a::linorder) <= m; m < u |] ==> {l..m} Un {)m..u(} = {l..u(}"
  "[| (l::'a::linorder) < m; m <= u |] ==> {)l..m(} Un {m..u} = {)l..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {)l..m} Un {)m..u} = {)l..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..m(} Un {m..u} = {l..u}"
  "[| (l::'a::linorder) <= m; m <= u |] ==> {l..m} Un {)m..u} = {l..u}"
by auto

lemmas ivl_disj_un = ivl_disj_un_singleton ivl_disj_un_one ivl_disj_un_two

subsubsection {* Disjoint Intersections *}

text {* Singletons and open intervals *}

lemma ivl_disj_int_singleton:
  "{l::'a::order} Int {)l..} = {}"
  "{..u(} Int {u} = {}"
  "{l} Int {)l..u(} = {}"
  "{)l..u(} Int {u} = {}"
  "{l} Int {)l..u} = {}"
  "{l..u(} Int {u} = {}"
  by simp+

text {* One- and two-sided intervals *}

lemma ivl_disj_int_one:
  "{..l::'a::order} Int {)l..u(} = {}"
  "{..l(} Int {l..u(} = {}"
  "{..l} Int {)l..u} = {}"
  "{..l(} Int {l..u} = {}"
  "{)l..u} Int {)u..} = {}"
  "{)l..u(} Int {u..} = {}"
  "{l..u} Int {)u..} = {}"
  "{l..u(} Int {u..} = {}"
  by auto

text {* Two- and two-sided intervals *}

lemma ivl_disj_int_two:
  "{)l::'a::order..m(} Int {m..u(} = {}"
  "{)l..m} Int {)m..u(} = {}"
  "{l..m(} Int {m..u(} = {}"
  "{l..m} Int {)m..u(} = {}"
  "{)l..m(} Int {m..u} = {}"
  "{)l..m} Int {)m..u} = {}"
  "{l..m(} Int {m..u} = {}"
  "{l..m} Int {)m..u} = {}"
  by auto

lemmas ivl_disj_int = ivl_disj_int_singleton ivl_disj_int_one ivl_disj_int_two

end
