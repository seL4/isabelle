(*  Title:      HOL/SetInterval.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Clemens Ballarin
    Copyright   2000  TU Muenchen

lessThan, greaterThan, atLeast, atMost and two-sided intervals
*)

theory SetInterval = NatArith:

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


subsection {*lessThan*}

lemma lessThan_iff [iff]: "(i: lessThan k) = (i<k)"
by (simp add: lessThan_def)

lemma lessThan_0 [simp]: "lessThan (0::nat) = {}"
by (simp add: lessThan_def)

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
by (simp add: lessThan_def less_Suc_eq, blast)

lemma lessThan_Suc_atMost: "lessThan (Suc k) = atMost k"
by (simp add: lessThan_def atMost_def less_Suc_eq_le)

lemma UN_lessThan_UNIV: "(UN m::nat. lessThan m) = UNIV"
by blast

lemma Compl_lessThan [simp]: 
    "!!k:: 'a::linorder. -lessThan k = atLeast k"
apply (auto simp add: lessThan_def atLeast_def)
done

lemma single_Diff_lessThan [simp]: "!!k:: 'a::order. {k} - lessThan k = {k}"
by auto

subsection {*greaterThan*}

lemma greaterThan_iff [iff]: "(i: greaterThan k) = (k<i)"
by (simp add: greaterThan_def)

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

lemma Compl_greaterThan [simp]: 
    "!!k:: 'a::linorder. -greaterThan k = atMost k"
apply (simp add: greaterThan_def atMost_def le_def, auto)
done

lemma Compl_atMost [simp]: "!!k:: 'a::linorder. -atMost k = greaterThan k"
apply (subst Compl_greaterThan [symmetric])
apply (rule double_complement) 
done


subsection {*atLeast*}

lemma atLeast_iff [iff]: "(i: atLeast k) = (k<=i)"
by (simp add: atLeast_def)

lemma atLeast_0 [simp]: "atLeast (0::nat) = UNIV"
by (unfold atLeast_def UNIV_def, simp)

lemma atLeast_Suc: "atLeast (Suc k) = atLeast k - {k}"
apply (simp add: atLeast_def)
apply (simp add: Suc_le_eq)
apply (simp add: order_le_less, blast)
done

lemma UN_atLeast_UNIV: "(UN m::nat. atLeast m) = UNIV"
by blast

lemma Compl_atLeast [simp]: 
    "!!k:: 'a::linorder. -atLeast k = lessThan k"
apply (simp add: lessThan_def atLeast_def le_def, auto)
done


subsection {*atMost*}

lemma atMost_iff [iff]: "(i: atMost k) = (i<=k)"
by (simp add: atMost_def)

lemma atMost_0 [simp]: "atMost (0::nat) = {0}"
by (simp add: atMost_def)

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
apply (simp add: atMost_def)
apply (simp add: less_Suc_eq order_le_less, blast)
done

lemma UN_atMost_UNIV: "(UN m::nat. atMost m) = UNIV"
by blast


subsection {*Logical Equivalences for Set Inclusion and Equality*}

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


subsection {*Combined properties*}

lemma atMost_Int_atLeast: "!!n:: 'a::order. atMost n Int atLeast n = {n}"
by (blast intro: order_antisym)

subsection {*Two-sided intervals*}

(* greaterThanLessThan *)

lemma greaterThanLessThan_iff [simp]:
  "(i : {)l..u(}) = (l < i & i < u)"
by (simp add: greaterThanLessThan_def)

(* atLeastLessThan *)

lemma atLeastLessThan_iff [simp]:
  "(i : {l..u(}) = (l <= i & i < u)"
by (simp add: atLeastLessThan_def)

(* greaterThanAtMost *)

lemma greaterThanAtMost_iff [simp]:
  "(i : {)l..u}) = (l < i & i <= u)"
by (simp add: greaterThanAtMost_def)

(* atLeastAtMost *)

lemma atLeastAtMost_iff [simp]:
  "(i : {l..u}) = (l <= i & i <= u)"
by (simp add: atLeastAtMost_def)

(* The above four lemmas could be declared as iffs.
   If we do so, a call to blast in Hyperreal/Star.ML, lemma STAR_Int
   seems to take forever (more than one hour). *)

subsection {*Lemmas useful with the summation operator setsum*}

(* For examples, see Algebra/poly/UnivPoly.thy *)

(** Disjoint Unions **)

(* Singletons and open intervals *)

lemma ivl_disj_un_singleton:
  "{l::'a::linorder} Un {)l..} = {l..}"
  "{..u(} Un {u::'a::linorder} = {..u}"
  "(l::'a::linorder) < u ==> {l} Un {)l..u(} = {l..u(}"
  "(l::'a::linorder) < u ==> {)l..u(} Un {u} = {)l..u}"
  "(l::'a::linorder) <= u ==> {l} Un {)l..u} = {l..u}"
  "(l::'a::linorder) <= u ==> {l..u(} Un {u} = {l..u}"
by auto

(* One- and two-sided intervals *)

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

(* Two- and two-sided intervals *)

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

(** Disjoint Intersections **)

(* Singletons and open intervals *)

lemma ivl_disj_int_singleton:
  "{l::'a::order} Int {)l..} = {}"
  "{..u(} Int {u} = {}"
  "{l} Int {)l..u(} = {}"
  "{)l..u(} Int {u} = {}"
  "{l} Int {)l..u} = {}"
  "{l..u(} Int {u} = {}"
  by simp+

(* One- and two-sided intervals *)

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

(* Two- and two-sided intervals *)

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
