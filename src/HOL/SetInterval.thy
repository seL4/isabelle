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


subsection {* Setup of transitivity reasoner *}

ML {*

structure Trans_Tac = Trans_Tac_Fun (
  struct
    val less_reflE = thm "order_less_irrefl" RS thm "notE";
    val le_refl = thm "order_refl";
    val less_imp_le = thm "order_less_imp_le";
    val not_lessI = thm "linorder_not_less" RS thm "iffD2";
    val not_leI = thm "linorder_not_less" RS thm "iffD2";
    val not_lessD = thm "linorder_not_less" RS thm "iffD1";
    val not_leD = thm "linorder_not_le" RS thm "iffD1";
    val eqI = thm "order_antisym";
    val eqD1 = thm "order_eq_refl";
    val eqD2 = thm "sym" RS thm "order_eq_refl";
    val less_trans = thm "order_less_trans";
    val less_le_trans = thm "order_less_le_trans";
    val le_less_trans = thm "order_le_less_trans";
    val le_trans = thm "order_trans";
    fun decomp (Trueprop $ t) =
      let fun dec (Const ("Not", _) $ t) = (
              case dec t of
		None => None
	      | Some (t1, rel, t2) => Some (t1, "~" ^ rel, t2))
	    | dec (Const (rel, _) $ t1 $ t2) = 
                Some (t1, implode (drop (3, explode rel)), t2)
	    | dec _ = None
      in dec t end
      | decomp _ = None
  end);

val trans_tac = Trans_Tac.trans_tac;

*}

method_setup trans =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (trans_tac)) *}
  {* simple transitivity reasoner *}


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
 apply (blast intro: linorder_not_less [THEN iffD1])
apply (blast dest: order_le_less_trans)
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
apply (blast intro: linorder_not_less [THEN iffD1])
apply (blast dest: order_le_less_trans)
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
apply (blast intro: linorder_not_less [THEN iffD1])
apply (blast dest: order_le_less_trans)
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
apply (blast intro: order_le_less_trans) 
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
apply (blast intro: order_less_le_trans) 
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
by auto (elim linorder_neqE | trans+)+

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
by auto trans+

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
by auto trans+

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
  by auto trans+

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
  by auto trans+

lemmas ivl_disj_int = ivl_disj_int_singleton ivl_disj_int_one ivl_disj_int_two

end
