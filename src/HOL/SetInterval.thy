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

(* Setup of transitivity reasoner *)

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

(*** lessThan ***)

lemma lessThan_iff: "(i: lessThan k) = (i<k)"

apply (unfold lessThan_def)
apply blast
done
declare lessThan_iff [iff]

lemma lessThan_0: "lessThan (0::nat) = {}"
apply (unfold lessThan_def)
apply (simp (no_asm))
done
declare lessThan_0 [simp]

lemma lessThan_Suc: "lessThan (Suc k) = insert k (lessThan k)"
apply (unfold lessThan_def)
apply (simp (no_asm) add: less_Suc_eq)
apply blast
done

lemma lessThan_Suc_atMost: "lessThan (Suc k) = atMost k"
apply (unfold lessThan_def atMost_def)
apply (simp (no_asm) add: less_Suc_eq_le)
done

lemma UN_lessThan_UNIV: "(UN m::nat. lessThan m) = UNIV"
apply blast
done

lemma Compl_lessThan: 
    "!!k:: 'a::linorder. -lessThan k = atLeast k"
apply (unfold lessThan_def atLeast_def)
apply auto
apply (blast intro: linorder_not_less [THEN iffD1])
apply (blast dest: order_le_less_trans)
done

lemma single_Diff_lessThan: "!!k:: 'a::order. {k} - lessThan k = {k}"
apply auto
done
declare single_Diff_lessThan [simp]

(*** greaterThan ***)

lemma greaterThan_iff: "(i: greaterThan k) = (k<i)"

apply (unfold greaterThan_def)
apply blast
done
declare greaterThan_iff [iff]

lemma greaterThan_0: "greaterThan 0 = range Suc"
apply (unfold greaterThan_def)
apply (blast dest: gr0_conv_Suc [THEN iffD1])
done
declare greaterThan_0 [simp]

lemma greaterThan_Suc: "greaterThan (Suc k) = greaterThan k - {Suc k}"
apply (unfold greaterThan_def)
apply (auto elim: linorder_neqE)
done

lemma INT_greaterThan_UNIV: "(INT m::nat. greaterThan m) = {}"
apply blast
done

lemma Compl_greaterThan: 
    "!!k:: 'a::linorder. -greaterThan k = atMost k"
apply (unfold greaterThan_def atMost_def le_def)
apply auto
apply (blast intro: linorder_not_less [THEN iffD1])
apply (blast dest: order_le_less_trans)
done

lemma Compl_atMost: "!!k:: 'a::linorder. -atMost k = greaterThan k"
apply (simp (no_asm) add: Compl_greaterThan [symmetric])
done

declare Compl_greaterThan [simp] Compl_atMost [simp]

(*** atLeast ***)

lemma atLeast_iff: "(i: atLeast k) = (k<=i)"

apply (unfold atLeast_def)
apply blast
done
declare atLeast_iff [iff]

lemma atLeast_0: "atLeast (0::nat) = UNIV"
apply (unfold atLeast_def UNIV_def)
apply (simp (no_asm))
done
declare atLeast_0 [simp]

lemma atLeast_Suc: "atLeast (Suc k) = atLeast k - {k}"
apply (unfold atLeast_def)
apply (simp (no_asm) add: Suc_le_eq)
apply (simp (no_asm) add: order_le_less)
apply blast
done

lemma UN_atLeast_UNIV: "(UN m::nat. atLeast m) = UNIV"
apply blast
done

lemma Compl_atLeast: 
    "!!k:: 'a::linorder. -atLeast k = lessThan k"
apply (unfold lessThan_def atLeast_def le_def)
apply auto
apply (blast intro: linorder_not_less [THEN iffD1])
apply (blast dest: order_le_less_trans)
done

declare Compl_lessThan [simp] Compl_atLeast [simp]

(*** atMost ***)

lemma atMost_iff: "(i: atMost k) = (i<=k)"

apply (unfold atMost_def)
apply blast
done
declare atMost_iff [iff]

lemma atMost_0: "atMost (0::nat) = {0}"
apply (unfold atMost_def)
apply (simp (no_asm))
done
declare atMost_0 [simp]

lemma atMost_Suc: "atMost (Suc k) = insert (Suc k) (atMost k)"
apply (unfold atMost_def)
apply (simp (no_asm) add: less_Suc_eq order_le_less)
apply blast
done

lemma UN_atMost_UNIV: "(UN m::nat. atMost m) = UNIV"
apply blast
done


(*** Combined properties ***)

lemma atMost_Int_atLeast: "!!n:: 'a::order. atMost n Int atLeast n = {n}"
apply (blast intro: order_antisym)
done

(*** Two-sided intervals ***)

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

(*** The following lemmas are useful with the summation operator setsum ***)
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
