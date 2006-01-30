(*  Title:      HOL/Orderings.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson

FIXME: derive more of the min/max laws generically via semilattices
*)

header {* Type classes for $\le$ *}

theory Orderings
imports Lattice_Locales
uses ("antisym_setup.ML")
begin

subsection {* Order signatures and orders *}

axclass
  ord < type

syntax
  "op <"        :: "['a::ord, 'a] => bool"             ("op <")
  "op <="       :: "['a::ord, 'a] => bool"             ("op <=")

global

consts
  "op <"        :: "['a::ord, 'a] => bool"             ("(_/ < _)"  [50, 51] 50)
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ <= _)" [50, 51] 50)

local

syntax (xsymbols)
  "op <="       :: "['a::ord, 'a] => bool"             ("op \<le>")
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ \<le> _)"  [50, 51] 50)

syntax (HTML output)
  "op <="       :: "['a::ord, 'a] => bool"             ("op \<le>")
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ \<le> _)"  [50, 51] 50)

text{* Syntactic sugar: *}

syntax
  "_gt" :: "'a::ord => 'a => bool"             (infixl ">" 50)
  "_ge" :: "'a::ord => 'a => bool"             (infixl ">=" 50)
translations
  "x > y"  => "y < x"
  "x >= y" => "y <= x"

syntax (xsymbols)
  "_ge"       :: "'a::ord => 'a => bool"             (infixl "\<ge>" 50)

syntax (HTML output)
  "_ge"       :: "['a::ord, 'a] => bool"             (infixl "\<ge>" 50)


subsection {* Monotonicity *}

locale mono =
  fixes f
  assumes mono: "A <= B ==> f A <= f B"

lemmas monoI [intro?] = mono.intro
  and monoD [dest?] = mono.mono

constdefs
  min :: "['a::ord, 'a] => 'a"
  "min a b == (if a <= b then a else b)"
  max :: "['a::ord, 'a] => 'a"
  "max a b == (if a <= b then b else a)"

lemma min_leastL: "(!!x. least <= x) ==> min least x = least"
  by (simp add: min_def)

lemma min_of_mono:
    "ALL x y. (f x <= f y) = (x <= y) ==> min (f m) (f n) = f (min m n)"
  by (simp add: min_def)

lemma max_leastL: "(!!x. least <= x) ==> max least x = x"
  by (simp add: max_def)

lemma max_of_mono:
    "ALL x y. (f x <= f y) = (x <= y) ==> max (f m) (f n) = f (max m n)"
  by (simp add: max_def)


subsection "Orders"

axclass order < ord
  order_refl [iff]: "x <= x"
  order_trans: "x <= y ==> y <= z ==> x <= z"
  order_antisym: "x <= y ==> y <= x ==> x = y"
  order_less_le: "(x < y) = (x <= y & x ~= y)"

text{* Connection to locale: *}

interpretation order:
  partial_order["op \<le> :: 'a::order \<Rightarrow> 'a \<Rightarrow> bool"]
apply(rule partial_order.intro)
apply(rule order_refl, erule (1) order_trans, erule (1) order_antisym)
done

text {* Reflexivity. *}

lemma order_eq_refl: "!!x::'a::order. x = y ==> x <= y"
    -- {* This form is useful with the classical reasoner. *}
  apply (erule ssubst)
  apply (rule order_refl)
  done

lemma order_less_irrefl [iff]: "~ x < (x::'a::order)"
  by (simp add: order_less_le)

lemma order_le_less: "((x::'a::order) <= y) = (x < y | x = y)"
    -- {* NOT suitable for iff, since it can cause PROOF FAILED. *}
  apply (simp add: order_less_le, blast)
  done

lemmas order_le_imp_less_or_eq = order_le_less [THEN iffD1, standard]

lemma order_less_imp_le: "!!x::'a::order. x < y ==> x <= y"
  by (simp add: order_less_le)


text {* Asymmetry. *}

lemma order_less_not_sym: "(x::'a::order) < y ==> ~ (y < x)"
  by (simp add: order_less_le order_antisym)

lemma order_less_asym: "x < (y::'a::order) ==> (~P ==> y < x) ==> P"
  apply (drule order_less_not_sym)
  apply (erule contrapos_np, simp)
  done

lemma order_eq_iff: "!!x::'a::order. (x = y) = (x \<le> y & y \<le> x)"
by (blast intro: order_antisym)

lemma order_antisym_conv: "(y::'a::order) <= x ==> (x <= y) = (x = y)"
by(blast intro:order_antisym)

text {* Transitivity. *}

lemma order_less_trans: "!!x::'a::order. [| x < y; y < z |] ==> x < z"
  apply (simp add: order_less_le)
  apply (blast intro: order_trans order_antisym)
  done

lemma order_le_less_trans: "!!x::'a::order. [| x <= y; y < z |] ==> x < z"
  apply (simp add: order_less_le)
  apply (blast intro: order_trans order_antisym)
  done

lemma order_less_le_trans: "!!x::'a::order. [| x < y; y <= z |] ==> x < z"
  apply (simp add: order_less_le)
  apply (blast intro: order_trans order_antisym)
  done


text {* Useful for simplification, but too risky to include by default. *}

lemma order_less_imp_not_less: "(x::'a::order) < y ==>  (~ y < x) = True"
  by (blast elim: order_less_asym)

lemma order_less_imp_triv: "(x::'a::order) < y ==>  (y < x --> P) = True"
  by (blast elim: order_less_asym)

lemma order_less_imp_not_eq: "(x::'a::order) < y ==>  (x = y) = False"
  by auto

lemma order_less_imp_not_eq2: "(x::'a::order) < y ==>  (y = x) = False"
  by auto


text {* Other operators. *}

lemma min_leastR: "(!!x::'a::order. least <= x) ==> min x least = least"
  apply (simp add: min_def)
  apply (blast intro: order_antisym)
  done

lemma max_leastR: "(!!x::'a::order. least <= x) ==> max x least = x"
  apply (simp add: max_def)
  apply (blast intro: order_antisym)
  done


subsection {* Transitivity rules for calculational reasoning *}


lemma order_neq_le_trans: "a ~= b ==> (a::'a::order) <= b ==> a < b"
  by (simp add: order_less_le)

lemma order_le_neq_trans: "(a::'a::order) <= b ==> a ~= b ==> a < b"
  by (simp add: order_less_le)

lemma order_less_asym': "(a::'a::order) < b ==> b < a ==> P"
  by (rule order_less_asym)


subsection {* Least value operator *}

constdefs
  Least :: "('a::ord => bool) => 'a"               (binder "LEAST " 10)
  "Least P == THE x. P x & (ALL y. P y --> x <= y)"
    -- {* We can no longer use LeastM because the latter requires Hilbert-AC. *}

lemma LeastI2_order:
  "[| P (x::'a::order);
      !!y. P y ==> x <= y;
      !!x. [| P x; ALL y. P y --> x \<le> y |] ==> Q x |]
   ==> Q (Least P)"
  apply (unfold Least_def)
  apply (rule theI2)
    apply (blast intro: order_antisym)+
  done

lemma Least_equality:
    "[| P (k::'a::order); !!x. P x ==> k <= x |] ==> (LEAST x. P x) = k"
  apply (simp add: Least_def)
  apply (rule the_equality)
  apply (auto intro!: order_antisym)
  done


subsection "Linear / total orders"

axclass linorder < order
  linorder_linear: "x <= y | y <= x"

lemma linorder_less_linear: "!!x::'a::linorder. x<y | x=y | y<x"
  apply (simp add: order_less_le)
  apply (insert linorder_linear, blast)
  done

lemma linorder_le_less_linear: "!!x::'a::linorder. x\<le>y | y<x"
  by (simp add: order_le_less linorder_less_linear)

lemma linorder_le_cases [case_names le ge]:
    "((x::'a::linorder) \<le> y ==> P) ==> (y \<le> x ==> P) ==> P"
  by (insert linorder_linear, blast)

lemma linorder_cases [case_names less equal greater]:
    "((x::'a::linorder) < y ==> P) ==> (x = y ==> P) ==> (y < x ==> P) ==> P"
  by (insert linorder_less_linear, blast)

lemma linorder_not_less: "!!x::'a::linorder. (~ x < y) = (y <= x)"
  apply (simp add: order_less_le)
  apply (insert linorder_linear)
  apply (blast intro: order_antisym)
  done

lemma linorder_not_le: "!!x::'a::linorder. (~ x <= y) = (y < x)"
  apply (simp add: order_less_le)
  apply (insert linorder_linear)
  apply (blast intro: order_antisym)
  done

lemma linorder_neq_iff: "!!x::'a::linorder. (x ~= y) = (x<y | y<x)"
by (cut_tac x = x and y = y in linorder_less_linear, auto)

lemma linorder_neqE: "x ~= (y::'a::linorder) ==> (x < y ==> R) ==> (y < x ==> R) ==> R"
by (simp add: linorder_neq_iff, blast)

lemma linorder_antisym_conv1: "~ (x::'a::linorder) < y ==> (x <= y) = (x = y)"
by(blast intro:order_antisym dest:linorder_not_less[THEN iffD1])

lemma linorder_antisym_conv2: "(x::'a::linorder) <= y ==> (~ x < y) = (x = y)"
by(blast intro:order_antisym dest:linorder_not_less[THEN iffD1])

lemma linorder_antisym_conv3: "~ (y::'a::linorder) < x ==> (~ x < y) = (x = y)"
by(blast intro:order_antisym dest:linorder_not_less[THEN iffD1])

text{*Replacing the old Nat.leI*}
lemma leI: "~ x < y ==> y <= (x::'a::linorder)"
  by (simp only: linorder_not_less)

lemma leD: "y <= (x::'a::linorder) ==> ~ x < y"
  by (simp only: linorder_not_less)

(*FIXME inappropriate name (or delete altogether)*)
lemma not_leE: "~ y <= (x::'a::linorder) ==> x < y"
  by (simp only: linorder_not_le)

use "antisym_setup.ML";
setup antisym_setup

subsection {* Setup of transitivity reasoner as Solver *}

lemma less_imp_neq: "[| (x::'a::order) < y |] ==> x ~= y"
  by (erule contrapos_pn, erule subst, rule order_less_irrefl)

lemma eq_neq_eq_imp_neq: "[| x = a ; a ~= b; b = y |] ==> x ~= y"
  by (erule subst, erule ssubst, assumption)

ML_setup {*

(* The setting up of Quasi_Tac serves as a demo.  Since there is no
   class for quasi orders, the tactics Quasi_Tac.trans_tac and
   Quasi_Tac.quasi_tac are not of much use. *)

fun decomp_gen sort sign (Trueprop $ t) =
  let fun of_sort t = let val T = type_of t in
        (* exclude numeric types: linear arithmetic subsumes transitivity *)
        T <> HOLogic.natT andalso T <> HOLogic.intT andalso
        T <> HOLogic.realT andalso Sign.of_sort sign (T, sort) end
  fun dec (Const ("Not", _) $ t) = (
	  case dec t of
	    NONE => NONE
	  | SOME (t1, rel, t2) => SOME (t1, "~" ^ rel, t2))
	| dec (Const ("op =",  _) $ t1 $ t2) =
	    if of_sort t1
	    then SOME (t1, "=", t2)
	    else NONE
	| dec (Const ("op <=",  _) $ t1 $ t2) =
	    if of_sort t1
	    then SOME (t1, "<=", t2)
	    else NONE
	| dec (Const ("op <",  _) $ t1 $ t2) =
	    if of_sort t1
	    then SOME (t1, "<", t2)
	    else NONE
	| dec _ = NONE
  in dec t end;

structure Quasi_Tac = Quasi_Tac_Fun (
  struct
    val le_trans = thm "order_trans";
    val le_refl = thm "order_refl";
    val eqD1 = thm "order_eq_refl";
    val eqD2 = thm "sym" RS thm "order_eq_refl";
    val less_reflE = thm "order_less_irrefl" RS thm "notE";
    val less_imp_le = thm "order_less_imp_le";
    val le_neq_trans = thm "order_le_neq_trans";
    val neq_le_trans = thm "order_neq_le_trans";
    val less_imp_neq = thm "less_imp_neq";
    val decomp_trans = decomp_gen ["Orderings.order"];
    val decomp_quasi = decomp_gen ["Orderings.order"];

  end);  (* struct *)

structure Order_Tac = Order_Tac_Fun (
  struct
    val less_reflE = thm "order_less_irrefl" RS thm "notE";
    val le_refl = thm "order_refl";
    val less_imp_le = thm "order_less_imp_le";
    val not_lessI = thm "linorder_not_less" RS thm "iffD2";
    val not_leI = thm "linorder_not_le" RS thm "iffD2";
    val not_lessD = thm "linorder_not_less" RS thm "iffD1";
    val not_leD = thm "linorder_not_le" RS thm "iffD1";
    val eqI = thm "order_antisym";
    val eqD1 = thm "order_eq_refl";
    val eqD2 = thm "sym" RS thm "order_eq_refl";
    val less_trans = thm "order_less_trans";
    val less_le_trans = thm "order_less_le_trans";
    val le_less_trans = thm "order_le_less_trans";
    val le_trans = thm "order_trans";
    val le_neq_trans = thm "order_le_neq_trans";
    val neq_le_trans = thm "order_neq_le_trans";
    val less_imp_neq = thm "less_imp_neq";
    val eq_neq_eq_imp_neq = thm "eq_neq_eq_imp_neq";
    val not_sym = thm "not_sym";
    val decomp_part = decomp_gen ["Orderings.order"];
    val decomp_lin = decomp_gen ["Orderings.linorder"];

  end);  (* struct *)

change_simpset (fn ss => ss
    addSolver (mk_solver "Trans_linear" (fn _ => Order_Tac.linear_tac))
    addSolver (mk_solver "Trans_partial" (fn _ => Order_Tac.partial_tac)));
  (* Adding the transitivity reasoners also as safe solvers showed a slight
     speed up, but the reasoning strength appears to be not higher (at least
     no breaking of additional proofs in the entire HOL distribution, as
     of 5 March 2004, was observed). *)
*}

(* Optional setup of methods *)

(*
method_setup trans_partial =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (Order_Tac.partial_tac)) *}
  {* transitivity reasoner for partial orders *}	
method_setup trans_linear =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (Order_Tac.linear_tac)) *}
  {* transitivity reasoner for linear orders *}
*)

(*
declare order.order_refl [simp del] order_less_irrefl [simp del]

can currently not be removed, abel_cancel relies on it.
*)


subsection "Min and max on (linear) orders"

text{* Instantiate locales: *}

interpretation min_max:
  lower_semilattice["op \<le>" "min :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"]
apply(rule lower_semilattice_axioms.intro)
apply(simp add:min_def linorder_not_le order_less_imp_le)
apply(simp add:min_def linorder_not_le order_less_imp_le)
apply(simp add:min_def linorder_not_le order_less_imp_le)
done

interpretation min_max:
  upper_semilattice["op \<le>" "max :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"]
apply -
apply(rule upper_semilattice_axioms.intro)
apply(simp add: max_def linorder_not_le order_less_imp_le)
apply(simp add: max_def linorder_not_le order_less_imp_le)
apply(simp add: max_def linorder_not_le order_less_imp_le)
done

interpretation min_max:
  lattice["op \<le>" "min :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "max"]
.

interpretation min_max:
  distrib_lattice["op \<le>" "min :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "max"]
apply(rule distrib_lattice_axioms.intro)
apply(rule_tac x=x and y=y in linorder_le_cases)
apply(rule_tac x=x and y=z in linorder_le_cases)
apply(rule_tac x=y and y=z in linorder_le_cases)
apply(simp add:min_def max_def)
apply(simp add:min_def max_def)
apply(rule_tac x=y and y=z in linorder_le_cases)
apply(simp add:min_def max_def)
apply(simp add:min_def max_def)
apply(rule_tac x=x and y=z in linorder_le_cases)
apply(rule_tac x=y and y=z in linorder_le_cases)
apply(simp add:min_def max_def)
apply(simp add:min_def max_def)
apply(rule_tac x=y and y=z in linorder_le_cases)
apply(simp add:min_def max_def)
apply(simp add:min_def max_def)
done

lemma le_max_iff_disj: "!!z::'a::linorder. (z <= max x y) = (z <= x | z <= y)"
  apply(simp add:max_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2

lemma less_max_iff_disj: "!!z::'a::linorder. (z < max x y) = (z < x | z < y)"
  apply (simp add: max_def order_le_less)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma max_less_iff_conj [simp]:
    "!!z::'a::linorder. (max x y < z) = (x < z & y < z)"
  apply (simp add: order_le_less max_def)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma min_less_iff_conj [simp]:
    "!!z::'a::linorder. (z < min x y) = (z < x & z < y)"
  apply (simp add: order_le_less min_def)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma min_le_iff_disj: "!!z::'a::linorder. (min x y <= z) = (x <= z | y <= z)"
  apply (simp add: min_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma min_less_iff_disj: "!!z::'a::linorder. (min x y < z) = (x < z | y < z)"
  apply (simp add: min_def order_le_less)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemmas max_ac = min_max.sup_assoc min_max.sup_commute
               mk_left_commute[of max,OF min_max.sup_assoc min_max.sup_commute]

lemmas min_ac = min_max.inf_assoc min_max.inf_commute
               mk_left_commute[of min,OF min_max.inf_assoc min_max.inf_commute]

lemma split_min:
    "P (min (i::'a::linorder) j) = ((i <= j --> P(i)) & (~ i <= j --> P(j)))"
  by (simp add: min_def)

lemma split_max:
    "P (max (i::'a::linorder) j) = ((i <= j --> P(j)) & (~ i <= j --> P(i)))"
  by (simp add: max_def)


subsection "Bounded quantifiers"

syntax
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_gtAll" :: "[idt, 'a, bool] => bool"   ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_gtEx"  :: "[idt, 'a, bool] => bool"   ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_geAll"   :: "[idt, 'a, bool] => bool"   ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_geEx"    :: "[idt, 'a, bool] => bool"   ("(3EX _>=_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_gtAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_gtEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_geAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_geEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3? _<=_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_gtAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_gtEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_geAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_geEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

translations
 "ALL x<y. P"   =>  "ALL x. x < y --> P"
 "EX x<y. P"    =>  "EX x. x < y  & P"
 "ALL x<=y. P"  =>  "ALL x. x <= y --> P"
 "EX x<=y. P"   =>  "EX x. x <= y & P"
 "ALL x>y. P"   =>  "ALL x. x > y --> P"
 "EX x>y. P"    =>  "EX x. x > y  & P"
 "ALL x>=y. P"  =>  "ALL x. x >= y --> P"
 "EX x>=y. P"   =>  "EX x. x >= y & P"

print_translation {*
let
  fun mk v v' q n P =
    if v=v' andalso not (v mem (map fst (Term.add_frees n [])))
    then Syntax.const q $ Syntax.mark_bound v' $ n $ P else raise Match;
  fun all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_lessAll" n P

  | all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <=",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_leAll" n P

  | all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_gtAll" n P

  | all_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op -->",_) $ (Const ("op <=",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_geAll" n P;

  fun ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_lessEx" n P

  | ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <=",_) $ (Const ("_bound",_) $ Free (v',_)) $ n ) $ P] =
    mk v v' "_leEx" n P

  | ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_gtEx" n P

  | ex_tr' [Const ("_bound",_) $ Free (v,_),
               Const("op &",_) $ (Const ("op <=",_) $ n $ (Const ("_bound",_) $ Free (v',_))) $ P] =
    mk v v' "_geEx" n P
in
[("ALL ", all_tr'), ("EX ", ex_tr')]
end
*}

subsection {* Extra transitivity rules *}

text {* These support proving chains of decreasing inequalities
    a >= b >= c ... in Isar proofs. *}

lemma xt1: "a = b ==> b > c ==> a > c"
by simp

lemma xt2: "a > b ==> b = c ==> a > c"
by simp

lemma xt3: "a = b ==> b >= c ==> a >= c"
by simp

lemma xt4: "a >= b ==> b = c ==> a >= c"
by simp

lemma xt5: "(x::'a::order) >= y ==> y >= x ==> x = y"
by simp

lemma xt6: "(x::'a::order) >= y ==> y >= z ==> x >= z"
by simp

lemma xt7: "(x::'a::order) > y ==> y >= z ==> x > z"
by simp

lemma xt8: "(x::'a::order) >= y ==> y > z ==> x > z"
by simp

lemma xt9: "(a::'a::order) > b ==> b > a ==> ?P"
by simp

lemma xt10: "(x::'a::order) > y ==> y > z ==> x > z"
by simp

lemma xt11: "(a::'a::order) >= b ==> a ~= b ==> a > b"
by simp

lemma xt12: "(a::'a::order) ~= b ==> a >= b ==> a > b"
by simp

lemma xt13: "a = f b ==> b > c ==> (!!x y. x > y ==> f x > f y) ==>
    a > f c" 
by simp

lemma xt14: "a > b ==> f b = c ==> (!!x y. x > y ==> f x > f y) ==>
    f a > c"
by auto

lemma xt15: "a = f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==>
    a >= f c"
by simp

lemma xt16: "a >= b ==> f b = c ==> (!! x y. x >= y ==> f x >= f y) ==>
    f a >= c"
by auto

lemma xt17: "(a::'a::order) >= f b ==> b >= c ==> 
    (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt18: "(a::'a::order) >= b ==> (f b::'b::order) >= c ==> 
    (!!x y. x >= y ==> f x >= f y) ==> f a >= c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt19: "(a::'a::order) > f b ==> (b::'b::order) >= c ==>
  (!!x y. x >= y ==> f x >= f y) ==> a > f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt20: "(a::'a::order) > b ==> (f b::'b::order) >= c==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemma xt21: "(a::'a::order) >= f b ==> b > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt22: "(a::'a::order) >= b ==> (f b::'b::order) > c ==>
    (!!x y. x >= y ==> f x >= f y) ==> f a > c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt23: "(a::'a::order) > f b ==> (b::'b::order) > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt24: "(a::'a::order) > b ==> (f b::'b::order) > c ==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)


lemmas xtrans = xt1 xt2 xt3 xt4 xt5 xt6 xt7 xt8 xt9 xt10 xt11 xt12
    xt13 xt14 xt15 xt15 xt17 xt18 xt19 xt20 xt21 xt22 xt23 xt24

(* 
  Since "a >= b" abbreviates "b <= a", the abbreviation "..." stands
  for the wrong thing in an Isar proof.

  The extra transitivity rules can be used as follows: 

lemma "(a::'a::order) > z"
proof -
  have "a >= b" (is "_ >= ?rhs")
    sorry
  also have "?rhs >= c" (is "_ >= ?rhs")
    sorry
  also (xtrans) have "?rhs = d" (is "_ = ?rhs")
    sorry
  also (xtrans) have "?rhs >= e" (is "_ >= ?rhs")
    sorry
  also (xtrans) have "?rhs > f" (is "_ > ?rhs")
    sorry
  also (xtrans) have "?rhs > z"
    sorry
  finally (xtrans) show ?thesis .
qed

  Alternatively, one can use "declare xtrans [trans]" and then
  leave out the "(xtrans)" above.
*)

subsection {* Code generator setup *}

code_alias
  "op <=" "IntDef.op_le"
  "op <" "IntDef.op_lt"

end
