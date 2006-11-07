(*  Title:      HOL/Orderings.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* Abstract orderings *}

theory Orderings
imports Code_Generator
begin

section {* Abstract orderings *}

subsection {* Order signatures *}

class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq  ("op \<^loc><=")
  less_eq  ("(_/ \<^loc><= _)" [50, 51] 50)
  less  ("op \<^loc><")
  less  ("(_/ \<^loc>< _)"  [50, 51] 50)

notation (xsymbols)
  less_eq  ("op \<^loc>\<le>")
  less_eq  ("(_/ \<^loc>\<le> _)"  [50, 51] 50)

notation (HTML output)
  less_eq  ("op \<^loc>\<le>")
  less_eq  ("(_/ \<^loc>\<le> _)"  [50, 51] 50)

abbreviation (input)
  greater  (infix "\<^loc>>" 50)
  "x \<^loc>> y \<equiv> y \<^loc>< x"
  greater_eq  (infix "\<^loc>>=" 50)
  "x \<^loc>>= y \<equiv> y \<^loc><= x"

notation (xsymbols)
  greater_eq  (infixl "\<^loc>\<ge>" 50)

end

notation
  less_eq  ("op <=")
  less_eq  ("(_/ <= _)" [50, 51] 50)
  less  ("op <")
  less  ("(_/ < _)"  [50, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>")
  less_eq  ("(_/ \<le> _)"  [50, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>")
  less_eq  ("(_/ \<le> _)"  [50, 51] 50)

abbreviation (input)
  greater  (infixl ">" 50)
  "x > y \<equiv> y < x"
  greater_eq  (infixl ">=" 50)
  "x >= y \<equiv> y <= x"
  
notation (xsymbols)
  greater_eq  (infixl "\<ge>" 50)


subsection {* Partial orderings *}

locale partial_order =
  fixes below :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
  assumes refl [iff]: "x \<sqsubseteq> x"
  and trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  and antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
  and less_le: "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

axclass order < ord
  order_refl [iff]: "x <= x"
  order_trans: "x <= y ==> y <= z ==> x <= z"
  order_antisym: "x <= y ==> y <= x ==> x = y"
  order_less_le: "(x < y) = (x <= y & x ~= y)"

interpretation order:
  partial_order ["op \<le> \<Colon> 'a\<Colon>order \<Rightarrow> 'a \<Rightarrow> bool" "op < \<Colon> 'a\<Colon>order \<Rightarrow> 'a \<Rightarrow> bool"]
apply(rule partial_order.intro)
apply(rule order_refl, erule (1) order_trans, erule (1) order_antisym, rule order_less_le)
done

text {* Reflexivity. *}

lemma order_eq_refl: "(x \<Colon> 'a\<Colon>order) = y \<Longrightarrow> x \<le> y"
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

lemma less_imp_neq: "[| (x::'a::order) < y |] ==> x ~= y"
  by (erule contrapos_pn, erule subst, rule order_less_irrefl)

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

lemma eq_neq_eq_imp_neq: "[| x = a ; a ~= b; b = y |] ==> x ~= y"
  by (erule subst, erule ssubst, assumption)

text {* Useful for simplification, but too risky to include by default. *}

lemma order_less_imp_not_less: "(x::'a::order) < y ==>  (~ y < x) = True"
  by (blast elim: order_less_asym)

lemma order_less_imp_triv: "(x::'a::order) < y ==>  (y < x --> P) = True"
  by (blast elim: order_less_asym)

lemma order_less_imp_not_eq: "(x::'a::order) < y ==>  (x = y) = False"
  by auto

lemma order_less_imp_not_eq2: "(x::'a::order) < y ==>  (y = x) = False"
  by auto

text {* Transitivity rules for calculational reasoning *}

lemma order_neq_le_trans: "a ~= b ==> (a::'a::order) <= b ==> a < b"
  by (simp add: order_less_le)

lemma order_le_neq_trans: "(a::'a::order) <= b ==> a ~= b ==> a < b"
  by (simp add: order_less_le)

lemma order_less_asym': "(a::'a::order) < b ==> b < a ==> P"
  by (rule order_less_asym)


subsection {* Linear (total) orderings *}

locale linear_order = partial_order +
  assumes linear: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

axclass linorder < order
  linorder_linear: "x <= y | y <= x"

interpretation linorder:
  linear_order ["op \<le> \<Colon> 'a\<Colon>linorder \<Rightarrow> 'a \<Rightarrow> bool" "op < \<Colon> 'a\<Colon>linorder \<Rightarrow> 'a \<Rightarrow> bool"]
  by unfold_locales (rule linorder_linear)

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


subsection {* Reasoning tools setup *}

ML {*
local

fun decomp_gen sort thy (Trueprop $ t) =
  let fun of_sort t = let val T = type_of t in
        (* exclude numeric types: linear arithmetic subsumes transitivity *)
        T <> HOLogic.natT andalso T <> HOLogic.intT andalso
        T <> HOLogic.realT andalso Sign.of_sort thy (T, sort) end
  fun dec (Const ("Not", _) $ t) = (
	  case dec t of
	    NONE => NONE
	  | SOME (t1, rel, t2) => SOME (t1, "~" ^ rel, t2))
	| dec (Const ("op =",  _) $ t1 $ t2) =
	    if of_sort t1
	    then SOME (t1, "=", t2)
	    else NONE
	| dec (Const ("Orderings.less_eq",  _) $ t1 $ t2) =
	    if of_sort t1
	    then SOME (t1, "<=", t2)
	    else NONE
	| dec (Const ("Orderings.less",  _) $ t1 $ t2) =
	    if of_sort t1
	    then SOME (t1, "<", t2)
	    else NONE
	| dec _ = NONE
  in dec t end;

in

structure Quasi_Tac = Quasi_Tac_Fun (
(* The setting up of Quasi_Tac serves as a demo.  Since there is no
   class for quasi orders, the tactics Quasi_Tac.trans_tac and
   Quasi_Tac.quasi_tac are not of much use. *)
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

  end);

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

  end);

end;
*}

setup {*
let

val order_antisym_conv = thm "order_antisym_conv"
val linorder_antisym_conv1 = thm "linorder_antisym_conv1"
val linorder_antisym_conv2 = thm "linorder_antisym_conv2"
val linorder_antisym_conv3 = thm "linorder_antisym_conv3"

fun prp t thm = (#prop (rep_thm thm) = t);

fun prove_antisym_le sg ss ((le as Const(_,T)) $ r $ s) =
  let val prems = prems_of_ss ss;
      val less = Const("Orderings.less",T);
      val t = HOLogic.mk_Trueprop(le $ s $ r);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(HOLogic.Not $ (less $ r $ s))
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq(thm RS linorder_antisym_conv1))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS order_antisym_conv))
  end
  handle THM _ => NONE;

fun prove_antisym_less sg ss (NotC $ ((less as Const(_,T)) $ r $ s)) =
  let val prems = prems_of_ss ss;
      val le = Const("Orderings.less_eq",T);
      val t = HOLogic.mk_Trueprop(le $ r $ s);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(NotC $ (less $ s $ r))
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq(thm RS linorder_antisym_conv3))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS linorder_antisym_conv2))
  end
  handle THM _ => NONE;

val antisym_le = Simplifier.simproc (the_context())
  "antisym le" ["(x::'a::order) <= y"] prove_antisym_le;
val antisym_less = Simplifier.simproc (the_context())
  "antisym less" ["~ (x::'a::linorder) < y"] prove_antisym_less;

in
  (fn thy => (Simplifier.change_simpset_of thy
    (fn ss => ss
       addsimprocs [antisym_le, antisym_less]
       addSolver (mk_solver "Trans_linear" (fn _ => Order_Tac.linear_tac))
       addSolver (mk_solver "Trans_partial" (fn _ => Order_Tac.partial_tac)))
       (* Adding the transitivity reasoners also as safe solvers showed a slight
          speed up, but the reasoning strength appears to be not higher (at least
          no breaking of additional proofs in the entire HOL distribution, as
          of 5 March 2004, was observed). *); thy))
end
*}


subsection {* Bounded quantifiers *}

syntax
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _>=_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3? _<=_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

translations
  "ALL x<y. P"   =>  "ALL x. x < y \<longrightarrow> P"
  "EX x<y. P"    =>  "EX x. x < y \<and> P"
  "ALL x<=y. P"  =>  "ALL x. x <= y \<longrightarrow> P"
  "EX x<=y. P"   =>  "EX x. x <= y \<and> P"
  "ALL x>y. P"   =>  "ALL x. x > y \<longrightarrow> P"
  "EX x>y. P"    =>  "EX x. x > y \<and> P"
  "ALL x>=y. P"  =>  "ALL x. x >= y \<longrightarrow> P"
  "EX x>=y. P"   =>  "EX x. x >= y \<and> P"

print_translation {*
let
  val syntax_name = Sign.const_syntax_name (the_context ());
  val impl = syntax_name "op -->";
  val conj = syntax_name "op &";
  val less = syntax_name "Orderings.less";
  val less_eq = syntax_name "Orderings.less_eq";

  val trans =
   [(("ALL ", impl, less), ("_All_less", "_All_greater")),
    (("ALL ", impl, less_eq), ("_All_less_eq", "_All_greater_eq")),
    (("EX ", conj, less), ("_Ex_less", "_Ex_greater")),
    (("EX ", conj, less_eq), ("_Ex_less_eq", "_Ex_greater_eq"))];

  fun mk v v' c n P =
    if v = v' andalso not (Term.exists_subterm (fn Free (x, _) => x = v | _ => false) n)
    then Syntax.const c $ Syntax.mark_bound v' $ n $ P else raise Match;

  fun tr' q = (q,
    fn [Const ("_bound", _) $ Free (v, _), Const (c, _) $ (Const (d, _) $ t $ u) $ P] =>
      (case AList.lookup (op =) trans (q, c, d) of
        NONE => raise Match
      | SOME (l, g) =>
          (case (t, u) of
            (Const ("_bound", _) $ Free (v', _), n) => mk v v' l n P
          | (n, Const ("_bound", _) $ Free (v', _)) => mk v v' g n P
          | _ => raise Match))
     | _ => raise Match);
in [tr' "ALL ", tr' "EX "] end
*}


subsection {* Transitivity reasoning on decreasing inequalities *}

(* FIXME cleanup *)

text {* These support proving chains of decreasing inequalities
    a >= b >= c ... in Isar proofs. *}

lemma xt1:
  "a = b ==> b > c ==> a > c"
  "a > b ==> b = c ==> a > c"
  "a = b ==> b >= c ==> a >= c"
  "a >= b ==> b = c ==> a >= c"
  "(x::'a::order) >= y ==> y >= x ==> x = y"
  "(x::'a::order) >= y ==> y >= z ==> x >= z"
  "(x::'a::order) > y ==> y >= z ==> x > z"
  "(x::'a::order) >= y ==> y > z ==> x > z"
  "(a::'a::order) > b ==> b > a ==> ?P"
  "(x::'a::order) > y ==> y > z ==> x > z"
  "(a::'a::order) >= b ==> a ~= b ==> a > b"
  "(a::'a::order) ~= b ==> a >= b ==> a > b"
  "a = f b ==> b > c ==> (!!x y. x > y ==> f x > f y) ==> a > f c" 
  "a > b ==> f b = c ==> (!!x y. x > y ==> f x > f y) ==> f a > c"
  "a = f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
  "a >= b ==> f b = c ==> (!! x y. x >= y ==> f x >= f y) ==> f a >= c"
by auto

lemma xt2:
  "(a::'a::order) >= f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt3: "(a::'a::order) >= b ==> (f b::'b::order) >= c ==> 
    (!!x y. x >= y ==> f x >= f y) ==> f a >= c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt4: "(a::'a::order) > f b ==> (b::'b::order) >= c ==>
  (!!x y. x >= y ==> f x >= f y) ==> a > f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt5: "(a::'a::order) > b ==> (f b::'b::order) >= c==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemma xt6: "(a::'a::order) >= f b ==> b > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt7: "(a::'a::order) >= b ==> (f b::'b::order) > c ==>
    (!!x y. x >= y ==> f x >= f y) ==> f a > c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt8: "(a::'a::order) > f b ==> (b::'b::order) > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt9: "(a::'a::order) > b ==> (f b::'b::order) > c ==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemmas xtrans = xt1 xt2 xt3 xt4 xt5 xt6 xt7 xt8 xt9

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

subsection {* Monotonicity, syntactic least value operator and syntactic min/max *}

locale mono =
  fixes f
  assumes mono: "A \<le> B \<Longrightarrow> f A \<le> f B"

lemmas monoI [intro?] = mono.intro
  and monoD [dest?] = mono.mono

constdefs
  Least :: "('a::ord => bool) => 'a"               (binder "LEAST " 10)
  "Least P == THE x. P x & (ALL y. P y --> x <= y)"
    -- {* We can no longer use LeastM because the latter requires Hilbert-AC. *}

constdefs
  min :: "['a::ord, 'a] => 'a"
  "min a b == (if a <= b then a else b)"
  max :: "['a::ord, 'a] => 'a"
  "max a b == (if a <= b then b else a)"

end
