(*  Title:      HOL/Orderings.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* Syntactic and abstract orders *}

theory Orderings
imports HOL
begin

section {* Abstract orders *}

subsection {* Order syntax *}

class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq  ("op \<^loc><=")
  less_eq  ("(_/ \<^loc><= _)" [51, 51] 50)
  less  ("op \<^loc><")
  less  ("(_/ \<^loc>< _)"  [51, 51] 50)

notation (xsymbols)
  less_eq  ("op \<^loc>\<le>")
  less_eq  ("(_/ \<^loc>\<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<^loc>\<le>")
  less_eq  ("(_/ \<^loc>\<le> _)"  [51, 51] 50)

abbreviation (input)
  greater  (infix "\<^loc>>" 50)
  "x \<^loc>> y \<equiv> y \<^loc>< x"
  greater_eq  (infix "\<^loc>>=" 50)
  "x \<^loc>>= y \<equiv> y \<^loc><= x"

notation (xsymbols)
  greater_eq  (infix "\<^loc>\<ge>" 50)

end

notation
  less_eq  ("op <=")
  less_eq  ("(_/ <= _)" [51, 51] 50)
  less  ("op <")
  less  ("(_/ < _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>")
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>")
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

abbreviation (input)
  greater  (infix ">" 50)
  "x > y \<equiv> y < x"
  greater_eq  (infix ">=" 50)
  "x >= y \<equiv> y <= x"
  
notation (xsymbols)
  greater_eq  (infix "\<ge>" 50)


subsection {* Quasiorders (preorders) *}

locale preorder =
  fixes below :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
  assumes refl [iff]: "x \<sqsubseteq> x"
  and trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  and less_le: "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
begin

abbreviation (input)
  greater_eq (infixl "\<sqsupseteq>" 50)
  "x \<sqsupseteq> y \<equiv> y \<sqsubseteq> x"

abbreviation (input)
  greater (infixl "\<sqsupset>" 50)
  "x \<sqsupset> y \<equiv> y \<sqsubset> x"

text {* Reflexivity. *}

lemma eq_refl: "x = y \<Longrightarrow> x \<sqsubseteq> y"
    -- {* This form is useful with the classical reasoner. *}
  by (erule ssubst) (rule refl)

lemma less_irrefl [iff]: "\<not> x \<sqsubset> x"
  by (simp add: less_le)

lemma le_less: "x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubset> y \<or> x = y"
    -- {* NOT suitable for iff, since it can cause PROOF FAILED. *}
  by (simp add: less_le) blast

lemma le_imp_less_or_eq: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubset> y \<or> x = y"
  unfolding less_le by blast

lemma less_imp_le: "x \<sqsubset> y \<Longrightarrow> x \<sqsubseteq> y"
  unfolding less_le by blast

lemma less_imp_neq: "x \<sqsubset> y \<Longrightarrow> x \<noteq> y"
  by (erule contrapos_pn, erule subst, rule less_irrefl)


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_eq: "x \<sqsubset> y \<Longrightarrow> (x = y) \<longleftrightarrow> False"
  by auto

lemma less_imp_not_eq2: "x \<sqsubset> y \<Longrightarrow> (y = x) \<longleftrightarrow> False"
  by auto


text {* Transitivity rules for calculational reasoning *}

lemma neq_le_trans: "\<lbrakk> a \<noteq> b; a \<sqsubseteq> b \<rbrakk> \<Longrightarrow> a \<sqsubset> b"
  by (simp add: less_le)

lemma le_neq_trans: "\<lbrakk> a \<sqsubseteq> b; a \<noteq> b \<rbrakk> \<Longrightarrow> a \<sqsubset> b"
  by (simp add: less_le)

end


subsection {* Partial orderings *}

locale partial_order = preorder + 
  assumes antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"

context partial_order
begin

text {* Asymmetry. *}

lemma less_not_sym: "x \<sqsubset> y \<Longrightarrow> \<not> (y \<sqsubset> x)"
  by (simp add: less_le antisym)

lemma less_asym: "x \<sqsubset> y \<Longrightarrow> (\<not> P \<Longrightarrow> y \<sqsubset> x) \<Longrightarrow> P"
  by (drule less_not_sym, erule contrapos_np) simp

lemma eq_iff: "x = y \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
  by (blast intro: antisym)

lemma antisym_conv: "y \<sqsubseteq> x \<Longrightarrow> x \<sqsubseteq> y \<longleftrightarrow> x = y"
  by (blast intro: antisym)

lemma less_imp_neq: "x \<sqsubset> y \<Longrightarrow> x \<noteq> y"
  by (erule contrapos_pn, erule subst, rule less_irrefl)


text {* Transitivity. *}

lemma less_trans: "\<lbrakk> x \<sqsubset> y; y \<sqsubset> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  by (simp add: less_le) (blast intro: trans antisym)

lemma le_less_trans: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubset> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  by (simp add: less_le) (blast intro: trans antisym)

lemma less_le_trans: "\<lbrakk> x \<sqsubset> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  by (simp add: less_le) (blast intro: trans antisym)


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_less: "x \<sqsubset> y \<Longrightarrow> (\<not> y \<sqsubset> x) \<longleftrightarrow> True"
  by (blast elim: less_asym)

lemma less_imp_triv: "x \<sqsubset> y \<Longrightarrow> (y \<sqsubset> x \<longrightarrow> P) \<longleftrightarrow> True"
  by (blast elim: less_asym)


text {* Transitivity rules for calculational reasoning *}

lemma less_asym': "\<lbrakk> a \<sqsubset> b; b \<sqsubset> a \<rbrakk> \<Longrightarrow> P"
  by (rule less_asym)

end

axclass order < ord
  order_refl [iff]: "x <= x"
  order_trans: "x <= y ==> y <= z ==> x <= z"
  order_antisym: "x <= y ==> y <= x ==> x = y"
  order_less_le: "(x < y) = (x <= y & x ~= y)"

interpretation order:
  partial_order ["op \<le> \<Colon> 'a\<Colon>order \<Rightarrow> 'a \<Rightarrow> bool" "op < \<Colon> 'a\<Colon>order \<Rightarrow> 'a \<Rightarrow> bool"]
apply unfold_locales
apply (rule order_refl)
apply (erule (1) order_trans)
apply (rule order_less_le)
apply (erule (1) order_antisym)
done


subsection {* Linear (total) orders *}

locale linorder = partial_order +
  assumes linear: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

context linorder
begin

lemma trichotomy: "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
  unfolding less_le using less_le linear by blast 

lemma le_less_linear: "x \<sqsubseteq> y \<or> y \<sqsubset> x"
  by (simp add: le_less trichotomy)

lemma le_cases [case_names le ge]:
  "\<lbrakk> x \<sqsubseteq> y \<Longrightarrow> P; y \<sqsubseteq> x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using linear by blast

lemma cases [case_names less equal greater]:
    "\<lbrakk> x \<sqsubset> y \<Longrightarrow> P; x = y \<Longrightarrow> P; y \<sqsubset> x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using trichotomy by blast

lemma not_less: "\<not> x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x"
  apply (simp add: less_le)
  using linear apply (blast intro: antisym)
  done

lemma not_le: "\<not> x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x"
  apply (simp add: less_le)
  using linear apply (blast intro: antisym)
  done

lemma neq_iff: "x \<noteq> y \<longleftrightarrow> x \<sqsubset> y \<or> y \<sqsubset> x"
  by (cut_tac x = x and y = y in trichotomy, auto)

lemma neqE: "\<lbrakk> x \<noteq> y; x \<sqsubset> y \<Longrightarrow> R; y \<sqsubset> x \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (simp add: neq_iff) blast

lemma antisym_conv1: "\<not> x \<sqsubset> y \<Longrightarrow> x \<sqsubseteq> y \<longleftrightarrow> x = y"
  by (blast intro: antisym dest: not_less [THEN iffD1])

lemma antisym_conv2: "x \<sqsubseteq> y \<Longrightarrow> \<not> x \<sqsubset> y \<longleftrightarrow> x = y"
  by (blast intro: antisym dest: not_less [THEN iffD1])

lemma antisym_conv3: "\<not> y \<sqsubset> x \<Longrightarrow> \<not> x \<sqsubset> y \<longleftrightarrow> x = y"
  by (blast intro: antisym dest: not_less [THEN iffD1])

text{*Replacing the old Nat.leI*}
lemma leI: "\<not> x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> x"
  unfolding not_less .

lemma leD: "y \<sqsubseteq> x \<Longrightarrow> \<not> x \<sqsubset> y"
  unfolding not_less .

(*FIXME inappropriate name (or delete altogether)*)
lemma not_leE: "\<not> y \<sqsubseteq> x \<Longrightarrow> x \<sqsubset> y"
  unfolding not_le .

end

axclass linorder < order
  linorder_linear: "x <= y | y <= x"

interpretation linorder:
  linorder ["op \<le> \<Colon> 'a\<Colon>linorder \<Rightarrow> 'a \<Rightarrow> bool" "op < \<Colon> 'a\<Colon>linorder \<Rightarrow> 'a \<Rightarrow> bool"]
  by unfold_locales (rule linorder_linear)


subsection {* Name duplicates *}

lemmas order_eq_refl [where 'b = "?'a::order"] = order.eq_refl
lemmas order_less_irrefl [where 'b = "?'a::order"] = order.less_irrefl
lemmas order_le_less [where 'b = "?'a::order"] = order.le_less
lemmas order_le_imp_less_or_eq [where 'b = "?'a::order"] = order.le_imp_less_or_eq
lemmas order_less_imp_le [where 'b = "?'a::order"] = order.less_imp_le
lemmas order_less_not_sym [where 'b = "?'a::order"] = order.less_not_sym
lemmas order_less_asym [where 'b = "?'a::order"] = order.less_asym
lemmas order_eq_iff [where 'b = "?'a::order"] = order.eq_iff
lemmas order_antisym_conv [where 'b = "?'a::order"] = order.antisym_conv
lemmas less_imp_neq [where 'b = "?'a::order"] = order.less_imp_neq
lemmas order_less_trans [where 'b = "?'a::order"] = order.less_trans
lemmas order_le_less_trans [where 'b = "?'a::order"] = order.le_less_trans
lemmas order_less_le_trans [where 'b = "?'a::order"] = order.less_le_trans
lemmas order_less_imp_not_less [where 'b = "?'a::order"] = order.less_imp_not_less
lemmas order_less_imp_triv [where 'b = "?'a::order"] = order.less_imp_triv
lemmas order_less_imp_not_eq [where 'b = "?'a::order"] = order.less_imp_not_eq
lemmas order_less_imp_not_eq2 [where 'b = "?'a::order"] = order.less_imp_not_eq2
lemmas order_neq_le_trans [where 'b = "?'a::order"] = order.neq_le_trans
lemmas order_le_neq_trans [where 'b = "?'a::order"] = order.le_neq_trans
lemmas order_less_asym' [where 'b = "?'a::order"] = order.less_asym'
lemmas linorder_less_linear [where 'b = "?'a::linorder"] = linorder.trichotomy
lemmas linorder_le_less_linear [where 'b = "?'a::linorder"] = linorder.le_less_linear
lemmas linorder_le_cases [where 'b = "?'a::linorder"] = linorder.le_cases
lemmas linorder_cases [where 'b = "?'a::linorder"] = linorder.cases
lemmas linorder_not_less [where 'b = "?'a::linorder"] = linorder.not_less
lemmas linorder_not_le [where 'b = "?'a::linorder"] = linorder.not_le
lemmas linorder_neq_iff [where 'b = "?'a::linorder"] = linorder.neq_iff
lemmas linorder_neqE [where 'b = "?'a::linorder"] = linorder.neqE
lemmas linorder_antisym_conv1 [where 'b = "?'a::linorder"] = linorder.antisym_conv1
lemmas linorder_antisym_conv2 [where 'b = "?'a::linorder"] = linorder.antisym_conv2
lemmas linorder_antisym_conv3 [where 'b = "?'a::linorder"] = linorder.antisym_conv3
lemmas leI [where 'b = "?'a::linorder"] = linorder.leI
lemmas leD [where 'b = "?'a::linorder"] = linorder.leD
lemmas not_leE [where 'b = "?'a::linorder"] = linorder.not_leE


subsection {* Reasoning tools setup *}

ML {*
local

fun decomp_gen sort thy (Trueprop $ t) =
  let
    fun of_sort t =
      let
        val T = type_of t
      in
        (* exclude numeric types: linear arithmetic subsumes transitivity *)
        T <> HOLogic.natT andalso T <> HOLogic.intT
          andalso T <> HOLogic.realT andalso Sign.of_sort thy (T, sort)
      end;
    fun dec (Const ("Not", _) $ t) = (case dec t
          of NONE => NONE
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
      | dec _ = NONE;
  in dec t end;

in

(* The setting up of Quasi_Tac serves as a demo.  Since there is no
   class for quasi orders, the tactics Quasi_Tac.trans_tac and
   Quasi_Tac.quasi_tac are not of much use. *)

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

fun add_simprocs procs thy =
  (Simplifier.change_simpset_of thy (fn ss => ss
    addsimprocs (map (fn (name, raw_ts, proc) =>
      Simplifier.simproc thy name raw_ts proc)) procs); thy);
fun add_solver name tac thy =
  (Simplifier.change_simpset_of thy (fn ss => ss addSolver
    (mk_solver name (K tac))); thy);

in
  add_simprocs [
       ("antisym le", ["(x::'a::order) <= y"], prove_antisym_le),
       ("antisym less", ["~ (x::'a::linorder) < y"], prove_antisym_less)
     ]
  #> add_solver "Trans_linear" Order_Tac.linear_tac
  #> add_solver "Trans_partial" Order_Tac.partial_tac
  (* Adding the transitivity reasoners also as safe solvers showed a slight
     speed up, but the reasoning strength appears to be not higher (at least
     no breaking of additional proofs in the entire HOL distribution, as
     of 5 March 2004, was observed). *)
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
