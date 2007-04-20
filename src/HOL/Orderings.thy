(*  Title:      HOL/Orderings.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* Syntactic and abstract orders *}

theory Orderings
imports HOL
begin

subsection {* Order syntax *}

class ord = type +
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<sqsubseteq>" 50)
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<sqsubset>" 50)
begin

notation
  less_eq  ("op \<^loc><=") and
  less_eq  ("(_/ \<^loc><= _)" [51, 51] 50) and
  less  ("op \<^loc><") and
  less  ("(_/ \<^loc>< _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<^loc>\<le>") and
  less_eq  ("(_/ \<^loc>\<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<^loc>\<le>") and
  less_eq  ("(_/ \<^loc>\<le> _)"  [51, 51] 50)

abbreviation (input)
  greater  (infix "\<^loc>>" 50) where
  "x \<^loc>> y \<equiv> y \<^loc>< x"

abbreviation (input)
  greater_eq  (infix "\<^loc>>=" 50) where
  "x \<^loc>>= y \<equiv> y \<^loc><= x"

notation (input)
  greater_eq  (infix "\<^loc>\<ge>" 50)

text {*
  syntactic min/max -- these definitions reach
  their usual semantics in class linorder ahead.
*}

definition
  min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min a b = (if a \<sqsubseteq> b then a else b)"

definition
  max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max a b = (if a \<sqsubseteq> b then b else a)"

end

notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

abbreviation (input)
  greater  (infix ">" 50) where
  "x > y \<equiv> y < x"

abbreviation (input)
  greater_eq  (infix ">=" 50) where
  "x >= y \<equiv> y <= x"

notation (input)
  greater_eq  (infix "\<ge>" 50)

definition
  min :: "'a\<Colon>ord \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min a b = (if a \<le> b then a else b)"

definition
  max :: "'a\<Colon>ord \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max a b = (if a \<le> b then b else a)"

lemma min_linorder:
  "ord.min (op \<le> \<Colon> 'a\<Colon>ord \<Rightarrow> 'a \<Rightarrow> bool) = min"
  by rule+ (simp add: min_def ord_class.min_def)

lemma max_linorder:
  "ord.max (op \<le> \<Colon> 'a\<Colon>ord \<Rightarrow> 'a \<Rightarrow> bool) = max"
  by rule+ (simp add: max_def ord_class.max_def)


subsection {* Quasiorders (preorders) *}

class preorder = ord +
  assumes less_le: "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
  and order_refl [iff]: "x \<sqsubseteq> x"
  and order_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
begin

text {* Reflexivity. *}

lemma eq_refl: "x = y \<Longrightarrow> x \<sqsubseteq> y"
    -- {* This form is useful with the classical reasoner. *}
  by (erule ssubst) (rule order_refl)

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

class order = preorder + 
  assumes antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
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
  by (simp add: less_le) (blast intro: order_trans antisym)

lemma le_less_trans: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubset> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  by (simp add: less_le) (blast intro: order_trans antisym)

lemma less_le_trans: "\<lbrakk> x \<sqsubset> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  by (simp add: less_le) (blast intro: order_trans antisym)


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_less: "x \<sqsubset> y \<Longrightarrow> (\<not> y \<sqsubset> x) \<longleftrightarrow> True"
  by (blast elim: less_asym)

lemma less_imp_triv: "x \<sqsubset> y \<Longrightarrow> (y \<sqsubset> x \<longrightarrow> P) \<longleftrightarrow> True"
  by (blast elim: less_asym)


text {* Transitivity rules for calculational reasoning *}

lemma less_asym': "\<lbrakk> a \<sqsubset> b; b \<sqsubset> a \<rbrakk> \<Longrightarrow> P"
  by (rule less_asym)

end


subsection {* Linear (total) orders *}

class linorder = order +
  assumes linear: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
begin

lemma less_linear: "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
  unfolding less_le using less_le linear by blast 

lemma le_less_linear: "x \<sqsubseteq> y \<or> y \<sqsubset> x"
  by (simp add: le_less less_linear)

lemma le_cases [case_names le ge]:
  "\<lbrakk> x \<sqsubseteq> y \<Longrightarrow> P; y \<sqsubseteq> x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using linear by blast

lemma linorder_cases [case_names less equal greater]:
    "\<lbrakk> x \<sqsubset> y \<Longrightarrow> P; x = y \<Longrightarrow> P; y \<sqsubset> x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using less_linear by blast

lemma not_less: "\<not> x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x"
  apply (simp add: less_le)
  using linear apply (blast intro: antisym)
  done

lemma not_le: "\<not> x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x"
  apply (simp add: less_le)
  using linear apply (blast intro: antisym)
  done

lemma neq_iff: "x \<noteq> y \<longleftrightarrow> x \<sqsubset> y \<or> y \<sqsubset> x"
  by (cut_tac x = x and y = y in less_linear, auto)

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

text {* min/max properties *}

lemma min_le_iff_disj:
  "min x y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<or> y \<sqsubseteq> z"
  unfolding min_def using linear by (auto intro: order_trans)

lemma le_max_iff_disj:
  "z \<sqsubseteq> max x y \<longleftrightarrow> z \<sqsubseteq> x \<or> z \<sqsubseteq> y"
  unfolding max_def using linear by (auto intro: order_trans)

lemma min_less_iff_disj:
  "min x y \<sqsubset> z \<longleftrightarrow> x \<sqsubset> z \<or> y \<sqsubset> z"
  unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma less_max_iff_disj:
  "z \<sqsubset> max x y \<longleftrightarrow> z \<sqsubset> x \<or> z \<sqsubset> y"
  unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma min_less_iff_conj [simp]:
  "z \<sqsubset> min x y \<longleftrightarrow> z \<sqsubset> x \<and> z \<sqsubset> y"
  unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma max_less_iff_conj [simp]:
  "max x y \<sqsubset> z \<longleftrightarrow> x \<sqsubset> z \<and> y \<sqsubset> z"
  unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma split_min:
  "P (min i j) \<longleftrightarrow> (i \<sqsubseteq> j \<longrightarrow> P i) \<and> (\<not> i \<sqsubseteq> j \<longrightarrow> P j)"
  by (simp add: min_def)

lemma split_max:
  "P (max i j) \<longleftrightarrow> (i \<sqsubseteq> j \<longrightarrow> P j) \<and> (\<not> i \<sqsubseteq> j \<longrightarrow> P i)"
  by (simp add: max_def)

end


subsection {* Name duplicates *}

lemmas order_less_le = less_le
lemmas order_eq_refl = preorder_class.eq_refl
lemmas order_less_irrefl = preorder_class.less_irrefl
lemmas order_le_less = preorder_class.le_less
lemmas order_le_imp_less_or_eq = preorder_class.le_imp_less_or_eq
lemmas order_less_imp_le = preorder_class.less_imp_le
lemmas order_less_imp_not_eq = preorder_class.less_imp_not_eq
lemmas order_less_imp_not_eq2 = preorder_class.less_imp_not_eq2
lemmas order_neq_le_trans = preorder_class.neq_le_trans
lemmas order_le_neq_trans = preorder_class.le_neq_trans

lemmas order_antisym = antisym
lemmas order_less_not_sym = order_class.less_not_sym
lemmas order_less_asym = order_class.less_asym
lemmas order_eq_iff = order_class.eq_iff
lemmas order_antisym_conv = order_class.antisym_conv
lemmas less_imp_neq = order_class.less_imp_neq
lemmas order_less_trans = order_class.less_trans
lemmas order_le_less_trans = order_class.le_less_trans
lemmas order_less_le_trans = order_class.less_le_trans
lemmas order_less_imp_not_less = order_class.less_imp_not_less
lemmas order_less_imp_triv = order_class.less_imp_triv
lemmas order_less_asym' = order_class.less_asym'

lemmas linorder_linear = linear
lemmas linorder_less_linear = linorder_class.less_linear
lemmas linorder_le_less_linear = linorder_class.le_less_linear
lemmas linorder_le_cases = linorder_class.le_cases
lemmas linorder_not_less = linorder_class.not_less
lemmas linorder_not_le = linorder_class.not_le
lemmas linorder_neq_iff = linorder_class.neq_iff
lemmas linorder_neqE = linorder_class.neqE
lemmas linorder_antisym_conv1 = linorder_class.antisym_conv1
lemmas linorder_antisym_conv2 = linorder_class.antisym_conv2
lemmas linorder_antisym_conv3 = linorder_class.antisym_conv3
lemmas leI = linorder_class.leI
lemmas leD = linorder_class.leD
lemmas not_leE = linorder_class.not_leE


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
  val decomp_trans = decomp_gen ["Orderings.preorder"];
  val decomp_quasi = decomp_gen ["Orderings.preorder"];
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
            | SOME thm => SOME(mk_meta_eq(thm RS @{thm linorder_antisym_conv1}))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS @{thm order_antisym_conv}))
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
            | SOME thm => SOME(mk_meta_eq(thm RS @{thm linorder_antisym_conv3}))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS @{thm linorder_antisym_conv2}))
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
  val All_binder = Syntax.binder_name @{const_syntax "All"};
  val Ex_binder = Syntax.binder_name @{const_syntax "Ex"};
  val impl = @{const_syntax "op -->"};
  val conj = @{const_syntax "op &"};
  val less = @{const_syntax "less"};
  val less_eq = @{const_syntax "less_eq"};

  val trans =
   [((All_binder, impl, less), ("_All_less", "_All_greater")),
    ((All_binder, impl, less_eq), ("_All_less_eq", "_All_greater_eq")),
    ((Ex_binder, conj, less), ("_Ex_less", "_Ex_greater")),
    ((Ex_binder, conj, less_eq), ("_Ex_less_eq", "_Ex_greater_eq"))];

  fun matches_bound v t = 
     case t of (Const ("_bound", _) $ Free (v', _)) => (v = v')
              | _ => false
  fun contains_var v = Term.exists_subterm (fn Free (x, _) => x = v | _ => false)
  fun mk v c n P = Syntax.const c $ Syntax.mark_bound v $ n $ P

  fun tr' q = (q,
    fn [Const ("_bound", _) $ Free (v, _), Const (c, _) $ (Const (d, _) $ t $ u) $ P] =>
      (case AList.lookup (op =) trans (q, c, d) of
        NONE => raise Match
      | SOME (l, g) =>
          if matches_bound v t andalso not (contains_var v u) then mk v l u P
          else if matches_bound v u andalso not (contains_var v t) then mk v g t P
          else raise Match)
     | _ => raise Match);
in [tr' All_binder, tr' Ex_binder] end
*}


subsection {* Transitivity reasoning *}

lemma ord_le_eq_trans: "a <= b ==> b = c ==> a <= c"
  by (rule subst)

lemma ord_eq_le_trans: "a = b ==> b <= c ==> a <= c"
  by (rule ssubst)

lemma ord_less_eq_trans: "a < b ==> b = c ==> a < c"
  by (rule subst)

lemma ord_eq_less_trans: "a = b ==> b < c ==> a < c"
  by (rule ssubst)

lemma order_less_subst2: "(a::'a::order) < b ==> f b < (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b < c"
  finally (order_less_trans) show ?thesis .
qed

lemma order_less_subst1: "(a::'a::order) < f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_less_trans) show ?thesis .
qed

lemma order_le_less_subst2: "(a::'a::order) <= b ==> f b < (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a < c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b < c"
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_le_less_subst1: "(a::'a::order) <= f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a <= f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_less_le_subst2: "(a::'a::order) < b ==> f b <= (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b <= c"
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_less_le_subst1: "(a::'a::order) < f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a < f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a < f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_subst1: "(a::'a::order) <= f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_trans) show ?thesis .
qed

lemma order_subst2: "(a::'a::order) <= b ==> f b <= (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b <= c"
  finally (order_trans) show ?thesis .
qed

lemma ord_le_eq_subst: "a <= b ==> f b = c ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b = c"
  finally (ord_le_eq_trans) show ?thesis .
qed

lemma ord_eq_le_subst: "a = f b ==> b <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a = f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (ord_eq_le_trans) show ?thesis .
qed

lemma ord_less_eq_subst: "a < b ==> f b = c ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b = c"
  finally (ord_less_eq_trans) show ?thesis .
qed

lemma ord_eq_less_subst: "a = f b ==> b < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a = f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (ord_eq_less_trans) show ?thesis .
qed

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas order_trans_rules [trans] =
  order_less_subst2
  order_less_subst1
  order_le_less_subst2
  order_le_less_subst1
  order_less_le_subst2
  order_less_le_subst1
  order_subst2
  order_subst1
  ord_le_eq_subst
  ord_eq_le_subst
  ord_less_eq_subst
  ord_eq_less_subst
  forw_subst
  back_subst
  rev_mp
  mp
  order_neq_le_trans
  order_le_neq_trans
  order_less_trans
  order_less_asym'
  order_le_less_trans
  order_less_le_trans
  order_trans
  order_antisym
  ord_le_eq_trans
  ord_eq_le_trans
  ord_less_eq_trans
  ord_eq_less_trans
  trans


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

subsection {* Order on bool *}

instance bool :: linorder 
  le_bool_def: "P \<le> Q \<equiv> P \<longrightarrow> Q"
  less_bool_def: "P < Q \<equiv> P \<le> Q \<and> P \<noteq> Q"
  by default (auto simp add: le_bool_def less_bool_def)

lemma le_boolI: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<le> Q"
  by (simp add: le_bool_def)

lemma le_boolI': "P \<longrightarrow> Q \<Longrightarrow> P \<le> Q"
  by (simp add: le_bool_def)

lemma le_boolE: "P \<le> Q \<Longrightarrow> P \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: le_bool_def)

lemma le_boolD: "P \<le> Q \<Longrightarrow> P \<longrightarrow> Q"
  by (simp add: le_bool_def)

lemma [code func]:
  "False \<le> b \<longleftrightarrow> True"
  "True \<le> b \<longleftrightarrow> b"
  "False < b \<longleftrightarrow> b"
  "True < b \<longleftrightarrow> False"
  unfolding le_bool_def less_bool_def by simp_all


subsection {* Monotonicity, syntactic least value operator and min/max *}

locale mono =
  fixes f
  assumes mono: "A \<le> B \<Longrightarrow> f A \<le> f B"

lemmas monoI [intro?] = mono.intro
  and monoD [dest?] = mono.mono

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

lemmas min_le_iff_disj = linorder_class.min_le_iff_disj [unfolded min_linorder]
lemmas le_max_iff_disj = linorder_class.le_max_iff_disj [unfolded max_linorder]
lemmas min_less_iff_disj = linorder_class.min_less_iff_disj [unfolded min_linorder]
lemmas less_max_iff_disj = linorder_class.less_max_iff_disj [unfolded max_linorder]
lemmas min_less_iff_conj [simp] = linorder_class.min_less_iff_conj [unfolded min_linorder]
lemmas max_less_iff_conj [simp] = linorder_class.max_less_iff_conj [unfolded max_linorder]
lemmas split_min = linorder_class.split_min [unfolded min_linorder]
lemmas split_max = linorder_class.split_max [unfolded max_linorder]

lemma min_leastL: "(!!x. least <= x) ==> min least x = least"
  by (simp add: min_def)

lemma max_leastL: "(!!x. least <= x) ==> max least x = x"
  by (simp add: max_def)

lemma min_leastR: "(\<And>x\<Colon>'a\<Colon>order. least \<le> x) \<Longrightarrow> min x least = least"
  apply (simp add: min_def)
  apply (blast intro: order_antisym)
  done

lemma max_leastR: "(\<And>x\<Colon>'a\<Colon>order. least \<le> x) \<Longrightarrow> max x least = x"
  apply (simp add: max_def)
  apply (blast intro: order_antisym)
  done

lemma min_of_mono:
    "(!!x y. (f x <= f y) = (x <= y)) ==> min (f m) (f n) = f (min m n)"
  by (simp add: min_def)

lemma max_of_mono:
    "(!!x y. (f x <= f y) = (x <= y)) ==> max (f m) (f n) = f (max m n)"
  by (simp add: max_def)


subsection {* legacy ML bindings *}

ML {*
val monoI = @{thm monoI};

structure HOL =
struct
  val thy = theory "HOL";
end;
*}  -- "belongs to theory HOL"

end
