(*  Title:      HOL/HOL.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* The basis of Higher-Order Logic *}

theory HOL = CPure
files ("HOL_lemmas.ML") ("cladata.ML") ("blastdata.ML") ("simpdata.ML"):


subsection {* Primitive logic *}

subsubsection {* Core syntax *}

global

classes "term" < logic
defaultsort "term"

typedecl bool

arities
  bool :: "term"
  fun :: ("term", "term") "term"

judgment
  Trueprop      :: "bool => prop"                   ("(_)" 5)

consts
  Not           :: "bool => bool"                   ("~ _" [40] 40)
  True          :: bool
  False         :: bool
  If            :: "[bool, 'a, 'a] => 'a"           ("(if (_)/ then (_)/ else (_))" 10)
  arbitrary     :: 'a

  The           :: "('a => bool) => 'a"
  All           :: "('a => bool) => bool"           (binder "ALL " 10)
  Ex            :: "('a => bool) => bool"           (binder "EX " 10)
  Ex1           :: "('a => bool) => bool"           (binder "EX! " 10)
  Let           :: "['a, 'a => 'b] => 'b"

  "="           :: "['a, 'a] => bool"               (infixl 50)
  &             :: "[bool, bool] => bool"           (infixr 35)
  "|"           :: "[bool, bool] => bool"           (infixr 30)
  -->           :: "[bool, bool] => bool"           (infixr 25)

local


subsubsection {* Additional concrete syntax *}

nonterminals
  letbinds  letbind
  case_syn  cases_syn

syntax
  ~=            :: "['a, 'a] => bool"                    (infixl 50)
  "_The"        :: "[pttrn, bool] => 'a"                 ("(3THE _./ _)" [0, 10] 10)

  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"                ("(let (_)/ in (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"               ("(case _ of/ _)" 10)
  "_case1"      :: "['a, 'b] => case_syn"                ("(2_ =>/ _)" 10)
  ""            :: "case_syn => cases_syn"               ("_")
  "_case2"      :: "[case_syn, cases_syn] => cases_syn"  ("_/ | _")

translations
  "x ~= y"                == "~ (x = y)"
  "THE x. P"              == "The (%x. P)"
  "_Let (_binds b bs) e"  == "_Let b (_Let bs e)"
  "let x = a in e"        == "Let a (%x. e)"

syntax ("" output)
  "="           :: "['a, 'a] => bool"                    (infix 50)
  "~="          :: "['a, 'a] => bool"                    (infix 50)

syntax (symbols)
  Not           :: "bool => bool"                        ("\<not> _" [40] 40)
  "op &"        :: "[bool, bool] => bool"                (infixr "\<and>" 35)
  "op |"        :: "[bool, bool] => bool"                (infixr "\<or>" 30)
  "op -->"      :: "[bool, bool] => bool"                (infixr "\<midarrow>\<rightarrow>" 25)
  "op ~="       :: "['a, 'a] => bool"                    (infix "\<noteq>" 50)
  "ALL "        :: "[idts, bool] => bool"                ("(3\<forall>_./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3\<exists>_./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3\<exists>!_./ _)" [0, 10] 10)
  "_case1"      :: "['a, 'b] => case_syn"                ("(2_ \<Rightarrow>/ _)" 10)
(*"_case2"      :: "[case_syn, cases_syn] => cases_syn"  ("_/ \\<orelse> _")*)

syntax (symbols output)
  "op ~="       :: "['a, 'a] => bool"                    (infix "\<noteq>" 50)

syntax (xsymbols)
  "op -->"      :: "[bool, bool] => bool"                (infixr "\<longrightarrow>" 25)

syntax (HTML output)
  Not           :: "bool => bool"                        ("\<not> _" [40] 40)

syntax (HOL)
  "ALL "        :: "[idts, bool] => bool"                ("(3! _./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(3? _./ _)" [0, 10] 10)
  "EX! "        :: "[idts, bool] => bool"                ("(3?! _./ _)" [0, 10] 10)


subsubsection {* Axioms and basic definitions *}

axioms
  eq_reflection: "(x=y) ==> (x==y)"

  refl:         "t = (t::'a)"
  subst:        "[| s = t; P(s) |] ==> P(t::'a)"

  ext:          "(!!x::'a. (f x ::'b) = g x) ==> (%x. f x) = (%x. g x)"
    -- {* Extensionality is built into the meta-logic, and this rule expresses *}
    -- {* a related property.  It is an eta-expanded version of the traditional *}
    -- {* rule, and similar to the ABS rule of HOL *}

  the_eq_trivial: "(THE x. x = a) = (a::'a)"

  impI:         "(P ==> Q) ==> P-->Q"
  mp:           "[| P-->Q;  P |] ==> Q"

defs
  True_def:     "True      == ((%x::bool. x) = (%x. x))"
  All_def:      "All(P)    == (P = (%x. True))"
  Ex_def:       "Ex(P)     == !Q. (!x. P x --> Q) --> Q"
  False_def:    "False     == (!P. P)"
  not_def:      "~ P       == P-->False"
  and_def:      "P & Q     == !R. (P-->Q-->R) --> R"
  or_def:       "P | Q     == !R. (P-->R) --> (Q-->R) --> R"
  Ex1_def:      "Ex1(P)    == ? x. P(x) & (! y. P(y) --> y=x)"

axioms
  iff:          "(P-->Q) --> (Q-->P) --> (P=Q)"
  True_or_False:  "(P=True) | (P=False)"

defs
  Let_def:      "Let s f == f(s)"
  if_def:       "If P x y == THE z::'a. (P=True --> z=x) & (P=False --> z=y)"

  arbitrary_def:  "False ==> arbitrary == (THE x. False)"
    -- {* @{term arbitrary} is completely unspecified, but is made to appear as a
    definition syntactically *}


subsubsection {* Generic algebraic operations *}

axclass zero < "term"
axclass one < "term"
axclass plus < "term"
axclass minus < "term"
axclass times < "term"
axclass inverse < "term"

global

consts
  "0"           :: "'a::zero"                       ("0")
  "1"           :: "'a::one"                        ("1")
  "+"           :: "['a::plus, 'a]  => 'a"          (infixl 65)
  -             :: "['a::minus, 'a] => 'a"          (infixl 65)
  uminus        :: "['a::minus] => 'a"              ("- _" [81] 80)
  *             :: "['a::times, 'a] => 'a"          (infixl 70)

local

typed_print_translation {*
  let
    fun tr' c = (c, fn show_sorts => fn T => fn ts =>
      if T = dummyT orelse not (! show_types) andalso can Term.dest_Type T then raise Match
      else Syntax.const Syntax.constrainC $ Syntax.const c $ Syntax.term_of_typ show_sorts T);
  in [tr' "0", tr' "1"] end;
*} -- {* show types that are presumably too general *}


consts
  abs           :: "'a::minus => 'a"
  inverse       :: "'a::inverse => 'a"
  divide        :: "['a::inverse, 'a] => 'a"        (infixl "'/" 70)

syntax (xsymbols)
  abs :: "'a::minus => 'a"    ("\<bar>_\<bar>")
syntax (HTML output)
  abs :: "'a::minus => 'a"    ("\<bar>_\<bar>")

axclass plus_ac0 < plus, zero
  commute: "x + y = y + x"
  assoc:   "(x + y) + z = x + (y + z)"
  zero:    "0 + x = x"


subsection {* Theory and package setup *}

subsubsection {* Basic lemmas *}

use "HOL_lemmas.ML"
theorems case_split = case_split_thm [case_names True False]

declare trans [trans]
declare impE [CPure.elim]  iffD1 [CPure.elim]  iffD2 [CPure.elim]


subsubsection {* Atomizing meta-level connectives *}

lemma atomize_all [atomize]: "(!!x. P x) == Trueprop (ALL x. P x)"
proof
  assume "!!x. P x"
  show "ALL x. P x" by (rule allI)
next
  assume "ALL x. P x"
  thus "!!x. P x" by (rule allE)
qed

lemma atomize_imp [atomize]: "(A ==> B) == Trueprop (A --> B)"
proof
  assume r: "A ==> B"
  show "A --> B" by (rule impI) (rule r)
next
  assume "A --> B" and A
  thus B by (rule mp)
qed

lemma atomize_eq [atomize]: "(x == y) == Trueprop (x = y)"
proof
  assume "x == y"
  show "x = y" by (unfold prems) (rule refl)
next
  assume "x = y"
  thus "x == y" by (rule eq_reflection)
qed

lemma atomize_conj [atomize]:
  "(!!C. (A ==> B ==> PROP C) ==> PROP C) == Trueprop (A & B)"
proof
  assume "!!C. (A ==> B ==> PROP C) ==> PROP C"
  show "A & B" by (rule conjI)
next
  fix C
  assume "A & B"
  assume "A ==> B ==> PROP C"
  thus "PROP C"
  proof this
    show A by (rule conjunct1)
    show B by (rule conjunct2)
  qed
qed


subsubsection {* Classical Reasoner setup *}

use "cladata.ML"
setup hypsubst_setup

declare atomize_all [symmetric, rulify]  atomize_imp [symmetric, rulify]

setup Classical.setup
setup clasetup

declare ext [intro?]
declare disjI1 [elim?]  disjI2 [elim?]  ex1_implies_ex [elim?]  sym [elim?]

use "blastdata.ML"
setup Blast.setup


subsubsection {* Simplifier setup *}

use "simpdata.ML"
setup Simplifier.setup
setup "Simplifier.method_setup Splitter.split_modifiers" setup simpsetup
setup Splitter.setup setup Clasimp.setup


subsubsection {* Generic cases and induction *}

constdefs
  induct_forall :: "('a => bool) => bool"
  "induct_forall P == \<forall>x. P x"
  induct_implies :: "bool => bool => bool"
  "induct_implies A B == A --> B"
  induct_equal :: "'a => 'a => bool"
  "induct_equal x y == x = y"
  induct_conj :: "bool => bool => bool"
  "induct_conj A B == A & B"

lemma induct_forall_eq: "(!!x. P x) == Trueprop (induct_forall (\<lambda>x. P x))"
  by (simp only: atomize_all induct_forall_def)

lemma induct_implies_eq: "(A ==> B) == Trueprop (induct_implies A B)"
  by (simp only: atomize_imp induct_implies_def)

lemma induct_equal_eq: "(x == y) == Trueprop (induct_equal x y)"
  by (simp only: atomize_eq induct_equal_def)

lemma induct_forall_conj: "induct_forall (\<lambda>x. induct_conj (A x) (B x)) =
    induct_conj (induct_forall A) (induct_forall B)"
  by (unfold induct_forall_def induct_conj_def) blast

lemma induct_implies_conj: "induct_implies C (induct_conj A B) =
    induct_conj (induct_implies C A) (induct_implies C B)"
  by (unfold induct_implies_def induct_conj_def) blast

lemma induct_conj_curry: "(induct_conj A B ==> C) == (A ==> B ==> C)"
  by (simp only: atomize_imp atomize_eq induct_conj_def) (rule equal_intr_rule, blast+)

lemma induct_impliesI: "(A ==> B) ==> induct_implies A B"
  by (simp add: induct_implies_def)

lemmas induct_atomize = induct_forall_eq induct_implies_eq induct_equal_eq
lemmas induct_rulify1 = induct_atomize [symmetric, standard]
lemmas induct_rulify2 =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def
lemmas induct_conj = induct_forall_conj induct_implies_conj induct_conj_curry

hide const induct_forall induct_implies induct_equal induct_conj


text {* Method setup. *}

ML {*
  structure InductMethod = InductMethodFun
  (struct
    val dest_concls = HOLogic.dest_concls;
    val cases_default = thm "case_split";
    val local_impI = thm "induct_impliesI";
    val conjI = thm "conjI";
    val atomize = thms "induct_atomize";
    val rulify1 = thms "induct_rulify1";
    val rulify2 = thms "induct_rulify2";
  end);
*}

setup InductMethod.setup


subsection {* Order signatures and orders *}

axclass
  ord < "term"

syntax
  "op <"        :: "['a::ord, 'a] => bool"             ("op <")
  "op <="       :: "['a::ord, 'a] => bool"             ("op <=")

global

consts
  "op <"        :: "['a::ord, 'a] => bool"             ("(_/ < _)"  [50, 51] 50)
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ <= _)" [50, 51] 50)

local

syntax (symbols)
  "op <="       :: "['a::ord, 'a] => bool"             ("op \<le>")
  "op <="       :: "['a::ord, 'a] => bool"             ("(_/ \<le> _)"  [50, 51] 50)

(*Tell blast about overloading of < and <= to reduce the risk of
  its applying a rule for the wrong type*)
ML {*
Blast.overloaded ("op <" , domain_type);
Blast.overloaded ("op <=", domain_type);
*}


subsubsection {* Monotonicity *}

constdefs
  mono :: "['a::ord => 'b::ord] => bool"
  "mono f == ALL A B. A <= B --> f A <= f B"

lemma monoI [intro?]: "(!!A B. A <= B ==> f A <= f B) ==> mono f"
  by (unfold mono_def) blast

lemma monoD [dest?]: "mono f ==> A <= B ==> f A <= f B"
  by (unfold mono_def) blast

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


subsubsection "Orders"

axclass order < ord
  order_refl [iff]: "x <= x"
  order_trans: "x <= y ==> y <= z ==> x <= z"
  order_antisym: "x <= y ==> y <= x ==> x = y"
  order_less_le: "(x < y) = (x <= y & x ~= y)"


text {* Reflexivity. *}

lemma order_eq_refl: "!!x::'a::order. x = y ==> x <= y"
    -- {* This form is useful with the classical reasoner. *}
  apply (erule ssubst)
  apply (rule order_refl)
  done

lemma order_less_irrefl [simp]: "~ x < (x::'a::order)"
  by (simp add: order_less_le)

lemma order_le_less: "((x::'a::order) <= y) = (x < y | x = y)"
    -- {* NOT suitable for iff, since it can cause PROOF FAILED. *}
  apply (simp add: order_less_le)
  apply (blast intro!: order_refl)
  done

lemmas order_le_imp_less_or_eq = order_le_less [THEN iffD1, standard]

lemma order_less_imp_le: "!!x::'a::order. x < y ==> x <= y"
  by (simp add: order_less_le)


text {* Asymmetry. *}

lemma order_less_not_sym: "(x::'a::order) < y ==> ~ (y < x)"
  by (simp add: order_less_le order_antisym)

lemma order_less_asym: "x < (y::'a::order) ==> (~P ==> y < x) ==> P"
  apply (drule order_less_not_sym)
  apply (erule contrapos_np)
  apply simp
  done


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


subsubsection {* Least value operator *}

constdefs
  Least :: "('a::ord => bool) => 'a"               (binder "LEAST " 10)
  "Least P == THE x. P x & (ALL y. P y --> x <= y)"
    -- {* We can no longer use LeastM because the latter requires Hilbert-AC. *}

lemma LeastI2:
  "[| P (x::'a::order);
      !!y. P y ==> x <= y;
      !!x. [| P x; ALL y. P y --> x \<le> y |] ==> Q x |]
   ==> Q (Least P)";
  apply (unfold Least_def)
  apply (rule theI2)
    apply (blast intro: order_antisym)+
  done

lemma Least_equality:
    "[| P (k::'a::order); !!x. P x ==> k <= x |] ==> (LEAST x. P x) = k";
  apply (simp add: Least_def)
  apply (rule the_equality)
  apply (auto intro!: order_antisym)
  done


subsubsection "Linear / total orders"

axclass linorder < order
  linorder_linear: "x <= y | y <= x"

lemma linorder_less_linear: "!!x::'a::linorder. x<y | x=y | y<x"
  apply (simp add: order_less_le)
  apply (insert linorder_linear)
  apply blast
  done

lemma linorder_cases [case_names less equal greater]:
    "((x::'a::linorder) < y ==> P) ==> (x = y ==> P) ==> (y < x ==> P) ==> P"
  apply (insert linorder_less_linear)
  apply blast
  done

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
  apply (cut_tac x = x and y = y in linorder_less_linear)
  apply auto
  done

lemma linorder_neqE: "x ~= (y::'a::linorder) ==> (x < y ==> R) ==> (y < x ==> R) ==> R"
  apply (simp add: linorder_neq_iff)
  apply blast
  done


subsubsection "Min and max on (linear) orders"

lemma min_same [simp]: "min (x::'a::order) x = x"
  by (simp add: min_def)

lemma max_same [simp]: "max (x::'a::order) x = x"
  by (simp add: max_def)

lemma le_max_iff_disj: "!!z::'a::linorder. (z <= max x y) = (z <= x | z <= y)"
  apply (simp add: max_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma le_maxI1: "(x::'a::linorder) <= max x y"
  by (simp add: le_max_iff_disj)

lemma le_maxI2: "(y::'a::linorder) <= max x y"
    -- {* CANNOT use with @{text "[intro!]"} because blast will give PROOF FAILED. *}
  by (simp add: le_max_iff_disj)

lemma less_max_iff_disj: "!!z::'a::linorder. (z < max x y) = (z < x | z < y)"
  apply (simp add: max_def order_le_less)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma max_le_iff_conj [simp]:
    "!!z::'a::linorder. (max x y <= z) = (x <= z & y <= z)"
  apply (simp add: max_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
  done

lemma max_less_iff_conj [simp]:
    "!!z::'a::linorder. (max x y < z) = (x < z & y < z)"
  apply (simp add: order_le_less max_def)
  apply (insert linorder_less_linear)
  apply (blast intro: order_less_trans)
  done

lemma le_min_iff_conj [simp]:
    "!!z::'a::linorder. (z <= min x y) = (z <= x & z <= y)"
    -- {* @{text "[iff]"} screws up a Q{text blast} in MiniML *}
  apply (simp add: min_def)
  apply (insert linorder_linear)
  apply (blast intro: order_trans)
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

lemma split_min:
    "P (min (i::'a::linorder) j) = ((i <= j --> P(i)) & (~ i <= j --> P(j)))"
  by (simp add: min_def)

lemma split_max:
    "P (max (i::'a::linorder) j) = ((i <= j --> P(j)) & (~ i <= j --> P(i)))"
  by (simp add: max_def)


subsubsection "Bounded quantifiers"

syntax
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3EX _<=_./ _)" [0, 0, 10] 10)

syntax (symbols)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_lessAll" :: "[idt, 'a, bool] => bool"   ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_lessEx"  :: "[idt, 'a, bool] => bool"   ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_leAll"   :: "[idt, 'a, bool] => bool"   ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_leEx"    :: "[idt, 'a, bool] => bool"   ("(3? _<=_./ _)" [0, 0, 10] 10)

translations
 "ALL x<y. P"   =>  "ALL x. x < y --> P"
 "EX x<y. P"    =>  "EX x. x < y  & P"
 "ALL x<=y. P"  =>  "ALL x. x <= y --> P"
 "EX x<=y. P"   =>  "EX x. x <= y & P"

end
