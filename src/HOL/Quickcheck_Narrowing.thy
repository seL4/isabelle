(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Counterexample generator performing narrowing-based testing *}

theory Quickcheck_Narrowing
imports Quickcheck_Random
keywords "find_unused_assms" :: diag
begin

subsection {* Counterexample generator *}

subsubsection {* Code generation setup *}

setup {* Code_Target.extend_target ("Haskell_Quickcheck", (Code_Haskell.target, I)) *}

code_printing
  code_module Typerep \<rightharpoonup> (Haskell_Quickcheck) {*
data Typerep = Typerep String [Typerep]
*}
| type_constructor typerep \<rightharpoonup> (Haskell_Quickcheck) "Typerep.Typerep"
| constant Typerep.Typerep \<rightharpoonup> (Haskell_Quickcheck) "Typerep.Typerep"
| type_constructor integer \<rightharpoonup> (Haskell_Quickcheck) "Prelude.Int"

code_reserved Haskell_Quickcheck Typerep

code_printing
  constant "0::integer" \<rightharpoonup>
    (Haskell_Quickcheck) "!(0/ ::/ Prelude.Int)"

setup {*
  let
    val target = "Haskell_Quickcheck";
    fun print _ = Code_Haskell.print_numeral "Prelude.Int";
  in
    Numeral.add_code @{const_name Code_Numeral.Pos} I print target
    #> Numeral.add_code @{const_name Code_Numeral.Neg} (op ~) print target
  end
*}


subsubsection {* Narrowing's deep representation of types and terms *}

datatype (plugins only: code extraction) narrowing_type =
  Narrowing_sum_of_products "narrowing_type list list"

datatype (plugins only: code extraction) narrowing_term =
  Narrowing_variable "integer list" narrowing_type
| Narrowing_constructor integer "narrowing_term list"

datatype (plugins only: code extraction) (dead 'a) narrowing_cons =
  Narrowing_cons narrowing_type "(narrowing_term list \<Rightarrow> 'a) list"

primrec map_cons :: "('a => 'b) => 'a narrowing_cons => 'b narrowing_cons"
where
  "map_cons f (Narrowing_cons ty cs) = Narrowing_cons ty (map (\<lambda>c. f o c) cs)"

subsubsection {* From narrowing's deep representation of terms to @{theory Code_Evaluation}'s terms *}

class partial_term_of = typerep +
  fixes partial_term_of :: "'a itself => narrowing_term => Code_Evaluation.term"

lemma partial_term_of_anything: "partial_term_of x nt \<equiv> t"
  by (rule eq_reflection) (cases "partial_term_of x nt", cases t, simp)
 
subsubsection {* Auxilary functions for Narrowing *}

consts nth :: "'a list => integer => 'a"

code_printing constant nth \<rightharpoonup> (Haskell_Quickcheck) infixl 9 "!!"

consts error :: "char list => 'a"

code_printing constant error \<rightharpoonup> (Haskell_Quickcheck) "error"

consts toEnum :: "integer => char"

code_printing constant toEnum \<rightharpoonup> (Haskell_Quickcheck) "Prelude.toEnum"

consts marker :: "char"

code_printing constant marker \<rightharpoonup> (Haskell_Quickcheck) "''\\0'"

subsubsection {* Narrowing's basic operations *}

type_synonym 'a narrowing = "integer => 'a narrowing_cons"

definition empty :: "'a narrowing"
where
  "empty d = Narrowing_cons (Narrowing_sum_of_products []) []"
  
definition cons :: "'a => 'a narrowing"
where
  "cons a d = (Narrowing_cons (Narrowing_sum_of_products [[]]) [(\<lambda>_. a)])"

fun conv :: "(narrowing_term list => 'a) list => narrowing_term => 'a"
where
  "conv cs (Narrowing_variable p _) = error (marker # map toEnum p)"
| "conv cs (Narrowing_constructor i xs) = (nth cs i) xs"

fun non_empty :: "narrowing_type => bool"
where
  "non_empty (Narrowing_sum_of_products ps) = (\<not> (List.null ps))"

definition "apply" :: "('a => 'b) narrowing => 'a narrowing => 'b narrowing"
where
  "apply f a d =
     (case f d of Narrowing_cons (Narrowing_sum_of_products ps) cfs =>
       case a (d - 1) of Narrowing_cons ta cas =>
       let
         shallow = (d > 0 \<and> non_empty ta);
         cs = [(\<lambda>xs'. (case xs' of [] => undefined | x # xs => cf xs (conv cas x))). shallow, cf <- cfs]
       in Narrowing_cons (Narrowing_sum_of_products [ta # p. shallow, p <- ps]) cs)"

definition sum :: "'a narrowing => 'a narrowing => 'a narrowing"
where
  "sum a b d =
    (case a d of Narrowing_cons (Narrowing_sum_of_products ssa) ca => 
      case b d of Narrowing_cons (Narrowing_sum_of_products ssb) cb =>
      Narrowing_cons (Narrowing_sum_of_products (ssa @ ssb)) (ca @ cb))"

lemma [fundef_cong]:
  assumes "a d = a' d" "b d = b' d" "d = d'"
  shows "sum a b d = sum a' b' d'"
using assms unfolding sum_def by (auto split: narrowing_cons.split narrowing_type.split)

lemma [fundef_cong]:
  assumes "f d = f' d" "(\<And>d'. 0 \<le> d' \<and> d' < d \<Longrightarrow> a d' = a' d')"
  assumes "d = d'"
  shows "apply f a d = apply f' a' d'"
proof -
  note assms
  moreover have "0 < d' \<Longrightarrow> 0 \<le> d' - 1"
    by (simp add: less_integer_def less_eq_integer_def)
  ultimately show ?thesis
    by (auto simp add: apply_def Let_def
      split: narrowing_cons.split narrowing_type.split)
qed

subsubsection {* Narrowing generator type class *}

class narrowing =
  fixes narrowing :: "integer => 'a narrowing_cons"

datatype (plugins only: code extraction) property =
  Universal narrowing_type "(narrowing_term => property)" "narrowing_term => Code_Evaluation.term"
| Existential narrowing_type "(narrowing_term => property)" "narrowing_term => Code_Evaluation.term"
| Property bool

(* FIXME: hard-wired maximal depth of 100 here *)
definition exists :: "('a :: {narrowing, partial_term_of} => property) => property"
where
  "exists f = (case narrowing (100 :: integer) of Narrowing_cons ty cs => Existential ty (\<lambda> t. f (conv cs t)) (partial_term_of (TYPE('a))))"

definition "all" :: "('a :: {narrowing, partial_term_of} => property) => property"
where
  "all f = (case narrowing (100 :: integer) of Narrowing_cons ty cs => Universal ty (\<lambda>t. f (conv cs t)) (partial_term_of (TYPE('a))))"

subsubsection {* class @{text is_testable} *}

text {* The class @{text is_testable} ensures that all necessary type instances are generated. *}

class is_testable

instance bool :: is_testable ..

instance "fun" :: ("{term_of, narrowing, partial_term_of}", is_testable) is_testable ..

definition ensure_testable :: "'a :: is_testable => 'a :: is_testable"
where
  "ensure_testable f = f"


subsubsection {* Defining a simple datatype to represent functions in an incomplete and redundant way *}

datatype (plugins only: code quickcheck_narrowing extraction) (dead 'a, dead 'b) ffun =
  Constant 'b
| Update 'a 'b "('a, 'b) ffun"

primrec eval_ffun :: "('a, 'b) ffun => 'a => 'b"
where
  "eval_ffun (Constant c) x = c"
| "eval_ffun (Update x' y f) x = (if x = x' then y else eval_ffun f x)"

hide_type (open) ffun
hide_const (open) Constant Update eval_ffun

datatype (plugins only: code quickcheck_narrowing extraction) (dead 'b) cfun = Constant 'b

primrec eval_cfun :: "'b cfun => 'a => 'b"
where
  "eval_cfun (Constant c) y = c"

hide_type (open) cfun
hide_const (open) Constant eval_cfun Abs_cfun Rep_cfun

subsubsection {* Setting up the counterexample generator *}

ML_file "Tools/Quickcheck/narrowing_generators.ML"

setup {* Narrowing_Generators.setup *}

definition narrowing_dummy_partial_term_of :: "('a :: partial_term_of) itself => narrowing_term => term"
where
  "narrowing_dummy_partial_term_of = partial_term_of"

definition narrowing_dummy_narrowing :: "integer => ('a :: narrowing) narrowing_cons"
where
  "narrowing_dummy_narrowing = narrowing"

lemma [code]:
  "ensure_testable f =
    (let
      x = narrowing_dummy_narrowing :: integer => bool narrowing_cons;
      y = narrowing_dummy_partial_term_of :: bool itself => narrowing_term => term;
      z = (conv :: _ => _ => unit)  in f)"
unfolding Let_def ensure_testable_def ..

subsection {* Narrowing for sets *}

instantiation set :: (narrowing) narrowing
begin

definition "narrowing_set = Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons set) narrowing"

instance ..

end
  
subsection {* Narrowing for integers *}


definition drawn_from :: "'a list \<Rightarrow> 'a narrowing_cons"
where
  "drawn_from xs =
    Narrowing_cons (Narrowing_sum_of_products (map (\<lambda>_. []) xs)) (map (\<lambda>x _. x) xs)"

function around_zero :: "int \<Rightarrow> int list"
where
  "around_zero i = (if i < 0 then [] else (if i = 0 then [0] else around_zero (i - 1) @ [i, -i]))"
  by pat_completeness auto
termination by (relation "measure nat") auto

declare around_zero.simps [simp del]

lemma length_around_zero:
  assumes "i >= 0" 
  shows "length (around_zero i) = 2 * nat i + 1"
proof (induct rule: int_ge_induct [OF assms])
  case 1
  from 1 show ?case by (simp add: around_zero.simps)
next
  case (2 i)
  from 2 show ?case
    by (simp add: around_zero.simps [of "i + 1"])
qed

instantiation int :: narrowing
begin

definition
  "narrowing_int d = (let (u :: _ \<Rightarrow> _ \<Rightarrow> unit) = conv; i = int_of_integer d
    in drawn_from (around_zero i))"

instance ..

end

lemma [code, code del]: "partial_term_of (ty :: int itself) t \<equiv> undefined"
  by (rule partial_term_of_anything)+

lemma [code]:
  "partial_term_of (ty :: int itself) (Narrowing_variable p t) \<equiv>
    Code_Evaluation.Free (STR ''_'') (Typerep.Typerep (STR ''Int.int'') [])"
  "partial_term_of (ty :: int itself) (Narrowing_constructor i []) \<equiv>
    (if i mod 2 = 0
     then Code_Evaluation.term_of (- (int_of_integer i) div 2)
     else Code_Evaluation.term_of ((int_of_integer i + 1) div 2))"
  by (rule partial_term_of_anything)+

instantiation integer :: narrowing
begin

definition
  "narrowing_integer d = (let (u :: _ \<Rightarrow> _ \<Rightarrow> unit) = conv; i = int_of_integer d
    in drawn_from (map integer_of_int (around_zero i)))"

instance ..

end

lemma [code, code del]: "partial_term_of (ty :: integer itself) t \<equiv> undefined"
  by (rule partial_term_of_anything)+

lemma [code]:
  "partial_term_of (ty :: integer itself) (Narrowing_variable p t) \<equiv>
    Code_Evaluation.Free (STR ''_'') (Typerep.Typerep (STR ''Code_Numeral.integer'') [])"
  "partial_term_of (ty :: integer itself) (Narrowing_constructor i []) \<equiv>
    (if i mod 2 = 0
     then Code_Evaluation.term_of (- i div 2)
     else Code_Evaluation.term_of ((i + 1) div 2))"
  by (rule partial_term_of_anything)+

code_printing constant "Code_Evaluation.term_of :: integer \<Rightarrow> term" \<rightharpoonup> (Haskell_Quickcheck) 
  "(let { t = Typerep.Typerep \"Code'_Numeral.integer\" [];
     mkFunT s t = Typerep.Typerep \"fun\" [s, t];
     numT = Typerep.Typerep \"Num.num\" [];
     mkBit 0 = Generated'_Code.Const \"Num.num.Bit0\" (mkFunT numT numT);
     mkBit 1 = Generated'_Code.Const \"Num.num.Bit1\" (mkFunT numT numT);
     mkNumeral 1 = Generated'_Code.Const \"Num.num.One\" numT;
     mkNumeral i = let { q = i `Prelude.div` 2; r = i `Prelude.mod` 2 }
       in Generated'_Code.App (mkBit r) (mkNumeral q);
     mkNumber 0 = Generated'_Code.Const \"Groups.zero'_class.zero\" t;
     mkNumber 1 = Generated'_Code.Const \"Groups.one'_class.one\" t;
     mkNumber i = if i > 0 then
         Generated'_Code.App
           (Generated'_Code.Const \"Num.numeral'_class.numeral\"
              (mkFunT numT t))
           (mkNumeral i)
       else
         Generated'_Code.App
           (Generated'_Code.Const \"Groups.uminus'_class.uminus\" (mkFunT t t))
           (mkNumber (- i)); } in mkNumber)"

subsection {* The @{text find_unused_assms} command *}

ML_file "Tools/Quickcheck/find_unused_assms.ML"

subsection {* Closing up *}

hide_type narrowing_type narrowing_term narrowing_cons property
hide_const map_cons nth error toEnum marker empty Narrowing_cons conv non_empty ensure_testable all exists drawn_from around_zero
hide_const (open) Narrowing_variable Narrowing_constructor "apply" sum cons
hide_fact empty_def cons_def conv.simps non_empty.simps apply_def sum_def ensure_testable_def all_def exists_def

end
