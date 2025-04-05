(* Author: Lukas Bulwahn, TU Muenchen *)

section \<open>Counterexample generator performing narrowing-based testing\<close>

theory Quickcheck_Narrowing
imports Quickcheck_Random
keywords "find_unused_assms" :: diag
begin

subsection \<open>Counterexample generator\<close>

subsubsection \<open>Code generation setup\<close>

setup \<open>Code_Target.add_derived_target ("Haskell_Quickcheck", [(Code_Haskell.target, I)])\<close>

code_printing
  code_module Typerep \<rightharpoonup> (Haskell_Quickcheck) \<open>
module Typerep(Typerep(..)) where

data Typerep = Typerep String [Typerep]
\<close> for type_constructor typerep constant Typerep.Typerep
| type_constructor typerep \<rightharpoonup> (Haskell_Quickcheck) "Typerep.Typerep"
| constant Typerep.Typerep \<rightharpoonup> (Haskell_Quickcheck) "Typerep.Typerep"

code_reserved
  (Haskell_Quickcheck) Typerep

code_printing
  type_constructor integer \<rightharpoonup> (Haskell_Quickcheck) "Prelude.Int"
| constant "0::integer" \<rightharpoonup>
    (Haskell_Quickcheck) "!(0/ ::/ Prelude.Int)"

setup \<open>
  let
    val target = "Haskell_Quickcheck";
    fun print _ = Code_Haskell.print_numeral "Prelude.Int";
  in
    Numeral.add_code \<^const_name>\<open>Code_Numeral.Pos\<close> I print target
    #> Numeral.add_code \<^const_name>\<open>Code_Numeral.Neg\<close> (~) print target
  end
\<close>

code_printing
  constant Code_Numeral.push_bit \<rightharpoonup>
    (Haskell_Quickcheck) "Bit'_Shifts.drop'"
| constant Code_Numeral.drop_bit \<rightharpoonup>
    (Haskell_Quickcheck) "Bit'_Shifts.push'"


subsubsection \<open>Narrowing's deep representation of types and terms\<close>

datatype (plugins only: code extraction) narrowing_type =
  Narrowing_sum_of_products "narrowing_type list list"

datatype (plugins only: code extraction) narrowing_term =
  Narrowing_variable "integer list" narrowing_type
| Narrowing_constructor integer "narrowing_term list"

datatype (plugins only: code extraction) (dead 'a) narrowing_cons =
  Narrowing_cons narrowing_type "(narrowing_term list \<Rightarrow> 'a) list"

primrec map_cons :: "('a => 'b) => 'a narrowing_cons => 'b narrowing_cons"
where
  "map_cons f (Narrowing_cons ty cs) = Narrowing_cons ty (map (\<lambda>c. f \<circ> c) cs)"

subsubsection \<open>From narrowing's deep representation of terms to \<^theory>\<open>HOL.Code_Evaluation\<close>'s terms\<close>

class partial_term_of = typerep +
  fixes partial_term_of :: "'a itself => narrowing_term => Code_Evaluation.term"

lemma partial_term_of_anything: "partial_term_of x nt \<equiv> t"
  by (rule eq_reflection) (cases "partial_term_of x nt", cases t, simp)
 
subsubsection \<open>Auxilary functions for Narrowing\<close>

consts nth :: "'a list => integer => 'a"

code_printing constant nth \<rightharpoonup> (Haskell_Quickcheck) infixl 9 "!!"

consts error :: "char list => 'a"

code_printing constant error \<rightharpoonup> (Haskell_Quickcheck) "error"

consts toEnum :: "integer => char"

code_printing constant toEnum \<rightharpoonup> (Haskell_Quickcheck) "Prelude.toEnum"

consts marker :: "char"

code_printing constant marker \<rightharpoonup> (Haskell_Quickcheck) "''\\0'"

subsubsection \<open>Narrowing's basic operations\<close>

type_synonym 'a narrowing = "integer => 'a narrowing_cons"

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
  "apply f a d = (if d > 0 then
     (case f d of Narrowing_cons (Narrowing_sum_of_products ps) cfs \<Rightarrow>
       case a (d - 1) of Narrowing_cons ta cas \<Rightarrow>
       let
         shallow = non_empty ta;
         cs = [(\<lambda>(x # xs) \<Rightarrow> cf xs (conv cas x)). shallow, cf \<leftarrow> cfs]
       in Narrowing_cons (Narrowing_sum_of_products [ta # p. shallow, p \<leftarrow> ps]) cs)
     else Narrowing_cons (Narrowing_sum_of_products []) [])"

definition sum :: "'a narrowing => 'a narrowing => 'a narrowing"
where
  "sum a b d =
    (case a d of Narrowing_cons (Narrowing_sum_of_products ssa) ca \<Rightarrow>
      case b d of Narrowing_cons (Narrowing_sum_of_products ssb) cb \<Rightarrow>
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

subsubsection \<open>Narrowing generator type class\<close>

class narrowing =
  fixes narrowing :: "integer => 'a narrowing_cons"

datatype (plugins only: code extraction) property =
  Universal narrowing_type "(narrowing_term => property)" "narrowing_term => Code_Evaluation.term"
| Existential narrowing_type "(narrowing_term => property)" "narrowing_term => Code_Evaluation.term"
| Property bool

(* FIXME: hard-wired maximal depth of 100 here *)
definition exists :: "('a :: {narrowing, partial_term_of} => property) => property"
where
  "exists f = (case narrowing (100 :: integer) of Narrowing_cons ty cs \<Rightarrow> Existential ty (\<lambda> t. f (conv cs t)) (partial_term_of (TYPE('a))))"

definition "all" :: "('a :: {narrowing, partial_term_of} => property) => property"
where
  "all f = (case narrowing (100 :: integer) of Narrowing_cons ty cs \<Rightarrow> Universal ty (\<lambda>t. f (conv cs t)) (partial_term_of (TYPE('a))))"

subsubsection \<open>class \<open>is_testable\<close>\<close>

text \<open>The class \<open>is_testable\<close> ensures that all necessary type instances are generated.\<close>

class is_testable

instance bool :: is_testable ..

instance "fun" :: ("{term_of, narrowing, partial_term_of}", is_testable) is_testable ..

definition ensure_testable :: "'a :: is_testable => 'a :: is_testable"
where
  "ensure_testable f = f"


subsubsection \<open>Defining a simple datatype to represent functions in an incomplete and redundant way\<close>

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

subsubsection \<open>Setting up the counterexample generator\<close>

external_file \<open>~~/src/HOL/Tools/Quickcheck/Narrowing_Engine.hs\<close>
external_file \<open>~~/src/HOL/Tools/Quickcheck/PNF_Narrowing_Engine.hs\<close>
ML_file \<open>Tools/Quickcheck/narrowing_generators.ML\<close>

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

subsection \<open>Narrowing for sets\<close>

instantiation set :: (narrowing) narrowing
begin

definition "narrowing_set = Quickcheck_Narrowing.apply (Quickcheck_Narrowing.cons set) narrowing"

instance ..

end
  
subsection \<open>Narrowing for integers\<close>


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

declare [[code drop: "partial_term_of :: int itself \<Rightarrow> _"]]

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

declare [[code drop: "partial_term_of :: integer itself \<Rightarrow> _"]]  

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

subsection \<open>The \<open>find_unused_assms\<close> command\<close>

ML_file \<open>Tools/Quickcheck/find_unused_assms.ML\<close>

subsection \<open>Closing up\<close>

hide_type narrowing_type narrowing_term narrowing_cons property
hide_const map_cons nth error toEnum marker empty Narrowing_cons conv non_empty ensure_testable all exists drawn_from around_zero
hide_const (open) Narrowing_variable Narrowing_constructor "apply" sum cons
hide_fact empty_def cons_def conv.simps non_empty.simps apply_def sum_def ensure_testable_def all_def exists_def

end
