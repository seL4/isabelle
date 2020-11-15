(*  Title:      HOL/Code_Evaluation.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Term evaluation using the generic code generator\<close>

theory Code_Evaluation
imports Typerep Limited_Sequence
keywords "value" :: diag
begin

subsection \<open>Term representation\<close>

subsubsection \<open>Terms and class \<open>term_of\<close>\<close>

datatype (plugins only: extraction) "term" = dummy_term

definition Const :: "String.literal \<Rightarrow> typerep \<Rightarrow> term" where
  "Const _ _ = dummy_term"

definition App :: "term \<Rightarrow> term \<Rightarrow> term" where
  "App _ _ = dummy_term"

definition Abs :: "String.literal \<Rightarrow> typerep \<Rightarrow> term \<Rightarrow> term" where
  "Abs _ _ _ = dummy_term"

definition Free :: "String.literal \<Rightarrow> typerep \<Rightarrow> term" where
  "Free _ _ = dummy_term"

code_datatype Const App Abs Free

class term_of = typerep +
  fixes term_of :: "'a \<Rightarrow> term"

lemma term_of_anything: "term_of x \<equiv> t"
  by (rule eq_reflection) (cases "term_of x", cases t, simp)

definition valapp :: "('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)
  \<Rightarrow> 'a \<times> (unit \<Rightarrow> term) \<Rightarrow> 'b \<times> (unit \<Rightarrow> term)" where
  "valapp f x = (fst f (fst x), \<lambda>u. App (snd f ()) (snd x ()))"

lemma valapp_code [code, code_unfold]:
  "valapp (f, tf) (x, tx) = (f x, \<lambda>u. App (tf ()) (tx ()))"
  by (simp only: valapp_def fst_conv snd_conv)


subsubsection \<open>Syntax\<close>

definition termify :: "'a \<Rightarrow> term" where
  [code del]: "termify x = dummy_term"

abbreviation valtermify :: "'a \<Rightarrow> 'a \<times> (unit \<Rightarrow> term)" where
  "valtermify x \<equiv> (x, \<lambda>u. termify x)"

bundle term_syntax
begin

notation App (infixl "<\<cdot>>" 70)
  and valapp (infixl "{\<cdot>}" 70)

end


subsection \<open>Tools setup and evaluation\<close>

context
begin

qualified definition TERM_OF :: "'a::term_of itself"
where
  "TERM_OF = snd (Code_Evaluation.term_of :: 'a \<Rightarrow> _, TYPE('a))"

qualified definition TERM_OF_EQUAL :: "'a::term_of itself"
where
  "TERM_OF_EQUAL = snd (\<lambda>(a::'a). (Code_Evaluation.term_of a, HOL.eq a), TYPE('a))"

end

lemma eq_eq_TrueD:
  fixes x y :: "'a::{}"
  assumes "(x \<equiv> y) \<equiv> Trueprop True"
  shows "x \<equiv> y"
  using assms by simp

code_printing
  type_constructor "term" \<rightharpoonup> (Eval) "Term.term"
| constant Const \<rightharpoonup> (Eval) "Term.Const/ ((_), (_))"
| constant App \<rightharpoonup> (Eval) "Term.$/ ((_), (_))"
| constant Abs \<rightharpoonup> (Eval) "Term.Abs/ ((_), (_), (_))"
| constant Free \<rightharpoonup> (Eval) "Term.Free/ ((_), (_))"

ML_file \<open>Tools/code_evaluation.ML\<close>

code_reserved Eval Code_Evaluation

ML_file \<open>~~/src/HOL/Tools/value_command.ML\<close>


subsection \<open>Dedicated \<open>term_of\<close> instances\<close>

instantiation "fun" :: (typerep, typerep) term_of
begin

definition
  "term_of (f :: 'a \<Rightarrow> 'b) =
    Const (STR ''Pure.dummy_pattern'')
      (Typerep.Typerep (STR ''fun'') [Typerep.typerep TYPE('a), Typerep.typerep TYPE('b)])"

instance ..

end

declare [[code drop: rec_term case_term
  "term_of :: typerep \<Rightarrow> _" "term_of :: term \<Rightarrow> _" "term_of :: String.literal \<Rightarrow> _"
  "term_of :: _ Predicate.pred \<Rightarrow> term" "term_of :: _ Predicate.seq \<Rightarrow> term"]]

code_printing
  constant "term_of :: integer \<Rightarrow> term" \<rightharpoonup> (Eval) "HOLogic.mk'_number/ HOLogic.code'_integerT"
| constant "term_of :: String.literal \<Rightarrow> term" \<rightharpoonup> (Eval) "HOLogic.mk'_literal"

declare [[code drop: "term_of :: integer \<Rightarrow> _"]]

lemma term_of_integer [unfolded typerep_fun_def typerep_num_def typerep_integer_def, code]:
  "term_of (i :: integer) =
  (if i > 0 then 
     App (Const (STR ''Num.numeral_class.numeral'') (TYPEREP(num \<Rightarrow> integer)))
      (term_of (num_of_integer i))
   else if i = 0 then Const (STR ''Groups.zero_class.zero'') TYPEREP(integer)
   else
     App (Const (STR ''Groups.uminus_class.uminus'') TYPEREP(integer \<Rightarrow> integer))
       (term_of (- i)))"
  by (rule term_of_anything [THEN meta_eq_to_obj_eq])

code_reserved Eval HOLogic


subsection \<open>Generic reification\<close>

ML_file \<open>~~/src/HOL/Tools/reification.ML\<close>


subsection \<open>Diagnostic\<close>

definition tracing :: "String.literal \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code del]: "tracing s x = x"

code_printing
  constant "tracing :: String.literal => 'a => 'a" \<rightharpoonup> (Eval) "Code'_Evaluation.tracing"


hide_const dummy_term valapp
hide_const (open) Const App Abs Free termify valtermify term_of tracing

end
