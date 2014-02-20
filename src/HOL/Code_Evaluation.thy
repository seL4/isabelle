(*  Title:      HOL/Code_Evaluation.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Term evaluation using the generic code generator *}

theory Code_Evaluation
imports Typerep Limited_Sequence
begin

subsection {* Term representation *}

subsubsection {* Terms and class @{text term_of} *}

datatype "term" = dummy_term

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


subsubsection {* Syntax *}

definition termify :: "'a \<Rightarrow> term" where
  [code del]: "termify x = dummy_term"

abbreviation valtermify :: "'a \<Rightarrow> 'a \<times> (unit \<Rightarrow> term)" where
  "valtermify x \<equiv> (x, \<lambda>u. termify x)"

locale term_syntax
begin

notation App (infixl "<\<cdot>>" 70)
  and valapp (infixl "{\<cdot>}" 70)

end

interpretation term_syntax .

no_notation App (infixl "<\<cdot>>" 70)
  and valapp (infixl "{\<cdot>}" 70)


subsection {* Tools setup and evaluation *}

lemma eq_eq_TrueD:
  assumes "(x \<equiv> y) \<equiv> Trueprop True"
  shows "x \<equiv> y"
  using assms by simp

ML_file "Tools/code_evaluation.ML"

code_reserved Eval Code_Evaluation

setup {* Code_Evaluation.setup *}


subsection {* @{text term_of} instances *}

instantiation "fun" :: (typerep, typerep) term_of
begin

definition
  "term_of (f \<Colon> 'a \<Rightarrow> 'b) = Const (STR ''dummy_pattern'') (Typerep.Typerep (STR ''fun'')
     [Typerep.typerep TYPE('a), Typerep.typerep TYPE('b)])"

instance ..

end

instantiation String.literal :: term_of
begin

definition
  "term_of s = App (Const (STR ''STR'')
    (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''list'') [Typerep.Typerep (STR ''char'') []],
      Typerep.Typerep (STR ''String.literal'') []])) (term_of (String.explode s))"

instance ..

end


subsubsection {* Code generator setup *}

lemmas [code del] = term.rec term.case term.size
lemma [code, code del]: "HOL.equal (t1\<Colon>term) t2 \<longleftrightarrow> HOL.equal t1 t2" ..

lemma [code, code del]: "(term_of \<Colon> typerep \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(term_of \<Colon> term \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(term_of \<Colon> String.literal \<Rightarrow> term) = term_of" ..
lemma [code, code del]: "(Code_Evaluation.term_of \<Colon> 'a::{type, term_of} Predicate.pred \<Rightarrow> Code_Evaluation.term)
  = Code_Evaluation.term_of" ..
lemma [code, code del]: "(Code_Evaluation.term_of \<Colon> 'a::{type, term_of} Predicate.seq \<Rightarrow> Code_Evaluation.term)
  = Code_Evaluation.term_of" ..

lemma term_of_char [unfolded typerep_fun_def typerep_char_def typerep_nibble_def, code]:
  "Code_Evaluation.term_of c = (case c of Char x y \<Rightarrow>
   Code_Evaluation.App (Code_Evaluation.App
    (Code_Evaluation.Const (STR ''String.char.Char'') (TYPEREP(nibble \<Rightarrow> nibble \<Rightarrow> char)))
      (Code_Evaluation.term_of x)) (Code_Evaluation.term_of y))"
  by (subst term_of_anything) rule 

code_printing
  type_constructor "term" \<rightharpoonup> (Eval) "Term.term"
| constant Const \<rightharpoonup> (Eval) "Term.Const/ ((_), (_))"
| constant App \<rightharpoonup> (Eval) "Term.$/ ((_), (_))"
| constant Abs \<rightharpoonup> (Eval) "Term.Abs/ ((_), (_), (_))"
| constant Free \<rightharpoonup> (Eval) "Term.Free/ ((_), (_))"
| constant "term_of \<Colon> integer \<Rightarrow> term" \<rightharpoonup> (Eval) "HOLogic.mk'_number/ HOLogic.code'_integerT"
| constant "term_of \<Colon> String.literal \<Rightarrow> term" \<rightharpoonup> (Eval) "HOLogic.mk'_literal"

code_reserved Eval HOLogic


subsubsection {* Obfuscation *}

print_translation {*
  let
    val term = Const ("<TERM>", dummyT);
    fun tr1' _ [_, _] = term;
    fun tr2' _ [] = term;
  in
   [(@{const_syntax Const}, tr1'),
    (@{const_syntax App}, tr1'),
    (@{const_syntax dummy_term}, tr2')]
  end
*}


subsection {* Diagnostic *}

definition tracing :: "String.literal \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code del]: "tracing s x = x"

code_printing
  constant "tracing :: String.literal => 'a => 'a" \<rightharpoonup> (Eval) "Code'_Evaluation.tracing"


subsection {* Generic reification *}

ML_file "~~/src/HOL/Tools/reification.ML"


hide_const dummy_term valapp
hide_const (open) Const App Abs Free termify valtermify term_of tracing

end

