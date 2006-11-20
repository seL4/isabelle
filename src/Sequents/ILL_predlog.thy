(* $Id$ *)

theory ILL_predlog
imports ILL
begin

typedecl plf

consts
  conj :: "[plf,plf] => plf"   (infixr "&" 35)
  disj :: "[plf,plf] => plf"   (infixr "|" 35)
  impl :: "[plf,plf] => plf"   (infixr ">" 35)
  eq :: "[plf,plf] => plf"   (infixr "=" 35)
  "@NG" :: "plf => plf"   ("- _ " [50] 55)
  ff    :: "plf"

  PL    :: "plf => o"      ("[* / _ / *]" [] 100)

translations

  "[* A & B *]" == "[*A*] && [*B*]"
  "[* A | B *]" == "![*A*] ++ ![*B*]"
  "[* - A *]"   == "[*A > ff*]"
  "[* ff *]"    == "0"
  "[* A = B *]" => "[* (A > B) & (B > A) *]"

  "[* A > B *]" == "![*A*] -o [*B*]"

(* another translations for linear implication:
  "[* A > B *]" == "!([*A*] -o [*B*])" *)

method_setup auto1 =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (best_tac safe_cs)) *} ""
method_setup auto2 =
  {* Method.no_args (Method.SIMPLE_METHOD' HEADGOAL (best_tac power_cs)) *} ""

(* from [kleene 52] pp 118,119 *)

lemma k49a: "|- [* A > ( - ( - A)) *]"
  by auto1

lemma k49b: "|- [*( - ( - ( - A))) = ( - A)*]"
  by auto1

lemma k49c: "|- [* (A | - A) > ( - - A = A) *]"
  by auto1

lemma k50a: "|- [* - (A = - A) *]"
  by auto2

lemma k51a: "|- [* - - (A | - A) *]"
  by auto1

lemma k51b: "|- [* - - (- - A > A) *]"
  by auto2

lemma k56a: "|- [* (A | B) > - (- A & - B) *]"
  by auto1

lemma k56b: "|- [* (-A | B) > - (A & -B) *]"
  by auto1

lemma k57a: "|- [* (A & B) > - (-A | -B) *]"
  by auto1

lemma k57b: "|- [* (A & -B) > -(-A | B) *]"
  by auto2

lemma k58a: "|- [* (A > B) > - (A & -B) *]"
  by auto1

lemma k58b: "|- [* (A > -B) = -(A & B) *]"
  by auto1

lemma k58c: "|- [* - (A & B) = (- - A > - B) *]"
  by auto1

lemma k58d: "|- [* (- - A > - B) = - - (-A | -B) *]"
  by auto1

lemma k58e: "! [* - -B > B *] |- [* (- -A > B) = (A > B) *]"
  by auto1

lemma k58f: "! [* - -B > B *] |- [* (A > B) = - (A & -B) *]"
  by auto1

lemma k58g: "|- [* (- -A > B) > - (A & -B) *]"
  by auto1

lemma k59a: "|- [* (-A | B) > (A > B) *]"
  by auto1

lemma k59b: "|- [* (A > B) > - - (-A | B) *]"
  by auto2

lemma k59c: "|- [* (-A > B) > - -(A | B) *]"
  by auto2

lemma k60a: "|- [* (A & B) > - (A > -B) *]"
  by auto1

lemma k60b: "|- [* (A & -B) > - (A > B) *]"
  by auto1

lemma k60c: "|- [* ( - - A & B) > - (A > -B) *]"
  by auto1

lemma k60d: "|- [* (- - A & - B) = - (A > B) *]"
  by auto1

lemma k60e: "|- [* - (A > B) = - (-A | B) *]"
  by auto1

lemma k60f: "|- [* - (-A | B) = - - (A & -B) *]"
  by auto1

lemma k60g: "|- [* - - (A > B) = - (A & -B) *]"
  by auto2

lemma k60h: "|- [* - (A & -B) = (A > - -B) *]"
  by auto1

lemma k60i: "|- [* (A > - -B) = (- -A > - -B) *]"
  by auto1

lemma k61a: "|- [* (A | B) > (-A > B) *]"
  by auto1

lemma k61b: "|- [* - (A | B) = - (-A > B) *]"
  by auto2

lemma k62a: "|- [* (-A | -B) > - (A & B) *]"
  by auto1

end
