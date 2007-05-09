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
  ff    :: "plf"

  PL    :: "plf => o"      ("[* / _ / *]" [] 100)

syntax
  "_NG" :: "plf => plf"   ("- _ " [50] 55)

translations

  "[* A & B *]" == "[*A*] && [*B*]"
  "[* A | B *]" == "![*A*] ++ ![*B*]"
  "[* - A *]"   == "[*A > ff*]"
  "[* ff *]"    == "0"
  "[* A = B *]" => "[* (A > B) & (B > A) *]"

  "[* A > B *]" == "![*A*] -o [*B*]"

(* another translations for linear implication:
  "[* A > B *]" == "!([*A*] -o [*B*])" *)

(* from [kleene 52] pp 118,119 *)

lemma k49a: "|- [* A > ( - ( - A)) *]"
  by best_safe

lemma k49b: "|- [*( - ( - ( - A))) = ( - A)*]"
  by best_safe

lemma k49c: "|- [* (A | - A) > ( - - A = A) *]"
  by best_safe

lemma k50a: "|- [* - (A = - A) *]"
  by best_power

lemma k51a: "|- [* - - (A | - A) *]"
  by best_safe

lemma k51b: "|- [* - - (- - A > A) *]"
  by best_power

lemma k56a: "|- [* (A | B) > - (- A & - B) *]"
  by best_safe

lemma k56b: "|- [* (-A | B) > - (A & -B) *]"
  by best_safe

lemma k57a: "|- [* (A & B) > - (-A | -B) *]"
  by best_safe

lemma k57b: "|- [* (A & -B) > -(-A | B) *]"
  by best_power

lemma k58a: "|- [* (A > B) > - (A & -B) *]"
  by best_safe

lemma k58b: "|- [* (A > -B) = -(A & B) *]"
  by best_safe

lemma k58c: "|- [* - (A & B) = (- - A > - B) *]"
  by best_safe

lemma k58d: "|- [* (- - A > - B) = - - (-A | -B) *]"
  by best_safe

lemma k58e: "! [* - -B > B *] |- [* (- -A > B) = (A > B) *]"
  by best_safe

lemma k58f: "! [* - -B > B *] |- [* (A > B) = - (A & -B) *]"
  by best_safe

lemma k58g: "|- [* (- -A > B) > - (A & -B) *]"
  by best_safe

lemma k59a: "|- [* (-A | B) > (A > B) *]"
  by best_safe

lemma k59b: "|- [* (A > B) > - - (-A | B) *]"
  by best_power

lemma k59c: "|- [* (-A > B) > - -(A | B) *]"
  by best_power

lemma k60a: "|- [* (A & B) > - (A > -B) *]"
  by best_safe

lemma k60b: "|- [* (A & -B) > - (A > B) *]"
  by best_safe

lemma k60c: "|- [* ( - - A & B) > - (A > -B) *]"
  by best_safe

lemma k60d: "|- [* (- - A & - B) = - (A > B) *]"
  by best_safe

lemma k60e: "|- [* - (A > B) = - (-A | B) *]"
  by best_safe

lemma k60f: "|- [* - (-A | B) = - - (A & -B) *]"
  by best_safe

lemma k60g: "|- [* - - (A > B) = - (A & -B) *]"
  by best_power

lemma k60h: "|- [* - (A & -B) = (A > - -B) *]"
  by best_safe

lemma k60i: "|- [* (A > - -B) = (- -A > - -B) *]"
  by best_safe

lemma k61a: "|- [* (A | B) > (-A > B) *]"
  by best_safe

lemma k61b: "|- [* - (A | B) = - (-A > B) *]"
  by best_power

lemma k62a: "|- [* (-A | -B) > - (A & B) *]"
  by best_safe

end
