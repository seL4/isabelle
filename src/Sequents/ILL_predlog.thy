theory ILL_predlog
imports ILL
begin

typedecl plf

consts
  conj :: "[plf,plf] \<Rightarrow> plf"   (infixr \<open>&\<close> 35)
  disj :: "[plf,plf] \<Rightarrow> plf"   (infixr \<open>|\<close> 35)
  impl :: "[plf,plf] \<Rightarrow> plf"   (infixr \<open>>\<close> 35)
  eq :: "[plf,plf] \<Rightarrow> plf"   (infixr \<open>=\<close> 35)
  ff :: "plf"    (\<open>ff\<close>)

  PL    :: "plf \<Rightarrow> o"      (\<open>[* / _ / *]\<close> [] 100)

syntax
  "_NG" :: "plf \<Rightarrow> plf"   (\<open>- _ \<close> [50] 55)

translations
  "[* A & B *]" \<rightleftharpoons> "[*A*] && [*B*]"
  "[* A | B *]" \<rightleftharpoons> "![*A*] ++ ![*B*]"
  "[* - A *]" \<rightleftharpoons> "[*A > ff*]"
  "[* ff *]" \<rightleftharpoons> "0"
  "[* A = B *]" \<rightharpoonup> "[* (A > B) & (B > A) *]"

  "[* A > B *]" \<rightleftharpoons> "![*A*] -o [*B*]"

(* another translations for linear implication:
  "[* A > B *]" == "!([*A*] -o [*B*])" *)

(* from [kleene 52] pp 118,119 *)

lemma k49a: "\<turnstile> [* A > ( - ( - A)) *]"
  by best_safe

lemma k49b: "\<turnstile> [*( - ( - ( - A))) = ( - A)*]"
  by best_safe

lemma k49c: "\<turnstile> [* (A | - A) > ( - - A = A) *]"
  by best_safe

lemma k50a: "\<turnstile> [* - (A = - A) *]"
  by best_power

lemma k51a: "\<turnstile> [* - - (A | - A) *]"
  by best_safe

lemma k51b: "\<turnstile> [* - - (- - A > A) *]"
  by best_power

lemma k56a: "\<turnstile> [* (A | B) > - (- A & - B) *]"
  by best_safe

lemma k56b: "\<turnstile> [* (-A | B) > - (A & -B) *]"
  by best_safe

lemma k57a: "\<turnstile> [* (A & B) > - (-A | -B) *]"
  by best_safe

lemma k57b: "\<turnstile> [* (A & -B) > -(-A | B) *]"
  by best_power

lemma k58a: "\<turnstile> [* (A > B) > - (A & -B) *]"
  by best_safe

lemma k58b: "\<turnstile> [* (A > -B) = -(A & B) *]"
  by best_safe

lemma k58c: "\<turnstile> [* - (A & B) = (- - A > - B) *]"
  by best_safe

lemma k58d: "\<turnstile> [* (- - A > - B) = - - (-A | -B) *]"
  by best_safe

lemma k58e: "! [* - -B > B *] \<turnstile> [* (- -A > B) = (A > B) *]"
  by best_safe

lemma k58f: "! [* - -B > B *] \<turnstile> [* (A > B) = - (A & -B) *]"
  by best_safe

lemma k58g: "\<turnstile> [* (- -A > B) > - (A & -B) *]"
  by best_safe

lemma k59a: "\<turnstile> [* (-A | B) > (A > B) *]"
  by best_safe

lemma k59b: "\<turnstile> [* (A > B) > - - (-A | B) *]"
  by best_power

lemma k59c: "\<turnstile> [* (-A > B) > - -(A | B) *]"
  by best_power

lemma k60a: "\<turnstile> [* (A & B) > - (A > -B) *]"
  by best_safe

lemma k60b: "\<turnstile> [* (A & -B) > - (A > B) *]"
  by best_safe

lemma k60c: "\<turnstile> [* ( - - A & B) > - (A > -B) *]"
  by best_safe

lemma k60d: "\<turnstile> [* (- - A & - B) = - (A > B) *]"
  by best_safe

lemma k60e: "\<turnstile> [* - (A > B) = - (-A | B) *]"
  by best_safe

lemma k60f: "\<turnstile> [* - (-A | B) = - - (A & -B) *]"
  by best_safe

lemma k60g: "\<turnstile> [* - - (A > B) = - (A & -B) *]"
  by best_power

lemma k60h: "\<turnstile> [* - (A & -B) = (A > - -B) *]"
  by best_safe

lemma k60i: "\<turnstile> [* (A > - -B) = (- -A > - -B) *]"
  by best_safe

lemma k61a: "\<turnstile> [* (A | B) > (-A > B) *]"
  by best_safe

lemma k61b: "\<turnstile> [* - (A | B) = - (-A > B) *]"
  by best_power

lemma k62a: "\<turnstile> [* (-A | -B) > - (A & B) *]"
  by best_safe

end
