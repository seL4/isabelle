(* Author: Tobias Nipkow, Florian Haftmann, TU Muenchen *)

header {* Character and string types *}

theory String
imports List
uses
  "Tools/string_syntax.ML"
  ("Tools/string_code.ML")
begin

subsection {* Characters *}

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF

lemma UNIV_nibble:
  "UNIV = {Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF}" (is "_ = ?A")
proof (rule UNIV_eq_I)
  fix x show "x \<in> ?A" by (cases x) simp_all
qed

instance nibble :: finite
  by default (simp add: UNIV_nibble)

datatype char = Char nibble nibble
  -- "Note: canonical order of character encoding coincides with standard term ordering"

lemma UNIV_char:
  "UNIV = image (split Char) (UNIV \<times> UNIV)"
proof (rule UNIV_eq_I)
  fix x show "x \<in> image (split Char) (UNIV \<times> UNIV)" by (cases x) auto
qed

instance char :: finite
  by default (simp add: UNIV_char)

lemma size_char [code, simp]:
  "size (c::char) = 0" by (cases c) simp

lemma char_size [code, simp]:
  "char_size (c::char) = 0" by (cases c) simp

primrec nibble_pair_of_char :: "char \<Rightarrow> nibble \<times> nibble" where
  "nibble_pair_of_char (Char n m) = (n, m)"

declare nibble_pair_of_char.simps [code del]

setup {*
let
  val nibbles = map (Thm.cterm_of @{theory} o HOLogic.mk_nibble) (0 upto 15);
  val thms = map_product
   (fn n => fn m => Drule.instantiate' [] [SOME n, SOME m] @{thm nibble_pair_of_char.simps})
      nibbles nibbles;
in
  PureThy.note_thmss Thm.generated_theoremK [((Binding.name "nibble_pair_of_char_simps", []), [(thms, [])])]
  #-> (fn [(_, thms)] => fold_rev Code.add_eqn thms)
end
*}

lemma char_case_nibble_pair [code, code inline]:
  "char_case f = split f o nibble_pair_of_char"
  by (simp add: expand_fun_eq split: char.split)

lemma char_rec_nibble_pair [code, code inline]:
  "char_rec f = split f o nibble_pair_of_char"
  unfolding char_case_nibble_pair [symmetric]
  by (simp add: expand_fun_eq split: char.split)

syntax
  "_Char" :: "xstr => char"    ("CHR _")


subsection {* Strings *}

types string = "char list"

syntax
  "_String" :: "xstr => string"    ("_")

setup StringSyntax.setup


subsection {* Strings as dedicated datatype *}

datatype message_string = STR string

lemmas [code del] =
  message_string.recs message_string.cases

lemma [code]: "size (s\<Colon>message_string) = 0"
  by (cases s) simp_all

lemma [code]: "message_string_size (s\<Colon>message_string) = 0"
  by (cases s) simp_all


subsection {* Code generator *}

use "Tools/string_code.ML"

code_type message_string
  (SML "string")
  (OCaml "string")
  (Haskell "String")

setup {*
  fold String_Code.add_literal_message ["SML", "OCaml", "Haskell"]
*}

code_instance message_string :: eq
  (Haskell -)

code_const "eq_class.eq \<Colon> message_string \<Rightarrow> message_string \<Rightarrow> bool"
  (SML "!((_ : string) = _)")
  (OCaml "!((_ : string) = _)")
  (Haskell infixl 4 "==")

code_reserved SML string
code_reserved OCaml string


types_code
  "char" ("string")
attach (term_of) {*
val term_of_char = HOLogic.mk_char o ord;
*}
attach (test) {*
fun gen_char i =
  let val j = random_range (ord "a") (Int.min (ord "a" + i, ord "z"))
  in (chr j, fn () => HOLogic.mk_char j) end;
*}

setup {*
let

fun char_codegen thy defs dep thyname b t gr =
  let
    val i = HOLogic.dest_char t;
    val (_, gr') = Codegen.invoke_tycodegen thy defs dep thyname false
      (fastype_of t) gr;
  in SOME (Codegen.str (ML_Syntax.print_string (chr i)), gr')
  end handle TERM _ => NONE;

in Codegen.add_codegen "char_codegen" char_codegen end
*}

end