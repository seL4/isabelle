(* Author: Tobias Nipkow, Florian Haftmann, TU Muenchen *)

section \<open>Character and string types\<close>

theory String
imports Enum
begin

subsection \<open>Characters and strings\<close>

subsubsection \<open>Characters as finite algebraic type\<close>

typedef char = "{n::nat. n < 256}"
  morphisms nat_of_char Abs_char
proof
  show "Suc 0 \<in> {n. n < 256}" by simp
qed

definition char_of_nat :: "nat \<Rightarrow> char"
where
  "char_of_nat n = Abs_char (n mod 256)"

lemma char_cases [case_names char_of_nat, cases type: char]:
  "(\<And>n. c = char_of_nat n \<Longrightarrow> n < 256 \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases c) (simp add: char_of_nat_def)

lemma char_of_nat_of_char [simp]:
  "char_of_nat (nat_of_char c) = c"
  by (cases c) (simp add: char_of_nat_def Abs_char_inject Abs_char_inverse)

lemma inj_nat_of_char:
  "inj nat_of_char"
proof (rule injI)
  fix c d
  assume "nat_of_char c = nat_of_char d"
  then have "char_of_nat (nat_of_char c) = char_of_nat (nat_of_char d)"
    by simp
  then show "c = d"
    by simp
qed
  
lemma nat_of_char_eq_iff [simp]:
  "nat_of_char c = nat_of_char d \<longleftrightarrow> c = d"
  by (fact nat_of_char_inject)

lemma nat_of_char_of_nat [simp]:
  "nat_of_char (char_of_nat n) = n mod 256"
  by (cases "char_of_nat n") (simp add: char_of_nat_def Abs_char_inject Abs_char_inverse)

lemma char_of_nat_mod_256 [simp]:
  "char_of_nat (n mod 256) = char_of_nat n"
  by (cases "char_of_nat (n mod 256)") (simp add: char_of_nat_def)

lemma char_of_nat_quasi_inj [simp]:
  "char_of_nat m = char_of_nat n \<longleftrightarrow> m mod 256 = n mod 256"
  by (simp add: char_of_nat_def Abs_char_inject)

lemma inj_on_char_of_nat [simp]:
  "inj_on char_of_nat {..<256}"
  by (rule inj_onI) simp

lemma nat_of_char_mod_256 [simp]:
  "nat_of_char c mod 256 = nat_of_char c"
  by (cases c) simp

lemma nat_of_char_less_256 [simp]:
  "nat_of_char c < 256"
proof -
  have "nat_of_char c mod 256 < 256"
    by arith
  then show ?thesis by simp
qed

lemma UNIV_char_of_nat:
  "UNIV = char_of_nat ` {..<256}"
proof -
  { fix c
    have "c \<in> char_of_nat ` {..<256}"
      by (cases c) auto
  } then show ?thesis by auto
qed

lemma card_UNIV_char:
  "card (UNIV :: char set) = 256"
  by (auto simp add: UNIV_char_of_nat card_image)

lemma range_nat_of_char:
  "range nat_of_char = {..<256}"
  by (auto simp add: UNIV_char_of_nat image_image image_def)


subsubsection \<open>Character literals as variant of numerals\<close>

instantiation char :: zero
begin

definition zero_char :: char
  where "0 = char_of_nat 0"

instance ..

end

definition Char :: "num \<Rightarrow> char"
  where "Char k = char_of_nat (numeral k)"

code_datatype "0 :: char" Char

lemma nat_of_char_zero [simp]:
  "nat_of_char 0 = 0"
  by (simp add: zero_char_def)

lemma nat_of_char_Char [simp]:
  "nat_of_char (Char k) = numeral k mod 256"
  by (simp add: Char_def)

lemma Char_eq_Char_iff:
  "Char k = Char l \<longleftrightarrow> numeral k mod (256 :: nat) = numeral l mod 256" (is "?P \<longleftrightarrow> ?Q")
proof -
  have "?P \<longleftrightarrow> nat_of_char (Char k) = nat_of_char (Char l)"
    by (rule sym, rule inj_eq) (fact inj_nat_of_char)
  also have "nat_of_char (Char k) = nat_of_char (Char l) \<longleftrightarrow> ?Q"
    by (simp only: Char_def nat_of_char_of_nat)
  finally show ?thesis .
qed

lemma zero_eq_Char_iff:
  "0 = Char k \<longleftrightarrow> numeral k mod (256 :: nat) = 0"
  by (auto simp add: zero_char_def Char_def)

lemma Char_eq_zero_iff:
  "Char k = 0 \<longleftrightarrow> numeral k mod (256 :: nat) = 0"
  by (auto simp add: zero_char_def Char_def) 

simproc_setup char_eq
  ("Char m = Char n" | "Char m = 0" | "0 = Char n") = \<open>
  let
    val ss = put_simpset HOL_ss @{context}
      |> fold Simplifier.add_simp @{thms Char_eq_Char_iff zero_eq_Char_iff Char_eq_zero_iff cong_exp_iff_simps}
      |> simpset_of 
  in
    fn _ => fn ctxt => SOME o Simplifier.rewrite (put_simpset ss ctxt)
  end
\<close>

definition integer_of_char :: "char \<Rightarrow> integer"
where
  "integer_of_char = integer_of_nat \<circ> nat_of_char"

definition char_of_integer :: "integer \<Rightarrow> char"
where
  "char_of_integer = char_of_nat \<circ> nat_of_integer"

lemma integer_of_char_zero [simp, code]:
  "integer_of_char 0 = 0"
  by (simp add: integer_of_char_def integer_of_nat_def)

lemma integer_of_char_Char [simp]:
  "integer_of_char (Char k) = numeral k mod 256"
  by (simp only: integer_of_char_def integer_of_nat_def comp_apply nat_of_char_Char map_fun_def
    id_apply zmod_int modulo_integer.abs_eq [symmetric]) simp

lemma integer_of_char_Char_code [code]:
  "integer_of_char (Char k) = integer_of_num k mod 256"
  by simp
  
lemma nat_of_char_code [code]:
  "nat_of_char = nat_of_integer \<circ> integer_of_char"
  by (simp add: integer_of_char_def fun_eq_iff)

lemma char_of_nat_code [code]:
  "char_of_nat = char_of_integer \<circ> integer_of_nat"
  by (simp add: char_of_integer_def fun_eq_iff)

instantiation char :: equal
begin

definition equal_char
  where "equal_char (c :: char) d \<longleftrightarrow> c = d"

instance
  by standard (simp add: equal_char_def)

end

lemma equal_char_simps [code]:
  "HOL.equal (0::char) 0 \<longleftrightarrow> True"
  "HOL.equal (Char k) (Char l) \<longleftrightarrow> HOL.equal (numeral k mod 256 :: nat) (numeral l mod 256)"
  "HOL.equal 0 (Char k) \<longleftrightarrow> HOL.equal (numeral k mod 256 :: nat) 0"
  "HOL.equal (Char k) 0 \<longleftrightarrow> HOL.equal (numeral k mod 256 :: nat) 0"
  by (simp_all only: equal refl Char_eq_Char_iff zero_eq_Char_iff Char_eq_zero_iff)

syntax
  "_Char" :: "str_position \<Rightarrow> char"    ("CHR _")
  "_Char_ord" :: "num_const \<Rightarrow> char"   ("CHR _")

type_synonym string = "char list"

syntax
  "_String" :: "str_position => string"    ("_")

ML_file "Tools/string_syntax.ML"

instantiation char :: enum
begin

definition
  "Enum.enum = [0, CHR 0x01, CHR 0x02, CHR 0x03,
    CHR 0x04, CHR 0x05, CHR 0x06, CHR 0x07,
    CHR 0x08, CHR 0x09, CHR ''\<newline>'', CHR 0x0B,
    CHR 0x0C, CHR 0x0D, CHR 0x0E, CHR 0x0F,
    CHR 0x10, CHR 0x11, CHR 0x12, CHR 0x13,
    CHR 0x14, CHR 0x15, CHR 0x16, CHR 0x17,
    CHR 0x18, CHR 0x19, CHR 0x1A, CHR 0x1B,
    CHR 0x1C, CHR 0x1D, CHR 0x1E, CHR 0x1F,
    CHR '' '', CHR ''!'', CHR 0x22, CHR ''#'',
    CHR ''$'', CHR ''%'', CHR ''&'', CHR 0x27,
    CHR ''('', CHR '')'', CHR ''*'', CHR ''+'',
    CHR '','', CHR ''-'', CHR ''.'', CHR ''/'',
    CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'',
    CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'',
    CHR ''8'', CHR ''9'', CHR '':'', CHR '';'',
    CHR ''<'', CHR ''='', CHR ''>'', CHR ''?'',
    CHR ''@'', CHR ''A'', CHR ''B'', CHR ''C'',
    CHR ''D'', CHR ''E'', CHR ''F'', CHR ''G'',
    CHR ''H'', CHR ''I'', CHR ''J'', CHR ''K'',
    CHR ''L'', CHR ''M'', CHR ''N'', CHR ''O'',
    CHR ''P'', CHR ''Q'', CHR ''R'', CHR ''S'',
    CHR ''T'', CHR ''U'', CHR ''V'', CHR ''W'',
    CHR ''X'', CHR ''Y'', CHR ''Z'', CHR ''['',
    CHR 0x5C, CHR '']'', CHR ''^'', CHR ''_'',
    CHR 0x60, CHR ''a'', CHR ''b'', CHR ''c'',
    CHR ''d'', CHR ''e'', CHR ''f'', CHR ''g'',
    CHR ''h'', CHR ''i'', CHR ''j'', CHR ''k'',
    CHR ''l'', CHR ''m'', CHR ''n'', CHR ''o'',
    CHR ''p'', CHR ''q'', CHR ''r'', CHR ''s'',
    CHR ''t'', CHR ''u'', CHR ''v'', CHR ''w'',
    CHR ''x'', CHR ''y'', CHR ''z'', CHR ''{'',
    CHR ''|'', CHR ''}'', CHR ''~'', CHR 0x7F,
    CHR 0x80, CHR 0x81, CHR 0x82, CHR 0x83,
    CHR 0x84, CHR 0x85, CHR 0x86, CHR 0x87,
    CHR 0x88, CHR 0x89, CHR 0x8A, CHR 0x8B,
    CHR 0x8C, CHR 0x8D, CHR 0x8E, CHR 0x8F,
    CHR 0x90, CHR 0x91, CHR 0x92, CHR 0x93,
    CHR 0x94, CHR 0x95, CHR 0x96, CHR 0x97,
    CHR 0x98, CHR 0x99, CHR 0x9A, CHR 0x9B,
    CHR 0x9C, CHR 0x9D, CHR 0x9E, CHR 0x9F,
    CHR 0xA0, CHR 0xA1, CHR 0xA2, CHR 0xA3,
    CHR 0xA4, CHR 0xA5, CHR 0xA6, CHR 0xA7,
    CHR 0xA8, CHR 0xA9, CHR 0xAA, CHR 0xAB,
    CHR 0xAC, CHR 0xAD, CHR 0xAE, CHR 0xAF,
    CHR 0xB0, CHR 0xB1, CHR 0xB2, CHR 0xB3,
    CHR 0xB4, CHR 0xB5, CHR 0xB6, CHR 0xB7,
    CHR 0xB8, CHR 0xB9, CHR 0xBA, CHR 0xBB,
    CHR 0xBC, CHR 0xBD, CHR 0xBE, CHR 0xBF,
    CHR 0xC0, CHR 0xC1, CHR 0xC2, CHR 0xC3,
    CHR 0xC4, CHR 0xC5, CHR 0xC6, CHR 0xC7,
    CHR 0xC8, CHR 0xC9, CHR 0xCA, CHR 0xCB,
    CHR 0xCC, CHR 0xCD, CHR 0xCE, CHR 0xCF,
    CHR 0xD0, CHR 0xD1, CHR 0xD2, CHR 0xD3,
    CHR 0xD4, CHR 0xD5, CHR 0xD6, CHR 0xD7,
    CHR 0xD8, CHR 0xD9, CHR 0xDA, CHR 0xDB,
    CHR 0xDC, CHR 0xDD, CHR 0xDE, CHR 0xDF,
    CHR 0xE0, CHR 0xE1, CHR 0xE2, CHR 0xE3,
    CHR 0xE4, CHR 0xE5, CHR 0xE6, CHR 0xE7,
    CHR 0xE8, CHR 0xE9, CHR 0xEA, CHR 0xEB,
    CHR 0xEC, CHR 0xED, CHR 0xEE, CHR 0xEF,
    CHR 0xF0, CHR 0xF1, CHR 0xF2, CHR 0xF3,
    CHR 0xF4, CHR 0xF5, CHR 0xF6, CHR 0xF7,
    CHR 0xF8, CHR 0xF9, CHR 0xFA, CHR 0xFB,
    CHR 0xFC, CHR 0xFD, CHR 0xFE, CHR 0xFF]"

definition
  "Enum.enum_all P \<longleftrightarrow> list_all P (Enum.enum :: char list)"

definition
  "Enum.enum_ex P \<longleftrightarrow> list_ex P (Enum.enum :: char list)"

lemma enum_char_unfold:
  "Enum.enum = map char_of_nat [0..<256]"
proof -
  have *: "Suc (Suc 0) = 2" by simp
  have "map nat_of_char Enum.enum = [0..<256]"
    by (simp add: enum_char_def upt_conv_Cons_Cons *)
  then have "map char_of_nat (map nat_of_char Enum.enum) =
    map char_of_nat [0..<256]" by simp
  then show ?thesis by (simp add: comp_def)
qed

instance proof
  show UNIV: "UNIV = set (Enum.enum :: char list)"
    by (simp add: enum_char_unfold UNIV_char_of_nat atLeast0LessThan)
  show "distinct (Enum.enum :: char list)"
    by (auto simp add: enum_char_unfold distinct_map intro: inj_onI)
  show "\<And>P. Enum.enum_all P \<longleftrightarrow> Ball (UNIV :: char set) P"
    by (simp add: UNIV enum_all_char_def list_all_iff)
  show "\<And>P. Enum.enum_ex P \<longleftrightarrow> Bex (UNIV :: char set) P"
    by (simp add: UNIV enum_ex_char_def list_ex_iff)
qed

end

lemma char_of_integer_code [code]:
  "char_of_integer n = Enum.enum ! (nat_of_integer n mod 256)"
  by (simp add: char_of_integer_def enum_char_unfold)


subsection \<open>Strings as dedicated type\<close>

typedef literal = "UNIV :: string set"
  morphisms explode STR ..

setup_lifting type_definition_literal

lemma STR_inject' [simp]:
  "STR s = STR t \<longleftrightarrow> s = t"
  by transfer rule

definition implode :: "string \<Rightarrow> String.literal"
where
  [code del]: "implode = STR"

instantiation literal :: size
begin

definition size_literal :: "literal \<Rightarrow> nat"
where
  [code]: "size_literal (s::literal) = 0"

instance ..

end

instantiation literal :: equal
begin

lift_definition equal_literal :: "literal \<Rightarrow> literal \<Rightarrow> bool" is "op =" .

instance by intro_classes (transfer, simp)

end

declare equal_literal.rep_eq[code]

lemma [code nbe]:
  fixes s :: "String.literal"
  shows "HOL.equal s s \<longleftrightarrow> True"
  by (simp add: equal)

lifting_update literal.lifting
lifting_forget literal.lifting

  
subsection \<open>Dedicated conversion for generated computations\<close>

definition char_of_num :: "num \<Rightarrow> char"
  where "char_of_num = char_of_nat o nat_of_num"

lemma [code_computation_unfold]:
  "Char = char_of_num"
  by (simp add: fun_eq_iff char_of_num_def nat_of_num_numeral Char_def)


subsection \<open>Code generator\<close>

ML_file "Tools/string_code.ML"

code_reserved SML string
code_reserved OCaml string
code_reserved Scala string

code_printing
  type_constructor literal \<rightharpoonup>
    (SML) "string"
    and (OCaml) "string"
    and (Haskell) "String"
    and (Scala) "String"

setup \<open>
  fold String_Code.add_literal_string ["SML", "OCaml", "Haskell", "Scala"]
\<close>

code_printing
  class_instance literal :: equal \<rightharpoonup>
    (Haskell) -
| constant "HOL.equal :: literal \<Rightarrow> literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) = _)"
    and (OCaml) "!((_ : string) = _)"
    and (Haskell) infix 4 "=="
    and (Scala) infixl 5 "=="

setup \<open>Sign.map_naming (Name_Space.mandatory_path "Code")\<close>

definition abort :: "literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
where [simp, code del]: "abort _ f = f ()"

lemma abort_cong: "msg = msg' ==> Code.abort msg f = Code.abort msg' f"
by simp

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm Code.abort_cong})\<close>

code_printing constant Code.abort \<rightharpoonup>
    (SML) "!(raise/ Fail/ _)"
    and (OCaml) "failwith"
    and (Haskell) "!(error/ ::/ forall a./ String -> (() -> a) -> a)"
    and (Scala) "!{/ sys.error((_));/  ((_)).apply(())/ }"

hide_type (open) literal

hide_const (open) implode explode

end
