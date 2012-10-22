(* Author: Tobias Nipkow, Florian Haftmann, TU Muenchen *)

header {* Character and string types *}

theory String
imports List Enum
begin

subsection {* Characters and strings *}

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF

lemma UNIV_nibble:
  "UNIV = {Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF}" (is "_ = ?A")
proof (rule UNIV_eq_I)
  fix x show "x \<in> ?A" by (cases x) simp_all
qed

lemma size_nibble [code, simp]:
  "size (x::nibble) = 0" by (cases x) simp_all

lemma nibble_size [code, simp]:
  "nibble_size (x::nibble) = 0" by (cases x) simp_all

instantiation nibble :: enum
begin

definition
  "Enum.enum = [Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF]"

definition
  "Enum.enum_all P \<longleftrightarrow> P Nibble0 \<and> P Nibble1 \<and> P Nibble2 \<and> P Nibble3 \<and> P Nibble4 \<and> P Nibble5 \<and> P Nibble6 \<and> P Nibble7
     \<and> P Nibble8 \<and> P Nibble9 \<and> P NibbleA \<and> P NibbleB \<and> P NibbleC \<and> P NibbleD \<and> P NibbleE \<and> P NibbleF"

definition
  "Enum.enum_ex P \<longleftrightarrow> P Nibble0 \<or> P Nibble1 \<or> P Nibble2 \<or> P Nibble3 \<or> P Nibble4 \<or> P Nibble5 \<or> P Nibble6 \<or> P Nibble7
     \<or> P Nibble8 \<or> P Nibble9 \<or> P NibbleA \<or> P NibbleB \<or> P NibbleC \<or> P NibbleD \<or> P NibbleE \<or> P NibbleF"

instance proof
qed (simp_all only: enum_nibble_def enum_all_nibble_def enum_ex_nibble_def UNIV_nibble, simp_all)

end

lemma card_UNIV_nibble:
  "card (UNIV :: nibble set) = 16"
  by (simp add: card_UNIV_length_enum enum_nibble_def)

datatype char = Char nibble nibble
  -- "Note: canonical order of character encoding coincides with standard term ordering"

syntax
  "_Char" :: "str_position => char"    ("CHR _")

type_synonym string = "char list"

syntax
  "_String" :: "str_position => string"    ("_")

ML_file "Tools/string_syntax.ML"
setup String_Syntax.setup

lemma UNIV_char:
  "UNIV = image (split Char) (UNIV \<times> UNIV)"
proof (rule UNIV_eq_I)
  fix x show "x \<in> image (split Char) (UNIV \<times> UNIV)" by (cases x) auto
qed

lemma size_char [code, simp]:
  "size (c::char) = 0" by (cases c) simp

lemma char_size [code, simp]:
  "char_size (c::char) = 0" by (cases c) simp

instantiation char :: enum
begin

definition
  "Enum.enum = [Char Nibble0 Nibble0, Char Nibble0 Nibble1, Char Nibble0 Nibble2,
  Char Nibble0 Nibble3, Char Nibble0 Nibble4, Char Nibble0 Nibble5,
  Char Nibble0 Nibble6, Char Nibble0 Nibble7, Char Nibble0 Nibble8,
  Char Nibble0 Nibble9, Char Nibble0 NibbleA, Char Nibble0 NibbleB,
  Char Nibble0 NibbleC, Char Nibble0 NibbleD, Char Nibble0 NibbleE,
  Char Nibble0 NibbleF, Char Nibble1 Nibble0, Char Nibble1 Nibble1,
  Char Nibble1 Nibble2, Char Nibble1 Nibble3, Char Nibble1 Nibble4,
  Char Nibble1 Nibble5, Char Nibble1 Nibble6, Char Nibble1 Nibble7,
  Char Nibble1 Nibble8, Char Nibble1 Nibble9, Char Nibble1 NibbleA,
  Char Nibble1 NibbleB, Char Nibble1 NibbleC, Char Nibble1 NibbleD,
  Char Nibble1 NibbleE, Char Nibble1 NibbleF, CHR '' '', CHR ''!'',
  Char Nibble2 Nibble2, CHR ''#'', CHR ''$'', CHR ''%'', CHR ''&'',
  Char Nibble2 Nibble7, CHR ''('', CHR '')'', CHR ''*'', CHR ''+'', CHR '','',
  CHR ''-'', CHR ''.'', CHR ''/'', CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'',
  CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9'', CHR '':'',
  CHR '';'', CHR ''<'', CHR ''='', CHR ''>'', CHR ''?'', CHR ''@'', CHR ''A'',
  CHR ''B'', CHR ''C'', CHR ''D'', CHR ''E'', CHR ''F'', CHR ''G'', CHR ''H'',
  CHR ''I'', CHR ''J'', CHR ''K'', CHR ''L'', CHR ''M'', CHR ''N'', CHR ''O'',
  CHR ''P'', CHR ''Q'', CHR ''R'', CHR ''S'', CHR ''T'', CHR ''U'', CHR ''V'',
  CHR ''W'', CHR ''X'', CHR ''Y'', CHR ''Z'', CHR ''['', Char Nibble5 NibbleC,
  CHR '']'', CHR ''^'', CHR ''_'', Char Nibble6 Nibble0, CHR ''a'', CHR ''b'',
  CHR ''c'', CHR ''d'', CHR ''e'', CHR ''f'', CHR ''g'', CHR ''h'', CHR ''i'',
  CHR ''j'', CHR ''k'', CHR ''l'', CHR ''m'', CHR ''n'', CHR ''o'', CHR ''p'',
  CHR ''q'', CHR ''r'', CHR ''s'', CHR ''t'', CHR ''u'', CHR ''v'', CHR ''w'',
  CHR ''x'', CHR ''y'', CHR ''z'', CHR ''{'', CHR ''|'', CHR ''}'', CHR ''~'',
  Char Nibble7 NibbleF, Char Nibble8 Nibble0, Char Nibble8 Nibble1,
  Char Nibble8 Nibble2, Char Nibble8 Nibble3, Char Nibble8 Nibble4,
  Char Nibble8 Nibble5, Char Nibble8 Nibble6, Char Nibble8 Nibble7,
  Char Nibble8 Nibble8, Char Nibble8 Nibble9, Char Nibble8 NibbleA,
  Char Nibble8 NibbleB, Char Nibble8 NibbleC, Char Nibble8 NibbleD,
  Char Nibble8 NibbleE, Char Nibble8 NibbleF, Char Nibble9 Nibble0,
  Char Nibble9 Nibble1, Char Nibble9 Nibble2, Char Nibble9 Nibble3,
  Char Nibble9 Nibble4, Char Nibble9 Nibble5, Char Nibble9 Nibble6,
  Char Nibble9 Nibble7, Char Nibble9 Nibble8, Char Nibble9 Nibble9,
  Char Nibble9 NibbleA, Char Nibble9 NibbleB, Char Nibble9 NibbleC,
  Char Nibble9 NibbleD, Char Nibble9 NibbleE, Char Nibble9 NibbleF,
  Char NibbleA Nibble0, Char NibbleA Nibble1, Char NibbleA Nibble2,
  Char NibbleA Nibble3, Char NibbleA Nibble4, Char NibbleA Nibble5,
  Char NibbleA Nibble6, Char NibbleA Nibble7, Char NibbleA Nibble8,
  Char NibbleA Nibble9, Char NibbleA NibbleA, Char NibbleA NibbleB,
  Char NibbleA NibbleC, Char NibbleA NibbleD, Char NibbleA NibbleE,
  Char NibbleA NibbleF, Char NibbleB Nibble0, Char NibbleB Nibble1,
  Char NibbleB Nibble2, Char NibbleB Nibble3, Char NibbleB Nibble4,
  Char NibbleB Nibble5, Char NibbleB Nibble6, Char NibbleB Nibble7,
  Char NibbleB Nibble8, Char NibbleB Nibble9, Char NibbleB NibbleA,
  Char NibbleB NibbleB, Char NibbleB NibbleC, Char NibbleB NibbleD,
  Char NibbleB NibbleE, Char NibbleB NibbleF, Char NibbleC Nibble0,
  Char NibbleC Nibble1, Char NibbleC Nibble2, Char NibbleC Nibble3,
  Char NibbleC Nibble4, Char NibbleC Nibble5, Char NibbleC Nibble6,
  Char NibbleC Nibble7, Char NibbleC Nibble8, Char NibbleC Nibble9,
  Char NibbleC NibbleA, Char NibbleC NibbleB, Char NibbleC NibbleC,
  Char NibbleC NibbleD, Char NibbleC NibbleE, Char NibbleC NibbleF,
  Char NibbleD Nibble0, Char NibbleD Nibble1, Char NibbleD Nibble2,
  Char NibbleD Nibble3, Char NibbleD Nibble4, Char NibbleD Nibble5,
  Char NibbleD Nibble6, Char NibbleD Nibble7, Char NibbleD Nibble8,
  Char NibbleD Nibble9, Char NibbleD NibbleA, Char NibbleD NibbleB,
  Char NibbleD NibbleC, Char NibbleD NibbleD, Char NibbleD NibbleE,
  Char NibbleD NibbleF, Char NibbleE Nibble0, Char NibbleE Nibble1,
  Char NibbleE Nibble2, Char NibbleE Nibble3, Char NibbleE Nibble4,
  Char NibbleE Nibble5, Char NibbleE Nibble6, Char NibbleE Nibble7,
  Char NibbleE Nibble8, Char NibbleE Nibble9, Char NibbleE NibbleA,
  Char NibbleE NibbleB, Char NibbleE NibbleC, Char NibbleE NibbleD,
  Char NibbleE NibbleE, Char NibbleE NibbleF, Char NibbleF Nibble0,
  Char NibbleF Nibble1, Char NibbleF Nibble2, Char NibbleF Nibble3,
  Char NibbleF Nibble4, Char NibbleF Nibble5, Char NibbleF Nibble6,
  Char NibbleF Nibble7, Char NibbleF Nibble8, Char NibbleF Nibble9,
  Char NibbleF NibbleA, Char NibbleF NibbleB, Char NibbleF NibbleC,
  Char NibbleF NibbleD, Char NibbleF NibbleE, Char NibbleF NibbleF]"

definition
  "Enum.enum_all P \<longleftrightarrow> list_all P (Enum.enum :: char list)"

definition
  "Enum.enum_ex P \<longleftrightarrow> list_ex P (Enum.enum :: char list)"

instance proof
  have enum: "(Enum.enum :: char list) = map (split Char) (List.product Enum.enum Enum.enum)"
    by (simp add: enum_char_def enum_nibble_def)
  show UNIV: "UNIV = set (Enum.enum :: char list)"
    by (simp add: enum UNIV_char product_list_set enum_UNIV)
  show "distinct (Enum.enum :: char list)"
    by (auto intro: inj_onI simp add: enum distinct_map distinct_product enum_distinct)
  show "\<And>P. Enum.enum_all P \<longleftrightarrow> Ball (UNIV :: char set) P"
    by (simp add: UNIV enum_all_char_def list_all_iff)
  show "\<And>P. Enum.enum_ex P \<longleftrightarrow> Bex (UNIV :: char set) P"
    by (simp add: UNIV enum_ex_char_def list_ex_iff)
qed

end

lemma card_UNIV_char:
  "card (UNIV :: char set) = 256"
  by (simp add: card_UNIV_length_enum enum_char_def)

primrec nibble_pair_of_char :: "char \<Rightarrow> nibble \<times> nibble" where
  "nibble_pair_of_char (Char n m) = (n, m)"

setup {*
let
  val nibbles = map_range (Thm.cterm_of @{theory} o HOLogic.mk_nibble) 16;
  val thms = map_product
   (fn n => fn m => Drule.instantiate' [] [SOME n, SOME m] @{thm nibble_pair_of_char.simps})
      nibbles nibbles;
in
  Global_Theory.note_thmss ""
    [((@{binding nibble_pair_of_char_simps}, []), [(thms, [])])]
  #-> (fn [(_, thms)] => fold_rev Code.add_eqn thms)
end
*}

lemma char_case_nibble_pair [code, code_unfold]:
  "char_case f = split f o nibble_pair_of_char"
  by (simp add: fun_eq_iff split: char.split)

lemma char_rec_nibble_pair [code, code_unfold]:
  "char_rec f = split f o nibble_pair_of_char"
  unfolding char_case_nibble_pair [symmetric]
  by (simp add: fun_eq_iff split: char.split)


subsection {* Strings as dedicated type *}

typedef literal = "UNIV :: string set"
  morphisms explode STR ..

instantiation literal :: size
begin

definition size_literal :: "literal \<Rightarrow> nat"
where
  [code]: "size_literal (s\<Colon>literal) = 0"

instance ..

end

instantiation literal :: equal
begin

definition equal_literal :: "literal \<Rightarrow> literal \<Rightarrow> bool"
where
  "equal_literal s1 s2 \<longleftrightarrow> explode s1 = explode s2"

instance
proof
qed (auto simp add: equal_literal_def explode_inject)

end

lemma STR_inject' [simp]: "(STR xs = STR ys) = (xs = ys)"
by(simp add: STR_inject)


subsection {* Code generator *}

ML_file "Tools/string_code.ML"

code_reserved SML string
code_reserved OCaml string
code_reserved Scala string

code_type literal
  (SML "string")
  (OCaml "string")
  (Haskell "String")
  (Scala "String")

setup {*
  fold String_Code.add_literal_string ["SML", "OCaml", "Haskell", "Scala"]
*}

code_instance literal :: equal
  (Haskell -)

code_const "HOL.equal \<Colon> literal \<Rightarrow> literal \<Rightarrow> bool"
  (SML "!((_ : string) = _)")
  (OCaml "!((_ : string) = _)")
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")

hide_type (open) literal

end

