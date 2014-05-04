(* Author: Tobias Nipkow, Florian Haftmann, TU Muenchen *)

header {* Character and string types *}

theory String
imports Enum
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
  "size_nibble (x::nibble) = 0"
  "size (x::nibble) = 0"
  by (cases x, simp_all)+

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

primrec nat_of_nibble :: "nibble \<Rightarrow> nat"
where
  "nat_of_nibble Nibble0 = 0"
| "nat_of_nibble Nibble1 = 1"
| "nat_of_nibble Nibble2 = 2"
| "nat_of_nibble Nibble3 = 3"
| "nat_of_nibble Nibble4 = 4"
| "nat_of_nibble Nibble5 = 5"
| "nat_of_nibble Nibble6 = 6"
| "nat_of_nibble Nibble7 = 7"
| "nat_of_nibble Nibble8 = 8"
| "nat_of_nibble Nibble9 = 9"
| "nat_of_nibble NibbleA = 10"
| "nat_of_nibble NibbleB = 11"
| "nat_of_nibble NibbleC = 12"
| "nat_of_nibble NibbleD = 13"
| "nat_of_nibble NibbleE = 14"
| "nat_of_nibble NibbleF = 15"

definition nibble_of_nat :: "nat \<Rightarrow> nibble" where
  "nibble_of_nat n = Enum.enum ! (n mod 16)"

lemma nibble_of_nat_simps [simp]:
  "nibble_of_nat  0 = Nibble0"
  "nibble_of_nat  1 = Nibble1"
  "nibble_of_nat  2 = Nibble2"
  "nibble_of_nat  3 = Nibble3"
  "nibble_of_nat  4 = Nibble4"
  "nibble_of_nat  5 = Nibble5"
  "nibble_of_nat  6 = Nibble6"
  "nibble_of_nat  7 = Nibble7"
  "nibble_of_nat  8 = Nibble8"
  "nibble_of_nat  9 = Nibble9"
  "nibble_of_nat 10 = NibbleA"
  "nibble_of_nat 11 = NibbleB"
  "nibble_of_nat 12 = NibbleC"
  "nibble_of_nat 13 = NibbleD"
  "nibble_of_nat 14 = NibbleE"
  "nibble_of_nat 15 = NibbleF"
  unfolding nibble_of_nat_def by (simp_all add: enum_nibble_def)

lemma nibble_of_nat_of_nibble [simp]:
  "nibble_of_nat (nat_of_nibble x) = x"
  by (cases x) (simp_all add: nibble_of_nat_def enum_nibble_def)

lemma nat_of_nibble_of_nat [simp]:
  "nat_of_nibble (nibble_of_nat n) = n mod 16"
  by (cases "nibble_of_nat n")
     (simp_all add: nibble_of_nat_def enum_nibble_def nth_equal_first_eq nth_non_equal_first_eq, arith)

lemma inj_nat_of_nibble:
  "inj nat_of_nibble"
  by (rule inj_on_inverseI) (rule nibble_of_nat_of_nibble)

lemma nat_of_nibble_eq_iff:
  "nat_of_nibble x = nat_of_nibble y \<longleftrightarrow> x = y"
  by (rule inj_eq) (rule inj_nat_of_nibble)

lemma nat_of_nibble_less_16:
  "nat_of_nibble x < 16"
  by (cases x) auto

lemma nibble_of_nat_mod_16:
  "nibble_of_nat (n mod 16) = nibble_of_nat n"
  by (simp add: nibble_of_nat_def)

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
  "size_char (c::char) = 0"
  "size (c::char) = 0"
  by (cases c, simp)+

instantiation char :: enum
begin

definition
  "Enum.enum = [Char Nibble0 Nibble0, Char Nibble0 Nibble1, Char Nibble0 Nibble2,
  Char Nibble0 Nibble3, Char Nibble0 Nibble4, Char Nibble0 Nibble5,
  Char Nibble0 Nibble6, Char Nibble0 Nibble7, Char Nibble0 Nibble8,
  Char Nibble0 Nibble9, CHR ''\<newline>'', Char Nibble0 NibbleB,
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

lemma enum_char_product_enum_nibble:
  "(Enum.enum :: char list) = map (split Char) (List.product Enum.enum Enum.enum)"
  by (simp add: enum_char_def enum_nibble_def)

instance proof
  show UNIV: "UNIV = set (Enum.enum :: char list)"
    by (simp add: enum_char_product_enum_nibble UNIV_char product_list_set enum_UNIV)
  show "distinct (Enum.enum :: char list)"
    by (auto intro: inj_onI simp add: enum_char_product_enum_nibble distinct_map distinct_product enum_distinct)
  show "\<And>P. Enum.enum_all P \<longleftrightarrow> Ball (UNIV :: char set) P"
    by (simp add: UNIV enum_all_char_def list_all_iff)
  show "\<And>P. Enum.enum_ex P \<longleftrightarrow> Bex (UNIV :: char set) P"
    by (simp add: UNIV enum_ex_char_def list_ex_iff)
qed

end

lemma card_UNIV_char:
  "card (UNIV :: char set) = 256"
  by (simp add: card_UNIV_length_enum enum_char_def)

definition nat_of_char :: "char \<Rightarrow> nat"
where
  "nat_of_char c = (case c of Char x y \<Rightarrow> nat_of_nibble x * 16 + nat_of_nibble y)"

lemma nat_of_char_Char:
  "nat_of_char (Char x y) = nat_of_nibble x * 16 + nat_of_nibble y"
  by (simp add: nat_of_char_def)

setup {*
let
  val nibbles = map_range (Thm.cterm_of @{theory} o HOLogic.mk_nibble) 16;
  val simpset =
    put_simpset HOL_ss @{context}
      addsimps @{thms nat_of_nibble.simps mult_0 mult_1 add_0 add_0_right arith_simps numeral_plus_one};
  fun mk_code_eqn x y =
    Drule.instantiate' [] [SOME x, SOME y] @{thm nat_of_char_Char}
    |> simplify simpset;
  val code_eqns = map_product mk_code_eqn nibbles nibbles;
in
  Global_Theory.note_thmss ""
    [((@{binding nat_of_char_simps}, []), [(code_eqns, [])])]
  #> snd
end
*}

declare nat_of_char_simps [code]

lemma nibble_of_nat_of_char_div_16:
  "nibble_of_nat (nat_of_char c div 16) = (case c of Char x y \<Rightarrow> x)"
  by (cases c)
    (simp add: nat_of_char_def add_commute nat_of_nibble_less_16)

lemma nibble_of_nat_nat_of_char:
  "nibble_of_nat (nat_of_char c) = (case c of Char x y \<Rightarrow> y)"
proof (cases c)
  case (Char x y)
  then have *: "nibble_of_nat ((nat_of_nibble y + nat_of_nibble x * 16) mod 16) = y"
    by (simp add: nibble_of_nat_mod_16)
  then have "nibble_of_nat (nat_of_nibble y + nat_of_nibble x * 16) = y"
    by (simp only: nibble_of_nat_mod_16)
  with Char show ?thesis by (simp add: nat_of_char_def add_commute)
qed

code_datatype Char -- {* drop case certificate for char *}

lemma case_char_code [code]:
  "case_char f c = (let n = nat_of_char c in f (nibble_of_nat (n div 16)) (nibble_of_nat n))"
  by (cases c)
    (simp only: Let_def nibble_of_nat_of_char_div_16 nibble_of_nat_nat_of_char char.case)

lemma [code]:
  "rec_char = case_char"
  by (simp add: fun_eq_iff split: char.split)

definition char_of_nat :: "nat \<Rightarrow> char" where
  "char_of_nat n = Enum.enum ! (n mod 256)"

lemma char_of_nat_Char_nibbles:
  "char_of_nat n = Char (nibble_of_nat (n div 16)) (nibble_of_nat n)"
proof -
  from mod_mult2_eq [of n 16 16]
  have "n mod 256 = 16 * (n div 16 mod 16) + n mod 16" by simp
  then show ?thesis
    by (simp add: char_of_nat_def enum_char_product_enum_nibble card_UNIV_nibble
      card_UNIV_length_enum [symmetric] nibble_of_nat_def product_nth add_commute)
qed

lemma char_of_nat_of_char [simp]:
  "char_of_nat (nat_of_char c) = c"
  by (cases c)
    (simp add: char_of_nat_Char_nibbles nibble_of_nat_of_char_div_16 nibble_of_nat_nat_of_char)

lemma nat_of_char_of_nat [simp]:
  "nat_of_char (char_of_nat n) = n mod 256"
proof -
  have "n mod 256 = n mod (16 * 16)" by simp
  then have "n div 16 mod 16 * 16 + n mod 16 = n mod 256" by (simp only: mod_mult2_eq)
  then show ?thesis
    by (cases "char_of_nat n") (auto simp add: nat_of_char_def char_of_nat_Char_nibbles)
qed

lemma inj_nat_of_char:
  "inj nat_of_char"
  by (rule inj_on_inverseI) (rule char_of_nat_of_char)

lemma nat_of_char_eq_iff:
  "nat_of_char c = nat_of_char d \<longleftrightarrow> c = d"
  by (rule inj_eq) (rule inj_nat_of_char)

lemma nat_of_char_less_256:
  "nat_of_char c < 256"
proof (cases c)
  case (Char x y)
  with nat_of_nibble_less_16 [of x] nat_of_nibble_less_16 [of y]
  show ?thesis by (simp add: nat_of_char_def)
qed

lemma char_of_nat_mod_256:
  "char_of_nat (n mod 256) = char_of_nat n"
proof -
  from nibble_of_nat_mod_16 [of "n mod 256"]
  have "nibble_of_nat (n mod 256) = nibble_of_nat (n mod 256 mod 16)" by simp
  with nibble_of_nat_mod_16 [of n]
  have *: "nibble_of_nat (n mod 256) = nibble_of_nat n" by (simp add: mod_mod_cancel)
  have "n mod 256 = n mod (16 * 16)" by simp
  then have **: "n mod 256 = n div 16 mod 16 * 16 + n mod 16" by (simp only: mod_mult2_eq)
  show ?thesis
    by (simp add: char_of_nat_Char_nibbles *)
     (simp add: div_add1_eq nibble_of_nat_mod_16 [of "n div 16"] **)
qed


subsection {* Strings as dedicated type *}

typedef literal = "UNIV :: string set"
  morphisms explode STR ..

setup_lifting (no_code) type_definition_literal

instantiation literal :: size
begin

definition size_literal :: "literal \<Rightarrow> nat"
where
  [code]: "size_literal (s\<Colon>literal) = 0"

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

lemma STR_inject' [simp]:
  "STR xs = STR ys \<longleftrightarrow> xs = ys"
  by (simp add: STR_inject)

lifting_update literal.lifting
lifting_forget literal.lifting

subsection {* Code generator *}

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

setup {*
  fold String_Code.add_literal_string ["SML", "OCaml", "Haskell", "Scala"]
*}

code_printing
  class_instance literal :: equal \<rightharpoonup>
    (Haskell) -
| constant "HOL.equal :: literal \<Rightarrow> literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) = _)"
    and (OCaml) "!((_ : string) = _)"
    and (Haskell) infix 4 "=="
    and (Scala) infixl 5 "=="

setup {* Sign.map_naming (Name_Space.mandatory_path "Code") *}

definition abort :: "literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
where [simp, code del]: "abort _ f = f ()"

lemma abort_cong: "msg = msg' ==> Code.abort msg f = Code.abort msg' f"
by simp

setup {* Sign.map_naming Name_Space.parent_path *}

setup {* Code_Simp.map_ss (Simplifier.add_cong @{thm Code.abort_cong}) *}

code_printing constant Code.abort \<rightharpoonup>
    (SML) "!(raise/ Fail/ _)"
    and (OCaml) "failwith"
    and (Haskell) "error"
    and (Scala) "!{/ sys.error((_));/  ((_)).apply(())/ }"

hide_type (open) literal

end
