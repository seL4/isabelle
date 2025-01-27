(* Author: Tobias Nipkow, Florian Haftmann, TU Muenchen *)

section \<open>Character and string types\<close>

theory String
imports Enum Bit_Operations Code_Numeral
begin

subsection \<open>Strings as list of bytes\<close>

text \<open>
  When modelling strings, we follow the approach given
  in \<^url>\<open>https://utf8everywhere.org/\<close>:

  \<^item> Strings are a list of bytes (8 bit).

  \<^item> Byte values from 0 to 127 are US-ASCII.

  \<^item> Byte values from 128 to 255 are uninterpreted blobs.
\<close>

subsubsection \<open>Bytes as datatype\<close>

datatype char =
  Char (digit0: bool) (digit1: bool) (digit2: bool) (digit3: bool)
       (digit4: bool) (digit5: bool) (digit6: bool) (digit7: bool)

context comm_semiring_1
begin

definition of_char :: \<open>char \<Rightarrow> 'a\<close>
  where \<open>of_char c = horner_sum of_bool 2 [digit0 c, digit1 c, digit2 c, digit3 c, digit4 c, digit5 c, digit6 c, digit7 c]\<close>

lemma of_char_Char [simp]:
  \<open>of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) =
    horner_sum of_bool 2 [b0, b1, b2, b3, b4, b5, b6, b7]\<close>
  by (simp add: of_char_def)

end

lemma (in comm_semiring_1) of_nat_of_char:
  \<open>of_nat (of_char c) = of_char c\<close>
  by (cases c) simp

lemma (in comm_ring_1) of_int_of_char:
  \<open>of_int (of_char c) = of_char c\<close>
  by (cases c) simp

lemma nat_of_char [simp]:
  \<open>nat (of_char c) = of_char c\<close>
  by (cases c) (simp only: of_char_Char nat_horner_sum)


context linordered_euclidean_semiring_bit_operations
begin

definition char_of :: \<open>'a \<Rightarrow> char\<close>
  where \<open>char_of n = Char (bit n 0) (bit n 1) (bit n 2) (bit n 3) (bit n 4) (bit n 5) (bit n 6) (bit n 7)\<close>

lemma char_of_take_bit_eq:
  \<open>char_of (take_bit n m) = char_of m\<close> if \<open>n \<ge> 8\<close>
  using that by (simp add: char_of_def bit_take_bit_iff)

lemma char_of_char [simp]:
  \<open>char_of (of_char c) = c\<close>
  by (simp only: of_char_def char_of_def bit_horner_sum_bit_iff) simp

lemma char_of_comp_of_char [simp]:
  "char_of \<circ> of_char = id"
  by (simp add: fun_eq_iff)

lemma inj_of_char:
  \<open>inj of_char\<close>
proof (rule injI)
  fix c d
  assume "of_char c = of_char d"
  then have "char_of (of_char c) = char_of (of_char d)"
    by simp
  then show "c = d"
    by simp
qed

lemma of_char_eqI:
  \<open>c = d\<close> if \<open>of_char c = of_char d\<close>
  using that inj_of_char by (simp add: inj_eq)

lemma of_char_eq_iff [simp]:
  \<open>of_char c = of_char d \<longleftrightarrow> c = d\<close>
  by (auto intro: of_char_eqI)

lemma of_char_of [simp]:
  \<open>of_char (char_of a) = a mod 256\<close>
proof -
  have \<open>[0..<8] = [0, Suc 0, 2, 3, 4, 5, 6, 7 :: nat]\<close>
    by (simp add: upt_eq_Cons_conv)
  then have \<open>[bit a 0, bit a 1, bit a 2, bit a 3, bit a 4, bit a 5, bit a 6, bit a 7] = map (bit a) [0..<8]\<close>
    by simp
  then have \<open>of_char (char_of a) = take_bit 8 a\<close>
    by (simp only: char_of_def of_char_def char.sel horner_sum_bit_eq_take_bit)
  then show ?thesis
    by (simp add: take_bit_eq_mod)
qed

lemma char_of_mod_256 [simp]:
  \<open>char_of (n mod 256) = char_of n\<close>
  by (rule of_char_eqI) simp

lemma of_char_mod_256 [simp]:
  \<open>of_char c mod 256 = of_char c\<close>
proof -
  have \<open>of_char (char_of (of_char c)) mod 256 = of_char (char_of (of_char c))\<close>
    by (simp only: of_char_of) simp
  then show ?thesis
    by simp
qed

lemma char_of_quasi_inj [simp]:
  \<open>char_of m = char_of n \<longleftrightarrow> m mod 256 = n mod 256\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?Q
  then show ?P
    by (auto intro: of_char_eqI)
next
  assume ?P
  then have \<open>of_char (char_of m) = of_char (char_of n)\<close>
    by simp
  then show ?Q
    by simp
qed

lemma char_of_eq_iff:
  \<open>char_of n = c \<longleftrightarrow> take_bit 8 n = of_char c\<close>
  by (auto intro: of_char_eqI simp add: take_bit_eq_mod)

lemma char_of_nat [simp]:
  \<open>char_of (of_nat n) = char_of n\<close>
  by (simp add: char_of_def String.char_of_def drop_bit_of_nat bit_simps possible_bit_def)

end

lemma inj_on_char_of_nat [simp]:
  "inj_on char_of {0::nat..<256}"
  by (rule inj_onI) simp

lemma nat_of_char_less_256 [simp]:
  "of_char c < (256 :: nat)"
proof -
  have "of_char c mod (256 :: nat) < 256"
    by arith
  then show ?thesis by simp
qed

lemma range_nat_of_char:
  "range of_char = {0::nat..<256}"
proof (rule; rule)
  fix n :: nat
  assume "n \<in> range of_char"
  then show "n \<in> {0..<256}"
    by auto
next
  fix n :: nat
  assume "n \<in> {0..<256}"
  then have "n = of_char (char_of n)"
    by simp
  then show "n \<in> range of_char"
    by (rule range_eqI)
qed

lemma UNIV_char_of_nat:
  "UNIV = char_of ` {0::nat..<256}"
proof -
  have "range (of_char :: char \<Rightarrow> nat) = of_char ` char_of ` {0::nat..<256}"
    by (simp add: image_image range_nat_of_char)
  with inj_of_char [where ?'a = nat] show ?thesis
    by (simp add: inj_image_eq_iff)
qed

lemma card_UNIV_char:
  "card (UNIV :: char set) = 256"
  by (auto simp add: UNIV_char_of_nat card_image)

context
  includes lifting_syntax and integer.lifting and natural.lifting
begin

lemma [transfer_rule]:
  \<open>(pcr_integer ===> (=)) char_of char_of\<close>
  by (unfold char_of_def) transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_integer) of_char of_char\<close>
  by (unfold of_char_def) transfer_prover

lemma [transfer_rule]:
  \<open>(pcr_natural ===> (=)) char_of char_of\<close>
  by (unfold char_of_def) transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_natural) of_char of_char\<close>
  by (unfold of_char_def) transfer_prover

end

lifting_update integer.lifting
lifting_forget integer.lifting

lifting_update natural.lifting
lifting_forget natural.lifting

lemma size_char_eq_0 [simp, code]:
  \<open>size c = 0\<close> for c :: char
  by (cases c) simp

lemma size'_char_eq_0 [simp, code]:
  \<open>size_char c = 0\<close>
  by (cases c) simp

syntax
  "_Char" :: "str_position \<Rightarrow> char"    (\<open>(\<open>open_block notation=\<open>literal char\<close>\<close>CHR _)\<close>)
  "_Char_ord" :: "num_const \<Rightarrow> char"   (\<open>(\<open>open_block notation=\<open>literal char code\<close>\<close>CHR _)\<close>)
syntax_consts
  "_Char" "_Char_ord" \<rightleftharpoons> Char

type_synonym string = "char list"

syntax
  "_String" :: "str_position \<Rightarrow> string"    (\<open>(\<open>open_block notation=\<open>literal string\<close>\<close>_)\<close>)

ML_file \<open>Tools/string_syntax.ML\<close>

instantiation char :: enum
begin

definition
  "Enum.enum = [
    CHR 0x00, CHR 0x01, CHR 0x02, CHR 0x03,
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
  "Enum.enum = map char_of [0..<256]"
proof -
  have "map (of_char :: char \<Rightarrow> nat) Enum.enum = [0..<256]"
    by (simp add: enum_char_def of_char_def upt_conv_Cons_Cons numeral_2_eq_2 [symmetric])
  then have "map char_of (map (of_char :: char \<Rightarrow> nat) Enum.enum) =
    map char_of [0..<256]"
    by simp
  then show ?thesis
    by simp
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

lemma linorder_char:
  "class.linorder (\<lambda>c d. of_char c \<le> (of_char d :: nat)) (\<lambda>c d. of_char c < (of_char d :: nat))"
  by standard auto

text \<open>Optimized version for execution\<close>

definition char_of_integer :: "integer \<Rightarrow> char"
  where [code_abbrev]: "char_of_integer = char_of"

definition integer_of_char :: "char \<Rightarrow> integer"
  where [code_abbrev]: "integer_of_char = of_char"

lemma char_of_integer_code [code]:
  "char_of_integer k = (let
     (q0, b0) = bit_cut_integer k;
     (q1, b1) = bit_cut_integer q0;
     (q2, b2) = bit_cut_integer q1;
     (q3, b3) = bit_cut_integer q2;
     (q4, b4) = bit_cut_integer q3;
     (q5, b5) = bit_cut_integer q4;
     (q6, b6) = bit_cut_integer q5;
     (_, b7) = bit_cut_integer q6
    in Char b0 b1 b2 b3 b4 b5 b6 b7)"
  by (simp add: bit_cut_integer_def char_of_integer_def char_of_def div_mult2_numeral_eq bit_iff_odd_drop_bit drop_bit_eq_div)

lemma integer_of_char_code [code]:
  "integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) =
    ((((((of_bool b7 * 2 + of_bool b6) * 2 +
      of_bool b5) * 2 + of_bool b4) * 2 +
        of_bool b3) * 2 + of_bool b2) * 2 +
          of_bool b1) * 2 + of_bool b0"
  by (simp add: integer_of_char_def of_char_def)


subsection \<open>Strings as dedicated type for target language code generation\<close>

subsubsection \<open>Logical specification\<close>

context
begin

qualified definition ascii_of :: "char \<Rightarrow> char"
  where "ascii_of c = Char (digit0 c) (digit1 c) (digit2 c) (digit3 c) (digit4 c) (digit5 c) (digit6 c) False"

qualified lemma ascii_of_Char [simp]:
  "ascii_of (Char b0 b1 b2 b3 b4 b5 b6 b7) = Char b0 b1 b2 b3 b4 b5 b6 False"
  by (simp add: ascii_of_def)

qualified lemma digit0_ascii_of_iff [simp]:
  "digit0 (String.ascii_of c) \<longleftrightarrow> digit0 c"
  by (simp add: String.ascii_of_def)

qualified lemma digit1_ascii_of_iff [simp]:
  "digit1 (String.ascii_of c) \<longleftrightarrow> digit1 c"
  by (simp add: String.ascii_of_def)

qualified lemma digit2_ascii_of_iff [simp]:
  "digit2 (String.ascii_of c) \<longleftrightarrow> digit2 c"
  by (simp add: String.ascii_of_def)

qualified lemma digit3_ascii_of_iff [simp]:
  "digit3 (String.ascii_of c) \<longleftrightarrow> digit3 c"
  by (simp add: String.ascii_of_def)

qualified lemma digit4_ascii_of_iff [simp]:
  "digit4 (String.ascii_of c) \<longleftrightarrow> digit4 c"
  by (simp add: String.ascii_of_def)

qualified lemma digit5_ascii_of_iff [simp]:
  "digit5 (String.ascii_of c) \<longleftrightarrow> digit5 c"
  by (simp add: String.ascii_of_def)

qualified lemma digit6_ascii_of_iff [simp]:
  "digit6 (String.ascii_of c) \<longleftrightarrow> digit6 c"
  by (simp add: String.ascii_of_def)

qualified lemma not_digit7_ascii_of [simp]:
  "\<not> digit7 (ascii_of c)"
  by (simp add: ascii_of_def)

qualified lemma ascii_of_idem:
  "ascii_of c = c" if "\<not> digit7 c"
  using that by (cases c) simp

qualified typedef literal = "{cs. \<forall>c\<in>set cs. \<not> digit7 c}"
  morphisms explode Abs_literal
proof
  show "[] \<in> {cs. \<forall>c\<in>set cs. \<not> digit7 c}"
    by simp
qed

qualified setup_lifting type_definition_literal

qualified lift_definition implode :: "string \<Rightarrow> literal"
  is "map ascii_of"
  by auto

qualified lemma implode_explode_eq [simp]:
  "String.implode (String.explode s) = s"
proof transfer
  fix cs
  show "map ascii_of cs = cs" if "\<forall>c\<in>set cs. \<not> digit7 c"
    using that
      by (induction cs) (simp_all add: ascii_of_idem)
qed

qualified lemma explode_implode_eq [simp]:
  "String.explode (String.implode cs) = map ascii_of cs"
  by transfer rule

end

context linordered_euclidean_semiring_bit_operations
begin

context
begin

qualified lemma char_of_ascii_of [simp]:
  \<open>of_char (String.ascii_of c) = take_bit 7 (of_char c)\<close>
  by (cases c) (simp only: String.ascii_of_Char of_char_Char take_bit_horner_sum_bit_eq, simp)

qualified lemma ascii_of_char_of:
  \<open>String.ascii_of (char_of a) = char_of (take_bit 7 a)\<close>
  by (simp add: char_of_def bit_simps)

end

end


subsubsection \<open>Syntactic representation\<close>

text \<open>
  Logical ground representations for literals are:

  \<^enum> \<open>0\<close> for the empty literal;

  \<^enum> \<open>Literal b0 \<dots> b6 s\<close> for a literal starting with one
    character and continued by another literal.

  Syntactic representations for literals are:

  \<^enum> Printable text as string prefixed with \<open>STR\<close>;

  \<^enum> A single ascii value as numerical hexadecimal value prefixed with \<open>STR\<close>.
\<close>

instantiation String.literal :: zero
begin

context
begin

qualified lift_definition zero_literal :: String.literal
  is Nil
  by simp

instance ..

end

end

context
begin

qualified abbreviation (output) empty_literal :: String.literal
  where "empty_literal \<equiv> 0"

qualified lift_definition Literal :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> String.literal \<Rightarrow> String.literal"
  is "\<lambda>b0 b1 b2 b3 b4 b5 b6 cs. Char b0 b1 b2 b3 b4 b5 b6 False # cs"
  by auto

qualified lemma Literal_eq_iff [simp]:
  "Literal b0 b1 b2 b3 b4 b5 b6 s = Literal c0 c1 c2 c3 c4 c5 c6 t
     \<longleftrightarrow> (b0 \<longleftrightarrow> c0) \<and> (b1 \<longleftrightarrow> c1) \<and> (b2 \<longleftrightarrow> c2) \<and> (b3 \<longleftrightarrow> c3)
         \<and> (b4 \<longleftrightarrow> c4) \<and> (b5 \<longleftrightarrow> c5) \<and> (b6 \<longleftrightarrow> c6) \<and> s = t"
  by transfer simp

qualified lemma empty_neq_Literal [simp]:
  "empty_literal \<noteq> Literal b0 b1 b2 b3 b4 b5 b6 s"
  by transfer simp

qualified lemma Literal_neq_empty [simp]:
  "Literal b0 b1 b2 b3 b4 b5 b6 s \<noteq> empty_literal"
  by transfer simp

end

code_datatype "0 :: String.literal" String.Literal

syntax
  "_Literal" :: "str_position \<Rightarrow> String.literal"
    (\<open>(\<open>open_block notation=\<open>literal string\<close>\<close>STR _)\<close>)
  "_Ascii" :: "num_const \<Rightarrow> String.literal"
    (\<open>(\<open>open_block notation=\<open>literal char code\<close>\<close>STR _)\<close>)
syntax_consts
  "_Literal" "_Ascii" \<rightleftharpoons> String.Literal

ML_file \<open>Tools/literal.ML\<close>


subsubsection \<open>Operations\<close>

instantiation String.literal :: plus
begin

context
begin

qualified lift_definition plus_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"
  is "(@)"
  by auto

instance ..

end

end

instance String.literal :: monoid_add
  by (standard; transfer) simp_all

lemma add_Literal_assoc:
  \<open>String.Literal b0 b1 b2 b3 b4 b5 b6 t + s = String.Literal b0 b1 b2 b3 b4 b5 b6 (t + s)\<close>
  by transfer simp

instantiation String.literal :: size
begin

context
  includes literal.lifting
begin

lift_definition size_literal :: "String.literal \<Rightarrow> nat"
  is length .

end

instance ..

end

instantiation String.literal :: equal
begin

context
begin

qualified lift_definition equal_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
  is HOL.equal .

instance
  by (standard; transfer) (simp add: equal)

end

end

instantiation String.literal :: linorder
begin

context
begin

qualified lift_definition less_eq_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
  is "ord.lexordp_eq (\<lambda>c d. of_char c < (of_char d :: nat))"
  .

qualified lift_definition less_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"
  is "ord.lexordp (\<lambda>c d. of_char c < (of_char d :: nat))"
  .

instance proof -
  from linorder_char interpret linorder "ord.lexordp_eq (\<lambda>c d. of_char c < (of_char d :: nat))"
    "ord.lexordp (\<lambda>c d. of_char c < (of_char d :: nat)) :: string \<Rightarrow> string \<Rightarrow> bool"
    by (rule linorder.lexordp_linorder)
  show "PROP ?thesis"
    by (standard; transfer) (simp_all add: less_le_not_le linear)
qed

end

end

lemma infinite_literal:
  "infinite (UNIV :: String.literal set)"
proof -
  define S where "S = range (\<lambda>n. replicate n CHR ''A'')"
  have "inj_on String.implode S"
  proof (rule inj_onI)
    fix cs ds
    assume "String.implode cs = String.implode ds"
    then have "String.explode (String.implode cs) = String.explode (String.implode ds)"
      by simp
    moreover assume "cs \<in> S" and "ds \<in> S"
    ultimately show "cs = ds"
      by (auto simp add: S_def)
  qed
  moreover have "infinite S"
    by (auto simp add: S_def dest: finite_range_imageI [of _ length])
  ultimately have "infinite (String.implode ` S)"
    by (simp add: finite_image_iff)
  then show ?thesis
    by (auto intro: finite_subset)
qed

lemma add_literal_code [code]:
  \<open>STR '''' + s = s\<close>
  \<open>s + STR '''' = s\<close>
  \<open>String.Literal b0 b1 b2 b3 b4 b5 b6 t + s = String.Literal b0 b1 b2 b3 b4 b5 b6 (t + s)\<close>
  by (simp_all add: add_Literal_assoc)


subsubsection \<open>Executable conversions\<close>

context
begin

qualified lift_definition asciis_of_literal :: "String.literal \<Rightarrow> integer list"
  is "map of_char"
  .

qualified lemma asciis_of_zero [simp, code]:
  "asciis_of_literal 0 = []"
  by transfer simp

qualified lemma asciis_of_Literal [simp, code]:
  "asciis_of_literal (String.Literal b0 b1 b2 b3 b4 b5 b6 s) =
    of_char (Char b0 b1 b2 b3 b4 b5 b6 False) # asciis_of_literal s "
  by transfer simp

qualified lift_definition literal_of_asciis :: "integer list \<Rightarrow> String.literal"
  is "map (String.ascii_of \<circ> char_of)"
  by auto

qualified lemma literal_of_asciis_Nil [simp, code]:
  "literal_of_asciis [] = 0"
  by transfer simp

qualified lemma literal_of_asciis_Cons [simp, code]:
  "literal_of_asciis (k # ks) = (case char_of k
    of Char b0 b1 b2 b3 b4 b5 b6 b7 \<Rightarrow> String.Literal b0 b1 b2 b3 b4 b5 b6 (literal_of_asciis ks))"
  by (simp add: char_of_def) (transfer, simp add: char_of_def)

qualified lemma literal_of_asciis_of_literal [simp]:
  "literal_of_asciis (asciis_of_literal s) = s"
proof transfer
  fix cs
  assume "\<forall>c\<in>set cs. \<not> digit7 c"
  then show "map (String.ascii_of \<circ> char_of) (map of_char cs) = cs"
    by (induction cs) (simp_all add: String.ascii_of_idem)
qed

qualified lemma explode_code [code]:
  "String.explode s = map char_of (asciis_of_literal s)"
  by transfer simp

qualified lemma implode_code [code]:
  "String.implode cs = literal_of_asciis (map of_char cs)"
  by transfer simp

qualified lemma equal_literal [code]:
  "HOL.equal (String.Literal b0 b1 b2 b3 b4 b5 b6 s)
    (String.Literal a0 a1 a2 a3 a4 a5 a6 r)
    \<longleftrightarrow> (b0 \<longleftrightarrow> a0) \<and> (b1 \<longleftrightarrow> a1) \<and> (b2 \<longleftrightarrow> a2) \<and> (b3 \<longleftrightarrow> a3)
      \<and> (b4 \<longleftrightarrow> a4) \<and> (b5 \<longleftrightarrow> a5) \<and> (b6 \<longleftrightarrow> a6) \<and> (s = r)"
  by (simp add: equal)

end


subsubsection \<open>Technical code generation setup\<close>

text \<open>Alternative constructor for generated computations\<close>

context
begin

qualified definition Literal' :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> String.literal \<Rightarrow> String.literal"
  where [simp]: "Literal' = String.Literal"

lemma [code]:
  \<open>Literal' b0 b1 b2 b3 b4 b5 b6 s = String.literal_of_asciis
    [foldr (\<lambda>b k. of_bool b + k * 2) [b0, b1, b2, b3, b4, b5, b6] 0] + s\<close>
proof -
  have \<open>foldr (\<lambda>b k. of_bool b + k * 2) [b0, b1, b2, b3, b4, b5, b6] 0 = of_char (Char b0 b1 b2 b3 b4 b5 b6 False)\<close>
    by simp
  moreover have \<open>Literal' b0 b1 b2 b3 b4 b5 b6 s = String.literal_of_asciis
    [of_char (Char b0 b1 b2 b3 b4 b5 b6 False)] + s\<close>
    by (unfold Literal'_def) (transfer, simp only: list.simps comp_apply char_of_char, simp)
  ultimately show ?thesis
    by simp
qed

lemma [code_computation_unfold]:
  "String.Literal = Literal'"
  by simp

end

code_reserved
  (SML) string String Char Str_Literal
  and (OCaml) string String Char Str_Literal
  and (Haskell) Str_Literal
  and (Scala) String Str_Literal

code_identifier
  code_module String \<rightharpoonup>
    (SML) Str and (OCaml) Str and (Haskell) Str and (Scala) Str

code_printing
  type_constructor String.literal \<rightharpoonup>
    (SML) "string"
    and (OCaml) "string"
    and (Haskell) "String"
    and (Scala) "String"
| constant "STR ''''" \<rightharpoonup>
    (SML) "\"\""
    and (OCaml) "\"\""
    and (Haskell) "\"\""
    and (Scala) "\"\""

setup \<open>
  fold Literal.add_code ["SML", "OCaml", "Haskell", "Scala"]
\<close>

code_printing
  code_module "Str_Literal" \<rightharpoonup>
    (SML) \<open>structure Str_Literal : sig
  type int = IntInf.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open IntInf;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;\<close> for constant String.literal_of_asciis String.asciis_of_literal
    and (OCaml) \<open>module Str_Literal : sig
  val literal_of_asciis : Z.t list -> string
  val asciis_of_literal: string -> Z.t list
end = struct

(* deliberate clones not relying on List._ module *)

let rec length xs = match xs with
    [] -> 0
  | x :: xs -> 1 + length xs;;

let rec nth xs n = match xs with
  (x :: xs) -> if n <= 0 then x else nth xs (n - 1);;

let rec map_range f n =
  if n <= 0
    then []
    else
      let m = n - 1
    in map_range f m @ [f m];;

let implode f xs =
  String.init (length xs) (fun n -> f (nth xs n));;

let explode f s =
  map_range (fun n -> f (String.get s n)) (String.length s);;

let z_128 = Z.of_int 128;;

let check_ascii k =
  if 0 <= k && k < 128
  then k
  else failwith "Non-ASCII character in literal";;

let char_of_ascii k = Char.chr (Z.to_int (Z.rem k z_128));;

let ascii_of_char c = Z.of_int (check_ascii (Char.code c));;

let literal_of_asciis ks = implode char_of_ascii ks;;

let asciis_of_literal s = explode ascii_of_char s;;

end;;\<close> for constant String.literal_of_asciis String.asciis_of_literal
    and (Haskell) \<open>module Str_Literal(literalOfAsciis, asciisOfLiteral) where

check_ascii :: Int -> Int
check_ascii k
  | (0 <= k && k < 128) = k
  | otherwise = error "Non-ASCII character in literal"

charOfAscii :: Integer -> Char
charOfAscii = toEnum . Prelude.fromInteger . (\k -> k `mod ` 128)

asciiOfChar :: Char -> Integer
asciiOfChar = toInteger . check_ascii . fromEnum

literalOfAsciis :: [Integer] -> [Char]
literalOfAsciis = map charOfAscii

asciisOfLiteral :: [Char] -> [Integer]
asciisOfLiteral = map asciiOfChar
\<close> for constant String.literal_of_asciis String.asciis_of_literal
    and (Scala) \<open>object Str_Literal {

private def checkAscii(k : Int) : Int =
  0 <= k && k < 128 match {
    case true => k
    case false => sys.error("Non-ASCII character in literal")
  }

private def charOfAscii(k : BigInt) : Char =
  (k % 128).charValue

private def asciiOfChar(c : Char) : BigInt =
  BigInt(checkAscii(c.toInt))

def literalOfAsciis(ks : List[BigInt]) : String =
  ks.map(charOfAscii).mkString

def asciisOfLiteral(s : String) : List[BigInt] =
  s.toList.map(asciiOfChar)

}
\<close> for constant String.literal_of_asciis String.asciis_of_literal
| constant \<open>(+) :: String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal\<close> \<rightharpoonup>
    (SML) infixl 18 "^"
    and (OCaml) infixr 6 "^"
    and (Haskell) infixr 5 "++"
    and (Scala) infixl 7 "+"
| constant String.literal_of_asciis \<rightharpoonup>
    (SML) "Str'_Literal.literal'_of'_asciis"
    and (OCaml) "Str'_Literal.literal'_of'_asciis"
    and (Haskell) "Str'_Literal.literalOfAsciis"
    and (Scala) "Str'_Literal.literalOfAsciis"
| constant String.asciis_of_literal \<rightharpoonup>
    (SML) "Str'_Literal.asciis'_of'_literal"
    and (OCaml) "Str'_Literal.asciis'_of'_literal"
    and (Haskell) "Str'_Literal.asciisOfLiteral"
    and (Scala) "Str'_Literal.asciisOfLiteral"
| class_instance String.literal :: equal \<rightharpoonup>
    (Haskell) -
| constant \<open>HOL.equal :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool\<close> \<rightharpoonup>
    (SML) "!((_ : string) = _)"
    and (OCaml) "!((_ : string) = _)"
    and (Haskell) infix 4 "=="
    and (Scala) infixl 5 "=="
| constant \<open>(\<le>) :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool\<close> \<rightharpoonup>
    (SML) "!((_ : string) <= _)"
    and (OCaml) "!((_ : string) <= _)"
    and (Haskell) infix 4 "<="
    \<comment> \<open>Order operations for \<^typ>\<open>String.literal\<close> work in Haskell only
          if no type class instance needs to be generated, because String = [Char] in Haskell
          and \<^typ>\<open>char list\<close> need not have the same order as \<^typ>\<open>String.literal\<close>.\<close>
    and (Scala) infixl 4 "<="
    and (Eval) infixl 6 "<="
| constant "(<) :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool" \<rightharpoonup>
    (SML) "!((_ : string) < _)"
    and (OCaml) "!((_ : string) < _)"
    and (Haskell) infix 4 "<"
    and (Scala) infixl 4 "<"
    and (Eval) infixl 6 "<"


subsubsection \<open>Code generation utility\<close>

setup \<open>Sign.map_naming (Name_Space.mandatory_path "Code")\<close>

definition abort :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
  where [simp]: "abort _ f = f ()"

declare [[code drop: Code.abort]]

lemma abort_cong:
  "msg = msg' \<Longrightarrow> Code.abort msg f = Code.abort msg' f"
  by simp

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm Code.abort_cong})\<close>

code_printing
  constant Code.abort \<rightharpoonup>
    (SML) "!(raise/ Fail/ _)"
    and (OCaml) "failwith"
    and (Haskell) "!(error/ ::/ forall a./ String -> (() -> a) -> a)"
    and (Scala) "!{/ sys.error((_));/ ((_)).apply(())/ }"


subsubsection \<open>Finally\<close>

lifting_update literal.lifting
lifting_forget literal.lifting

end
